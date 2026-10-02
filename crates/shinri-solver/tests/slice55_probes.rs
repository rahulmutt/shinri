//! Slice 55 probes (spec §6.1). `get-value` echoed builtin terms as raw
//! TermId indices (`t9`), printed `?` for every term containing a slice-54
//! purified Bool argument, and neither `get-value` nor `get-model` quoted
//! symbols that need `|…|`. Each probe pins the exact response line.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

fn run_script(src: &str) -> Vec<String> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut out = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match result {
            Ok(cmd) => match solver.execute(cmd) {
                CommandResponse::None => {}
                CommandResponse::Sat => out.push("sat".into()),
                CommandResponse::Unsat => out.push("unsat".into()),
                CommandResponse::Unknown => out.push("unknown".into()),
                CommandResponse::Model(s) | CommandResponse::Values(s) => out.push(s),
                CommandResponse::Error(e) => out.push(format!("(error \"{e}\")")),
            },
            Err(diag) => out.push(format!("(error \"{}\")", diag.message)),
        }
    }
    out
}

/// e7: no internal name and no TermId index in any response line.
fn assert_no_leak(line: &str) {
    assert!(!line.contains("bool!"), "proxy name leaked: {line}");
    assert!(!line.contains("ite!"), "ite name leaked: {line}");
    let leaked = line.split([' ', '(', ')']).any(|tok| {
        tok.len() > 1 && tok.starts_with('t') && tok[1..].chars().all(|c| c.is_ascii_digit())
    });
    assert!(!leaked, "TermId index leaked: {line}");
}

/// Runs `src`, requires `sat` first, checks every later line for leaks,
/// and returns the lines after `sat`.
fn sat_then(src: &str) -> Vec<String> {
    let out = run_script(src);
    assert_eq!(
        out.first().map(String::as_str),
        Some("sat"),
        "{src}\n{out:?}"
    );
    for l in &out[1..] {
        assert_no_leak(l);
    }
    out[1..].to_vec()
}

// ── echo (e1, e5, Review Focus 1, 5) ───────────────────────────────────────

#[test]
fn e1_builtin_echo() {
    let out = sat_then(
        "(set-logic QF_LIA)(declare-fun a () Int)(assert (= a 0))\
         (check-sat)(get-value ((+ a 1)))",
    );
    // The value of (+ a 1) is not a registered term; `?` is the honest
    // fallback. A V2 evaluator would change this line deliberately.
    assert_eq!(out[0], "(((+ a 1) ?))", "{out:?}");
}

#[test]
fn e5_quoted_symbol_and_sort() {
    let out = sat_then(
        "(set-logic QF_UF)(declare-sort |my sort| 0)\
         (declare-fun |a#b| () |my sort|)(declare-fun c () |my sort|)\
         (assert (= |a#b| c))(check-sat)(get-value (|a#b|))(get-model)",
    );
    assert!(out[0].starts_with("((|a#b| "), "{out:?}");
    assert!(
        out[1].contains("(define-fun |a#b| () |my sort| "),
        "{out:?}"
    );
    assert!(out[1].contains("(define-fun c () |my sort| "), "{out:?}");
}

#[test]
fn e5_get_model_quotes_esbmc_style_name() {
    let out = sat_then(
        "(set-logic QF_BV)(declare-fun |__ESBMC_rounding_mode&0#10| () (_ BitVec 8))\
         (assert (= |__ESBMC_rounding_mode&0#10| #x2a))(check-sat)(get-model)",
    );
    assert_eq!(
        out[0],
        "((define-fun |__ESBMC_rounding_mode&0#10| () (_ BitVec 8) #x2a))"
    );
}

#[test]
fn quoted_uf_application_echo() {
    let out = sat_then(
        "(set-logic QF_UFLIA)(declare-fun |f g| (Int) Int)(declare-fun x () Int)\
         (assert (= (|f g| x) 3))(check-sat)(get-value ((|f g| x)))",
    );
    assert_eq!(out[0], "(((|f g| x) 3))");
}

#[test]
fn tester_echo_reparses() {
    let out = sat_then(
        "(set-logic QF_DT)(declare-datatypes ((B 0)) (((mk (fa Bool)) (nil))))\
         (declare-fun v () B)(assert ((_ is mk) v))(check-sat)(get-value (((_ is mk) v)))",
    );
    // Stored as the minted `is-mk` tester symbol, printed as the SMT-LIB 2.6
    // indexed form; the legacy `(is-mk v)` does not parse in shinri.
    assert!(out[0].starts_with("((((_ is mk) v) "), "{out:?}");
    // The echoed label must re-parse in shinri.
    let label = "((_ is mk) v)";
    let re = run_script(&format!(
        "(set-logic QF_DT)(declare-datatypes ((B 0)) (((mk (fa Bool)) (nil))))\
         (declare-fun v () B)(assert {label})(check-sat)"
    ));
    assert_eq!(re, vec!["sat"], "echo did not re-parse: {re:?}");
}

#[test]
fn e6_shared_let_chain_is_bounded_and_truncated() {
    // Same shape as qfdt_model_e2e's slice-43 T6 test: a 25-level chain of
    // `let`-shared `(g x x)` nodes, 2^25 nodes when unshared.
    let lets: String = (1..=25)
        .map(|i| format!("(let ((x{i} (g x{} x{}))) ", i - 1, i - 1))
        .collect();
    let query = format!("(let ((x0 0)) {lets}x25{})", ")".repeat(26));
    let src = format!(
        "(set-logic QF_UFLIA)(declare-fun g (Int Int) Int)(check-sat)(get-value ({query}))"
    );
    let out = run_script(&src);
    assert_eq!(out[0], "sat");
    assert!(
        out[1].len() < 2_000_000,
        "not bounded: {} bytes",
        out[1].len()
    );
    assert!(out[1].contains("|<truncated>|"), "no placeholder");
    assert_no_leak(&out[1]);
}

// ── remap (e2, e3, e4, Review Focus 3, 4) ──────────────────────────────────

const UFLIA: &str = "(set-logic QF_UFLIA)(declare-fun x () Int)(declare-fun y () Int)\
    (declare-fun c () Bool)(declare-fun P (Bool) Bool)(declare-fun f (Bool) Int)";

#[test]
fn e2_purified_uf_argument_gets_value() {
    let out = sat_then(&format!(
        "{UFLIA}(assert (= (f (= x 1)) 7))(check-sat)(get-value ((f (= x 1))))"
    ));
    assert_eq!(out[0], "(((f (= x 1)) 7))");
}

#[test]
fn e3_slice54_report_query() {
    let out = sat_then(&format!(
        "{UFLIA}(assert (P (= x 1)))(assert (not (P true)))(assert (= x 2))\
         (check-sat)(get-value ((P (= x 1)) (= x 1) (P false)))"
    ));
    // (P (= x 1)) is asserted true; (= x 1) is false since x = 2. (P false)
    // occurs in no assertion: `?` (no evaluator; V2 is queued).
    assert_eq!(out[0], "(((P (= x 1)) true) ((= x 1) false) ((P false) ?))");
}

#[test]
fn e4_ite_inside_purified_argument() {
    let out = sat_then(&format!(
        "{UFLIA}(assert (P (> (ite c x y) 0)))(assert c)(assert (= x 5))\
         (check-sat)(get-value ((P (> (ite c x y) 0)) (> (ite c x y) 0) (ite c x y)))"
    ));
    assert_eq!(
        out[0],
        "(((P (> (ite c x y) 0)) true) ((> (ite c x y) 0) true) ((ite c x y) 5))"
    );
}

#[test]
fn stale_rewrite_after_pop_prints_unknown_value() {
    let out = sat_then(&format!(
        "{UFLIA}(push 1)(assert (= (f (= x 1)) 7))(check-sat)(pop 1)\
         (assert (= x 3))(check-sat)(get-value ((f (= x 1))))"
    ));
    // `sat_then` drops the first `sat`, so out[0] is the second check-sat's
    // `sat` and out[1] is the get-value line.
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], "(((f (= x 1)) ?))", "stale value served: {out:?}");
}

#[test]
fn nary_eq_query_is_true_or_unknown() {
    let out = sat_then(&format!(
        "{UFLIA}(declare-fun z () Int)(assert (= x y z))(check-sat)(get-value ((= x y z)))"
    ));
    assert!(
        out[0] == "(((= x y z) true))" || out[0] == "(((= x y z) ?))",
        "wrong value for an asserted n-ary =: {out:?}"
    );
}

#[test]
fn unrewritten_bool_uf_application_unchanged() {
    // Regression guard mirroring qfufbv_e2e.rs:866: a term the walk did not
    // rewrite takes the old path; the remap must not invent a value.
    let out = sat_then(&format!(
        "{UFLIA}(assert (P c))(check-sat)(get-value ((P c)))"
    ));
    assert_eq!(out[0], "(((P c) true))");
}

#[test]
fn e5_quoted_datatype_constructor_value() {
    let out = sat_then(
        "(set-logic QF_DT)(declare-datatypes ((|my dt| 0)) \
         (((|mk a| (|fa b| Int)) (|nil x|))))\
         (declare-fun v () |my dt|)(assert ((_ is |mk a|) v))\
         (check-sat)(get-model)(get-value (v))",
    );
    assert_eq!(out[0], "((define-fun v () |my dt| (|mk a| 0)))", "{out:?}");
    assert_eq!(out[1], "((v (|mk a| 0)))", "{out:?}");
}
