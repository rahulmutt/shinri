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
    // fallback (a V2 evaluator is queued). The echo is what this pins.
    assert!(
        out[0] == "(((+ a 1) 1))" || out[0] == "(((+ a 1) ?))",
        "{out:?}"
    );
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
    // Stored as the minted `is-mk` tester symbol (legacy form z3/cvc5 accept).
    assert!(out[0].starts_with("(((is-mk v) "), "{out:?}");
    // The echoed label must re-parse in shinri.
    let label = "(is-mk v)";
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
