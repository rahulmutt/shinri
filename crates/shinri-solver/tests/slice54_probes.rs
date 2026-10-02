//! Slice 54 probes (spec §6.2). A compound Bool term used as an argument of a
//! non-connective parent (UF, datatype constructor/selector) was an opaque
//! e-graph node, never tied to its truth value, so `(P t)` and `(P true)`
//! could differ while `t` held (wrong `sat`). `word_norm` now replaces such an
//! argument with an internal proxy `bool!<n>` plus `(= b t)`. Every `unsat`
//! case here answered `sat` at `61be117` unless marked "regression pin"; each
//! has a `sat` sibling so the fix cannot pass by over-refuting.
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

const UFLIA: &str = "(set-logic QF_UFLIA)(declare-fun p () Bool)(declare-fun q () Bool)\
    (declare-fun x () Int)(declare-fun y () Int)(declare-fun P (Bool) Bool)\
    (declare-fun f (Bool) Int)(declare-fun F (Bool Int Bool) Int)";
const UFLRA: &str = "(set-logic QF_UFLRA)(declare-fun x () Real)(declare-fun P (Bool) Bool)";
const UF: &str = "(set-logic QF_UF)(declare-sort U 0)(declare-fun a () U)(declare-fun b () U)\
    (declare-fun q () Bool)(declare-fun P (Bool) Bool)";
const DT: &str = "(set-logic QF_DT)(declare-datatypes ((B 0)) (((mk (fld Bool)))))\
    (declare-fun y () B)(declare-fun q () Bool)(declare-fun r () Bool)";

fn verdict(header: &str, body: &str) -> String {
    let out = run_script(&format!("{header}{body}(check-sat)"));
    out.first().cloned().unwrap_or_default()
}

/// Asserts `body` is unsat and `sibling` (one constraint relaxed) is sat.
fn pair(header: &str, body: &str, sibling: &str) {
    assert_eq!(verdict(header, body), "unsat", "{header}{body}");
    assert_eq!(verdict(header, sibling), "sat", "{header}{sibling}");
}

// ── spec §1.2 ──────────────────────────────────────────────────────────────

#[test]
fn r1_int_eq_argument() {
    pair(
        UFLIA,
        "(assert (P (= x 1)))(assert (not (P true)))(assert (= x 1))",
        "(assert (P (= x 1)))(assert (not (P true)))(assert (= x 2))",
    );
}

#[test]
fn r2_distinct_over_int_valued_uf() {
    pair(
        UFLIA,
        "(assert (distinct (f (= x 1)) (f true)))(assert (= x 1))",
        "(assert (distinct (f (= x 1)) (f true)))(assert (= x 2))",
    );
}

#[test]
fn r3_int_le_argument() {
    pair(
        UFLIA,
        "(assert (P (<= x 1)))(assert (not (P true)))(assert (= x 0))",
        "(assert (P (<= x 1)))(assert (not (P true)))(assert (= x 2))",
    );
}

#[test]
fn r4_uninterpreted_sort_eq_argument() {
    pair(
        UF,
        "(assert (P (= a b)))(assert (not (P true)))(assert (= a b))",
        "(assert (P (= a b)))(assert (not (P true)))(assert (distinct a b))",
    );
}

#[test]
fn r5_pure_boolean_argument() {
    pair(
        UF,
        "(assert (P (and q q)))(assert (not (P true)))(assert q)",
        "(assert (P (and q q)))(assert (not (P true)))(assert (not q))",
    );
}

/// Regression pin: a bare Bool constant argument was already linked.
#[test]
fn r6_bare_bool_constant_argument() {
    pair(
        UF,
        "(assert (P q))(assert (not (P true)))(assert q)",
        "(assert (P q))(assert (not (P true)))(assert (not q))",
    );
}

#[test]
fn r7_false_side() {
    pair(
        UFLIA,
        "(assert (P (= x 1)))(assert (not (P false)))(assert (not (= x 1)))",
        "(assert (P (= x 1)))(assert (not (P false)))(assert (= x 1))",
    );
}

#[test]
fn uflra_eq_argument() {
    pair(
        UFLRA,
        "(assert (P (= x 1.0)))(assert (not (P true)))(assert (= x 1.0))",
        "(assert (P (= x 1.0)))(assert (not (P true)))(assert (= x 2.0))",
    );
}

#[test]
fn uflra_le_argument() {
    pair(
        UFLRA,
        "(assert (P (<= x 1.0)))(assert (not (P true)))(assert (= x 0.5))",
        "(assert (P (<= x 1.0)))(assert (not (P true)))(assert (= x 1.5))",
    );
}

#[test]
fn s5_datatype_constructor_argument() {
    pair(
        DT,
        "(assert (= (mk (and q r)) (mk true)))(assert (not q))",
        "(assert (= (mk (and q r)) (mk true)))(assert q)",
    );
}

#[test]
fn datatype_selector_over_purified_field() {
    pair(
        DT,
        "(assert (= y (mk (and q r))))(assert (fld y))(assert (not q))",
        "(assert (= y (mk (and q r))))(assert (fld y))(assert r)",
    );
}

#[test]
fn multi_argument_uf() {
    pair(
        UFLIA,
        "(assert (distinct (F (= x 1) y (and p q)) (F true y false)))(assert (= x 1))(assert (not p))",
        "(assert (distinct (F (= x 1) y (and p q)) (F true y false)))(assert (= x 1))(assert p)(assert q)",
    );
}

#[test]
fn bool_argument_uf_under_arithmetic() {
    pair(
        UFLIA,
        "(assert (= (f true) 5))(assert (< (f (= x 1)) 3))(assert (= x 1))",
        "(assert (= (f true) 5))(assert (< (f (= x 1)) 3))(assert (= x 2))",
    );
}

#[test]
fn nested_purification() {
    pair(
        UFLIA,
        "(assert (P (P (and p q))))(assert (not (P (P true))))(assert p)(assert q)",
        "(assert (P (P (and p q))))(assert p)(assert q)",
    );
}

// ── Fence pins: sound `unknown` today, must stay so (spec §3.5) ────────────

#[test]
fn fence_pin_ufbv_bool_argument_stays_unknown() {
    let h = "(set-logic QF_UFBV)(declare-fun x () (_ BitVec 4))(declare-fun P (Bool) Bool)";
    assert_eq!(
        verdict(
            h,
            "(assert (P (= x #x1)))(assert (not (P true)))(assert (= x #x1))"
        ),
        "unknown"
    );
}

#[test]
fn fence_pin_bool_array_select_stays_unknown() {
    let h = "(set-logic QF_AUFLIA)(declare-fun a () (Array Int Bool))(declare-fun P (Bool) Bool)";
    assert_eq!(
        verdict(
            h,
            "(assert (P (select a 0)))(assert (not (P true)))(assert (select a 0))"
        ),
        "unknown"
    );
}

#[test]
fn fence_pin_bool_array_store_stays_unknown() {
    let h = "(set-logic QF_AUFLIA)(declare-fun x () Int)(declare-fun a () (Array Int Bool))";
    assert_eq!(
        verdict(
            h,
            "(assert (= a (store a 0 (= x 1))))(assert (= x 1))(assert (not (select a 0)))"
        ),
        "unknown"
    );
}

// ── Model hygiene ──────────────────────────────────────────────────────────

#[test]
fn get_model_has_no_proxy_symbols() {
    let out = run_script(
        "(set-logic QF_UFLIA)(set-option :produce-models true)(declare-fun x () Int)\
         (declare-fun P (Bool) Bool)(assert (P (= x 1)))(assert (not (P true)))\
         (assert (= x 2))(check-sat)(get-model)",
    );
    assert_eq!(out[0], "sat");
    assert!(out[1].contains("(define-fun x () Int 2)"), "{:?}", out[1]);
    assert!(
        !out[1].contains("bool!"),
        "proxy leaked into get-model: {:?}",
        out[1]
    );
}

// ── Review Focus ───────────────────────────────────────────────────────────

/// Review Focus 1. HEAD: sat sat sat; z3: unsat sat unsat.
#[test]
fn push_pop_reuses_proxy_soundly() {
    let out = run_script(&format!(
        "{UFLIA}(push 1)(assert (P (= x 1)))(assert (not (P true)))(assert (= x 1))(check-sat)(pop 1)\
         (assert (not (P true)))(assert (= x 1))(check-sat)\
         (push 1)(assert (P (= x 1)))(check-sat)(pop 1)"
    ));
    assert_eq!(out, vec!["unsat", "sat", "unsat"]);
}

/// Review Focus 2. HEAD: sat sat; z3: sat unsat.
#[test]
fn incremental_pin_after_first_check() {
    let out = run_script(&format!(
        "{UFLIA}(assert (P (= x 1)))(assert (not (P true)))(check-sat)(assert (= x 1))(check-sat)"
    ));
    assert_eq!(out, vec!["sat", "unsat"]);
}

/// Review Focus 3. HEAD: sat; z3: unsat. `unknown` is acceptable: the string
/// model gate evaluates the user's original assertions, which contain the UF.
#[test]
fn string_path_bool_arg_is_not_sat() {
    let v = verdict(
        "(set-logic QF_SLIA)(declare-fun s () String)(declare-fun P (Bool) Bool)",
        "(assert (P (= (str.len s) 1)))(assert (not (P true)))(assert (= s \"a\"))",
    );
    assert_ne!(v, "sat", "wrong sat on the string path");
}

/// Review Focus 4: mirrors script_e2e::post_mint_declaration_of_internal_name_is_rejected.
#[test]
fn post_mint_declaration_of_bool_proxy_is_rejected() {
    let out = run_script(&format!(
        "{UFLIA}(assert (P (= x 1)))(check-sat)\
         (declare-fun bool!0 () Bool)(assert bool!0)(check-sat)"
    ));
    assert_eq!(
        out.len(),
        4,
        "sat / declare-error / use-error / sat: {out:?}"
    );
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("reserved for solver-internal use"),
        "declaration of the minted name must be rejected, got {:?}",
        out[1]
    );
    assert!(
        out[2].starts_with("(error"),
        "use is undeclared, got {:?}",
        out[2]
    );
    assert_eq!(out[3], "sat");
}

/// Review Focus 5. HEAD: sat; z3: unsat.
#[test]
fn proxy_inside_eliminated_term_ite() {
    pair(
        UFLIA,
        "(assert (= (ite p (f (= x 1)) 0) 7))(assert p)(assert (= x 1))(assert (= (f true) 5))",
        "(assert (= (ite p (f (= x 1)) 0) 7))(assert p)(assert (= x 1))(assert (= (f true) 7))",
    );
}
