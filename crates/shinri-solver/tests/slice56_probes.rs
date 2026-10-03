//! Slice 56 probes (spec §6.2). A nullary user Bool constant used only as an
//! argument of a non-connective parent (UF, datatype constructor) was never a
//! SAT atom, so EUF never merged it with ⊤/⊥ and `(P q)`, `(P true)`,
//! `(P false)` could take three different values (wrong `sat`; `get-model`
//! bound `q` to `@elem0`). `word_norm` now appends `(or q (not q))` for such
//! an argument. Every `unsat` case answered `sat` at `1a9db04`; each `pair`
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

const UF: &str = "(set-logic QF_UF)(declare-sort U 0)(declare-fun q () Bool)\
    (declare-fun r () Bool)(declare-fun P (Bool) Bool)(declare-fun P2 (Bool Bool) Bool)\
    (declare-fun g (Bool) U)";
const UFLIA: &str = "(set-logic QF_UFLIA)(declare-fun q () Bool)(declare-fun f (Bool) Int)";
const UFLRA: &str = "(set-logic QF_UFLRA)(declare-fun q () Bool)(declare-fun f (Bool) Real)";
const DT: &str = "(set-logic QF_DT)(declare-datatypes ((B 0)) (((mk (fld Bool)))))\
    (declare-fun q () Bool)";

/// a1's three assertions over `P` and `q`.
const A1: &str = "(assert (P q))(assert (not (P true)))(assert (not (P false)))";

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

/// a1 — the slice-55 report's reproducer. HEAD: sat; z3: unsat.
#[test]
fn a1_bare_constant_uf_argument() {
    pair(UF, A1, "(assert (P q))(assert (not (P true)))");
}

/// a2 — Int-valued UF over the constant. HEAD: sat; z3: unsat.
#[test]
fn a2_int_valued_uf() {
    pair(
        UFLIA,
        "(assert (distinct (f q) (f true) (f false)))",
        "(assert (distinct (f q) (f true)))",
    );
}

/// a3 — uninterpreted-sort-valued UF. HEAD: sat; z3: unsat.
#[test]
fn a3_usort_valued_uf() {
    pair(
        UF,
        "(assert (distinct (g q) (g true) (g false)))",
        "(assert (distinct (g q) (g true)))",
    );
}

/// a4 — multi-argument UF, second argument pinned by an atom. HEAD: sat; z3: unsat.
#[test]
fn a4_multi_argument_uf() {
    pair(
        UF,
        "(assert (P2 q r))(assert (not (P2 true true)))(assert (not (P2 false true)))(assert r)",
        "(assert (P2 q r))(assert (not (P2 true true)))(assert (not (P2 false true)))",
    );
}

/// a5 — datatype constructor argument. HEAD: sat; z3: unsat.
#[test]
fn a5_datatype_constructor_argument() {
    pair(
        DT,
        "(assert (distinct (mk q) (mk true) (mk false)))",
        "(assert (distinct (mk q) (mk true)))",
    );
}

/// a6 — Real-valued UF. HEAD: sat; z3: unsat.
#[test]
fn a6_real_valued_uf() {
    pair(
        UFLRA,
        "(assert (distinct (f q) (f true) (f false)))",
        "(assert (distinct (f q) (f true)))",
    );
}

/// a7 — completeness side and model. HEAD: sat with `((q @elem0))`;
/// z3: sat with `((q false))`. Also pins that the tautology is not folded
/// away anywhere downstream (if it were, `q` would print `@elem0` again).
#[test]
fn a7_model_binds_constant_to_false() {
    let out = run_script(&format!(
        "(set-option :produce-models true){UF}(assert (P q))(assert (not (P true)))\
         (check-sat)(get-value (q))(get-model)"
    ));
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "((q false))");
    assert!(
        out[2].contains("(define-fun q () Bool false)"),
        "{:?}",
        out[2]
    );
    assert!(
        !out[2].contains('@'),
        "abstract value in get-model: {:?}",
        out[2]
    );
}

/// a8 — incremental: the definition is re-emitted after `pop`.
/// HEAD: sat sat sat; z3: unsat sat unsat.
#[test]
fn a8_push_pop_reemits_definition() {
    let out = run_script(&format!(
        "{UF}(push 1){A1}(check-sat)(pop 1)(check-sat){A1}(check-sat)"
    ));
    assert_eq!(out, vec!["unsat", "sat", "unsat"]);
}

// ── Review Focus ───────────────────────────────────────────────────────────

/// Review Focus 1. HEAD: sat; z3: unsat. `unknown` is acceptable (string
/// model gate).
#[test]
fn rf1_string_logic_header() {
    let v = verdict(
        "(set-logic QF_SLIA)(declare-fun q () Bool)(declare-fun s () String)\
         (declare-fun P (Bool) Bool)(assert (= s \"ab\"))",
        A1,
    );
    assert_ne!(v, "sat");
}

/// Review Focus 2a. HEAD: sat; z3: unsat. No BV term, so no fence applies and
/// the answer must be exactly `unsat`.
#[test]
fn rf2_ufbv_header_without_bv_term() {
    let v = verdict(
        "(set-logic QF_UFBV)(declare-fun q () Bool)(declare-fun P (Bool) Bool)",
        A1,
    );
    assert_eq!(v, "unsat");
}

/// Review Focus 2b. HEAD: unknown (fenced); z3: unsat. Must not become sat.
#[test]
fn rf2_ufbv_header_with_bv_term() {
    let v = verdict(
        "(set-logic QF_UFBV)(declare-fun q () Bool)(declare-fun v () (_ BitVec 4))\
         (declare-fun P (Bool) Bool)(assert (= v #x1))",
        A1,
    );
    assert_ne!(v, "sat");
}

/// Review Focus 3. HEAD: unknown (fenced); z3: unsat. Must not become sat.
#[test]
fn rf3_bool_index_array_not_sat() {
    let v = verdict(
        "(set-logic QF_AUFLIA)(declare-fun q () Bool)(declare-fun a () (Array Bool Int))",
        "(assert (distinct (select a q) (select a true) (select a false)))",
    );
    assert_ne!(v, "sat");
}

/// Review Focus 4. Regression pin (HEAD: unsat; z3: unsat): `(not q)` is
/// proxied, `q` gets the definition; both must agree.
#[test]
fn rf4_bare_and_negated_argument() {
    assert_eq!(verdict(UF, &format!("{A1}(assert (P (not q)))")), "unsat");
}
