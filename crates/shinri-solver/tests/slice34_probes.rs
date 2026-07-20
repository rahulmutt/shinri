//! Slice 34 probes (spec §7). These pin the alias-propagation frontier.
//!
//! Written BEFORE the implementation as a measured baseline: A1/A2/A4 record
//! the engine's current sound-but-needless `unknown` (z3 says `unsat` for all
//! three), A3 is the SAT control, and B1 pins the §2 scope fence (the
//! multi-atom variable-bearing shape, banked — must NOT flip this slice).
//! Task 3 re-measured after the mechanism landed: A1/A2/A4 flipped
//! `unknown → unsat` (each z3-confirmed before the pin was written); A3 held
//! `sat`; B1 held `unknown` (the fence held).
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

/// Probe A1 — PIN (slice 34). `"a"·x = "a"·y` strips the shared head to the
/// alias residual `[x] = [y]`, which now propagates `x ≈ y` (spec §3) and
/// collides with the asserted `distinct`. Measured `unknown → unsat` at
/// Task 3; z3 confirms unsat.
#[test]
fn probe_a1_prefix_alias() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ "a" x) (str.++ "a" y)))
           (assert (distinct x y))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

/// Probe A2 — PIN (slice 34). Suffix twin of A1: tail-stripping produces the
/// same alias residual; same propagation path. Measured `unknown → unsat` at
/// Task 3; z3 confirms unsat.
#[test]
fn probe_a2_suffix_alias() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ x "a") (str.++ y "a")))
           (assert (distinct x y))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

/// Probe A3 — SAT CONTROL. The alias equation alone. A var–var merge creates
/// a string class with NO constant member (spec §5); model construction must
/// keep producing a self-check-passing model. Must stay `sat` throughout.
#[test]
fn probe_a3_sat_control() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ "a" x) (str.++ "a" y)))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"], "control: must never regress");
}

/// Probe A4 — PIN (slice 34). Chained aliasing: `x ≈ y` and `y ≈ z` compose
/// in EUF; `distinct x z` conflicts. Each propagation eagerly re-inserts its
/// own post-merge root into cond_roots (slice-33 §11.6). Measured
/// `unknown → unsat`; z3 confirms.
#[test]
fn probe_a4_chain() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (declare-fun z () String)
           (assert (= (str.++ "a" x) (str.++ "a" y)))
           (assert (= (str.++ "b" y) (str.++ "b" z)))
           (assert (distinct x z))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

/// Probe B1 — SCOPE FENCE (spec §2, banked shape). After stripping, the
/// residual is `[x] = [y, "b"]` — MULTI-ATOM and variable-bearing. The fence
/// says this must NOT propagate; the pin says the verdict must NOT flip this
/// slice. z3: unsat — the gap is real and banked WITH this measurement.
#[test]
fn probe_b1_multi_atom_fence() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ "a" x) (str.++ "a" y "b")))
           (assert (distinct x (str.++ y "b")))(check-sat)"#,
    );
    assert_eq!(
        out,
        vec!["unknown"],
        "banked shape: must NOT flip in slice 34"
    );
}
