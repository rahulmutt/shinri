//! Slice 34 probes (spec §7). These pin the alias-propagation frontier.
//!
//! Written BEFORE the implementation as a measured baseline: A1/A2/A4 record
//! the engine's current sound-but-needless `unknown` (z3 says `unsat` for all
//! three), A3 is the SAT control, and B1 pins the §2 scope fence (the
//! multi-atom variable-bearing shape, banked — must NOT flip this slice).
//! Task 3 re-measures after the mechanism lands and flips A1/A2/A4 only after
//! oracle confirmation.
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

/// Probe A1 — BASELINE. `"a"·x = "a"·y` strips the shared head to the alias
/// residual `[x] = [y]`, which today falls through to F-split → dedup →
/// `Saturated` → a sound `unknown`. z3: unsat (cancellation entails x = y).
#[test]
fn probe_a1_prefix_alias() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ "a" x) (str.++ "a" y)))
           (assert (distinct x y))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "baseline; Task 3 flips this pin");
}

/// Probe A2 — BASELINE. Suffix twin of A1: tail-stripping produces the same
/// alias residual. z3: unsat.
#[test]
fn probe_a2_suffix_alias() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ x "a") (str.++ y "a")))
           (assert (distinct x y))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "baseline; Task 3 flips this pin");
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

/// Probe A4 — BASELINE. Chained aliasing: two alias merges (`x ≈ y`, `y ≈ z`)
/// must compose so `distinct x z` conflicts. Exercises the §11.6 per-merge
/// eager cond_roots re-insertion on chained propagations (spec §9). z3: unsat.
#[test]
fn probe_a4_chain() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (declare-fun z () String)
           (assert (= (str.++ "a" x) (str.++ "a" y)))
           (assert (= (str.++ "b" y) (str.++ "b" z)))
           (assert (distinct x z))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "baseline; Task 3 flips this pin");
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
