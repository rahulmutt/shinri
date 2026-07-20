//! Slice 33 probes (spec §7). These pin the resolver-propagation frontier.
//!
//! Written BEFORE the implementation as a measured baseline: every probe here
//! records what the engine does TODAY. Task 6 updates the ones that actually
//! flip, and only after z3 confirms the new verdict.
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

/// Probe E — the empty string is a SOURCE-LEVEL literal, so there is nothing to
/// ground. Predicted (spec §7) to flip to `unsat` once the resolver can
/// propagate `[y] = ["ab"]`.
#[test]
fn probe_e_empty_literal_concat() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun y () String)
           (assert (= (str.++ "" y) "ab"))(assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "BASELINE (pre-slice-33)");
}

/// Probe G — `x = ""` asserted by hand, strictly more than any grounding
/// mechanism could achieve. Predicted to flip to `unsat`.
#[test]
fn probe_g_asserted_empty_var() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= x ""))(assert (= (str.++ x y) "ab"))
           (assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "BASELINE (pre-slice-33)");
}

/// Probe C — needs `len(x) = 0 → x ≈ ""` grounding, i.e. the RETRACTED wall-3
/// seam. Predicted to stay `unknown`. That is a STATED NON-GOAL (spec §7), not
/// a failure: this assertion must still read `unknown` at the end of slice 33.
#[test]
fn probe_c_len_zero_var() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.len x) 0))(assert (= (str.++ x y) "ab"))
           (assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "NON-GOAL: out of scope for slice 33");
}

/// Probe F — control. The contradiction machinery is intact once the equality
/// exists. This must stay `unsat` throughout the slice.
#[test]
fn probe_f_control_direct_contradiction() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun y () String)
           (assert (= y "ab"))(assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"], "control: must never regress");
}
