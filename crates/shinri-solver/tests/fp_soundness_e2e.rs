//! Slice 64 amendment A (spec §3.5, §7.5): FP soundness fixes exposed once
//! `define-sort` let QF_FP files parse.

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Run an SMT-LIB script; the outcome of its last `check-sat`. Any parse
/// error fails the test.
fn script_outcome(src: &str) -> SolveOutcome {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut outcome = None;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.unwrap_or_else(|e| panic!("parse error: {e:?}"));
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = Some(SolveOutcome::Sat),
            CommandResponse::Unsat => outcome = Some(SolveOutcome::Unsat),
            CommandResponse::Unknown => outcome = Some(SolveOutcome::Unknown),
            _ => {}
        }
    }
    outcome.expect("script has a check-sat")
}

const F64: &str = "(_ FloatingPoint 11 53)";

/// §3.5.1: both zeros are admissible results of a ±0 tie, for both orders
/// and both operators.
#[test]
fn slice64a_zero_tie_admits_both_results() {
    for op in ["fp.min", "fp.max"] {
        for (xv, yv) in [("-zero", "+zero"), ("+zero", "-zero")] {
            for r in ["+zero", "-zero"] {
                let src = format!(
                    "(set-logic QF_FP)(declare-fun x () {F64})(declare-fun y () {F64})\
                     (assert (= x (_ {xv} 11 53)))(assert (= y (_ {yv} 11 53)))\
                     (assert (= ({op} x y) (_ {r} 11 53)))(check-sat)"
                );
                assert_eq!(
                    script_outcome(&src),
                    SolveOutcome::Sat,
                    "{op} {xv} {yv} -> {r}"
                );
            }
        }
    }
}

/// §3.5.1: fp.min/fp.max are functions — two applications to equal
/// arguments must agree, so per-occurrence free choice would be unsound.
#[test]
fn slice64a_zero_tie_is_functionally_consistent() {
    for op in ["fp.min", "fp.max"] {
        let src = format!(
            "(set-logic QF_FP)(declare-fun a () {F64})(declare-fun b () {F64})\
             (declare-fun c () {F64})(declare-fun d () {F64})\
             (assert (= a (_ -zero 11 53)))(assert (= b (_ +zero 11 53)))\
             (assert (= c (_ -zero 11 53)))(assert (= d (_ +zero 11 53)))\
             (assert (not (= ({op} a b) ({op} c d))))(check-sat)"
        );
        assert_eq!(script_outcome(&src), SolveOutcome::Unsat, "{op}");
    }
}

/// QF_FP/wintersteiger/min/min-has-solution-13472 (`:status sat`).
#[test]
fn slice64a_min_has_solution_13472() {
    let src = "(set-logic QF_FP)(define-sort FPN () (_ FloatingPoint 11 53))\
        (declare-fun x () FPN)(declare-fun y () FPN)(declare-fun r () FPN)\
        (assert (= x (fp #b1 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))\
        (assert (= y (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))\
        (assert (= r (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)))\
        (assert (= (fp.min x y) r))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Sat);
}
