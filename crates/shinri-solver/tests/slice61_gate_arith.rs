//! Slice 61 (R11): the model gate evaluates length arithmetic from the
//! string values, so a seed that changes a leaf's length cannot be hidden
//! behind the arith model's value for `(+ (str.len x) (str.len y))`.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

fn run(src: &str) -> SolveOutcome {
    let mut s = Solver::new();
    let mut p = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(result) = p.next_command(s.ctx_mut()) {
        let cmd = result.expect("parse");
        match s.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    outcome
}

const DECLS: &str = "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)";

#[test]
fn lensum_concat_membership_is_not_sat() {
    // z3: unsat (|xy| is even, the sum is 3).
    let src = format!(
        "{DECLS}(assert (str.in_re (str.++ x y) (re.* (str.to_re \"ab\"))))\
         (assert (= (+ (str.len x) (str.len y)) 3))(check-sat)"
    );
    assert_ne!(run(&src), SolveOutcome::Sat);
}

#[test]
fn lensum_bare_memberships_is_not_sat() {
    // z3: unsat (each length is even, the sum is 3).
    let src = format!(
        "{DECLS}(assert (str.in_re x (re.* (str.to_re \"ab\"))))\
         (assert (str.in_re y (re.* (str.to_re \"ab\"))))\
         (assert (= (+ (str.len x) (str.len y)) 3))(check-sat)"
    );
    assert_ne!(run(&src), SolveOutcome::Sat);
}

#[test]
fn lensum_even_sibling_stays_sat() {
    let src = format!(
        "{DECLS}(assert (str.in_re (str.++ x y) (re.* (str.to_re \"ab\"))))\
         (assert (= (+ (str.len x) (str.len y)) 4))(check-sat)"
    );
    assert_eq!(run(&src), SolveOutcome::Sat);
}
