//! Slice 64: script-level reproducers for the parser-coverage gaps
//! (Reals-logic numerals, `(! t :named n)`, nullary `define-sort`).

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Run an SMT-LIB script; the outcome of its last `check-sat`. Any parse
/// error fails the test: these scripts must parse completely.
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

/// QF_UFLRA/FFT/smtlib.624882 (`:status unsat`), set-info lines dropped.
#[test]
fn slice64_fft_reproducer_unsat() {
    let src = "(set-logic QF_UFLRA)(declare-sort S1 0)\
               (declare-fun f1 () S1)(declare-fun f2 () S1)(declare-fun f3 (Real) Real)\
               (declare-fun f4 () Real)(declare-fun f5 () Real)\
               (assert (not (= f1 f2)))(assert (not (not (= (f3 f4) 1.0))))\
               (assert (= f4 f5))(assert (= f4 f5))(assert (= (f3 f5) (- 1)))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Unsat);
}

/// Let-bound integer literal in QF_LRA: x = -1 pinned by a let.
#[test]
fn slice64_lra_let_bound_literal() {
    let base = "(set-logic QF_LRA)(declare-fun x () Real)\
                (assert (let ((?k (- 1))) (and (<= x ?k) (>= x ?k))))";
    assert_eq!(
        script_outcome(&format!("{base}(assert (> x (- 2)))(check-sat)")),
        SolveOutcome::Sat
    );
    assert_eq!(
        script_outcome(&format!("{base}(assert (> x 0))(check-sat)")),
        SolveOutcome::Unsat
    );
}

/// Rodin shape (QF_UF/20170829-Rodin): a named hypothesis and its use.
#[test]
fn slice64_rodin_named_hypothesis() {
    let src = "(set-logic QF_UF)(declare-fun a () Bool)(declare-fun b () Bool)\
               (assert (! (= a b) :named hyp1))(assert (not hyp1))(check-sat)";
    assert_eq!(script_outcome(src), SolveOutcome::Unsat);
}

/// QF_FP/wintersteiger/abs/abs-has-solution-8522 (`:status sat`) and its
/// `abs-has-no-other-solution-8522` sibling (`:status unsat`).
#[test]
fn slice64_wintersteiger_define_sort() {
    let base = "(set-logic QF_FP)(define-sort FPN () (_ FloatingPoint 11 53))\
                (declare-fun x () FPN)(declare-fun r () FPN)\
                (assert (= x (_ +oo 11 53)))(assert (= r (_ +oo 11 53)))";
    assert_eq!(
        script_outcome(&format!("{base}(assert (= (fp.abs x) r))(check-sat)")),
        SolveOutcome::Sat
    );
    assert_eq!(
        script_outcome(&format!("{base}(assert (not (= (fp.abs x) r)))(check-sat)")),
        SolveOutcome::Unsat
    );
}
