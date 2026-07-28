//! Slice 44 — UF/BV congruence in the bit-blaster.
//!
//! Task 2 pins Fence 1: an uninterpreted application with a BV result sort
//! whose argument has no blastable word must fence to `unknown` rather than
//! reach the congruence arm (Task 3). Tasks 4, 5, 6 and 7 append more tests
//! to this file.

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

/// Fence 1 (spec §4): an Int-sorted argument has no blastable word, so the
/// query fences to a SOUND `unknown` rather than reaching the congruence arm.
/// This is the spec §2.1 named decided → unknown exception.
#[test]
fn int_argument_to_a_bv_uf_fences_to_unknown() {
    let out = run_script(
        "(set-logic ALL)(declare-fun h (Int) (_ BitVec 8))(declare-fun n () Int)\
         (assert (= (h n) #x2a))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}

/// Fence 2 (spec §4): an encoding past the calibrated budget fences to a SOUND
/// `unknown` rather than hanging. Generated rather than written out, because
/// the application count needed to exceed the budget is large by construction.
#[test]
fn encoding_past_the_budget_fences_to_unknown() {
    let k = 1500; // pairs(1500) * 96 = 1_124_250 * 96 = 107_928_000, 11.6x
                  // the calibrated UF_CONGRUENCE_BUDGET (9_271_680, k=440 --
                  // see bv_stage.rs) -- still far past.
    let mut src = String::from(
        "(set-logic QF_UFBV)\
         (declare-fun g ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))",
    );
    for i in 0..k {
        src.push_str(&format!("(declare-fun v{i} () (_ BitVec 32))"));
    }
    for i in 0..k {
        src.push_str(&format!("(assert (= (g v{i} v{i}) #x00000000))"));
    }
    src.push_str("(check-sat)");
    let out = run_script(&src);
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}

/// The FP/mixed path shares blast_bv_word, so it had the identical defect.
/// MEASURED pre-slice: shinri `sat`, z3 `unsat`.
#[test]
fn fp_argument_congruence_on_the_mixed_path() {
    let out = run_script(
        "(set-logic ALL)(declare-fun k (Float32) (_ BitVec 8))\
         (declare-fun f () Float32)(declare-fun g () Float32)\
         (assert (= f g))(assert (distinct (k f) (k g)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// core_eq, not bitwise: SMT-LIB Float has ONE NaN value across many bit
/// patterns, so two NaN arguments must trigger congruence. A bitwise word_eq
/// leaves this `sat`.
#[test]
fn nan_arguments_trigger_congruence() {
    let out = run_script(
        "(set-logic ALL)(declare-fun k (Float32) (_ BitVec 8))\
         (declare-fun f () Float32)(declare-fun g () Float32)\
         (assert (fp.isNaN f))(assert (fp.isNaN g))\
         (assert (distinct (k f) (k g)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// The canonical case. MEASURED pre-slice: shinri `sat`; z3 `unsat`; cvc5 `unsat`.
#[test]
fn one_ary_congruence() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))\
         (assert (= x y))(assert (distinct (f x) (f y)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// Two-ary with the arguments permuted — congruence must compare argument
/// words POSITIONALLY, not as a set. A position-blind encoding leaves this sat.
#[test]
fn two_ary_congruence_with_permuted_arguments() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun g ((_ BitVec 4)(_ BitVec 4)) (_ BitVec 4))\
         (declare-fun a () (_ BitVec 4))(declare-fun b () (_ BitVec 4))\
         (assert (= a b))(assert (distinct (g a b) (g b a)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// The congruence must reach a BV PREDICATE over two applications, not just an
/// equality between them.
#[test]
fn congruence_reaches_a_bv_predicate() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (= x y))(assert (bvult (f x) (f y)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// ...and through a structural op applied to the results.
#[test]
fn congruence_survives_extract_over_the_results() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 8))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (= x y))\
         (assert (distinct ((_ extract 3 0) (f x)) ((_ extract 3 0) (f y))))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// The ABV stage builds its own Blaster, so it hits the same arm.
/// MEASURED pre-slice: shinri `sat`; z3 `unsat`; cvc5 `unsat`.
#[test]
fn congruence_on_the_abv_path() {
    let out = run_script(
        "(set-logic QF_AUFBV)(declare-fun a () (Array (_ BitVec 4)(_ BitVec 8)))\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (declare-fun i () (_ BitVec 4))(declare-fun j () (_ BitVec 4))\
         (assert (= i j))(assert (distinct (f (select a i)) (f (select a j))))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// DIRECTION TEST. Congruence is an IMPLICATION, not a biconditional. An
/// over-strong encoding (`args equal <-> results equal`) makes this `unsat`.
/// It must be `sat`: nothing forbids a function from differing on differing
/// arguments.
#[test]
fn distinct_arguments_may_give_distinct_results() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (distinct x y))(assert (distinct (f x) (f y)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// THE SHARPER DIRECTION TEST. A function may legitimately AGREE on distinct
/// arguments. An inverted encoding (`args differ -> results differ`) fails
/// exactly here and nowhere else — the test above would still pass under it.
#[test]
fn distinct_arguments_may_still_give_equal_results() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (distinct x y))(assert (= (f x) (f y)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// Pins Task 3's load-bearing step order: the inner application is registered
/// while the outer one's argument is lowered, so `prior` must be read AFTER
/// argument blasting. Reading it first drops the inner/outer pair and this
/// returns `sat` — silent incompleteness, no crash, no other symptom.
#[test]
fn nested_application_congruence() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\
         (declare-fun x () (_ BitVec 4))(declare-fun y () (_ BitVec 4))\
         (assert (= x y))(assert (distinct (f (f x)) (f (f y))))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}
