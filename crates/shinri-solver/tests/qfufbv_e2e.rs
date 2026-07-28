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

/// Two-ary: pins that congruence fires across two applications of a 2-ary
/// symbol whose arguments are forced equal (`a = b`, so `g(a,b)` and `g(b,a)`
/// are congruent applications of `g` to the same underlying values in both
/// argument positions). NOTE: because `g(a,b)` and `g(b,a)` are the same two
/// terms merely reordered, `{a,b} = {b,a}` as an unordered pair regardless of
/// whether `a = b` holds — so this query does NOT by itself discriminate a
/// positional argument comparison from a set/multiset one; a position-blind
/// comparator also computes `cond = true` here and also returns `unsat`. See
/// `positional_argument_comparison_is_not_set_based` below for the test that
/// actually isolates positional vs. set-based comparison.
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

/// DIRECTION TEST, positional vs. set-based argument comparison. `a` and `b`
/// are DISTINCT here (unlike the sibling test above), so a correct positional
/// encoder computes `cond = false` for the `g(a,b)`/`g(b,a)` pair — position 0
/// compares `a` to `b` and they differ — leaving the results unconstrained,
/// hence `sat`. A set/multiset-based comparator instead sees the *unordered*
/// argument sets `{a,b}` and `{b,a}` as identical regardless of whether `a`
/// equals `b`, wrongly computes `cond = true`, forces the results equal, and
/// returns `unsat`. This is exactly the gap `two_ary_congruence_with_permuted_arguments`
/// cannot cover (there `a = b` is asserted, so both a positional and a
/// set-based comparator agree). MEASURED against z3 4.16.0 and cvc5 1.3.4:
/// both `sat`.
#[test]
fn positional_argument_comparison_is_not_set_based() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun g ((_ BitVec 4)(_ BitVec 4)) (_ BitVec 4))\
         (declare-fun a () (_ BitVec 4))(declare-fun b () (_ BitVec 4))\
         (assert (distinct a b))(assert (distinct (g a b) (g b a)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
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

/// DIRECTION TEST. `x` and `y` are DISTINCT, so the congruence guard `cond`
/// (args equal) blasts to false and the arm must place NO constraint on
/// `(f x)` vs `(f y)` — nothing forbids a function from differing on
/// differing arguments, so this must be `sat`. This catches a mutant that
/// drops the `cond` guard and forces the per-bit congruence clauses
/// unconditionally (congruence applied regardless of whether the arguments
/// are actually equal): that mutant would force `(f x) = (f y)`, contradicting
/// the asserted `(distinct (f x) (f y))` and flipping this to `unsat`.
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

/// Spec §2.2: a MEASURED SIDE EFFECT, not a goal. Pre-slice this printed
/// `(define-fun x () (_ BitVec 8) ?)` — the argument was never blasted, so it
/// never entered Blaster.cache and exported_var_bits could not see it.
/// Congruence forces the arguments to be blasted, so the value appears.
///
/// This does NOT make get-model complete for UF queries: `f` itself is still
/// omitted, because a function graph needs EUF congruence-class enumeration
/// (slice 43 §5, still open).
#[test]
fn argument_variables_now_get_a_model_value() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (declare-fun x () (_ BitVec 8))(assert (= (f x) #x2a))(check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    // MEASURED 2026-07-28, release binary (`./target/release/shinri`) and via
    // the identical Solver::execute path used by run_script above.
    assert_eq!(out[1], "((define-fun x () (_ BitVec 8) #x00))");
    assert!(
        !out[1].contains('?'),
        "the argument variable must have a real value, not a placeholder: {}",
        out[1]
    );
}
