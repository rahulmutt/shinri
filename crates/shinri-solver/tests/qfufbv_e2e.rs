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
    // MEASURED 2026-07-27, release binary (`./target/release/shinri`) and via
    // the identical Solver::execute path used by run_script above.
    assert_eq!(out[1], "((define-fun x () (_ BitVec 8) #x00))");
    assert!(
        !out[1].contains('?'),
        "the argument variable must have a real value, not a placeholder: {}",
        out[1]
    );
}

// ---------------------------------------------------------------------------
// Redeclaration: one `SymbolId`, two different functions.
//
// `Context::declare_fun` interns by NAME and OVERWRITES `fun_sigs`, and
// `Command::DeclareFun` accepts a redeclaration silently, so applications built
// before and after a redeclaration are distinct `TermId`s carrying the SAME
// `Op::Uninterpreted(sym)` at different arities / argument sorts / widths. No
// `push`/`pop` is involved — both live in one assertion list in one
// `check_sat`.
//
// Congruence must NOT relate them: they are different functions. The blaster's
// pairing predicate (`shape_compatible`) is what keeps them apart; skipping an
// incompatible prior is sound because congruence is an ADDED constraint, so
// omitting it can only admit more models.
//
// Every verdict below was CONFIRMED against z3 4.16.0. Each of these four
// returned a wrong `unsat` (or panicked) before the shape-total filter landed.
// ---------------------------------------------------------------------------

/// Same arity, different widths, NARROW-FIRST. The 8-bit application is
/// recorded first; the 16-bit one then pairs with it. `compare::eq` loops
/// `0..x.len()` over the 8-bit prior word, so it compares it against the LOW 8
/// bits of the 16-bit argument, `cond` blasts true, and the result `zip`
/// forces `#x00 == #x01`. Wrong `unsat`; z3 4.16.0 says `sat`.
#[test]
fn redeclared_at_a_wider_signature_is_a_different_function() {
    let out = run_script(
        "(set-logic ALL)\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 16))\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (assert (= (f x) #x00))\
         (declare-fun f ((_ BitVec 16)) (_ BitVec 16))\
         (assert (= ((_ extract 7 0) y) x))\
         (assert (= ((_ extract 7 0) (f y)) #x01))(check-sat)",
    );
    assert_eq!(out.last().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// The SAME shape in the REVERSE order — 16-bit recorded first, 8-bit second.
/// Here `compare::eq`'s `0..x.len()` runs off the end of the 8-bit word: at
/// HEAD this PANICKED in the release profile ("index out of bounds: the len is
/// 8 but the index is 8", `crates/shinri-bv/src/blast/compare.rs:6`), exit 101.
/// Both orders are pinned because they fail differently. z3 4.16.0 says `sat`.
#[test]
fn redeclared_at_a_narrower_signature_is_a_different_function() {
    let out = run_script(
        "(set-logic ALL)\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 16))\
         (declare-fun f ((_ BitVec 16)) (_ BitVec 16))\
         (assert (= ((_ extract 7 0) (f y)) #x01))\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (assert (= (f x) #x00))(check-sat)",
    );
    assert_eq!(out.last().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// Different ARITY: 2-ary then redeclared 1-ary. The congruence loop walks
/// `arg_words` — the NEW arity — so the surplus prior argument was silently
/// dropped and `cond` blasted true, forcing `#x2a == #x2b`. Wrong `unsat`;
/// z3 4.16.0 says `sat`.
#[test]
fn redeclared_at_a_different_arity_is_a_different_function() {
    let out = run_script(
        "(set-logic ALL)(declare-fun x () (_ BitVec 8))\
         (declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))\
         (assert (= (f x x) #x2a))\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (assert (= (f x) #x2b))(check-sat)",
    );
    assert_eq!(out.last().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// WHY WIDTH EQUALITY IS NOT ENOUGH, and the reason `UfApp` carries
/// `arg_sorts`. `Float32` and `(_ BitVec 32)` are both 32-bit words, so arity,
/// argument width and result width all match and NO shape assertion would
/// fire — yet these are different functions, and `word_eq` compares the two
/// sorts by different semantics (`core_eq` vs. bitwise). At HEAD this returned
/// a wrong `unsat` completely silently. z3 4.16.0 says `sat`.
#[test]
fn redeclared_at_an_equal_width_different_sort_is_a_different_function() {
    let out = run_script(
        "(set-logic ALL)(declare-fun b () (_ BitVec 32))\
         (declare-fun f (Float32) (_ BitVec 32))\
         (assert (= (f ((_ to_fp 8 24) b)) #x00000000))\
         (declare-fun f ((_ BitVec 32)) (_ BitVec 32))\
         (assert (= (f b) #x00000001))(check-sat)",
    );
    assert_eq!(out.last().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

// ── Slice 45: Bool-result uninterpreted applications ─────────────────────────

/// Spec §1 Q1: congruence fires through a Bool-result predicate.
#[test]
fn equal_arguments_force_equal_predicate_results() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))\
         (assert (= x y))(assert (p x))(assert (not (p y)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// Spec §1 Q3: the converse must NOT hold — distinct arguments may disagree.
#[test]
fn distinct_arguments_leave_predicate_results_free() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))\
         (assert (p x))(assert (not (p y)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// Spec §1 Q5: the same hash-consed term at both polarities is refutable by
/// the SAT skeleton alone. Pre-slice the fence fired before the skeleton ever
/// ran, which is the sharpest illustration of the completeness gap.
#[test]
fn a_predicate_at_both_polarities_is_unsat() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p x))(assert (not (p x)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// Spec §1 Q4: a predicate coexisting with a genuine BV atom decides.
#[test]
fn a_predicate_beside_a_bv_atom_decides() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p x))(assert (bvult x #x05))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// Spec §1.1: a predicate buried inside a BV `ite`. Collection and the fence
/// both treat a collected atom as a LEAF and do not descend, so this shape is
/// invisible to their walks — it decides only because `word_norm.normalize`
/// (crates/shinri-solver/src/lib.rs:759) eliminates BV ites into a fresh
/// symbol plus a defining assertion BEFORE collection, lifting `(p x)` to the
/// assertion level. This test is what proves that lifting, rather than
/// assuming it.
#[test]
fn a_predicate_lifted_out_of_a_bv_ite_decides() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))\
         (assert (= x y))\
         (assert (= (ite (p x) #x01 #x00) #x01))\
         (assert (= (ite (p y) #x01 #x00) #x00))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// Spec §1.1, the single-term variant: one hash-consed `(p x)` used at both
/// ite branches must not mint two independent conditions.
#[test]
fn one_predicate_term_in_two_bv_ites_decides() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (= (ite (p x) #x01 #x00) #x01))\
         (assert (= (ite (p x) #x01 #x00) #x00))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// Spec §2 out-of-scope: a Bool ARGUMENT has no blastable word — a Bool child
/// can be an arbitrary formula and the blaster has no Tseitin encoder — so
/// Fence 1 still fences. Sound, deliberately incomplete.
#[test]
fn bool_argument_to_a_predicate_still_fences() {
    let out = run_script(
        "(set-logic ALL)(declare-fun p (Bool) Bool)(declare-fun c () Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p c))(assert (bvult x #x05))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}

/// Fence 1, the Bool-result sibling of `int_argument_to_a_bv_uf_fences_to_unknown`.
#[test]
fn int_argument_to_a_predicate_still_fences() {
    let out = run_script(
        "(set-logic ALL)(declare-fun p (Int) Bool)(declare-fun n () Int)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p n))(assert (bvult x #x05))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}

/// Spec §3.2(a): `Lowerer::atom` dispatched on the FIRST OPERAND's sort
/// (crates/shinri-fp/src/lower.rs:137-138, now reached only AFTER the
/// `Op::Uninterpreted` match Task 4 put in front of it), so a predicate over
/// an FP argument routed to `blast_fp_atom`, which has no
/// uninterpreted-application arm. That is a PANIC, not an `unknown` — the
/// slice-43 shape. This test is the one that catches it. MEASURED pre-fix:
/// `internal error: entered unreachable code: blast_atom: FP atom
/// Uninterpreted(SymbolId(0)) out of slice-1 scope` at
/// `crates/shinri-fp/src/lib.rs:432:18`. z3 4.16.0 and cvc5 1.3.4 both
/// `unsat`.
#[test]
fn fp_argument_predicate_congruence() {
    let out = run_script(
        "(set-logic ALL)(declare-fun p ((_ FloatingPoint 8 24)) Bool)\
         (declare-fun a () (_ FloatingPoint 8 24))\
         (declare-fun b () (_ FloatingPoint 8 24))\
         (assert (= a b))(assert (p a))(assert (not (p b)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// FP value equality is NOT bitwise: SMT-LIB `FloatingPoint` has exactly one
/// NaN VALUE across many bit patterns. `blast_uf_app` calls `sink.word_eq`,
/// which the `Lowerer` overrides with `core_eq` for exactly this reason
/// (`crates/shinri-bv/src/blast/mod.rs:184` declares `word_eq`;
/// `crates/shinri-fp/src/lower.rs:97` is the `core_eq` override). A bitwise
/// comparison would UNDER-trigger congruence here and leave the results free,
/// so this comes back `sat` on a wrong implementation.
///
/// DO NOT "correct" this expectation to `sat` against z3. MEASURED: cvc5 1.3.4
/// `unsat`, z3 4.16.0 `sat` — and **z3 is wrong here**. Asked for its model z3
/// returns `p := λx. true` and then evaluates `(p b)` to `true`, contradicting
/// the asserted `(not (p b))`: the model does not satisfy the input. z3 also
/// agrees the arguments are equal (`fp.isNaN a ∧ fp.isNaN b ∧ a ≠ b` is `unsat`
/// for z3) and returns `unsat` once `(= a b)` is stated syntactically, so the
/// defect is its FP+UF congruence closure missing an ENTAILED equality.
/// SMT-LIB `FloatingPoint` has exactly one NaN value, so `unsat` is the ground
/// truth.
#[test]
fn nan_arguments_are_congruent_for_a_predicate() {
    let out = run_script(
        "(set-logic ALL)(declare-fun p ((_ FloatingPoint 8 24)) Bool)\
         (declare-fun a () (_ FloatingPoint 8 24))\
         (declare-fun b () (_ FloatingPoint 8 24))\
         (assert (fp.isNaN a))(assert (fp.isNaN b))\
         (assert (p a))(assert (not (p b)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// Slice 45 widened `collect_bv_atoms`, which changes the INPUT SET of
/// `fp_stage::bridge_admissible` (`fp_stage.rs:437-455`): it requires every
/// atom outside `fp_atoms ∪ bv_atoms` to be a pure-LRA-Real atom, so moving
/// Bool-result applications INTO `bv_atoms` lets it return `true` where it
/// returned `false`. That matters because `bridge` both suppresses the
/// crossing-conversion `Unknown` (`lib.rs:999-1001`) and SKIPS
/// `has_non_bvfp_theory_atom` entirely (`lib.rs:1058`, `if !bridge && …`) —
/// a fence-skipping gate whose input set this slice changed.
///
/// This probe pins that the newly-admitted path is sound. It also proves the
/// gate actually flipped rather than merely deciding: if `bridge` were false,
/// `has_non_bvfp_theory_atom` would run and fence on the two Real atoms
/// (neither is an FP atom nor a BV atom), returning `unknown` — which is
/// exactly what this query returns on pre-slice `bv_stage.rs`. z3 4.16.0 and
/// cvc5 1.3.4 both say `unsat`.
#[test]
fn a_predicate_alongside_the_real_bridge_decides() {
    let out = run_script(
        "(set-logic ALL)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))\
         (declare-fun a () Float32)(declare-fun r () Real)\
         (assert (= x y))(assert (p x))(assert (not (p y)))\
         (assert (= r (fp.to_real a)))(assert (> r 0.0))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

/// The ABV path shares `blast_bv_atom` through a PERSISTENT blaster that
/// survives refinement rounds (crates/shinri-solver/src/abv_stage.rs:351),
/// unlike `lower`'s one-shot. The `UfApp` registry must survive with it, or a
/// predicate application registered in round 1 will not be paired with one
/// blasted in round 2.
///
/// The array abstraction replaces `select`/`store` with fresh BV symbols
/// BEFORE `collect_bv_atoms` runs, so the predicate's argument is already a
/// plain word by the time the arm sees it.
///
/// Reaching this at all required widening `abv_stage::fenced` (slice 45 Task 5,
/// authorized after measurement): that fence walks the RAW assertions at
/// `lib.rs:903`, before the abstraction exists, so it never sees
/// `collect_bv_atoms`' output and Task 3's widening of the collector could not
/// reach this path. Pre-widening this query returned `unknown`. z3 4.16.0 and
/// cvc5 1.3.4 both answer `unsat`.
#[test]
fn predicate_over_an_array_read_decides() {
    let out = run_script(
        "(set-logic QF_AUFBV)\
         (declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))\
         (declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun i () (_ BitVec 4))(declare-fun j () (_ BitVec 4))\
         (assert (= i j))\
         (assert (p (select a i)))(assert (not (p (select a j))))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
}

// ── Slice 45 Task 6: the Fence-1 blastability audit ──────────────────────────
//
// Fence 1 (`bv_stage::uf_args_supported`) originally checked argument SORTS
// only. A BitVec-sorted `(select a i)` passed by sort while `blast_bv_word`
// has no `Select` arm. The audit measured this on the release AND debug
// binaries, for both result sorts, at commit 99b282af.
//
// The routing predicate that decides which way a query goes is
// `abv_stage::uses_arrays_over_bv` (`lib.rs:902`): it is true only for a
// `select`/`store`/array-(dis)equality whose array operand is BV-INDEXED and
// BV-VALUED. True → the ABV path, where `shinri_abv::abstract_arrays`
// substitutes a fresh BV read symbol for every `select` (its `collect`/`subst`
// walk children generically, so one buried in a UF application's arguments is
// substituted too) before `collect_bv_atoms` ever sees the abstraction.
// False → the pure-BV / FP paths, which have no array machinery at all.
//
// So the exposure is exactly the array shapes that predicate does NOT claim.
// The four pins below cover both sides of it for both result sorts.

/// ABV side, BV result (slice 44's shipped arm). `uses_arrays_over_bv` is TRUE
/// (the array is `(Array (_ BitVec 4) (_ BitVec 8))`), so the read is
/// abstracted to a fresh BV symbol before blasting. Measured `sat` on both
/// binaries; z3 4.16.0 and cvc5 1.3.4 both say `sat`.
///
/// This pin is what makes a future narrowing of `uses_arrays_over_bv` loud:
/// if such a query ever stopped routing to the ABV path, Fence 1's
/// blastability check would fence it and this would flip to `unknown`.
#[test]
fn a_bv_array_read_argument_is_abstracted_and_decides() {
    let out = run_script(
        "(set-logic QF_AUFBV)\
         (declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (declare-fun i () (_ BitVec 4))\
         (assert (= (f (select a i)) #x2a))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// ABV side, Bool result (slice 45's new arm). Same routing, same abstraction.
/// Measured `sat` on both binaries; z3 4.16.0 and cvc5 1.3.4 both say `sat`.
/// On pre-slice `main` (e1baa3bb) this was `unknown` — the slice-45 gain.
#[test]
fn a_bv_array_read_argument_to_a_predicate_is_abstracted_and_decides() {
    let out = run_script(
        "(set-logic QF_AUFBV)\
         (declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))\
         (declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun i () (_ BitVec 4))\
         (assert (p (select a i)))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

/// Non-ABV side, BV result. The array is `(Array Int (_ BitVec 8))`, so
/// `uses_arrays_over_bv` is FALSE and the query takes the pure-BV path — where
/// nothing abstracts the read away. The read is BitVec-8-SORTED, so Fence 1's
/// sort check admitted it and the blaster then hit
/// `unreachable!("non-BV builtin reached blast_word")`
/// (`crates/shinri-bv/src/blast/mod.rs:624`) on BOTH profiles.
///
/// This shape PREDATES slice 45: pre-slice `main` (e1baa3bb) panicked on it
/// too, through slice 44's BitVec-result arm. Task 6's blastability check
/// turns that panic into a sound `unknown`.
#[test]
fn a_foreign_array_read_argument_fences_to_unknown() {
    let out = run_script(
        "(set-logic ALL)\
         (declare-fun a () (Array Int (_ BitVec 8)))\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (declare-fun i () Int)\
         (assert (= (f (select a i)) #x2a))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}

/// Non-ABV side, Bool result — the one case slice 45 itself regressed, and the
/// reason this audit ended in a code change rather than an unreachability
/// argument.
///
/// Pre-slice `main` (e1baa3bb) answered a sound `unknown` here: the Bool-result
/// application was NOT a collected BV atom, so `has_non_bv_theory_atom` treated
/// it as a foreign Bool-sorted atom and fenced. Task 3 widened
/// `collect_bv_atoms` to collect it — which makes it a collected atom, i.e. a
/// LEAF that `has_non_bv_theory_atom` no longer descends into — so the foreign
/// `select` in its arguments stopped being seen and the query PANICKED on both
/// profiles. Fence 1's blastability check restores the `unknown`.
#[test]
fn a_foreign_array_read_argument_to_a_predicate_fences_to_unknown() {
    let out = run_script(
        "(set-logic ALL)\
         (declare-fun a () (Array Int (_ BitVec 8)))\
         (declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun i () Int)\
         (assert (p (select a i)))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}

// ── Slice 45 Task 6, review round 1: the FP→BV conversion half of Fence 1 ────
//
// `Select` is not the only BV-SORTED head the bare blaster lacks an arm for.
// Enumerating `BuiltinOp` against `blast_bv_word`'s dispatch, the BV-sorted
// heads with no arm are `Select`, `Ite`, `FpToUbv` and `FpToSbv`. `Ite` is
// eliminated unconditionally by `word_norm.normalize` (`lib.rs:759`) before any
// routing decision; `Select` is covered by the four pins above; the FP→BV
// conversions are these two.
//
// The discriminator is `allow_fp_args`, i.e. "does this path's sink have an
// arm". `Lowerer::word` intercepts `FpToUbv`/`FpToSbv` and routes them to
// `blast_fp_to_bv` (`crates/shinri-fp/src/lower.rs:52-73`); a bare
// `shinri_bv::Blaster` does not. The ABV path uses a bare `Blaster` and passes
// `allow_fp_args = false` (`lib.rs:910`), so it must fence — and, crucially,
// its gate at `lib.rs:902` runs BEFORE any FP routing and `return`s in every
// arm, so `solver_uses_fp` never gets to divert such a query to the FP path.

/// The ABV path with an FP→BV conversion inside a UF argument. The argument is
/// BitVec-8-SORTED and contains no `select`, so neither the sort check nor the
/// array half of the blastability check catches it; `abv_stage::fenced` cannot
/// either, because `(fp.to_ubv rm x)` is not Bool-sorted and `walk_fence` only
/// descends through it into constants.
///
/// Measured at commit 4a3701e8 (the pre-fix tip of this task): PANIC on BOTH
/// the release and the debug binary —
/// `unreachable!("non-BV builtin reached blast_word")`,
/// `crates/shinri-bv/src/blast/mod.rs:624`. Now a sound `unknown`.
/// z3 4.16.0 and cvc5 1.3.4 both answer `sat`, so this is a completeness cost
/// on a shape that previously crashed, not a lost verdict.
#[test]
fn an_fp_to_bv_argument_fences_on_the_array_path() {
    let out = run_script(
        "(set-logic ALL)\
         (declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))\
         (declare-fun i () (_ BitVec 4))(declare-fun x () Float32)\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (assert (= (select a i) (f ((_ fp.to_ubv 8) RNE x))))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}

/// The other direction, and the reason the fence above had to be GATED rather
/// than unconditional. The same conversion in the same argument position on the
/// FP/mixed path decides `sat` — `Lowerer::word` has the arm. Rejecting
/// `FpToUbv`/`FpToSbv` outright would flip this to `unknown`: a decided →
/// unknown regression, forbidden with no named-exception list.
///
/// Measured `sat` on both binaries before and after the round-1 fix; z3 4.16.0
/// and cvc5 1.3.4 both answer `sat`.
#[test]
fn an_fp_to_bv_argument_still_decides_on_the_fp_path() {
    let out = run_script(
        "(set-logic ALL)(declare-fun x () Float32)\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
         (assert (= (f ((_ fp.to_ubv 8) RNE x)) #x2a))(check-sat)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
}

// ---------------------------------------------------------------------------
// Spec §6.5 / §8.3 — the model channel, MEASURED not predicted.
// ---------------------------------------------------------------------------

/// Spec §6.5: measured, not predicted. Pre-slice this query never got past the
/// `bv_stage` foreign-theory fence, so neither channel had ever been observed
/// on a non-nullary Bool-result application. Measured on the RELEASE binary at
/// commit 7b69df2f (the branch tip before this task), verbatim:
///
/// ```text
/// sat
/// (((p x) ?))
/// ((define-fun x () (_ BitVec 8) #x00))
/// ```
///
/// Three separate facts, pinned separately:
///
/// 0. **The query decides `sat` at all.** Pre-slice it was `unknown` (spec §1,
///    Q2), so `get-value` returned the `model is not available` error
///    (`lib.rs:438`) and neither channel below was observable. That is why
///    this had to be measured after the slice rather than predicted before it.
///
/// 1. **The label renders, the value does not.** `display_term`
///    (`crates/shinri-solver/src/tseitin.rs:483`) renders the application
///    structurally, so the label is `(p x)`. `format_value` (`lib.rs:585`)
///    then returns `None` — it resolves a *0-arity* symbol through
///    `last_model`, and `(p x)` is not one — and `get-value` prints the
///    established `?` placeholder (`lib.rs:453`). That is the correct
///    rendering of "no value": slice 43's lesson is that absence must never be
///    dressed up as a confident default, and `?` is exactly the visible
///    placeholder that refusal uses. This test pins that the value channel
///    does NOTHING here, plainly — it is not an aspiration that it should.
///
/// 2. **`get-model` still omits `p`.** `format_model` filters
///    `d.arity == 0` (`lib.rs:540`), so an arity-1 symbol is structurally
///    absent regardless of what the blaster learned. A function graph needs
///    congruence-class enumeration (slice 43 §5, still open); slice 45 does
///    not change this and the spec's §2 records it as deliberately out of
///    scope. The argument `x` DOES get a value, by the slice 44 §7.5
///    mechanism: congruence forces the argument word to be blasted, so it
///    enters `Blaster.cache` and reaches `exported_var_bits`.
///
/// The concrete witness `#x00` is not pinned — `(p x)` constrains nothing
/// about `x`, so any 8-bit value is a legitimate model and pinning the
/// solver's current choice would be pinning an implementation detail.
#[test]
fn get_value_on_a_predicate_application() {
    let out = run_script(
        "(set-logic QF_UFBV)(declare-fun p ((_ BitVec 8)) Bool)\
         (declare-fun x () (_ BitVec 8))\
         (assert (p x))(check-sat)(get-value ((p x)))(get-model)",
    );
    assert_eq!(
        out.len(),
        3,
        "expected sat + get-value + get-model: {out:?}"
    );
    assert_eq!(out[0].as_str(), "sat", "got {out:?}");

    // Fact 1: the label is structural, the value is the `?` placeholder.
    assert_eq!(out[1].as_str(), "(((p x) ?))", "got {out:?}");

    // Fact 2: `get-model` omits the arity-1 symbol `p` entirely, and gives the
    // argument a value.
    assert!(
        !out[2].contains("define-fun p"),
        "get-model must still omit the arity-1 symbol p: {out:?}"
    );
    assert!(
        out[2].starts_with("((define-fun x () (_ BitVec 8) #x"),
        "the argument x must still get a concrete 8-bit value: {out:?}"
    );
}
