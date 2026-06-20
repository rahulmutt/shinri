//! End-to-end QF_LRA tests for shinri-solver with the Arith theory wired in.

use shinri_core::{BuiltinOp, Op};
use shinri_num::Rational;
use shinri_solver::{SolveOutcome, Solver};
use shinri_theory::types::ModelVal;

/// Convenience: declare a Real-sorted constant.
fn real_const(s: &mut Solver, name: &str) -> shinri_core::TermId {
    let real = s.real_sort();
    s.declare_const(name, real)
}

/// Build a numeral with the given integer value over Real sort.
fn real_num(s: &mut Solver, n: i128) -> shinri_core::TermId {
    let real = s.real_sort();
    s.numeral(Rational::from_int(n.into()), real)
}

/// 1. Pure QF_LRA sat: 0 < x < 1
#[test]
fn pure_lra_sat() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let zero = real_num(&mut s, 0);
    let one = real_num(&mut s, 1);
    // x > 0
    let gt0 = s.app(Op::Builtin(BuiltinOp::Gt), &[x, zero]);
    // x < 1
    let lt1 = s.app(Op::Builtin(BuiltinOp::Lt), &[x, one]);
    s.assert(gt0);
    s.assert(lt1);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

/// 2. Pure QF_LRA unsat: 0 < x < 1 AND x > 2
#[test]
fn pure_lra_unsat() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let zero = real_num(&mut s, 0);
    let one = real_num(&mut s, 1);
    let two = real_num(&mut s, 2);
    // x > 0
    let gt0 = s.app(Op::Builtin(BuiltinOp::Gt), &[x, zero]);
    // x < 1
    let lt1 = s.app(Op::Builtin(BuiltinOp::Lt), &[x, one]);
    // x > 2
    let gt2 = s.app(Op::Builtin(BuiltinOp::Gt), &[x, two]);
    s.assert(gt0);
    s.assert(lt1);
    s.assert(gt2);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// 3. Arithmetic equality model: x = y, x = 2 → Sat, get_value(y) == 2
#[test]
fn arith_equality_model() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let y = real_const(&mut s, "y");
    let two = real_num(&mut s, 2);
    // (= x y)
    let xy = s.eq(x, y);
    // (= x 2)
    let x2 = s.eq(x, two);
    s.assert(xy);
    s.assert(x2);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
    assert_eq!(
        s.get_value(y),
        Some(ModelVal::Num(Rational::from_int(2i128.into())))
    );
}

/// 4. Arith disequality sat: x ≠ 0 → Sat
#[test]
fn arith_disequality_sat() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let zero = real_num(&mut s, 0);
    // (not (= x 0))  →  after lower: (not (and (Le x 0) (Ge x 0)))
    //                             →  (or (not (Le x 0)) (not (Ge x 0)))
    //                             →  x > 0 ∨ x < 0 : satisfiable
    let eq0 = s.eq(x, zero);
    let neq0 = s.app(Op::Builtin(BuiltinOp::Not), &[eq0]);
    s.assert(neq0);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

/// 5. Arith disequality forced unsat: x = 0 AND x ≠ 0
#[test]
fn arith_disequality_forced_unsat() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let zero = real_num(&mut s, 0);
    let eq0 = s.eq(x, zero);
    let neq0 = s.app(Op::Builtin(BuiltinOp::Not), &[eq0]);
    s.assert(eq0);
    s.assert(neq0);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// 6. Distinct reals unsat: (distinct a b c) AND (= a b) → Unsat
#[test]
fn distinct_reals_unsat() {
    let mut s = Solver::new();
    let a = real_const(&mut s, "a");
    let b = real_const(&mut s, "b");
    let c = real_const(&mut s, "c");
    // (distinct a b c)  →  lower to (and (distinct a b) (distinct a c) (distinct b c))
    //                              →  each pair lower to (or (Lt ai bi) (Gt ai bi))
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[a, b, c]);
    // (= a b)  →  lower to (and (Le a b) (Ge a b))
    let eq_ab = s.eq(a, b);
    s.assert(dist);
    s.assert(eq_ab);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// 8. N-ary real equality soundness: (= x y z) AND (not (= x z)) → Unsat
///
/// Pre-fix: the rewrite truncated (= x y z) to (and (Le x y)(Ge x y)),
/// dropping z entirely, leaving z free → wrongly returned Sat.
/// Post-fix: all adjacent pairs are chained, so x==y and y==z are both
/// asserted, forcing x==z, which contradicts (not (= x z)) → Unsat.
#[test]
fn nary_real_equality_is_transitive() {
    let mut s = Solver::new();
    let r = s.real_sort();
    let x = s.declare_const("x", r);
    let y = s.declare_const("y", r);
    let z = s.declare_const("z", r);
    // (= x y z)  — n-ary equality; the bug dropped z
    let eq3 = s.app(Op::Builtin(BuiltinOp::Eq), &[x, y, z]);
    // (not (= x z))
    let xz = s.eq(x, z);
    let nxz = s.app(Op::Builtin(BuiltinOp::Not), &[xz]);
    s.assert(eq3);
    s.assert(nxz);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// 7. Variable-disjoint UF + LRA → Sat (fence removed in Task 12b).
///
/// `(= p:U q:U) ∧ (> x:Real 0)` shares NO terms between EUF (sort U) and Arith
/// (Real). Both halves are independently satisfiable (p=q in EUF, x>0 in arith)
/// and disjoint ⇒ the combination is Sat. The former `saw_euf_nonreal &&
/// saw_arith` fence over-approximated this to Unknown; bidirectional N-O makes
/// the combination sound, so it now returns Sat. (Was `mixed_uf_lra_is_unknown`.)
#[test]
fn disjoint_uf_lra_is_sat() {
    let mut s = Solver::new();
    // Uninterpreted sort U with consts p, q
    let u = s.declare_sort("U");
    let p = s.declare_const("p", u);
    let q = s.declare_const("q", u);
    // (= p q)  →  EUF atom
    let pq = s.eq(p, q);
    // Real x with (> x 0)  →  Arith atom
    let x = real_const(&mut s, "x");
    let zero = real_num(&mut s, 0);
    let gt0 = s.app(Op::Builtin(BuiltinOp::Gt), &[x, zero]);
    s.assert(pq);
    s.assert(gt0);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}
