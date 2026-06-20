//! End-to-end QF_UFLRA tests for the bidirectional Nelson-Oppen wiring
//! (Task 12b). These exercise Arith↔EUF entailed-equality propagation through
//! the full solver stack.

use shinri_core::{BuiltinOp, Op};
use shinri_num::Rational;
use shinri_solver::{SolveOutcome, Solver};

fn real_const(s: &mut Solver, name: &str) -> shinri_core::TermId {
    let real = s.real_sort();
    s.declare_const(name, real)
}

fn real_num(s: &mut Solver, n: i128) -> shinri_core::TermId {
    let real = s.real_sort();
    s.numeral(Rational::from_int(n.into()), real)
}

/// `f : Real -> Real` declared symbol.
fn real_fun1(s: &mut Solver, name: &str) -> shinri_core::SymbolId {
    let real = s.real_sort();
    s.declare_fun(name, &[real], real)
}

/// THE discriminating witness: `x>=5 ∧ x<=5 ∧ distinct(f x)(f 5)` ⇒ UNSAT.
/// x is pinned to 5 by the two bounds; numeral 5 is pinned by R4; arith entails
/// x=5; EUF closes f(x)=f(5), contradicting the distinct. (Was wrongly sat.)
#[test]
fn witness_bounds_pinned_unsat() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let five = real_num(&mut s, 5);
    let f = real_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let f5 = s.app(Op::Uninterpreted(f), &[five]);
    // x >= 5
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[x, five]);
    // x <= 5
    let le = s.app(Op::Builtin(BuiltinOp::Le), &[x, five]);
    // distinct (f x) (f 5)
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, f5]);
    s.assert(ge);
    s.assert(le);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Non-fixed entailed equality: x<=y ∧ y<=x ∧ distinct(f x)(f y) ⇒ UNSAT.
#[test]
fn nonfixed_entailed_unsat() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let y = real_const(&mut s, "y");
    let f = real_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let le1 = s.app(Op::Builtin(BuiltinOp::Le), &[x, y]);
    let le2 = s.app(Op::Builtin(BuiltinOp::Le), &[y, x]);
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, fy]);
    s.assert(le1);
    s.assert(le2);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Congruence-derived (EUF→arith): g:Real→Real,
/// (= a b) ∧ (= (g a) p) ∧ (= (g b) q) ∧ (>= (- p q) 1) ⇒ UNSAT.
/// a=b ⟹ g(a)=g(b) (EUF congruence) ⟹ p=q must reach arith, contradicting p-q>=1.
#[test]
fn congruence_derived_unsat() {
    let mut s = Solver::new();
    let a = real_const(&mut s, "a");
    let b = real_const(&mut s, "b");
    let p = real_const(&mut s, "p");
    let q = real_const(&mut s, "q");
    let g = real_fun1(&mut s, "g");
    let ga = s.app(Op::Uninterpreted(g), &[a]);
    let gb = s.app(Op::Uninterpreted(g), &[b]);
    let ab = s.eq(a, b);
    let gap = s.eq(ga, p);
    let gbq = s.eq(gb, q);
    // (>= (- p q) 1)
    let pq = s.app(Op::Builtin(BuiltinOp::Sub), &[p, q]);
    let one = real_num(&mut s, 1);
    let ge1 = s.app(Op::Builtin(BuiltinOp::Ge), &[pq, one]);
    s.assert(ab);
    s.assert(gap);
    s.assert(gbq);
    s.assert(ge1);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Genuinely sat UFLRA: (= x y) ∧ (= (f x) (f y)) ⇒ SAT.
#[test]
fn genuinely_sat_uflra() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let y = real_const(&mut s, "y");
    let f = real_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let xy = s.eq(x, y);
    let ffeq = s.eq(fx, fy);
    s.assert(xy);
    s.assert(ffeq);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

/// Not entailed: x<=y ∧ distinct(f x)(f y) ⇒ SAT (x,y not forced equal).
#[test]
fn not_entailed_sat() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let y = real_const(&mut s, "y");
    let f = real_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let le = s.app(Op::Builtin(BuiltinOp::Le), &[x, y]);
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, fy]);
    s.assert(le);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}
