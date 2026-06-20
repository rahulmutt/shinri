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

/// CRITICAL-2 (EUF→arith, f-app directly inside a linear arith term):
/// `(= x0 x1) ∧ (>= (- (f x0) (f x1)) 1)` ⇒ UNSAT.
/// x0=x1 ⟹ f(x0)=f(x1) by congruence ⟹ (f x0)-(f x1)=0, contradicting >=1.
/// Was wrongly Sat: `(f x0)`/`(f x1)` were interned by arith as free vars but
/// never registered in EUF, so congruence never fired. (z3: unsat.)
#[test]
fn crit2_fapp_in_arith_term_euf_to_arith_unsat() {
    let mut s = Solver::new();
    let x0 = real_const(&mut s, "x0");
    let x1 = real_const(&mut s, "x1");
    let f = real_fun1(&mut s, "f");
    let fx0 = s.app(Op::Uninterpreted(f), &[x0]);
    let fx1 = s.app(Op::Uninterpreted(f), &[x1]);
    let eq = s.eq(x0, x1);
    let sub = s.app(Op::Builtin(BuiltinOp::Sub), &[fx0, fx1]);
    let one = real_num(&mut s, 1);
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[sub, one]);
    s.assert(eq);
    s.assert(ge);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// CRITICAL-2 (arith→EUF, numeral-arg f-app directly inside a linear term):
/// `x0>=0 ∧ x0<=0 ∧ (>= (- (f x0) (f 0)) 1)` ⇒ UNSAT.
/// x0 pinned to 0 ⟹ x0=0 entailed by LRA ⟹ f(x0)=f(0) by congruence ⟹
/// (f x0)-(f 0)=0, contradicting >=1. (z3: unsat.)
#[test]
fn crit2_fapp_numeral_arg_arith_to_euf_unsat() {
    let mut s = Solver::new();
    let x0 = real_const(&mut s, "x0");
    let zero = real_num(&mut s, 0);
    let f = real_fun1(&mut s, "f");
    let fx0 = s.app(Op::Uninterpreted(f), &[x0]);
    let f0 = s.app(Op::Uninterpreted(f), &[zero]);
    let ge0 = s.app(Op::Builtin(BuiltinOp::Ge), &[x0, zero]);
    let le0 = s.app(Op::Builtin(BuiltinOp::Le), &[x0, zero]);
    let sub = s.app(Op::Builtin(BuiltinOp::Sub), &[fx0, f0]);
    let one = real_num(&mut s, 1);
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[sub, one]);
    s.assert(ge0);
    s.assert(le0);
    s.assert(ge);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// CRITICAL-2 completeness caveat: nested apps. `f(g(x))` must be interned with
/// `g(x)` so deeper congruence works.
/// `(= x0 x1) ∧ (>= (- (f (g x0)) (f (g x1))) 1)` ⇒ UNSAT.
#[test]
fn crit2_nested_fapp_in_arith_term_unsat() {
    let mut s = Solver::new();
    let x0 = real_const(&mut s, "x0");
    let x1 = real_const(&mut s, "x1");
    let f = real_fun1(&mut s, "f");
    let g = real_fun1(&mut s, "g");
    let gx0 = s.app(Op::Uninterpreted(g), &[x0]);
    let gx1 = s.app(Op::Uninterpreted(g), &[x1]);
    let fgx0 = s.app(Op::Uninterpreted(f), &[gx0]);
    let fgx1 = s.app(Op::Uninterpreted(f), &[gx1]);
    let eq = s.eq(x0, x1);
    let sub = s.app(Op::Builtin(BuiltinOp::Sub), &[fgx0, fgx1]);
    let one = real_num(&mut s, 1);
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[sub, one]);
    s.assert(eq);
    s.assert(ge);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
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
