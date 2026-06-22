//! End-to-end QF_UFLIA (EUF + linear integer arithmetic) via MBTC. Every witness
//! gets a DEFINITE verdict (no `unknown`): convex/entailed cases via N-O exchange,
//! non-convex/free arrangements via the integer trichotomy split. z3 ground truth
//! is noted per witness.

use shinri_core::{BuiltinOp, Op};
use shinri_num::Rational;
use shinri_solver::{SolveOutcome, Solver};

fn int_const(s: &mut Solver, name: &str) -> shinri_core::TermId {
    let int = s.int_sort();
    s.declare_const(name, int)
}
fn int_num(s: &mut Solver, n: i128) -> shinri_core::TermId {
    let int = s.int_sort();
    s.numeral(Rational::from_int(n.into()), int)
}
fn int_fun1(s: &mut Solver, name: &str) -> shinri_core::SymbolId {
    let int = s.int_sort();
    s.declare_fun(name, &[int], int)
}

/// Entailed (pinned): x>=5 ∧ x<=5 ∧ distinct(f x)(f 5) ⇒ UNSAT (z3: unsat).
#[test]
fn int_bounds_pinned_unsat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let five = int_num(&mut s, 5);
    let f = int_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let f5 = s.app(Op::Uninterpreted(f), &[five]);
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[x, five]);
    let le = s.app(Op::Builtin(BuiltinOp::Le), &[x, five]);
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, f5]);
    s.assert(ge);
    s.assert(le);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Non-fixed entailed: x<=y ∧ y<=x ∧ distinct(f x)(f y) ⇒ UNSAT (z3: unsat).
#[test]
fn int_nonfixed_entailed_unsat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let f = int_fun1(&mut s, "f");
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

/// Genuinely SAT: (= x y) ∧ (= (f x) (f y)) ⇒ SAT (z3: sat).
#[test]
fn int_genuinely_sat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let f = int_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let xy = s.eq(x, y);
    let ffeq = s.eq(fx, fy);
    s.assert(xy);
    s.assert(ffeq);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

/// SOUNDNESS HEADLINE — non-convex: 1<=x ∧ x<=2 ∧ y=1 ∧ z=2 ∧
/// distinct(f x)(f y) ∧ distinct(f x)(f z) ⇒ UNSAT (z3: unsat). No single
/// equality is entailed; the MBTC trichotomy split on x decides x=1 (→ f(x)=f(y)
/// conflict) or x=2 (→ f(x)=f(z) conflict) ⇒ UNSAT. Was wrongly SAT pre-MBTC.
#[test]
fn int_nonconvex_unsat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let z = int_const(&mut s, "z");
    let one = int_num(&mut s, 1);
    let two = int_num(&mut s, 2);
    let f = int_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let fz = s.app(Op::Uninterpreted(f), &[z]);
    let xge1 = s.app(Op::Builtin(BuiltinOp::Ge), &[x, one]);
    let xle2 = s.app(Op::Builtin(BuiltinOp::Le), &[x, two]);
    let yeq = s.eq(y, one);
    let zeq = s.eq(z, two);
    let dxy = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, fy]);
    let dxz = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, fz]);
    for a in [xge1, xle2, yeq, zeq, dxy, dxz] {
        s.assert(a);
    }
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Free arrangement: x<=y ∧ distinct(f x)(f y) ⇒ SAT (z3: sat). arith may park
/// x=y; the trichotomy split picks x<y, then f(x)<f(y), yielding a valid model.
#[test]
fn int_free_arrangement_sat() {
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let f = int_fun1(&mut s, "f");
    let fx = s.app(Op::Uninterpreted(f), &[x]);
    let fy = s.app(Op::Uninterpreted(f), &[y]);
    let le = s.app(Op::Builtin(BuiltinOp::Le), &[x, y]);
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[fx, fy]);
    s.assert(le);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}
