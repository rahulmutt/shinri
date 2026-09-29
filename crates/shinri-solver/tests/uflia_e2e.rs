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

// ----- Slice 50: compound UF arguments (spec §1.2, Review Focus 1–5) -----

/// Assert `a = a_val`, `f(k) = 5`, `¬(f(arg) = 5)` with `arg = build(s, a)`,
/// and return the verdict. `build` may declare and assert extra context.
fn slice50_case(
    a_val: i128,
    k: i128,
    build: impl FnOnce(&mut Solver, shinri_core::TermId) -> shinri_core::TermId,
) -> SolveOutcome {
    let mut s = Solver::new();
    let a = int_const(&mut s, "a");
    let f = int_fun1(&mut s, "f");
    let av = int_num(&mut s, a_val);
    let kn = int_num(&mut s, k);
    let five = int_num(&mut s, 5);
    let arg = build(&mut s, a);
    let fk = s.app(Op::Uninterpreted(f), &[kn]);
    let farg = s.app(Op::Uninterpreted(f), &[arg]);
    let a_eq = s.eq(a, av);
    let fk_eq = s.eq(fk, five);
    let farg_eq = s.eq(farg, five);
    let not_farg = s.app(Op::Builtin(BuiltinOp::Not), &[farg_eq]);
    s.assert(a_eq);
    s.assert(fk_eq);
    s.assert(not_farg);
    s.check_sat()
}

/// Spec §1.2: a=0 ∧ f(1)=5 ∧ ¬f(a+1)=5 ⇒ UNSAT (z3: unsat). Was `sat` with
/// `(+ a 1) ↦ 0`: the compound argument had no arithmetic definition.
#[test]
fn slice50_compound_arg_add_unsat() {
    let got = slice50_case(0, 1, |s, a| {
        let one = int_num(s, 1);
        s.app(Op::Builtin(BuiltinOp::Add), &[a, one])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Spec §1.2 variant: a=1 ∧ f(1)=5 ∧ ¬f(a+0)=5 ⇒ UNSAT (z3: unsat).
#[test]
fn slice50_compound_arg_add_zero_unsat() {
    let got = slice50_case(1, 1, |s, a| {
        let zero = int_num(s, 0);
        s.app(Op::Builtin(BuiltinOp::Add), &[a, zero])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Spec §1.2 variant: a=0 ∧ f(0)=5 ∧ ¬f(2·a)=5 ⇒ UNSAT (z3: unsat).
#[test]
fn slice50_compound_arg_mul_unsat() {
    let got = slice50_case(0, 0, |s, a| {
        let two = int_num(s, 2);
        s.app(Op::Builtin(BuiltinOp::Mul), &[two, a])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// The Wisa shape `(- (- fmt1 2) fmt0)`: a=3 ∧ b=0 ∧ f(1)=5 ∧ ¬f((a−2)−b)=5
/// ⇒ UNSAT (z3: unsat).
#[test]
fn slice50_compound_arg_nested_sub_unsat() {
    let got = slice50_case(3, 1, |s, a| {
        let b = int_const(s, "b");
        let zero = int_num(s, 0);
        let two = int_num(s, 2);
        let b_eq = s.eq(b, zero);
        s.assert(b_eq);
        let a2 = s.app(Op::Builtin(BuiltinOp::Sub), &[a, two]);
        s.app(Op::Builtin(BuiltinOp::Sub), &[a2, b])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Review Focus 2: a=7 ∧ f(0)=5 ∧ ¬f(a−a)=5 ⇒ UNSAT (z3: unsat). The row
/// cancels to `v = 0` (the degenerate `comb == [(v, 1)]` branch).
#[test]
fn slice50_cancelling_arg_unsat() {
    let got = slice50_case(7, 0, |s, a| s.app(Op::Builtin(BuiltinOp::Sub), &[a, a]));
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Review Focus 3: a=0 ∧ g(1)=4 ∧ f(5)=5 ∧ ¬f(g(a+1)+1)=5 ⇒ UNSAT (z3: unsat).
/// `g(a+1)` is a linearization leaf and must share its arith var with the
/// shared term `g(a+1)`; `a+1` is itself a defined compound.
#[test]
fn slice50_nested_uf_leaf_unsat() {
    let got = slice50_case(0, 5, |s, a| {
        let g = int_fun1(s, "g");
        let one = int_num(s, 1);
        let four = int_num(s, 4);
        let g1 = s.app(Op::Uninterpreted(g), &[one]);
        let g1_eq = s.eq(g1, four);
        s.assert(g1_eq);
        let a1 = s.app(Op::Builtin(BuiltinOp::Add), &[a, one]);
        let ga1 = s.app(Op::Uninterpreted(g), &[a1]);
        s.app(Op::Builtin(BuiltinOp::Add), &[ga1, one])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Review Focus 4: a=0 ∧ f(1)=5 ∧ ¬f(a+2)=5 ⇒ SAT (z3: sat). f(2) is free; the
/// definitional row must not over-constrain.
#[test]
fn slice50_compound_arg_sat_direction() {
    let got = slice50_case(0, 1, |s, a| {
        let two = int_num(s, 2);
        s.app(Op::Builtin(BuiltinOp::Add), &[a, two])
    });
    assert_eq!(got, SolveOutcome::Sat);
}

/// Review Focus 1: a=b+1 ∧ ¬(f(a+1)=f(b+2)) ⇒ UNSAT (z3: unsat). The two
/// arguments are structurally different and neither is a numeral: only an
/// arith entailment between two DEFINED shared vars can merge them. (`a=b` with
/// `f(a+1)` vs `f(b+1)` is already unsat on `main` via EUF congruence over `+`.)
#[test]
fn slice50_two_compound_args_equal_unsat() {
    let mut s = Solver::new();
    let a = int_const(&mut s, "a");
    let b = int_const(&mut s, "b");
    let f = int_fun1(&mut s, "f");
    let one = int_num(&mut s, 1);
    let two = int_num(&mut s, 2);
    let b_plus_1 = s.app(Op::Builtin(BuiltinOp::Add), &[b, one]);
    let a1 = s.app(Op::Builtin(BuiltinOp::Add), &[a, one]);
    let b2 = s.app(Op::Builtin(BuiltinOp::Add), &[b, two]);
    let fa1 = s.app(Op::Uninterpreted(f), &[a1]);
    let fb2 = s.app(Op::Uninterpreted(f), &[b2]);
    let a_eq = s.eq(a, b_plus_1);
    let ff = s.eq(fa1, fb2);
    let not_ff = s.app(Op::Builtin(BuiltinOp::Not), &[ff]);
    s.assert(a_eq);
    s.assert(not_ff);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Review Focus 5 (guard, not red): a nonlinear argument is outside QF_UFLIA.
/// It must stay opaque and must not reach `linearize`'s "nonlinear reached
/// normalize" debug assertion. Any verdict is acceptable; a panic is not.
#[test]
fn slice50_nonlinear_arg_does_not_panic() {
    let _ = slice50_case(0, 0, |s, a| s.app(Op::Builtin(BuiltinOp::Mul), &[a, a]));
}
