//! Slice 63: the three "is this factor a constant" sites — classify's
//! `contains_nonlinear_mul` (shinri-theory), `is_linear_arith` and
//! `normalize::linearize` — must agree. All three use
//! `Context::const_arith_value`.

use super::is_linear_arith;
use shinri_core::{BuiltinOp, Context, Op, TermId};
use shinri_num::Rational;

fn int_var(ctx: &mut Context, name: &str) -> TermId {
    let int = ctx.int_sort();
    let sym = ctx.declare_fun(name, &[], int);
    ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
}

fn int(ctx: &mut Context, k: i64) -> TermId {
    let int = ctx.int_sort();
    ctx.mk_numeral(Rational::from_int((k as i128).into()), int)
}

fn app(ctx: &mut Context, op: BuiltinOp, args: &[TermId]) -> TermId {
    ctx.mk_app(Op::Builtin(op), args).unwrap()
}

#[test]
fn is_linear_arith_accepts_negated_numeral_factors() {
    let mut ctx = Context::new();
    let x = int_var(&mut ctx, "x");
    let y = int_var(&mut ctx, "y");
    let four = int(&mut ctx, 4);
    let n4 = app(&mut ctx, BuiltinOp::Neg, &[four]);
    let left = app(&mut ctx, BuiltinOp::Mul, &[n4, x]);
    let right = app(&mut ctx, BuiltinOp::Mul, &[x, n4]);
    assert!(is_linear_arith(&ctx, left));
    assert!(is_linear_arith(&ctx, right));
    let nx = app(&mut ctx, BuiltinOp::Neg, &[x]);
    let nonlinear = app(&mut ctx, BuiltinOp::Mul, &[nx, y]);
    assert!(!is_linear_arith(&ctx, nonlinear));
}
