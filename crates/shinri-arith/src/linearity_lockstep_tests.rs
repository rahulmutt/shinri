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

use crate::normalize::linearize;
use crate::vars::VarStore;
use proptest::prelude::*;
use shinri_theory::atom::classify;
use shinri_theory::types::Owner;

/// A generated Int arith term over x, y, z. `NegNum(k)` is the slice-63
/// shape `(- k)`; `Num` may be negative (an interned negative numeral).
#[derive(Clone, Debug)]
enum E {
    Var(usize),
    Num(i64),
    NegNum(i64),
    Neg(Box<E>),
    Add(Vec<E>),
    Sub(Box<E>, Box<E>),
    Mul(Vec<E>),
}

fn expr() -> impl Strategy<Value = E> {
    let leaf = prop_oneof![
        (0usize..3).prop_map(E::Var),
        (-5i64..=5).prop_map(E::Num),
        (0i64..=5).prop_map(E::NegNum),
    ];
    leaf.prop_recursive(4, 24, 3, |inner| {
        prop_oneof![
            inner.clone().prop_map(|e| E::Neg(Box::new(e))),
            prop::collection::vec(inner.clone(), 2..=3).prop_map(E::Add),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| E::Sub(Box::new(a), Box::new(b))),
            prop::collection::vec(inner, 2..=3).prop_map(E::Mul),
        ]
    })
}

fn build(ctx: &mut Context, vars: &[TermId; 3], e: &E) -> TermId {
    match e {
        E::Var(i) => vars[*i],
        E::Num(k) => int(ctx, *k),
        E::NegNum(k) => {
            let n = int(ctx, *k);
            app(ctx, BuiltinOp::Neg, &[n])
        }
        E::Neg(a) => {
            let a = build(ctx, vars, a);
            app(ctx, BuiltinOp::Neg, &[a])
        }
        E::Add(xs) => {
            let xs: Vec<TermId> = xs.iter().map(|x| build(ctx, vars, x)).collect();
            app(ctx, BuiltinOp::Add, &xs)
        }
        E::Sub(a, b) => {
            let a = build(ctx, vars, a);
            let b = build(ctx, vars, b);
            app(ctx, BuiltinOp::Sub, &[a, b])
        }
        E::Mul(xs) => {
            let xs: Vec<TermId> = xs.iter().map(|x| build(ctx, vars, x)).collect();
            app(ctx, BuiltinOp::Mul, &xs)
        }
    }
}

fn q(n: i64) -> Rational {
    Rational::from_int((n as i128).into())
}

fn eval(e: &E, asg: &[i64; 3]) -> Rational {
    match e {
        E::Var(i) => q(asg[*i]),
        E::Num(k) => q(*k),
        E::NegNum(k) => -q(*k),
        E::Neg(a) => -eval(a, asg),
        E::Add(xs) => xs.iter().fold(q(0), |acc, x| acc + eval(x, asg)),
        E::Sub(a, b) => eval(a, asg) - eval(b, asg),
        E::Mul(xs) => xs.iter().fold(q(1), |acc, x| acc * eval(x, asg)),
    }
}

proptest! {
    /// classify accepts `(<= t 0)` ⇔ `is_linear_arith(t)`; when accepted,
    /// `linearize(t)` does not trip its debug assertion and its linear form
    /// evaluates equal to `t`.
    #[test]
    fn classify_is_linear_and_linearize_agree(
        e in expr(),
        asg in [-4i64..=4, -4i64..=4, -4i64..=4],
    ) {
        let mut ctx = Context::new();
        let vars = [
            int_var(&mut ctx, "x"),
            int_var(&mut ctx, "y"),
            int_var(&mut ctx, "z"),
        ];
        let t = build(&mut ctx, &vars, &e);
        let zero = int(&mut ctx, 0);
        let atom = app(&mut ctx, BuiltinOp::Le, &[t, zero]);
        let accepted = classify(&ctx, atom).is_ok();
        prop_assert_eq!(accepted, is_linear_arith(&ctx, t), "term {:?}", e);
        if accepted {
            prop_assert_eq!(classify(&ctx, atom), Ok(Owner::Arith));
            let mut vs = VarStore::default();
            let pv: Vec<_> = vars.iter().map(|&x| vs.problem_var(x)).collect();
            let (lin, c) = linearize(&ctx, &mut vs, t);
            let mut val = c;
            for (v, coef) in lin {
                let i = pv.iter().position(|p| *p == v).expect("leaf is x, y or z");
                val = val + coef * q(asg[i]);
            }
            prop_assert_eq!(val, eval(&e, &asg), "term {:?}", e);
        }
    }
}
