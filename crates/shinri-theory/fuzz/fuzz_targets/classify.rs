#![no_main]
//! `classify` must never panic on any well-sorted atom; it returns Ok/Err.
use libfuzzer_sys::fuzz_target;
use shinri_core::{BuiltinOp, Context, Op, Rational};

fuzz_target!(|data: &[u8]| {
    // Build a small arithmetic atom from the fuzz bytes and classify it.
    let mut ctx = Context::new();
    let real = ctx.real_sort();
    let xs = ctx.declare_fun("x", &[], real);
    let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
    let n = data.first().copied().unwrap_or(0) as i128;
    let k = ctx.mk_numeral(Rational::from_int(n.into()), real);
    let op = match data.get(1).copied().unwrap_or(0) % 4 {
        0 => BuiltinOp::Le,
        1 => BuiltinOp::Lt,
        2 => BuiltinOp::Ge,
        _ => BuiltinOp::Gt,
    };
    if let Ok(atom) = ctx.mk_app(Op::Builtin(op), &[x, k]) {
        let _ = shinri_theory::classify(&ctx, atom); // must not panic
    }
});
