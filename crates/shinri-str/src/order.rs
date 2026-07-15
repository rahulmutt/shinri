//! Slice 23 pre-pass: `str.<` / `str.<=` lexicographic ordering — exact
//! rewriting + fence.
//!
//! Every rewrite here is a FULL logical equivalence (sound at any polarity,
//! nesting, or occurrence count): literal–literal folds, empty-string boundary
//! idioms, and syntactic reflexivity. A single bottom-up memoized pass plus a
//! presence fence. No fresh vars, no polarity tracking, no model repair —
//! the same shape as slice 18's `code_conv` and slice 12's predicate fold.
//!
//! Folding on Rust `&str` is exactly SMT-LIB code-point order: UTF-8 is
//! code-point-order-preserving byte-wise, so `<`/`<=` on `&str` coincides with
//! `str.<`/`str.<=` (the same argument `predicates.rs` makes for
//! prefix/suffix/contains).

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// One bottom-up, memoized equivalence rewrite over each assertion. Untouched
/// subtrees keep their `TermId`s.
pub fn rewrite_str_order(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect()
}

fn rewrite(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> =
                children.iter().map(|&c| rewrite(ctx, c, memo)).collect();
            let special = match op {
                Op::Builtin(BuiltinOp::StrLt) => try_order_atom(ctx, &new_children, false),
                Op::Builtin(BuiltinOp::StrLeq) => try_order_atom(ctx, &new_children, true),
                _ => None,
            };
            if let Some(r) = special {
                r
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(n, o)| n != o);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("order: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// One equivalence-preserving rewrite of `(str.< a b)` / `(str.<= a b)`.
/// `reflexive` distinguishes `<=` (reflexive: `s <= s` is true) from `<`
/// (irreflexive: `s < s` is false). Returns `None` — leave the atom to the
/// fence — for anything not one of the three decided idioms.
fn try_order_atom(ctx: &mut Context, args: &[TermId], reflexive: bool) -> Option<TermId> {
    let (a, b) = (args[0], args[1]);

    // (c) Reflexivity: syntactically identical (same hash-consed term).
    //     s <= s -> true ; s < s -> false.
    if a == b {
        return Some(ctx.mk_const_bool(reflexive));
    }

    let av = ctx.string_const_value(a).map(str::to_owned);
    let bv = ctx.string_const_value(b).map(str::to_owned);

    match (av, bv) {
        // (a) Literal–literal fold: Rust &str order == code-point order.
        (Some(x), Some(y)) => {
            let v = if reflexive { x <= y } else { x < y };
            Some(ctx.mk_const_bool(v))
        }
        // (b) Empty-string boundary, symbolic right side:
        //     ("" <= s) -> true ; ("" < s) -> (not (= s "")).
        (Some(x), None) if x.is_empty() => {
            if reflexive {
                Some(ctx.mk_const_bool(true))
            } else {
                let empty = ctx.mk_string_const("");
                let eq = ctx.mk_eq(b, empty).expect("s = \"\"");
                Some(
                    ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq])
                        .expect("not (s = \"\")"),
                )
            }
        }
        // (b) Empty-string boundary, symbolic left side:
        //     (s <= "") -> (= s "") ; (s < "") -> false.
        (None, Some(y)) if y.is_empty() => {
            if reflexive {
                let empty = ctx.mk_string_const("");
                Some(ctx.mk_eq(a, empty).expect("s = \"\""))
            } else {
                Some(ctx.mk_const_bool(false))
            }
        }
        _ => None,
    }
}

/// Presence fence: `true` iff any `str.<`/`str.<=` application survives the
/// rewrite (a genuinely symbolic comparison outside the decided fragment).
/// Mirrors `code_conv::has_unreduced_code_conv`.
pub fn has_unreduced_str_order(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(BuiltinOp::StrLt | BuiltinOp::StrLeq))
                    || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn str_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn order(ctx: &mut Context, op: BuiltinOp, a: TermId, b: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(op), &[a, b]).unwrap()
    }

    #[test]
    fn folds_literal_literal_both_ops() {
        let mut ctx = Context::new();
        let a = ctx.mk_string_const("a");
        let b = ctx.mk_string_const("b");
        let t = ctx.mk_const_bool(true);
        let f = ctx.mk_const_bool(false);
        // "a" < "b" -> true ; "b" < "a" -> false ; "a" <= "a" -> true.
        let lt = order(&mut ctx, BuiltinOp::StrLt, a, b);
        let gt = order(&mut ctx, BuiltinOp::StrLt, b, a);
        let le = order(&mut ctx, BuiltinOp::StrLeq, a, a);
        let out = rewrite_str_order(&mut ctx, &[lt, gt, le]);
        assert_eq!(out, vec![t, f, t]);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn empty_boundaries_rewrite() {
        let mut ctx = Context::new();
        let empty = ctx.mk_string_const("");
        let s = str_var(&mut ctx, "s");
        let t = ctx.mk_const_bool(true);
        let f = ctx.mk_const_bool(false);
        // "" <= s -> true ; s < "" -> false.
        let le = order(&mut ctx, BuiltinOp::StrLeq, empty, s);
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, empty);
        // s <= "" -> (= s "") ; "" < s -> (not (= s "")).
        let le2 = order(&mut ctx, BuiltinOp::StrLeq, s, empty);
        let lt2 = order(&mut ctx, BuiltinOp::StrLt, empty, s);
        let out = rewrite_str_order(&mut ctx, &[le, lt, le2, lt2]);
        assert_eq!(out[0], t);
        assert_eq!(out[1], f);
        let eq = ctx.mk_eq(s, empty).unwrap();
        let neq = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq]).unwrap();
        assert_eq!(out[2], eq);
        assert_eq!(out[3], neq);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn reflexivity_decides() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let t = ctx.mk_const_bool(true);
        let f = ctx.mk_const_bool(false);
        let le = order(&mut ctx, BuiltinOp::StrLeq, s, s);
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, s);
        let out = rewrite_str_order(&mut ctx, &[le, lt]);
        assert_eq!(out, vec![t, f]);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn symbolic_pair_survives_to_fence() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let u = str_var(&mut ctx, "u");
        // s < u over two distinct free vars: no arm fires -> survives -> fenced.
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, u);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        assert_eq!(out, vec![lt]);
        assert!(has_unreduced_str_order(&ctx, &out));
    }
}
