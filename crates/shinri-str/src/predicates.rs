//! Slice 12 pre-pass: string predicates (`str.prefixof` / `str.suffixof` /
//! `str.contains`).
//!
//! Three stages, run by the solver's string-path seam in this order:
//! 1. [`fold_str_predicates`] — constant-fold literal-literal predicate atoms
//!    to Boolean constants (any polarity).
//! 2. [`has_unrewritable_str_predicate`] — polarity fence: any surviving
//!    predicate occurrence that is not positive-only (negative, mixed, or
//!    non-monotone context) makes the query fence to a sound `Unknown`.
//! 3. [`rewrite_str_predicates`] — rewrite positive-only atoms to their
//!    existential concat decomposition (fresh String vars).
//!
//! Folding on Rust `&str` is correct for SMT-LIB code-point semantics:
//! UTF-8 is concatenation-preserving and code-point-aligned, so byte-level
//! `starts_with`/`ends_with`/`contains` coincide with code-point
//! prefix/suffix/substring.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

fn is_str_predicate(op: &Op) -> bool {
    matches!(
        op,
        Op::Builtin(BuiltinOp::StrPrefixOf | BuiltinOp::StrSuffixOf | BuiltinOp::StrContains)
    )
}

/// Stage 1: constant-fold every predicate app whose BOTH args are string
/// literals, at any polarity/position. Returns rewritten assertions;
/// untouched subtrees keep their `TermId`s.
pub fn fold_str_predicates(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| fold_term(ctx, a, &mut memo))
        .collect()
}

fn fold_term(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> = children
                .iter()
                .map(|&c| fold_term(ctx, c, memo))
                .collect();
            let folded = if is_str_predicate(&op) {
                let a = ctx.string_const_value(new_children[0]).map(str::to_owned);
                let b = ctx.string_const_value(new_children[1]).map(str::to_owned);
                match (op, a, b) {
                    // prefixof/suffixof: args are (needle p, haystack s).
                    (Op::Builtin(BuiltinOp::StrPrefixOf), Some(p), Some(s)) => {
                        Some(s.starts_with(&p))
                    }
                    (Op::Builtin(BuiltinOp::StrSuffixOf), Some(p), Some(s)) => {
                        Some(s.ends_with(&p))
                    }
                    // contains: args are (haystack s, needle sub).
                    (Op::Builtin(BuiltinOp::StrContains), Some(s), Some(sub)) => {
                        Some(s.contains(&sub))
                    }
                    _ => None,
                }
            } else {
                None
            };
            if let Some(v) = folded {
                ctx.mk_const_bool(v)
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(nc, oc)| nc != oc);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("fold: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn str_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn pred(ctx: &mut Context, op: BuiltinOp, a: TermId, b: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(op), &[a, b]).unwrap()
    }

    #[test]
    fn folds_all_three_predicates_true_and_false() {
        let mut ctx = Context::new();
        let ab = ctx.mk_string_const("ab");
        let abc = ctx.mk_string_const("abc");
        let d = ctx.mk_string_const("d");
        let t_true = ctx.mk_const_bool(true);
        let t_false = ctx.mk_const_bool(false);
        // (str.prefixof "ab" "abc") → true ; (str.prefixof "d" "abc") → false
        let p1 = pred(&mut ctx, BuiltinOp::StrPrefixOf, ab, abc);
        let p2 = pred(&mut ctx, BuiltinOp::StrPrefixOf, d, abc);
        // (str.suffixof "ab" "abc") → false (needle-first arg order!)
        let p3 = pred(&mut ctx, BuiltinOp::StrSuffixOf, ab, abc);
        // (str.contains "abc" "d") → false (haystack-first arg order!)
        let p4 = pred(&mut ctx, BuiltinOp::StrContains, abc, d);
        let out = fold_str_predicates(&mut ctx, &[p1, p2, p3, p4]);
        assert_eq!(out, vec![t_true, t_false, t_false, t_false]);
    }

    #[test]
    fn folds_under_negation_and_leaves_symbolic_untouched() {
        let mut ctx = Context::new();
        let abc = ctx.mk_string_const("abc");
        let d = ctx.mk_string_const("d");
        let s = str_var(&mut ctx, "s");
        // (not (str.contains "abc" "d")) → (not false)
        let inner = pred(&mut ctx, BuiltinOp::StrContains, abc, d);
        let not_inner = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[inner]).unwrap();
        // symbolic: (str.prefixof "d" s) untouched, same TermId.
        let sym = pred(&mut ctx, BuiltinOp::StrPrefixOf, d, s);
        let out = fold_str_predicates(&mut ctx, &[not_inner, sym]);
        let f = ctx.mk_const_bool(false);
        let want_not = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[f]).unwrap();
        assert_eq!(out[0], want_not);
        assert_eq!(out[1], sym, "symbolic predicate must keep its TermId");
    }
}
