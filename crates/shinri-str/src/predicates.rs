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

use rustc_hash::{FxHashMap, FxHashSet};
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
            let new_children: Vec<TermId> =
                children.iter().map(|&c| fold_term(ctx, c, memo)).collect();
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

#[derive(Clone, Copy, Default)]
struct Polarity {
    pos: bool,
    neg: bool,
}

/// Stage 2: polarity fence. True iff any string-predicate atom (surviving
/// stage-1 folding) has a reachable NEGATIVE occurrence — i.e. is not
/// positive-only. Positive-only atoms are safe for the stage-3 existential
/// rewrite; everything else must fence the query to a sound `Unknown`.
///
/// Polarity descent: `and`/`or` preserve; `not` flips; `=>` flips every
/// antecedent (all args but the last). ANY other enclosing structure —
/// `xor`, `=`/`distinct` over Bool, `ite` in any position, uninterpreted
/// applications, or a predicate nested inside another predicate's args —
/// marks descendants both-polarity. Unrecognized structure therefore fails
/// SOUND (fence), never unsound (wrong-side rewrite).
pub fn has_unrewritable_str_predicate(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut map: FxHashMap<TermId, Polarity> = FxHashMap::default();
    let mut seen: FxHashSet<(TermId, bool, bool)> = FxHashSet::default();
    for &a in assertions {
        collect_polarities(ctx, a, true, false, &mut map, &mut seen);
    }
    map.values().any(|p| p.neg)
}

fn collect_polarities(
    ctx: &Context,
    t: TermId,
    pos: bool,
    both: bool,
    map: &mut FxHashMap<TermId, Polarity>,
    seen: &mut FxHashSet<(TermId, bool, bool)>,
) {
    if !seen.insert((t, pos, both)) {
        return;
    }
    match ctx.term_node(t) {
        TermNode::Const { .. } => {}
        TermNode::App { op, args, .. } => {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            if is_str_predicate(op) {
                let e = map.entry(t).or_default();
                if both {
                    e.pos = true;
                    e.neg = true;
                } else if pos {
                    e.pos = true;
                } else {
                    e.neg = true;
                }
                // A predicate nested inside THIS predicate's String args can
                // only sit in a Bool position (an ite condition) — treat it
                // as non-monotone.
                for &k in &kids {
                    collect_polarities(ctx, k, true, true, map, seen);
                }
                return;
            }
            match op {
                Op::Builtin(BuiltinOp::And | BuiltinOp::Or) => {
                    for &k in &kids {
                        collect_polarities(ctx, k, pos, both, map, seen);
                    }
                }
                Op::Builtin(BuiltinOp::Not) => {
                    collect_polarities(ctx, kids[0], !pos, both, map, seen);
                }
                Op::Builtin(BuiltinOp::Implies) => {
                    // n-ary right-assoc: all but the last arg are antecedents.
                    let (last, ants) = kids.split_last().expect("=> has args");
                    for &k in ants {
                        collect_polarities(ctx, k, !pos, both, map, seen);
                    }
                    collect_polarities(ctx, *last, pos, both, map, seen);
                }
                // Everything else is a non-monotone context for anything below.
                _ => {
                    for &k in &kids {
                        collect_polarities(ctx, k, true, true, map, seen);
                    }
                }
            }
        }
    }
}

fn fresh_str_var(ctx: &mut Context, name: &str) -> TermId {
    let str_s = ctx.string_sort();
    let sym = ctx.declare_fun(name, &[], str_s);
    ctx.mk_app(Op::Uninterpreted(sym), &[])
        .expect("fresh string var")
}

/// Stage 3: rewrite every remaining (positive-only — the caller must have
/// fenced otherwise via [`has_unrewritable_str_predicate`]) predicate atom to
/// its existential concat decomposition:
///
/// - `(str.prefixof p s)` → `(= s (str.++ p k))`
/// - `(str.suffixof p s)` → `(= s (str.++ k p))`
/// - `(str.contains s sub)` → `(= s (str.++ k1 sub k2))`
///
/// Equisatisfiable for positive occurrences: the equation implies the
/// predicate, and any model of the predicate extends to the fresh vars.
/// Memoized on the atom's TermId so a repeated atom reuses one fresh-var set.
pub fn rewrite_str_predicates(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite_pred(ctx, a, &mut memo))
        .collect()
}

fn rewrite_pred(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> = children
                .iter()
                .map(|&c| rewrite_pred(ctx, c, memo))
                .collect();
            match op {
                Op::Builtin(BuiltinOp::StrPrefixOf) => {
                    let (p, s) = (new_children[0], new_children[1]);
                    let n = crate::reduce::next_fresh();
                    let k = fresh_str_var(ctx, &format!("!pfx{n}"));
                    let cat = ctx
                        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[p, k])
                        .expect("p ++ k");
                    ctx.mk_eq(s, cat).expect("s = p ++ k")
                }
                Op::Builtin(BuiltinOp::StrSuffixOf) => {
                    let (p, s) = (new_children[0], new_children[1]);
                    let n = crate::reduce::next_fresh();
                    let k = fresh_str_var(ctx, &format!("!sfx{n}"));
                    let cat = ctx
                        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[k, p])
                        .expect("k ++ p");
                    ctx.mk_eq(s, cat).expect("s = k ++ p")
                }
                Op::Builtin(BuiltinOp::StrContains) => {
                    let (s, sub) = (new_children[0], new_children[1]);
                    let n = crate::reduce::next_fresh();
                    let kl = fresh_str_var(ctx, &format!("!ctnl{n}"));
                    let kr = fresh_str_var(ctx, &format!("!ctnr{n}"));
                    let cat = ctx
                        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[kl, sub, kr])
                        .expect("kl ++ sub ++ kr");
                    ctx.mk_eq(s, cat).expect("s = kl ++ sub ++ kr")
                }
                _ => {
                    let changed = new_children
                        .iter()
                        .zip(children.iter())
                        .any(|(nc, oc)| nc != oc);
                    if changed {
                        ctx.mk_app(op, &new_children)
                            .expect("rewrite: well-sorted rebuild")
                    } else {
                        t
                    }
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

    fn bool_var(ctx: &mut Context, name: &str) -> TermId {
        let b = ctx.bool_sort();
        let f = ctx.declare_fun(name, &[], b);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn polarity_fence_classification() {
        let mut ctx = Context::new();
        let lit = ctx.mk_string_const("a");
        let s = str_var(&mut ctx, "s");
        let x = bool_var(&mut ctx, "x");
        let p = pred(&mut ctx, BuiltinOp::StrPrefixOf, lit, s);

        // Positive-only shapes: NOT fenced.
        let or_px = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[p, x]).unwrap();
        let and_px = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[p, x]).unwrap();
        let imp_xp = ctx
            .mk_app(Op::Builtin(BuiltinOp::Implies), &[x, p])
            .unwrap();
        assert!(!has_unrewritable_str_predicate(&ctx, &[p]));
        assert!(!has_unrewritable_str_predicate(
            &ctx,
            &[or_px, and_px, imp_xp]
        ));

        // Negative / non-monotone shapes: fenced.
        let not_p = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[p]).unwrap();
        let imp_px = ctx
            .mk_app(Op::Builtin(BuiltinOp::Implies), &[p, x])
            .unwrap();
        let xor_px = ctx.mk_app(Op::Builtin(BuiltinOp::Xor), &[p, x]).unwrap();
        let eq_px = ctx.mk_eq(p, x).unwrap(); // Bool-eq: non-monotone
        let a_lit = ctx.mk_string_const("a");
        let b_lit = ctx.mk_string_const("b");
        let ite_p = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[p, a_lit, b_lit])
            .unwrap(); // predicate as ite condition
        let eq_ite = ctx.mk_eq(ite_p, s).unwrap();
        for bad in [not_p, imp_px, xor_px, eq_px, eq_ite] {
            assert!(
                has_unrewritable_str_predicate(&ctx, &[bad]),
                "shape must fence"
            );
        }

        // Mixed polarity across assertions: fenced.
        assert!(has_unrewritable_str_predicate(&ctx, &[or_px, not_p]));

        // Double negation is positive again: NOT fenced.
        let not_not_p = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[not_p]).unwrap();
        assert!(!has_unrewritable_str_predicate(&ctx, &[not_not_p]));
    }

    /// Destructure `(= lhs (str.++ …))` and return (lhs, concat kids).
    fn eq_concat_parts(ctx: &Context, t: TermId) -> (TermId, Vec<TermId>) {
        let shinri_core::TermNode::App { op, args, .. } = ctx.term_node(t) else {
            panic!("expected eq app");
        };
        assert!(matches!(op, Op::Builtin(BuiltinOp::Eq)));
        let kids: Vec<TermId> = ctx.children(*args).to_vec();
        let shinri_core::TermNode::App {
            op: cop,
            args: cargs,
            ..
        } = ctx.term_node(kids[1])
        else {
            panic!("expected concat rhs");
        };
        assert!(matches!(cop, Op::Builtin(BuiltinOp::StrConcat)));
        (kids[0], ctx.children(*cargs).to_vec())
    }

    #[test]
    fn rewrites_positive_predicates_to_concat_equations() {
        let mut ctx = Context::new();
        let p = ctx.mk_string_const("ab");
        let s = str_var(&mut ctx, "s");

        // prefixof(p, s) → (= s (str.++ p k))
        let pf = pred(&mut ctx, BuiltinOp::StrPrefixOf, p, s);
        let out = rewrite_str_predicates(&mut ctx, &[pf]);
        let (lhs, kids) = eq_concat_parts(&ctx, out[0]);
        assert_eq!(lhs, s);
        assert_eq!(kids.len(), 2);
        assert_eq!(kids[0], p, "needle must lead in prefixof decomposition");

        // suffixof(p, s) → (= s (str.++ k p))
        let sf = pred(&mut ctx, BuiltinOp::StrSuffixOf, p, s);
        let out = rewrite_str_predicates(&mut ctx, &[sf]);
        let (lhs, kids) = eq_concat_parts(&ctx, out[0]);
        assert_eq!(lhs, s);
        assert_eq!(kids.len(), 2);
        assert_eq!(kids[1], p, "needle must trail in suffixof decomposition");

        // contains(s, sub) → (= s (str.++ k1 sub k2))
        let ct = pred(&mut ctx, BuiltinOp::StrContains, s, p);
        let out = rewrite_str_predicates(&mut ctx, &[ct]);
        let (lhs, kids) = eq_concat_parts(&ctx, out[0]);
        assert_eq!(lhs, s);
        assert_eq!(kids.len(), 3);
        assert_eq!(kids[1], p, "needle must be the middle of contains");
    }

    #[test]
    fn rewrite_dedups_repeated_atom() {
        let mut ctx = Context::new();
        let p = ctx.mk_string_const("a");
        let s = str_var(&mut ctx, "s");
        let x = bool_var(&mut ctx, "x");
        let pf = pred(&mut ctx, BuiltinOp::StrPrefixOf, p, s);
        let or1 = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[pf, x]).unwrap();
        // Same atom in two assertions → SAME equation term (one fresh var set).
        let out = rewrite_str_predicates(&mut ctx, &[pf, or1]);
        let (_, kids0) = eq_concat_parts(&ctx, out[0]);
        let shinri_core::TermNode::App { args, .. } = ctx.term_node(out[1]) else {
            panic!("or app");
        };
        let or_kids: Vec<TermId> = ctx.children(*args).to_vec();
        let (_, kids1) = eq_concat_parts(&ctx, or_kids[0]);
        assert_eq!(kids0[1], kids1[1], "repeated atom must reuse its fresh var");
    }
}
