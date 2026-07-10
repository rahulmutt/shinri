//! Slice 13 pre-pass: `str.indexof` / `str.replace` — fold, partial-eval,
//! fence.
//!
//! Both ops are value-sorted FUNCTIONS (Int / String), so unlike the slice-12
//! predicates the rewrites here are exact at any position and polarity — no
//! polarity analysis, and the pass introduces ZERO fresh variables.
//!
//! Stages (run by the solver's string-path seam):
//! 1. [`partial_eval_indexof_replace`] — bottom-up memoized rewrite:
//!    - fold fully-literal applications to their concrete value;
//!    - `(str.replace lit lit u)` → concat decomposition around the leftmost
//!      occurrence (exact for any symbolic `u`);
//!    - `(str.indexof lit lit i)` with symbolic `i` → bounded Int-ite step
//!      chain (`INDEXOF_CHAIN_CAP`), eliminated downstream by
//!      `reduce_assertions`' `elim_term_ite`.
//! 2. [`has_unreduced_indexof_replace`] — presence fence: any surviving
//!    application (symbolic haystack/needle, over-cap literal, or a
//!    non-literal-yet-foldable operand like a constant substr — sound, just
//!    undecided) fences the query to a sound `Unknown`.
//!
//! All indices are CODE POINTS (`Vec<char>`), matching `eval_substr_const` —
//! never bytes.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// Cap on `|s|` (code points) for the symbolic-`i` indexof ite chain. Over-cap
/// applications are left in place and fence. Folding has NO cap.
const INDEXOF_CHAIN_CAP: usize = 64;

/// Every occurrence position (code-point index) of `needle` in `hay`,
/// ascending, OVERLAPS INCLUDED. The empty needle occurs at every
/// `0..=|hay|` position (SMT-LIB semantics).
fn occurrences(hay: &[char], needle: &[char]) -> Vec<usize> {
    let (n, m) = (hay.len(), needle.len());
    if m > n {
        return Vec::new();
    }
    (0..=(n - m)).filter(|&j| hay[j..j + m] == *needle).collect()
}

/// Concrete `(str.indexof s sub i)` per the pinned SMT-LIB 2.6 semantics.
fn eval_indexof(hay: &[char], needle: &[char], i: i128) -> i128 {
    let n = hay.len() as i128;
    if i < 0 || i > n {
        return -1;
    }
    occurrences(hay, needle)
        .into_iter()
        .map(|j| j as i128)
        .find(|&j| j >= i)
        .unwrap_or(-1)
}

/// Concrete `(str.replace s t u)`: replace the LEFTMOST occurrence of `t`
/// by `u`; `s` unchanged if `t` does not occur.
fn eval_replace(hay: &[char], t: &[char], u: &str) -> String {
    match occurrences(hay, t).first() {
        Some(&p) => {
            let pre: String = hay[..p].iter().collect();
            let post: String = hay[p + t.len()..].iter().collect();
            format!("{pre}{u}{post}")
        }
        None => hay.iter().collect(),
    }
}

/// Stage 1: bottom-up memoized rewrite. Folds / partial-evals every
/// `str.indexof` / `str.replace` application whose haystack AND needle are
/// string literals; anything else is left in place (the caller fences it via
/// [`has_unreduced_indexof_replace`]). Untouched subtrees keep their TermIds.
pub fn partial_eval_indexof_replace(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
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
                Op::Builtin(BuiltinOp::StrIndexOf) => rewrite_indexof(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrReplace) => rewrite_replace(ctx, &new_children),
                _ => None,
            };
            if let Some(r) = special {
                r
            } else {
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
    };
    memo.insert(t, result);
    result
}

/// `(str.indexof s sub i)`, children already rewritten. Some(_) iff a fold /
/// partial-eval case applies; None leaves the app in place (→ fence).
fn rewrite_indexof(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let hay: Vec<char> = ctx.string_const_value(kids[0])?.chars().collect();
    let needle: Vec<char> = ctx.string_const_value(kids[1])?.chars().collect();
    if let Some(iv) = crate::reduce::int_numeral(ctx, kids[2]) {
        let v = eval_indexof(&hay, &needle, iv);
        let int_s = ctx.int_sort();
        return Some(ctx.mk_numeral(shinri_core::Rational::from_int(v.into()), int_s));
    }
    None // Task 5 adds the symbolic-i ite chain here.
}

/// `(str.replace s t u)`, children already rewritten. Some(_) iff haystack
/// and needle are literals; None leaves the app in place (→ fence).
fn rewrite_replace(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let hay: Vec<char> = ctx.string_const_value(kids[0])?.chars().collect();
    let t: Vec<char> = ctx.string_const_value(kids[1])?.chars().collect();
    let u = ctx.string_const_value(kids[2]).map(str::to_owned)?;
    Some(ctx.mk_string_const(&eval_replace(&hay, &t, &u)))
    // Task 4 replaces the two lines above with the symbolic-u decomposition.
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── Concrete evaluators ──────────────────────────────────────────────

    fn chars(s: &str) -> Vec<char> {
        s.chars().collect()
    }

    #[test]
    fn occurrences_enumerates_overlaps_and_edges() {
        // Overlapping occurrences are ALL enumerated.
        assert_eq!(occurrences(&chars("aaa"), &chars("aa")), vec![0, 1]);
        // Empty needle occurs at every 0..=|s| position.
        assert_eq!(occurrences(&chars("ab"), &chars("")), vec![0, 1, 2]);
        // Needle longer than haystack: none.
        assert_eq!(occurrences(&chars("a"), &chars("ab")), Vec::<usize>::new());
        // Needle at the very end.
        assert_eq!(occurrences(&chars("abc"), &chars("c")), vec![2]);
        // Code points, not bytes: 'é' is 1 position.
        assert_eq!(occurrences(&chars("héllo"), &chars("l")), vec![2, 3]);
    }

    #[test]
    fn eval_indexof_pinned_semantics() {
        let h = chars("abcb");
        let b = chars("b");
        assert_eq!(eval_indexof(&h, &b, 0), 1);
        assert_eq!(eval_indexof(&h, &b, 2), 3); // smallest occurrence >= i
        assert_eq!(eval_indexof(&h, &b, 4), -1); // i = |s| in range, no hit
        assert_eq!(eval_indexof(&h, &b, -1), -1); // i < 0
        assert_eq!(eval_indexof(&h, &b, 5), -1); // i > |s|
        // Empty needle: result = i whenever 0 <= i <= |s| (INCLUDING |s|).
        let e = chars("");
        assert_eq!(eval_indexof(&h, &e, 4), 4);
        assert_eq!(eval_indexof(&h, &e, 0), 0);
        assert_eq!(eval_indexof(&h, &e, 5), -1);
        // Code points: indexof("héllo","l",0) = 2 (byte-based would be 3).
        assert_eq!(eval_indexof(&chars("héllo"), &chars("l"), 0), 2);
    }

    #[test]
    fn eval_replace_pinned_semantics() {
        // Leftmost occurrence only.
        assert_eq!(eval_replace(&chars("abcb"), &chars("b"), "X"), "aXcb");
        // Needle absent: haystack unchanged (u irrelevant).
        assert_eq!(eval_replace(&chars("abc"), &chars("z"), "X"), "abc");
        // Empty needle: u ++ s.
        assert_eq!(eval_replace(&chars("ab"), &chars(""), "X"), "Xab");
        // Code points.
        assert_eq!(eval_replace(&chars("héllo"), &chars("é"), "e"), "hello");
    }

    // ── Fold rewrite ─────────────────────────────────────────────────────

    fn str_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn int_lit(ctx: &mut Context, v: i128) -> TermId {
        let int_s = ctx.int_sort();
        ctx.mk_numeral(shinri_core::Rational::from_int(v.into()), int_s)
    }

    #[test]
    fn folds_all_literal_indexof_and_replace() {
        let mut ctx = Context::new();
        let abcb = ctx.mk_string_const("abcb");
        let b = ctx.mk_string_const("b");
        let x_lit = ctx.mk_string_const("X");
        let zero = int_lit(&mut ctx, 0);
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[abcb, b, zero])
            .unwrap();
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[abcb, b, x_lit])
            .unwrap();
        // Wrap in Bool atoms (assertions are Bool): (= idx 1), (= rep "aXcb").
        let one = int_lit(&mut ctx, 1);
        let a1 = ctx.mk_eq(idx, one).unwrap();
        let want_rep = ctx.mk_string_const("aXcb");
        let a2 = ctx.mk_eq(rep, want_rep).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[a1, a2]);
        // (= 1 1) and (= "aXcb" "aXcb") — both sides now the SAME TermId.
        let want1 = ctx.mk_eq(one, one).unwrap();
        let want2 = ctx.mk_eq(want_rep, want_rep).unwrap();
        assert_eq!(out, vec![want1, want2]);
    }

    #[test]
    fn folds_negative_result_indexof() {
        let mut ctx = Context::new();
        let abc = ctx.mk_string_const("abc");
        let z = ctx.mk_string_const("z");
        let zero = int_lit(&mut ctx, 0);
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[abc, z, zero])
            .unwrap();
        let neg1 = int_lit(&mut ctx, -1);
        let atom = ctx.mk_eq(idx, neg1).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let want = ctx.mk_eq(neg1, neg1).unwrap();
        assert_eq!(out, vec![want]);
    }

    #[test]
    fn symbolic_haystack_left_untouched_same_termid() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let b = ctx.mk_string_const("b");
        let zero = int_lit(&mut ctx, 0);
        let one = int_lit(&mut ctx, 1);
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[s, b, zero])
            .unwrap();
        let atom = ctx.mk_eq(idx, one).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom], "untouched subtree must keep its TermId");
    }
}
