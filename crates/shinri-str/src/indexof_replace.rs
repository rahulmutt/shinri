//! Slice 13–14 pre-pass: `str.indexof` / `str.replace` / `str.replace_all` — fold, partial-eval,
//! fence.
//!
//! All three ops are value-sorted FUNCTIONS (Int / String), so unlike the slice-12
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

/// Cap on the number of non-overlapping occurrences spliced into the
/// symbolic-`u` `str.replace_all` concat. Over-cap applications are left in
/// place and fence. Folding (all-literal) has NO cap.
const REPLACE_ALL_CONCAT_CAP: usize = 64;

/// Every occurrence position (code-point index) of `needle` in `hay`,
/// ascending, OVERLAPS INCLUDED. The empty needle occurs at every
/// `0..=|hay|` position (SMT-LIB semantics).
fn occurrences(hay: &[char], needle: &[char]) -> Vec<usize> {
    let (n, m) = (hay.len(), needle.len());
    if m > n {
        return Vec::new();
    }
    (0..=(n - m))
        .filter(|&j| hay[j..j + m] == *needle)
        .collect()
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

/// Non-overlapping occurrence positions of `needle` in `hay`, greedy
/// left-to-right: after a match at `j`, scanning resumes at `j + |needle|`.
/// The empty needle yields NO positions — SMT-LIB `str.replace_all` leaves `s`
/// unchanged on an empty needle (unlike `str.replace`/`str.indexof`).
fn nonoverlapping_occurrences(hay: &[char], needle: &[char]) -> Vec<usize> {
    let m = needle.len();
    if m == 0 {
        return Vec::new();
    }
    let n = hay.len();
    let mut out = Vec::new();
    let mut j = 0;
    while j + m <= n {
        if hay[j..j + m] == *needle {
            out.push(j);
            j += m;
        } else {
            j += 1;
        }
    }
    out
}

/// Concrete `(str.replace_all s t u)`: replace ALL non-overlapping occurrences
/// of `t` by `u`, left-to-right. Empty `t` or absent `t` → `s` unchanged
/// (`u` dropped).
fn eval_replace_all(hay: &[char], t: &[char], u: &str) -> String {
    let positions = nonoverlapping_occurrences(hay, t);
    if positions.is_empty() {
        return hay.iter().collect();
    }
    let m = t.len();
    let mut out = String::new();
    let mut cursor = 0usize;
    for &p in &positions {
        out.extend(&hay[cursor..p]);
        out.push_str(u);
        cursor = p + m;
    }
    out.extend(&hay[cursor..]);
    out
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
                Op::Builtin(BuiltinOp::StrReplaceAll) => rewrite_replace_all(ctx, &new_children),
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

/// Construct an Int literal from an i128 value.
fn int_num(ctx: &mut Context, v: i128) -> TermId {
    let int_s = ctx.int_sort();
    ctx.mk_numeral(shinri_core::Rational::from_int(v.into()), int_s)
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
    // Symbolic i, literal haystack+needle: the result as a function of i is a
    // STEP FUNCTION over the concrete occurrence positions o1 < … < ok:
    //   i < 0 → -1;  i ≤ o1 → o1;  o1 < i ≤ o2 → o2;  …;  i > ok → -1
    // (i > |s| needs no own arm: it also has no occurrence ≥ i → -1).
    // Emitted as an Int-ite chain; reduce_assertions' elim_term_ite eliminates
    // it downstream. Capped to bound term growth on adversarial literals.
    if hay.len() > INDEXOF_CHAIN_CAP {
        return None; // over-cap: leave in place → fence
    }
    let i = kids[2];
    let neg1 = int_num(ctx, -1);
    let zero = int_num(ctx, 0);
    if needle.is_empty() {
        // Spec §2.3 special case: (ite (and (>= i 0) (<= i |s|)) i -1).
        let n_lit = int_num(ctx, hay.len() as i128);
        let ge0 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[i, zero])
            .expect("i >= 0");
        let le_n = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[i, n_lit])
            .expect("i <= |s|");
        let in_range = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[ge0, le_n])
            .expect("in_range");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[in_range, i, neg1])
                .expect("empty-needle ite"),
        );
    }
    // Build the chain inside-out (last arm first).
    let mut chain = neg1;
    for &o in occurrences(&hay, &needle).iter().rev() {
        let ov = int_num(ctx, o as i128);
        let cond = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[i, ov])
            .expect("i <= o");
        chain = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[cond, ov, chain])
            .expect("chain ite");
    }
    let lt0 = ctx
        .mk_app(Op::Builtin(BuiltinOp::Lt), &[i, zero])
        .expect("i < 0");
    Some(
        ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[lt0, neg1, chain])
            .expect("outer ite"),
    )
}

/// `(str.replace s t u)`, children already rewritten. Some(_) iff haystack
/// and needle are literals — EXACT for any `u` (the decomposition point is
/// concrete). None (symbolic haystack/needle) leaves the app in place (→
/// fence).
fn rewrite_replace(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let hay: Vec<char> = ctx.string_const_value(kids[0])?.chars().collect();
    let t: Vec<char> = ctx.string_const_value(kids[1])?.chars().collect();
    let u = kids[2];
    let Some(&p) = occurrences(&hay, &t).first() else {
        // Needle absent: result is the haystack; `u` is irrelevant (exact).
        return Some(kids[0]);
    };
    if let Some(uv) = ctx.string_const_value(u).map(str::to_owned) {
        // Fully literal: fold to a single literal.
        return Some(ctx.mk_string_const(&eval_replace(&hay, &t, &uv)));
    }
    // Symbolic u: (str.++ pre u post), empty literal flanks dropped.
    let pre: String = hay[..p].iter().collect();
    let post: String = hay[p + t.len()..].iter().collect();
    let mut parts: Vec<TermId> = Vec::new();
    if !pre.is_empty() {
        parts.push(ctx.mk_string_const(&pre));
    }
    parts.push(u);
    if !post.is_empty() {
        parts.push(ctx.mk_string_const(&post));
    }
    Some(if parts.len() == 1 {
        parts[0]
    } else {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &parts)
            .expect("pre ++ u ++ post")
    })
}

/// `(str.replace_all s t u)`, children already rewritten. Some(_) iff haystack
/// and needle are literals — EXACT for any `u` (all split points are concrete).
/// None (symbolic haystack/needle, or over-cap occurrence count) leaves the app
/// in place (→ fence).
fn rewrite_replace_all(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let hay: Vec<char> = ctx.string_const_value(kids[0])?.chars().collect();
    let t: Vec<char> = ctx.string_const_value(kids[1])?.chars().collect();
    let u = kids[2];
    let positions = nonoverlapping_occurrences(&hay, &t);
    if positions.is_empty() {
        // Needle absent or empty: result is the haystack; `u` is irrelevant.
        return Some(kids[0]);
    }
    if let Some(uv) = ctx.string_const_value(u).map(str::to_owned) {
        // Fully literal: fold to a single literal.
        return Some(ctx.mk_string_const(&eval_replace_all(&hay, &t, &uv)));
    }
    // Symbolic u: bound the concat width by the occurrence count.
    if positions.len() > REPLACE_ALL_CONCAT_CAP {
        return None; // over-cap: leave in place → fence
    }
    // (str.++ pre u mid1 u … u post), empty literal gaps/flanks dropped.
    let m = t.len();
    let mut parts: Vec<TermId> = Vec::new();
    let mut cursor = 0usize;
    for &p in &positions {
        let gap: String = hay[cursor..p].iter().collect();
        if !gap.is_empty() {
            parts.push(ctx.mk_string_const(&gap));
        }
        parts.push(u);
        cursor = p + m;
    }
    let tail: String = hay[cursor..].iter().collect();
    if !tail.is_empty() {
        parts.push(ctx.mk_string_const(&tail));
    }
    Some(if parts.len() == 1 {
        parts[0]
    } else {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &parts)
            .expect("pre ++ u ++ … ++ post")
    })
}

/// Stage 2: presence fence. True iff any `str.indexof` / `str.replace`
/// application SURVIVED [`partial_eval_indexof_replace`] — symbolic haystack
/// or needle, an over-cap literal, or a non-literal-yet-foldable operand
/// (e.g. a constant substr, which only folds later in `reduce_assertions`).
/// The solver fences such queries to a sound `Unknown` (canary-pinned
/// flip-markers for a future symbolic-encoding slice).
pub fn has_unreduced_indexof_replace(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(
                    op,
                    Op::Builtin(
                        BuiltinOp::StrIndexOf | BuiltinOp::StrReplace | BuiltinOp::StrReplaceAll
                    )
                ) || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
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

    #[test]
    fn nonoverlapping_occurrences_are_greedy_left_to_right() {
        // Overlaps are NOT taken: "aaa"/"aa" matches only at 0 (resume at 2).
        assert_eq!(nonoverlapping_occurrences(&chars("aaa"), &chars("aa")), vec![0]);
        // Adjacent matches: "abab"/"ab" → {0, 2}.
        assert_eq!(nonoverlapping_occurrences(&chars("abab"), &chars("ab")), vec![0, 2]);
        // Single-char needle repeated.
        assert_eq!(nonoverlapping_occurrences(&chars("aaa"), &chars("a")), vec![0, 1, 2]);
        // Empty needle → NO positions (u dropped downstream).
        assert_eq!(nonoverlapping_occurrences(&chars("ab"), &chars("")), Vec::<usize>::new());
        // Code points, not bytes: 'l' in "héllo" at 2 and 3.
        assert_eq!(nonoverlapping_occurrences(&chars("héllo"), &chars("l")), vec![2, 3]);
    }

    #[test]
    fn eval_replace_all_pinned_semantics() {
        // All non-overlapping occurrences replaced.
        assert_eq!(eval_replace_all(&chars("abab"), &chars("ab"), "Z"), "ZZ");
        // Non-overlapping only: "aaa"/"aa" → "Xa" (NOT "XX").
        assert_eq!(eval_replace_all(&chars("aaa"), &chars("aa"), "X"), "Xa");
        // Needle absent → haystack unchanged (u dropped).
        assert_eq!(eval_replace_all(&chars("abc"), &chars("z"), "X"), "abc");
        // EMPTY needle → haystack unchanged, u DROPPED (contrast str.replace → "Xab").
        assert_eq!(eval_replace_all(&chars("ab"), &chars(""), "X"), "ab");
        // Code points.
        assert_eq!(eval_replace_all(&chars("héllo"), &chars("l"), "L"), "héLLo");
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
    fn folds_all_literal_replace_all() {
        let mut ctx = Context::new();
        let abab = ctx.mk_string_const("abab");
        let ab = ctx.mk_string_const("ab");
        let z = ctx.mk_string_const("Z");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[abab, ab, z])
            .unwrap();
        let want_lit = ctx.mk_string_const("ZZ");
        let atom = ctx.mk_eq(rep, want_lit).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        // (= "ZZ" "ZZ") — both sides the SAME TermId, and no replace_all survives.
        let want = ctx.mk_eq(want_lit, want_lit).unwrap();
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_indexof_replace(&ctx, &out));
    }

    #[test]
    fn folds_empty_needle_replace_all_drops_u() {
        // Empty needle: result is the haystack, u dropped (contrast str.replace).
        let mut ctx = Context::new();
        let ab = ctx.mk_string_const("ab");
        let empty = ctx.mk_string_const("");
        let x = ctx.mk_string_const("X");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[ab, empty, x])
            .unwrap();
        let r = str_var(&mut ctx, "r");
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let want = ctx.mk_eq(ab, r).unwrap(); // (= "ab" r)
        assert_eq!(out, vec![want]);
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

    // ── Partial-eval replace (symbolic u) ────────────────────────────────

    /// Destructure `(str.++ …)` into its children.
    fn concat_parts(ctx: &Context, t: TermId) -> Vec<TermId> {
        let TermNode::App { op, args, .. } = ctx.term_node(t) else {
            panic!("expected concat app");
        };
        assert!(matches!(op, Op::Builtin(BuiltinOp::StrConcat)));
        ctx.children(*args).to_vec()
    }

    #[test]
    fn replace_symbolic_u_decomposes_at_leftmost_occurrence() {
        let mut ctx = Context::new();
        let abcb = ctx.mk_string_const("abcb");
        let b = ctx.mk_string_const("b");
        let u = str_var(&mut ctx, "u");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[abcb, b, u])
            .unwrap();
        let out_s = str_var(&mut ctx, "r");
        let atom = ctx.mk_eq(rep, out_s).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        // (= (str.++ "a" u "cb") r) — leftmost "b" is at position 1.
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let eq_kids = ctx.children(args).to_vec();
        let parts = concat_parts(&ctx, eq_kids[0]);
        assert_eq!(parts.len(), 3);
        assert_eq!(ctx.string_const_value(parts[0]), Some("a"));
        assert_eq!(parts[1], u);
        assert_eq!(ctx.string_const_value(parts[2]), Some("cb"));
    }

    #[test]
    fn replace_empty_flanks_dropped() {
        let mut ctx = Context::new();
        let u = str_var(&mut ctx, "u2");
        let r = str_var(&mut ctx, "r2");
        // Whole-haystack needle: (str.replace "ab" "ab" u) → bare u.
        let ab = ctx.mk_string_const("ab");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[ab, ab, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let want = ctx.mk_eq(u, r).unwrap();
        assert_eq!(out, vec![want], "both flanks empty → result is bare u");
        // Empty needle: (str.replace "ab" "" u) → (str.++ u "ab").
        let empty = ctx.mk_string_const("");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[ab, empty, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let eq_kids = ctx.children(args).to_vec();
        let parts = concat_parts(&ctx, eq_kids[0]);
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0], u);
        assert_eq!(ctx.string_const_value(parts[1]), Some("ab"));
    }

    #[test]
    fn replace_needle_absent_drops_symbolic_u() {
        let mut ctx = Context::new();
        let abc = ctx.mk_string_const("abc");
        let z = ctx.mk_string_const("z");
        let u = str_var(&mut ctx, "u3");
        let r = str_var(&mut ctx, "r3");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[abc, z, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        // Result does not depend on u: (= "abc" r).
        let want = ctx.mk_eq(abc, r).unwrap();
        assert_eq!(out, vec![want]);
    }

    // ── Partial-eval indexof (symbolic start) ────────────────────────────

    fn is_ite(ctx: &Context, t: TermId) -> bool {
        matches!(
            ctx.term_node(t),
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Ite),
                ..
            }
        )
    }

    fn contains_op(ctx: &Context, t: TermId, want: BuiltinOp) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(o) if *o == want)
                    || ctx
                        .children(*args)
                        .to_vec()
                        .iter()
                        .any(|&c| contains_op(ctx, c, want))
            }
            TermNode::Const { .. } => false,
        }
    }

    #[test]
    fn indexof_symbolic_start_becomes_ite_chain() {
        let mut ctx = Context::new();
        let abcb = ctx.mk_string_const("abcb");
        let b = ctx.mk_string_const("b");
        let int_s = ctx.int_sort();
        let i = {
            let f = ctx.declare_fun("i", &[], int_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[abcb, b, i])
            .unwrap();
        let one = int_lit(&mut ctx, 1);
        let atom = ctx.mk_eq(idx, one).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(
            !contains_op(&ctx, out[0], BuiltinOp::StrIndexOf),
            "indexof must be rewritten away"
        );
        // The eq's lhs is now the outer (ite (< i 0) -1 …) chain.
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let lhs = ctx.children(args).to_vec()[0];
        assert!(is_ite(&ctx, lhs), "expected an Int-ite chain, got {lhs:?}");
        assert_eq!(ctx.sort_of(lhs), int_s);
    }

    #[test]
    fn indexof_empty_needle_symbolic_start_is_range_ite() {
        let mut ctx = Context::new();
        let ab = ctx.mk_string_const("ab");
        let empty = ctx.mk_string_const("");
        let int_s = ctx.int_sort();
        let i = {
            let f = ctx.declare_fun("i2", &[], int_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[ab, empty, i])
            .unwrap();
        let zero = int_lit(&mut ctx, 0);
        let atom = ctx.mk_eq(idx, zero).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(!contains_op(&ctx, out[0], BuiltinOp::StrIndexOf));
        // (ite (and (>= i 0) (<= i 2)) i -1): the chain contains i itself as
        // a branch and an And condition.
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let lhs = ctx.children(args).to_vec()[0];
        assert!(is_ite(&ctx, lhs));
        assert!(contains_op(&ctx, lhs, BuiltinOp::And));
    }

    #[test]
    fn indexof_over_cap_literal_left_in_place() {
        let mut ctx = Context::new();
        let big = ctx.mk_string_const(&"a".repeat(65)); // cap is 64
        let a = ctx.mk_string_const("a");
        let int_s = ctx.int_sort();
        let i = {
            let f = ctx.declare_fun("i3", &[], int_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[big, a, i])
            .unwrap();
        let zero = int_lit(&mut ctx, 0);
        let atom = ctx.mk_eq(idx, zero).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom], "over-cap must survive unchanged (→ fence)");
        // At exactly the cap it rewrites.
        let at_cap = ctx.mk_string_const(&"a".repeat(64));
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[at_cap, a, i])
            .unwrap();
        let atom = ctx.mk_eq(idx, zero).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(!contains_op(&ctx, out[0], BuiltinOp::StrIndexOf));
    }

    // ── Fence ─────────────────────────────────────────────────────────────

    #[test]
    fn fence_predicate_classification() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "sf");
        let b = ctx.mk_string_const("b");
        let zero = int_lit(&mut ctx, 0);
        let one = int_lit(&mut ctx, 1);
        // Symbolic haystack survives the rewrite → fence.
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[s, b, zero])
            .unwrap();
        let atom = ctx.mk_eq(idx, one).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(has_unreduced_indexof_replace(&ctx, &out));
        // Literal haystack folds → no fence.
        let abcb = ctx.mk_string_const("abcb");
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[abcb, b, zero])
            .unwrap();
        let atom = ctx.mk_eq(idx, one).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(!has_unreduced_indexof_replace(&ctx, &out));
    }

    // ── Partial-eval replace_all (symbolic u) ──────────────────────────────

    #[test]
    fn replace_all_symbolic_u_two_occurrences_concat() {
        // (str.replace_all "aza" "a" u) → (str.++ u "z" u): matches at 0 and 2.
        let mut ctx = Context::new();
        let aza = ctx.mk_string_const("aza");
        let a = ctx.mk_string_const("a");
        let u = str_var(&mut ctx, "u");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[aza, a, u])
            .unwrap();
        let out_s = str_var(&mut ctx, "r");
        let atom = ctx.mk_eq(rep, out_s).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let lhs = ctx.children(args).to_vec()[0];
        let parts = concat_parts(&ctx, lhs);
        assert_eq!(parts.len(), 3);
        assert_eq!(parts[0], u);
        assert_eq!(ctx.string_const_value(parts[1]), Some("z"));
        assert_eq!(parts[2], u);
        assert!(!has_unreduced_indexof_replace(&ctx, &out));
    }

    #[test]
    fn replace_all_symbolic_u_all_needle_collapses_to_bare_u_repeats() {
        // (str.replace_all "aa" "a" u) → (str.++ u u): both flanks/gaps empty.
        let mut ctx = Context::new();
        let aa = ctx.mk_string_const("aa");
        let a = ctx.mk_string_const("a");
        let u = str_var(&mut ctx, "u2");
        let r = str_var(&mut ctx, "r2");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[aa, a, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let lhs = ctx.children(args).to_vec()[0];
        let parts = concat_parts(&ctx, lhs);
        assert_eq!(parts, vec![u, u]);
    }

    #[test]
    fn replace_all_needle_absent_drops_symbolic_u() {
        let mut ctx = Context::new();
        let abc = ctx.mk_string_const("abc");
        let z = ctx.mk_string_const("z");
        let u = str_var(&mut ctx, "u3");
        let r = str_var(&mut ctx, "r3");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[abc, z, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let want = ctx.mk_eq(abc, r).unwrap(); // (= "abc" r): u irrelevant
        assert_eq!(out, vec![want]);
    }

    #[test]
    fn replace_all_over_cap_symbolic_u_fences() {
        // 65 single-char occurrences with symbolic u → over cap (64) → left in place.
        let mut ctx = Context::new();
        let big = ctx.mk_string_const(&"a".repeat(65));
        let a = ctx.mk_string_const("a");
        let u = str_var(&mut ctx, "u4");
        let r = str_var(&mut ctx, "r4");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[big, a, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom], "over-cap symbolic-u must survive unchanged");
        assert!(has_unreduced_indexof_replace(&ctx, &out), "→ fence");
        // At exactly the cap (64 occurrences) it rewrites.
        let at_cap = ctx.mk_string_const(&"a".repeat(64));
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[at_cap, a, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(!has_unreduced_indexof_replace(&ctx, &out), "at cap → rewritten");
    }

    #[test]
    fn replace_all_symbolic_haystack_fences() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "sf2");
        let a = ctx.mk_string_const("a");
        let x = ctx.mk_string_const("X");
        let r = str_var(&mut ctx, "rf2");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[s, a, x])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom], "symbolic haystack survives unchanged");
        assert!(has_unreduced_indexof_replace(&ctx, &out));
    }
}
