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

use crate::regex::{concat, range_rex, rex_to_term, star, union, Rex, MAX_CODE};

/// Max constant-word length that gets the order→membership rewrite. A length-k
/// word builds an O(k)-branch regex; SMT-LIB literal text is untrusted input
/// (threat model), so cap the blow-up. Above the cap ⇒ fence (sound Unknown).
/// Mirrors `regex::ENUM_WORD_CAP`.
const ORDER_CONST_LEN_CAP: usize = 256;

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
        // Constant word on the RIGHT: (str.< s w) / (str.<= s w).
        // (Empty y is handled by the empty-boundary arm above, so y is non-empty.)
        (None, Some(y)) => match word_codes(&y) {
            Some(cs) => order_const_right(ctx, a, &cs, reflexive),
            None => None, // above-alphabet char or over cap ⇒ fence
        },
        // Constant word on the LEFT: (str.< w s) / (str.<= w s).
        (Some(x), None) => match word_codes(&x) {
            Some(cs) => order_const_left(ctx, b, &cs, reflexive),
            None => None,
        },
        _ => None,
    }
}

/// The code points of a constant word, each within the SMT-LIB alphabet, or
/// `None` if the word is empty, contains a char above `MAX_CODE`, or exceeds
/// `ORDER_CONST_LEN_CAP` (all of which fall through to the fence — sound
/// Unknown, never wrong). Generalizes slice 24's `single_char_code` to any
/// length; the k=1 result reproduces the single-char arms exactly.
fn word_codes(s: &str) -> Option<Vec<i128>> {
    if s.is_empty() || s.chars().count() > ORDER_CONST_LEN_CAP {
        return None;
    }
    s.chars()
        .map(|c| ((c as u32) <= MAX_CODE).then_some(c as u32 as i128))
        .collect()
}

/// Σ* = re.all — any string (including empty).
fn sigma_star() -> Rex {
    star(Rex::Range(0, MAX_CODE))
}

/// Σ = re.allchar — exactly one character.
fn sigma() -> Rex {
    Rex::Range(0, MAX_CODE)
}

/// `(str.in_re other <r>)`.
fn membership(ctx: &mut Context, other: TermId, r: Rex) -> TermId {
    let rt = rex_to_term(ctx, &r);
    ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[other, rt])
        .expect("str.in_re well-sorted")
}

/// The exact-word language `word(w) = Range(c₀,c₀)·…·Range(c_{k-1},c_{k-1})`
/// as a `Rex` (empty slice ⇒ `Eps`). Every code is in-alphabet (guaranteed by
/// `word_codes`), so each `Range` is expressible.
fn word_rex(cs: &[i128]) -> Rex {
    concat(cs.iter().map(|&c| Rex::Range(c as u32, c as u32)).collect())
}

/// `(str.< s w)` / `(str.<= s w)` for a constant word `w` (codes `cs`, k = |w| ≥ 1)
/// and symbolic `s`. `reflexive` = the `<=` case (adds the word `w` itself).
///
/// `s <  w` ≡ s ∈  ⋃_{j<k} word(w[0..j])                      (proper prefixes: ε, w[0..1], …)
///                ∪ ⋃_{i<k} word(w[0..i])·Range(0, cᵢ-1)·Σ*   (first differ at i, sᵢ < cᵢ)
/// `s <= w` ≡  … ∪ word(w)                                    (… or s = w)
///
/// k = 1 reproduces slice 24's `Eps ∪ Range(0,c₀-1)·Σ*` (+ word for `<=`).
/// `None` only if a `range_rex` interior endpoint is an inexpressible surrogate
/// — unreachable for an in-alphabet word (a valid char's neighbour is at worst a
/// block edge), but propagated for totality.
fn order_const_right(ctx: &mut Context, s: TermId, cs: &[i128], reflexive: bool) -> Option<TermId> {
    let mut branches: Vec<Rex> = Vec::new();
    for j in 0..cs.len() {
        branches.push(word_rex(&cs[..j])); // proper prefix (j = 0 ⇒ Eps)
    }
    for i in 0..cs.len() {
        branches.push(concat(vec![
            word_rex(&cs[..i]),
            range_rex(0, cs[i] - 1)?,
            sigma_star(),
        ]));
    }
    if reflexive {
        branches.push(word_rex(cs)); // word(w)
    }
    Some(membership(ctx, s, union(branches)))
}

/// `(str.< w s)` / `(str.<= w s)` for a constant word `w` (codes `cs`, k ≥ 1)
/// and symbolic `s`. `reflexive` = the `<=` case.
///
/// `w <  s` ≡ s ∈  ⋃_{i<k} word(w[0..i])·Range(cᵢ+1, MAX)·Σ*  (first differ at i, sᵢ > cᵢ)
///                ∪ word(w)·Σ·Σ*                              (w a PROPER prefix of s)
/// `w <= s` ≡  ⋃ (differ) ∪ word(w)·Σ*                        (… or w a prefix incl. = w)
///
/// k = 1 reproduces slice 24's `Range(c₀+1,MAX)·Σ* ∪ word(c₀)·(Σ·Σ* | Σ*)`.
fn order_const_left(ctx: &mut Context, s: TermId, cs: &[i128], reflexive: bool) -> Option<TermId> {
    let mut branches: Vec<Rex> = Vec::new();
    for i in 0..cs.len() {
        branches.push(concat(vec![
            word_rex(&cs[..i]),
            range_rex(cs[i] + 1, MAX_CODE as i128)?,
            sigma_star(),
        ]));
    }
    let word_w = word_rex(cs);
    let prefix = if reflexive {
        concat(vec![word_w, sigma_star()]) // word(w)·Σ*
    } else {
        concat(vec![word_w, sigma(), sigma_star()]) // word(w)·Σ·Σ*
    };
    branches.push(prefix);
    Some(membership(ctx, s, union(branches)))
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

    #[test]
    fn fence_recurses_into_nested_str_order() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let u = str_var(&mut ctx, "u");
        // s < u over two distinct free vars: no arm fires -> survives.
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, u);
        // Bury it: (not (str.< s u)).
        let nested = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[lt]).unwrap();
        let out = rewrite_str_order(&mut ctx, &[nested]);
        assert_eq!(out, vec![nested]);
        assert!(has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn single_char_const_right_rewrites() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let b = ctx.mk_string_const("b"); // code 98
                                          // (str.< s "b") ≡ s ∈ Eps ∪ Range(0,'a')·Σ*.
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, b);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        let want_lang = union(vec![
            Rex::Eps,
            concat(vec![Rex::Range(0, 97), star(Rex::Range(0, MAX_CODE))]),
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_str_order(&ctx, &out));
        // (str.<= s "b") adds the singleton word "b" = Range(98,98).
        let le = order(&mut ctx, BuiltinOp::StrLeq, s, b);
        let out = rewrite_str_order(&mut ctx, &[le]);
        let want_lang = union(vec![
            Rex::Eps,
            concat(vec![Rex::Range(0, 97), star(Rex::Range(0, MAX_CODE))]),
            Rex::Range(98, 98),
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
    }

    #[test]
    fn single_char_const_right_null_char_collapses_to_empty() {
        // (str.< s "\0") (m = 0): Range(0,-1) is empty ⇒ union([Eps, Empty]) = Eps ≡ s = "".
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let nul = ctx.mk_string_const("\u{0}");
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, nul);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        let want = membership(&mut ctx, s, Rex::Eps);
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn single_char_const_right_null_char_leq_keeps_word_branch() {
        // (str.<= s "\0") (m = 0): the below-range Range(0,-1) is empty and drops,
        // but the reflexive word branch survives:
        // s ∈ Eps ∪ Range(0,0) ≡ s = "" ∨ s = "\0".
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let nul = ctx.mk_string_const("\u{0}");
        let le = order(&mut ctx, BuiltinOp::StrLeq, s, nul);
        let out = rewrite_str_order(&mut ctx, &[le]);
        let want = membership(&mut ctx, s, union(vec![Rex::Eps, Rex::Range(0, 0)]));
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn multi_char_const_right_now_rewrites() {
        // Slice 30: a length-≥2 constant on the RIGHT now rewrites to membership
        // (was fenced pre-slice-30). (str.< s "bc") ≡
        //   s ∈ Eps ∪ "b" ∪ Range(0,'a')·Σ* ∪ "b"·Range(0,'b')·Σ*.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let bc = ctx.mk_string_const("bc"); // codes 98, 99
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, bc);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        let want_lang = union(vec![
            Rex::Eps,                                                       // proper prefix j=0 (ε)
            Rex::Range(98, 98), // proper prefix j=1 ("b")
            concat(vec![Rex::Range(0, 97), star(Rex::Range(0, MAX_CODE))]), // differ i=0
            concat(vec![
                Rex::Range(98, 98),
                Rex::Range(0, 98),
                star(Rex::Range(0, MAX_CODE)),
            ]), // differ i=1: "b"·Range(0,'b')·Σ*
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_str_order(&ctx, &out));

        // (str.<= s "bc") additionally admits the word "bc" itself.
        let le = order(&mut ctx, BuiltinOp::StrLeq, s, bc);
        let out = rewrite_str_order(&mut ctx, &[le]);
        let want_lang = union(vec![
            Rex::Eps,
            Rex::Range(98, 98),
            concat(vec![Rex::Range(0, 97), star(Rex::Range(0, MAX_CODE))]),
            concat(vec![
                Rex::Range(98, 98),
                Rex::Range(0, 98),
                star(Rex::Range(0, MAX_CODE)),
            ]),
            concat(vec![Rex::Range(98, 98), Rex::Range(99, 99)]), // word "bc"
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
    }

    #[test]
    fn single_char_const_left_rewrites() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let b = ctx.mk_string_const("b"); // code 98
                                          // (str.< "b" s) ≡ s ∈ Range(99,MAX)·Σ* ∪ "b"·Σ·Σ*.
        let lt = order(&mut ctx, BuiltinOp::StrLt, b, s);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        let want_lang = union(vec![
            concat(vec![
                Rex::Range(99, MAX_CODE),
                star(Rex::Range(0, MAX_CODE)),
            ]),
            concat(vec![
                Rex::Range(98, 98),
                Rex::Range(0, MAX_CODE),
                star(Rex::Range(0, MAX_CODE)),
            ]),
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_str_order(&ctx, &out));
        // (str.<= "b" s) ≡ s ∈ Range(99,MAX)·Σ* ∪ "b"·Σ*.
        let le = order(&mut ctx, BuiltinOp::StrLeq, b, s);
        let out = rewrite_str_order(&mut ctx, &[le]);
        let want_lang = union(vec![
            concat(vec![
                Rex::Range(99, MAX_CODE),
                star(Rex::Range(0, MAX_CODE)),
            ]),
            concat(vec![Rex::Range(98, 98), star(Rex::Range(0, MAX_CODE))]),
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
    }

    #[test]
    fn single_char_const_left_max_char_drops_range_branch() {
        // c = U+2FFFF (greatest char): Range(MAX+1, MAX) empty ⇒ only the prefix branch.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let mx = ctx.mk_string_const("\u{2FFFF}");
        let lt = order(&mut ctx, BuiltinOp::StrLt, mx, s);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        let want_lang = concat(vec![
            Rex::Range(MAX_CODE, MAX_CODE),
            Rex::Range(0, MAX_CODE),
            star(Rex::Range(0, MAX_CODE)),
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn above_alphabet_const_survives_to_fence() {
        // U+30001 > MAX_CODE: out of the SMT-LIB alphabet — banked ⇒ fence, both
        // orientations (pre-guard these panicked on out-of-alphabet Range terms).
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let c = ctx.mk_string_const("\u{30001}");
        for (l, r) in [(s, c), (c, s)] {
            for op in [BuiltinOp::StrLt, BuiltinOp::StrLeq] {
                let atom = order(&mut ctx, op, l, r);
                let out = rewrite_str_order(&mut ctx, &[atom]);
                assert_eq!(out, vec![atom]);
                assert!(has_unreduced_str_order(&ctx, &out));
            }
        }
    }

    #[test]
    fn max_code_char_still_decides() {
        // Exactly MAX_CODE (U+2FFFF) is IN the alphabet and must keep deciding.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let mx = ctx.mk_string_const("\u{2FFFF}");
        let le = order(&mut ctx, BuiltinOp::StrLeq, s, mx);
        let out = rewrite_str_order(&mut ctx, &[le]);
        assert!(
            !has_unreduced_str_order(&ctx, &out),
            "in-alphabet max char must not fence"
        );
    }

    #[test]
    fn single_char_const_block_edge_does_not_fence() {
        // c = U+E000 (first char above the surrogate block): the endpoint m-1 = 0xDFFF
        // is the block EDGE (expressible) ⇒ must NOT fence (spec §3: guard is
        // provably non-load-bearing for a single char).
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let c = ctx.mk_string_const("\u{E000}"); // code 0xE000
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, c);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        assert!(
            !has_unreduced_str_order(&ctx, &out),
            "block-edge endpoint must not fence"
        );
        let want_lang = union(vec![
            Rex::Eps,
            concat(vec![Rex::Range(0, 0xDFFF), star(Rex::Range(0, MAX_CODE))]),
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
    }

    #[test]
    fn multi_char_const_left_now_rewrites() {
        // (str.< "bc" s) ≡ s ∈ Range(99,MAX)·Σ* ∪ "b"·Range(100,MAX)·Σ* ∪ "bc"·Σ·Σ*.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let bc = ctx.mk_string_const("bc"); // codes 98, 99
        let lt = order(&mut ctx, BuiltinOp::StrLt, bc, s);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        let want_lang = union(vec![
            concat(vec![
                Rex::Range(99, MAX_CODE),
                star(Rex::Range(0, MAX_CODE)),
            ]), // differ i=0
            concat(vec![
                Rex::Range(98, 98),
                Rex::Range(100, MAX_CODE),
                star(Rex::Range(0, MAX_CODE)),
            ]), // differ i=1
            concat(vec![
                Rex::Range(98, 98),
                Rex::Range(99, 99),
                Rex::Range(0, MAX_CODE),
                star(Rex::Range(0, MAX_CODE)),
            ]), // "bc"·Σ·Σ*
        ]);
        let want = membership(&mut ctx, s, want_lang);
        assert_eq!(out, vec![want]);
        assert!(!has_unreduced_str_order(&ctx, &out));
    }

    #[test]
    fn const_word_over_cap_survives_to_fence() {
        // A constant word longer than ORDER_CONST_LEN_CAP is banked ⇒ fence.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let long = ctx.mk_string_const(&"a".repeat(ORDER_CONST_LEN_CAP + 1));
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, long);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        assert_eq!(out, vec![lt]);
        assert!(has_unreduced_str_order(&ctx, &out));
        // Exactly at the cap still rewrites (does not fence).
        let at = ctx.mk_string_const(&"a".repeat(ORDER_CONST_LEN_CAP));
        let lt2 = order(&mut ctx, BuiltinOp::StrLt, s, at);
        let out2 = rewrite_str_order(&mut ctx, &[lt2]);
        assert!(
            !has_unreduced_str_order(&ctx, &out2),
            "at-cap word must rewrite"
        );
    }

    #[test]
    fn const_word_block_edge_interior_does_not_fence() {
        // Multi-char word with a char at the surrogate block boundary: the interior
        // class Range(0, 0xE000-1) = Range(0, 0xDFFF) is a block EDGE (expressible),
        // so the word rewrites without fencing (generalizes
        // single_char_const_block_edge_does_not_fence to an interior position).
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let w = ctx.mk_string_const("\u{E000}b"); // codes 0xE000, 98
        let lt = order(&mut ctx, BuiltinOp::StrLt, s, w);
        let out = rewrite_str_order(&mut ctx, &[lt]);
        assert!(
            !has_unreduced_str_order(&ctx, &out),
            "block-edge interior must not fence"
        );
    }
}
