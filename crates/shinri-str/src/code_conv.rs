//! Slice 18 pre-pass: `str.to_code` / `str.from_code` / `str.is_digit` —
//! exact rewriting + fence.
//!
//! Every rewrite in this module is a FULL logical equivalence — sound at any
//! position, any polarity, any occurrence count. No model repair, no length
//! pins, no occurrence analysis (unlike int_conv's slice-17 stage): the
//! fragment is decided by a SINGLE bottom-up pass plus a presence fence.
//!
//! Stages (run by the solver's string-path seam, right after int_conv):
//! 1. [`rewrite_code_conv`] — bottom-up memoized rewrite applying the whole
//!    spec catalog (R1–R10): literal folds, both roundtrip rewrites,
//!    constant-RHS atom equivalences (either orientation), and `str.is_digit`
//!    expansion. (Lands in Tasks 2–3.)
//! 2. [`has_unreduced_code_conv`] — presence fence: any surviving
//!    application ⇒ the solver returns a sound `Unknown`.
//!
//! Representational fence: `Box<str>` cannot hold surrogate code points
//! (`0xD800..=0xDFFF`) even though the SMT-LIB alphabet includes them —
//! `from_code(<surrogate k>)` never folds and `to_code(s) = <surrogate k>`
//! never rewrites; both survive to the fence. Input literals cannot contain
//! surrogates (the parser does not decode `\u{...}` escapes), so the
//! literal side of an equality needs no surrogate case.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Integer, Op, Rational, TermId, TermNode};

use crate::int_conv::int_const_value;
use crate::regex::{rex_to_term, Rex};

/// Largest SMT-LIB string character (inclusive): U+2FFFF.
pub const MAX_CODE: i128 = 0x2FFFF;

fn is_surrogate(k: i128) -> bool {
    (0xD800..=0xDFFF).contains(&k)
}

/// The singleton string's char for in-alphabet, NON-surrogate `k`; None for
/// surrogates (in the SMT-LIB alphabet but unrepresentable in `Box<str>`)
/// and out-of-alphabet values.
fn char_of_code(k: i128) -> Option<char> {
    if !(0..=MAX_CODE).contains(&k) || is_surrogate(k) {
        return None;
    }
    char::from_u32(k as u32)
}

/// Concrete `str.to_code(s)` per SMT-LIB 2.6: the code point for a singleton,
/// `-1` otherwise. None (no fold) for a singleton ABOVE the SMT-LIB alphabet
/// — such a literal is not a valid String value; leave it to the fence.
fn eval_to_code(s: &str) -> Option<Integer> {
    let mut it = s.chars();
    match (it.next(), it.next()) {
        (Some(c), None) => {
            let code = c as u32 as i128;
            if code > MAX_CODE {
                return None;
            }
            Some(Integer::from(code))
        }
        _ => Some(Integer::from(-1i128)),
    }
}

/// Concrete `str.from_code(k)` per SMT-LIB 2.6: the singleton for in-alphabet
/// `k`, `""` for out-of-alphabet `k` (including values beyond i128). None
/// (no fold -> fence) for surrogates: representable in the SMT-LIB alphabet
/// but not in `Box<str>`.
fn eval_from_code(k: &Integer) -> Option<String> {
    match k.to_i128() {
        Some(v) if (0..=MAX_CODE).contains(&v) => char_of_code(v).map(String::from),
        _ => Some(String::new()),
    }
}

/// Two passes over the assertion list.
///
/// Pass 1 (slice 18, R1–R10): bottom-up, memoized; untouched subtrees keep
/// their TermIds. Every rule is a full equivalence — no model repair, no
/// polarity tracking, no occurrence analysis.
///
/// Pass 2 (slice 22): the `str.to_code` character-range gadget. It runs SECOND
/// so every foldable `to_code` application is already gone and it only ever
/// sees genuinely symbolic ones.
pub fn rewrite_code_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    let folded: Vec<TermId> = assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect();

    // The top-level assertion list is an implicit conjunction (§1.3).
    let fused = fuse_bounds(ctx, &folded);
    let mut gmemo: FxHashMap<TermId, TermId> = FxHashMap::default();
    fused.iter().map(|&a| gadget(ctx, a, &mut gmemo)).collect()
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
                Op::Builtin(BuiltinOp::StrToCode) => rewrite_to_code(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrFromCode) => rewrite_from_code(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrIsDigit) => rewrite_is_digit(ctx, new_children[0]),
                Op::Builtin(BuiltinOp::Eq) => try_code_atom(ctx, &new_children),
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
                        .expect("code_conv: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// `(str.to_code x)`, child already rewritten. R1 fold + R2 roundtrip.
/// None leaves the app in place (-> fence).
fn rewrite_to_code(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    // R1: fold a literal argument.
    if let Some(s) = ctx.string_const_value(kids[0]).map(str::to_owned) {
        let v = eval_to_code(&s)?;
        let int_s = ctx.int_sort();
        return Some(ctx.mk_numeral(Rational::from_int(v), int_s));
    }
    // R2: to_code(from_code(n)) → ite(0 <= n <= MAX_CODE, n, -1). Exact for
    // ALL n — surrogates included, since no literal is minted.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrFromCode),
        args,
        ..
    } = ctx.term_node(kids[0]).clone()
    {
        let n = ctx.children(args)[0];
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(Rational::from_int(Integer::zero()), int_s);
        let max = ctx.mk_numeral(Rational::from_int(Integer::from(MAX_CODE)), int_s);
        let neg1 = ctx.mk_numeral(Rational::from_int(Integer::from(-1i128)), int_s);
        let ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero])
            .expect("n >= 0");
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[n, max])
            .expect("n <= MAX_CODE");
        let in_range = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[ge, le])
            .expect("range conj");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[in_range, n, neg1])
                .expect("roundtrip ite"),
        );
    }
    None
}

/// `(str.from_code x)`, child already rewritten. R1 fold + R3 roundtrip.
/// None leaves the app in place (-> fence; surrogate literals land here).
fn rewrite_from_code(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    // R1: fold a numeral argument (None on a surrogate -> fence).
    if let Some(k) = int_const_value(ctx, kids[0]) {
        let s = eval_from_code(&k)?;
        return Some(ctx.mk_string_const(&s));
    }
    // R3: from_code(to_code(s)) → ite(len(s) = 1, s, ""). Exact: for a
    // singleton the code roundtrips (surrogates cannot occur in s — Box<str>);
    // otherwise to_code = -1 and from_code(-1) = "".
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrToCode),
        args,
        ..
    } = ctx.term_node(kids[0]).clone()
    {
        let s = ctx.children(args)[0];
        let len = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[s])
            .expect("len");
        let int_s = ctx.int_sort();
        let one = ctx.mk_numeral(Rational::from_int(Integer::one()), int_s);
        let cond = ctx.mk_eq(len, one).expect("len = 1");
        let empty = ctx.mk_string_const("");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[cond, s, empty])
                .expect("roundtrip ite"),
        );
    }
    None
}

/// `(str.is_digit x)`, child already rewritten. R1 fold for a literal; R10
/// expansion otherwise: `(or (= t "0") … (= t "9"))` — each minted equality
/// is routed back through the atom rules, so `is_digit(from_code(n))`
/// reduces fully in this same pass (no fixpoint loop).
fn rewrite_is_digit(ctx: &mut Context, t: TermId) -> Option<TermId> {
    if let Some(s) = ctx.string_const_value(t).map(str::to_owned) {
        let mut it = s.chars();
        let v = matches!((it.next(), it.next()), (Some('0'..='9'), None));
        return Some(ctx.mk_const_bool(v));
    }
    let disjuncts: Vec<TermId> = ('0'..='9')
        .map(|d| {
            let lit = ctx.mk_string_const(&d.to_string());
            let kids = [t, lit];
            try_code_atom(ctx, &kids)
                .unwrap_or_else(|| ctx.mk_eq(t, lit).expect("is_digit: t = digit"))
        })
        .collect();
    Some(
        ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disjuncts)
            .expect("is_digit expansion"),
    )
}

/// R4–R9: constant-RHS equality atoms, either orientation. Children are
/// already rewritten (so a foldable side has already folded). None → not a
/// code-conv atom, or the surrogate fence.
fn try_code_atom(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    if kids.len() != 2 {
        return None;
    }
    for (a, b) in [(kids[0], kids[1]), (kids[1], kids[0])] {
        match ctx.term_node(a).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrToCode),
                args,
                ..
            } => {
                let s = ctx.children(args)[0];
                if let Some(k) = int_const_value(ctx, b) {
                    return rw_to_code_const(ctx, s, &k);
                }
            }
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrFromCode),
                args,
                ..
            } => {
                let n = ctx.children(args)[0];
                if let Some(lit) = ctx.string_const_value(b).map(str::to_owned) {
                    return Some(rw_from_code_const(ctx, n, &lit));
                }
            }
            _ => {}
        }
    }
    None
}

/// R4/R5/R6: `(= (str.to_code s) k)` — a full partition of k:
/// `-1` ⇒ `not (len(s) = 1)`; in-alphabet non-surrogate ⇒ `s = "<char k>"`;
/// surrogate ⇒ None (representational fence); anything else ⇒ `false`.
fn rw_to_code_const(ctx: &mut Context, s: TermId, k: &Integer) -> Option<TermId> {
    match k.to_i128() {
        Some(-1) => {
            let len = ctx
                .mk_app(Op::Builtin(BuiltinOp::StrLen), &[s])
                .expect("len");
            let int_s = ctx.int_sort();
            let one = ctx.mk_numeral(Rational::from_int(Integer::one()), int_s);
            let eq1 = ctx.mk_eq(len, one).expect("len = 1");
            Some(
                ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq1])
                    .expect("not singleton"),
            )
        }
        Some(v) if (0..=MAX_CODE).contains(&v) => {
            let c = char_of_code(v)?; // surrogate → fence
            let lit = ctx.mk_string_const(&c.to_string());
            Some(ctx.mk_eq(s, lit).expect("s = char"))
        }
        // k <= -2, k > MAX_CODE, or |k| beyond i128: outside to_code's range.
        _ => Some(ctx.mk_const_bool(false)),
    }
}

/// R7/R8/R9: `(= (str.from_code n) "lit")`.
fn rw_from_code_const(ctx: &mut Context, n: TermId, lit: &str) -> TermId {
    if lit.is_empty() {
        // R8: the out-of-alphabet escape — n < 0 ∨ n > MAX_CODE.
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(Rational::from_int(Integer::zero()), int_s);
        let max = ctx.mk_numeral(Rational::from_int(Integer::from(MAX_CODE)), int_s);
        let lt = ctx
            .mk_app(Op::Builtin(BuiltinOp::Lt), &[n, zero])
            .expect("n < 0");
        let gt = ctx
            .mk_app(Op::Builtin(BuiltinOp::Gt), &[n, max])
            .expect("n > MAX_CODE");
        return ctx
            .mk_app(Op::Builtin(BuiltinOp::Or), &[lt, gt])
            .expect("escape disj");
    }
    let mut it = lit.chars();
    match (it.next(), it.next()) {
        // R7: from_code is injective on the alphabet ⇒ n = code(c).
        (Some(c), None) if (c as u32 as i128) <= MAX_CODE => {
            let int_s = ctx.int_sort();
            let code = ctx.mk_numeral(Rational::from_int(Integer::from(c as u32 as i128)), int_s);
            ctx.mk_eq(n, code).expect("n = code")
        }
        // R9: multi-char, or a singleton above the alphabet — outside
        // from_code's range.
        _ => ctx.mk_const_bool(false),
    }
}

// ─── Slice 22: the str.to_code character-range gadget ────────────────────
//
// A SECOND pass over the same assertion list, run after the slice-18 pass
// above (so every foldable `str.to_code` application is already gone and only
// genuinely symbolic ones remain). Every rule is a full equivalence.

/// A `str.to_code` inequality atom canonicalized to the lower-bound form
/// `to_code(s) >= k`, possibly negated (spec §1.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Bound {
    k: i128,
    negated: bool,
}

/// Clamp a threshold to `[-2, MAX_CODE + 1]`. Exact, because `to_code` is
/// total into `{-1} ∪ [0, MAX_CODE]`: every value below `-1` makes
/// `to_code(s) >= k` a tautology, and every value above `MAX_CODE` makes it
/// unsatisfiable. Clamping removes the i128-overflow and bignum cases in one
/// step, so the `+1` shifts below cannot overflow.
fn clamp_code(k: &Integer) -> i128 {
    match k.to_i128() {
        Some(v) => v.clamp(-2, MAX_CODE + 1),
        None if k.is_negative() => -2,
        None => MAX_CODE + 1,
    }
}

/// `(>= k (str.to_code s))` ≡ `(<= (str.to_code s) k)` — mirroring the operator
/// is how the reversed orientation joins the same canonical table.
fn mirror(op: BuiltinOp) -> BuiltinOp {
    match op {
        BuiltinOp::Ge => BuiltinOp::Le,
        BuiltinOp::Le => BuiltinOp::Ge,
        BuiltinOp::Gt => BuiltinOp::Lt,
        BuiltinOp::Lt => BuiltinOp::Gt,
        other => other,
    }
}

/// The String argument of a `(str.to_code s)` application.
fn to_code_arg(ctx: &Context, t: TermId) -> Option<TermId> {
    match ctx.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrToCode),
            args,
            ..
        } => Some(ctx.children(*args)[0]),
        _ => None,
    }
}

/// Spec §1.1: match `(⋈ (str.to_code s) k)` / `(⋈ k (str.to_code s))` for
/// `⋈ ∈ {>=, >, <=, <}` and constant Int `k`, canonicalized to
/// `to_code(s) >= b.k`. The strict/non-strict shifts are exact because
/// `to_code` is Int-valued.
fn match_code_ineq(ctx: &Context, op: BuiltinOp, kids: &[TermId]) -> Option<(TermId, Bound)> {
    if kids.len() != 2 {
        return None;
    }
    let (s, k, op) = if let Some(s) = to_code_arg(ctx, kids[0]) {
        (s, clamp_code(&int_const_value(ctx, kids[1])?), op)
    } else if let Some(s) = to_code_arg(ctx, kids[1]) {
        (s, clamp_code(&int_const_value(ctx, kids[0])?), mirror(op))
    } else {
        return None;
    };
    let b = match op {
        BuiltinOp::Ge => Bound { k, negated: false },
        BuiltinOp::Gt => Bound {
            k: k + 1,
            negated: false,
        },
        BuiltinOp::Le => Bound {
            k: k + 1,
            negated: true,
        },
        BuiltinOp::Lt => Bound { k, negated: true },
        _ => return None,
    };
    Some((s, b))
}

/// `s ∈ Range(lo, hi)` as a `str.in_re` term. An empty interval is `false`.
///
/// None ⇒ the representational fence (spec §3.1): `range_term` encodes the FULL
/// surrogate block via `re.diff`, so `0xD800` is an admissible `lo` and
/// `0xDFFF` an admissible `hi`, but an endpoint STRICTLY inside the block would
/// need a lone-surrogate `re.range` endpoint, which is not a `Box<str>`. The
/// caller then leaves the atom alone and `has_unreduced_code_conv` turns it into
/// a sound Unknown.
///
/// The empty-interval check comes FIRST, deliberately: `48 <= to_code(s) <= 47`
/// is unsatisfiable whatever the endpoints are, so it decides even when they
/// would not have been expressible.
fn range_membership(ctx: &mut Context, s: TermId, lo: i128, hi: i128) -> Option<TermId> {
    if lo > hi {
        return Some(ctx.mk_const_bool(false));
    }
    debug_assert!((0..=MAX_CODE).contains(&lo) && (0..=MAX_CODE).contains(&hi));
    if (is_surrogate(lo) && lo != 0xD800) || (is_surrogate(hi) && hi != 0xDFFF) {
        return None;
    }
    let r = rex_to_term(ctx, &Rex::Range(lo as u32, hi as u32));
    Some(
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, r])
            .expect("str.in_re well-sorted"),
    )
}

/// Spec §1.2, for a bound no fusion group claimed. None ⇒ not a `to_code`
/// inequality atom, or an inexpressible threshold (→ fence).
fn try_code_ineq_atom(ctx: &mut Context, op: Op, kids: &[TermId]) -> Option<TermId> {
    let Op::Builtin(bop) = op else { return None };
    if !matches!(
        bop,
        BuiltinOp::Ge | BuiltinOp::Gt | BuiltinOp::Le | BuiltinOp::Lt
    ) {
        return None;
    }
    let (s, b) = match_code_ineq(ctx, bop, kids)?;
    // Degenerate thresholds fold to constants, negation included.
    if b.k <= -1 {
        return Some(ctx.mk_const_bool(!b.negated)); // `>= k` is a tautology
    }
    if b.k > MAX_CODE {
        return Some(ctx.mk_const_bool(b.negated)); // `>= k` is unsatisfiable
    }
    let m = range_membership(ctx, s, b.k, MAX_CODE)?;
    Some(if b.negated {
        ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[m])
            .expect("not membership")
    } else {
        m
    })
}

/// Canonicalize a whole conjunct to `(s, to_code(s) >= k)` (spec §1.1),
/// absorbing an optional `not` wrapper into the polarity. None ⇒ not a
/// `to_code` bound, so it passes through the conjunction untouched.
fn match_bound(ctx: &Context, t: TermId) -> Option<(TermId, Bound)> {
    let (inner, neg) = match ctx.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Not),
            args,
            ..
        } => (ctx.children(*args)[0], true),
        _ => (t, false),
    };
    let TermNode::App {
        op: Op::Builtin(bop),
        args,
        ..
    } = ctx.term_node(inner)
    else {
        return None;
    };
    let (bop, kids) = (*bop, ctx.children(*args).to_vec());
    let (s, mut b) = match_code_ineq(ctx, bop, &kids)?;
    if neg {
        b.negated = !b.negated;
    }
    Some((s, b))
}

/// Spec §1.3 interval meet: the bounds on ONE string term within ONE
/// conjunction collapse to a single membership. None ⇒ the fused range has an
/// inexpressible endpoint (§3.1) and the caller must leave the group alone.
fn fuse_group(ctx: &mut Context, s: TermId, bounds: &[Bound]) -> Option<TermId> {
    let mut lo: Option<i128> = None; // max of the positive thresholds
    let mut cap: Option<i128> = None; // min of the negated thresholds
    for b in bounds {
        // Degenerate thresholds fold to constants (§1.2) and so never enter the
        // meet: a tautological conjunct drops out, an unsatisfiable one
        // collapses the whole conjunction.
        if b.k <= -1 {
            // `to_code(s) >= k` is a tautology.
            if b.negated {
                return Some(ctx.mk_const_bool(false));
            }
            continue;
        }
        if b.k > MAX_CODE {
            // `to_code(s) >= k` is unsatisfiable.
            if !b.negated {
                return Some(ctx.mk_const_bool(false));
            }
            continue;
        }
        if b.negated {
            cap = Some(cap.map_or(b.k, |c| c.min(b.k)));
        } else {
            lo = Some(lo.map_or(b.k, |l| l.max(b.k)));
        }
    }
    match (lo, cap) {
        // A lower bound forces len(s) = 1, which kills the `-1` escape and
        // turns every upper bound into a clean interval cap.
        (Some(lo), cap) => range_membership(ctx, s, lo, cap.map_or(MAX_CODE, |c| c - 1)),
        // Upper bounds only: the `len != 1` escape survives, so this is a
        // genuine complement — but still ONE membership.
        (None, Some(cap)) => {
            let m = range_membership(ctx, s, cap, MAX_CODE)?;
            Some(
                ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[m])
                    .expect("not membership"),
            )
        }
        // Every bound was degenerate and dropped: vacuously true.
        (None, None) => Some(ctx.mk_const_bool(true)),
    }
}

/// Spec §1.3. Fuse the `to_code` bounds among an implicit conjunction — an
/// `And` node's children, or the top-level assertion list — into AT MOST ONE
/// membership per string term. That invariant is what keeps slice 21's
/// intersection gap out of reach.
///
/// Conjuncts that are not `to_code` bounds pass through untouched. A group
/// whose fused range is inexpressible (§3.1) is left entirely alone, so its
/// atoms survive to the presence fence.
///
/// `Or` nodes are deliberately NOT fused: SAT selects one disjunct, so only one
/// membership is ever asserted on `s` and there is nothing to intersect.
///
/// Fusion is per-syntactic-conjunction: it groups bounds among ONE `And`
/// node's direct children (or the top-level list), never across levels, and
/// never through a wrapper. Two bounds on the same string term do NOT fuse —
/// so both survive as separate memberships and can hit slice 21's
/// intersection gap (a sound `Unknown`, never a wrong answer) — when they sit
/// in a nested `And` rather than a flat one, when one is at the top level and
/// its partner is inside an `And`, or when either is wrapped in a double
/// negation (`match_bound` absorbs one `not`, not two).
fn fuse_bounds(ctx: &mut Context, conjuncts: &[TermId]) -> Vec<TermId> {
    let mut order: Vec<TermId> = Vec::new();
    let mut groups: FxHashMap<TermId, Vec<(usize, Bound)>> = FxHashMap::default();
    for (i, &c) in conjuncts.iter().enumerate() {
        if let Some((s, b)) = match_bound(ctx, c) {
            groups
                .entry(s)
                .or_insert_with(|| {
                    order.push(s);
                    Vec::new()
                })
                .push((i, b));
        }
    }
    let mut out: Vec<TermId> = conjuncts.to_vec();
    for s in order {
        let members = &groups[&s];
        if members.len() < 2 {
            // A lone bound needs no meet — `gadget` materializes it directly.
            continue;
        }
        let bounds: Vec<Bound> = members.iter().map(|&(_, b)| b).collect();
        let Some(fused) = fuse_group(ctx, s, &bounds) else {
            continue; // inexpressible ⇒ leave the group alone ⇒ fence
        };
        out[members[0].0] = fused;
        let tt = ctx.mk_const_bool(true);
        for &(i, _) in &members[1..] {
            out[i] = tt;
        }
    }
    out
}

/// Pass 2 (spec §1.2 / §1.3). An `And` fuses its conjuncts BEFORE recursing
/// (top-down); every other node recurses first. Memoized: fusion happens at the
/// PARENT and never inside `gadget(atom)`, so a bound shared between an `And`
/// (fused) and an `Or` (not fused) still caches one consistent result.
///
/// The `And` arm must fuse before recursing: fusion needs to see the raw,
/// un-materialized inequality atoms, and once each atom has already been
/// turned into its own membership term there is nothing left for it to fuse.
///
/// On a match, `gadget` recurses into the produced term `r` rather than
/// returning it verbatim, because the string argument `s` extracted from the
/// atom may itself contain a `to_code` inequality (reachable e.g. via a
/// string-sorted `ite` whose condition is itself a `to_code` inequality) —
/// without recursing, that nested atom would survive un-canonicalized. This
/// recursion is well-founded and cannot re-match or re-fuse: `r` is always a
/// membership (`str.in_re`), its negation, or a Bool constant — never itself
/// an inequality atom or an `And` — and `r`'s children (in particular the `s`
/// that was pulled out) are strict subterms of the ORIGINAL `t` (the term DAG
/// is acyclic, so no subterm can contain an ancestor). It is idempotent
/// because a second `gadget` pass over the now-canonical `r` finds nothing
/// left to change.
fn gadget(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let orig: Vec<TermId> = ctx.children(args).to_vec();
            let conjuncts = if matches!(op, Op::Builtin(BuiltinOp::And)) {
                fuse_bounds(ctx, &orig)
            } else {
                orig.clone()
            };
            match try_code_ineq_atom(ctx, op, &conjuncts) {
                // Recurse into the result so a to_code inequality nested in
                // the string argument is canonicalized too. `r` is a
                // membership or a Bool constant — never an inequality atom —
                // so this terminates and cannot re-fuse.
                Some(r) => gadget(ctx, r, memo),
                None => {
                    let kids: Vec<TermId> =
                        conjuncts.iter().map(|&c| gadget(ctx, c, memo)).collect();
                    if kids == orig {
                        t
                    } else {
                        ctx.mk_app(op, &kids).expect("gadget: well-sorted rebuild")
                    }
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// Presence fence: true iff any `str.to_code` / `str.from_code` /
/// `str.is_digit` application survived [`rewrite_code_conv`].
pub fn has_unreduced_code_conv(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(
                    op,
                    Op::Builtin(
                        BuiltinOp::StrToCode | BuiltinOp::StrFromCode | BuiltinOp::StrIsDigit
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
    use super::*; // brings in Integer, Rational, BuiltinOp, Context, Op, TermId, TermNode

    /// A nullary uninterpreted constant of the given sort (codebase pattern —
    /// there is no `mk_const`).
    fn nullary(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }
    fn to_code(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToCode), &[s]).unwrap()
    }
    fn from_code(ctx: &mut Context, n: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrFromCode), &[n])
            .unwrap()
    }
    fn is_digit(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrIsDigit), &[s])
            .unwrap()
    }
    fn int_lit(ctx: &mut Context, v: i128) -> TermId {
        let int_s = ctx.int_sort();
        ctx.mk_numeral(Rational::from_int(Integer::from(v)), int_s)
    }

    #[test]
    fn eval_to_code_pinned_semantics() {
        assert_eq!(eval_to_code("a"), Some(Integer::from(97i128)));
        assert_eq!(eval_to_code("0"), Some(Integer::from(48i128)));
        assert_eq!(eval_to_code(""), Some(Integer::from(-1i128))); // empty
        assert_eq!(eval_to_code("ab"), Some(Integer::from(-1i128))); // multi-char
        assert_eq!(eval_to_code("\u{2FFFF}"), Some(Integer::from(0x2FFFFi128)));
        // A char ABOVE the SMT-LIB alphabet: not a valid String value — no fold.
        assert_eq!(eval_to_code("\u{30000}"), None);
    }

    #[test]
    fn eval_from_code_pinned_semantics() {
        assert_eq!(eval_from_code(&Integer::from(97i128)), Some("a".to_owned()));
        assert_eq!(
            eval_from_code(&Integer::from(0i128)),
            Some("\u{0}".to_owned())
        );
        assert_eq!(
            eval_from_code(&Integer::from(0x2FFFFi128)),
            Some("\u{2FFFF}".to_owned())
        );
        // Out of the alphabet (negative / too large) -> "".
        assert_eq!(eval_from_code(&Integer::from(-1i128)), Some(String::new()));
        assert_eq!(
            eval_from_code(&Integer::from(0x30000i128)),
            Some(String::new())
        );
        // A value too large for i128 is certainly out of the alphabet -> "".
        let huge = Integer::from_str_radix("1234567890123456789012345678901234567890", 10).unwrap();
        assert_eq!(eval_from_code(&huge), Some(String::new()));
        // Surrogates: unrepresentable -> None (fence).
        assert_eq!(eval_from_code(&Integer::from(0xD800i128)), None);
        assert_eq!(eval_from_code(&Integer::from(0xDFFFi128)), None);
        // Surrogate-block edges DO fold.
        assert_eq!(
            eval_from_code(&Integer::from(0xD7FFi128)),
            Some("\u{D7FF}".to_owned())
        );
        assert_eq!(
            eval_from_code(&Integer::from(0xE000i128)),
            Some("\u{E000}".to_owned())
        );
    }

    #[test]
    fn folds_literal_applications() {
        let mut ctx = Context::new();
        let a_lit = ctx.mk_string_const("a");
        let tc = to_code(&mut ctx, a_lit);
        let k97 = int_lit(&mut ctx, 97);
        let fc = from_code(&mut ctx, k97);
        let idig = is_digit(&mut ctx, a_lit);
        let seven = ctx.mk_string_const("7");
        let idig7 = is_digit(&mut ctx, seven);

        let out = rewrite_code_conv(&mut ctx, &[tc, fc, idig, idig7]);
        // to_code("a") -> 97 (hash-consed: same id as the numeral).
        assert_eq!(out[0], int_lit(&mut ctx, 97));
        // from_code(97) -> "a".
        assert_eq!(out[1], ctx.mk_string_const("a"));
        // is_digit("a") -> false; is_digit("7") -> true.
        assert_eq!(out[2], ctx.mk_const_bool(false));
        assert_eq!(out[3], ctx.mk_const_bool(true));
    }

    #[test]
    fn surrogate_from_code_does_not_fold() {
        let mut ctx = Context::new();
        let k = int_lit(&mut ctx, 0xD800);
        let fc = from_code(&mut ctx, k);
        let out = rewrite_code_conv(&mut ctx, &[fc]);
        assert_eq!(out[0], fc, "surrogate from_code must survive to the fence");
        assert!(has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn roundtrip_to_code_of_from_code() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fc = from_code(&mut ctx, n);
        let tc = to_code(&mut ctx, fc);
        let out = rewrite_code_conv(&mut ctx, &[tc]);
        // ite(and(n >= 0, n <= MAX_CODE), n, -1)
        let zero = int_lit(&mut ctx, 0);
        let max = int_lit(&mut ctx, MAX_CODE);
        let neg1 = int_lit(&mut ctx, -1);
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[n, max]).unwrap();
        let in_range = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[ge, le]).unwrap();
        let want = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[in_range, n, neg1])
            .unwrap();
        assert_eq!(out[0], want);
        assert!(!has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn roundtrip_from_code_of_to_code() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);
        let fc = from_code(&mut ctx, tc);
        let out = rewrite_code_conv(&mut ctx, &[fc]);
        // ite(len(s) = 1, s, "")
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[s]).unwrap();
        let one = int_lit(&mut ctx, 1);
        let cond = ctx.mk_eq(len, one).unwrap();
        let empty = ctx.mk_string_const("");
        let want = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[cond, s, empty])
            .unwrap();
        assert_eq!(out[0], want);
        assert!(!has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn untouched_subtrees_keep_their_termids() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let t = nullary(&mut ctx, "t", str_s);
        // An assertion with NO code-conv content at all.
        let eq = ctx.mk_eq(s, t).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[eq]);
        assert_eq!(out[0], eq, "no-op inputs must keep their TermId");
    }

    /// Convenience: rewrite a single assertion.
    fn rw1(ctx: &mut Context, t: TermId) -> TermId {
        rewrite_code_conv(ctx, &[t])[0]
    }

    #[test]
    fn to_code_const_rhs_boundary_lattice() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);

        // R4: in-alphabet, non-surrogate k ⇒ s = "<char k>". Check the edges
        // and a digit: 0, '9' (0x39), 0xD7FF, 0xE000, MAX_CODE.
        for k in [0i128, 0x39, 0xD7FF, 0xE000, MAX_CODE] {
            let kt = int_lit(&mut ctx, k);
            let atom = ctx.mk_eq(tc, kt).unwrap();
            let lit = ctx.mk_string_const(&char::from_u32(k as u32).unwrap().to_string());
            let want = ctx.mk_eq(s, lit).unwrap();
            assert_eq!(rw1(&mut ctx, atom), want, "k = {k:#x}");
        }

        // R5: k = -1 ⇒ not (len(s) = 1).
        let neg1 = int_lit(&mut ctx, -1);
        let atom = ctx.mk_eq(tc, neg1).unwrap();
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[s]).unwrap();
        let one = int_lit(&mut ctx, 1);
        let eq1 = ctx.mk_eq(len, one).unwrap();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq1]).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);

        // R6: k <= -2 or k > MAX_CODE ⇒ false.
        for k in [-2i128, 0x30000] {
            let kt = int_lit(&mut ctx, k);
            let atom = ctx.mk_eq(tc, kt).unwrap();
            assert_eq!(rw1(&mut ctx, atom), ctx.mk_const_bool(false), "k = {k}");
        }

        // Surrogate k: representational fence — the atom must SURVIVE.
        for k in [0xD800i128, 0xDFFF] {
            let kt = int_lit(&mut ctx, k);
            let atom = ctx.mk_eq(tc, kt).unwrap();
            let out = rw1(&mut ctx, atom);
            assert_eq!(out, atom, "surrogate k = {k:#x} must fence");
            assert!(has_unreduced_code_conv(&ctx, &[out]));
        }
    }

    #[test]
    fn to_code_const_rhs_matches_either_orientation() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);
        let k = int_lit(&mut ctx, 97);
        // (= 97 (str.to_code s)) — literal on the LEFT.
        let atom = ctx.mk_eq(k, tc).unwrap();
        let a_lit = ctx.mk_string_const("a");
        let want = ctx.mk_eq(s, a_lit).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);
    }

    #[test]
    fn to_code_const_rhs_under_negation_and_or() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);
        let k = int_lit(&mut ctx, 97);
        let atom = ctx.mk_eq(tc, k).unwrap();
        let neg = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[atom]).unwrap();
        let bool_s = ctx.bool_sort();
        let t = nullary(&mut ctx, "p", bool_s);
        let or = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[neg, t]).unwrap();

        let a_lit = ctx.mk_string_const("a");
        let want_eq = ctx.mk_eq(s, a_lit).unwrap();
        let want_neg = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[want_eq]).unwrap();
        let want = ctx
            .mk_app(Op::Builtin(BuiltinOp::Or), &[want_neg, t])
            .unwrap();
        assert_eq!(rw1(&mut ctx, or), want);
    }

    #[test]
    fn from_code_const_rhs_shapes() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fc = from_code(&mut ctx, n);

        // R7: singleton literal ⇒ n = code.
        let a_lit = ctx.mk_string_const("a");
        let atom = ctx.mk_eq(fc, a_lit).unwrap();
        let k97 = int_lit(&mut ctx, 97);
        let want = ctx.mk_eq(n, k97).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);

        // R8: empty literal ⇒ n < 0 ∨ n > MAX_CODE.
        let empty = ctx.mk_string_const("");
        let atom = ctx.mk_eq(fc, empty).unwrap();
        let zero = int_lit(&mut ctx, 0);
        let max = int_lit(&mut ctx, MAX_CODE);
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::Lt), &[n, zero]).unwrap();
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[n, max]).unwrap();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[lt, gt]).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);

        // R9: multi-char literal ⇒ false; above-alphabet singleton ⇒ false.
        for lit in ["ab", "\u{30000}"] {
            let l = ctx.mk_string_const(lit);
            let atom = ctx.mk_eq(fc, l).unwrap();
            assert_eq!(rw1(&mut ctx, atom), ctx.mk_const_bool(false), "lit {lit:?}");
        }
    }

    #[test]
    fn is_digit_expands_to_ten_way_disjunction() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let idig = is_digit(&mut ctx, s);
        let out = rw1(&mut ctx, idig);
        let disjuncts: Vec<TermId> = ('0'..='9')
            .map(|d| {
                let lit = ctx.mk_string_const(&d.to_string());
                ctx.mk_eq(s, lit).unwrap()
            })
            .collect();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disjuncts).unwrap();
        assert_eq!(out, want);
        assert!(!has_unreduced_code_conv(&ctx, &[out]));
    }

    #[test]
    fn is_digit_of_from_code_reduces_fully_in_one_pass() {
        // The minted-atom chain: is_digit(from_code(n)) must become a pure
        // LIA disjunction n = 48 ∨ … ∨ n = 57 — R10 routing each minted
        // equality through R7.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fc = from_code(&mut ctx, n);
        let idig = is_digit(&mut ctx, fc);
        let out = rw1(&mut ctx, idig);
        let disjuncts: Vec<TermId> = (48i128..=57)
            .map(|code| {
                let k = int_lit(&mut ctx, code);
                ctx.mk_eq(n, k).unwrap()
            })
            .collect();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disjuncts).unwrap();
        assert_eq!(out, want);
        assert!(!has_unreduced_code_conv(&ctx, &[out]));
    }

    #[test]
    fn symbolic_linking_still_fences() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let n = nullary(&mut ctx, "n", int_s);
        let tc = to_code(&mut ctx, s);
        // (= (str.to_code s) n): symbolic RHS — no rule applies.
        let atom = ctx.mk_eq(tc, n).unwrap();
        let out = rw1(&mut ctx, atom);
        assert_eq!(out, atom);
        assert!(has_unreduced_code_conv(&ctx, &[out]));
    }

    // ── Slice 22: the character-range gadget ─────────────────────────────
    //
    // The assertions below compare TermIds directly. That is exact, not
    // fragile: the Context is hash-consed and `rex_to_term` is documented as
    // deterministic (regex.rs:387-392), so an equal Rex yields an equal
    // TermId.

    fn str_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        nullary(ctx, name, s)
    }

    /// `(<op> (str.to_code s) k)`.
    fn ineq(ctx: &mut Context, op: BuiltinOp, s: TermId, k: i128) -> TermId {
        let tc = to_code(ctx, s);
        let kk = int_lit(ctx, k);
        ctx.mk_app(Op::Builtin(op), &[tc, kk]).unwrap()
    }

    /// The expected `s ∈ Range(lo, hi)` membership term.
    fn want_range(ctx: &mut Context, s: TermId, lo: u32, hi: u32) -> TermId {
        let r = crate::regex::rex_to_term(ctx, &crate::regex::Rex::Range(lo, hi));
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, r])
            .unwrap()
    }

    const MAX_U32: u32 = MAX_CODE as u32;

    #[test]
    fn ge_rewrites_to_suffix_range_membership() {
        // §1.2 master equivalence: to_code(s) >= 48 ⟺ s ∈ Range(48, MAX_CODE).
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let atom = ineq(&mut ctx, BuiltinOp::Ge, s, 48);
        let out = rewrite_code_conv(&mut ctx, &[atom]);
        assert!(!has_unreduced_code_conv(&ctx, &out), "to_code must be gone");
        let want = want_range(&mut ctx, s, 48, MAX_U32);
        assert_eq!(out[0], want);
    }

    #[test]
    fn canonicalization_table() {
        // §1.1: every op, both orientations, reduced to `to_code(s) >= k*`.
        // `>  47` ≡ `>= 48`;  `<  48` ≡ ¬(>= 48);  `<= 47` ≡ ¬(>= 48).
        //
        // Each atom below gets its OWN string variable (`s_gt`/`s_lt`/`s_le`)
        // rather than sharing one `s`: bound fusion groups bounds by string
        // term and collapses each group to one membership, so three bounds
        // sharing `s` would fuse into a single result and no longer pin these
        // per-atom expectations. Distinct variables ensure fusion never
        // groups them, keeping this table's atom-by-atom pins exact.
        let mut ctx = Context::new();
        let s_gt = str_var(&mut ctx, "s_gt");
        let s_lt = str_var(&mut ctx, "s_lt");
        let s_le = str_var(&mut ctx, "s_le");
        let want_pos_gt = want_range(&mut ctx, s_gt, 48, MAX_U32);
        let want_pos_lt = want_range(&mut ctx, s_lt, 48, MAX_U32);
        let want_pos_le = want_range(&mut ctx, s_le, 48, MAX_U32);
        let want_neg_lt = ctx
            .mk_app(Op::Builtin(BuiltinOp::Not), &[want_pos_lt])
            .unwrap();
        let want_neg_le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Not), &[want_pos_le])
            .unwrap();

        let gt = ineq(&mut ctx, BuiltinOp::Gt, s_gt, 47);
        let lt = ineq(&mut ctx, BuiltinOp::Lt, s_lt, 48);
        let le = ineq(&mut ctx, BuiltinOp::Le, s_le, 47);
        let out = rewrite_code_conv(&mut ctx, &[gt, lt, le]);
        assert_eq!(out[0], want_pos_gt);
        assert_eq!(out[1], want_neg_lt);
        assert_eq!(out[2], want_neg_le);

        // Mirrored orientation: `(<= k (to_code s))` ≡ `(>= (to_code s) k)`.
        let s = str_var(&mut ctx, "s");
        let want_pos = want_range(&mut ctx, s, 48, MAX_U32);
        let tc = to_code(&mut ctx, s);
        let k = int_lit(&mut ctx, 48);
        let mirrored = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[k, tc]).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[mirrored]);
        assert_eq!(out[0], want_pos);
    }

    #[test]
    fn zero_threshold_is_the_singleton_language() {
        // §1.2: to_code(s) >= 0 ⟺ len(s) = 1 ⟺ s ∈ Range(0, MAX_CODE)
        // (= re.allchar). Not a special case — it falls out of the formula.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let atom = ineq(&mut ctx, BuiltinOp::Ge, s, 0);
        let out = rewrite_code_conv(&mut ctx, &[atom]);
        let want = want_range(&mut ctx, s, 0, MAX_U32);
        assert_eq!(out[0], want);
    }

    #[test]
    fn degenerate_thresholds_fold_to_constants() {
        // §1.2. `to_code(s) >= -1` is a TAUTOLOGY (to_code is total into
        // {-1} ∪ [0, MAX_CODE]); `>= MAX_CODE + 1` is unsatisfiable. Negation
        // flips each.
        //
        // Each atom gets its OWN string variable (`s_taut`/`s_unsat`/
        // `s_neg_taut`/`s_neg_unsat`) instead of sharing one `s`, for the same
        // fusion-grouping reason as `canonicalization_table` above — this
        // pins the degenerate folds atom-by-atom, unaffected by bound fusion.
        let mut ctx = Context::new();
        let s_taut = str_var(&mut ctx, "s_taut");
        let s_unsat = str_var(&mut ctx, "s_unsat");
        let s_neg_taut = str_var(&mut ctx, "s_neg_taut");
        let s_neg_unsat = str_var(&mut ctx, "s_neg_unsat");
        let tt = ctx.mk_const_bool(true);
        let ff = ctx.mk_const_bool(false);

        let taut = ineq(&mut ctx, BuiltinOp::Ge, s_taut, -1);
        let unsat = ineq(&mut ctx, BuiltinOp::Ge, s_unsat, MAX_CODE + 1);
        // `< -1` is ¬(>= -1) = false;  `<= MAX_CODE` is ¬(>= MAX_CODE+1) = true.
        let neg_taut = ineq(&mut ctx, BuiltinOp::Lt, s_neg_taut, -1);
        let neg_unsat = ineq(&mut ctx, BuiltinOp::Le, s_neg_unsat, MAX_CODE);

        let out = rewrite_code_conv(&mut ctx, &[taut, unsat, neg_taut, neg_unsat]);
        assert_eq!(out[0], tt);
        assert_eq!(out[1], ff);
        assert_eq!(out[2], ff);
        assert_eq!(out[3], tt);
    }

    #[test]
    fn far_out_of_range_thresholds_fold() {
        // §1.1 clamping: a threshold too large for i128 still folds — the sign
        // decides. The threshold built here is a 40-digit repunit (111…1,
        // ≈1.11×10^39) — comfortably beyond `i128::MAX`, so it exercises the
        // bignum-clamp path — and being positive is unsatisfiable regardless
        // of its exact magnitude.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let int_s = ctx.int_sort();
        let huge = Integer::from_str_radix("1".repeat(40).as_str(), 10).unwrap();
        let k = ctx.mk_numeral(Rational::from_int(huge), int_s);
        let tc = to_code(&mut ctx, s);
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[tc, k]).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[atom]);
        assert_eq!(out[0], ctx.mk_const_bool(false));
    }

    #[test]
    fn interior_surrogate_threshold_fences() {
        // §3.1 representational fence. `range_term` encodes the FULL surrogate
        // block via `re.diff`, so 0xD800 is an admissible `lo`; a threshold
        // STRICTLY inside the block would need a lone-surrogate `re.range`
        // endpoint, which is not a `Box<str>`. Those survive to the fence.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");

        for k in [0xD801, 0xDFFF] {
            let atom = ineq(&mut ctx, BuiltinOp::Ge, s, k);
            let out = rewrite_code_conv(&mut ctx, &[atom]);
            assert!(
                has_unreduced_code_conv(&ctx, &out),
                "threshold {k:#x} must fence"
            );
        }
        // The block boundaries DO express.
        for k in [0xD7FF, 0xD800] {
            let atom = ineq(&mut ctx, BuiltinOp::Ge, s, k);
            let out = rewrite_code_conv(&mut ctx, &[atom]);
            assert!(
                !has_unreduced_code_conv(&ctx, &out),
                "threshold {k:#x} must express"
            );
        }
    }

    #[test]
    fn two_sided_bounds_fuse_to_one_range() {
        // §1.3, the whole point of the slice. 48 <= to_code(s) <= 57 must
        // produce ONE membership — s ∈ Range(48, 57) — not two. Two would land
        // on slice 21's intersection gap and return Unknown.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 48);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 57);
        // The top-level assertion list is an implicit conjunction.
        let out = rewrite_code_conv(&mut ctx, &[lo, hi]);
        let want = want_range(&mut ctx, s, 48, 57);
        let tt = ctx.mk_const_bool(true);
        assert_eq!(out[0], want);
        assert_eq!(out[1], tt);
    }

    #[test]
    fn fusion_meets_the_interval() {
        // §1.3 algebra: several lower bounds meet to their MAX, several upper
        // bounds to their MIN.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let a = ineq(&mut ctx, BuiltinOp::Ge, s, 40);
        let b = ineq(&mut ctx, BuiltinOp::Ge, s, 48); // max ⇒ lo = 48
        let c = ineq(&mut ctx, BuiltinOp::Le, s, 90);
        let d = ineq(&mut ctx, BuiltinOp::Le, s, 57); // min ⇒ hi = 57
        let out = rewrite_code_conv(&mut ctx, &[a, b, c, d]);
        let want = want_range(&mut ctx, s, 48, 57);
        assert_eq!(out[0], want);
    }

    #[test]
    fn fusion_inside_an_and_node() {
        // §1.3: `And` nodes fuse exactly like the top-level list.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 97);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 122);
        let conj = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[lo, hi]).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[conj]);
        let want = want_range(&mut ctx, s, 97, 122);
        let tt = ctx.mk_const_bool(true);
        let want_and = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[want, tt])
            .unwrap();
        assert_eq!(out[0], want_and);
    }

    #[test]
    fn fusion_absorbs_a_not_wrapper() {
        // §1.3: `(not (>= tc 58))` is the negated bound k = 58 — it must join
        // the meet, not sit outside it as a second membership.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 48);
        let raw = ineq(&mut ctx, BuiltinOp::Ge, s, 58);
        let neg = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[raw]).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[lo, neg]);
        let want = want_range(&mut ctx, s, 48, 57);
        assert_eq!(out[0], want);
    }

    #[test]
    fn crossed_bounds_fuse_to_false() {
        // §1.3: lo > hi ⇒ the empty interval ⇒ `false`.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 57);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 48);
        let out = rewrite_code_conv(&mut ctx, &[lo, hi]);
        assert_eq!(out[0], ctx.mk_const_bool(false));
    }

    #[test]
    fn crossed_bounds_beat_the_surrogate_fence() {
        // §1.3 / §3.1, ordering: the empty-interval check runs BEFORE the
        // expressibility check, so `to_code(s) >= 0xD801 ∧ to_code(s) <= 0xD7FF`
        // decides `false` even though 0xD801 is an inexpressible endpoint.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 0xD801);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 0xD7FF);
        let out = rewrite_code_conv(&mut ctx, &[lo, hi]);
        assert_eq!(out[0], ctx.mk_const_bool(false));
        assert!(!has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn upper_bounds_only_stay_a_complement() {
        // §1.3: with NO lower bound the `-1` escape survives (to_code(s) = -1
        // whenever len(s) != 1), so the constraint is genuinely a complement —
        // one NEGATED membership, still not an intersection.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let a = ineq(&mut ctx, BuiltinOp::Le, s, 90);
        let b = ineq(&mut ctx, BuiltinOp::Le, s, 57); // min ⇒ ¬(>= 58)
        let out = rewrite_code_conv(&mut ctx, &[a, b]);
        let m = want_range(&mut ctx, s, 58, MAX_U32);
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[m]).unwrap();
        assert_eq!(out[0], want);
    }

    #[test]
    fn fusion_groups_by_string_term() {
        // §1.3: bounds on DIFFERENT string terms must not be meeted together.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let t = str_var(&mut ctx, "t");
        let s_lo = ineq(&mut ctx, BuiltinOp::Ge, s, 48);
        let t_lo = ineq(&mut ctx, BuiltinOp::Ge, t, 97);
        let s_hi = ineq(&mut ctx, BuiltinOp::Le, s, 57);
        let out = rewrite_code_conv(&mut ctx, &[s_lo, t_lo, s_hi]);
        let want_s = want_range(&mut ctx, s, 48, 57);
        let want_t = want_range(&mut ctx, t, 97, MAX_U32);
        let tt = ctx.mk_const_bool(true);
        assert_eq!(out[0], want_s);
        assert_eq!(out[1], want_t);
        assert_eq!(out[2], tt);
    }

    #[test]
    fn inexpressible_fused_range_leaves_the_group_alone() {
        // §3.1: if the FUSED range has an interior-surrogate endpoint, the
        // whole group is left untouched — both conjuncts come back exactly as
        // they went in, not just fenced independently — and the presence
        // fence catches it.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 0xD801);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 0xDF00);
        let out = rewrite_code_conv(&mut ctx, &[lo, hi]);
        assert_eq!(out, vec![lo, hi]);
        assert!(has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn gadget_recurses_into_a_nested_to_code_inside_the_matched_string_arg() {
        // `gadget` recurses into the term it produces on a match, so a
        // `to_code` inequality nested INSIDE the string argument of another
        // `to_code` inequality — reachable via a String-sorted `ite` whose
        // condition holds one — gets canonicalized too, instead of surviving
        // to the fence:
        //   (>= (str.to_code (ite (>= (str.to_code x) 48) "a" "b")) 48)
        // must rewrite the INNER atom (the `ite`'s condition) to
        // `x ∈ Range(48, MAX_CODE)`, and the outer atom to
        // `(ite <that> "a" "b") ∈ Range(48, MAX_CODE)`.
        let mut ctx = Context::new();
        let x = str_var(&mut ctx, "x");
        let inner_atom = ineq(&mut ctx, BuiltinOp::Ge, x, 48);
        let a_lit = ctx.mk_string_const("a");
        let b_lit = ctx.mk_string_const("b");
        let ite_term = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[inner_atom, a_lit, b_lit])
            .unwrap();
        let outer_atom = ineq(&mut ctx, BuiltinOp::Ge, ite_term, 48);

        let out = rewrite_code_conv(&mut ctx, &[outer_atom]);
        assert!(
            !has_unreduced_code_conv(&ctx, &out),
            "the nested to_code must be canonicalized away, not just fenced"
        );

        let want_inner = want_range(&mut ctx, x, 48, MAX_U32);
        let want_ite = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[want_inner, a_lit, b_lit])
            .unwrap();
        let want_outer = want_range(&mut ctx, want_ite, 48, MAX_U32);
        assert_eq!(out[0], want_outer);
    }
}
