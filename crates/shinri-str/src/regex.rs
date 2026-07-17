//! Slice 19+20 pre-pass: `str.in_re` over SMT-LIB regular expressions —
//! ground evaluation by Brzozowski derivatives + presence fence.
//!
//! Decided fragment: `str.in_re(s, R)` where `s` is a string literal and `R`
//! is a CONSTANT regex (every `str.to_re` argument and every `re.range`
//! endpoint is a literal). The atom folds to true/false — evaluation, a full
//! logical equivalence at any polarity, any occurrence count. No model
//! repair, no fresh variables.
//!
//! Slice 20 adds: `str.in_re(t, R)` for ANY String term `t` when `L(R)` is
//! STRUCTURALLY finite (rewrites to `⋁ t = wᵢ`) or co-finite (rewrites to
//! `¬⋁ t = wᵢ` over the exception set) within the enumeration caps
//! (`ENUM_WORD_CAP`, `ENUM_TOTAL_BYTES_CAP`) — full equivalences at any
//! polarity; the produced (dis)equalities are word equations the engine
//! already owns. Surrogate-crossing ranges and above-alphabet string
//! sides are skipped (→ fence), never guessed.
//!
//! Stages (run by the solver's string-path seam, right after code_conv):
//! 1. [`rewrite_ground_in_re`] — bottom-up memoized pass folding every ground
//!    membership atom. (Lands in Task 3.)
//! 2. [`has_unreduced_regex`] — presence fence: any surviving `str.in_re`
//!    application or RegLan-sorted subterm ⇒ the solver returns a sound
//!    `Unknown`. The solver additionally fences any query that DECLARES a
//!    RegLan-sorted symbol (`Context::any_fun_sig_mentions`).
//!
//! Above-alphabet fence: Rust literals can hold chars in
//! `0x30000..=0x10FFFF`, outside the SMT-LIB alphabet — if the ground string
//! or a range endpoint contains one, the fold is skipped (→ fence) rather
//! than guessing semantics.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use std::collections::BTreeSet;

/// Largest SMT-LIB string character (inclusive): U+2FFFF.
pub(crate) const MAX_CODE: u32 = 0x2FFFF;

/// Derivative-size fuel: if any intermediate derivative exceeds this many
/// AST nodes the fold is abandoned (→ presence fence → sound Unknown).
pub(crate) const FUEL_NODE_CAP: usize = 10_000;

/// Canonical regex AST for ground evaluation. Invariants (enforced by the
/// smart constructors, NEVER by direct construction of compound nodes):
/// - `Range(lo, hi)`: `lo <= hi <= MAX_CODE`; a surrogate endpoint is legal
///   only as `lo = 0xD800` / `hi = 0xDFFF` (block edges — `range_rex`'s
///   policy; interval algebra preserves this since derived endpoints are
///   `endpoint ± 1` of non-interior inputs). Interior surrogates may occur
///   strictly INSIDE a range (a straddling range covers the block).
/// - `Concat`/`Union`/`Inter`: >= 2 elements, flattened, no identity/absorber
///   elements; `Union`/`Inter` deduped.
/// - `Star`: argument is not `Empty`/`Eps`/`Star`.
/// - `Comp`: argument is not `Comp`, `Empty`, or Σ* (`Star(Range(0,
///   MAX_CODE))`) — `comp` collapses `comp(∅) = Σ*` and `comp(Σ*) = ∅` in
///   addition to cancelling `Comp∘Comp` (slice 25 task 5b).
/// - `Loop(r, lo, hi)`: `lo <= hi`, `hi >= 1`, `r` not `Empty`/`Eps`.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Rex {
    /// ∅ — matches nothing.
    Empty,
    /// {ε} — matches exactly the empty string.
    Eps,
    /// One char with code point in `[lo, hi]` (inclusive).
    Range(u32, u32),
    Concat(Vec<Rex>),
    Union(Vec<Rex>),
    Inter(Vec<Rex>),
    Star(Box<Rex>),
    /// Complement w.r.t. Σ* (Σ = the SMT-LIB alphabet).
    Comp(Box<Rex>),
    /// `r{lo..=hi}` — between lo and hi copies of r.
    Loop(Box<Rex>, u32, u32),
}

pub(crate) fn concat(parts: Vec<Rex>) -> Rex {
    let mut out = Vec::new();
    for p in parts {
        match p {
            Rex::Empty => return Rex::Empty,
            Rex::Eps => {}
            Rex::Concat(inner) => out.extend(inner),
            other => out.push(other),
        }
    }
    match out.len() {
        0 => Rex::Eps,
        1 => out.pop().expect("len 1"),
        _ => Rex::Concat(out),
    }
}

/// Sort inclusive intervals by `lo` and merge overlapping or ADJACENT ones
/// (`[a,b] ∪ [b+1,c] → [a,c]`). Exact set arithmetic on character classes.
fn coalesce(mut iv: Vec<(u32, u32)>) -> Vec<(u32, u32)> {
    iv.sort_unstable();
    let mut out: Vec<(u32, u32)> = Vec::new();
    for (lo, hi) in iv {
        match out.last_mut() {
            Some((_, phi)) if lo <= phi.saturating_add(1) => *phi = (*phi).max(hi),
            _ => out.push((lo, hi)),
        }
    }
    out
}

pub(crate) fn union(parts: Vec<Rex>) -> Rex {
    // Slice 25: Range members are coalesced (sorted by lo, overlapping/
    // adjacent merged) and emitted FIRST; non-range members follow in
    // first-appearance order, deduped. Deterministic output — hash-consing
    // and the engine's dedup keys rely on `rex_to_term` determinism per Rex.
    fn add(p: Rex, ranges: &mut Vec<(u32, u32)>, others: &mut Vec<Rex>) {
        match p {
            Rex::Empty => {}
            Rex::Range(lo, hi) => ranges.push((lo, hi)),
            Rex::Union(inner) => {
                for q in inner {
                    add(q, ranges, others);
                }
            }
            other => {
                if !others.contains(&other) {
                    others.push(other);
                }
            }
        }
    }
    let mut ranges = Vec::new();
    let mut others = Vec::new();
    for p in parts {
        add(p, &mut ranges, &mut others);
    }
    let mut out: Vec<Rex> = coalesce(ranges)
        .into_iter()
        .map(|(lo, hi)| Rex::Range(lo, hi))
        .collect();
    out.extend(others);
    match out.len() {
        0 => Rex::Empty,
        1 => out.pop().expect("len 1"),
        _ => Rex::Union(out),
    }
}

pub(crate) fn inter(parts: Vec<Rex>) -> Rex {
    let mut out: Vec<Rex> = Vec::new();
    for p in parts {
        match p {
            Rex::Empty => return Rex::Empty,
            Rex::Inter(inner) => {
                for q in inner {
                    if !out.contains(&q) {
                        out.push(q);
                    }
                }
            }
            other => {
                if !out.contains(&other) {
                    out.push(other);
                }
            }
        }
    }
    match out.len() {
        // Unreachable from user syntax (arity >= 2, Empty short-circuits),
        // but be safe: the intersection of no languages is Σ*.
        0 => star(Rex::Range(0, MAX_CODE)),
        1 => out.pop().expect("len 1"),
        _ => {
            // Slice 26 Task 6a: collapse a BOUNDS-CERTIFIED empty
            // intersection at construction. `min_len`/`max_len` are sound
            // (resp. lower/upper) bounds on every word's length in the
            // built Rex's language (see their doc comments); for `Inter`
            // specifically, `min_len` = max of the arm min_lens and
            // `max_len` = min of the FINITE arm max_lens are each derived
            // from the very shape we just built, so if the lower bound
            // exceeds a known finite upper bound, no length is
            // simultaneously admissible by every arm: L = ∅. This is the
            // structural counterpart of `comp()`'s universal/empty
            // collapse (slice 25 task 5b) — a smart constructor catching
            // an emptiness the naive shape would otherwise hide (here,
            // from a surrounding `concat()`'s all-or-nothing Empty check,
            // which only sees the per-arm bounds, not their combination).
            let built = Rex::Inter(out);
            match max_len(&built) {
                Some(hi) if min_len(&built) > hi => Rex::Empty,
                _ => built,
            }
        }
    }
}

pub(crate) fn star(r: Rex) -> Rex {
    match r {
        Rex::Empty | Rex::Eps => Rex::Eps,
        s @ Rex::Star(_) => s,
        other => Rex::Star(Box::new(other)),
    }
}

/// True iff `k` is a UTF-16 surrogate code point — in the SMT-LIB alphabet but
/// unrepresentable as a `Box<str>` character.
pub(crate) fn is_surrogate(k: i128) -> bool {
    (0xD800..=0xDFFF).contains(&k)
}

/// A single character class `[lo, hi]` as a `Rex`, applying slice-22's endpoint
/// policy (the term-free core shared with `code_conv::range_membership`):
///   * `lo > hi`  ⇒ `Some(Rex::Empty)` (the empty interval; the caller's
///     `union`/`concat` drop it — see `regex.rs` `concat`/`union`).
///   * an endpoint STRICTLY inside the surrogate block (a surrogate other than
///     the block edges `0xD800` / `0xDFFF`, which ARE expressible) ⇒ `None`.
///   * otherwise ⇒ `Some(Rex::Range(lo as u32, hi as u32))`.
///
/// Takes `i128` so callers can pass `m-1` / `m+1` / `MAX+1` without under/overflow.
pub(crate) fn range_rex(lo: i128, hi: i128) -> Option<Rex> {
    if lo > hi {
        return Some(Rex::Empty);
    }
    debug_assert!((0..=MAX_CODE as i128).contains(&lo) && (0..=MAX_CODE as i128).contains(&hi));
    if (is_surrogate(lo) && lo != 0xD800) || (is_surrogate(hi) && hi != 0xDFFF) {
        return None;
    }
    Some(Rex::Range(lo as u32, hi as u32))
}

pub(crate) fn comp(r: Rex) -> Rex {
    match r {
        Rex::Comp(inner) => *inner,
        Rex::Empty => star(Rex::Range(0, MAX_CODE)), // comp(∅) = Σ*
        ref s if is_sigma_star(s) => Rex::Empty,     // comp(Σ*) = ∅
        other => Rex::Comp(Box::new(other)),
    }
}

/// True iff `r` is exactly `Σ*` (`Star(Range(0, MAX_CODE))`) — the canonical
/// shape `star`/`extract_const_regex` produce for `re.all`/derived universals.
fn is_sigma_star(r: &Rex) -> bool {
    matches!(r, Rex::Star(inner) if **inner == Rex::Range(0, MAX_CODE))
}

pub(crate) fn loop_(r: Rex, lo: u32, hi: u32) -> Rex {
    if lo > hi {
        return Rex::Empty;
    }
    if hi == 0 {
        return Rex::Eps; // r{0,0} = ε
    }
    match r {
        // ∅ has no words: ∅{lo..hi} = ε iff lo == 0, else ∅.
        Rex::Empty => {
            if lo == 0 {
                Rex::Eps
            } else {
                Rex::Empty
            }
        }
        Rex::Eps => Rex::Eps,
        other => Rex::Loop(Box::new(other), lo, hi),
    }
}

/// ε ∈ L(r)?
pub(crate) fn nullable(r: &Rex) -> bool {
    match r {
        Rex::Empty | Rex::Range(..) => false,
        Rex::Eps | Rex::Star(_) => true,
        Rex::Concat(ps) | Rex::Inter(ps) => ps.iter().all(nullable),
        Rex::Union(ps) => ps.iter().any(nullable),
        Rex::Comp(inner) => !nullable(inner),
        Rex::Loop(inner, lo, _) => *lo == 0 || nullable(inner),
    }
}

/// Sound LOWER bound on accepted-word length: every `w ∈ L(r)` has
/// `|w| ≥ min_len(r)`. Exact for the range/concat/union/inter/star/loop
/// shapes the membership pass mints; conservative (0) for `Comp`. `Empty`
/// returns 0 — vacuously sound (L = ∅); the memb.rs leaf arm never consults
/// it for `Empty` (excluded there so the Rule-E conflict path keeps firing).
///
/// Uses SATURATING arithmetic deliberately: unlike `max_len` (below), a
/// lower bound stays sound even when the true value overflows `u32` and
/// saturation caps it DOWN — a smaller-than-true lower bound is still a
/// valid lower bound (`|w| ≥ min_len(r)` still holds; it's just not tight).
/// Do not "fix" this to checked arithmetic — the asymmetry with `max_len`
/// is intentional. Only an upper bound can be pushed the *wrong* direction
/// by saturation, which is why `max_len` needs `None`-on-overflow instead.
pub(crate) fn min_len(r: &Rex) -> u32 {
    match r {
        Rex::Empty | Rex::Eps | Rex::Star(_) | Rex::Comp(_) => 0,
        Rex::Range(..) => 1,
        Rex::Concat(ps) => ps.iter().map(min_len).fold(0u32, u32::saturating_add),
        Rex::Union(ps) => ps.iter().map(min_len).min().unwrap_or(0),
        Rex::Inter(ps) => ps.iter().map(min_len).max().unwrap_or(0),
        Rex::Loop(inner, lo, _) => min_len(inner).saturating_mul(*lo),
    }
}

/// Sound UPPER bound: `Some(k)` ⟹ every `w ∈ L(r)` has `|w| ≤ k`; `None`
/// when no finite bound is known (star, comp, any unbounded part, OR the
/// true bound overflows `u32`). For `Inter` the MIN of the finite arm
/// bounds is sound (a word must satisfy every arm); for `Union`/`Concat`
/// one unbounded arm forfeits the bound.
///
/// Uses CHECKED arithmetic: overflow must yield `None`, not a saturated
/// `u32::MAX`. A saturated value SILENTLY UNDER-STATES the true maximum
/// (e.g. `(_ re.loop 0 3000000000)` over a 2-char literal has a true max of
/// 6·10⁹, but `u32::MAX` ≈ 4.3·10⁹ is smaller) — that would make the sound
/// upper bound unsound. `None` (no known finite bound) is always safe here;
/// a wrong-but-finite bound is not. See `min_len` above for why the lower
/// bound doesn't need this.
pub(crate) fn max_len(r: &Rex) -> Option<u32> {
    match r {
        Rex::Empty | Rex::Eps => Some(0),
        Rex::Range(..) => Some(1),
        Rex::Star(_) | Rex::Comp(_) => None,
        Rex::Concat(ps) => ps
            .iter()
            .map(max_len)
            .try_fold(0u32, |a, b| a.checked_add(b?)),
        Rex::Union(ps) => ps
            .iter()
            .map(max_len)
            .try_fold(0u32, |a, b| Some(a.max(b?))),
        Rex::Inter(ps) => ps.iter().filter_map(max_len).min(),
        Rex::Loop(inner, _, hi) => max_len(inner).and_then(|m| m.checked_mul(*hi)),
    }
}

/// The Brzozowski derivative of `r` w.r.t. the char with code point `c`:
/// `L(deriv(c, r)) = { w | c·w ∈ L(r) }`. Total — every operator (comp,
/// inter, loop included) has a native rule; no automaton is built.
pub(crate) fn deriv(c: u32, r: &Rex) -> Rex {
    match r {
        Rex::Empty | Rex::Eps => Rex::Empty,
        Rex::Range(lo, hi) => {
            if *lo <= c && c <= *hi {
                Rex::Eps
            } else {
                Rex::Empty
            }
        }
        Rex::Concat(ps) => {
            // d(r1·rest) = d(r1)·rest  ∪  (if ε ∈ r1) d(rest)
            let head = &ps[0];
            let rest = concat(ps[1..].to_vec());
            let first = concat(vec![deriv(c, head), rest.clone()]);
            if nullable(head) {
                union(vec![first, deriv(c, &rest)])
            } else {
                first
            }
        }
        Rex::Union(ps) => union(ps.iter().map(|p| deriv(c, p)).collect()),
        Rex::Inter(ps) => inter(ps.iter().map(|p| deriv(c, p)).collect()),
        Rex::Star(inner) => concat(vec![deriv(c, inner), Rex::Star(inner.clone())]),
        Rex::Comp(inner) => comp(deriv(c, inner)),
        Rex::Loop(inner, lo, hi) => {
            // Consume one char from `inner`; the remainder completes `inner`,
            // then loops lo-1..hi-1 more times (hi >= 1 by the invariant).
            // Bounds decrement lazily — huge hi costs nothing.
            let tail = loop_((**inner).clone(), lo.saturating_sub(1), hi - 1);
            concat(vec![deriv(c, inner), tail])
        }
    }
}

pub(crate) fn node_count(r: &Rex) -> usize {
    1 + match r {
        Rex::Empty | Rex::Eps | Rex::Range(..) => 0,
        Rex::Concat(ps) | Rex::Union(ps) | Rex::Inter(ps) => ps.iter().map(node_count).sum(),
        Rex::Star(i) | Rex::Comp(i) | Rex::Loop(i, ..) => node_count(i),
    }
}

/// Ground membership by |s| derivative steps + nullability. `None` iff an
/// intermediate derivative exceeds `cap` nodes (→ caller fences).
fn eval_membership_capped(s: &str, r: &Rex, cap: usize) -> Option<bool> {
    let mut cur = r.clone();
    for c in s.chars() {
        cur = deriv(c as u32, &cur);
        if node_count(&cur) > cap {
            return None;
        }
    }
    Some(nullable(&cur))
}

pub(crate) fn eval_membership(s: &str, r: &Rex) -> Option<bool> {
    eval_membership_capped(s, r, FUEL_NODE_CAP)
}

/// A literal word as a Rex (concat of single-char ranges). None if any char
/// is above the SMT-LIB alphabet (→ fence).
fn lit_to_rex(s: &str) -> Option<Rex> {
    let mut parts = Vec::new();
    for c in s.chars() {
        let code = c as u32;
        if code > MAX_CODE {
            return None;
        }
        parts.push(Rex::Range(code, code));
    }
    Some(concat(parts)) // "" → Eps
}

// ─── Slice 21: derivative unfolding support ──────────────────────────────

/// Max next-character classes per Rule-E expansion; more ⇒ fence (Unknown).
pub(crate) const CLASS_SPLIT_CAP: usize = 64;
/// Max derivative states visited by the model-repair word search.
pub(crate) const MEMB_SEARCH_STEP_CAP: usize = 10_000;

const SURR_LO: u32 = 0xD800;
const SURR_HI: u32 = 0xDFFF;

/// Collect the class boundaries contributed by every `Range` node in `r`:
/// each range [lo, hi] cuts Σ at lo and hi+1.
fn range_bounds(r: &Rex, out: &mut BTreeSet<u32>) {
    match r {
        Rex::Empty | Rex::Eps => {}
        Rex::Range(lo, hi) => {
            out.insert(*lo);
            if *hi < MAX_CODE {
                out.insert(hi + 1);
            }
        }
        Rex::Concat(ps) | Rex::Union(ps) | Rex::Inter(ps) => {
            for p in ps {
                range_bounds(p, out);
            }
        }
        Rex::Star(i) | Rex::Comp(i) | Rex::Loop(i, ..) => range_bounds(i, out),
    }
}

/// Next-character classes: a partition of Σ = [0, MAX_CODE] into maximal
/// ranges on which `deriv` is uniform. `deriv` branches only on `Range`
/// membership tests, and no `Range` boundary of `r` falls strictly inside a
/// class, so every test answers identically across the class. Using ALL
/// ranges in `r` (not just head-reachable ones) yields a finer-than-needed
/// partition — still correct. `None` iff the partition exceeds
/// `CLASS_SPLIT_CAP` (→ caller fences).
pub(crate) fn next_classes(r: &Rex) -> Option<Vec<(u32, u32)>> {
    let mut bounds = BTreeSet::new();
    bounds.insert(0u32);
    range_bounds(r, &mut bounds);
    let cuts: Vec<u32> = bounds.into_iter().collect();
    if cuts.len() > CLASS_SPLIT_CAP {
        return None;
    }
    let mut classes = Vec::with_capacity(cuts.len());
    for (i, &lo) in cuts.iter().enumerate() {
        let hi = if i + 1 < cuts.len() {
            cuts[i + 1] - 1
        } else {
            MAX_CODE
        };
        classes.push((lo, hi));
    }
    Some(classes)
}

/// The syntactic shape `Range · R''` (Rule-E disjunct shape): a bare `Range`
/// (residual ε) or a `Concat` whose head is a `Range`. Rule S peels exactly
/// this shape; everything else goes through Rule E first.
pub(crate) fn head_forced(r: &Rex) -> Option<((u32, u32), Rex)> {
    match r {
        Rex::Range(lo, hi) => Some(((*lo, *hi), Rex::Eps)),
        Rex::Concat(ps) => match &ps[0] {
            Rex::Range(lo, hi) => Some(((*lo, *hi), concat(ps[1..].to_vec()))),
            _ => None,
        },
        _ => None,
    }
}

/// `(re.range c c')` for NON-surrogate endpoints.
fn range_term_raw(ctx: &mut Context, lo: u32, hi: u32) -> TermId {
    let l = ctx.mk_string_const(&char::from_u32(lo).expect("non-surrogate lo").to_string());
    let h = ctx.mk_string_const(&char::from_u32(hi).expect("non-surrogate hi").to_string());
    ctx.mk_app(Op::Builtin(BuiltinOp::ReRange), &[l, h])
        .expect("re.range well-sorted")
}

/// A RegLan term denoting exactly the char set [lo, hi] ⊆ Σ. Surrogate
/// endpoints — only `lo = 0xD800` / `hi = 0xDFFF` can arise, because class
/// boundaries are user chars ±1 and user chars are never surrogates — are
/// handled by splitting at the block and encoding the FULL block as
/// `(re.diff (re.range \u{D7FF} \u{E000}) (re.union (re.range \u{D7FF} \u{D7FF})
/// (re.range \u{E000} \u{E000})))`, whose endpoints are all expressible.
fn range_term(ctx: &mut Context, lo: u32, hi: u32) -> TermId {
    debug_assert!(lo <= hi && hi <= MAX_CODE);
    debug_assert!(
        lo == SURR_LO || !(SURR_LO..=SURR_HI).contains(&lo),
        "interior surrogate lo"
    );
    debug_assert!(
        hi == SURR_HI || !(SURR_LO..=SURR_HI).contains(&hi),
        "interior surrogate hi"
    );
    let mut parts: Vec<TermId> = Vec::new();
    if lo < SURR_LO {
        parts.push(range_term_raw(ctx, lo, hi.min(SURR_LO - 1)));
    }
    if lo <= SURR_LO && hi >= SURR_HI {
        let outer = range_term_raw(ctx, SURR_LO - 1, SURR_HI + 1);
        let a = range_term_raw(ctx, SURR_LO - 1, SURR_LO - 1);
        let b = range_term_raw(ctx, SURR_HI + 1, SURR_HI + 1);
        let u = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &[a, b])
            .expect("re.union well-sorted");
        parts.push(
            ctx.mk_app(Op::Builtin(BuiltinOp::ReDiff), &[outer, u])
                .expect("re.diff well-sorted"),
        );
    }
    if hi > SURR_HI {
        parts.push(range_term_raw(ctx, lo.max(SURR_HI + 1), hi));
    }
    match parts.len() {
        1 => parts[0],
        _ => ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &parts)
            .expect("re.union well-sorted"),
    }
}

/// Reverse translation Rex → RegLan term over the existing Re* builtins.
/// Total (surrogate-endpoint ranges included). Guarantee (slice 25): the
/// minted term re-extracts (`extract_const_regex`) to the SAME Rex — shape
/// identity, not merely language equality; the surrogate-block diff gadget
/// folds back to its Range via the ReDiff character-class fast path.
/// Deterministic, so hash-consing gives TermId identity for equal Rex
/// inputs (the engine's dedup keys rely on this).
/// Pinned by `roundtrip_extract_of_rex_to_term_is_identity`.
pub(crate) fn rex_to_term(ctx: &mut Context, r: &Rex) -> TermId {
    let kids = |ctx: &mut Context, ps: &[Rex]| -> Vec<TermId> {
        ps.iter().map(|p| rex_to_term(ctx, p)).collect()
    };
    match r {
        Rex::Empty => ctx
            .mk_app(Op::Builtin(BuiltinOp::ReNone), &[])
            .expect("re.none well-sorted"),
        Rex::Eps => {
            let e = ctx.mk_string_const("");
            ctx.mk_app(Op::Builtin(BuiltinOp::StrToRe), &[e])
                .expect("str.to_re well-sorted")
        }
        Rex::Range(lo, hi) => range_term(ctx, *lo, *hi),
        Rex::Concat(ps) => {
            let ks = kids(ctx, ps);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReConcat), &ks)
                .expect("re.++ well-sorted")
        }
        Rex::Union(ps) => {
            let ks = kids(ctx, ps);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReUnion), &ks)
                .expect("re.union well-sorted")
        }
        Rex::Inter(ps) => {
            let ks = kids(ctx, ps);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReInter), &ks)
                .expect("re.inter well-sorted")
        }
        Rex::Star(i) => {
            let k = rex_to_term(ctx, i);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReStar), &[k])
                .expect("re.* well-sorted")
        }
        Rex::Comp(i) => {
            let k = rex_to_term(ctx, i);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReComp), &[k])
                .expect("re.comp well-sorted")
        }
        Rex::Loop(i, lo, hi) => {
            let k = rex_to_term(ctx, i);
            ctx.mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: *lo, hi: *hi }), &[k])
                .expect("re.loop well-sorted")
        }
    }
}

/// A word of length EXACTLY `n` in L(r), or None if none exists within
/// `MEMB_SEARCH_STEP_CAP` visited states (an abort is NOT a verdict — the
/// caller leaves the value untouched and the self-check backstops). DFS over
/// next-character classes; per class the witness char is the smallest
/// NON-SURROGATE code point (a pure-surrogate class has no Rust witness and
/// is skipped — sound: skipping loses completeness only). `dead` memoizes
/// (remaining, Rex) states with no word, preventing exponential re-search.
/// The DFS carries an EXPLICIT frame stack: recursion would be one frame per
/// character, and slice-26 length bounds legitimately request witnesses
/// thousands of chars long — deep enough to overflow a 2 MiB test-thread
/// stack in a debug build.
pub(crate) fn search_word(r: &Rex, n: usize) -> Option<String> {
    /// Prologue of a DFS visit: terminal checks + memo lookup, no descent.
    enum Visit {
        /// The state completes a word (`n` hit 0 on a nullable state).
        Word,
        /// The state provably contributes no word — try the next sibling.
        DeadEnd,
        /// The state needs exploring: its next-character classes.
        Explore(Vec<(u32, u32)>),
    }
    fn visit(state: &Rex, n: usize, steps: &mut usize, dead: &FxHashSet<(usize, Rex)>) -> Visit {
        if *steps >= MEMB_SEARCH_STEP_CAP {
            return Visit::DeadEnd;
        }
        *steps += 1;
        if n == 0 {
            return if nullable(state) {
                Visit::Word
            } else {
                Visit::DeadEnd
            };
        }
        if matches!(state, Rex::Empty) {
            return Visit::DeadEnd;
        }
        if dead.contains(&(n, state.clone())) {
            return Visit::DeadEnd;
        }
        Visit::Explore(next_classes(state).unwrap_or_default())
    }

    struct Frame {
        /// Memo key: (remaining length, state). Inserted into `dead` once
        /// every class is exhausted without a word.
        key: (usize, Rex),
        classes: Vec<(u32, u32)>,
        /// Next class index to try.
        idx: usize,
    }

    let mut steps = 0usize;
    let mut dead: FxHashSet<(usize, Rex)> = FxHashSet::default();
    let mut out = String::new();
    let mut stack: Vec<Frame> = Vec::new();
    match visit(r, n, &mut steps, &dead) {
        Visit::Word => return Some(out),
        Visit::DeadEnd => return None,
        Visit::Explore(classes) => stack.push(Frame {
            key: (n, r.clone()),
            classes,
            idx: 0,
        }),
    }
    'descend: while let Some(mut f) = stack.pop() {
        while f.idx < f.classes.len() {
            let (lo, hi) = f.classes[f.idx];
            f.idx += 1;
            // Smallest non-surrogate witness in the class (boundaries can
            // only be 0xD800 / 0xDFFF, so lo either avoids the block or
            // the block ends inside the class at 0xDFFF).
            let c = if (SURR_LO..=SURR_HI).contains(&lo) {
                if hi > SURR_HI {
                    SURR_HI + 1
                } else {
                    continue; // pure-surrogate class: no Rust witness
                }
            } else {
                lo
            };
            let d = deriv(c, &f.key.1);
            if node_count(&d) > FUEL_NODE_CAP {
                continue;
            }
            out.push(char::from_u32(c).expect("non-surrogate in-alphabet"));
            let rem = f.key.0 - 1;
            match visit(&d, rem, &mut steps, &dead) {
                Visit::Word => return Some(out),
                Visit::DeadEnd => {
                    out.pop();
                }
                Visit::Explore(classes) => {
                    stack.push(f);
                    stack.push(Frame {
                        key: (rem, d),
                        classes,
                        idx: 0,
                    });
                    continue 'descend;
                }
            }
        }
        // Every class exhausted without a word: memoize and backtrack. The
        // char popped is the one pushed when this frame was entered; the
        // root frame has no entering char and `out` is empty — pop is a
        // no-op there.
        dead.insert(f.key);
        out.pop();
    }
    None
}

/// The SHORTEST word in L(r), or None if none is found within
/// `MEMB_SEARCH_STEP_CAP` expanded states (an abort is NOT a verdict — the
/// caller leaves the variable un-seeded and the post-solve self-check
/// backstops, exactly like `search_word`). Breadth-first over
/// next-character classes, so the first nullable state reached sits at the
/// minimal length; per class the witness char is the smallest non-surrogate
/// code point (pure-surrogate classes are skipped — sound: completeness
/// only). Visited Rex states are memoized globally: re-reaching a state at
/// a longer prefix can only yield longer words, so it is skipped.
pub(crate) fn search_shortest(r: &Rex) -> Option<String> {
    let mut steps = 0usize;
    let mut seen: FxHashSet<Rex> = FxHashSet::default();
    seen.insert(r.clone());
    let mut frontier: Vec<(Rex, String)> = vec![(r.clone(), String::new())];
    while !frontier.is_empty() {
        let mut next: Vec<(Rex, String)> = Vec::new();
        for (state, word) in frontier {
            if nullable(&state) {
                return Some(word);
            }
            if matches!(state, Rex::Empty) {
                continue;
            }
            if steps >= MEMB_SEARCH_STEP_CAP {
                return None;
            }
            steps += 1;
            let Some(classes) = next_classes(&state) else {
                continue;
            };
            for (lo, hi) in classes {
                let c = if (SURR_LO..=SURR_HI).contains(&lo) {
                    if hi > SURR_HI {
                        SURR_HI + 1
                    } else {
                        continue; // pure-surrogate class: no Rust witness
                    }
                } else {
                    lo
                };
                let d = deriv(c, &state);
                if node_count(&d) > FUEL_NODE_CAP {
                    continue;
                }
                if seen.insert(d.clone()) {
                    let mut w = word.clone();
                    w.push(char::from_u32(c).expect("non-surrogate in-alphabet"));
                    next.push((d, w));
                }
            }
        }
        frontier = next;
    }
    None
}

/// Three-valued emptiness of `L(r)`. `Empty` / `NonEmpty` are DECISIONS;
/// `Unknown` means a fuel/partition cap prevented a complete traversal (an
/// abort, NOT a verdict — the caller keeps its prior sound Unknown). `Empty`
/// is returned ONLY when the entire reachable derivative automaton was
/// explored, no reachable state is nullable, and no taint occurred.
///
/// Unlike `search_shortest`, this EXPLORES pure-surrogate character classes:
/// a surrogate is a valid SMT-LIB code point, so a state whose only accepting
/// path runs through a surrogate class denotes a NON-empty language. The
/// class's `lo` is a valid derivative representative (every code point in a
/// `next_classes` interval has identical derivative behaviour), and `deriv`
/// takes a raw `u32`, so no `char` is materialised.
pub(crate) enum Emptiness {
    Empty,
    NonEmpty,
    Unknown,
}

pub(crate) fn language_empty(r: &Rex) -> Emptiness {
    let mut steps = 0usize;
    let mut seen: FxHashSet<Rex> = FxHashSet::default();
    seen.insert(r.clone());
    let mut frontier: Vec<Rex> = vec![r.clone()];
    while !frontier.is_empty() {
        let mut next: Vec<Rex> = Vec::new();
        for state in frontier {
            if nullable(&state) {
                return Emptiness::NonEmpty;
            }
            if matches!(state, Rex::Empty) {
                continue;
            }
            if steps >= MEMB_SEARCH_STEP_CAP {
                return Emptiness::Unknown;
            }
            steps += 1;
            let Some(classes) = next_classes(&state) else {
                return Emptiness::Unknown; // CLASS_SPLIT_CAP overflow — taint
            };
            for (lo, _hi) in classes {
                let d = deriv(lo, &state);
                if node_count(&d) > FUEL_NODE_CAP {
                    return Emptiness::Unknown; // derivative blowup — taint
                }
                if seen.insert(d.clone()) {
                    next.push(d);
                }
            }
        }
        frontier = next;
    }
    Emptiness::Empty
}

/// Ground membership of a CONCRETE string in the regex TERM `re_t`.
/// 3-valued for the post-solve witness self-check: `Some(verdict)` iff `s`
/// is in-alphabet, `re_t` extracts as a constant regex, and evaluation stays
/// within fuel; `None` = cannot evaluate (treated as satisfied — can only
/// MISS a violation, never fabricate one).
pub fn eval_str_in_re(ctx: &Context, s: &str, re_t: TermId) -> Option<bool> {
    if s.chars().any(|c| c as u32 > MAX_CODE) {
        return None;
    }
    let rex = extract_const_regex(ctx, re_t)?;
    eval_membership(s, &rex)
}

// ─── Slice 20: finite / co-finite language enumeration ──────────────────

/// Max cardinality of any intermediate word set in either enumerator.
const ENUM_WORD_CAP: usize = 256;
/// Max total bytes (sum of word lengths) of any intermediate word set.
/// The cardinality cap alone does not bound work: `(_ re.loop n n)` over a
/// one-word language has exactly ONE word of unbounded length.
const ENUM_TOTAL_BYTES_CAP: usize = 4096;

type Words = BTreeSet<String>;

/// `None` iff the set crosses either enumeration cap (→ caller aborts).
fn check_caps(ws: Words) -> Option<Words> {
    if ws.len() > ENUM_WORD_CAP {
        return None;
    }
    if ws.iter().map(|w| w.len()).sum::<usize>() > ENUM_TOTAL_BYTES_CAP {
        return None;
    }
    Some(ws)
}

/// Pairwise concatenation of two finite languages, cap-checked.
fn concat_words(a: &Words, b: &Words) -> Option<Words> {
    let mut out = Words::new();
    for x in a {
        for y in b {
            out.insert(format!("{x}{y}"));
            if out.len() > ENUM_WORD_CAP {
                return None;
            }
        }
    }
    check_caps(out)
}

/// The words of `L(r)` when STRUCTURALLY finite and within the caps; `None`
/// otherwise. A `None` is never wrong — it only means "not recognized"
/// (→ the atom survives to the presence fence).
fn enum_lang(r: &Rex) -> Option<Words> {
    match r {
        Rex::Empty => Some(Words::new()),
        Rex::Eps => Some(Words::from([String::new()])),
        Rex::Range(lo, hi) => {
            // Surrogates (0xD800..=0xDFFF) are SMT-LIB alphabet characters
            // but not Rust chars — a range touching them cannot be
            // enumerated faithfully (words would be silently MISSED,
            // breaking the equivalence). Any such range spans >= 2050
            // chars (endpoints are Rust chars, hence non-surrogate), so
            // the cardinality cap also rejects it — this guard makes the
            // soundness argument local instead of an accident of the cap.
            if *lo <= 0xDFFF && *hi >= 0xD800 {
                return None;
            }
            if (*hi - *lo) as usize + 1 > ENUM_WORD_CAP {
                return None;
            }
            let ws: Words = (*lo..=*hi)
                .map(|c| {
                    char::from_u32(c)
                        .expect("non-surrogate in-alphabet code point")
                        .to_string()
                })
                .collect();
            check_caps(ws)
        }
        Rex::Concat(ps) => {
            let mut acc = Words::from([String::new()]);
            for p in ps {
                acc = concat_words(&acc, &enum_lang(p)?)?;
            }
            Some(acc)
        }
        Rex::Union(ps) => {
            let mut acc = Words::new();
            for p in ps {
                acc.extend(enum_lang(p)?);
            }
            check_caps(acc)
        }
        Rex::Inter(ps) => {
            // Some part must enumerate finite; filter its words through
            // the remaining parts by ground evaluation (comp/star parts
            // are fine — eval_membership is total up to fuel).
            let (i, base) = ps
                .iter()
                .enumerate()
                .find_map(|(i, p)| Some((i, enum_lang(p)?)))?;
            let mut out = Words::new();
            for w in base {
                let mut keep = true;
                for (j, p) in ps.iter().enumerate() {
                    if j == i {
                        continue;
                    }
                    match eval_membership(&w, p) {
                        Some(true) => {}
                        Some(false) => {
                            keep = false;
                            break;
                        }
                        // Derivative fuel — abort the WHOLE enumeration,
                        // never guess.
                        None => return None,
                    }
                }
                if keep {
                    out.insert(w);
                }
            }
            Some(out)
        }
        Rex::Loop(inner, lo, hi) => {
            let s = enum_lang(inner)?;
            // Early-outs the smart constructors cannot see (they only
            // collapse SYNTACTIC Empty/Eps arguments): L(inner) = ∅ or
            // {""} would otherwise spin up to `hi` no-growth iterations.
            if s.is_empty() {
                return Some(if *lo == 0 {
                    Words::from([String::new()])
                } else {
                    Words::new()
                });
            }
            if s.len() == 1 && s.contains("") {
                return Some(Words::from([String::new()]));
            }
            // cur = S^n from n = 0; acc collects S^lo ∪ … ∪ S^hi.
            // Termination: S now has a nonempty word, so every power
            // either grows `cur`'s total bytes (single-word S) or `acc`'s
            // cardinality — one of the caps fires within ~max(cap) steps
            // unless the fixpoint breaks first.
            let mut cur = Words::from([String::new()]);
            let mut acc = Words::new();
            let mut n: u32 = 0;
            loop {
                if n >= *lo {
                    let before = acc.len();
                    acc.extend(cur.iter().cloned());
                    acc = check_caps(acc)?;
                    if acc.len() == before && n > *lo {
                        // S^n ⊆ (union of lower powers ≥ lo) implies
                        // S^(n+1) = S^n·S ⊆ acc·S ⊆ acc, inductively for
                        // all higher powers — nothing new can appear.
                        break;
                    }
                }
                if n == *hi {
                    break;
                }
                cur = concat_words(&cur, &s)?;
                n += 1;
            }
            Some(acc)
        }
        Rex::Star(_) | Rex::Comp(_) => None,
    }
}

/// The EXCEPTION set `Σ* \ L(r)` when `L(r)` is STRUCTURALLY co-finite and
/// within the caps; `None` otherwise.
fn enum_comp(r: &Rex) -> Option<Words> {
    match r {
        Rex::Comp(inner) => enum_lang(inner),
        // Σ* itself (re.all's extraction): co-finite, zero exceptions.
        Rex::Star(inner) if **inner == Rex::Range(0, MAX_CODE) => Some(Words::new()),
        // Σ* \ ⋂ps = ⋃(Σ* \ p): EVERY part must be co-finite.
        Rex::Inter(ps) => {
            let mut acc = Words::new();
            for p in ps {
                acc.extend(enum_comp(p)?);
            }
            check_caps(acc)
        }
        // Σ* \ ⋃ps = ⋂(Σ* \ p): SOME part must be co-finite; its
        // exceptions, filtered by NON-membership in every other part.
        Rex::Union(ps) => {
            let (i, base) = ps
                .iter()
                .enumerate()
                .find_map(|(i, p)| Some((i, enum_comp(p)?)))?;
            let mut out = Words::new();
            for w in base {
                let mut keep = true;
                for (j, p) in ps.iter().enumerate() {
                    if j == i {
                        continue;
                    }
                    match eval_membership(&w, p) {
                        Some(false) => {}
                        Some(true) => {
                            keep = false;
                            break;
                        }
                        None => return None,
                    }
                }
                if keep {
                    out.insert(w);
                }
            }
            Some(out)
        }
        // Complements of Empty/Eps/Range/Concat/Loop and other Stars are
        // infinite (or rare enough not to chase) — not recognized.
        _ => None,
    }
}

/// `Some(sorted, coalesced intervals)` iff `r` is a pure character class:
/// `Empty`, a `Range`, or a `Union` whose members are themselves classes.
/// `None` for anything else (the caller falls back to the generic path).
fn class_intervals(r: &Rex) -> Option<Vec<(u32, u32)>> {
    fn go(r: &Rex, out: &mut Vec<(u32, u32)>) -> Option<()> {
        match r {
            Rex::Empty => Some(()),
            Rex::Range(lo, hi) => {
                out.push((*lo, *hi));
                Some(())
            }
            Rex::Union(ps) => ps.iter().try_for_each(|p| go(p, out)),
            _ => None,
        }
    }
    let mut out = Vec::new();
    go(r, &mut out)?;
    Some(coalesce(out))
}

/// `a \ b` over sorted, coalesced inclusive interval sets; output sorted,
/// coalesced. Exact set arithmetic — the ReDiff fast path's core.
fn interval_diff(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut out = Vec::new();
    for &(alo, ahi) in a {
        let mut lo = alo;
        let mut live = true;
        for &(blo, bhi) in b {
            if bhi < lo {
                continue;
            }
            if blo > ahi {
                break;
            }
            if blo > lo {
                out.push((lo, blo - 1));
            }
            if bhi >= ahi {
                live = false;
                break;
            }
            lo = bhi + 1;
        }
        if live {
            out.push((lo, ahi));
        }
    }
    out
}

/// Structural translation of a CONSTANT RegLan term. None on any
/// non-constant leaf (symbolic `str.to_re` argument, non-literal `re.range`
/// endpoint, RegLan variable / non-builtin application) or an
/// above-alphabet literal char (→ fence).
pub(crate) fn extract_const_regex(ctx: &Context, t: TermId) -> Option<Rex> {
    let TermNode::App { op, args, .. } = ctx.term_node(t) else {
        return None;
    };
    let Op::Builtin(b) = *op else {
        return None; // RegLan variable or uninterpreted application.
    };
    let kids: Vec<TermId> = ctx.children(*args).to_vec();
    let sub = |ctx: &Context, ids: &[TermId]| -> Option<Vec<Rex>> {
        ids.iter().map(|&k| extract_const_regex(ctx, k)).collect()
    };
    match b {
        BuiltinOp::StrToRe => lit_to_rex(ctx.string_const_value(kids[0])?),
        BuiltinOp::ReNone => Some(Rex::Empty),
        BuiltinOp::ReAll => Some(star(Rex::Range(0, MAX_CODE))),
        BuiltinOp::ReAllChar => Some(Rex::Range(0, MAX_CODE)),
        BuiltinOp::ReConcat => Some(concat(sub(ctx, &kids)?)),
        BuiltinOp::ReUnion => Some(union(sub(ctx, &kids)?)),
        BuiltinOp::ReInter => Some(inter(sub(ctx, &kids)?)),
        BuiltinOp::ReDiff => {
            let rs = sub(ctx, &kids)?;
            // Character-class fast path (slice 25): when every operand is a
            // character class, compute the difference as intervals, so the
            // surrogate-block gadget minted by `range_term` re-extracts as the
            // Range it encodes (round-trip shape stability). Derived endpoints
            // are `operand endpoint ± 1`, which for non-interior inputs can only
            // be the block edges D800/DFFF — never an interior surrogate.
            if let Some(all) = rs.iter().map(class_intervals).collect::<Option<Vec<_>>>() {
                let mut it = all.into_iter();
                let mut acc = it.next().expect("re.diff arity >= 2");
                for b in it {
                    acc = interval_diff(&acc, &b);
                }
                let parts: Vec<Rex> = acc
                    .into_iter()
                    .map(|(lo, hi)| {
                        debug_assert!(
                            range_rex(lo as i128, hi as i128).is_some(),
                            "interval algebra minted an interior-surrogate endpoint"
                        );
                        Rex::Range(lo, hi)
                    })
                    .collect();
                return Some(union(parts));
            }
            // Left-associative difference: a \ b \ c = inter(a, comp(b), comp(c)).
            let mut rs = rs.into_iter();
            let first = rs.next().expect("arity >= 2");
            let mut parts = vec![first];
            for r in rs {
                parts.push(comp(r));
            }
            Some(inter(parts))
        }
        BuiltinOp::ReStar => Some(star(extract_const_regex(ctx, kids[0])?)),
        BuiltinOp::RePlus => {
            // r+ = r · r*.
            let r = extract_const_regex(ctx, kids[0])?;
            Some(concat(vec![r.clone(), star(r)]))
        }
        BuiltinOp::ReOpt => {
            let r = extract_const_regex(ctx, kids[0])?;
            Some(union(vec![r, Rex::Eps]))
        }
        BuiltinOp::ReComp => Some(comp(extract_const_regex(ctx, kids[0])?)),
        BuiltinOp::ReRange => {
            let a = ctx.string_const_value(kids[0])?;
            let b = ctx.string_const_value(kids[1])?;
            let single = |s: &str| -> Option<Option<u32>> {
                // Outer None = fence (above alphabet); inner None = not a
                // single char (⇒ empty range per SMT-LIB).
                let mut it = s.chars();
                match (it.next(), it.next()) {
                    (Some(c), None) => {
                        let code = c as u32;
                        if code > MAX_CODE {
                            None // fence
                        } else {
                            Some(Some(code))
                        }
                    }
                    _ => Some(None), // empty range, decided
                }
            };
            match (single(a)?, single(b)?) {
                (Some(lo), Some(hi)) if lo <= hi => Some(Rex::Range(lo, hi)),
                _ => Some(Rex::Empty), // multi-char endpoint or lo > hi
            }
        }
        BuiltinOp::ReLoop { lo, hi } => Some(loop_(extract_const_regex(ctx, kids[0])?, lo, hi)),
        BuiltinOp::RePow(n) => Some(loop_(extract_const_regex(ctx, kids[0])?, n, n)),
        _ => None, // not a RegLan constructor
    }
}

/// `(str.in_re s R)`, children already rewritten. Some(bool-const) iff the
/// string side is a literal with no above-alphabet chars, `R` extracts as a
/// constant regex, and evaluation stays within fuel.
fn try_fold_in_re(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let s = ctx.string_const_value(kids[0])?.to_owned();
    if s.chars().any(|c| c as u32 > MAX_CODE) {
        return None; // above-alphabet fence
    }
    let rex = extract_const_regex(ctx, kids[1])?;
    let v = eval_membership(&s, &rex)?; // None = fuel → fence
    Some(ctx.mk_const_bool(v))
}

/// Slice 20: `t ∈ R` for ANY string term `t` when `L(R)` is structurally
/// finite (⇒ `⋁ t = wᵢ`) or co-finite (⇒ `¬⋁ t = wᵢ` over the exception
/// set). Full equivalences at any polarity — no fresh variables, no
/// repair. Skipped (→ fence) when the string side contains an
/// above-alphabet literal character (slice-18/19 posture: don't guess
/// semantics outside Σ) or when neither enumerator recognizes `R`.
fn try_rewrite_symbolic_in_re(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    if str_term_mentions_above_alphabet(ctx, kids[0]) {
        return None;
    }
    let rex = extract_const_regex(ctx, kids[1])?;
    if let Some(ws) = enum_lang(&rex) {
        return Some(mk_eq_disjunction(ctx, kids[0], &ws, false));
    }
    let exceptions = enum_comp(&rex)?;
    Some(mk_eq_disjunction(ctx, kids[0], &exceptions, true))
}

/// `⋁ᵢ (= t wᵢ)` — 0-ary folds straight to a Bool const (`negate` for the
/// co-finite reading), 1-ary is the bare equality, and `negate` wraps the
/// result in Not.
fn mk_eq_disjunction(ctx: &mut Context, t: TermId, words: &Words, negate: bool) -> TermId {
    if words.is_empty() {
        return ctx.mk_const_bool(negate);
    }
    let disj: Vec<TermId> = words
        .iter()
        .map(|w| {
            let lit = ctx.mk_string_const(w);
            ctx.mk_eq(t, lit).expect("well-sorted equality")
        })
        .collect();
    let core = if disj.len() == 1 {
        disj[0]
    } else {
        ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disj)
            .expect("well-sorted disjunction")
    };
    if negate {
        ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[core])
            .expect("well-sorted negation")
    } else {
        core
    }
}

/// Any literal character above the SMT-LIB alphabet anywhere in `t`?
pub(crate) fn str_term_mentions_above_alphabet(ctx: &Context, t: TermId) -> bool {
    if let Some(s) = ctx.string_const_value(t) {
        return s.chars().any(|c| c as u32 > MAX_CODE);
    }
    match ctx.term_node(t) {
        TermNode::App { args, .. } => {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            kids.iter()
                .any(|&k| str_term_mentions_above_alphabet(ctx, k))
        }
        TermNode::Const { .. } => false,
    }
}

/// Bottom-up memoized pass folding every GROUND `str.in_re` atom to a Bool
/// constant. Untouched subtrees keep their TermIds. Mirrors
/// `code_conv::rewrite_code_conv`.
pub fn rewrite_ground_in_re(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
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
                // Ground fold first (cheaper; also decides INFINITE
                // languages for literal strings), then the slice-20
                // finite/co-finite equivalence rewrite.
                Op::Builtin(BuiltinOp::StrInRe) => match try_fold_in_re(ctx, &new_children) {
                    Some(r) => Some(r),
                    None => try_rewrite_symbolic_in_re(ctx, &new_children),
                },
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
                        .expect("regex: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// Presence fence: true iff any `str.in_re` application or RegLan-sorted
/// subterm survives in `assertions`. Any hit ⇒ sound `Unknown`.
pub fn has_unreduced_regex(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        if ctx.sort_of(t) == ctx.reglan_sort() {
            return true;
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(BuiltinOp::StrInRe))
                    || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}

/// Slice-21 fence (replaces the slice-19/20 blanket presence fence at the
/// solver seam): true iff anything regex-shaped survives that the ENGINE
/// cannot own — a `str.in_re` whose regex side fails constant extraction or
/// whose string side mentions an above-alphabet literal, or any
/// RegLan-sorted subterm OUTSIDE the regex position of a supported
/// membership (RegLan equality, bare RegLan terms). Engine-eligible
/// memberships are NOT fenced — they flow to StrSolver as ordinary atoms.
pub fn has_unsupported_regex(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        if ctx.sort_of(t) == ctx.reglan_sort() {
            return true; // RegLan term outside a supported membership position
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids: Vec<TermId> = ctx.children(*args).to_vec();
                if matches!(op, Op::Builtin(BuiltinOp::StrInRe)) {
                    return extract_const_regex(ctx, kids[1]).is_none()
                        || str_term_mentions_above_alphabet(ctx, kids[0])
                        || walk(ctx, kids[0]);
                }
                kids.iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}

/// Test-only: `(re.* (re.range "a" "z"))` as a term.
#[cfg(test)]
pub(crate) fn test_az_star_term(ctx: &mut Context) -> TermId {
    rex_to_term(ctx, &star(Rex::Range('a' as u32, 'z' as u32)))
}

#[cfg(test)]
pub(crate) fn rex_to_term_test(ctx: &mut Context, r: &Rex) -> TermId {
    rex_to_term(ctx, r)
}
#[cfg(test)]
pub(crate) fn lit_test(s: &str) -> Rex {
    lit_to_rex(s).expect("ascii test literal")
}
#[cfg(test)]
pub(crate) fn star_lit_test(s: &str) -> Rex {
    star(lit_test(s))
}
#[cfg(test)]
pub(crate) fn star_range_test(lo: char, hi: char) -> Rex {
    star(Rex::Range(lo as u32, hi as u32))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A nullary uninterpreted constant of the given sort (codebase pattern).
    fn nullary(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn in_re(ctx: &mut Context, s: TermId, r: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, r])
            .unwrap()
    }

    fn to_re(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToRe), &[s]).unwrap()
    }

    #[test]
    fn fence_detects_in_re_and_reglan_subterms() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let re_s = ctx.reglan_sort();
        let s = nullary(&mut ctx, "s", str_s);

        // str.in_re app → fenced.
        let lit = ctx.mk_string_const("a");
        let r = to_re(&mut ctx, lit);
        let atom = in_re(&mut ctx, s, r);
        assert!(has_unreduced_regex(&ctx, &[atom]));

        // Bare RegLan equality → fenced (RegLan-sorted subterms).
        let rv = nullary(&mut ctx, "r", re_s);
        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let eq = ctx.mk_eq(rv, none).unwrap();
        assert!(has_unreduced_regex(&ctx, &[eq]));

        // Plain string assertion → NOT fenced.
        let b = ctx.mk_string_const("b");
        let seq = ctx.mk_eq(s, b).unwrap();
        assert!(!has_unreduced_regex(&ctx, &[seq]));
    }

    // ── Task 2: pure derivative engine ───────────────────────────────────

    /// (regex, string, expected membership) — one row per operator + the
    /// boundary lattice from the spec.
    fn chr(c: char) -> Rex {
        Rex::Range(c as u32, c as u32)
    }

    fn lit(s: &str) -> Rex {
        concat(s.chars().map(chr).collect())
    }

    #[test]
    fn smart_constructors_canonicalize() {
        // Concat: Empty absorbs, Eps drops, nested flattens, 0/1-ary collapse.
        assert_eq!(concat(vec![lit("a"), Rex::Empty]), Rex::Empty);
        assert_eq!(concat(vec![Rex::Eps, Rex::Eps]), Rex::Eps);
        assert_eq!(concat(vec![Rex::Eps, chr('a')]), chr('a'));
        assert_eq!(
            concat(vec![concat(vec![chr('a'), chr('b')]), chr('c')]),
            Rex::Concat(vec![chr('a'), chr('b'), chr('c')])
        );
        // Union: Empty drops, duplicates dedupe, nested flattens.
        assert_eq!(union(vec![Rex::Empty, chr('a')]), chr('a'));
        assert_eq!(union(vec![chr('a'), chr('a')]), chr('a'));
        assert_eq!(union(vec![Rex::Empty, Rex::Empty]), Rex::Empty);
        // Inter: Empty annihilates, duplicates dedupe.
        assert_eq!(inter(vec![chr('a'), Rex::Empty]), Rex::Empty);
        assert_eq!(inter(vec![chr('a'), chr('a')]), chr('a'));
        // Star: ∅* = ε* = ε; (r*)* = r*.
        assert_eq!(star(Rex::Empty), Rex::Eps);
        assert_eq!(star(Rex::Eps), Rex::Eps);
        assert_eq!(star(star(chr('a'))), star(chr('a')));
        // Comp: comp(comp(r)) = r.
        assert_eq!(comp(comp(chr('a'))), chr('a'));
        // Loop: lo > hi = ∅; r{0,0} = ε; ∅{0,k} = ε; ∅{1,k} = ∅.
        assert_eq!(loop_(chr('a'), 3, 2), Rex::Empty);
        assert_eq!(loop_(chr('a'), 0, 0), Rex::Eps);
        assert_eq!(loop_(Rex::Empty, 0, 4), Rex::Eps);
        assert_eq!(loop_(Rex::Empty, 1, 4), Rex::Empty);
    }

    #[test]
    fn comp_collapses_universal_and_empty_complements() {
        // Slice 25 task 5b, Part 1: comp(∅) = Σ* and comp(Σ*) = ∅ — the two
        // complement-of-Σ* identities the smart constructor was previously
        // missing (it only cancelled Comp∘Comp). Without these, derivatives
        // under negative polarity mint Comp(Star(Range(0,MAX_CODE))) (= ∅)
        // and Comp(Empty) (= Σ*) that never collapse, cascading toward the
        // Fuel budget.
        assert_eq!(comp(Rex::Empty), star(Rex::Range(0, MAX_CODE)));
        assert_eq!(comp(star(Rex::Range(0, MAX_CODE))), Rex::Empty);
        // Double-complement through the new identities too.
        assert_eq!(comp(comp(Rex::Empty)), Rex::Empty);
        assert_eq!(
            comp(comp(star(Rex::Range(0, MAX_CODE)))),
            star(Rex::Range(0, MAX_CODE))
        );
        // Generic double-complement (pre-existing identity) still holds.
        assert_eq!(comp(comp(chr('a'))), chr('a'));
    }

    #[test]
    fn inter_collapses_bounds_certified_empty_intersection() {
        // Slice 26 task 6a: `re.inter (str.to_re "b") (str.to_re "")` (the
        // it145 fuzz repro's shape) — two disjoint singletons {"b"} and
        // {""}. Structurally: min_len(Inter) = max(1, 0) = 1, max_len(Inter)
        // = min(Some(1), Some(0)) = Some(0). 1 > 0 is a sound emptiness
        // certificate (no length is simultaneously admissible by both
        // arms), so the smart constructor collapses to `Rex::Empty` instead
        // of building `Inter([chr('b'), Eps])` and losing the
        // contradiction to `concat()`'s all-or-nothing Empty check.
        assert_eq!(inter(vec![chr('b'), Rex::Eps]), Rex::Empty);

        // Negative: a·Σ* ∩ b·Σ* — the `targeted_leaf_membership_infinite_
        // conflict_known_gap` shape. Both arms have min_len = 1, max_len =
        // None (unbounded tail) — no FINITE upper bound exists on either
        // arm, so `max_len(Inter)` is `None` and the collapse must NOT
        // fire: no bounds certificate here, even though the languages are
        // in fact disjoint (refuting that needs real intersection
        // emptiness, banked as a known gap — see the pinned test).
        let a_star = concat(vec![chr('a'), star(Rex::Range(0, MAX_CODE))]);
        let b_star = concat(vec![chr('b'), star(Rex::Range(0, MAX_CODE))]);
        assert_eq!(
            inter(vec![a_star.clone(), b_star.clone()]),
            Rex::Inter(vec![a_star, b_star])
        );
    }

    #[test]
    fn union_coalesces_ranges() {
        // Adjacent intervals merge ([a,b] ∪ [b+1,c] = [a,c]).
        assert_eq!(
            union(vec![Rex::Range(97, 99), Rex::Range(100, 105)]),
            Rex::Range(97, 105)
        );
        // Overlapping intervals merge.
        assert_eq!(
            union(vec![Rex::Range(97, 103), Rex::Range(100, 105)]),
            Rex::Range(97, 105)
        );
        // Contained interval collapses.
        assert_eq!(
            union(vec![Rex::Range(97, 120), Rex::Range(100, 105)]),
            Rex::Range(97, 120)
        );
        // Disjoint (gap > 1) stays split, sorted by lo regardless of input order.
        assert_eq!(
            union(vec![Rex::Range(110, 120), Rex::Range(97, 99)]),
            Rex::Union(vec![Rex::Range(97, 99), Rex::Range(110, 120)])
        );
        // The slice's motivating fold: lo..D7FF ∪ block ∪ E000..hi = lo..hi.
        assert_eq!(
            union(vec![
                Rex::Range(99, 0xD7FF),
                Rex::Range(0xD800, 0xDFFF),
                Rex::Range(0xE000, MAX_CODE)
            ]),
            Rex::Range(99, MAX_CODE)
        );
        // Mixed members: coalesced ranges FIRST (sorted), then non-range
        // members in first-appearance order. Deterministic under permutation
        // of the range members.
        let st = star(Rex::Range(0, MAX_CODE));
        assert_eq!(
            union(vec![
                st.clone(),
                Rex::Range(100, 105),
                Rex::Eps,
                Rex::Range(97, 99)
            ]),
            Rex::Union(vec![Rex::Range(97, 105), st.clone(), Rex::Eps])
        );
        assert_eq!(
            union(vec![
                Rex::Range(97, 99),
                st.clone(),
                Rex::Range(100, 105),
                Rex::Eps
            ]),
            Rex::Union(vec![Rex::Range(97, 105), st, Rex::Eps])
        );
    }

    #[test]
    fn nullability_per_operator() {
        assert!(!nullable(&Rex::Empty));
        assert!(nullable(&Rex::Eps));
        assert!(!nullable(&chr('a')));
        assert!(nullable(&star(chr('a'))));
        assert!(!nullable(&concat(vec![chr('a'), star(chr('b'))])));
        assert!(nullable(&union(vec![chr('a'), Rex::Eps])));
        assert!(!nullable(&inter(vec![Rex::Eps, chr('a')])));
        assert!(nullable(&comp(chr('a')))); // "" ∉ {a} ⇒ "" ∈ comp
        assert!(!nullable(&comp(star(chr('a')))));
        assert!(nullable(&loop_(chr('a'), 0, 3)));
        assert!(!nullable(&loop_(chr('a'), 1, 3)));
        assert!(nullable(&loop_(union(vec![chr('a'), Rex::Eps]), 2, 3)));
    }

    #[test]
    fn ground_membership_per_operator() {
        let sigma = Rex::Range(0, MAX_CODE);
        let all = star(sigma.clone());
        let cases: Vec<(Rex, &str, bool)> = vec![
            // to_re / literal word.
            (lit("ab"), "ab", true),
            (lit("ab"), "ba", false),
            (lit(""), "", true),
            (lit(""), "a", false),
            // none / all / allchar.
            (Rex::Empty, "", false),
            (all.clone(), "", true),
            (all.clone(), "xyz", true),
            (sigma.clone(), "a", true),
            (sigma.clone(), "", false),
            (sigma.clone(), "ab", false),
            // concat / union / inter.
            (concat(vec![lit("a"), lit("b")]), "ab", true),
            (union(vec![lit("a"), lit("b")]), "b", true),
            (union(vec![lit("a"), lit("b")]), "c", false),
            (inter(vec![lit("ab"), all.clone()]), "ab", true),
            (inter(vec![lit("a"), lit("b")]), "a", false),
            // star / plus (plus = r·r*) / opt (union with ε).
            (star(lit("ab")), "", true),
            (star(lit("ab")), "ababab", true),
            (star(lit("ab")), "aba", false),
            (concat(vec![lit("a"), star(lit("a"))]), "", false),
            (concat(vec![lit("a"), star(lit("a"))]), "aaa", true),
            (union(vec![lit("a"), Rex::Eps]), "", true),
            // comp / diff (diff = inter with comp).
            (comp(lit("a")), "b", true),
            (comp(lit("a")), "a", false),
            (comp(lit("a")), "", true),
            (comp(Rex::Empty), "", true),
            (comp(Rex::Empty), "anything", true),
            (comp(all.clone()), "x", false),
            (comp(all.clone()), "", false),
            (inter(vec![sigma.clone(), comp(lit("a"))]), "b", true),
            (inter(vec![sigma.clone(), comp(lit("a"))]), "a", false),
            // range (incl. equal endpoints).
            (Rex::Range('a' as u32, 'c' as u32), "b", true),
            (Rex::Range('a' as u32, 'c' as u32), "d", false),
            (Rex::Range('a' as u32, 'a' as u32), "a", true),
            (Rex::Range('a' as u32, 'a' as u32), "b", false),
            // loop / pow.
            (loop_(lit("a"), 1, 2), "a", true),
            (loop_(lit("a"), 1, 2), "aa", true),
            (loop_(lit("a"), 1, 2), "aaa", false),
            (loop_(lit("a"), 1, 2), "", false),
            (loop_(lit("a"), 0, 2), "", true),
            (loop_(lit("ab"), 2, 2), "abab", true),
            (loop_(lit("ab"), 2, 2), "ab", false),
            // huge lazy bounds cost nothing.
            (loop_(lit("a"), 0, u32::MAX), "aaaa", true),
        ];
        for (rex, s, want) in cases {
            assert_eq!(
                eval_membership(s, &rex),
                Some(want),
                "membership of {s:?} in {rex:?}"
            );
        }
    }

    #[test]
    fn fuel_cap_aborts_instead_of_diverging() {
        // A tiny cap forces an abort on a regex whose derivative grows.
        let r = inter(vec![
            star(union(vec![lit("aa"), lit("aaa")])),
            star(union(vec![lit("aa"), lit("aaa")])),
            comp(star(lit("aaaa"))),
        ]);
        assert_eq!(eval_membership_capped("aaaaaaaa", &r, 1), None);
        // The real cap decides this easily (and correctly).
        assert!(eval_membership("aaaaaaaa", &r).is_some());
    }

    // ── Task 3: extraction + ground rewrite pass ─────────────────────────

    /// Build a str.in_re atom over a LITERAL string from an SMT-LIB-shaped
    /// term tree, run the rewrite pass, and expect a Bool fold.
    fn fold_of(ctx: &mut Context, atom: TermId) -> Option<bool> {
        let out = rewrite_ground_in_re(ctx, &[atom]);
        match ctx.term_node(out[0]) {
            TermNode::Const {
                val: shinri_core::ConstVal::Bool(b),
                ..
            } => Some(*b),
            _ => None,
        }
    }

    fn slit(ctx: &mut Context, s: &str) -> TermId {
        ctx.mk_string_const(s)
    }

    #[test]
    fn ground_atoms_fold_per_operator() {
        let mut ctx = Context::new();

        // ("ab", to_re("ab")) → true; ("ab", re.none) → false.
        let ab = slit(&mut ctx, "ab");
        let re_ab = to_re(&mut ctx, ab);
        let atom = in_re(&mut ctx, ab, re_ab);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let atom = in_re(&mut ctx, ab, none);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        // re.all / re.allchar.
        let all = ctx.mk_app(Op::Builtin(BuiltinOp::ReAll), &[]).unwrap();
        let atom = in_re(&mut ctx, ab, all);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let allchar = ctx.mk_app(Op::Builtin(BuiltinOp::ReAllChar), &[]).unwrap();
        let atom = in_re(&mut ctx, ab, allchar);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        let a = slit(&mut ctx, "a");
        let atom = in_re(&mut ctx, a, allchar);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        // (_ re.loop 1 2) over to_re("a"): "aa" in, "aaa" out.
        let re_a = to_re(&mut ctx, a);
        let loop12 = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: 1, hi: 2 }), &[re_a])
            .unwrap();
        let aa = slit(&mut ctx, "aa");
        let aaa = slit(&mut ctx, "aaa");
        let atom = in_re(&mut ctx, aa, loop12);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, aaa, loop12);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        // (_ re.^ 2): exactly two copies.
        let pow2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::RePow(2)), &[re_a])
            .unwrap();
        let atom = in_re(&mut ctx, aa, pow2);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, pow2);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        // re.comp / re.diff / re.inter / re.union / re.opt / re.+ / re.range.
        let b = slit(&mut ctx, "b");
        let re_b = to_re(&mut ctx, b);
        let comp_a = ctx.mk_app(Op::Builtin(BuiltinOp::ReComp), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, b, comp_a);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, comp_a);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        let diff = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReDiff), &[allchar, re_a])
            .unwrap();
        let atom = in_re(&mut ctx, b, diff);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, diff);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        let un = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &[re_a, re_b])
            .unwrap();
        let atom = in_re(&mut ctx, b, un);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let it = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReInter), &[un, re_b])
            .unwrap();
        let atom = in_re(&mut ctx, b, it);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, it);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        let empty = slit(&mut ctx, "");
        let opt = ctx.mk_app(Op::Builtin(BuiltinOp::ReOpt), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, empty, opt);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let plus = ctx.mk_app(Op::Builtin(BuiltinOp::RePlus), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, empty, plus);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        let atom = in_re(&mut ctx, aaa, plus);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let z = slit(&mut ctx, "c");
        let range = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, z])
            .unwrap();
        let atom = in_re(&mut ctx, b, range);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let d = slit(&mut ctx, "d");
        let atom = in_re(&mut ctx, d, range);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
    }

    #[test]
    fn degenerate_range_and_loop_are_decided_empty() {
        let mut ctx = Context::new();
        let a = slit(&mut ctx, "a");
        // Multi-char endpoint ⇒ empty range (decided, NOT fenced).
        let ab = slit(&mut ctx, "ab");
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, ab])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // Reversed endpoints ⇒ empty.
        let c = slit(&mut ctx, "c");
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[c, a])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // Loop lo > hi ⇒ empty.
        let re_a = to_re(&mut ctx, a);
        let l = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: 3, hi: 1 }), &[re_a])
            .unwrap();
        let atom = in_re(&mut ctx, a, l);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // Empty-string membership of ε-shapes: "" in to_re("") → true.
        let empty = slit(&mut ctx, "");
        let re_empty = to_re(&mut ctx, empty);
        let atom = in_re(&mut ctx, empty, re_empty);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
    }

    #[test]
    fn atoms_fold_under_boolean_structure() {
        // Equivalences need no polarity tracking: fold under not/or/ite too.
        let mut ctx = Context::new();
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, a, re_a); // true
        let not = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[atom]).unwrap();
        let out = rewrite_ground_in_re(&mut ctx, &[not]);
        // not(true) — the pass does NOT simplify Boolean structure, only the
        // atom folds; check the child became const true.
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("expected Not app");
        };
        let child = ctx.children(args).to_vec()[0];
        assert!(matches!(
            ctx.term_node(child),
            TermNode::Const {
                val: shinri_core::ConstVal::Bool(true),
                ..
            }
        ));
        assert!(!has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn non_ground_shapes_survive_to_fence() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");

        // Symbolic string side, against a genuinely undecidable (neither
        // finite nor co-finite) language: slice 20 DECIDES symbolic string
        // sides when `L(R)` is finite/co-finite (see the
        // `symbolic_*` tests below), so `to_re("a")` alone (finite, {"a"})
        // no longer belongs here — use `re.*` to keep testing a genuine
        // fence reason.
        let re_a = to_re(&mut ctx, a);
        let st = ctx.mk_app(Op::Builtin(BuiltinOp::ReStar), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, s, st);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert_eq!(out[0], atom, "must not rewrite");
        assert!(has_unreduced_regex(&ctx, &out));

        // Symbolic to_re argument.
        let re_s = to_re(&mut ctx, s);
        let atom = in_re(&mut ctx, a, re_s);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));

        // Symbolic range endpoint.
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, s])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));

        // RegLan variable in the regex.
        let reglan = ctx.reglan_sort();
        let rv = nullary(&mut ctx, "r", reglan);
        let atom = in_re(&mut ctx, a, rv);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn above_alphabet_literals_fence() {
        let mut ctx = Context::new();
        // Ground string containing U+30000 (> MAX_CODE) — no fold.
        let hi = slit(&mut ctx, "\u{30000}");
        let all = ctx.mk_app(Op::Builtin(BuiltinOp::ReAll), &[]).unwrap();
        let atom = in_re(&mut ctx, hi, all);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // Range endpoint above the alphabet — no fold.
        let a = slit(&mut ctx, "a");
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, hi])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // to_re over an above-alphabet literal — no fold.
        let re_hi = to_re(&mut ctx, hi);
        let atom = in_re(&mut ctx, a, re_hi);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn untouched_subtrees_keep_their_termids() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let lit = slit(&mut ctx, "xy");
        let eq = ctx.mk_eq(s, lit).unwrap();
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, a, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[eq, atom]);
        assert_eq!(out[0], eq, "unrelated assertion must keep its TermId");
        assert!(matches!(
            ctx.term_node(out[1]),
            TermNode::Const {
                val: shinri_core::ConstVal::Bool(true),
                ..
            }
        ));
    }

    // ── Task 1 (slice 20): finite / co-finite enumeration ────────────────

    fn words(xs: &[&str]) -> Words {
        xs.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn enum_lang_per_operator() {
        // Leaves.
        assert_eq!(enum_lang(&Rex::Empty), Some(words(&[])));
        assert_eq!(enum_lang(&Rex::Eps), Some(words(&[""])));
        assert_eq!(
            enum_lang(&Rex::Range('a' as u32, 'c' as u32)),
            Some(words(&["a", "b", "c"]))
        );
        // Concat: cross product.
        assert_eq!(
            enum_lang(&concat(vec![union(vec![lit("a"), lit("b")]), lit("x")])),
            Some(words(&["ax", "bx"]))
        );
        // Union: set union, deduped (BTreeSet order = determinism).
        assert_eq!(
            enum_lang(&union(vec![lit("b"), lit("a"), lit("b")])),
            Some(words(&["a", "b"]))
        );
        // Inter: filter the finite side through the other (comp!) sides.
        assert_eq!(
            enum_lang(&inter(vec![
                union(vec![lit("a"), lit("b")]),
                comp(lit("a"))
            ])),
            Some(words(&["b"]))
        );
        // Loop: bounded powers, including the ε floor at lo = 0.
        assert_eq!(
            enum_lang(&loop_(lit("a"), 1, 3)),
            Some(words(&["a", "aa", "aaa"]))
        );
        assert_eq!(
            enum_lang(&loop_(union(vec![lit("a"), lit("b")]), 0, 1)),
            Some(words(&["", "a", "b"]))
        );
        // Star / Comp: never structurally finite.
        assert_eq!(enum_lang(&star(lit("a"))), None);
        assert_eq!(enum_lang(&comp(lit("a"))), None);
    }

    #[test]
    fn enum_lang_loop_degenerate_inner_terminates() {
        // L(inner) = ∅ (Inter of disjoint literals) — invisible to the smart
        // constructors, so the Loop node survives; the enumerator must
        // early-out instead of iterating toward the huge bound.
        let empty_lang = inter(vec![lit("a"), lit("b")]);
        assert_eq!(
            enum_lang(&loop_(empty_lang.clone(), 1, u32::MAX)),
            Some(words(&[]))
        );
        assert_eq!(
            enum_lang(&loop_(empty_lang, 0, u32::MAX)),
            Some(words(&[""]))
        );
        // L(inner) = {""}: Inter of two opt-shapes — again invisible to the
        // constructors. Without the early-out this loop would spin ~2^32
        // no-growth iterations.
        let eps_lang = inter(vec![
            union(vec![lit("a"), Rex::Eps]),
            union(vec![lit("b"), Rex::Eps]),
        ]);
        assert_eq!(enum_lang(&loop_(eps_lang, 5, u32::MAX)), Some(words(&[""])));
    }

    #[test]
    fn enum_caps_and_surrogates_abort() {
        // Cardinality cap: 3^6 = 729 words > 256.
        let abc = union(vec![lit("a"), lit("b"), lit("c")]);
        assert_eq!(enum_lang(&loop_(abc, 6, 6)), None);
        // Byte cap: ONE word of 100·60 = 6000 bytes > 4096 — the shape the
        // cardinality cap cannot see.
        let a100 = lit(&"a".repeat(100));
        assert_eq!(enum_lang(&loop_(a100, 60, 60)), None);
        // Huge-bound loop over a single word: aborts via the caps, fast.
        assert_eq!(enum_lang(&loop_(lit("a"), 1, u32::MAX)), None);
        // Range wider than the cardinality cap.
        assert_eq!(enum_lang(&Rex::Range(0, 300)), None);
        // Surrogate-crossing range: explicit guard.
        assert_eq!(enum_lang(&Rex::Range(0xD000, 0xE000)), None);
    }

    #[test]
    fn enum_comp_per_operator() {
        let sigma_star = star(Rex::Range(0, MAX_CODE));
        // re.all: co-finite with zero exceptions.
        assert_eq!(enum_comp(&sigma_star), Some(words(&[])));
        // comp(finite): exceptions are exactly the finite words.
        assert_eq!(
            enum_comp(&comp(union(vec![lit("a"), lit("b")]))),
            Some(words(&["a", "b"]))
        );
        // Inter of co-finites: union of exceptions (Σ*\⋂ = ⋃ complements).
        assert_eq!(
            enum_comp(&inter(vec![comp(lit("a")), comp(lit("b"))])),
            Some(words(&["a", "b"]))
        );
        // The extracted re.diff(re.all, X) shape: inter(Σ*, comp(X)).
        assert_eq!(
            enum_comp(&inter(vec![sigma_star.clone(), comp(lit("a"))])),
            Some(words(&["a"]))
        );
        // Union with a co-finite part: its exceptions filtered by
        // NON-membership in the other parts ("b" rejoins via to_re "b").
        assert_eq!(
            enum_comp(&union(vec![
                comp(union(vec![lit("a"), lit("b")])),
                lit("b")
            ])),
            Some(words(&["a"]))
        );
        // Not structurally co-finite: finite shapes, star, bare ranges.
        assert_eq!(enum_comp(&lit("a")), None);
        assert_eq!(enum_comp(&Rex::Eps), None);
        assert_eq!(enum_comp(&Rex::Empty), None);
        assert_eq!(enum_comp(&star(lit("a"))), None);
        assert_eq!(enum_comp(&Rex::Range('a' as u32, 'c' as u32)), None);
    }

    // ── Task 2 (slice 20): symbolic rewrite fallback ─────────────────────

    /// Collect the string-literal RHS values of an Or-of-equalities term.
    fn eq_disjunct_values(ctx: &Context, t: TermId) -> Vec<String> {
        let TermNode::App { op, args, .. } = ctx.term_node(t) else {
            panic!("expected app");
        };
        let kids: Vec<TermId> = ctx.children(*args).to_vec();
        let eqs: Vec<TermId> = match op {
            Op::Builtin(BuiltinOp::Or) => kids,
            Op::Builtin(BuiltinOp::Eq) => vec![t],
            other => panic!("expected Or/Eq, got {other:?}"),
        };
        eqs.iter()
            .map(|&e| {
                let TermNode::App { args, .. } = ctx.term_node(e) else {
                    panic!("expected Eq app");
                };
                let ch = ctx.children(*args).to_vec();
                ctx.string_const_value(ch[1])
                    .expect("literal RHS")
                    .to_owned()
            })
            .collect()
    }

    #[test]
    fn symbolic_finite_atom_rewrites_to_eq_disjunction() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let b = slit(&mut ctx, "b");
        let re_a = to_re(&mut ctx, a);
        let re_b = to_re(&mut ctx, b);
        let un = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &[re_a, re_b])
            .unwrap();
        let atom = in_re(&mut ctx, s, un);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(!has_unreduced_regex(&ctx, &out), "atom must be rewritten");
        let mut vals = eq_disjunct_values(&ctx, out[0]);
        vals.sort();
        assert_eq!(vals, vec!["a".to_owned(), "b".to_owned()]);

        // Singleton language: a bare equality, no Or wrapper.
        let atom = in_re(&mut ctx, s, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert_eq!(eq_disjunct_values(&ctx, out[0]), vec!["a".to_owned()]);
    }

    #[test]
    fn symbolic_cofinite_atom_rewrites_to_negated_disjunction() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let cmp = ctx.mk_app(Op::Builtin(BuiltinOp::ReComp), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, s, cmp);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(!has_unreduced_regex(&ctx, &out));
        // Shape: (not (= s "a")).
        let TermNode::App {
            op: Op::Builtin(BuiltinOp::Not),
            args,
            ..
        } = ctx.term_node(out[0]).clone()
        else {
            panic!("expected Not, got {:?}", ctx.term_node(out[0]));
        };
        let inner = ctx.children(args).to_vec()[0];
        assert_eq!(eq_disjunct_values(&ctx, inner), vec!["a".to_owned()]);
    }

    #[test]
    fn symbolic_zero_word_languages_fold_to_bool_consts() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        // s ∈ re.none → false.
        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let atom = in_re(&mut ctx, s, none);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // s ∈ re.all → true (co-finite, zero exceptions).
        let all = ctx.mk_app(Op::Builtin(BuiltinOp::ReAll), &[]).unwrap();
        let atom = in_re(&mut ctx, s, all);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
    }

    #[test]
    fn symbolic_out_of_fragment_shapes_still_fence() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        // Star: neither finite nor co-finite.
        let st = ctx.mk_app(Op::Builtin(BuiltinOp::ReStar), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, s, st);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // Over-cap: (_ re.loop 1 300) over one char = 300 words > 256.
        let l = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: 1, hi: 300 }), &[re_a])
            .unwrap();
        let atom = in_re(&mut ctx, s, l);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // Symbolic regex leaf still fences (extraction fails).
        let re_s = to_re(&mut ctx, s);
        let atom = in_re(&mut ctx, s, re_s);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn above_alphabet_string_side_skips_symbolic_rewrite() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        // Bare above-alphabet literal side (ground path already declines;
        // the symbolic path must decline too, not "decide" it).
        let hi = slit(&mut ctx, "\u{30000}");
        let atom = in_re(&mut ctx, hi, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // Concat-embedded above-alphabet literal.
        let cc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[s, hi])
            .unwrap();
        let atom = in_re(&mut ctx, cc, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn symbolic_rewrite_keeps_unrelated_termids() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let lit_xy = slit(&mut ctx, "xy");
        let eq = ctx.mk_eq(s, lit_xy).unwrap();
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, s, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[eq, atom]);
        assert_eq!(out[0], eq, "unrelated assertion must keep its TermId");
        assert_ne!(out[1], atom, "membership atom must be rewritten");
    }

    // ── Task 1 (slice 21): classes, reverse translation, word search ────────

    #[test]
    fn next_classes_partition_sigma() {
        // [a-z]* → boundaries {0, 'a', 'z'+1} → 3 classes covering Σ exactly.
        let r = star(Rex::Range('a' as u32, 'z' as u32));
        let cls = next_classes(&r).unwrap();
        assert_eq!(
            cls,
            vec![
                (0, 'a' as u32 - 1),
                ('a' as u32, 'z' as u32),
                ('z' as u32 + 1, MAX_CODE)
            ]
        );
        // Σ itself (re.allchar): ONE class.
        assert_eq!(
            next_classes(&Rex::Range(0, MAX_CODE)),
            Some(vec![(0, MAX_CODE)])
        );
        // No ranges at all (∅, ε): one class covering Σ.
        assert_eq!(next_classes(&Rex::Eps), Some(vec![(0, MAX_CODE)]));
        // Cap abort: 40 disjoint single-char ranges → 81 boundaries > 64.
        let many = union((0..40u32).map(|i| Rex::Range(3 * i, 3 * i)).collect());
        assert_eq!(next_classes(&many), None);
    }

    #[test]
    fn next_classes_derivative_uniform() {
        // Inside each class the derivative is identical to the representative's.
        let r = concat(vec![
            union(vec![Rex::Range('a' as u32, 'm' as u32), lit("xy")]),
            star(Rex::Range('0' as u32, '9' as u32)),
        ]);
        for (lo, hi) in next_classes(&r).unwrap() {
            let d0 = deriv(lo, &r);
            for c in [lo, (lo + hi) / 2, hi] {
                assert_eq!(deriv(c, &r), d0, "class [{lo},{hi}] not uniform at {c}");
            }
        }
    }

    #[test]
    fn head_forced_shapes() {
        // Bare range: forced head, ε residual.
        assert_eq!(
            head_forced(&Rex::Range('a' as u32, 'z' as u32)),
            Some((('a' as u32, 'z' as u32), Rex::Eps))
        );
        // Range-headed concat: forced head, concat residual.
        let r = concat(vec![Rex::Range('a' as u32, 'a' as u32), star(lit("b"))]);
        let (c, rest) = head_forced(&r).unwrap();
        assert_eq!(c, ('a' as u32, 'a' as u32));
        assert_eq!(rest, star(lit("b")));
        // Not head-forced: star, union, eps, empty, comp.
        assert_eq!(head_forced(&star(lit("a"))), None);
        assert_eq!(head_forced(&Rex::Eps), None);
        assert_eq!(head_forced(&Rex::Empty), None);
        assert_eq!(head_forced(&comp(lit("a"))), None);
    }

    #[test]
    fn rex_to_term_roundtrips_language() {
        // Round-trip is SEMANTIC (same language), not syntactic in general —
        // e.g. RePlus desugars to Concat/Star on the way back. (Surrogate
        // ranges specifically DO fold back to Range shape; see
        // rediff_block_gadget_folds_to_range.)
        let mut ctx = Context::new();
        let samples = ["", "a", "z", "ab", "ba", "0", "abc", "zzz"];
        let cases = vec![
            Rex::Empty,
            Rex::Eps,
            Rex::Range('a' as u32, 'z' as u32),
            star(Rex::Range('a' as u32, 'z' as u32)),
            comp(star(Rex::Range('a' as u32, 'z' as u32))),
            concat(vec![lit("a"), star(union(vec![lit("b"), lit("c")]))]),
            loop_(Rex::Range('a' as u32, 'b' as u32), 1, 3),
            inter(vec![star(lit("a")), comp(lit("aa"))]),
        ];
        for r in cases {
            let t = rex_to_term(&mut ctx, &r);
            let back = extract_const_regex(&ctx, t).expect("minted term must extract");
            for s in samples {
                assert_eq!(
                    eval_membership(s, &back),
                    eval_membership(s, &r),
                    "language mismatch on {s:?} for {r:?}"
                );
            }
        }
    }

    #[test]
    fn rex_to_term_surrogate_block_range() {
        // A class ending at 0xDFFF and one starting at 0xD800 — the only
        // surrogate endpoints that can arise. The minted term must extract to
        // a Rex with the same membership on representative code points.
        let mut ctx = Context::new();
        for (lo, hi) in [
            (0xD800u32, 0xDFFFu32),
            ('a' as u32, 0xDFFF),
            (0xD800, 0x2FFFF),
        ] {
            let t = rex_to_term(&mut ctx, &Rex::Range(lo, hi));
            let back = extract_const_regex(&ctx, t).expect("surrogate range term extracts");
            // Membership decided per code point via deriv (u32-exact — works
            // for surrogates even though no Rust literal can hold them).
            for c in [
                0u32, 'a' as u32, 0xD7FF, 0xD800, 0xDBBB, 0xDFFF, 0xE000, 0x2FFFF,
            ] {
                let want = lo <= c && c <= hi;
                assert_eq!(
                    nullable(&deriv(c, &back)),
                    want,
                    "code point {c:#x} in [{lo:#x},{hi:#x}]"
                );
            }
        }
    }

    #[test]
    fn search_word_finds_and_bounds() {
        let az_star = star(Rex::Range('a' as u32, 'z' as u32));
        // Word of exact length, all lengths realizable.
        assert_eq!(search_word(&az_star, 0), Some(String::new()));
        let w = search_word(&az_star, 3).unwrap();
        assert_eq!(w.chars().count(), 3);
        assert_eq!(eval_membership(&w, &az_star), Some(true));
        // Intersection via the smart constructor: a* ∩ [a-z]{2}.
        let two = loop_(Rex::Range('a' as u32, 'z' as u32), 2, 2);
        let w2 = search_word(&inter(vec![star(lit("a")), two]), 2).unwrap();
        assert_eq!(w2, "aa");
        // No word of that length: a* has no length-1 word other than "a";
        // a* ∩ b* has none at length ≥ 1.
        assert_eq!(
            search_word(&inter(vec![star(lit("a")), star(lit("b"))]), 1),
            None
        );
        // Surrogate-only language: L = the surrogate block — no Rust witness.
        assert_eq!(search_word(&Rex::Range(0xD800, 0xDFFF), 1), None);
        // Witness skips the block: [0xD7FF-0xE001] at length 1 minted as 0xD7FF.
        let w3 = search_word(&Rex::Range(0xD7FF, 0xE001), 1).unwrap();
        assert_eq!(w3.chars().next().unwrap() as u32, 0xD7FF);
        // Step-cap abort returns None (sound): a comp-heavy state space at a
        // length the cap cannot cover. comp(a*) words of length 40 over Σ force
        // one derivative state per prefix — cap trips before depth 40 × classes.
        let hard = inter(
            (0..12)
                .map(|i| comp(loop_(Rex::Range(0, MAX_CODE), i, i)))
                .collect(),
        );
        let _ = search_word(&hard, 40); // must terminate (None or Some) without hanging
    }

    #[test]
    fn search_word_deep_witness_no_stack_overflow() {
        // Regression pin (slice 26): `search_word` used to recurse once per
        // character — a witness this deep overflowed the default 2 MiB
        // test-thread stack, aborting the whole test binary. Σ* yields a
        // single next-character class, so the 9000-char descent costs exactly
        // 9001 visited states — inside MEMB_SEARCH_STEP_CAP with the
        // explicit-stack DFS, and 9000 stack frames if the O(n) recursion
        // ever returns.
        let sigma_star = Rex::Star(Box::new(Rex::Range(0, MAX_CODE)));
        let w = search_word(&sigma_star, 9000).expect("Σ* word of length 9000");
        assert_eq!(w.chars().count(), 9000);
    }

    #[test]
    fn search_shortest_finds_minimal_words() {
        let sigma = Rex::Range(0, MAX_CODE);
        let sigma_star = star(Rex::Range(0, MAX_CODE));
        let b = Rex::Range('b' as u32, 'b' as u32);
        let c = Rex::Range('c' as u32, 'c' as u32);
        // b·Σ·Σ*: shortest word has exactly 2 chars and is a member.
        let strict = concat(vec![b.clone(), sigma.clone(), sigma_star.clone()]);
        let w = search_shortest(&strict).unwrap();
        assert_eq!(w.chars().count(), 2);
        assert_eq!(eval_membership(&w, &strict), Some(true));
        // Union with a trivially-short arm: (bc·Σ* ∪ "q") → the length-1 arm.
        let bc_star = concat(vec![b.clone(), c.clone(), sigma_star.clone()]);
        let q = Rex::Range('q' as u32, 'q' as u32);
        let u = union(vec![bc_star, q]);
        let wq = search_shortest(&u).unwrap();
        assert_eq!(wq, "q");
        // Nullable goal: the shortest word is ε.
        assert_eq!(search_shortest(&sigma_star), Some(String::new()));
        // Empty intersection: no word at any length — None, terminating.
        let empty = inter(vec![b.clone(), c.clone()]);
        assert_eq!(search_shortest(&empty), None);
        // Rex::Empty: None.
        assert_eq!(search_shortest(&Rex::Empty), None);
        // Pure-surrogate language: no Rust witness — None (skipped classes).
        assert_eq!(search_shortest(&Rex::Range(0xD800, 0xDFFF)), None);
    }

    #[test]
    fn min_max_len_bounds() {
        let sigma = Rex::Range(0, MAX_CODE);
        let sigma_star = star(Rex::Range(0, MAX_CODE));
        let b = Rex::Range('b' as u32, 'b' as u32);
        let c = Rex::Range('c' as u32, 'c' as u32);
        // The strict-< gadget arm: b·Σ·Σ* — min 2, no upper bound.
        let strict = concat(vec![b.clone(), sigma.clone(), sigma_star.clone()]);
        assert_eq!(min_len(&strict), 2);
        assert_eq!(max_len(&strict), None);
        // The full order gadget: Range(c,MAX)·Σ* ∪ b·Σ·Σ* — min 1 (above arm).
        let above = concat(vec![Rex::Range('c' as u32, MAX_CODE), sigma_star.clone()]);
        let gadget = union(vec![above, strict.clone()]);
        assert_eq!(min_len(&gadget), 1);
        assert_eq!(max_len(&gadget), None);
        // Finite concat: b·Σ·Σ — exactly [3,3].
        let finite = concat(vec![b.clone(), sigma.clone(), sigma.clone()]);
        assert_eq!(min_len(&finite), 3);
        assert_eq!(max_len(&finite), Some(3));
        // Bare range: the degenerate [1,1] (the sibling leaf arm's axiom).
        assert_eq!(min_len(&b), 1);
        assert_eq!(max_len(&b), Some(1));
        // Word via concat of ranges: "bc" then Σ* — min 2, unbounded.
        let bc_star = concat(vec![b.clone(), c.clone(), sigma_star.clone()]);
        assert_eq!(min_len(&bc_star), 2);
        assert_eq!(max_len(&bc_star), None);
        // Nullable shapes: 0.
        assert_eq!(min_len(&sigma_star), 0);
        assert_eq!(max_len(&sigma_star), None);
        assert_eq!(min_len(&Rex::Eps), 0);
        assert_eq!(max_len(&Rex::Eps), Some(0));
        // Comp is conservative: [0, None] — sound, not exact.
        assert_eq!(min_len(&comp(b.clone())), 0);
        assert_eq!(max_len(&comp(b.clone())), None);
        // Inter: min is the MAX of arm minima; max is the MIN of finite arm maxima.
        let i = inter(vec![strict.clone(), finite.clone()]);
        assert_eq!(min_len(&i), 3);
        assert_eq!(max_len(&i), Some(3));
        // Loop: r{2,4} over a single char.
        let l = loop_(b.clone(), 2, 4);
        assert_eq!(min_len(&l), 2);
        assert_eq!(max_len(&l), Some(4));
        // Union with an unbounded arm has no finite max.
        assert_eq!(max_len(&union(vec![b.clone(), sigma_star])), None);
    }

    // slice-26 final-review soundness fix: `max_len` must yield `None` (not
    // a saturated, too-small `u32::MAX`) whenever the true upper bound
    // overflows `u32`. A saturated value here would understate the true
    // maximum and turn the memb.rs leaf `len ≤ max_len` axiom unsound
    // (wrong Unsat). See the `max_len` doc comment for the full rationale.
    #[test]
    fn max_len_overflow_yields_none() {
        let b = Rex::Range('b' as u32, 'b' as u32);
        let c = Rex::Range('c' as u32, 'c' as u32);
        // Loop: a 2-char literal "bc" looped up to 3e9 times has a true max
        // of 6e9, which overflows u32 (max ~4.3e9) — must be None, not a
        // saturated (and too-small) u32::MAX.
        let bc = concat(vec![b.clone(), c.clone()]);
        let looped = loop_(bc, 0, 3_000_000_000);
        assert_eq!(max_len(&looped), None);
        // Concat: sum of finite child maxima overflows u32 — must be None.
        let big = loop_(b.clone(), 0, u32::MAX);
        let overflowing_concat = concat(vec![big.clone(), big]);
        assert_eq!(max_len(&overflowing_concat), None);
        // Non-regression: a comfortably finite case still returns the exact
        // Some value.
        let finite = concat(vec![b.clone(), c.clone(), b]);
        assert_eq!(max_len(&finite), Some(3));
    }

    #[test]
    fn eval_str_in_re_term_level() {
        let mut ctx = Context::new();
        let r = star(Rex::Range('a' as u32, 'z' as u32));
        let t = rex_to_term(&mut ctx, &r);
        assert_eq!(eval_str_in_re(&ctx, "abc", t), Some(true));
        assert_eq!(eval_str_in_re(&ctx, "aBc", t), Some(false));
        // Symbolic regex term → None (cannot evaluate).
        let v = {
            let s = ctx.declare_fun("L", &[], ctx.reglan_sort());
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        assert_eq!(eval_str_in_re(&ctx, "a", v), None);
        // Above-alphabet string → None.
        assert_eq!(eval_str_in_re(&ctx, "\u{30000}", t), None);
    }

    // ── Task 2 (slice 21): narrowed fence ────────────────────────────────

    #[test]
    fn unsupported_regex_fence_narrowed() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        // Engine-eligible: symbolic string × constant infinite regex → NOT fenced.
        let az_star = rex_to_term(&mut ctx, &star(Rex::Range('a' as u32, 'z' as u32)));
        let ok = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, az_star])
            .unwrap();
        assert!(!has_unsupported_regex(&ctx, &[ok]));
        // Symbolic REGEX side → fenced.
        let lvar = {
            let s = ctx.declare_fun("L", &[], ctx.reglan_sort());
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let sym = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, lvar])
            .unwrap();
        assert!(has_unsupported_regex(&ctx, &[sym]));
        // Above-alphabet string side → fenced.
        let hi = ctx.mk_string_const("\u{30000}");
        let bad = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[hi, az_star])
            .unwrap();
        assert!(has_unsupported_regex(&ctx, &[bad]));
        // Bare RegLan term outside membership position (RegLan equality) → fenced.
        let two = rex_to_term(&mut ctx, &lit("q"));
        let re_eq = ctx.mk_eq(lvar, two).unwrap();
        assert!(has_unsupported_regex(&ctx, &[re_eq]));
        // The eligible atom under Boolean structure stays unfenced.
        let notok = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[ok]).unwrap();
        assert!(!has_unsupported_regex(&ctx, &[notok]));
    }

    #[test]
    fn rediff_block_gadget_folds_to_range() {
        let mut ctx = Context::new();
        // rex_to_term encodes the surrogate block Range(D800,DFFF) as the
        // re.diff gadget (range_term); extraction must fold it back to the
        // Range it encodes — shape, not just language.
        let block = Rex::Range(0xD800, 0xDFFF);
        let t = rex_to_term(&mut ctx, &block);
        assert_eq!(extract_const_regex(&ctx, t), Some(block));
        // A full straddling range round-trips whole (gadget fold + Task 1's
        // union coalescing).
        let straddle = Rex::Range('c' as u32, 0xE000);
        let t = rex_to_term(&mut ctx, &straddle);
        assert_eq!(extract_const_regex(&ctx, t), Some(straddle));
        let full = Rex::Range('c' as u32, MAX_CODE);
        let t = rex_to_term(&mut ctx, &full);
        assert_eq!(extract_const_regex(&ctx, t), Some(full));
    }

    #[test]
    fn rediff_ascii_interval_algebra() {
        let mut ctx = Context::new();
        // [a-z] \ [d-f] = [a-c] ∪ [g-z].
        let az = range_term_raw(&mut ctx, 'a' as u32, 'z' as u32);
        let df = range_term_raw(&mut ctx, 'd' as u32, 'f' as u32);
        let d = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReDiff), &[az, df])
            .unwrap();
        assert_eq!(
            extract_const_regex(&ctx, d),
            Some(Rex::Union(vec![
                Rex::Range('a' as u32, 'c' as u32),
                Rex::Range('g' as u32, 'z' as u32)
            ]))
        );
        // Subtracting a superset → Empty.
        let d2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReDiff), &[df, az])
            .unwrap();
        assert_eq!(extract_const_regex(&ctx, d2), Some(Rex::Empty));
    }

    #[test]
    fn rediff_non_class_operand_keeps_inter_comp_shape() {
        let mut ctx = Context::new();
        // A non-class operand (Star) must keep today's inter/comp construction
        // bit-for-bit — the fast path fires ONLY when all operands are classes.
        let az = range_term_raw(&mut ctx, 'a' as u32, 'z' as u32);
        let inner = range_term_raw(&mut ctx, 'a' as u32, 'z' as u32);
        let star_t = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReStar), &[inner])
            .unwrap();
        let d = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReDiff), &[az, star_t])
            .unwrap();
        assert_eq!(
            extract_const_regex(&ctx, d),
            Some(inter(vec![
                Rex::Range('a' as u32, 'z' as u32),
                comp(star(Rex::Range('a' as u32, 'z' as u32)))
            ]))
        );
    }

    #[test]
    fn interval_diff_edges() {
        // b covers a's head; a's tail survives.
        assert_eq!(interval_diff(&[(5, 20)], &[(0, 9)]), vec![(10, 20)]);
        // b splits a in two.
        assert_eq!(
            interval_diff(&[(5, 20)], &[(8, 12)]),
            vec![(5, 7), (13, 20)]
        );
        // Multiple b intervals carve multiple holes.
        assert_eq!(
            interval_diff(&[(0, 30)], &[(5, 6), (10, 12), (28, 40)]),
            vec![(0, 4), (7, 9), (13, 27)]
        );
        // Disjoint b: a unchanged.
        assert_eq!(interval_diff(&[(5, 9)], &[(20, 30)]), vec![(5, 9)]);
        // Exact cover → empty.
        assert_eq!(
            interval_diff(&[(5, 9)], &[(5, 9)]),
            Vec::<(u32, u32)>::new()
        );
    }

    #[test]
    fn range_rex_endpoint_policy() {
        // Empty interval ⇒ Rex::Empty (the caller's union/concat then drop it).
        assert_eq!(range_rex(0, -1), Some(Rex::Empty));
        assert_eq!(range_rex(98, 97), Some(Rex::Empty));
        // Ordinary in-alphabet range.
        assert_eq!(range_rex(0, 97), Some(Rex::Range(0, 97)));
        assert_eq!(range_rex(97, 97), Some(Rex::Range(97, 97)));
        // Surrogate BLOCK EDGES (0xD800 / 0xDFFF) are expressible via re.diff.
        assert_eq!(range_rex(0, 0xDFFF), Some(Rex::Range(0, 0xDFFF)));
        assert_eq!(range_rex(0xD800, 0xDFFF), Some(Rex::Range(0xD800, 0xDFFF)));
        // An endpoint STRICTLY inside the surrogate block ⇒ None (fence).
        assert_eq!(range_rex(0, 0xDA00), None);
        assert_eq!(range_rex(0xDA00, 0xE000), None);
    }

    /// Deterministic LCG (Knuth's MMIX constants), independent of the
    /// differential harness's generator.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
    }

    /// A random legal Range: endpoints drawn from a pool mixing ASCII, the
    /// block edges, and beyond-BMP codes; retried until `range_rex`'s endpoint
    /// policy admits it (lo may be D800, hi may be DFFF, never interior).
    fn arb_range(g: &mut Lcg) -> Rex {
        const POOL: [u32; 8] = [
            0, 'a' as u32, 'z' as u32, 0xD7FF, 0xD800, 0xDFFF, 0xE000, MAX_CODE,
        ];
        loop {
            let a = POOL[(g.next() % 8) as usize];
            let b = POOL[(g.next() % 8) as usize];
            let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
            if let Some(r @ Rex::Range(..)) = range_rex(lo as i128, hi as i128) {
                return r;
            }
        }
    }

    /// A random CANONICAL Rex — built exclusively through the smart
    /// constructors, so the enum invariants hold by construction.
    fn arb_rex(g: &mut Lcg, depth: u32) -> Rex {
        if depth == 0 {
            return match g.next() % 3 {
                0 => Rex::Eps,
                1 => Rex::Empty,
                _ => arb_range(g),
            };
        }
        match g.next() % 7 {
            0 => arb_range(g),
            1 => concat(vec![arb_rex(g, depth - 1), arb_rex(g, depth - 1)]),
            2 => union(vec![arb_rex(g, depth - 1), arb_rex(g, depth - 1)]),
            3 => inter(vec![arb_rex(g, depth - 1), arb_rex(g, depth - 1)]),
            4 => star(arb_rex(g, depth - 1)),
            5 => comp(arb_rex(g, depth - 1)),
            _ => {
                let lo = (g.next() % 3) as u32;
                let hi = lo + 1 + (g.next() % 3) as u32;
                loop_(arb_rex(g, depth - 1), lo, hi)
            }
        }
    }

    #[test]
    fn roundtrip_extract_of_rex_to_term_is_identity() {
        // The slice's acceptance property: the term↔Rex round-trip is
        // SHAPE-stable (not merely language-preserving) for canonical Rex.
        let mut g = Lcg(0x5E_ED_25_5E_ED_25_01);
        let mut ctx = Context::new();
        for i in 0..500 {
            let r = arb_rex(&mut g, 4);
            let t = rex_to_term(&mut ctx, &r);
            assert_eq!(
                extract_const_regex(&ctx, t),
                Some(r.clone()),
                "round-trip changed shape at iter {i}: {r:?}"
            );
        }
    }

    #[test]
    fn straddling_range_consumer_shapes_survive_roundtrip() {
        // The two consumer misses from the spec's Root cause: head_forced and
        // the bare-Range ground-out both key on Rex SHAPE after extraction.
        let mut ctx = Context::new();
        // Bare straddling range: stays a bare Range (memb.rs's ground-out arm).
        let bare = Rex::Range('c' as u32, 0xE000);
        let t = rex_to_term(&mut ctx, &bare);
        let back = extract_const_regex(&ctx, t).unwrap();
        assert!(matches!(back, Rex::Range(..)), "got {back:?}");
        // Straddling Range·Σ*: stays head-forced (memb.rs's Rule-S arm).
        let shape = concat(vec![
            Rex::Range('c' as u32, MAX_CODE),
            star(Rex::Range(0, MAX_CODE)),
        ]);
        let t = rex_to_term(&mut ctx, &shape);
        let back = extract_const_regex(&ctx, t).unwrap();
        assert_eq!(
            head_forced(&back),
            Some((('c' as u32, MAX_CODE), star(Rex::Range(0, MAX_CODE))))
        );
    }

    // ── Task 1 (slice 28): language_empty — three-valued emptiness certificate

    #[test]
    fn language_empty_basic_shapes() {
        // ∅ is empty; ε and Σ* are non-empty (both nullable).
        assert!(matches!(language_empty(&Rex::Empty), Emptiness::Empty));
        assert!(matches!(language_empty(&Rex::Eps), Emptiness::NonEmpty));
        let sigma_star = Rex::Star(Box::new(Rex::Range(0, MAX_CODE)));
        assert!(matches!(language_empty(&sigma_star), Emptiness::NonEmpty));
    }

    #[test]
    fn language_empty_disjoint_infinite_tails() {
        // a·Σ* ∩ b·Σ* — first char must be both 'a' and 'b' ⇒ empty language.
        let sigma_star = Rex::Star(Box::new(Rex::Range(0, MAX_CODE)));
        let a_tail = concat(vec![Rex::Range('a' as u32, 'a' as u32), sigma_star.clone()]);
        let b_tail = concat(vec![Rex::Range('b' as u32, 'b' as u32), sigma_star]);
        let goal = inter(vec![a_tail, b_tail]);
        assert!(matches!(language_empty(&goal), Emptiness::Empty));
    }

    #[test]
    fn language_empty_r_inter_comp_r_is_empty() {
        // R ∩ comp(R) = ∅ — exercises the derivative over `Comp` and confirms
        // negative-polarity folding is decided empty.
        let sigma_star = Rex::Star(Box::new(Rex::Range(0, MAX_CODE)));
        let r = concat(vec![Rex::Range('a' as u32, 'a' as u32), sigma_star]);
        let goal = inter(vec![r.clone(), comp(r)]);
        assert!(matches!(language_empty(&goal), Emptiness::Empty));
    }

    #[test]
    fn language_empty_explores_surrogate_only_path() {
        // A single-surrogate range is NON-empty: `search_word` skips this class
        // (no Rust char), but a surrogate is a valid SMT-LIB code point, so the
        // emptiness certificate must EXPLORE it and report NonEmpty.
        let surr = Rex::Range(0xD800, 0xD800);
        assert!(matches!(language_empty(&surr), Emptiness::NonEmpty));
    }

    #[test]
    fn language_empty_class_split_overflow_taints_to_unknown() {
        // > CLASS_SPLIT_CAP (64) distinct, non-adjacent first-char classes ⇒
        // `next_classes` returns None ⇒ the traversal cannot complete ⇒ Unknown
        // (a taint, NOT a false Empty).
        let ranges: Vec<Rex> = (0u32..70).map(|i| Rex::Range(2 * i, 2 * i)).collect();
        let many = union(ranges);
        assert!(matches!(language_empty(&many), Emptiness::Unknown));
    }
}
