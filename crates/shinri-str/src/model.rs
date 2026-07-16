//! Model construction for the string theory (Task 17 + Task 19 overlay).
//!
//! On a SAT result the solver assembles a concrete `ModelVal::String(...)` for
//! each string-sorted term. The value of a term is assembled from its **deep
//! normal form** (the flattened concat of class representatives, preferring
//! string constants — see `normalize::deep_normal_form`):
//!
//! - **String-constant atoms** contribute their exact characters (this overlays
//!   constants pinned by `eq_true` normal forms, e.g. `x = "ab"` ⟹ value "ab",
//!   and assembles concat terms `x++y` from their operands' values).
//! - **Variable atoms** contribute a word of `FILL` (`'A'`) characters whose
//!   length is read from the arith model's `(str.len atom)`. These are the
//!   genuinely-free positions.
//!
//! The result is consistent: word-equation reasoning has already merged every
//! constrained variable with a constant or a concat of constants/vars, so the
//! deep normal form captures all pinned characters, and only truly-free length
//! is filled uniformly.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::types::ModelVal;
use shinri_theory::{EqualityEngine, ModelBuilder};

/// Read the length of term `t` from the model, via its `(str.len t)` term.
///
/// Builds `(str.len t)`, looks up `m.get(...)` for `ModelVal::Num(r)`.
/// Converts the rational to a non-negative `usize`; clamps negatives to 0.
/// Returns 0 if the length is absent from the model.
pub fn len_of_in_model(terms: &mut Context, m: &ModelBuilder, t: TermId) -> usize {
    let lt = terms
        .mk_app(Op::Builtin(BuiltinOp::StrLen), &[t])
        .expect("str.len application must succeed for a string-sorted term");
    match m.get(lt) {
        Some(ModelVal::Num(r)) => {
            // A str.len value is always a non-negative integer.
            // Extract numerator (denominator is 1 for integers); clamp negatives to 0.
            if r.is_negative() || r.is_zero() {
                0
            } else {
                // r is positive; denom = 1 for integer-valued rationals.
                // numer() returns Integer; use to_i128() -> Option<i128>.
                r.numer().to_i128().map(|v| v as usize).unwrap_or(0)
            }
        }
        _ => 0,
    }
}

/// Model length of `t`, consulting `t`'s EUF class: returns `len_of_in_model(t)`
/// if positive, else the max model length over the class members in `known` that
/// are EUF-equal to `t`. A derived concat term's own `(str.len …)` may be absent
/// from the arith model while an EUF-equal variable's is pinned, so the class read
/// recovers the true length (needed by the cycle-guard fallback).
fn class_len_in_model(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    m: &ModelBuilder,
    t: TermId,
) -> usize {
    let direct = len_of_in_model(terms, m, t);
    if direct > 0 {
        return direct;
    }
    let tn = eq.intern(t);
    let troot = eq.find(tn);
    let mut best = 0usize;
    for &k in known {
        let kn = eq.intern(k);
        if eq.find(kn) == troot {
            let n = len_of_in_model(terms, m, k);
            if n > best {
                best = n;
            }
        }
    }
    best
}

/// Assign each string term a concrete `ModelVal::String` value, assembling
/// compound (concat) terms from their operands and overlaying constant
/// characters pinned by the equality-engine normal forms.
///
/// `known` must contain every string-sorted term visible to the solver (so that
/// `deep_normal_form` can reflect merges with terms not syntactically inside
/// `t`, e.g. `x = "ab"` pins `x`'s value to "ab").
pub fn assign(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    str_terms: &[TermId],
    m: &mut ModelBuilder,
    seed: &FxHashMap<TermId, String>,
) {
    let mut memo: FxHashMap<TermId, String> = seed.clone();
    let mut in_progress: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();

    // Value concat terms FIRST: an anchored concat (e.g. `x++y = "ab"`) slices its
    // word among its operands and caches their values in `memo`, so a later direct
    // request for an operand returns the correct slice instead of a free fill.
    // (Without this ordering, an operand valued first as a free `FILL` word would
    // win the memo and the concat could not pin it — yielding a non-satisfying
    // witness.) Longer concats first, so a top-level concat slices before any
    // nested sub-concat is independently valued.
    let mut concats: Vec<TermId> = known
        .iter()
        .copied()
        .filter(|&t| is_concat(terms, t))
        .collect();
    concats.sort_by_key(|&t| std::cmp::Reverse(concat_arity(terms, t)));
    for t in concats {
        let _ = value_of(terms, eq, known, t, m, &mut memo, &mut in_progress);
    }

    for &t in str_terms {
        // Respect an existing *string* assignment, but OVERRIDE non-string
        // placeholders: EUF assigns string-sorted variables an opaque
        // `ModelVal::Elem(...)` (it treats String as an uninterpreted sort), which
        // must be replaced by the real string value here.
        if matches!(m.get(t), Some(ModelVal::String(_))) {
            continue;
        }
        let v = value_of(terms, eq, known, t, m, &mut memo, &mut in_progress);
        m.assign(t, ModelVal::String(v));
    }
}

/// Recursively compute the concrete string value of `t`.
///
/// Uses the deep normal form: each atom is either a string constant (contributes
/// its characters verbatim — this is the constant overlay / concat assembly) or a
/// variable (contributes `FILL × len(atom)`, the genuinely-free positions).
/// Memoized; an `in_progress` set guards against the (sound-model-impossible but
/// defensively handled) cycle of a variable normalising through itself.
fn value_of(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    t: TermId,
    m: &ModelBuilder,
    memo: &mut FxHashMap<TermId, String>,
    in_progress: &mut rustc_hash::FxHashSet<TermId>,
) -> String {
    if let Some(s) = memo.get(&t) {
        return s.clone();
    }
    // Direct string constant.
    if let Some(v) = terms.string_const_value(t) {
        let s = v.to_owned();
        memo.insert(t, s.clone());
        return s;
    }
    // Cycle guard: if we re-enter `t` while resolving it, fall back to a
    // length-filled free value (avoids infinite recursion on degenerate merges,
    // e.g. the self-referential `s1 = s0 ++ s1` with `s0 = ""`). Read the length
    // from `t`'s EUF class — `(str.len t)` itself may not be pinned in the arith
    // model when `t` is a derived concat, but an EUF-equal term (e.g. the variable
    // `s1`, whose `str.len` IS pinned) gives the correct class length. Using a bare
    // `len_of_in_model(t)` here returned 0 for such concats, producing an empty
    // word that violated an asserted `len ≥ k` (a wrong model / witness failure).
    if !in_progress.insert(t) {
        let n = class_len_in_model(terms, eq, known, m, t);
        return free_fill(eq, t, n);
    }

    // If `t` is itself a concat `a0 ++ a1 ++ …`, value it.
    if is_concat(terms, t) {
        let out = value_concat(terms, eq, known, t, m, memo, in_progress);
        in_progress.remove(&t);
        memo.insert(t, out.clone());
        return out;
    }

    // `t` is an opaque variable. Resolve it via its EUF class:
    //   1. a string constant in the class → its value (constant overlay);
    //   2. otherwise a CONCAT in the class → assemble/slice it (an F-split merged
    //      `t = "a"++z`, or `t` equals a concat anchored to a constant word);
    //   3. otherwise genuinely free → a per-class fill word of its model length.
    let class_const = class_member(terms, eq, known, t, |terms, mm| {
        terms.string_const_value(mm).is_some() && mm != t
    });
    let class_concat = class_member(terms, eq, known, t, |terms, mm| {
        is_concat(terms, mm) && mm != t
    });
    let out = match class_const.or(class_concat) {
        Some(rep) => {
            let v = value_of(terms, eq, known, rep, m, memo, in_progress);
            // Length-consistency guard for a variable resolved through a class
            // CONCAT (never a constant — a class constant IS the value). A concat
            // member may be a MINTED word-equation F-split remainder (e.g.
            // `s0 = s2 ++ !k`); in a cyclic merge (`s0 ≈ s2++!k`, `s2 ≈ s0++"cc"`)
            // the recursive value picks up the WRONG word length, producing a
            // witness that violates both the arith length model and the input word
            // equation `s2 = s0 ++ "cc"` (the F2 wrong-model class newly exercised
            // by the 7.5 length link's changed length trajectory). A genuine free
            // variable must take its arith-pinned length: if the concat-resolved
            // word's length disagrees with `t`'s class length, discard it for a
            // free fill of the correct length (a correct concat resolution matches
            // the length and is kept unchanged).
            if class_const.is_none() {
                let n = class_len_in_model(terms, eq, known, m, t);
                if v.chars().count() != n {
                    free_fill(eq, t, n)
                } else {
                    v
                }
            } else {
                v
            }
        }
        None => {
            let n = len_of_in_model(terms, m, t);
            free_fill(eq, t, n)
        }
    };
    in_progress.remove(&t);
    memo.insert(t, out.clone());
    out
}

/// Fill word for a genuinely-free variable: `n` copies of a character chosen
/// from the variable's EUF class root, so DISTINCT free classes receive DISTINCT
/// words (satisfying asserted disequalities like `x ≠ y` where both are free),
/// while equal variables (same class) get the same word. Falls back to cycling
/// the printable lowercase/uppercase range; collisions only past 52 distinct free
/// classes, which the differential corpus does not reach.
fn free_fill(eq: &mut EqualityEngine, t: TermId, n: usize) -> String {
    if n == 0 {
        return String::new();
    }
    let n_id = eq.intern(t);
    let root = eq.find(n_id);
    // Map the class root index onto a stable distinct character.
    const ALPHABET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
    let c = ALPHABET[root.index() % ALPHABET.len()] as char;
    std::iter::repeat_n(c, n).collect()
}

/// Value a concat term `c = a0 ++ a1 ++ …`.
///
/// If `c`'s EUF class is anchored to a concrete word `V` (a string constant in
/// the class), SLICE `V` among the operands using each operand's model length:
/// operand `ai` gets `V[off .. off+len(ai)]`. This is what produces a *satisfying*
/// witness for queries like `x ++ y = "ab"` with `len(x)=1` (→ x="a", y="b"):
/// word-equation search establishes the lengths and the constraint `c = "ab"`,
/// but may leave the individual operands un-pinned; slicing recovers them.
///
/// If `c` is NOT anchored to a constant, fall back to assembling it from the
/// operands' independently-resolved values.
fn value_concat(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    t: TermId,
    m: &ModelBuilder,
    memo: &mut FxHashMap<TermId, String>,
    in_progress: &mut rustc_hash::FxHashSet<TermId>,
) -> String {
    let kids: Vec<TermId> = match terms.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            args,
            ..
        } => terms.children(*args).to_vec(),
        _ => return String::new(),
    };
    // Is the whole concat anchored to a fixed word in its EUF class? Accept either
    // a string constant OR a concat whose operands are ALL constants (e.g.
    // `"ab"++"cc"`, which the asserted equality `"a"++s1 = "ab"++"cc"` leaves
    // unfolded) — the latter still denotes a fixed word and must anchor the slicing,
    // else the operands (`s1`) get a free fill that violates the equation (a wrong
    // model / witness failure).
    let anchor = class_member(terms, eq, known, t, |terms, mm| {
        const_word_of(terms, mm).is_some()
    })
    .and_then(|c| const_word_of(terms, c));

    if let Some(word) = anchor {
        let chars: Vec<char> = word.chars().collect();
        let mut off = 0usize;
        let mut out = String::new();
        let n_kids = kids.len();
        for (idx, &k) in kids.iter().enumerate() {
            // Resolve the operand's value if it is itself pinned (constant / class
            // constant / nested anchored concat); otherwise slice it out of `word`
            // by its model length.
            let pinned = resolve_pinned(terms, eq, known, k, m, memo, in_progress);
            let piece = match pinned {
                Some(v) => v,
                None => {
                    let len = if idx + 1 == n_kids {
                        // Last operand absorbs the remainder (robust to a missing
                        // length in the model).
                        chars.len().saturating_sub(off)
                    } else {
                        len_of_in_model(terms, m, k)
                    };
                    let end = (off + len).min(chars.len());
                    chars[off.min(chars.len())..end].iter().collect()
                }
            };
            off += piece.chars().count();
            // Cache the operand value so a later direct request returns the slice.
            memo.insert(k, piece.clone());
            out.push_str(&piece);
        }
        return out;
    }

    // Not anchored: assemble from operands' independent values.
    let mut out = String::new();
    for k in kids {
        out.push_str(&value_of(terms, eq, known, k, m, memo, in_progress));
    }
    out
}

/// If `k` is pinned to a definite value (a string constant, a class member that
/// is a constant, or a nested concat anchored to a constant), return it; else
/// `None` (meaning the caller should slice it out of the parent word).
fn resolve_pinned(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    k: TermId,
    m: &ModelBuilder,
    memo: &mut FxHashMap<TermId, String>,
    in_progress: &mut rustc_hash::FxHashSet<TermId>,
) -> Option<String> {
    if let Some(v) = memo.get(&k) {
        return Some(v.clone());
    }
    if let Some(v) = terms.string_const_value(k) {
        return Some(v.to_owned());
    }
    // A constant in k's class pins it.
    if let Some(c) = class_member(terms, eq, known, k, |terms, mm| {
        terms.string_const_value(mm).is_some() && mm != k
    }) {
        return terms.string_const_value(c).map(|s| s.to_owned());
    }
    // A nested concat anchored to a constant pins it.
    if is_concat(terms, k)
        && class_member(terms, eq, known, k, |terms, mm| {
            terms.string_const_value(mm).is_some()
        })
        .is_some()
    {
        return Some(value_of(terms, eq, known, k, m, memo, in_progress));
    }
    None
}

/// Find a member of `t`'s EUF equivalence class (drawn from `known`) satisfying
/// `pred`, or `None`. Used by the model builder to locate a constant or concat
/// representative for an otherwise-opaque variable.
fn class_member(
    terms: &Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    t: TermId,
    pred: impl Fn(&Context, TermId) -> bool,
) -> Option<TermId> {
    let tn = eq.intern(t);
    let troot = eq.find(tn);
    for &k in known {
        if !pred(terms, k) {
            continue;
        }
        let kn = eq.intern(k);
        if eq.find(kn) == troot {
            return Some(k);
        }
    }
    None
}

/// If `t` denotes a FIXED word — a string constant, or a `str.++` whose operands
/// all (recursively) denote fixed words — return that word. Otherwise `None`.
/// Used by `value_concat` to recognise an unfolded constant concat (e.g.
/// `"ab"++"cc"`) as a slicing anchor.
fn const_word_of(terms: &Context, t: TermId) -> Option<String> {
    if let Some(s) = terms.string_const_value(t) {
        return Some(s.to_owned());
    }
    match terms.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            args,
            ..
        } => {
            let kids = terms.children(*args).to_vec();
            let mut out = String::new();
            for k in kids {
                out.push_str(&const_word_of(terms, k)?);
            }
            Some(out)
        }
        _ => None,
    }
}

/// True iff `t` is a `str.++` application.
fn is_concat(terms: &Context, t: TermId) -> bool {
    matches!(
        terms.term_node(t),
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            ..
        }
    )
}

/// Number of direct operands of a concat (0 if not a concat).
fn concat_arity(terms: &Context, t: TermId) -> usize {
    match terms.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            args,
            ..
        } => terms.children(*args).len(),
        _ => 0,
    }
}

/// Slice 21: words for FREE string variables carrying membership atoms.
/// A variable is repair-eligible iff it is a leaf (nullary uninterpreted)
/// whose class holds no constant and no concat (the `value_of` free path) —
/// anything else has its value dictated elsewhere and repair would fight it.
/// The word: `search_word` over the intersection of all its (polarity-
/// adjusted) Rex constraints at the class's model length. No word / cap hit
/// / extraction failure ⇒ no seed (the post-solve self-check backstops).
pub(crate) fn memb_seeds(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    membs: &[(TermId, bool)],
    m: &ModelBuilder,
) -> FxHashMap<TermId, String> {
    use crate::regex;
    let mut per_var: FxHashMap<TermId, Vec<regex::Rex>> = FxHashMap::default();
    for &(atom, pos) in membs {
        let (t, re_t) = crate::memb::memb_sides(terms, atom);
        let is_leaf = matches!(
            terms.term_node(t),
            TermNode::App { op: Op::Uninterpreted(_), args, .. }
                if terms.children(*args).is_empty()
        );
        if !is_leaf {
            continue;
        }
        let Some(mut rex) = regex::extract_const_regex(terms, re_t) else {
            continue;
        };
        if !pos {
            rex = regex::comp(rex);
        }
        per_var.entry(t).or_default().push(rex);
    }
    let mut out = FxHashMap::default();
    for (v, rexes) in per_var {
        // Free check: no constant and no concat in v's class.
        let pinned = class_member(terms, eq, known, v, |terms, mm| {
            (terms.string_const_value(mm).is_some() || is_concat(terms, mm)) && mm != v
        });
        if pinned.is_some() {
            continue;
        }
        let n = class_len_in_model(terms, eq, known, m, v);
        let goal = regex::inter(rexes);
        // Try the model length first: `n` comes from the arith model, so it
        // respects every genuinely-asserted length pin. It can still fail —
        // a fully-free variable reads 0 here, and the slice-26 leaf axiom is
        // a LOWER bound only, so arith may pick any feasible length the goal
        // cannot realize (parity-constrained languages, arbitrary slack). On
        // failure fall back to the SHORTEST accepted word (slice 26 —
        // subsumes the slice-25 amendment-1 length-1 bump: a nullable goal
        // at n=0 still resolves to "" via `search_word`, a non-nullable one
        // falls through to its true minimal witness). Seeds are only ever
        // CANDIDATES re-checked by the post-solve self-check against every
        // assertion, so a fallback seed that violates a real length pin can
        // only fall back to the prior sound Unknown, never fabricate a
        // wrong Sat.
        if let Some(w) = regex::search_word(&goal, n).or_else(|| regex::search_shortest(&goal)) {
            out.insert(v, w);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::BuiltinOp;
    use shinri_theory::types::ModelVal;

    // ── Task 4 (slice 21): membership-aware seeding ──────────────────────

    #[test]
    fn memb_seed_replaces_free_fill() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let re_t = crate::regex::test_az_star_term(&mut ctx);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let mut m = ModelBuilder::default();
        // Arith pinned len(x) = 3.
        let len_x = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        m.assign(
            len_x,
            ModelVal::Num(shinri_core::Rational::from_int(3i128.into())),
        );
        let known = vec![x];
        let seeds = memb_seeds(&mut ctx, &mut eq, &known, &[(atom, true)], &m);
        let w = seeds.get(&x).expect("free membership var must be seeded");
        assert_eq!(w.chars().count(), 3);
        assert!(w.chars().all(|c| c.is_ascii_lowercase()));
        // A var pinned by a class CONSTANT must NOT be seeded (not free).
        let ab = ctx.mk_string_const("ab");
        let xa = eq.intern(x);
        let ca = eq.intern(ab);
        let _ = eq.merge(xa, ca, shinri_theory::types::EqJust::Definitional);
        let seeds2 = memb_seeds(&mut ctx, &mut eq, &[x, ab], &[(atom, true)], &m);
        assert!(seeds2.is_empty(), "constant-pinned var is not repaired");
    }

    // ── Task 4b (slice 25): witness search at length 1 for non-nullable
    // free leaves (bare wide / surrogate-straddling Range goals) ─────────

    #[test]
    fn memb_seed_wide_straddling_range_gets_length_one_witness() {
        // `s ∈ [c, U+E000]` — a bare Range straddling the surrogate block
        // (D800-DFFF) and far wider than ENUM_WORD_CAP (256), so it can never
        // fold to a word disjunction upstream. With NO independent length
        // constraint on `x`, the arith model has no `str.len x` entry, so
        // `class_len_in_model` reads 0. A bare Range is never nullable, so
        // `search_word(&goal, 0)` fails and (pre-fix) no seed is produced.
        // Pins the fix: `memb_seeds` must additionally try length 1.
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let re_rex = crate::regex::Rex::Range('c' as u32, 0xE000);
        let re_t = crate::regex::rex_to_term(&mut ctx, &re_rex);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let m = ModelBuilder::default(); // no len(x) pinned -> model length reads 0.
        let known = vec![x];
        let seeds = memb_seeds(&mut ctx, &mut eq, &known, &[(atom, true)], &m);
        let w = seeds
            .get(&x)
            .expect("non-nullable bare-range leaf must get a length-1 witness");
        assert_eq!(w.chars().count(), 1);
    }

    #[test]
    fn memb_seed_wide_range_over_256_gets_length_one_witness() {
        // Companion shape: a wide but non-straddling Range (> ENUM_WORD_CAP
        // words), e.g. "c".."<U+D000>" from the slice-25 spec. Same gap, same
        // fix.
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let re_rex = crate::regex::Rex::Range('c' as u32, 0xD000);
        let re_t = crate::regex::rex_to_term(&mut ctx, &re_rex);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let m = ModelBuilder::default();
        let known = vec![x];
        let seeds = memb_seeds(&mut ctx, &mut eq, &known, &[(atom, true)], &m);
        let w = seeds
            .get(&x)
            .expect("non-nullable bare-range leaf must get a length-1 witness");
        assert_eq!(w.chars().count(), 1);
    }

    #[test]
    fn memb_seed_nullable_goal_at_zero_length_unchanged() {
        // No-regression pin: when the goal IS nullable (e.g. `(re.* (re.range
        // "a" "z")))`), n=0 with no length constraint must still resolve to
        // the empty-string witness as before the fix — the length-1 bump
        // must only fire for NON-nullable goals.
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let re_t = crate::regex::test_az_star_term(&mut ctx);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let m = ModelBuilder::default(); // no len(x) pinned -> model length reads 0.
        let known = vec![x];
        let seeds = memb_seeds(&mut ctx, &mut eq, &known, &[(atom, true)], &m);
        let w = seeds
            .get(&x)
            .expect("nullable free membership var must be seeded at length 0");
        assert_eq!(w, "");
    }

    // ── Task 3 (slice 26): shortest-word fallback replaces the length-1
    // bump ──────────────────────────────────────────────────────────────

    #[test]
    fn memb_seed_min_len_two_goal_gets_shortest_witness() {
        // Slice 26: `x ∈ "b"·Σ·Σ*` (the strict-< proper-prefix gadget arm)
        // over a fully-free leaf — no length constraint, so the model length
        // reads 0 and `search_word(goal, 0)` fails (non-nullable). The
        // shortest-word fallback must produce a length-2 member. Subsumes
        // the slice-25 amendment-1 length-1 bump (whose pins stay green).
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let sigma = crate::regex::Rex::Range(0, crate::regex::MAX_CODE);
        let goal = crate::regex::concat(vec![
            crate::regex::Rex::Range('b' as u32, 'b' as u32),
            sigma.clone(),
            crate::regex::star(sigma),
        ]);
        let re_t = crate::regex::rex_to_term(&mut ctx, &goal);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let m = ModelBuilder::default(); // no len(x) pinned -> model length 0.
        let known = vec![x];
        let seeds = memb_seeds(&mut ctx, &mut eq, &known, &[(atom, true)], &m);
        let w = seeds
            .get(&x)
            .expect("min-len-2 star-tail leaf must get a shortest witness");
        assert_eq!(w.chars().count(), 2);
        assert_eq!(crate::regex::eval_membership(w, &goal), Some(true));
    }

    #[test]
    fn memb_seed_union_easy_arm_gets_witness() {
        // Slice 26: `x ∈ (bc·Σ* ∪ "q")` — the union-poisoning probe cell.
        // The shortest-word fallback finds the trivially-sat length-1 arm.
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let sigma_star = crate::regex::star(crate::regex::Rex::Range(0, crate::regex::MAX_CODE));
        let goal = crate::regex::union(vec![
            crate::regex::concat(vec![
                crate::regex::Rex::Range('b' as u32, 'b' as u32),
                crate::regex::Rex::Range('c' as u32, 'c' as u32),
                sigma_star,
            ]),
            crate::regex::Rex::Range('q' as u32, 'q' as u32),
        ]);
        let re_t = crate::regex::rex_to_term(&mut ctx, &goal);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[x, re_t])
            .unwrap();
        let mut eq = EqualityEngine::default();
        let m = ModelBuilder::default();
        let known = vec![x];
        let seeds = memb_seeds(&mut ctx, &mut eq, &known, &[(atom, true)], &m);
        assert_eq!(seeds.get(&x).map(String::as_str), Some("q"));
    }
}
