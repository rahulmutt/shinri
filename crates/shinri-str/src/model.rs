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

use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use rustc_hash::FxHashMap;
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
                r.numer()
                    .to_i128()
                    .map(|v| v as usize)
                    .unwrap_or(0)
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
) {
    let mut memo: FxHashMap<TermId, String> = FxHashMap::default();
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
    let resolved = class_const.or_else(|| {
        class_member(terms, eq, known, t, |terms, mm| is_concat(terms, mm) && mm != t)
    });
    let out = match resolved {
        Some(rep) => value_of(terms, eq, known, rep, m, memo, in_progress),
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
    std::iter::repeat(c).take(n).collect()
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
        TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), args, .. } => {
            terms.children(*args).to_vec()
        }
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
        TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), args, .. } => {
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
        TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), .. }
    )
}

/// Number of direct operands of a concat (0 if not a concat).
fn concat_arity(terms: &Context, t: TermId) -> usize {
    match terms.term_node(t) {
        TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), args, .. } => {
            terms.children(*args).len()
        }
        _ => 0,
    }
}
