use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, TermNode};
use shinri_theory::types::EqLeaf;
use shinri_theory::EqualityEngine;

pub enum StepResult {
    Done,
    /// The word equation has a variable-headed residual whose F-split was ALREADY
    /// emitted (dedup hit) — the search is saturated WITHOUT having ground-resolved
    /// the equation. The caller must NOT conclude SAT from this state (the model
    /// builder cannot reliably realise the chained F-split merges into a satisfying
    /// witness — the (B′) premature-SAT hazard), and instead returns a SOUND
    /// `Unknown`. Distinct from `Done` (which means trivially resolved / consumed).
    Saturated,
    Conflict(Vec<EqLeaf>),
    /// A GUARDED F-split. `atoms` are the fresh-positive disjuncts
    /// `[len_eq, a_pref, b_pref]`; `guard` is the NEGATION of the triggering
    /// word-equation literal. The learnt clause is `guard ∨ len_eq ∨ a_pref ∨
    /// b_pref` ≡ `eqn → (len_eq ∨ a_pref ∨ b_pref)` — the sound Nielsen lemma.
    Split {
        atoms: Vec<TermId>,
        guard: Lit,
    },
}

/// Mint a fresh string constant `!strk<N>` and return its term ID.
pub fn fresh_str(terms: &mut Context, ctr: &mut u32) -> TermId {
    let name = format!("!strk{}", *ctr);
    *ctr += 1;
    let str_s = terms.string_sort();
    let sym = terms.declare_fun(&name, &[], str_s);
    terms
        .mk_app(Op::Uninterpreted(sym), &[])
        .expect("well-sorted")
}

/// Build `(str.len t)`.
pub fn len_of(terms: &mut Context, t: TermId) -> TermId {
    terms
        .mk_app(Op::Builtin(BuiltinOp::StrLen), &[t])
        .expect("well-sorted")
}

/// Build the three F-split atoms for heads `a`, `b` (at least one a variable).
///
/// Returns `[len_eq, a_pref, b_pref]` where:
///   `len_eq`  = `(= (str.len a) (str.len b))`
///   `a_pref`  = `(= a (str.++ b z1))`   for a fresh remainder `z1`
///   `b_pref`  = `(= b (str.++ a z2))`   for a fresh remainder `z2`
///
/// Soundness: the disjunction `len_eq ∨ a_pref ∨ b_pref` is valid over string
/// algebra ONLY GIVEN the triggering word equation (Nielsen transformation: if
/// two words starting with `a` resp. `b` are equal, one head is a prefix of the
/// other or they have equal length). It is NOT a tautology: a="xy", b="z" makes
/// all three disjuncts false. Therefore the caller MUST guard the learnt clause
/// with `¬eqn` (the negation of the asserted word equation), turning it into the
/// VALID implication `eqn → (len_eq ∨ a_pref ∨ b_pref)`. Without the guard the
/// clause is a non-entailed permanent learnt clause and causes spurious UNSAT
/// (it would forbid e.g. x="xy" on EVERY branch). The fresh z1/z2 are existential
/// witnesses under that implication.
pub fn fsplit_atoms(terms: &mut Context, a: TermId, b: TermId, ctr: &mut u32) -> Vec<TermId> {
    let la = len_of(terms, a);
    let lb = len_of(terms, b);
    let len_eq = terms.mk_eq(la, lb).expect("well-sorted");
    let z1 = fresh_str(terms, ctr);
    let bc = terms
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[b, z1])
        .expect("well-sorted");
    let a_pref = terms.mk_eq(a, bc).expect("well-sorted");
    let z2 = fresh_str(terms, ctr);
    let ac = terms
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, z2])
        .expect("well-sorted");
    let b_pref = terms.mk_eq(b, ac).expect("well-sorted");
    vec![len_eq, a_pref, b_pref]
}

/// Returns the two children of an `Eq` atom.
pub fn sides(terms: &Context, atom: TermId) -> (TermId, TermId) {
    match terms.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Eq),
            args,
            ..
        } => {
            let ch = terms.children(*args);
            (ch[0], ch[1])
        }
        _ => panic!("sides: expected Eq atom"),
    }
}

/// Returns the two children of a disequality atom (either `Eq` or `Distinct`).
///
/// A disequality is represented either as a positive `(distinct s t)` atom or as
/// the proposition of a negative `(= s t)` literal. Both forms have their two
/// string-sorted operands as the first two children.
pub fn diseq_sides(terms: &Context, atom: TermId) -> (TermId, TermId) {
    match terms.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct),
            args,
            ..
        } => {
            let ch = terms.children(*args);
            (ch[0], ch[1])
        }
        _ => panic!("diseq_sides: expected Eq or Distinct atom"),
    }
}

/// True iff the two normal forms are atom-wise equal (definitely the same word).
///
/// "Equal" here means each positional pair satisfies `same()`: same TermId, same
/// string literal value, or same EqualityEngine equivalence class. Returns `false`
/// immediately if the lengths differ.
pub fn nf_equal(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    lhs: &[TermId],
    rhs: &[TermId],
) -> bool {
    if lhs.len() != rhs.len() {
        return false;
    }
    lhs.iter().zip(rhs).all(|(&a, &b)| same(terms, eq, a, b))
}

/// Build the EqLeaf conflict justification explaining WHY `lhs` and `rhs` are
/// atom-wise equal. Must be called only after `nf_equal` returned `true`.
///
/// For each positional pair `(a, b)` that is NOT the same TermId but is in the
/// same EqualityEngine class, calls `eq.explain(an, bn, out)` to gather the
/// asserted-equality antecedents that caused the merge. Pairs with `a == b`
/// contribute no leaves (trivially equal; no merge was needed).
pub fn nf_equal_explain(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    lhs: &[TermId],
    rhs: &[TermId],
    out: &mut Vec<EqLeaf>,
) {
    debug_assert_eq!(lhs.len(), rhs.len(), "nf_equal_explain: mismatched lengths");
    for (&a, &b) in lhs.iter().zip(rhs) {
        if a == b {
            continue; // trivially equal; no EUF merge involved
        }
        // Literal-value equality: both string constants with the same value.
        if let (Some(sa), Some(sb)) = (terms.string_const_value(a), terms.string_const_value(b)) {
            if sa == sb {
                continue; // same constant value, different TermIds — no merge antecedent
            }
        }
        // EUF equality: explain the merge path.
        let an = eq.intern(a);
        let bn = eq.intern(b);
        if eq.are_equal(an, bn) {
            eq.explain(an, bn, out);
        }
    }
}

/// Occurs-check helper for `resolve_equation`. Returns `true` iff a single
/// variable `single` cannot equal the word `rest` because `rest` contains an
/// occurrence of `single` PLUS at least one NON-EMPTY string CONSTANT — i.e.
/// `len(single) = len(single) + (>0)`, impossible.
///
/// SOUNDNESS (free-monoid emptiness): in the free monoid `Σ*` every string
/// variable can take the EMPTY word `ε`. So a second VARIABLE occurrence (the
/// same `single` again, or any other distinct variable) is NOT necessarily
/// non-empty — it can be `ε`, contributing length 0. The ONLY syntactic atom
/// that is GUARANTEED to contribute strictly positive length is a non-empty
/// string CONSTANT. Therefore the equation `single = …single…X…` (with `X` the
/// surrounding material) forces `len(single) = len(single) + len(X)`, i.e.
/// `len(X) = 0`, which is a contradiction ONLY when `X` is forced to be
/// non-empty — and that happens iff some atom of `rest` is a non-empty constant.
/// A second variable / second `single` occurrence is satisfiable via emptiness
/// (e.g. `v = w v u` with `w=u=v=ε`, or `v = u v u` with `u=ε`), so it must NOT
/// conflict here; it falls through to the normal F-split/Done machinery.
fn occurs_unsat(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    single: TermId,
    rest: &[TermId],
) -> bool {
    let same_as_single = |eq: &mut EqualityEngine, a: TermId| -> bool {
        a == single || {
            let an = eq.intern(a);
            let sn = eq.intern(single);
            eq.are_equal(an, sn)
        }
    };
    // `rest` must contain `single` again.
    let mut contains = false;
    for &a in rest {
        if same_as_single(eq, a) {
            contains = true;
            break;
        }
    }
    if !contains {
        return false;
    }
    // … PLUS at least one NON-EMPTY string constant. Only a non-empty constant is
    // necessarily non-empty material; a second variable (or a second occurrence
    // of `single`) can be ε and so does NOT force a length contradiction.
    rest.iter()
        .any(|&a| terms.string_const_value(a).is_some_and(|s| !s.is_empty()))
}

/// Compare two atoms for definite equality: same TermId, same literal string
/// value, or same EqualityEngine equivalence class.
pub(crate) fn same(terms: &mut Context, eq: &mut EqualityEngine, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    if let (Some(x), Some(y)) = (terms.string_const_value(a), terms.string_const_value(b)) {
        return x == y;
    }
    let an = eq.intern(a);
    let bn = eq.intern(b);
    eq.are_equal(an, bn)
}

/// Resolve one word equation between two normal forms.
///
/// A single-level `normal_form` can leave a CONCAT atom in a word — an unflattened
/// concat CLASS REPRESENTATIVE that a merge substituted for a variable (e.g.
/// `rep(s1) = !sfx ++ "cb"` after `s1 = !sfx ++ "cb"`). This wrapper:
///
/// 1. Structurally FLATTENS those concat atoms (`X ++ Y` denotes `[X, Y]` — a
///    sound identity needing no antecedent) so the head/tail strip and F-split
///    operate on the real word rather than treating the opaque concat as a fresh
///    variable head. Without this, the opaque-concat head is re-split with a fresh
///    minted concat every round — the F1 divergence whose Nielsen clause, guarded
///    only by `¬eqn`, drove a spurious UNSAT.
/// 2. If a concat atom WAS flattened and the inner resolver reports a CONFLICT,
///    downgrades it to `Saturated` (→ a sound Unknown / witness-checked SAT). Such
///    a conflict is derived from constant/structure surfaced by the merge-driven
///    substitution, yet `resolve_inner` cites only the word-equation literal — an
///    under-cited (unsound) global exclusion. Suppressing exactly these conflicts
///    keeps the single-level regime sound WITHOUT threading merge antecedents (a
///    citation that over-approximates and trips the SAT conflict-analyzability
///    guard). Purely structural conflicts on words that had NO concat atom are
///    unaffected — every b10bd27 constant-length exemplar still Conflicts.
#[allow(clippy::too_many_arguments)]
pub fn resolve_equation(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    lhs: &[TermId],
    rhs: &[TermId],
    just: Vec<EqLeaf>,
    eqn_lit: Lit,
    fresh_ctr: &mut u32,
    emitted: &mut FxHashSet<(TermId, TermId)>,
) -> StepResult {
    let is_concat = |t: TermId| {
        matches!(
            terms.term_node(t),
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrConcat),
                ..
            }
        )
    };
    let had_concat_atom = lhs.iter().chain(rhs.iter()).copied().any(is_concat);
    if !had_concat_atom {
        return resolve_inner(terms, eq, lhs, rhs, just, eqn_lit, fresh_ctr, emitted);
    }
    let lhs_flat = flatten_concat_atoms(terms, lhs);
    let rhs_flat = flatten_concat_atoms(terms, rhs);
    match resolve_inner(
        terms, eq, &lhs_flat, &rhs_flat, just, eqn_lit, fresh_ctr, emitted,
    ) {
        // A conflict off a flattened concat rep would be under-cited → Saturate.
        StepResult::Conflict(_) => StepResult::Saturated,
        other => other,
    }
}

/// Structural flatten: expand every `str.++` atom of `word` into its operands
/// (recursively). `X ++ Y` denotes the sequence `[X, Y]` by definition, so this
/// is sound and needs no equality antecedent.
fn flatten_concat_atoms(terms: &Context, word: &[TermId]) -> Vec<TermId> {
    fn go(terms: &Context, t: TermId, out: &mut Vec<TermId>) {
        match terms.term_node(t) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrConcat),
                args,
                ..
            } => {
                let kids: Vec<TermId> = terms.children(*args).to_vec();
                for k in kids {
                    go(terms, k, out);
                }
            }
            _ => out.push(t),
        }
    }
    let mut out = Vec::with_capacity(word.len());
    for &a in word {
        go(terms, a, &mut out);
    }
    out
}

/// Inner resolver over ALREADY-FLATTENED words (no concat atoms among the heads
/// except any the caller deliberately left). See [`resolve_equation`] for the
/// flattening/conflict-suppression wrapper.
///
/// - Strips equal leading and trailing atoms (sound cancellation in free monoid).
/// - If both sides are fully consumed after stripping → Done (trivially satisfied).
/// - If both sides have constant heads whose first characters differ → Conflict.
/// - If one side is empty and the other still contains a non-empty constant → Conflict.
/// - If the residual has a variable head and the pair has not been split yet →
///   emits an F-split (three-disjunct length-aware alignment).
/// - If the pair was already split (dedup) → Saturated (wait for SAT to case-split).
///
/// `fresh_ctr` is used to mint fresh string variables for the split remainders.
/// `emitted` deduplicates splits to prevent re-emitting the same pair (termination).
/// `eqn_lit` is the literal that asserted this word equation (positive). The
/// F-split it may emit is GUARDED with `eqn_lit.negate()` so the learnt clause is
/// the valid implication `eqn → (len_eq ∨ a_pref ∨ b_pref)`, never the unsound
/// bare disjunction.
#[allow(clippy::too_many_arguments)]
fn resolve_inner(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    lhs: &[TermId],
    rhs: &[TermId],
    just: Vec<EqLeaf>,
    eqn_lit: Lit,
    fresh_ctr: &mut u32,
    emitted: &mut FxHashSet<(TermId, TermId)>,
) -> StepResult {
    let (mut i, mut j) = (0usize, 0usize);
    let (mut le, mut re) = (lhs.len(), rhs.len());

    // Strip equal heads.
    while i < le && j < re && same(terms, eq, lhs[i], rhs[j]) {
        i += 1;
        j += 1;
    }

    // Strip equal tails.
    while le > i && re > j && same(terms, eq, lhs[le - 1], rhs[re - 1]) {
        le -= 1;
        re -= 1;
    }

    // Both exhausted: equation holds trivially.
    if i == le && j == re {
        return StepResult::Done;
    }

    // OCCURS CHECK (length-based contradiction in the free monoid). If one side
    // is the SINGLE variable `v` and the residual of the other side both
    //   (a) contains an occurrence of `v` (same TermId / same EUF class), and
    //   (b) contains a NON-EMPTY string CONSTANT,
    // then `v = …v… + nonempty-const + …` forces `len(v) = len(v) + (>0)`, which
    // is impossible. This is UNSAT. It is the decidable length-contradiction core
    // of variable-headed word equations such as `s = "b" ++ t ++ s ++ "c"`, which
    // the pure F-split would otherwise diverge on (→ Unknown) or wrongly call SAT.
    //
    // SOUNDNESS: a SECOND VARIABLE (a distinct variable, or a second occurrence of
    // `v` itself) is NOT necessarily non-empty — in the free monoid any variable
    // can be ε. So cases like `v = w ++ v ++ u` (w=u=v=ε) and `v = u ++ v ++ u`
    // (u=ε) are SAT and must NOT conflict here; without a non-empty constant the
    // occurs-check returns false and the equation falls through to the F-split/Done
    // machinery (which splits or saturates → Unknown — never wrong UNSAT/SAT).
    {
        if le - i == 1
            && terms.string_const_value(lhs[i]).is_none()
            && occurs_unsat(terms, eq, lhs[i], &rhs[j..re])
        {
            return StepResult::Conflict(just);
        }
        if re - j == 1
            && terms.string_const_value(rhs[j]).is_none()
            && occurs_unsat(terms, eq, rhs[j], &lhs[i..le])
        {
            return StepResult::Conflict(just);
        }
    }

    // E1 PROBE: single-variable side not occurring in the other → Done.
    // If one residual is EXACTLY one variable atom `v` and `v` does not occur
    // (same TermId / same EUF class) anywhere in the other residual, the equation
    // is a pure assignment `v = W` (v ∉ W), trivially satisfiable by v := W. The
    // EUF merge already records v ≈ W; the model builder assembles v from W. There
    // is NOTHING to align, so emitting a char-peel / F-split here is spurious: it
    // mints a `v = ""` disjunct that (asserted false) becomes a `v ≠ ""` diseq
    // driving the non-empty separation lemma, and (asserted true) drives a length
    // link — three interlocking length lemmas whose CDCL interaction manufactures a
    // false `len(v) ≤ 0` unit (the t8iter175 wrong-UNSAT). Returning Done avoids it.
    {
        let occurs_in = |eq: &mut EqualityEngine, v: TermId, w: &[TermId]| -> bool {
            w.iter().any(|&a| {
                a == v || {
                    let an = eq.intern(a);
                    let vn = eq.intern(v);
                    eq.are_equal(an, vn)
                }
            })
        };
        if le - i == 1 && terms.string_const_value(lhs[i]).is_none() && !occurs_in(eq, lhs[i], &rhs[j..re]) {
            return StepResult::Done;
        }
        if re - j == 1 && terms.string_const_value(rhs[j]).is_none() && !occurs_in(eq, rhs[j], &lhs[i..le]) {
            return StepResult::Done;
        }
    }

    // Both residuals fully constant: compare the concatenated words. When neither
    // residual contains a variable, each side denotes a FIXED word; if those words
    // differ (including the case where one is a proper prefix of the other, e.g.
    // `"b" = "ba"` after stripping a common prefix), the equation is UNSAT in the
    // free monoid. The head-char walk below catches a differing character but NOT a
    // length difference with a common prefix (`"b"` vs `"ba"`), so handle the
    // all-constant case explicitly here.
    {
        let all_const = |sl: &[TermId], terms: &Context| {
            sl.iter().all(|&a| terms.string_const_value(a).is_some())
        };
        if all_const(&lhs[i..le], terms) && all_const(&rhs[j..re], terms) {
            let cat = |sl: &[TermId], terms: &Context| -> String {
                sl.iter()
                    .map(|&a| terms.string_const_value(a).unwrap().to_owned())
                    .collect()
            };
            if cat(&lhs[i..le], terms) != cat(&rhs[j..re], terms) {
                return StepResult::Conflict(just);
            }
        }

        // Constant-length bound: a FULLY-CONSTANT residual has an EXACT length; the
        // other residual has a MINIMUM length = the sum of its string-constant atoms'
        // char counts (variables are ≥ 0). If the exact length of a fully-constant
        // side is STRICTLY LESS than the other side's minimum length, the equation is
        // UNSAT in the free monoid — the constant side is too short to ever hold the
        // other side's mandatory constant characters. This catches e.g.
        // `s2++"ba" = "b"` (RHS exact 1 < LHS min 2 ⟹ UNSAT), which the single-level
        // word-equation resolver otherwise leaves SAT (its NF does not expand the
        // `s2 = "b"++z` merge the char-peel split mints). No fresh terms are created,
        // so unlike a per-equation length lemma it cannot flood the String↔Arith seam.
        {
            let const_chars = |a: TermId, terms: &Context| -> usize {
                terms.string_const_value(a).map_or(0, |s| s.chars().count())
            };
            let min_len = |sl: &[TermId], terms: &Context| -> usize {
                sl.iter().map(|&a| const_chars(a, terms)).sum()
            };
            let l_res = &lhs[i..le];
            let r_res = &rhs[j..re];
            let l_all_const = all_const(l_res, terms);
            let r_all_const = all_const(r_res, terms);
            let l_min = min_len(l_res, terms);
            let r_min = min_len(r_res, terms);
            // A fully-constant side has exact length == its min_len.
            if (l_all_const && l_min < r_min) || (r_all_const && r_min < l_min) {
                return StepResult::Conflict(just);
            }

            // Character-set containment: when ONE side is fully constant, its word
            // fixes the entire alphabet of the equal word, so every character of any
            // CONSTANT atom on the other side must occur in that fixed word. If a
            // constant atom on the variable side uses a character absent from the
            // fully-constant side, the equation is UNSAT in the free monoid (e.g.
            // `s1 ++ "cc" ++ s2 = "bbb"`: 'c' ∉ {b} ⟹ UNSAT). Sound and needs no
            // fresh terms; it catches a class of premature-SAT word equations the
            // F-split fixpoint would otherwise dedup-terminate as (wrongly) SAT.
            let char_set =
                |sl: &[TermId], terms: &Context| -> Option<std::collections::BTreeSet<char>> {
                    if !all_const(sl, terms) {
                        return None;
                    }
                    let mut s = std::collections::BTreeSet::new();
                    for &a in sl {
                        for c in terms.string_const_value(a).unwrap().chars() {
                            s.insert(c);
                        }
                    }
                    Some(s)
                };
            let other_const_chars_subset = |fixed: &std::collections::BTreeSet<char>,
                                            other: &[TermId],
                                            terms: &Context|
             -> bool {
                for &a in other {
                    if let Some(cs) = terms.string_const_value(a) {
                        if cs.chars().any(|c| !fixed.contains(&c)) {
                            return false;
                        }
                    }
                }
                true
            };
            if let Some(lset) = char_set(l_res, terms) {
                if !other_const_chars_subset(&lset, r_res, terms) {
                    return StepResult::Conflict(just);
                }
            }
            if let Some(rset) = char_set(r_res, terms) {
                if !other_const_chars_subset(&rset, l_res, terms) {
                    return StepResult::Conflict(just);
                }
            }
        }
    }

    // Both sides non-empty: check for constant-head character mismatch.
    // When both heads are string constants, strip the longest common character
    // prefix. If after stripping both have remaining characters with different
    // first chars, it is a genuine contradiction in the free monoid.
    if i < le && j < re {
        if let (Some(a_str), Some(b_str)) = (
            terms.string_const_value(lhs[i]).map(str::to_owned),
            terms.string_const_value(rhs[j]).map(str::to_owned),
        ) {
            // Walk character by character to find the first mismatch.
            let mut a_chars = a_str.chars();
            let mut b_chars = b_str.chars();
            loop {
                match (a_chars.next(), b_chars.next()) {
                    (Some(ca), Some(cb)) if ca != cb => {
                        return StepResult::Conflict(just);
                    }
                    (Some(_), Some(_)) => {} // common prefix char, keep walking
                    // One constant is a prefix of the other or they are equal;
                    // cannot determine a conflict here without knowing what follows.
                    // Fall through to the variable-head case.
                    _ => break,
                }
            }
        }
    }

    // One side empty, other has a non-empty constant remaining: contradiction.
    if (i == le) != (j == re) {
        let rest = if i == le { &rhs[j..re] } else { &lhs[i..le] };
        if rest
            .iter()
            .any(|&a| terms.string_const_value(a).is_some_and(|s| !s.is_empty()))
        {
            return StepResult::Conflict(just);
        }
    }

    // Residual has at least one variable head: check for var-vs-nonempty-constant
    // before falling through to the generic F-split. When one head is a variable
    // and the other is a non-empty constant with known first character `ch`, emit
    // the two-way split:
    //   `(= v "")` ∨ `(= v ("ch" ++ z))`
    // This is the Nielsen character-peel lemma for the constant-head case: given
    // the triggering word equation, the variable head is either empty or begins
    // with the known constant character. The split is GUARDED with `¬eqn` so the
    // learnt clause is `¬eqn ∨ (= v "") ∨ (= v ("ch" ++ z))` ≡
    // `eqn → (v="" ∨ v="ch"++z)`, which IS valid given the words are equal.
    if i < le && j < re {
        let (ha, hb) = (lhs[i], rhs[j]);
        // Identify the (variable, nonempty-constant) pair, if any.
        let vc_pair: Option<(TermId, TermId)> =
            match (terms.string_const_value(ha), terms.string_const_value(hb)) {
                (None, Some(s)) if !s.is_empty() => Some((ha, hb)),
                (Some(s), None) if !s.is_empty() => Some((hb, ha)),
                _ => None,
            };
        if let Some((var, cst)) = vc_pair {
            // Extract first character of the constant (guaranteed non-empty above by
            // the `!s.is_empty()` guard in the match arm that produced `vc_pair`).
            let cs = terms.string_const_value(cst).unwrap().to_owned();
            let ch = cs
                .chars()
                .next()
                .expect("non-empty constant by construction");
            // Canonical dedup key: order by index to be unordered.
            let key = if var.index() <= cst.index() {
                (var, cst)
            } else {
                (cst, var)
            };
            if emitted.insert(key) {
                // v = ""
                let empty = terms.mk_string_const("");
                let v_empty = terms.mk_eq(var, empty).expect("well-sorted");
                // v = "ch" ++ z
                let head = terms.mk_string_const(&ch.to_string());
                let z = fresh_str(terms, fresh_ctr);
                let hz = terms
                    .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[head, z])
                    .expect("well-sorted");
                let v_head = terms.mk_eq(var, hz).expect("well-sorted");
                // GUARD with ¬eqn: the disjunction `v="" ∨ v="ch"++z` is valid
                // ONLY given the triggering word equation. Without the guard this
                // would be a non-entailed permanent learnt clause causing spurious
                // UNSAT (e.g. v="xy", c="b": neither disjunct holds, so the bare
                // clause would make {v="xy"} UNSAT). The guard turns it into the
                // valid implication `eqn → (v="" ∨ v="ch"++z)`.
                return StepResult::Split {
                    atoms: vec![v_empty, v_head],
                    guard: eqn_lit.negate(),
                };
            }
            // Already split this pair; the search is saturated without resolution.
            return StepResult::Saturated;
        }
    }

    // Residual has at least one variable head: emit a generic F-split if not yet emitted.
    if i < le && j < re {
        let (ha, hb) = (lhs[i], rhs[j]);
        let var_head =
            terms.string_const_value(ha).is_none() || terms.string_const_value(hb).is_none();
        if var_head {
            // Canonical (unordered) key for dedup.
            let key = if ha.index() <= hb.index() {
                (ha, hb)
            } else {
                (hb, ha)
            };
            if emitted.insert(key) {
                let atoms = fsplit_atoms(terms, ha, hb, fresh_ctr);
                // GUARD with ¬eqn: the learnt clause is `¬eqn ∨ len_eq ∨ a_pref ∨
                // b_pref` ≡ `eqn → (len_eq ∨ a_pref ∨ b_pref)`, the valid Nielsen
                // lemma. On branches where the equation is false, ¬eqn satisfies
                // the clause and the head variable is unconstrained — no spurious
                // UNSAT.
                return StepResult::Split {
                    atoms,
                    guard: eqn_lit.negate(),
                };
            }
            // Already split this pair; the search is saturated without resolution.
            return StepResult::Saturated;
        }
    }

    StepResult::Done
}

#[cfg(test)]
mod tests {
    use crate::wordeq::{resolve_equation, StepResult};
    use crate::StrSolver;
    use rustc_hash::FxHashSet;
    use shinri_core::{BuiltinOp, Context, Lit, Op, TermNode, Var};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    /// A dummy positive equation literal for `resolve_equation` calls whose guard
    /// is not under test.
    fn dummy_eqn_lit() -> Lit {
        Lit::new(Var::new(0), true)
    }

    // Helper: make a string variable term in `ctx`.
    fn mk_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let str_s = ctx.string_sort();
        let s = ctx.declare_fun(name, &[], str_s);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    // ── Non-conflict case 1: prefix-of-constant ───────────────────────────────
    // Normal forms: lhs = ["ab", X],  rhs = ["abc", Y]
    // After stripping: both heads are constants "ab" vs "abc".
    // "ab" is a proper prefix of "abc" — no character mismatch, just one is
    // shorter.  This is satisfiable (X = "c" ++ Y), so resolve_equation MUST
    // return Done (constant heads → no F-split needed), not Conflict.
    #[test]
    fn prefix_of_constant_is_done_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = mk_var(&mut ctx, "x_pfx");
        let y = mk_var(&mut ctx, "y_pfx");
        let ab = ctx.mk_string_const("ab");
        let abc = ctx.mk_string_const("abc");
        let lhs = [ab, x];
        let rhs = [abc, y];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let result = resolve_equation(
            &mut ctx,
            &mut eq,
            &lhs,
            &rhs,
            vec![],
            dummy_eqn_lit(),
            &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(result, StepResult::Done),
            "prefix-of-constant residual must be Done (satisfiable: X = \"c\" ++ Y)"
        );
    }

    // ── Non-conflict case 2: variable head ───────────────────────────────────
    // Normal forms: lhs = [X, "a"],  rhs = ["b", Y]
    // After stripping: lhs head is variable X — emits an F-split on the first
    // call, then Done on the second (dedup prevents re-emission).
    #[test]
    fn variable_head_is_done_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = mk_var(&mut ctx, "x_vh");
        let y = mk_var(&mut ctx, "y_vh");
        let a = ctx.mk_string_const("a");
        let b = ctx.mk_string_const("b");
        let lhs = [x, a];
        let rhs = [b, y];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        // First call: emits F-split (not Conflict).
        let result = resolve_equation(
            &mut ctx,
            &mut eq,
            &lhs,
            &rhs,
            vec![],
            dummy_eqn_lit(),
            &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(result, StepResult::Split { .. } | StepResult::Done),
            "variable-headed residual must NOT be Conflict (X could equal \"b\" ++ ...)"
        );
        assert!(
            !matches!(result, StepResult::Conflict(_)),
            "variable-headed residual must NOT be Conflict"
        );
    }

    // ── Non-conflict case 3: both sides fully consumed after strip ────────────
    // Normal forms: lhs = [X, "a"],  rhs = [X, "a"]
    // Both heads are equal (same TermId X), both tails "a" are equal.
    // After stripping the solver exhausts both sides — trivially satisfied.
    // Must return Done.
    #[test]
    fn equal_sides_fully_consumed_is_done() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = mk_var(&mut ctx, "x_eq");
        let a = ctx.mk_string_const("a");
        let lhs = [x, a];
        let rhs = [x, a]; // identical slices
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let result = resolve_equation(
            &mut ctx,
            &mut eq,
            &lhs,
            &rhs,
            vec![],
            dummy_eqn_lit(),
            &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(result, StepResult::Done),
            "fully-consumed (trivially equal) sides must be Done"
        );
    }

    // ── Non-conflict case 4: one side empty, other is all-variable ────────────
    // Normal forms: lhs = [],  rhs = [Y]
    // lhs is exhausted; rhs has only a variable Y.  Y = "" is a valid
    // assignment, so this is NOT a conflict.  Must return Done.
    #[test]
    fn empty_vs_single_variable_is_done_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let y = mk_var(&mut ctx, "y_emp");
        let lhs: [shinri_core::TermId; 0] = [];
        let rhs = [y];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let result = resolve_equation(
            &mut ctx,
            &mut eq,
            &lhs,
            &rhs,
            vec![],
            dummy_eqn_lit(),
            &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(result, StepResult::Done),
            "empty lhs vs single-variable rhs must be Done (Y could be \"\")"
        );
    }

    // ── Task 12: variable-headed word equation emits an F-split ──────────────
    // x ++ "a"  =  "b" ++ y  with x,y variables → an F-split is emitted (not
    // immediate sat/conflict).
    #[test]
    fn variable_head_emits_fsplit() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");
        let a = ctx.mk_string_const("a");
        let b = ctx.mk_string_const("b");
        let l = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, a])
            .unwrap();
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[b, y])
            .unwrap();
        let atom = ctx.mk_eq(l, r).unwrap();
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        s.test_force_eq_true(atom);
        let mut saw_split = false;
        for _ in 0..32 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split { atoms, guard } => {
                    if atoms.len() >= 2 {
                        // The F-split MUST be guarded by the negated word equation
                        // (sound Nielsen lemma), never a bare disjunction.
                        assert!(
                            guard.is_some(),
                            "variable-head F-split must carry a guard (¬eqn)"
                        );
                        saw_split = true;
                        break;
                    }
                }
                TCheck::Sat => break,
                TCheck::Conflict(_) => break,
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
            }
        }
        assert!(
            saw_split,
            "a variable-headed word equation must emit a multi-atom F-split"
        );
    }

    // ── Task 13: variable-vs-constant head split ─────────────────────────────
    // x = "ab" with x a variable → must NOT conflict; must emit a GUARDED split
    // whose atoms include the empty-branch `(= x "")`.
    #[test]
    fn variable_equals_constant_splits_then_sat() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let ab = ctx.mk_string_const("ab");
        let atom = ctx.mk_eq(x, ab).unwrap();
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        s.test_force_eq_true(atom);
        // Must not conflict; must emit a split (or be Sat).
        let mut ok = false;
        let mut saw_guarded_split_with_empty_branch = false;
        for _ in 0..32 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Conflict(_) => panic!("x = \"ab\" is satisfiable — must not conflict"),
                TCheck::Split { atoms, guard } => {
                    // The specialized split must contain the empty-branch atom (= x "").
                    // Check that at least one atom is an equality of x with the empty string.
                    let has_empty_branch = atoms.iter().any(|&a| {
                        if let TermNode::App {
                            op: Op::Builtin(BuiltinOp::Eq),
                            args,
                            ..
                        } = cx.terms.term_node(a)
                        {
                            let ch = cx.terms.children(*args);
                            let (lhs, rhs) = (ch[0], ch[1]);
                            // Either side equals x and the other equals "".
                            (lhs == x
                                && cx
                                    .terms
                                    .string_const_value(rhs)
                                    .is_some_and(|s| s.is_empty()))
                                || (rhs == x
                                    && cx
                                        .terms
                                        .string_const_value(lhs)
                                        .is_some_and(|s| s.is_empty()))
                        } else {
                            false
                        }
                    });
                    if has_empty_branch {
                        // The specialized var-vs-const split MUST be guarded (sound).
                        assert!(
                            guard.is_some(),
                            "var-vs-const split with empty branch must carry a guard (¬eqn)"
                        );
                        let g = guard.unwrap();
                        // test_force_eq_true uses Lit::new(Var::new(0), true) as the
                        // asserting literal; the guard must be its negation.
                        let expected_guard = Lit::new(Var::new(0), true).negate();
                        assert_eq!(
                            g, expected_guard,
                            "guard must be ¬eqn (negation of the asserting literal)"
                        );
                        saw_guarded_split_with_empty_branch = true;
                        ok = true;
                        break;
                    }
                    // Non-empty-branch splits (e.g. length axioms) may be unguarded tautologies.
                }
                TCheck::Sat => {
                    ok = true;
                    break;
                }
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
            }
        }
        assert!(
            ok,
            "x = \"ab\" must reach Sat or emit a split without conflict"
        );
        assert!(
            saw_guarded_split_with_empty_branch,
            "specialized var-vs-const split must emit an empty-branch atom (= x \"\") with a guard"
        );
    }

    // ── Positive control: conflict still detected ─────────────────────────────
    // "ab" ++ x  =  "ac" ++ x   is UNSAT by prefix mismatch (b != c at index 1).
    #[test]
    fn constant_prefix_mismatch_is_conflict() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let ab = ctx.mk_string_const("ab");
        let ac = ctx.mk_string_const("ac");
        let l = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ab, x])
            .unwrap();
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ac, x])
            .unwrap();
        let atom = ctx.mk_eq(l, r).unwrap();

        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        // Simulate the SAT layer asserting the equality true:
        s.test_force_eq_true(atom);
        // Drain length axioms, then expect a conflict.
        loop {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split { .. } => continue,
                TCheck::Conflict(_) => break,
                TCheck::Sat => panic!("expected conflict on prefix mismatch"),
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
            }
        }
    }

    // ── Task 19: occurs-check soundness (free-monoid emptiness) ──────────────
    // The occurs-check must conflict ONLY when a non-empty CONSTANT accompanies
    // the recurring variable. A second variable / second occurrence of the same
    // variable is satisfiable via emptiness and must NOT conflict.

    // `v = w ++ v ++ u`  (residual after suffix-stripping `v`: `w ++ v ++ u` on
    // RHS, `v` alone on LHS — actually after head/tail strip it's a variable
    // residual). w=u=v="" is a model ⇒ must NOT be Conflict.
    #[test]
    fn occurs_distinct_vars_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let v = mk_var(&mut ctx, "v_occ1");
        let w = mk_var(&mut ctx, "w_occ1");
        let u = mk_var(&mut ctx, "u_occ1");
        // lhs = [v], rhs = [w, v, u]
        let lhs = [v];
        let rhs = [w, v, u];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let result = resolve_equation(
            &mut ctx,
            &mut eq,
            &lhs,
            &rhs,
            vec![],
            dummy_eqn_lit(),
            &mut ctr,
            &mut emitted,
        );
        assert!(
            !matches!(result, StepResult::Conflict(_)),
            "v = w++v++u is SAT (w=u=v=\"\"); occurs-check must NOT conflict (got Conflict)"
        );
    }

    // `v = u ++ v ++ u`  — second occurrence of a DISTINCT variable `u` flanks `v`.
    // u="" is a model ⇒ must NOT be Conflict.
    #[test]
    fn occurs_repeated_flank_var_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let v = mk_var(&mut ctx, "v_occ2");
        let u = mk_var(&mut ctx, "u_occ2");
        let lhs = [v];
        let rhs = [u, v, u];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let result = resolve_equation(
            &mut ctx,
            &mut eq,
            &lhs,
            &rhs,
            vec![],
            dummy_eqn_lit(),
            &mut ctr,
            &mut emitted,
        );
        assert!(
            !matches!(result, StepResult::Conflict(_)),
            "v = u++v++u is SAT (u=\"\"); occurs-check must NOT conflict (got Conflict)"
        );
    }

    // `v = v ++ v`  — a SECOND occurrence of the SAME variable `v`. v="" is a model
    // ⇒ must NOT be Conflict (free-monoid emptiness).
    #[test]
    fn occurs_second_same_var_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let v = mk_var(&mut ctx, "v_occ3");
        let lhs = [v];
        let rhs = [v, v];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let result = resolve_equation(
            &mut ctx,
            &mut eq,
            &lhs,
            &rhs,
            vec![],
            dummy_eqn_lit(),
            &mut ctr,
            &mut emitted,
        );
        assert!(
            !matches!(result, StepResult::Conflict(_)),
            "v = v++v is SAT (v=\"\"); occurs-check must NOT conflict (got Conflict)"
        );
    }

    // SOUND occurs-check: `s = "b" ++ t ++ s` — a NON-EMPTY constant flanks the
    // recurring `s`, forcing len(s) = len(s) + (>0): genuine UNSAT. Must Conflict
    // and cite the asserted equation literal.
    #[test]
    fn occurs_nonempty_const_flank_is_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let s = mk_var(&mut ctx, "s_occ4");
        let t = mk_var(&mut ctx, "t_occ4");
        let b = ctx.mk_string_const("b");
        let lhs = [s];
        let rhs = [b, t, s];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let lit = dummy_eqn_lit();
        let just = vec![shinri_theory::types::EqLeaf::Asserted(lit)];
        let result = resolve_equation(
            &mut ctx,
            &mut eq,
            &lhs,
            &rhs,
            just,
            lit,
            &mut ctr,
            &mut emitted,
        );
        match result {
            StepResult::Conflict(cf) => {
                assert!(
                    cf.iter().any(
                        |l| matches!(l, shinri_theory::types::EqLeaf::Asserted(x) if *x == lit)
                    ),
                    "occurs-check conflict must cite the asserting word-equation literal"
                );
            }
            _ => panic!("s = \"b\"++t++s is UNSAT (non-empty constant flank); expected Conflict"),
        }
    }

    // ── Task 14: disequality same-word conflict ──────────────────────────────
    // x = "a" ++ y  AND  x != "a" ++ y  → UNSAT (same normal form, asserted distinct).
    #[test]
    fn disequality_on_equal_normal_forms_conflicts() {
        use shinri_theory::types::EqJust;
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");
        let a = ctx.mk_string_const("a");
        let ay = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, y])
            .unwrap();
        let eq_atom = ctx.mk_eq(x, ay).unwrap();
        let diseq_atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, ay])
            .unwrap();
        let mut s = StrSolver::default();
        let mut eqe = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eqe,
            atoms: &areg,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), eq_atom);
        s.new_var(&mut cx, shinri_core::Var::new(1), diseq_atom);
        // Merge x and (a++y) in the EqualityEngine to model the asserted equality.
        let xn = cx.eq.intern(x);
        let an = cx.eq.intern(ay);
        let _ = cx.eq.merge(xn, an, EqJust::Definitional);
        s.test_force_diseq_true(diseq_atom);
        let mut conflicted = false;
        for _ in 0..16 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Conflict(_) => {
                    conflicted = true;
                    break;
                }
                TCheck::Split { .. } => continue,
                TCheck::Sat => break,
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
            }
        }
        assert!(
            conflicted,
            "asserted distinct over equal normal forms is UNSAT"
        );
    }
}
