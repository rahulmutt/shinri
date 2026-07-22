use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, TermNode};
use shinri_theory::types::EqLeaf;
use shinri_theory::EqualityEngine;

#[derive(Debug)]
pub enum StepResult {
    Done,
    /// The word equation has a variable-headed residual whose F-split was ALREADY
    /// emitted (dedup hit) — the search is saturated WITHOUT having ground-resolved
    /// the equation. The caller must NOT conclude SAT from this state (the model
    /// builder cannot reliably realise the chained F-split merges into a satisfying
    /// witness — the (B′) premature-SAT hazard), and instead returns a SOUND
    /// `Unknown`. Distinct from `Done` (which means trivially resolved / consumed).
    Saturated,
    /// SLICE 33 (widened in SLICE 34). The equation entails the single-atom
    /// propagation `var ≈ word`. Two residual shapes report it:
    ///
    /// - slice 33: a single variable vs an ALL-CONSTANT word. `word` is a
    ///   SINGLE interned string constant — a multi-atom constant side is
    ///   folded before it is reported, so the caller's merge never depends on
    ///   a CONCAT term's own normal form.
    /// - slice 34: BOTH residuals a single free variable (`[v] = [u]`;
    ///   stripping guarantees the classes are distinct). `word` is the other
    ///   VARIABLE's term; the merge is a var–var class union and may create a
    ///   string class with NO constant member.
    ///
    /// This is NOT the deleted E1 probe (see the comment further down this
    /// file). That probe returned `Done` — it claimed the equation was
    /// RESOLVED and cited nothing. This reports a FACT together with `just`,
    /// its full antecedent set, which the caller merges into EUF under an
    /// `EqJust::Interface` tag. `just` includes not only the asserting
    /// word-equation literal and any `normal_form` antecedents but, as of
    /// slice 37, every EUF-door strip merge the strip loops consumed (via
    /// `same_explain`, on BOTH the flattened and non-flattened paths — the
    /// pass is shared) — so the interface merge is fully
    /// justified even when a strip cancelled through a live EUF class rather
    /// than same-TermId or literal-value identity. Nothing is emitted and
    /// nothing is learnt, so the E1 branch-locality gate has no clause to
    /// reject. The MULTI-ATOM variable-bearing word stays fenced (slice-34
    /// spec §2).
    Propagate {
        var: TermId,
        word: TermId,
        just: Vec<EqLeaf>,
    },
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
///
/// BRANDING CONTRACT (load-bearing): the `!strk` name prefix is how
/// `is_minted_skolem` below recognizes a term minted here. If this prefix
/// ever changes, `is_minted_skolem` MUST change with it — keep the two in
/// sync.
///
/// FRESHNESS (slice 35, mirrors word_norm's `ite!` mint): user-owned names
/// are skipped (a pre-declared `|!strkN|` is never adopted as a skolem),
/// and the minted name is reserved so a later user `declare-fun` naming it
/// is rejected at parse time — otherwise the user's app hash-conses to the
/// skolem and inherits its internal identity (wrong-verdict shape; see the
/// slice-5 `ite!` finding).
///
/// **Slice-35 final-review correction:** the "rejected at parse time" claim
/// above does not hold for `fresh_str` mints reached via `check_sat`.
/// `Solver::check_sat` clones `self.ctx` into the theory Combiner before
/// search (`crates/shinri-solver/src/lib.rs:711`), so every mint (and its
/// `reserve_symbol` call) here runs on that clone; the clone — and the
/// reservation with it — is discarded when `check_sat` returns, and a
/// subsequent user `declare-fun` naming the minted symbol is accepted, not
/// rejected. This is unlike word_norm's `ite!` mint, which runs on
/// `self.ctx` itself, pre-clone (`lib.rs:384`), so its reservation genuinely
/// reaches the parser. The `reserve_symbol` call here is retained as
/// unit-level defense-in-depth — it protects a future refactor that moves
/// this mint to run pre-clone — not as the mechanism that currently
/// prevents aliasing (that is clone isolation itself: the skolem never
/// exists in the parser-visible context a later `declare-fun` runs against).
pub fn fresh_str(terms: &mut Context, ctr: &mut u32) -> TermId {
    let str_s = terms.string_sort();
    loop {
        let name = format!("!strk{}", *ctr);
        *ctr += 1;
        if terms.lookup_symbol(&name).is_some() {
            continue; // user (or an earlier check) owns this name
        }
        let sym = terms.declare_fun(&name, &[], str_s);
        terms.reserve_symbol(sym);
        return terms
            .mk_app(Op::Uninterpreted(sym), &[])
            .expect("well-sorted");
    }
}

/// True iff `t` is a MINTED char-peel/F-split skolem — a nullary symbol whose
/// name carries the `!strk` prefix branded by `fresh_str` above (branding
/// contract: keep the two in sync). Used to EXCLUDE skolem atoms from the
/// slice-34 alias-propagation guard: a skolem is purely internal bookkeeping
/// for the char-peel/F-split machinery and never appears in a user-asserted
/// `distinct` or constant constraint, so merging two skolems can never
/// produce a useful conflict — it can only bypass the F-split the model
/// builder relies on (task-4-blocker-diagnosis.md, T4b, slice 34).
///
/// This is a NAME check, not a tracked-TermId check, so it is a heuristic: a
/// user symbol literally declared as `|!strkN|` would false-positive here.
/// Since slice 35, `fresh_str` skips user-owned names and reserves minted
/// ones, so such a term is never ALSO a skolem — the false positive only
/// narrows completeness (the slice-34 guard declines to propagate), never
/// soundness. The tracked-TermId-set upgrade remains banked.
fn is_minted_skolem(terms: &Context, t: TermId) -> bool {
    match terms.term_node(t) {
        TermNode::App {
            op: Op::Uninterpreted(sym),
            args,
            ..
        } if args.len == 0 => terms.symbol_name(*sym).starts_with("!strk"),
        _ => false,
    }
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

/// Sound completeness for the "one side fully constant, other side is a single
/// (possibly repeated) variable interleaved with constants" pattern. Returns
/// `true` iff the (already head/tail-stripped) equation is UNSAT by this
/// analysis.
///
/// When exactly one residual `cw` is a FIXED word `W` (all string constants,
/// `|W| = L`) and the other residual `vw` is a sequence of constant atoms
/// (contributing `C` fixed chars over `k_v` variable occurrences of a SINGLE
/// variable `v`), the length of `v` is FORCED: `k·|v| + C = L` has a unique
/// non-negative integer solution `m = (L − C)/k` (or none, ⟹ UNSAT). Given that
/// forced length the layout of `vw` against `W` is fully determined; tiling it
/// left-to-right, every constant atom must equal its span and every occurrence
/// of `v` must equal the SAME span. Any mismatch ⟹ UNSAT in the free monoid.
///
/// SOUNDNESS: `m` is genuinely forced (every model must give `v` length `m`),
/// so a tiling contradiction rules out ALL models — never a wrong UNSAT. The
/// analysis is COMPLETE for this pattern (a consistent tiling exhibits the model
/// `v = window`), self-contained (mints no fresh terms, cites only the equation
/// literal like the neighbouring constant-length/char-set bounds), and only
/// ADDS conflicts — it never changes SAT/split behaviour. It requires a SINGLE
/// distinct variable: two distinct variables (e.g. `u ++ w = "bc"`, SAT with
/// `u="b", w="c"`) are a different pattern and fall through untouched. A
/// variable EUF-merged to a constant is still treated as a free window here,
/// which stays sound (we only ever emit a conflict, never claim SAT). This
/// decides repeated-variable equations such as `u ++ "z" ++ u = "bzc"` (the
/// `str.replace_all` symbolic-`u` shape) that the atom-wise resolver otherwise
/// leaves as a sound Unknown.
fn single_var_forced_length_conflict(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    lhs: &[TermId],
    rhs: &[TermId],
) -> bool {
    let all_const =
        |sl: &[TermId], terms: &Context| sl.iter().all(|&a| terms.string_const_value(a).is_some());
    // Identify (fully-constant side `cw`, variable-bearing side `vw`). Exactly one
    // side must be fully constant (both-const is handled by the caller's earlier
    // cat-compare; both-variable is not this pattern).
    let (cw, vw): (&[TermId], &[TermId]) = if all_const(lhs, terms) && !all_const(rhs, terms) {
        (lhs, rhs)
    } else if all_const(rhs, terms) && !all_const(lhs, terms) {
        (rhs, lhs)
    } else {
        return false;
    };
    // The fixed word as code points (never bytes).
    let w: Vec<char> = cw
        .iter()
        .flat_map(|&a| {
            terms
                .string_const_value(a)
                .unwrap()
                .chars()
                .collect::<Vec<char>>()
        })
        .collect();
    let l = w.len();
    // Partition `vw`: constant atoms contribute fixed chars; every non-constant
    // atom must be the SAME variable (by TermId / EUF class) or we bail.
    let mut var_atom: Option<TermId> = None;
    let mut k = 0usize;
    let mut c = 0usize;
    for &a in vw {
        if let Some(s) = terms.string_const_value(a) {
            c += s.chars().count();
        } else {
            match var_atom {
                None => var_atom = Some(a),
                Some(v) if same(terms, eq, a, v) => {}
                Some(_) => return false, // ≥2 distinct variables: not this pattern
            }
            k += 1;
        }
    }
    if k == 0 {
        return false; // no variable ⟹ both-const, handled by caller
    }
    // Forced length: k·m + c = l. No non-negative integer solution ⟹ UNSAT.
    if l < c || !(l - c).is_multiple_of(k) {
        return true;
    }
    let m = (l - c) / k;
    // Tile `vw` over `W` at the forced layout; check every span.
    let mut cursor = 0usize;
    let mut window: Option<&[char]> = None;
    for &a in vw {
        if let Some(s) = terms.string_const_value(a) {
            let cs: Vec<char> = s.chars().collect();
            let end = cursor + cs.len();
            if end > l || w[cursor..end] != cs[..] {
                return true; // constant atom mismatched its forced span
            }
            cursor = end;
        } else {
            let end = cursor + m;
            if end > l {
                return true;
            }
            let span = &w[cursor..end];
            match window {
                None => window = Some(span),
                Some(prev) if prev == span => {}
                Some(_) => return true, // two occurrences forced to differ
            }
            cursor = end;
        }
    }
    // cursor == l by construction and every span matched ⟹ SAT (v = window).
    false
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

/// Like [`same`], but on the EUF-class door (the pair is equal only because a
/// MERGE placed both atoms in one class) it appends the merge's antecedent
/// leaves to `out` via `eq.explain`. The same-TermId and equal-literal-value
/// doors are self-justifying and contribute no leaf (mirroring
/// `nf_equal_explain`'s two `continue` guards). Used by the strip loops so a
/// residual propagation cites every class equality a strip consumed — the
/// citation slice 35 lacked, which forced the flattened-path `Propagate`
/// downgrade.
pub(crate) fn same_explain(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    a: TermId,
    b: TermId,
    out: &mut Vec<EqLeaf>,
) -> bool {
    if a == b {
        return true; // identity: no merge, no leaf
    }
    if let (Some(x), Some(y)) = (terms.string_const_value(a), terms.string_const_value(b)) {
        return x == y; // literal-value equality: no merge antecedent
    }
    let an = eq.intern(a);
    let bn = eq.intern(b);
    if eq.are_equal(an, bn) {
        eq.explain(an, bn, out); // EUF door: cite the merge path
        true
    } else {
        false
    }
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
///    downgrades it to `Saturated`. Such a conflict cites only the word-equation
///    literal, an under-cited global exclusion. This downgrade STAYS (slice 37
///    lifted only the Propagate sibling; the Conflict lift is separately banked
///    behind its own measured trigger). Purely structural conflicts on words
///    with NO concat atom are unaffected.
/// 3. If a concat atom WAS flattened and the inner resolver reports a PROPAGATE,
///    it is now PASSED THROUGH (slice 37, un-banking approach B). The strip
///    loops cite every EUF-class merge they consume into `just` via
///    `same_explain`, so the residual merge the caller lands is fully justified
///    — no longer the under-citation slice 35 fenced by downgrading to
///    `Saturated`. This restores the one measured completeness cost slice 35
///    logged (hash 8e950d0d, `qfs_predicates_matches_z3`).
/// 4. `Split` (both the char-peel and generic F-split) is now guarded INSIDE
///    `resolve_inner` (slice 38): a split reached through a non-identity
///    EUF-door strip downgrades to `Saturated`, because its `¬eqn`-only learnt
///    clause omits the stripped class equality (an under-guarded, wrong-UNSAT
///    shape a learnt clause — unlike a `Propagate` merge — is not backstopped by
///    the model gate). The guard lives in the inner resolver, so it covers BOTH
///    this flattened path and the direct non-flattened path; the wrapper needs
///    no `Split` arm of its own.
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
        // (Lifting THIS arm is separately banked — no qualifying trigger yet.)
        StepResult::Conflict(_) => StepResult::Saturated,
        // A Propagate is now passed through: the strip loops cite every
        // EUF-door merge into `just` (slice 37, un-banking approach B), so the
        // EUF merge the caller lands is fully justified. The one measured cost
        // slice 35 logged (hash 8e950d0d, qfs_predicates_matches_z3) is bought
        // back here.
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
    mut just: Vec<EqLeaf>,
    eqn_lit: Lit,
    fresh_ctr: &mut u32,
    emitted: &mut FxHashSet<(TermId, TermId)>,
) -> StepResult {
    let (mut i, mut j) = (0usize, 0usize);
    let (mut le, mut re) = (lhs.len(), rhs.len());

    // SLICE 38: snapshot the citation count BEFORE the strip loops. `same_explain`
    // grows `just` only on the EUF door (identity/equal-literal doors push
    // nothing — see `same_explain`), and nothing between here and the F-split
    // emission sites below pushes to `just` except the strip loops. So
    // `just.len() > incoming_just` at an F-split site means a non-identity class
    // equality was load-bearing for the residual — the F-split's `¬eqn`-only
    // clause would omit it (under-guarded, wrong-UNSAT shape). Guard both sites.
    let incoming_just = just.len();

    // Strip equal heads (citing any EUF-class merge each cancellation consumes).
    while i < le && j < re && same_explain(terms, eq, lhs[i], rhs[j], &mut just) {
        i += 1;
        j += 1;
    }

    // Strip equal tails (same citation).
    while le > i && re > j && same_explain(terms, eq, lhs[le - 1], rhs[re - 1], &mut just) {
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

    // E1 PROBE — REMOVED (E1 design). The probe returned `Done` for a pure
    // assignment `v = W` (single variable `v` ∉ `W`) to dodge the t8iter175
    // wrong-UNSAT, whose true cause was the UNDER-CITED minted-skolem length
    // lemmas (the char-peel `v = ""` empty branch feeding the non-empty separation
    // + length-link over a fresh skolem). That root cause is now fixed at source in
    // `lib.rs::check` (the minted-equality gate on the length-link, empty-residual,
    // and non-empty-separation lemmas), so the probe is redundant. Removing it
    // restores the correct char-peel/F-split emission for `v = W` (the
    // `variable_equals_constant_splits_then_sat` and `str_input_var_concat_length_*`
    // pins the probe had broken) while t8iter175 stays SAT. The probe was also
    // unsound-shaped: `string_const_value(lhs[i]).is_none()` matches an unflattened
    // CONCAT rep as if it were a free variable (mitigated only because the wrapper
    // flattens first) — another reason to drop it rather than narrow it.

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

    // ── SLICE 33/34: single-atom propagation ─────────────────────────────────
    // SLICE 33: a residual `[v] = [constant word]` ENTAILS `v ≈ W` (multi-atom
    // constant sides folded to one interned term). SLICE 34: a residual
    // `[v] = [u]` (free variable each side) ENTAILS `v ≈ u` by cancellation.
    // Before these, both shapes fell through to the variable-headed F-split
    // below, hit the dedup, and returned `Saturated` → a sound but needless
    // `Unknown`. Reporting the fact here, BEFORE the F-split, is the whole fix.
    //
    // Scope (slice-34 spec §2): the MULTI-ATOM variable-bearing word stays
    // fenced — it is the deleted E1 probe's shape (needs a CONCAT merge target
    // and an in-word occurs-check) and is deliberately out of scope.
    //
    // The `is_concat` guard fixes the probe's other defect: it tested
    // `string_const_value(..).is_none()`, which matches an unflattened CONCAT
    // rep as if it were a free variable. The wrapper flattens, but we do not
    // rely on that here — an atom that is still a CONCAT is never treated as a
    // variable.
    {
        let l_res = &lhs[i..le];
        let r_res = &rhs[j..re];

        let is_concat = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrConcat),
                    ..
                }
            )
        };
        let is_free_var = |terms: &Context, t: TermId| {
            terms.string_const_value(t).is_none() && !is_concat(terms, t)
        };
        let all_const = |sl: &[TermId], terms: &Context| {
            sl.iter().all(|&a| terms.string_const_value(a).is_some())
        };

        // SLICE 34: alias case — BOTH residuals are a single free variable.
        // `[v] = [u]` entails `v ≈ u` by cancellation in the free monoid.
        // No occurs-check is needed here, structurally: head/tail stripping
        // removed every same-class pair, so a SURVIVING var–var residual
        // proves the two classes are distinct — the merge is never `v ≈ v`,
        // and a one-atom variable side cannot contain `v` any other way
        // (contrast the fenced multi-atom shape, where `v` can occur inside
        // the word). Left residual is `var`, fixed, for determinism; the EUF
        // merge is symmetric. `word` here is the other VARIABLE's TermId —
        // the driver's merge is a var–var class union and may create a string
        // class with NO constant member (spec §5); the driver and model paths
        // are shape-agnostic.
        //
        // SKOLEM EXCLUSION (task-4-blocker-diagnosis.md, T4b fix, slice 34,
        // 2026-07-20): neither atom may be a MINTED `!strk*` char-peel/F-split
        // skolem (`is_minted_skolem` above). A char-peel of a literal head
        // (e.g. `"ab" ++ s0` peeling to `"a" ++ !strk0`) can produce a
        // residual `[!strk1] = [!strk0]` that satisfies the shape above but
        // whose atoms are both fresh internal remainders, not the user's
        // input variables. Merging such a pair directly into EUF REPLACES the
        // F-split the model builder needs to realise the length-alignment
        // between the peeled head and the anchoring original concat — the
        // merged class free-fills to a garbage, too-short value and the
        // post-solve witness self-check soundly downgrades a genuine `sat` to
        // `unknown` (a completeness regression, not an unsoundness). A
        // skolem never appears in a user `distinct` or constant constraint,
        // so excluding it here loses no useful conflict: the fallback is
        // exactly the pre-slice-34 F-split path.
        if l_res.len() == 1
            && r_res.len() == 1
            && is_free_var(terms, l_res[0])
            && is_free_var(terms, r_res[0])
            && !is_minted_skolem(terms, l_res[0])
            && !is_minted_skolem(terms, r_res[0])
        {
            return StepResult::Propagate {
                var: l_res[0],
                word: r_res[0],
                just,
            };
        }

        let pair = if l_res.len() == 1 && is_free_var(terms, l_res[0]) && all_const(r_res, terms) {
            Some((l_res[0], r_res))
        } else if r_res.len() == 1 && is_free_var(terms, r_res[0]) && all_const(l_res, terms) {
            Some((r_res[0], l_res))
        } else {
            None
        };

        if let Some((var, const_side)) = pair {
            // Fold the constant side to ONE interned constant. The empty side
            // folds to "" — `v ≈ ""` is a legitimate propagation.
            let mut w = String::new();
            for &a in const_side {
                w.push_str(
                    terms
                        .string_const_value(a)
                        .expect("all_const checked every atom"),
                );
            }
            let word = terms.mk_string_const(&w);
            return StepResult::Propagate { var, word, just };
        }
    }

    // Single-variable forced-length analysis: one side fully constant, the other
    // a single (possibly repeated) variable interleaved with constants. The
    // variable's length is FORCED (k·|v| + C = L); tiling `vw` over the constant
    // word at that unique length decides this pattern exactly. Sound,
    // self-contained (no fresh terms), cites only the equation literal, and only
    // ADDS conflicts — it decides repeated-variable equations like
    // `u ++ "z" ++ u = "bzc"` (the str.replace_all symbolic-`u` shape) that the
    // atom-wise resolver otherwise leaves as a sound Unknown.
    if single_var_forced_length_conflict(terms, eq, &lhs[i..le], &rhs[j..re]) {
        return StepResult::Conflict(just);
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
            // SLICE 38: under-guard check — a residual reached through an EUF-door
            // strip makes this char-peel clause depend on the stripped class
            // equality, which the `¬eqn` guard omits. Wait for SAT instead. Do
            // NOT record the dedup key: a later round whose class state no longer
            // needs the strip can emit the split cleanly.
            if just.len() > incoming_just {
                return StepResult::Saturated;
            }
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
            // SLICE 38: same under-guard check as the char-peel site above.
            if just.len() > incoming_just {
                return StepResult::Saturated;
            }
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
    use crate::wordeq::{fresh_str, resolve_equation, StepResult};
    use crate::StrSolver;
    use rustc_hash::FxHashSet;
    use shinri_core::{BuiltinOp, Context, Lit, Op, Var};
    use shinri_sat::Effort;
    use shinri_theory::types::EqLeaf;
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

    // Slice 33: same shape as `mk_var`, named to match the pure-assignment
    // fixture below.
    fn declare_str_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        mk_var(ctx, name)
    }

    // Slice 33: shared fixture for the pure-assignment propagation tests below,
    // factored out of the `occurs_*` setup style (mirrors
    // `occurs_nonempty_const_flank_is_conflict`'s `Context`/`EqualityEngine`
    // construction and its non-trivial `just` citing the asserting word-equation
    // literal). Returns `(terms, eq, var, word, just, eqn_lit)`.
    fn setup_pure_assignment(
        var_name: &str,
        const_value: &str,
    ) -> (
        Context,
        EqualityEngine,
        shinri_core::TermId,
        shinri_core::TermId,
        Vec<EqLeaf>,
        Lit,
    ) {
        let mut ctx = Context::new();
        let eq = EqualityEngine::default();
        let var = declare_str_var(&mut ctx, var_name);
        let word = ctx.mk_string_const(const_value);
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        (ctx, eq, var, word, just, lit)
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
    // assignment, so this is NOT a conflict.
    //
    // SLICE 33: this is itself a pure assignment (`Y ≈ ""`, the empty constant
    // side folds to the empty string — see the propagation block's comment).
    // Before slice 33 this fell through unreported to `Done`; now it PROPAGATES,
    // same as any other single-variable-vs-all-constant residual. Renamed from
    // `empty_vs_single_variable_is_done_not_conflict` to match.
    #[test]
    fn empty_vs_single_variable_propagates_empty_word() {
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
        match result {
            StepResult::Propagate { var, word, .. } => {
                assert_eq!(var, y, "the variable side must be reported as `var`");
                assert_eq!(
                    ctx.string_const_value(word),
                    Some(""),
                    "the empty constant side must fold to the empty string"
                );
            }
            _ => panic!("empty lhs vs single-variable rhs must Propagate `Y ≈ \"\"`"),
        }
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
                TCheck::Split { atoms, guard, .. } => {
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

    // ── Task 13 / Slice 33: variable-vs-constant pure assignment ─────────────
    // `x = "ab"` with `x` a variable is the CORE pure-assignment shape (single
    // variable vs. single all-constant word). Pre-slice-33 this shape reached
    // SAT by emitting a GUARDED char-peel split whose atoms included the
    // empty-branch `(= x "")`. Slice 33 replaces that with a DIRECT outcome:
    // `resolve_equation` reports `StepResult::Propagate { var: x, word: "ab" }`,
    // and `check()` (Task 5) merges `x ≈ "ab"` into EUF under an
    // `EqJust::Interface` tag BEFORE any char-peel/F-split path runs (that
    // interception is the whole point of slice 33; see
    // `pure_assignment_propagates_constant_word` above).
    //
    // Renamed from `variable_equals_constant_splits_then_sat`: this shape no
    // longer splits. The test now proves the STRONGER post-slice-33 property —
    // the equation decides SAT with NO conflict and NO split, AND the outcome is
    // self-consistent: `x` and `"ab"` are EUF-equal afterwards (the propagated
    // merge actually landed, so any model read off EUF satisfies the equation).
    // The char-peel var-vs-const split machinery is still exercised by
    // `constant_prefix_mismatch_is_conflict` and the residual-headed split tests
    // below, whose residuals the pure-assignment fence does not intercept.
    #[test]
    fn variable_equals_constant_propagates_then_sat() {
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
        // Must NOT conflict and must reach Sat via propagation — no split needed.
        let mut reached_sat = false;
        for _ in 0..32 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Conflict(_) => panic!("x = \"ab\" is satisfiable — must not conflict"),
                TCheck::Split { .. } => {
                    // A length/axiom split may still fire; keep pumping to a verdict.
                    continue;
                }
                TCheck::Sat => {
                    reached_sat = true;
                    break;
                }
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
            }
        }
        assert!(
            reached_sat,
            "x = \"ab\" must decide Sat (pure-assignment propagation)"
        );
        // Self-consistency: the propagated fact actually landed in EUF, so `x`
        // and `"ab"` are now in the same class. A model read off EUF therefore
        // assigns `x = "ab"`, satisfying the equation (this is what the old
        // empty-branch split was a proxy for — here we assert the merge directly).
        let xn = cx.eq.intern(x);
        let abn = cx.eq.intern(ab);
        assert!(
            cx.eq.are_equal(xn, abn),
            "propagation must merge x ≈ \"ab\" in EUF (self-consistent SAT)"
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

    // ── Slice 33: propagation outcome ────────────────────────────────────────
    // A residual pure assignment `v = W` (W all-constant) must PROPAGATE, not
    // fall through to the variable-headed F-split → dedup → Saturated path.

    /// The core shape: `[y] = ["ab"]` reports `y ≈ "ab"`.
    #[test]
    fn pure_assignment_propagates_constant_word() {
        // Build `y = "ab"` as a residual and resolve it.
        // (setup mirrors occurs_distinct_vars_not_conflict)
        let (mut terms, mut eq, y, ab, just, eqn_lit) = setup_pure_assignment("y", "ab");
        let mut fresh_ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut terms,
            &mut eq,
            &[y],
            &[ab],
            just,
            eqn_lit,
            &mut fresh_ctr,
            &mut emitted,
        );
        match r {
            StepResult::Propagate { var, word, .. } => {
                assert_eq!(var, y, "the variable side must be reported as `var`");
                assert_eq!(
                    terms.string_const_value(word),
                    Some("ab"),
                    "`word` must be a single interned constant"
                );
            }
            _ => panic!("expected Propagate for a pure assignment, got a different outcome"),
        }
    }

    /// A MULTI-ATOM constant side folds to ONE constant. Merging against a
    /// multi-atom CONCAT term would make the merge depend on that term's own
    /// normal form (spec §3).
    #[test]
    fn pure_assignment_folds_multi_atom_constant_side() {
        let (mut terms, mut eq, y, _unused, just, eqn_lit) = setup_pure_assignment("y", "ab");
        let a = terms.mk_string_const("a");
        let b = terms.mk_string_const("b");
        let mut fresh_ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut terms,
            &mut eq,
            &[y],
            &[a, b],
            just,
            eqn_lit,
            &mut fresh_ctr,
            &mut emitted,
        );
        match r {
            StepResult::Propagate { word, .. } => assert_eq!(
                terms.string_const_value(word),
                Some("ab"),
                "['a','b'] must fold to the single constant \"ab\""
            ),
            _ => panic!("expected Propagate for a multi-atom constant side"),
        }
    }

    /// Orientation-independent: the variable may sit on either side.
    #[test]
    fn pure_assignment_propagates_with_variable_on_right() {
        let (mut terms, mut eq, y, ab, just, eqn_lit) = setup_pure_assignment("y", "ab");
        let mut fresh_ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut terms,
            &mut eq,
            &[ab],
            &[y],
            just,
            eqn_lit,
            &mut fresh_ctr,
            &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Propagate { var, .. } if var == y),
            "the variable must be found on either side"
        );
    }

    /// SCOPE FENCE (slice-34 spec §2): a MULTI-ATOM variable-bearing word must
    /// NOT propagate — `v = w ++ "a"` needs a CONCAT merge target and an
    /// in-word occurs-check; it is the deleted E1 probe's shape and stays
    /// fenced. (The SINGLE-variable alias residual `[v] = [u]` DOES propagate
    /// as of slice 34 — see `alias_residual_propagates`.)
    #[test]
    fn multi_atom_variable_bearing_word_does_not_propagate() {
        let (mut terms, mut eq, y, _ab, just, eqn_lit) = setup_pure_assignment("y", "ab");
        let w = declare_str_var(&mut terms, "w");
        let a = terms.mk_string_const("a");
        let mut fresh_ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut terms,
            &mut eq,
            &[y],
            &[w, a],
            just,
            eqn_lit,
            &mut fresh_ctr,
            &mut emitted,
        );
        assert!(
            !matches!(r, StepResult::Propagate { .. }),
            "a MULTI-ATOM variable-bearing word must NOT propagate (slice-34 spec §2)"
        );
    }

    // ── Slice 34: alias propagation ──────────────────────────────────────────
    // A residual `[v] = [u]` (free variable each side, distinct classes — the
    // stripping loop guarantees distinctness) entails `v ≈ u` by cancellation
    // and must PROPAGATE, not fall to the F-split → dedup → Saturated path.

    /// The core shape: `[x] = [y]` reports `x ≈ y`, left residual as `var`.
    #[test]
    fn alias_residual_propagates() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_al");
        let y = declare_str_var(&mut ctx, "y_al");
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[x],
            &[y],
            just,
            lit,
            &mut ctr,
            &mut emitted,
        );
        match r {
            StepResult::Propagate { var, word, just } => {
                assert_eq!(var, x, "left residual must be reported as `var`");
                assert_eq!(word, y, "right residual must be reported as `word`");
                assert!(
                    just.iter()
                        .any(|l| matches!(l, EqLeaf::Asserted(a) if *a == lit)),
                    "alias propagation must cite the asserting equation literal"
                );
            }
            _ => panic!("expected Propagate for an alias residual"),
        }
    }

    /// The real e2e path: `"a"·x = "a"·y` strips the shared constant head,
    /// leaving the alias residual.
    #[test]
    fn alias_after_head_strip_propagates() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_hs");
        let y = declare_str_var(&mut ctx, "y_hs");
        let a = ctx.mk_string_const("a");
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[a, x],
            &[a, y],
            just,
            lit,
            &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Propagate { var, word, .. } if var == x && word == y),
            "shared head must strip, then the alias residual must propagate"
        );
    }

    /// A single CONCAT atom is NOT a free variable (`is_free_var` excludes it,
    /// the deleted E1 probe's other defect): `[x] = [concat(w, z)]` must NOT
    /// propagate.
    #[test]
    fn single_concat_atom_does_not_propagate() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_cc");
        let w = declare_str_var(&mut ctx, "w_cc");
        let z = declare_str_var(&mut ctx, "z_cc");
        let concat = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[w, z])
            .unwrap();
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[x],
            &[concat],
            just,
            lit,
            &mut ctr,
            &mut emitted,
        );
        assert!(
            !matches!(r, StepResult::Propagate { .. }),
            "an unflattened CONCAT atom must never be treated as a variable"
        );
    }

    /// Slice 37 (was slice 35's `..._does_not_propagate`): a pure-assignment
    /// residual reached by FLATTENING a concat rep now PROPAGATES. This fixture's
    /// only cancellation is none at all (`x` vs the constant word), so no EUF-door
    /// strip runs and `just` is unchanged; the wrapper no longer downgrades it.
    /// Control: `flattened_alias_residual_cites_euf_strip_merge` covers the case
    /// where a strip DOES consume a merge and the leaf must appear.
    #[test]
    fn flattened_pure_assignment_now_propagates() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_fpa");
        let a = ctx.mk_string_const("a");
        let b = ctx.mk_string_const("b");
        let concat = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, b])
            .unwrap();
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[x],
            &[concat],
            just,
            lit,
            &mut ctr,
            &mut emitted,
        );
        match r {
            StepResult::Propagate { var, word, .. } => {
                assert_eq!(var, x, "the variable side is reported as `var`");
                assert_eq!(
                    ctx.string_const_value(word),
                    Some("ab"),
                    "the flattened constant side folds to \"ab\""
                );
            }
            _ => panic!("a flattened pure assignment must now Propagate, not Saturate"),
        }
    }

    /// Slice 37 (was slice 35's `..._does_not_propagate`): the alias variant now
    /// PROPAGATES. Flattening exposes a strippable constant head `"a"` that cancels
    /// via the identity/literal door (no merge, no leaf), leaving the var–var
    /// residual `[x] = [y]` that slice 34 merges. `just` is unchanged; the wrapper
    /// passes the propagation through.
    #[test]
    fn flattened_alias_residual_now_propagates() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_far");
        let y = declare_str_var(&mut ctx, "y_far");
        let a = ctx.mk_string_const("a");
        let concat = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, x])
            .unwrap();
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[concat],
            &[a, y],
            just,
            lit,
            &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Propagate { var, word, .. } if var == x && word == y),
            "an alias residual off a flattened concat rep must now Propagate `x ≈ y`"
        );
    }

    /// Slice 37: a strip through the identity/literal door must NOT enrich `just`
    /// (the two self-justifying `same_explain` doors add no leaf). `[a, x] = [a, y]`
    /// has no concat atom (non-flattened path) and its shared `"a"` head strips by
    /// identity — the propagated `just` must be byte-identical to the input.
    #[test]
    fn non_flattened_literal_strip_leaves_just_unchanged() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_inv");
        let y = declare_str_var(&mut ctx, "y_inv");
        let a = ctx.mk_string_const("a");
        let eqn_lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(eqn_lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[a, x],
            &[a, y],
            just,
            eqn_lit,
            &mut ctr,
            &mut emitted,
        );
        match r {
            StepResult::Propagate { just, .. } => {
                assert_eq!(
                    just,
                    vec![EqLeaf::Asserted(eqn_lit)],
                    "a self-justifying strip must leave `just` unchanged"
                );
            }
            _ => panic!("expected Propagate for the alias residual"),
        }
    }

    /// Slice 37: the flattened alias residual that slice 35 downgraded now
    /// PROPAGATES — and cites the EUF-door strip merge. `p ≈ q` is merged with
    /// antecedent `merge_lit`; the flattened head strip cancels `p` against `q`
    /// through the `eq.are_equal` door, so the propagated `x ≈ y` MUST carry
    /// `merge_lit` in its justification (the under-citation slice 35 fenced).
    #[test]
    fn flattened_alias_residual_cites_euf_strip_merge() {
        use shinri_theory::types::EqJust;
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let p = declare_str_var(&mut ctx, "p_cite");
        let q = declare_str_var(&mut ctx, "q_cite");
        let x = declare_str_var(&mut ctx, "x_cite");
        let y = declare_str_var(&mut ctx, "y_cite");
        // Merge p ≈ q via a genuine EUF merge whose antecedent is `merge_lit`.
        let merge_lit = Lit::new(Var::new(1), true);
        let pn = eq.intern(p);
        let qn = eq.intern(q);
        let _ = eq.merge(pn, qn, EqJust::Asserted(merge_lit));
        // lhs carries a concat atom → flattened path; the head strip cancels p
        // against q via the EUF door (not same-TermId, not literal value).
        let concat = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[p, x])
            .unwrap();
        let eqn_lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(eqn_lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[concat],
            &[q, y],
            just,
            eqn_lit,
            &mut ctr,
            &mut emitted,
        );
        match r {
            StepResult::Propagate { var, word, just } => {
                assert_eq!(var, x, "left residual must be reported as `var`");
                assert_eq!(word, y, "right residual must be reported as `word`");
                assert!(
                    just.iter()
                        .any(|l| matches!(l, EqLeaf::Asserted(a) if *a == eqn_lit)),
                    "must retain the asserting equation literal"
                );
                assert!(
                    just.iter()
                        .any(|l| matches!(l, EqLeaf::Asserted(a) if *a == merge_lit)),
                    "must CITE the EUF-door strip merge antecedent (slice-37 fix)"
                );
            }
            _ => panic!("expected Propagate carrying the cited strip merge"),
        }
    }

    /// Slice 38: a char-peel F-split reached through a NON-IDENTITY EUF-door
    /// strip is under-guarded (its `¬eqn`-only clause omits the strip's class
    /// equality `p≈q`). It must downgrade to `Saturated`, not emit `Split`.
    /// `p ≈ q` is merged (antecedent `merge_lit`); the head strip cancels p
    /// against q via the EUF door, growing `just`; the residual `[x, x2] = ["b"]`
    /// would otherwise char-peel-split on the (x, "b") pair.
    #[test]
    fn charpeel_split_after_euf_strip_downgrades_to_saturated() {
        use shinri_theory::types::EqJust;
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let p = mk_var(&mut ctx, "p_s38a");
        let q = mk_var(&mut ctx, "q_s38a");
        let x = mk_var(&mut ctx, "x_s38a");
        let x2 = mk_var(&mut ctx, "x2_s38a");
        let b = ctx.mk_string_const("b");
        let merge_lit = Lit::new(Var::new(1), true);
        let pn = eq.intern(p);
        let qn = eq.intern(q);
        let _ = eq.merge(pn, qn, EqJust::Asserted(merge_lit));
        let eqn_lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(eqn_lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[p, x, x2],
            &[q, b],
            just,
            eqn_lit,
            &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Saturated),
            "char-peel split reached through an EUF-door strip must downgrade to Saturated, got {r:?}"
        );
        assert!(
            emitted.is_empty(),
            "downgrade must NOT record the dedup key (a later clean round must be able to split)"
        );
    }

    /// Slice 38: same under-guard, generic (two-variable-head) F-split site.
    /// Residual `[x, x2] = [w]` would otherwise emit the generic Nielsen split.
    #[test]
    fn generic_fsplit_after_euf_strip_downgrades_to_saturated() {
        use shinri_theory::types::EqJust;
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let p = mk_var(&mut ctx, "p_s38b");
        let q = mk_var(&mut ctx, "q_s38b");
        let x = mk_var(&mut ctx, "x_s38b");
        let x2 = mk_var(&mut ctx, "x2_s38b");
        let w = mk_var(&mut ctx, "w_s38b");
        let merge_lit = Lit::new(Var::new(1), true);
        let pn = eq.intern(p);
        let qn = eq.intern(q);
        let _ = eq.merge(pn, qn, EqJust::Asserted(merge_lit));
        let eqn_lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(eqn_lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[p, x, x2],
            &[q, w],
            just,
            eqn_lit,
            &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Saturated),
            "generic F-split reached through an EUF-door strip must downgrade to Saturated, got {r:?}"
        );
        assert!(
            emitted.is_empty(),
            "downgrade must NOT record the dedup key"
        );
    }

    /// Slice 38: the guard keys on the EUF door specifically, NOT on stripping
    /// in general. An IDENTITY strip (same TermId `x` cancels against `x`) pushes
    /// no leaf, so `just` does not grow and the residual char-peel split still
    /// fires. Pins that the guard does not over-fire (correct at base AND fix).
    #[test]
    fn identity_strip_split_still_emits() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = mk_var(&mut ctx, "x_s38c");
        let y = mk_var(&mut ctx, "y_s38c");
        let y2 = mk_var(&mut ctx, "y2_s38c");
        let b = ctx.mk_string_const("b");
        let eqn_lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(eqn_lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        // Head strip cancels x against x (identity door → no `just` growth);
        // residual [y, y2] = ["b"] char-peels on (y, "b").
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[x, y, y2],
            &[x, b],
            just,
            eqn_lit,
            &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Split { .. }),
            "an identity-strip F-split must still emit Split (guard must not over-fire), got {r:?}"
        );
    }

    /// Slice 35: a user-declared `|!strk0|` that predates minting must NOT be
    /// adopted as a skolem — `fresh_str` skips user-owned names, so the
    /// minted term is a distinct TermId under the next free name.
    #[test]
    fn fresh_str_skips_user_owned_name() {
        let mut ctx = Context::new();
        let user = declare_str_var(&mut ctx, "!strk0");
        let mut ctr = 0u32;
        let minted = fresh_str(&mut ctx, &mut ctr);
        assert_ne!(
            minted, user,
            "minting must never hash-cons onto a pre-declared user |!strk0|"
        );
        assert!(
            ctx.lookup_symbol("!strk1").is_some(),
            "the mint must have landed on the next free name !strk1"
        );
        assert_eq!(ctr, 2, "counter passed the taken name and the minted one");
    }

    /// Slice 35: a minted `!strk` name is reserved. The user-owned name from
    /// the skip case is NOT reserved.
    ///
    /// **Final-review caveat:** the reservation does NOT reject a later user
    /// declaration at parse time for this mint — that overstates it. Every
    /// `fresh_str` mint reached via `check_sat` runs on a CLONE of the
    /// context (`Solver::check_sat` clones `self.ctx` into the theory
    /// Combiner, `crates/shinri-solver/src/lib.rs:711`), so the reservation
    /// dies with the discarded clone before the parser ever sees it — unlike
    /// word_norm's `ite!` regime, which genuinely rejects because it mints
    /// on `self.ctx` pre-clone (`lib.rs:384`). Here `reserve_symbol` is
    /// defense-in-depth guarding a future refactor that moves this mint to
    /// run pre-clone, not the mechanism that currently blocks aliasing (see
    /// `fresh_str`'s doc comment above for the full correction).
    #[test]
    fn fresh_str_reserves_minted_name_only() {
        let mut ctx = Context::new();
        let _user = declare_str_var(&mut ctx, "!strk0");
        let mut ctr = 0u32;
        let _minted = fresh_str(&mut ctx, &mut ctr);
        let user_sym = ctx.lookup_symbol("!strk0").unwrap();
        let minted_sym = ctx.lookup_symbol("!strk1").unwrap();
        assert!(
            !ctx.is_reserved(user_sym),
            "the user-owned name must stay a normal free constant"
        );
        assert!(
            ctx.is_reserved(minted_sym),
            "the minted name must be reserved against later user declaration"
        );
    }

    /// T4b regression test (task-4-blocker-diagnosis.md, 2026-07-20): a
    /// residual `[!strk1] = [!strk0]` — BOTH atoms MINTED char-peel/F-split
    /// skolems, named exactly the way `fresh_str` brands them — must NOT
    /// propagate. Merging two skolems directly into EUF replaces the F-split
    /// the model builder needs and corrupts model construction (see the
    /// skolem-exclusion comment on the alias case above). Before the T4b fix
    /// this fired `Propagate`; after, it must fall through to the F-split
    /// (i.e. NOT `Propagate`).
    #[test]
    fn skolem_skolem_residual_does_not_propagate() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        // Declared the same way `fresh_str` mints them: nullary symbols named
        // `!strk<N>`.
        let strk1 = declare_str_var(&mut ctx, "!strk1");
        let strk0 = declare_str_var(&mut ctx, "!strk0");
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx,
            &mut eq,
            &[strk1],
            &[strk0],
            just,
            lit,
            &mut ctr,
            &mut emitted,
        );
        assert!(
            !matches!(r, StepResult::Propagate { .. }),
            "a skolem-skolem residual must NOT propagate — it must fall through \
             to the F-split (T4b: propagating it corrupts model construction)"
        );
    }

    /// Final-review pin: a MIXED residual — one input variable, one minted
    /// `!strk*` skolem — must NOT propagate either. The T4b guard
    /// (`!is_minted_skolem(l) && !is_minted_skolem(r)`) excludes a residual
    /// as soon as EITHER atom is a minted skolem, not only the skolem-skolem
    /// shape `skolem_skolem_residual_does_not_propagate` above pins. This is
    /// a deliberate scope decision — the T4b diagnosis only demonstrated
    /// corruption for skolem-skolem residuals, so the mixed pair's exclusion
    /// was a choice, not something the diagnosis forced. Pins both
    /// orientations.
    #[test]
    fn mixed_var_skolem_residual_does_not_propagate() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        // Input variable, declared the same way every other test in this
        // module declares one.
        let x = declare_str_var(&mut ctx, "x_mixed");
        // Minted skolem, named exactly the way `fresh_str` brands one —
        // mirrors `skolem_skolem_residual_does_not_propagate` above.
        let strk0 = declare_str_var(&mut ctx, "!strk0");
        let lit = dummy_eqn_lit();

        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r1 = resolve_equation(
            &mut ctx,
            &mut eq,
            &[x],
            &[strk0],
            vec![EqLeaf::Asserted(lit)],
            lit,
            &mut ctr,
            &mut emitted,
        );
        assert!(
            !matches!(r1, StepResult::Propagate { .. }),
            "a mixed var-skolem residual [x] = [!strk0] must NOT propagate — \
             mixed pairs are deliberately excluded by the T4b guard (either \
             atom being a minted skolem is enough), not just the skolem-skolem \
             shape"
        );

        // Symmetric orientation: the EUF merge is symmetric, so the guard
        // must reject the pair regardless of which side the skolem lands on.
        let mut ctr2 = 0u32;
        let mut emitted2 = FxHashSet::default();
        let r2 = resolve_equation(
            &mut ctx,
            &mut eq,
            &[strk0],
            &[x],
            vec![EqLeaf::Asserted(lit)],
            lit,
            &mut ctr2,
            &mut emitted2,
        );
        assert!(
            !matches!(r2, StepResult::Propagate { .. }),
            "the symmetric orientation [!strk0] = [x] must NOT propagate \
             either — mixed pairs are deliberately excluded, not forced by \
             the T4b diagnosis"
        );
    }

    // ── Slice 14 root-fix: single-variable forced-length analysis ────────────
    // When one side is fully constant and the other is a single (possibly
    // repeated) variable interleaved with constants, the variable length is
    // FORCED; tiling at that length decides the pattern exactly.

    // `u ++ u = "bc"`: |u| forced to 1; the two occurrences map to "b" and "c"
    // → UNSAT (z3: unsat). Was a sound Unknown before this fix.
    #[test]
    fn repeated_var_forced_length_mismatch_is_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let u = mk_var(&mut ctx, "u_rv1");
        let bc = ctx.mk_string_const("bc");
        let lhs = [u, u];
        let rhs = [bc];
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
            matches!(result, StepResult::Conflict(_)),
            "u++u=\"bc\" forces |u|=1 with u=\"b\" and u=\"c\": UNSAT"
        );
    }

    // `u ++ "z" ++ u = "bzc"`: the str.replace_all symbolic-u shape → UNSAT.
    #[test]
    fn repeated_var_with_gap_forced_length_is_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let u = mk_var(&mut ctx, "u_rv2");
        let z = ctx.mk_string_const("z");
        let bzc = ctx.mk_string_const("bzc");
        let lhs = [u, z, u];
        let rhs = [bzc];
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
            matches!(result, StepResult::Conflict(_)),
            "u++\"z\"++u=\"bzc\" forces u=\"b\" and u=\"c\": UNSAT"
        );
    }

    // SAT guard: `u ++ u = "aa"` → |u|=1, both windows "a": consistent, NOT conflict.
    #[test]
    fn repeated_var_consistent_windows_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let u = mk_var(&mut ctx, "u_rv3");
        let aa = ctx.mk_string_const("aa");
        let lhs = [u, u];
        let rhs = [aa];
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
            "u++u=\"aa\" is SAT (u=\"a\"); must not conflict"
        );
    }

    // "Same variable" via a genuine EUF MERGE of DISTINCT TermIds (not literal
    // TermId reuse): `u1 ++ "z" ++ u2` with `u1 = u2` asserted in the
    // EqualityEngine collapses to the repeated-variable shape `u++"z"++u="bzc"`
    // → the merged variable is forced to "b" and "c" ⟹ UNSAT. Exercises the
    // safety-critical `same(terms, eq, a, v)` classification branch.
    #[test]
    fn same_var_via_euf_merge_forced_length_is_conflict() {
        use shinri_theory::types::EqJust;
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let u1 = mk_var(&mut ctx, "u1_merge");
        let u2 = mk_var(&mut ctx, "u2_merge");
        // Merge u1 = u2: distinct TermIds, same equivalence class.
        let n1 = eq.intern(u1);
        let n2 = eq.intern(u2);
        let _ = eq.merge(n1, n2, EqJust::Definitional);
        let z = ctx.mk_string_const("z");
        let bzc = ctx.mk_string_const("bzc");
        let lhs = [u1, z, u2];
        let rhs = [bzc];
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
            matches!(result, StepResult::Conflict(_)),
            "u1++\"z\"++u2 with u1=u2 (EUF) collapses to u++\"z\"++u=\"bzc\": UNSAT"
        );
    }

    // SOUNDNESS guard: DISTINCT variables `u ++ w = "bc"` → SAT (u="b", w="c").
    // Two distinct variables are NOT this pattern; must NOT conflict.
    #[test]
    fn distinct_vars_forced_length_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let u = mk_var(&mut ctx, "u_rv4");
        let w = mk_var(&mut ctx, "w_rv4");
        let bc = ctx.mk_string_const("bc");
        let lhs = [u, w];
        let rhs = [bc];
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
            "u++w=\"bc\" is SAT (u=\"b\", w=\"c\"); distinct vars must not conflict"
        );
    }

    // SAT guard: single occurrence `u ++ "c" = "bc"` → SAT (u="b"); NOT conflict.
    #[test]
    fn single_var_occurrence_not_conflict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let u = mk_var(&mut ctx, "u_rv5");
        let c = ctx.mk_string_const("c");
        let bc = ctx.mk_string_const("bc");
        let lhs = [u, c];
        let rhs = [bc];
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
            "u++\"c\"=\"bc\" is SAT (u=\"b\"); single occurrence must not conflict"
        );
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
