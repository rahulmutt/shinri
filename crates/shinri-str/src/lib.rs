mod collect;
mod fuel;
pub mod indexof_replace;
pub mod int_conv;
mod length;
pub mod model;
pub mod normalize;
pub mod predicates;
pub mod reduce;
mod trail;
pub mod wordeq;
pub use fuel::Fuel;

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, TermNode, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::{ENodeId, EqLeaf};
use shinri_theory::{EqualityEngine, Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct StrSolver {
    /// Asserted string equalities: (atom, the literal that asserted it).
    /// The `Lit` is used to build `EqLeaf::Asserted` justifications for conflicts.
    eq_true: Vec<(TermId, Lit)>,
    diseq_true: Vec<(TermId, Lit)>,
    /// SAT decision level at which each `eq_true` / `diseq_true` entry was asserted
    /// (parallel, index-for-index; truncated together on `pop`). Level 0 ⟹ the
    /// (dis)equality is UNCONDITIONALLY entailed (a top-level fact); level > 0 ⟹ it
    /// is only CONDITIONALLY active (selected inside a disjunction at a decision).
    /// Used by `check` to gate MERGE-DERIVED length lemmas (E1): those lemmas read
    /// the live EUF class map / deep normal forms, so their content is only valid
    /// given the currently-active merges. Emitted GLOBALLY (guard `¬eq` or, for the
    /// `next_axiom` defining axiom, guard `None`), such a lemma is unsound on a
    /// backtracked branch unless every contributing merge is unconditional. We emit
    /// them only when NO conditional string (dis)equality is active.
    eq_levels: Vec<u32>,
    diseq_levels: Vec<u32>,
    len_terms: FxHashSet<TermId>,
    str_terms: FxHashSet<TermId>,
    emitted_len_axioms: FxHashSet<TermId>,
    /// Dedup set for F-splits: keyed on the canonical (unordered) head pair.
    /// Monotone (never cleared on backtrack); prevents re-emitting the same
    /// split after dedup (termination guarantee).
    emitted_splits: FxHashSet<(TermId, TermId)>,
    /// String-equality atoms MINTED by the word-equation search itself (the
    /// F-split `a = b++z` / char-peel `v = h++z` / `v = ""` disjuncts), as
    /// opposed to equalities present in the reduced INPUT assertions. These carry
    /// fresh skolem remainders and are re-minted every round, so the per-concat
    /// length link is deliberately NOT emitted for them (see the length-link loop
    /// and the historical unsound-conflict note there). Monotone: recorded at the
    /// moment a split is emitted, before the disjunct can be asserted back.
    minted_eqs: FxHashSet<TermId>,
    /// Counter for fresh string skolem variables minted by F-split.
    fresh_ctr: u32,
    fuel: Fuel,
    trail: trail::Trail,
}

impl TheorySolver for StrSolver {
    const THEORY_ID: u16 = 4;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        let mut seen = FxHashSet::default();
        collect::collect(
            cx.terms,
            atom,
            &mut self.len_terms,
            &mut self.str_terms,
            &mut seen,
        );
    }

    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        // Record asserted string (dis)equalities for consumption by Task 11+.
        // Gate on the operands being String-sorted so non-string equalities
        // (e.g. integer or bitvector) cannot pollute eq_true/diseq_true.
        let atom = cx.atoms.atom(lit.var());
        // Decision level at which this literal is being asserted (E1 gate): the
        // number of open trail scopes. Recorded parallel to eq_true/diseq_true so
        // `check` can tell a top-level (dl0) equality from a conditional (dl>0) one.
        let lvl = self.trail.level();
        if let TermNode::App { op, args, .. } = cx.terms.term_node(atom) {
            let args = cx.terms.children(*args).to_vec();
            let is_str_eq = !args.is_empty() && cx.terms.sort_of(args[0]) == cx.terms.string_sort();
            if is_str_eq {
                // Direction: `Eq` positive / `Distinct` negative ⟹ equality; the
                // opposite polarities ⟹ disequality.
                let is_eq = match op {
                    Op::Builtin(BuiltinOp::Eq) => Some(lit.is_positive()),
                    Op::Builtin(BuiltinOp::Distinct) => Some(!lit.is_positive()),
                    _ => None,
                };
                match is_eq {
                    Some(true) => {
                        self.eq_true.push((atom, lit));
                        self.eq_levels.push(lvl);
                    }
                    Some(false) => {
                        self.diseq_true.push((atom, lit));
                        self.diseq_levels.push(lvl);
                    }
                    None => {}
                }
            }
        }
        None
    }

    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        None
    }

    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }

        // E1 iterations 2/3 — MERGE-DERIVED length lemmas & same-word conflicts must not
        // be emitted GLOBALLY (guard=None, or a conflict/split cited only by the trigger)
        // when their content reads a BRANCH-LOCAL merge — a merge some (dis)equality
        // asserted at decision level > 0 produced (a decided INPUT disjunct OR the word-
        // equation search's own minted F-split/char-peel). Over such a merge the global
        // clause survives backtracking and over-constrains the sibling branch → the
        // wrong-UNSAT class (ce1..ce8, all also wrong at base). iter-2 gated this with
        // COARSE flags (skip whenever ANY conditional (dis)equality was active anywhere);
        // iter-3 makes every gate ANTECEDENT-PRECISE via the `lit_lvl` / `cond_roots` /
        // per-lemma `eq.explain` infrastructure below, so an UNRELATED conditional
        // (dis)equality no longer forfeits a decidable verdict. The post-solve model gate
        // (Fix B) remains the backstop; the per-equation length LINK stays unconditional
        // (`¬eq ∨ len(l)=len(r)` over the equality's OWN sides is a pure tautology).

        // ── E1 (iter 3) ANTECEDENT-PRECISE gating ────────────────────────────────
        // The coarse flags above skip a merge-derived GLOBAL lemma whenever ANY
        // conditional (dis)equality is active anywhere — even when the SPECIFIC merges
        // that lemma's content reads are all dl0 and only an UNRELATED equality is
        // conditional. That needlessly forfeits decidable verdicts. The precise test:
        // a global lemma is unconditionally valid iff every antecedent its content
        // actually depends on (the triggering (dis)equality, plus each EUF merge that
        // `normal_form`/`deep_normal_form`/`same()` traverses to substitute a term by
        // its class representative) is recorded at decision level 0.
        //
        // `lit_lvl` maps each currently-asserted string (dis)equality literal to the
        // decision level it was asserted at (0 = top-level / unconditional). A merge's
        // antecedents are the `EqLeaf::Asserted` proof-forest leaves `eq.explain`
        // returns; a merge is "dl0-entailed" iff every such leaf is a level-0 literal
        // (an `Interface` leaf is cross-theory — its level is unknown here, so it is
        // treated conservatively as conditional).
        let mut lit_lvl: FxHashMap<Lit, u32> = FxHashMap::default();
        let mut minted_lits: FxHashSet<Lit> = FxHashSet::default();
        for (i, &(atom, l)) in self.eq_true.iter().enumerate() {
            lit_lvl.insert(l, *self.eq_levels.get(i).unwrap_or(&u32::MAX));
            if self.minted_eqs.contains(&atom) {
                minted_lits.insert(l);
            }
        }
        for (i, &(atom, l)) in self.diseq_true.iter().enumerate() {
            lit_lvl.insert(l, *self.diseq_levels.get(i).unwrap_or(&u32::MAX));
            if self.minted_eqs.contains(&atom) {
                minted_lits.insert(l);
            }
        }

        // CONDITIONAL-CLASS ROOTS. A term whose EUF class root is in one of these
        // sets sits in a class a CONDITIONAL (dl>0) (dis)equality merged, so its
        // `normal_form` substitution may be branch-local. A lemma reading only terms
        // OUTSIDE these sets used no conditional merge (precise replacement for the
        // blanket "any conditional active" flags).
        //   * `input_cond_roots` — classes touched by a conditional INPUT (non-minted)
        //     (dis)equality (a disjunct decided at dl>0). Gates channels that must stay
        //     branch-independent but may run over the search's OWN minted disjuncts.
        //   * `all_cond_roots` — additionally classes touched by a MINTED F-split /
        //     char-peel disjunct. Gates the GLOBAL same-word conflicts, whose citation
        //     over a minted-skolem merge is not guaranteed complete.
        // (An unconditional (dl0) equality contributes to NEITHER — its merge is
        // globally entailed, so terms it touches stay resolvable.)
        let mut input_cond_roots: FxHashSet<ENodeId> = FxHashSet::default();
        let mut all_cond_roots: FxHashSet<ENodeId> = FxHashSet::default();
        {
            let mut cond: Vec<(TermId, bool)> = Vec::new(); // (atom, is_minted)
            for (i, &(atom, _)) in self.eq_true.iter().enumerate() {
                if *self.eq_levels.get(i).unwrap_or(&u32::MAX) > 0 {
                    cond.push((atom, self.minted_eqs.contains(&atom)));
                }
            }
            for (i, &(atom, _)) in self.diseq_true.iter().enumerate() {
                if *self.diseq_levels.get(i).unwrap_or(&u32::MAX) > 0 {
                    cond.push((atom, self.minted_eqs.contains(&atom)));
                }
            }
            for (atom, minted) in cond {
                let (a, b) = crate::wordeq::diseq_sides(cx.terms, atom);
                for side in [a, b] {
                    let n = cx.eq.intern(side);
                    let r = cx.eq.find(n);
                    all_cond_roots.insert(r);
                    if !minted {
                        input_cond_roots.insert(r);
                    }
                }
            }
        }

        // ── E1 (iter 3) side_clean / cond_roots SOUNDNESS INVARIANT (debug-only) ──
        // Antecedent precision is sound because: a conditional (dl>0) merge of a string
        // LEAF variable is caused by a TRACKED (dis)equality — an `eq_true`/`diseq_true`
        // entry — whose sides we just added to `cond_roots`; since every member of an
        // EUF class shares one root, a conditionally-merged leaf's root is therefore in
        // `cond_roots`, so `side_clean` flags it. The load-bearing premise is that a
        // string leaf is NEVER merged by an UNTRACKED mechanism (a merge with no
        // corresponding `eq_true`/`diseq_true` literal): if it were AND that merge were
        // branch-local, `cond_roots` would miss it and `side_clean` could wrongly pass.
        // We pin the WEAKEST sound approximation that catches such a violation: every
        // `EqLeaf::Asserted` antecedent of any string leaf's merge-to-root is a literal
        // we track in `lit_lvl` (so its decision level — hence its cond_roots membership
        // when dl>0 — is known). `Interface` leaves would signal a cross-theory merge of
        // a string leaf, which does not occur in this fragment (the N-O seam exchanges
        // only Int length terms, never string-leaf equalities); we assert their absence
        // too, so a future seam change that violates the premise trips here rather than
        // silently at a later wrong-UNSAT. Debug-only: no release cost, no verdict change.
        #[cfg(debug_assertions)]
        {
            let leaves: Vec<TermId> = self
                .str_terms
                .iter()
                .copied()
                .filter(|&t| {
                    matches!(
                        cx.terms.term_node(t),
                        TermNode::App { op: Op::Uninterpreted(_), args, .. }
                            if cx.terms.children(*args).is_empty()
                    )
                })
                .collect();
            for t in leaves {
                let tn = cx.eq.intern(t);
                let rn = cx.eq.find(tn);
                if tn == rn {
                    continue; // canonical node of its class: its merges surface from the
                              // non-canonical members, which are checked in turn.
                }
                let mut ante = Vec::new();
                cx.eq.explain(tn, rn, &mut ante);
                for leaf in &ante {
                    match leaf {
                        EqLeaf::Asserted(l) => debug_assert!(
                            lit_lvl.contains_key(l),
                            "side_clean invariant violated: string leaf {t:?} is merged by \
                             UNTRACKED literal {l:?} — cond_roots may miss a conditional merge",
                        ),
                        EqLeaf::Interface(_) => debug_assert!(
                            false,
                            "side_clean invariant violated: string leaf {t:?} merged via a \
                             cross-theory Interface antecedent — cond_roots cannot level-check it",
                        ),
                    }
                }
            }
        }

        // Build the `known` set FIRST: all string-sorted subterms visible to the
        // solver, plus both sides of each asserted equality.
        // This must be built before the len_terms loop so `next_axiom` can consult
        // EUF representatives (e.g. to detect that `str.len(x) = 0` when `x = ""`
        // was merged via the EqualityEngine — the N-O length seam).
        let mut known: Vec<TermId> = self.str_terms.iter().copied().collect();
        for &(atom, lit) in &self.eq_true {
            // `eq_true` may hold a `Distinct` atom asserted FALSE (¬distinct ≡ eq);
            // `diseq_sides` accepts both `Eq` and `Distinct` operands.
            let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);
            known.push(l);
            known.push(r);
            // Direct distinct-constant contradiction: an equality between two
            // DIFFERENT string literals is UNSAT. Must be caught BEFORE normalization
            // (once the EUF merges l≈r, `normal_form` substitutes both to one
            // representative and the mismatch disappears → wrong SAT, e.g. `(= "a" "b")`).
            if let (Some(ls), Some(rs)) = (
                cx.terms.string_const_value(l),
                cx.terms.string_const_value(r),
            ) {
                if ls != rs {
                    return TCheck::Conflict(vec![EqLeaf::Asserted(lit)]);
                }
            }
        }

        // TRANSITIVE distinct-constant contradiction: any EUF class (over the known
        // string terms) containing two DIFFERENT string literals was forced equal
        // (e.g. `x="a" ∧ x="b"` merges "a"≈x≈"b") → UNSAT. `normal_form` would pick
        // one constant representative and hide the clash, so detect it explicitly.
        if let Some((ca, cb)) = first_distinct_const_clash(cx.terms, cx.eq, &known) {
            let an = cx.eq.intern(ca);
            let bn = cx.eq.intern(cb);
            let mut just = Vec::new();
            cx.eq.explain(an, bn, &mut just);
            return TCheck::Conflict(just);
        }

        // Per-equation length lemma: `l = r → len(l) = len(r)`, emitted via arith
        // Ge/Le companions guarded by ¬eq. Required so e.g. `s1 = s2` forces
        // `len(s1) = len(s2)` in arith (string equality merges s1≈s2 in EUF, but
        // str.len is not an EUF congruence function here, so arith would otherwise
        // assign inconsistent lengths → a non-satisfying model). SAFE for atom
        // equalities (no fresh concat skolems, so it does not feed the unbounded
        // String↔Arith MBTC).
        //
        // Emitted for a CONCAT-sided equality ONLY when the equality is an INPUT
        // assertion (its atom is NOT in `minted_eqs`) — Task 7.5. This closes the
        // wrong-SAT on e.g. `s = "ab"++k ∧ len(s)=1`: without the link `len(s)`
        // floats free in arith (an opaque-var length gets no defining axiom, and
        // the var-headed word equation solves trivially), so arith SATs `len(s)=1`
        // while `len("ab"++k) ≥ 2`. Emitting `len(s)=len("ab"++k)` feeds the
        // existing length-defining fixpoint (`len("ab"++k)=len("ab")+len(k)=2+len(k)
        // ≥ 2`) → arith UNSAT.
        //
        // NOT emitted for a concat-sided equality that the word-equation search
        // MINTED (`minted_eqs`): those are the F-split disjuncts `a = b++z` / char-
        // peel `v = h++z`, re-minted with a FRESH skolem `z` every round. A per-
        // concat length link over them both floods the seam (unbounded fresh
        // `str.len(skolem)` terms) AND, interacting with the length-defining axioms
        // over those skolems, produced the historically-documented unsound conflict.
        // Restricting to input equalities keeps emission FINITE (a fixed set of
        // input equations, companions deduped via `emitted_len_axioms`) and mints NO
        // fresh skolems (a concat's parts already exist; their `str.len` terms feed
        // the existing axiom fixpoint) — so neither the flood nor the skolem
        // interaction can arise. Concat length contradictions that need no fresh
        // terms are still ALSO caught directly in `resolve_equation` by the
        // constant-length bound check (e.g. `s2++"ba" = "b"`).
        {
            let eqs: Vec<(TermId, Lit)> = self.eq_true.clone();
            for (atom, lit) in eqs {
                let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);
                // Skip ANY equality minted by the word-equation search (its F-split /
                // char-peel disjuncts carry fresh skolems). NOTE (E1): the original
                // guard only skipped a CONCAT-sided minted equality, so the char-peel
                // empty branch `v = ""` (neither side a concat) slipped through and
                // got a `len(v)=0` link — one of the under-cited minted-skolem length
                // constraints that, combined across branches, drove the two-suffixof
                // spurious UNSAT. Gate on `minted_eqs` membership alone.
                if self.minted_eqs.contains(&atom) {
                    continue;
                }
                if cx.terms.string_const_value(l).is_some()
                    && cx.terms.string_const_value(r).is_some()
                {
                    continue; // two literals: lengths already pinned constants
                }
                let ll = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrLen), &[l])
                    .expect("len l");
                let lr = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrLen), &[r])
                    .expect("len r");
                self.len_terms.insert(ll);
                self.len_terms.insert(lr);
                if ll == lr {
                    continue;
                }
                let len_eq = cx.terms.mk_eq(ll, lr).expect("(= len(l) len(r))");
                let (ge, le) = length::arith_eq_companions(cx.terms, len_eq)
                    .expect("len_eq is an arith equality");
                for comp in [ge, le] {
                    if self.emitted_len_axioms.contains(&comp) {
                        continue;
                    }
                    self.emitted_len_axioms.insert(comp);
                    if !self.fuel.spend() {
                        return TCheck::Unknown;
                    }
                    let mut seen = FxHashSet::default();
                    collect::collect(
                        cx.terms,
                        comp,
                        &mut self.len_terms,
                        &mut self.str_terms,
                        &mut seen,
                    );
                    return TCheck::Split {
                        atoms: vec![comp],
                        guard: Some(lit.negate()),
                    };
                }
            }
        }

        // Per-len-term defining axioms. `next_axiom` returns arith-friendly atoms:
        // `(>= len 0)` and the defining equation's `(>= )` / `(<= )` companions
        // (a bare Int equality would route to EUF, not Arith — see length.rs).
        let lens: Vec<TermId> = self.len_terms.iter().copied().collect();
        for lt in lens {
            // E1 (iter 3): `next_axiom` resolves an opaque variable's length through
            // its EUF class CONSTANT (`x ≈ "a"` ⟹ `len(x)=1`) — an UNCONDITIONAL
            // `guard=None` dl0-pinned unit — only when the SPECIFIC `x ≈ const` merge
            // is dl0-entailed (checked ANTECEDENT-PRECISELY inside via `lit_lvl`). Over
            // a branch-local merge it is the wrong-UNSAT channel (ce1/ce3/ce4); an
            // unrelated conditional equality no longer suppresses it. STRUCTURAL axioms
            // (`≥0`, literal length, concat sum) are merge-independent and always emitted.
            if let Some(axiom) = length::next_axiom(
                cx.terms,
                cx.eq,
                &known,
                lt,
                &self.emitted_len_axioms,
                &lit_lvl,
            ) {
                // Register NEW str.len subterms introduced by this axiom so the
                // defining-axiom chain over nested concats continues to a fixpoint.
                let mut seen = FxHashSet::default();
                collect::collect(
                    cx.terms,
                    axiom,
                    &mut self.len_terms,
                    &mut self.str_terms,
                    &mut seen,
                );
                // Spend fuel FIRST; only record the axiom as emitted if the split is
                // actually delivered (tracks only delivered axioms invariant).
                if !self.fuel.spend() {
                    return TCheck::Unknown;
                }
                self.emitted_len_axioms.insert(axiom);
                return TCheck::Split {
                    atoms: vec![axiom],
                    guard: None,
                };
            }
        }

        // (The empty-length link is enforced in the disequality loop below via
        // `len_class_zero`: a read of the shared engine rather than an emitted
        // lemma, so it cannot flood the String↔Arith N-O seam.)

        // Word-equation resolution: strip equal heads/tails, detect constant
        // prefix mismatches and occurs-check contradictions. Variable-headed
        // residuals emit F-splits (Task 12).
        let eqs: Vec<(TermId, Lit)> = self.eq_true.clone();
        for (atom, lit) in eqs {
            // `eq_true` may hold a `Distinct` asserted FALSE (¬distinct ≡ eq).
            let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);
            // Single-level normal forms for the CONFLICT/SPLIT path (NOT deep: deep
            // expansion substitutes merge-derived material whose antecedents the
            // ground resolver does not cite, so a branch-local contradiction would
            // be reported as a GLOBAL conflict — unsound). To stay within that
            // single-level regime, `resolve_equation` refuses to F-split / char-peel
            // an UNFLATTENED concat class representative (it Saturates instead — the
            // opaque-concat split is the F1 divergence that yielded a spurious
            // UNSAT). Model reconstruction uses the deep view in model.rs.
            let lhs = crate::normalize::normal_form(cx.terms, cx.eq, &known, l);
            let rhs = crate::normalize::normal_form(cx.terms, cx.eq, &known, r);

            // Empty-residual lemma (sound, model-preserving). After cancelling the
            // common prefix/suffix, if ONE side's residual is empty and the other is
            // entirely variables (no non-empty constant), then EACH of those variables
            // must be empty: `eq → (Σ len(vars) ≤ 0)`. This pins e.g. the self-
            // referential `s1 = s0 ++ s1` (suffix-cancel `s1` ⟹ `"" = s0` ⟹ `s0=""`),
            // whose single-level resolver otherwise returns Done (SAT) and leaves the
            // model builder free to assign `s0` a non-empty value — yielding a witness
            // that does NOT satisfy the equation (a wrong model). Forcing the residual
            // length to 0 makes every SAT model satisfy the equation. Guarded by `¬eq`
            // and deduped via `emitted_len_axioms`; `Σlen ≤ 0` adds no fresh skolems.
            {
                use crate::wordeq::same;
                let (mut i, mut j) = (0usize, 0usize);
                let (mut le2, mut re2) = (lhs.len(), rhs.len());
                while i < le2 && j < re2 && same(cx.terms, cx.eq, lhs[i], rhs[j]) {
                    i += 1;
                    j += 1;
                }
                while le2 > i && re2 > j && same(cx.terms, cx.eq, lhs[le2 - 1], rhs[re2 - 1]) {
                    le2 -= 1;
                    re2 -= 1;
                }
                let l_res = &lhs[i..le2];
                let r_res = &rhs[j..re2];
                let other: Option<&[TermId]> = if l_res.is_empty() && !r_res.is_empty() {
                    Some(r_res)
                } else if r_res.is_empty() && !l_res.is_empty() {
                    Some(l_res)
                } else {
                    None
                };
                if let Some(vars) = other {
                    // Every residual atom must be a genuine string VARIABLE (an
                    // uninterpreted nullary symbol). A residual atom may be:
                    //   * a non-empty CONSTANT — then `Σlen ≤ 0` is plainly wrong
                    //     (already excluded by `string_const_value(a).is_none()`); OR
                    //   * a CONCAT term — `normal_form`/`rep()` can substitute a
                    //     residual variable by a concat-valued class representative
                    //     (e.g. via a self-referential merge `s1 ≈ s1·s1·s2` whose
                    //     rep chain surfaces `(s2·"bb")·z`). That concat is NOT a
                    //     string constant, so the old `string_const_value` check let
                    //     it through, and `len(concat) ≤ 0` over a concat that
                    //     contains the non-empty constant "bb" forced `2 ≤ 0` — a
                    //     SPURIOUS UNSAT (the documented wrong-UNSAT class). A concat
                    //     residual carries hidden mandatory constant length, so the
                    //     empty-residual lemma is unsound over it. Require each atom
                    //     be a bare uninterpreted variable; if any is a concat (or
                    //     other compound), SKIP the lemma (fall through to the bounded
                    //     word-equation machinery → sound Split/Done/Unknown).
                    let all_var = vars.iter().all(|&a| {
                        cx.terms.string_const_value(a).is_none()
                            && matches!(
                                cx.terms.term_node(a),
                                TermNode::App {
                                    op: Op::Uninterpreted(_),
                                    ..
                                }
                            )
                    });
                    // E1: do NOT emit the empty-residual length lemma over a MINTED
                    // (dis)equality (an F-split disjunct). Its residual is computed
                    // from merge-substituted normal forms whose antecedents the
                    // ¬eq guard does not cite; over branch-local minted skolems the
                    // learnt `Σlen ≤ 0` clause is unsound on backtracked branches.
                    // E1 (iter 2): also skip while a conditional INPUT (dis)equality is
                    // active. The residual comes from `normal_form` + `same()` over the
                    // live merges; the globally-learnt `¬eq ∨ Σlen ≤ 0` (which forces the
                    // residual VARS empty) is unsound on the branch where the disjunct
                    // that produced those merges is not selected. Combined with a
                    // separation `Σlen ≥ 1` over a sibling diseq it manufactured a
                    // spurious UNSAT (fuzz seed 13: `(or (= s0·s2 s0) (= s1 s0)) ∧
                    // s2·s1 ≠ s2 ∧ s0 = s0·s0`). Gating THIS channel (not the weaker
                    // separation `≥1`, which a decided disequality-family SAT needs for
                    // its model) breaks the chain while preserving the oracle SAT pins.
                    // E1 (iter 3): precise — emit iff neither side is in a conditional
                    // class (`all_cond_roots`: input disjunct OR minted split). This
                    // `Σlen ≤ 0` forces residual vars empty, so it must not read any
                    // branch-local merge; but an UNRELATED conditional (dis)equality no
                    // longer blocks it (recovers decisiveness over the old blanket gate).
                    if all_var
                        && !self.minted_eqs.contains(&atom)
                        && side_clean(cx.eq, cx.terms, l, &all_cond_roots)
                        && side_clean(cx.eq, cx.terms, r, &all_cond_roots)
                    {
                        let int_s = cx.terms.int_sort();
                        let len_atoms: Vec<TermId> = vars
                            .iter()
                            .map(|&a| {
                                cx.terms
                                    .mk_app(Op::Builtin(BuiltinOp::StrLen), &[a])
                                    .expect("str.len(var) well-sorted")
                            })
                            .collect();
                        let sum = if len_atoms.len() == 1 {
                            len_atoms[0]
                        } else {
                            cx.terms
                                .mk_app(Op::Builtin(BuiltinOp::Add), &len_atoms)
                                .expect("(+ len ...) well-sorted")
                        };
                        let zero = cx
                            .terms
                            .mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
                        let le_atom = cx
                            .terms
                            .mk_app(Op::Builtin(BuiltinOp::Le), &[sum, zero])
                            .expect("(<= Σlen 0) well-sorted");
                        if !self.emitted_len_axioms.contains(&le_atom) {
                            self.emitted_len_axioms.insert(le_atom);
                            for &la in &len_atoms {
                                self.len_terms.insert(la);
                            }
                            if !self.fuel.spend() {
                                return TCheck::Unknown;
                            }
                            let mut seen = FxHashSet::default();
                            collect::collect(
                                cx.terms,
                                le_atom,
                                &mut self.len_terms,
                                &mut self.str_terms,
                                &mut seen,
                            );
                            return TCheck::Split {
                                atoms: vec![le_atom],
                                guard: Some(lit.negate()),
                            };
                        }
                    }
                }
            }

            // E1 (iter 2): the word-equation Conflict/Split are derived from the
            // SINGLE-LEVEL normal forms `lhs`/`rhs`, which substitute EUF class
            // representatives — including CONSTANT substitutions from a currently-
            // active merge (e.g. a decided disjunct `s0="y"` rewrites `"x"++s0`'s
            // normal form to `"xy"`). When a conditional (dl>0) string (dis)equality
            // is active, that substitution is branch-local, but the emitted Conflict
            // cites only `EqLeaf::Asserted(lit)` (the equation literal) and the F-split
            // is guarded only by `¬eqn` — NEITHER cites the merge antecedent. Learnt
            // globally, such a Conflict/Split is unsound on the branch where the
            // merge-producing disjunct is not selected (ce2: the `s0="y"` disjunct's
            // head-mismatch conflict kills the `s0=s1` branch → wrong global UNSAT).
            // E1 (iter 3) ANTECEDENT-PRECISE: resolve this word equation iff neither
            // side sits in a class an INPUT disjunct (dl>0) merged — i.e. the
            // single-level normal forms `lhs`/`rhs` are branch-independent w.r.t.
            // external disjunctions (`side_clean(input_cond_roots)`). This replaces the
            // coarse "no conditional INPUT (dis)equality ANYWHERE" gate: an unrelated
            // disjunction over OTHER variables no longer disables resolution here. The
            // search's OWN minted disjuncts are deliberately NOT in `input_cond_roots`,
            // so it keeps resolving them (else a decided dl0 word equation stalls at
            // `unknown`). Unconditional constant clashes are still caught by the
            // (ungated) direct/transitive distinct-const checks above; any SAT this
            // admits is re-validated by the model gate; skipped ⟹ saturated (no
            // fabricated verdict).
            if side_clean(cx.eq, cx.terms, l, &input_cond_roots)
                && side_clean(cx.eq, cx.terms, r, &input_cond_roots)
            {
                // Build the EqLeaf justification from the asserted equality literal.
                // This feeds `expand_conflict` so the conflict clause cites the right
                // input literal. `resolve_equation` never derives a ground conflict from
                // a variable it substituted by a concat class representative (it
                // Saturates on a concat residual head instead — see wordeq.rs), so no
                // extra merge-antecedent citation is needed here.
                let just = vec![EqLeaf::Asserted(lit)];
                match crate::wordeq::resolve_equation(
                    cx.terms,
                    cx.eq,
                    &lhs,
                    &rhs,
                    just,
                    lit,
                    &mut self.fresh_ctr,
                    &mut self.emitted_splits,
                ) {
                    crate::wordeq::StepResult::Conflict(cf) => {
                        // A word-equation Conflict is a GLOBAL fact (`¬eqn` learnt), and
                        // `resolve_equation` cites only `EqLeaf::Asserted(lit)` — not the
                        // merges its normal forms substituted. So it must be emitted only
                        // when the normal forms used NO branch-local merge at all,
                        // including the search's OWN minted skolem merges (`prefixof "a"
                        // (s2·"c")` mints `s2 ≈ "a"·!strk`; a later round's head-mismatch
                        // conflict over that merge, cited by the eq literal alone, kills
                        // sibling branches → wrong-UNSAT, fuzz 966367641601, also wrong at
                        // base). E1 (iter 3): gate ANTECEDENT-PRECISELY on `all_cond_roots`
                        // (input + minted): emit iff neither side touches a conditional
                        // class. This is strictly more permissive than the old global
                        // `no_minted_active` (an unrelated minted split elsewhere no
                        // longer blocks a conflict whose own sides are clean). Declined ⟹
                        // saturated; the model gate backstops and the conflict re-derives
                        // from the clean state on backtrack. F-SPLITS still fire (they add
                        // only guarded branches, never a global fact).
                        if side_clean(cx.eq, cx.terms, l, &all_cond_roots)
                            && side_clean(cx.eq, cx.terms, r, &all_cond_roots)
                        {
                            return TCheck::Conflict(cf);
                        }
                    }
                    crate::wordeq::StepResult::Split { atoms, guard } => {
                        // Register the new str.len terms produced by the F-split so
                        // their length axioms are emitted on the next check round.
                        // The F-split atoms are: [len_eq, a_pref, b_pref].
                        // len_eq = (= (str.len a) (str.len b)); extract the len sub-terms.
                        let mut seen = FxHashSet::default();
                        for &split_atom in &atoms {
                            collect::collect(
                                cx.terms,
                                split_atom,
                                &mut self.len_terms,
                                &mut self.str_terms,
                                &mut seen,
                            );
                            // Mark every minted disjunct (`a = b++z`, `v = h++z`,
                            // `v = ""`) so that once the SAT layer asserts it back into
                            // `eq_true`, the per-concat length link above skips it — it
                            // carries a fresh skolem and must not feed the length seam
                            // (Task 7.5). Recorded HERE, at emission, i.e. strictly
                            // before the disjunct can be asserted (assertion happens
                            // between check rounds), so the guard is always in place by
                            // the time the atom appears in `eq_true`.
                            self.minted_eqs.insert(split_atom);
                        }
                        // Spend one unit of fuel before emitting a word-equation split.
                        // If the budget is exhausted, signal Unknown (sound). The
                        // word-equation search is only semi-decidable; this bounds it.
                        if !self.fuel.spend() {
                            return TCheck::Unknown;
                        }
                        // GUARDED split: `guard = ¬eqn`. The learnt clause is
                        // `¬eqn ∨ len_eq ∨ a_pref ∨ b_pref` ≡ `eqn → (…)`, a valid
                        // implication (Nielsen lemma) — NOT the unsound bare disjunction.
                        return TCheck::Split {
                            atoms,
                            guard: Some(guard),
                        };
                    }
                    crate::wordeq::StepResult::Done => {}
                    // A dedup-saturated variable-headed residual: the SAT layer must
                    // case-split on the already-emitted F-split disjunction to make
                    // progress. Treated like `Done` here (wait for SAT). The (B′)
                    // premature-SAT hazard — concluding SAT with a model that does not
                    // actually satisfy the equation — is caught instead by the post-solve
                    // witness self-check in `Solver::solve` (model-substitution re-check),
                    // which downgrades an unrealisable SAT to a SOUND `Unknown`.
                    crate::wordeq::StepResult::Saturated => {}
                }
            } // end antecedent-precise word-eq resolution gate (E1 iter 3)
        }

        // Disequality same-word conflict check (Task 14).
        //
        // For each asserted `s ≠ t`, compute the normal forms of both sides and
        // check atom-wise equality. If the normal forms are identical (the two sides
        // denote the same word), the disequality is contradicted → Conflict.
        //
        // Soundness: the conflict justification MUST include the disequality literal
        // AND any equality antecedents that caused pairs in the normal forms to be
        // merged in the EqualityEngine (e.g. `x = "a"` was asserted, so `x` and `"a"`
        // appear equal in the normal form). `nf_equal_explain` gathers those
        // antecedents via `eq.explain`, mirroring the EUF conflict pattern in
        // `shinri-euf/src/egraph.rs::conflict_leaves` (the `explain(a, b, out)` path
        // for the merge-antecedent part).
        let diseqs: Vec<(TermId, Lit)> = self.diseq_true.clone();
        for (atom, lit) in diseqs {
            let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);

            // Empty-length link (sound conflict direction): `s ≠ "" ∧ len(s)=0` is
            // UNSAT, because a string of length 0 IS the empty string. We detect it
            // by reading the entailed length from the shared engine: if one side of
            // the disequality is the empty literal and the OTHER side's `str.len` is
            // EUF-equal to 0 (e.g. `(= (str.len s) 0)` was asserted — that Int
            // equality routes to EUF, merging `len(s) ≈ 0`), the disequality is
            // contradicted.
            //
            // Soundness / justification: the conflict cites the diseq literal PLUS
            // `eq.explain(len(s), 0)` — the exact input literals that forced
            // `len(s) ≈ 0` (mirroring the EUF diseq-conflict pattern used in Case 1
            // below and in `egraph.rs::assert_diseq`). The learnt clause is therefore
            // `¬(len(s)=0) ∨ ¬(s≠"")`, a VALID lemma (`len(s)=0 ∧ s≠"" ⟹ ⊥`), so it
            // is model-preserving. Crucially this fires ONLY when an empty-side
            // disequality is present AND the length is entailed to 0 — it adds NO
            // constraint to satisfiable queries where `len(s)` is merely otherwise
            // bounded (e.g. `len(x)=2` with no `x≠""`), so it cannot cause the broad
            // wrong-UNSAT that the eager/guarded forms did at the N-O seam.
            for (empty_side, other) in [(l, r), (r, l)] {
                if cx.terms.string_const_value(empty_side) == Some("") {
                    let len_other = cx
                        .terms
                        .mk_app(Op::Builtin(BuiltinOp::StrLen), &[other])
                        .expect("str.len(other) well-sorted");
                    // Cluster A / #1 (slice 8): a concat whose normal form carries a
                    // non-empty string constant has structural length ≥ 1 and can
                    // NEVER equal "", so `other ≠ ""` is trivially satisfiable — the
                    // empty-length link must NOT conflict it. An arith length axiom can
                    // never entail `len(concat-with-const)=0` (it would force a var's
                    // length negative), so any `len_class_zero` hit here would be a
                    // SPURIOUS unit merge (empty-antecedent conflict) forcing the diseq
                    // false — the wrong-UNSAT this slice closes. Only the genuinely-
                    // entailed-zero case (a bare/const-free side EUF-merged to 0 via an
                    // asserted literal) is a sound conflict, and that path is preserved.
                    if let Some(nf) =
                        crate::normalize::deep_normal_form(cx.terms, cx.eq, &known, other)
                    {
                        if nf.iter().any(|&a| {
                            cx.terms
                                .string_const_value(a)
                                .is_some_and(|s| !s.is_empty())
                        }) {
                            continue;
                        }
                    }
                    if let Some(zero) = len_class_zero(cx.terms, cx.eq, len_other) {
                        let ln = cx.eq.intern(len_other);
                        let zn = cx.eq.intern(zero);
                        let mut just = vec![EqLeaf::Asserted(lit)];
                        cx.eq.explain(ln, zn, &mut just);
                        return TCheck::Conflict(just);
                    }
                }
            }

            // Non-empty separation lemma (sound, model-preserving). After cancelling
            // the common prefix and suffix of the two sides (free-monoid
            // cancellation: `u·L·w ≠ u·R·w ⟺ L ≠ R`), two DISTINCT words cannot both
            // be empty, so the residuals `L`, `R` satisfy the necessary condition
            //   `s ≠ t  →  (Σlen(L) ≥ 1) ∨ (Σlen(R) ≥ 1)`.
            // This forces arith to give at least one residual a non-empty length, so
            // every SAT model genuinely separates the two sides; the both-residuals-
            // empty case becomes a sound CONFLICT (e.g. `s≠t ∧ len(s)=0 ∧ len(t)=0`,
            // or `"b" ≠ "b"++s1++s2` with `s1=s2=""`). Without it, the model builder
            // would assign all the free residual vars `""`, the residuals would
            // coincide, and `s ≠ t` would be VIOLATED — a premature / wrong SAT whose
            // witness fails z3 (the (B′) class). The lemma is a sound NECESSARY (not
            // sufficient) condition: it never rejects a real model — equal-length
            // non-empty residuals that genuinely differ (e.g. "a" vs "b") are
            // separated by the model builder's per-class fill char. It is GUARDED by
            // `¬(s≠t)` (constrains only branches asserting the disequality) and deduped
            // via `emitted_len_axioms`.
            //
            // Skipped when EITHER residual already contains a NON-EMPTY string
            // constant: that residual's length is already ≥ 1, so the disjunct holds
            // trivially and the lemma is pure overhead. Also skipped when both
            // residuals are empty (handled as a CONFLICT by the `nf_equal` check in
            // Case 2 below).
            {
                use crate::wordeq::same;
                let mut known_d = known.clone();
                known_d.push(l);
                known_d.push(r);
                // A self-referential class merge (e.g. `s ≈ str.++ s s u`) makes the
                // deep normal form non-convergent; `deep_normal_form` returns `None`.
                // We cannot soundly derive a separation lemma from a side we could
                // not ground-resolve, so yield a SOUND `Unknown` (never a wrong
                // verdict). This is the UNIFORM bound for the divergent
                // self-referential word-equation / disequality shapes.
                // E1 (iter 3): collect the expansion merge antecedents so the gate can
                // be ANTECEDENT-PRECISE. Separation is a guarded SPLIT (single-literal
                // guard), so unlike Case-2 it cannot cite multiple antecedents in its
                // clause; instead it emits GLOBALLY only when every merge its residual
                // reads is dl0-entailed (`sep_ante` all level-0), else declines. An
                // unrelated conditional (dis)equality no longer blocks it.
                let mut sep_ante: Vec<EqLeaf> = Vec::new();
                let (lhs, rhs) = match (
                    crate::normalize::deep_normal_form_cited(
                        cx.terms,
                        cx.eq,
                        &known_d,
                        l,
                        &mut sep_ante,
                    ),
                    crate::normalize::deep_normal_form_cited(
                        cx.terms,
                        cx.eq,
                        &known_d,
                        r,
                        &mut sep_ante,
                    ),
                ) {
                    (Some(lhs), Some(rhs)) => (lhs, rhs),
                    _ => return TCheck::Unknown,
                };
                // Precise separation gate: decline iff the residual read a MINTED
                // merge (an F-split / char-peel skolem substitution) — the ce5/ce6
                // wrong-UNSAT channel. An INPUT-conditional merge is left ENABLED: iter-2
                // gated separation on `no_minted_active` only (never on input
                // conditionality), and that stayed sweep-clean while a decided
                // disequality-family SAT (`targeted_pending_conflict_pop_decides_sat`)
                // relies on separation firing over its input merges. This is the precise
                // form of that same rule: block only when THIS residual's antecedents
                // include a minted-disjunct literal, not whenever any minted split is
                // active elsewhere.
                let sep_reads_minted = sep_ante
                    .iter()
                    .any(|leaf| matches!(leaf, EqLeaf::Asserted(l) if minted_lits.contains(l)));
                // Cancel common prefix, then common suffix (free-monoid cancellation).
                let (mut i, mut j) = (0usize, 0usize);
                let (mut le, mut re) = (lhs.len(), rhs.len());
                while i < le && j < re && same(cx.terms, cx.eq, lhs[i], rhs[j]) {
                    i += 1;
                    j += 1;
                }
                while le > i && re > j && same(cx.terms, cx.eq, lhs[le - 1], rhs[re - 1]) {
                    le -= 1;
                    re -= 1;
                }
                let l_res = &lhs[i..le];
                let r_res = &rhs[j..re];
                let has_nonempty_const = |atoms: &[TermId], terms: &Context| {
                    atoms
                        .iter()
                        .any(|&a| terms.string_const_value(a).is_some_and(|s| !s.is_empty()))
                };
                // Emit only for the genuinely-ambiguous shape: neither residual pins a
                // non-empty constant, and not both empty (the s=t conflict is Case 2).
                // E1: and NOT over a MINTED disequality (a negated F-split disjunct,
                // e.g. `!sfx ≠ ""`). Its residual comes from `deep_normal_form` +
                // `same()` cancellation over the CURRENT EUF merges, but the emitted
                // `Σlen(residual) ≥ 1` clause is guarded only by ¬(diseq) — not the
                // merges used to compute the residual. Learnt globally, it is unsound
                // on backtracked branches and (with the other minted-skolem length
                // constraints) drove the two-suffixof spurious UNSAT (s07). Any SAT it
                // would otherwise have blocked is now re-validated by the post-solve
                // model gate (`string_model_satisfies`), so soundness is preserved.
                let diseq_minted = self.minted_eqs.contains(&atom);
                // E1 (iter 2): also skip while ANY minted (dis)equality is currently
                // active (the word-equation search has committed to an F-split /
                // char-peel disjunct). Even a residual that is per-se sound
                // (`¬(s2≠s1) ∨ len(s2)≥1 ∨ len(s1)≥1` over an ALWAYS-TRUE input diseq)
                // then FORCES a length while branch-local minted length axioms are live
                // (the length-link `len(s2·"b"·s2)=len("c"·!strk)` over the prefixof
                // rewrite + `next_axiom` over the char-peel), and the combination is a
                // spurious UNSAT — fuzz seeds 4660 / 966367641601
                // (`prefixof "c" (s2·"b"·s2) ∧ distinct s2 s1`), also wrong at base.
                // Declining the AUXILIARY separation lemma while the search is mid-split
                // breaks the interaction; the decided disequality-family SAT that needs
                // it (`targeted_pending_conflict_pop_decides_sat`) reaches its separation
                // E1 (iter 3): emit iff every merge the deep residual read is
                // dl0-entailed (`sep_ante_dl0`). This precisely replaces iter-2's coarse
                // `no_minted_active`: it declines only when THIS residual actually used a
                // branch-local (input-disjunct OR minted-skolem) merge (ce5/ce6), not
                // whenever any unrelated conditional (dis)equality happens to be active.
                if !(diseq_minted
                    || sep_reads_minted
                    || has_nonempty_const(l_res, cx.terms)
                    || has_nonempty_const(r_res, cx.terms)
                    || l_res.is_empty() && r_res.is_empty())
                {
                    let int_s = cx.terms.int_sort();
                    let one = cx
                        .terms
                        .mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
                    // Build `Σlen(side) ≥ 1` for one residual side. An EMPTY residual
                    // contributes the unsatisfiable `0 ≥ 1` disjunct (i.e. that side
                    // is forced empty), correctly degenerating the disjunction to the
                    // other side's `Σlen ≥ 1`.
                    let build_side = |atoms: &[TermId],
                                      len_terms: &mut FxHashSet<TermId>,
                                      terms: &mut Context|
                     -> TermId {
                        if atoms.is_empty() {
                            // `0 ≥ 1`: this side is forced empty.
                            let zero = terms
                                .mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
                            return terms
                                .mk_app(Op::Builtin(BuiltinOp::Ge), &[zero, one])
                                .expect("(>= 0 1) well-sorted");
                        }
                        let len_atoms: Vec<TermId> = atoms
                            .iter()
                            .map(|&a| {
                                terms
                                    .mk_app(Op::Builtin(BuiltinOp::StrLen), &[a])
                                    .expect("str.len(atom) well-sorted")
                            })
                            .collect();
                        for &la in &len_atoms {
                            len_terms.insert(la);
                        }
                        let sum = if len_atoms.len() == 1 {
                            len_atoms[0]
                        } else {
                            terms
                                .mk_app(Op::Builtin(BuiltinOp::Add), &len_atoms)
                                .expect("(+ len ...) well-sorted")
                        };
                        terms
                            .mk_app(Op::Builtin(BuiltinOp::Ge), &[sum, one])
                            .expect("(>= Σlen 1) well-sorted")
                    };
                    let ge_l = build_side(l_res, &mut self.len_terms, cx.terms);
                    let ge_r = build_side(r_res, &mut self.len_terms, cx.terms);
                    if !self.emitted_len_axioms.contains(&ge_l)
                        || !self.emitted_len_axioms.contains(&ge_r)
                    {
                        self.emitted_len_axioms.insert(ge_l);
                        self.emitted_len_axioms.insert(ge_r);
                        if !self.fuel.spend() {
                            return TCheck::Unknown;
                        }
                        let mut seen = FxHashSet::default();
                        collect::collect(
                            cx.terms,
                            ge_l,
                            &mut self.len_terms,
                            &mut self.str_terms,
                            &mut seen,
                        );
                        collect::collect(
                            cx.terms,
                            ge_r,
                            &mut self.len_terms,
                            &mut self.str_terms,
                            &mut seen,
                        );
                        return TCheck::Split {
                            atoms: vec![ge_l, ge_r],
                            guard: Some(lit.negate()),
                        };
                    }
                }
            }

            // Case 1: direct EUF class equality — `l` and `r` are in the same
            // EqualityEngine class, so they trivially denote the same word. This
            // handles e.g. `x ≠ "a"++y` when `x = "a"++y` was merged in the EUF
            // (the normal-form comparison cannot detect this since `x` is opaque).
            //
            // Soundness (mirroring EUF `egraph.rs::assert_diseq` conflict pattern):
            // The conflict cites the diseq literal PLUS the equality antecedents from
            // the proof forest (via `eq.explain`). `eq.explain` walks the path
            // between l and r in the proof forest, collecting `EqLeaf::Asserted`
            // leaves — these are the input equality literals that forced the merge.
            // If the merge was `EqJust::Definitional`, explain returns nothing (which
            // is still sound: a definitional equality is unconditionally true, so the
            // diseq literal alone is a sufficient contradiction).
            let ln = cx.eq.intern(l);
            let rn = cx.eq.intern(r);
            if cx.eq.are_equal(ln, rn) {
                let mut just = vec![EqLeaf::Asserted(lit)];
                cx.eq.explain(ln, rn, &mut just);
                return TCheck::Conflict(just);
            }

            // Case 2: same-word conflict via normal-form comparison — catches cases
            // like `"a"++x ≠ "a"++y` when `x = y` was asserted in the EUF. Here l
            // and r are NOT in the same EUF class directly, but their normal forms
            // (after substituting class representatives) are atom-wise equal.
            //
            // Extend `known` to include both sides of the disequality so that
            // normal_form can reflect any merges involving these terms.
            let mut known_d = known.clone();
            known_d.push(l);
            known_d.push(r);
            // Use `deep_normal_form` which recursively expands concat-valued class
            // representatives (e.g. when `x = "a"++y` was merged, the NF of `x`
            // should be `["a", y]` after one expansion level). A non-convergent
            // self-referential merge yields `None`; we then cannot soundly compare
            // the two words for a same-word conflict, so yield a SOUND `Unknown`
            // rather than risk a wrong verdict or diverge.
            // E1 (iter 3) FULL CITATION: collect the EXPANSION merge antecedents while
            // building the deep normal forms (`deep_normal_form_cited`). iter-2 gated
            // this conflict coarsely because `nf_equal_explain` only cites the FINAL
            // per-pair merges while `deep_normal_form` FOLDS substituted atoms into
            // constants (`"c"·s0` with `s0≈"b"` → `["cb"]`), losing the `s0≈"b"`
            // provenance (ce8, wrong-UNSAT 966367641601 @6000, also wrong at base). By
            // threading every substitution's `eq.explain` leaves into `expand_ante`, the
            // conflict cites its COMPLETE antecedent set — trigger diseq + all expansion
            // merges + the final per-pair merges — so it is a fully-cited, globally-valid
            // clause and needs NO decision-level gate at all (max decisiveness). The
            // citation is STRING-only (no cross-sort arith), so it stays within the SAT
            // conflict-analyzability guard.
            let mut expand_ante: Vec<EqLeaf> = Vec::new();
            let (lhs, rhs) = match (
                crate::normalize::deep_normal_form_cited(
                    cx.terms,
                    cx.eq,
                    &known_d,
                    l,
                    &mut expand_ante,
                ),
                crate::normalize::deep_normal_form_cited(
                    cx.terms,
                    cx.eq,
                    &known_d,
                    r,
                    &mut expand_ante,
                ),
            ) {
                (Some(lhs), Some(rhs)) => (lhs, rhs),
                _ => return TCheck::Unknown,
            };
            if crate::wordeq::nf_equal(cx.terms, cx.eq, &lhs, &rhs) {
                // Fully-cited conflict: diseq literal + expansion merges + per-pair merges.
                //
                // SOUNDNESS RELIANCE (hardening note): this conflict is emitted UNGATED,
                // so its correctness depends on the cited antecedent set being SUFFICIENT
                // — i.e. `diseq ∧ (expand_ante) ∧ (per-pair merges)` really does entail
                // `nf(l) = nf(r)`, so `¬(that conjunction)` is a valid clause. That in
                // turn relies on `eq.explain` returning a set of `EqLeaf::Asserted` /
                // `Interface` leaves that fully justifies each merge it is asked about
                // (the EUF proof-forest invariant). TWO backstops make an incomplete or
                // stale citation SAFE rather than a wrong-UNSAT: (1) the SAT seam's
                // `theory_conflict_analyzable` check REJECTS a malformed conflict clause
                // (any cited literal not currently false at a level ≤ the current one) and
                // bails to a SOUND `Unknown` (`theory_guard_bailouts`) instead of learning
                // it; (2) the post-solve model gate (`Solver::string_model_satisfies`,
                // Fix B) re-validates any resulting SAT and downgrades an unrealisable one
                // to `Unknown`. So a citation gap can only cost DECISIVENESS, never
                // soundness. (Empirically the string-only citation stays analyzable — the
                // guard-bailout rate is unchanged from before full citation.)
                let mut just = vec![EqLeaf::Asserted(lit)];
                just.extend(expand_ante.iter().copied());
                crate::wordeq::nf_equal_explain(cx.terms, cx.eq, &lhs, &rhs, &mut just);
                return TCheck::Conflict(just);
            }
        }

        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {
        // String theory does not mint self-tagged interface (theory:4) leaves:
        // string conflicts use EqLeaf::Asserted / resolve through EUF tags.
        // This guard makes a future invariant break fail loud in debug.
        debug_assert!(false, "StrSolver::explain reached — string theory should not mint self-tagged interface (theory:4) leaves");
    }

    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        self.model_with(cx, m);
    }

    fn push(&mut self) {
        self.trail.push(self.eq_true.len(), self.diseq_true.len());
    }

    fn pop(&mut self, level: usize) {
        if let Some((e, d)) = self.trail.pop_to(level) {
            self.eq_true.truncate(e);
            self.diseq_true.truncate(d);
            // Keep the parallel assertion-level records in lock-step (E1 gate).
            self.eq_levels.truncate(e);
            self.diseq_levels.truncate(d);
        }
    }

    #[cfg(debug_assertions)]
    fn cited_lits(&self, out: &mut Vec<(Lit, &'static str)>) {
        out.extend(self.eq_true.iter().map(|&(_, l)| (l, "str.eq_true")));
        out.extend(self.diseq_true.iter().map(|&(_, l)| (l, "str.diseq_true")));
    }

    fn shared_arith_terms(&self, cx: &mut TheoryCtx) -> Vec<TermId> {
        let mut out: Vec<TermId> = self.len_terms.iter().copied().collect();
        // Empty-length link, robust (arith-entailed) direction: if any disequality
        // has an empty-literal side, expose the Int numeral `0` as a shared term.
        // The N-O exchange then ENTAILS `len(s) = 0` (merging it into the shared
        // engine with a proper arith tag) whenever arith forces the length to zero
        // — even when that is implied only by bounds (`len(s) ≤ 0 ∧ len(s) ≥ 0`),
        // which produce NO `len(s) ≈ 0` merge on their own. The diseq-loop conflict
        // check (`len_class_zero`) then fires with a correct, theory-resolved
        // justification. We add `0` ONLY in the presence of an empty-side
        // disequality, so unrelated queries see no extra shared term (and the MBTC
        // arrangement set is unperturbed for them).
        let has_empty_diseq = self.diseq_true.iter().any(|&(atom, _)| {
            let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);
            cx.terms.string_const_value(l) == Some("") || cx.terms.string_const_value(r) == Some("")
        });
        if has_empty_diseq {
            let int_s = cx.terms.int_sort();
            let zero = cx
                .terms
                .mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
            if !out.contains(&zero) {
                out.push(zero);
            }
        }
        out
    }
}

impl StrSolver {
    /// Assemble concrete string values into the model.
    ///
    /// Called by `TheorySolver::model`; also exposed so tests can inject a
    /// pre-seeded `ModelBuilder` (e.g. with arith-model lengths already set).
    pub(crate) fn model_with(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        let str_terms: Vec<TermId> = self.str_terms.iter().copied().collect();
        // `known` = all string-sorted terms PLUS both sides of every asserted
        // equality, so `deep_normal_form` / class lookups can reflect merges
        // (e.g. `x = "ab"` pins x's value) even when the other side is not in
        // `str_terms`. `diseq_sides` tolerates `Distinct` atoms parked in eq_true.
        let mut known: Vec<TermId> = str_terms.clone();
        for &(atom, _) in &self.eq_true {
            let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);
            known.push(l);
            known.push(r);
        }
        model::assign(cx.terms, cx.eq, &known, &str_terms, m);
    }
}

/// E1 (iter 3) — antecedent-precise gate primitive. `true` iff no flattened atom of
/// `t` sits in an EUF class whose root is in `cond_roots` — i.e. computing `t`'s
/// normal form substitutes no term that a conditional (dl>0) (dis)equality merged.
/// When this holds for both sides of an equation/disequality, the merge-derived
/// lemma read off their normal forms used only unconditionally-entailed merges and
/// is a globally-valid clause; when it fails, some substitution the lemma reads is
/// branch-local, so the global lemma is skipped (or the trigger cited). Sound over-
/// approximation: it flags a class touched by a conditional equality even if `t`'s
/// own rep is reachable by a dl0 sub-path — never the reverse.
fn side_clean(
    eq: &mut EqualityEngine,
    terms: &Context,
    t: TermId,
    cond_roots: &FxHashSet<ENodeId>,
) -> bool {
    if cond_roots.is_empty() {
        return true;
    }
    let mut flat = Vec::new();
    crate::normalize::flatten(terms, t, &mut flat);
    flat.iter().all(|&a| {
        let n = eq.intern(a);
        !cond_roots.contains(&eq.find(n))
    })
}

/// `true` iff every `EqLeaf::Asserted` merge antecedent is a level-0 (unconditional)
/// literal per `lit_lvl`; an `Interface` (cross-theory) leaf, or an untracked literal,
/// is treated conservatively as conditional. Used to certify that a specific merge is
/// dl0-entailed (e.g. the `v ≈ const` merge behind `next_axiom`'s EUF-repr axiom).
pub(crate) fn leaves_all_dl0(leaves: &[EqLeaf], lit_lvl: &FxHashMap<Lit, u32>) -> bool {
    leaves.iter().all(|leaf| match leaf {
        EqLeaf::Asserted(l) => lit_lvl.get(l) == Some(&0),
        EqLeaf::Interface(_) => false,
    })
}

/// If `str.len(s)` is interned in the shared EqualityEngine and lives in a class
/// that contains a numeral whose value is `0`, return that numeral's TermId.
/// Returns `None` otherwise (length unknown, non-zero, or `str.len(s)` never
/// interned). Pure read of the shared engine — no merges, no side effects.
///
/// This is the sound side of the empty-length link (`len(s)=0 ⟹ s=""`): when the
/// length is *entailed* to be `0` (e.g. `(= (str.len s) 0)` was asserted, which
/// routes to EUF and merges `len(s) ≈ 0`), a co-asserted `s ≠ ""` is a genuine
/// contradiction. Reading the entailment from the shared engine — rather than
/// emitting an opaque `(=> (= len 0) (= s ""))` implication (EUF holds it without
/// decoding it ⇒ no-op) or a guarded `(s≠"") → len(s)≥1` arith lemma (floods the
/// String↔Arith N-O seam ⇒ broad wrong-UNSAT) — keeps the mechanism local and
/// model-preserving, with a justification built from the actual antecedents.
fn len_class_zero(
    terms: &mut Context,
    eq: &mut shinri_theory::EqualityEngine,
    len_term: TermId,
) -> Option<TermId> {
    // Only meaningful if `len_term` was actually interned (some atom referenced
    // it). `intern` is idempotent, but interning a term never seen by any theory
    // would create a fresh singleton class that can't be equal to anything, so a
    // negative result is still correct.
    let zero = terms.mk_numeral(
        shinri_core::Rational::from_int(0i128.into()),
        terms.int_sort(),
    );
    let ln = eq.intern(len_term);
    let zn = eq.intern(zero);
    if eq.are_equal(ln, zn) {
        Some(zero)
    } else {
        None
    }
}

/// Scan `known` for two DIFFERENT string-literal terms in the same EUF class
/// (forced equal) — an outright contradiction (distinct constants ≠).
fn first_distinct_const_clash(
    terms: &Context,
    eq: &mut shinri_theory::EqualityEngine,
    known: &[TermId],
) -> Option<(TermId, TermId)> {
    use rustc_hash::FxHashMap;
    let mut by_root: FxHashMap<shinri_theory::types::ENodeId, (TermId, String)> =
        FxHashMap::default();
    for &t in known {
        let val = match terms.string_const_value(t) {
            Some(s) => s.to_owned(),
            None => continue,
        };
        let n = eq.intern(t);
        let root = eq.find(n);
        match by_root.get(&root) {
            None => {
                by_root.insert(root, (t, val));
            }
            Some((prev_t, prev_val)) => {
                if *prev_val != val {
                    return Some((*prev_t, t));
                }
            }
        }
    }
    None
}

#[cfg(test)]
impl StrSolver {
    /// Push `atom` directly onto `eq_true`, simulating the SAT layer asserting
    /// a string equality without going through `assert`. Used only in unit tests.
    /// Uses a dummy Lit (var 0, positive) since the justification is not exercised
    /// in unit tests (no combiner expand_conflict path).
    pub fn test_force_eq_true(&mut self, atom: TermId) {
        self.eq_true.push((atom, Lit::new(Var::new(0), true)));
        // Level 0 ⟹ unconditional, so merge-derived length lemmas stay enabled for
        // the existing unit tests (which assert without a surrounding disjunction).
        self.eq_levels.push(0);
    }

    /// Push `atom` directly onto `diseq_true`, simulating the SAT layer asserting
    /// a string disequality. Uses a dummy Lit (var 0, positive) since the test
    /// exercises the conflict detection path, not the full conflict-expansion path.
    pub fn test_force_diseq_true(&mut self, atom: TermId) {
        self.diseq_true.push((atom, Lit::new(Var::new(0), true)));
        self.diseq_levels.push(0);
    }

    /// Override the fuel budget. Used only in unit tests to force exhaustion.
    pub fn test_set_fuel(&mut self, n: u32) {
        self.fuel = Fuel { remaining: n };
    }

    /// Force a term into `str_terms` without going through `new_var`.
    /// Used in unit tests to seed model construction.
    pub fn test_force_str_term(&mut self, t: TermId) {
        self.str_terms.insert(t);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_sat::Effort;
    use shinri_theory::types::ModelVal;
    use shinri_theory::{
        AtomRegistry, EqualityEngine, ModelBuilder, TCheck, TheoryCtx, TheorySolver,
    };

    #[test]
    fn collects_len_terms_and_reaches_sat_fixpoint() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let len = ctx
            .mk_app(
                shinri_core::Op::Builtin(shinri_core::BuiltinOp::StrLen),
                &[x],
            )
            .unwrap();
        let ge = {
            // (>= (str.len x) 0) — an arith atom carrying str.len
            let zero = ctx.mk_numeral(
                shinri_core::Rational::from_int(0i128.into()),
                ctx.int_sort(),
            );
            ctx.mk_app(
                shinri_core::Op::Builtin(shinri_core::BuiltinOp::Ge),
                &[len, zero],
            )
            .unwrap()
        };
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        s.new_var(&mut cx, Var::new(0), ge);
        assert!(
            s.shared_arith_terms(&mut cx).contains(&len),
            "str.len term must be shared"
        );
        // For an opaque variable x (no concat/literal) with NO disequality, check
        // emits only the `(>= (str.len x) 0)` axiom, then reaches Sat fixpoint. The
        // empty-length link is a CONFLICT CHECK in the disequality loop (it reads
        // the entailed length from the shared engine, emitting no atoms), and only
        // fires for an empty-side `s ≠ ""` disequality — none here — so it stays Sat.
        let first = s.check(&mut cx, Effort::Full);
        assert!(
            matches!(first, TCheck::Split { .. }),
            "should emit >=0 axiom for str.len(x)"
        );
        assert!(
            matches!(s.check(&mut cx, Effort::Full), TCheck::Sat),
            "fixpoint after all axioms emitted"
        );
    }

    // Task 7.5: an INPUT (assertion-time) equality `s = "ab" ++ k` must emit the
    // guarded length link `len(s) = len("ab"++k)` (via its Ge/Le arith
    // companions), so arith can derive `len(s) = 2 + len(k) >= 2` and contradict
    // an asserted `len(s) = 1`. Before the fix the concat side was unconditionally
    // skipped and the link was never emitted → the variable-headed word equation
    // solved trivially and the query was wrongly SAT.
    #[test]
    fn input_var_equals_concat_emits_length_link() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let s = mk(&mut ctx, "s");
        let k = mk(&mut ctx, "k");
        let ab = ctx.mk_string_const("ab");
        let concat = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ab, k])
            .unwrap();
        let atom = ctx.mk_eq(s, concat).unwrap();
        let len_s = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[s]).unwrap();
        let len_c = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[concat])
            .unwrap();
        // The expected companions of `(= len_s len_c)`.
        let expected_ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_s, len_c])
            .unwrap();
        let expected_le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[len_s, len_c])
            .unwrap();

        let mut solver = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        solver.new_var(&mut cx, Var::new(0), atom);
        solver.test_force_eq_true(atom);
        let (mut saw_ge, mut saw_le) = (false, false);
        for _ in 0..64 {
            match solver.check(&mut cx, Effort::Full) {
                TCheck::Split { atoms, guard } => {
                    for a in atoms {
                        if a == expected_ge {
                            saw_ge = true;
                            // Non-tautological len link must be guarded by ¬eqn.
                            assert!(guard.is_some(), "length link must be guarded (¬eqn)");
                        }
                        if a == expected_le {
                            saw_le = true;
                            assert!(guard.is_some(), "length link must be guarded (¬eqn)");
                        }
                    }
                }
                TCheck::Sat => break,
                TCheck::Conflict(_) => panic!("s = \"ab\"++k is satisfiable in isolation"),
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
            }
        }
        assert!(
            saw_ge && saw_le,
            "input `s = \"ab\"++k` must emit the len(s)=len(\"ab\"++k) Ge/Le companions"
        );
    }

    #[test]
    fn fuel_exhaustion_yields_unknown_not_hang() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");
        // x ++ y = y ++ x : needs several length axioms + a word-equation F-split.
        // A 1-unit fuel budget must run out before resolving → Unknown (sound),
        // never a fabricated verdict or loop.
        let l = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[y, x])
            .unwrap();
        let atom = ctx.mk_eq(l, r).unwrap();
        let mut s = StrSolver::default();
        s.test_set_fuel(1); // tiny budget — exhausts before all axioms/splits
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        s.test_force_eq_true(atom);
        let mut got_unknown = false;
        for _ in 0..50 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Unknown => {
                    got_unknown = true;
                    break;
                }
                TCheck::Split { .. } => continue,
                _ => break,
            }
        }
        assert!(
            got_unknown,
            "tiny fuel must force Unknown, never fabricate a verdict"
        );
    }

    // With len(x)=2 fixed and no constant constraints, x's model is a uniform
    // 2-character fill word (per-class fill char; for a lone free var a single
    // repeated letter).
    #[test]
    fn free_var_model_filled_with_default_char() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let f = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let lenx = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut m = ModelBuilder::default();
        // Seed the model with len(x) = 2 (as arith would).
        m.assign(
            lenx,
            ModelVal::Num(shinri_core::Rational::from_int(2i64.into())),
        );
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), lenx);
        s.test_force_str_term(x);
        s.model_with(&mut cx, &mut m);
        match m.get(x) {
            Some(ModelVal::String(s)) => {
                assert_eq!(s.chars().count(), 2, "free var filled to len 2");
                let c0 = s.chars().next().unwrap();
                assert!(s.chars().all(|c| c == c0), "fill is uniform");
                assert!(c0.is_ascii_alphabetic(), "fill char is a letter");
            }
            other => panic!("expected a String model for x, got {other:?}"),
        }
    }
}
