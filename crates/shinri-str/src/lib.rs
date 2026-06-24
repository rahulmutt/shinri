mod collect;
mod fuel;
mod length;
pub mod model;
pub mod normalize;
pub mod reduce;
mod trail;
pub mod wordeq;
pub use fuel::Fuel;


use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, TermNode, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

pub struct StrSolver {
    /// Asserted string equalities: (atom, the literal that asserted it).
    /// The `Lit` is used to build `EqLeaf::Asserted` justifications for conflicts.
    eq_true: Vec<(TermId, Lit)>,
    diseq_true: Vec<(TermId, Lit)>,
    len_terms: FxHashSet<TermId>,
    str_terms: FxHashSet<TermId>,
    emitted_len_axioms: FxHashSet<TermId>,
    /// Dedup set for F-splits: keyed on the canonical (unordered) head pair.
    /// Monotone (never cleared on backtrack); prevents re-emitting the same
    /// split after dedup (termination guarantee).
    emitted_splits: FxHashSet<(TermId, TermId)>,
    /// Counter for fresh string skolem variables minted by F-split.
    fresh_ctr: u32,
    #[allow(dead_code)] // used in Task 15 (unfolding fuel budget)
    fuel: Fuel,
    trail: trail::Trail,
}

impl Default for StrSolver {
    fn default() -> Self {
        StrSolver {
            eq_true: Vec::new(),
            diseq_true: Vec::new(),
            len_terms: FxHashSet::default(),
            str_terms: FxHashSet::default(),
            emitted_len_axioms: FxHashSet::default(),
            emitted_splits: FxHashSet::default(),
            fresh_ctr: 0,
            fuel: Fuel::default(),
            trail: trail::Trail::default(),
        }
    }
}

impl TheorySolver for StrSolver {
    const THEORY_ID: u16 = 4;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        let mut seen = FxHashSet::default();
        collect::collect(cx.terms, atom, &mut self.len_terms, &mut self.str_terms, &mut seen);
    }

    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        // Record asserted string (dis)equalities for consumption by Task 11+.
        // Gate on the operands being String-sorted so non-string equalities
        // (e.g. integer or bitvector) cannot pollute eq_true/diseq_true.
        let atom = cx.atoms.atom(lit.var());
        if let TermNode::App { op, args, .. } = cx.terms.term_node(atom) {
            let args = cx.terms.children(*args).to_vec();
            let is_str_eq = !args.is_empty()
                && cx.terms.sort_of(args[0]) == cx.terms.string_sort();
            if is_str_eq {
                match op {
                    Op::Builtin(BuiltinOp::Eq) => {
                        if lit.is_positive() {
                            self.eq_true.push((atom, lit));
                        } else {
                            self.diseq_true.push((atom, lit));
                        }
                    }
                    Op::Builtin(BuiltinOp::Distinct) => {
                        if lit.is_positive() {
                            self.diseq_true.push((atom, lit));
                        } else {
                            self.eq_true.push((atom, lit));
                        }
                    }
                    _ => {}
                }
            }
        }
        None
    }

    fn propagate(&mut self, _cx: &mut TheoryCtx, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> {
        None
    }

    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
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
            if let (Some(ls), Some(rs)) =
                (cx.terms.string_const_value(l), cx.terms.string_const_value(r))
            {
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

        // Per-equation length lemma, RESTRICTED to ATOM equalities (neither side a
        // concat): `l = r → len(l) = len(r)`, emitted via arith Ge/Le companions
        // guarded by ¬eq. Required so e.g. `s1 = s2` forces `len(s1) = len(s2)` in
        // arith (string equality merges s1≈s2 in EUF, but str.len is not an EUF
        // congruence function here, so arith would otherwise assign inconsistent
        // lengths → a non-satisfying model). SAFE for atom equalities (no fresh
        // concat skolems, so it does not feed the unbounded String↔Arith MBTC).
        // NOT emitted for concat equalities: there the word-equation F-split mints
        // fresh `str.len(skolem)` terms every round, so a per-concat length lemma
        // both floods the seam AND (interacting with the length-defining axioms over
        // those skolems) produced an unsound conflict — so concat length
        // contradictions are caught DIRECTLY in `resolve_equation` by the
        // constant-length bound check (a fully-constant side shorter than the other
        // side's minimum constant length is UNSAT — e.g. `s2++"ba" = "b"`), which
        // needs no fresh terms. A concat-vs-variable-bound length mismatch that
        // depends on an arith-only bound (e.g. `s2++"c"++"bc" = (str.at s0 2)`, where
        // the str.at result is length-bounded only in arith) is left to the bounded
        // fuel/round/pivot caps, which yield a SOUND `Unknown`.
        {
            let eqs: Vec<(TermId, Lit)> = self.eq_true.clone();
            for (atom, lit) in eqs {
                let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);
                let is_concat = |t: TermId| {
                    matches!(
                        cx.terms.term_node(t),
                        TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), .. }
                    )
                };
                if is_concat(l) || is_concat(r) {
                    continue;
                }
                if cx.terms.string_const_value(l).is_some()
                    && cx.terms.string_const_value(r).is_some()
                {
                    continue; // two literals: lengths already pinned constants
                }
                let ll = cx.terms.mk_app(Op::Builtin(BuiltinOp::StrLen), &[l]).expect("len l");
                let lr = cx.terms.mk_app(Op::Builtin(BuiltinOp::StrLen), &[r]).expect("len r");
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
                    collect::collect(cx.terms, comp, &mut self.len_terms, &mut self.str_terms, &mut seen);
                    return TCheck::Split { atoms: vec![comp], guard: Some(lit.negate()) };
                }
            }
        }

        // Per-len-term defining axioms. `next_axiom` returns arith-friendly atoms:
        // `(>= len 0)` and the defining equation's `(>= )` / `(<= )` companions
        // (a bare Int equality would route to EUF, not Arith — see length.rs).
        let lens: Vec<TermId> = self.len_terms.iter().copied().collect();
        for lt in lens {
            if let Some(axiom) = length::next_axiom(cx.terms, cx.eq, &known, lt, &self.emitted_len_axioms) {
                self.emitted_len_axioms.insert(axiom);
                // Register NEW str.len subterms introduced by this axiom so the
                // defining-axiom chain over nested concats continues to a fixpoint.
                let mut seen = FxHashSet::default();
                collect::collect(cx.terms, axiom, &mut self.len_terms, &mut self.str_terms, &mut seen);
                if !self.fuel.spend() {
                    return TCheck::Unknown;
                }
                return TCheck::Split { atoms: vec![axiom], guard: None };
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
            // expansion substitutes merge-derived constants, and resolve's ground
            // conflicts cite only the word-equation literal — not the EUF merge
            // antecedents — so a branch-local contradiction would be reported as a
            // GLOBAL conflict (unsound). Model reconstruction uses the deep view in
            // model.rs).
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
                    let all_var =
                        vars.iter().all(|&a| cx.terms.string_const_value(a).is_none());
                    if all_var {
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

            // Build the EqLeaf justification from the asserted equality literal.
            // This feeds `expand_conflict` so the conflict clause cites the right input literal.
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
                crate::wordeq::StepResult::Conflict(cf) => return TCheck::Conflict(cf),
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
                    return TCheck::Split { atoms, guard: Some(guard) };
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
                let lhs = crate::normalize::deep_normal_form(cx.terms, cx.eq, &known_d, l);
                let rhs = crate::normalize::deep_normal_form(cx.terms, cx.eq, &known_d, r);
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
                    atoms.iter().any(|&a| {
                        terms.string_const_value(a).map_or(false, |s| !s.is_empty())
                    })
                };
                // Emit only for the genuinely-ambiguous shape: neither residual pins a
                // non-empty constant, and not both empty (the s=t conflict is Case 2).
                if !has_nonempty_const(l_res, cx.terms)
                    && !has_nonempty_const(r_res, cx.terms)
                    && !(l_res.is_empty() && r_res.is_empty())
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
            // should be `["a", y]` after one expansion level).
            let lhs = crate::normalize::deep_normal_form(cx.terms, cx.eq, &known_d, l);
            let rhs = crate::normalize::deep_normal_form(cx.terms, cx.eq, &known_d, r);
            if crate::wordeq::nf_equal(cx.terms, cx.eq, &lhs, &rhs) {
                
                // Build conflict: diseq literal + merge antecedents for each pair.
                let mut just = vec![EqLeaf::Asserted(lit)];
                crate::wordeq::nf_equal_explain(cx.terms, cx.eq, &lhs, &rhs, &mut just);
                return TCheck::Conflict(just);
            }
        }

        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}

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
        }
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
            cx.terms.string_const_value(l) == Some("")
                || cx.terms.string_const_value(r) == Some("")
        });
        if has_empty_diseq {
            let int_s = cx.terms.int_sort();
            let zero =
                cx.terms.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
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
    pub fn model_with(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
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
    let zero = terms.mk_numeral(shinri_core::Rational::from_int(0i128.into()), terms.int_sort());
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
    }

    /// Push `atom` directly onto `diseq_true`, simulating the SAT layer asserting
    /// a string disequality. Uses a dummy Lit (var 0, positive) since the test
    /// exercises the conflict detection path, not the full conflict-expansion path.
    pub fn test_force_diseq_true(&mut self, atom: TermId) {
        self.diseq_true.push((atom, Lit::new(Var::new(0), true)));
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
    use shinri_theory::{AtomRegistry, EqualityEngine, ModelBuilder, TCheck, TheoryCtx, TheorySolver};
    use shinri_theory::types::ModelVal;

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
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y]).unwrap();
        let r = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[y, x]).unwrap();
        let atom = ctx.mk_eq(l, r).unwrap();
        let mut s = StrSolver::default();
        s.test_set_fuel(1); // tiny budget — exhausts before all axioms/splits
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        s.test_force_eq_true(atom);
        let mut got_unknown = false;
        for _ in 0..50 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Unknown => { got_unknown = true; break; }
                TCheck::Split { .. } => continue,
                _ => break,
            }
        }
        assert!(got_unknown, "tiny fuel must force Unknown, never fabricate a verdict");
    }

    // With len(x)=2 fixed and no constant constraints, x's model is a uniform
    // 2-character fill word (per-class fill char; for a lone free var a single
    // repeated letter).
    #[test]
    fn free_var_model_filled_with_default_char() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = { let f = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
        let lenx = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut m = ModelBuilder::default();
        // Seed the model with len(x) = 2 (as arith would).
        m.assign(lenx, ModelVal::Num(shinri_core::Rational::from_int(2i64.into())));
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
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
