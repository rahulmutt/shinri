//! The Nelson–Oppen combinator (spec §6). Generic over its three theory fields
//! (`euf`, `arith`, `arrays`) until shinri-euf/shinri-arith/shinri-arrays exist;
//! a fixed-arity, enum-routed, fully monomorphized struct — not a variadic tuple.

use crate::atom::{classify, AtomRegistry, Unsupported};
use crate::eq_engine::EqualityEngine;
use crate::interface::InterfaceSet;
use crate::model::ModelBuilder;
use crate::proof::CertLog;
use crate::solver_trait::{TCheck, TheoryCtx, TheorySolver};
use crate::types::{Explainer, MergeEvent, Owner};
use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{Context, Lit, TermId, TheoryJust, Var};
use shinri_sat::{Effort, Theory, TheoryResult};

/// Private tri-state result for `drive_final_check`, carrying the Split variant
/// through to `Theory::check` so it can be lifted to `TheoryResult::SplitAtoms`.
enum FinalCheck {
    Sat,
    Conflict(Vec<crate::types::EqLeaf>),
    Split {
        atoms: Vec<TermId>,
        guard: Option<Lit>,
    },
    /// A sub-theory exhausted its fuel budget; the overall result is unknown.
    Unknown,
}

pub struct Combiner<E: TheorySolver, A: TheorySolver, R: TheorySolver, S: TheorySolver> {
    terms: Context,
    eq: EqualityEngine,
    atoms: AtomRegistry,
    iface: InterfaceSet,
    euf: E,
    arith: A,
    arrays: R,
    string: S,
    level: usize,
    merges: Vec<MergeEvent>,
    /// A conflict detected during `assert` (the SAT seam's `assert` is
    /// infallible); surfaced on the next `propagate` (spec §5.2 bridge).
    pending_conflict: Option<Vec<crate::types::EqLeaf>>,
    cert: CertLog,
}

impl<E: TheorySolver, A: TheorySolver, R: TheorySolver, S: TheorySolver> Default
    for Combiner<E, A, R, S>
{
    fn default() -> Self {
        Combiner::with_context(Context::new())
    }
}

impl<E: TheorySolver, A: TheorySolver, R: TheorySolver, S: TheorySolver> Combiner<E, A, R, S> {
    pub fn with_context(terms: Context) -> Self {
        Combiner {
            terms,
            eq: EqualityEngine::default(),
            atoms: AtomRegistry::default(),
            iface: InterfaceSet::default(),
            euf: E::default(),
            arith: A::default(),
            arrays: R::default(),
            string: S::default(),
            level: 0,
            merges: Vec::new(),
            pending_conflict: None,
            cert: CertLog::default(),
        }
    }

    /// Expose the term context for tests and callers that need to build atoms.
    pub fn context_mut(&mut self) -> &mut Context {
        &mut self.terms
    }

    /// Expose the EUF theory field for EUF-specific setup (e.g. set_truth_terms).
    pub fn euf_mut(&mut self) -> &mut E {
        &mut self.euf
    }

    /// Mutable access to the arith theory slot (mirrors `euf_mut`). Used by the
    /// solver to set the Plan B2 Stage-B gate before solving.
    pub fn arith_mut(&mut self) -> &mut A {
        &mut self.arith
    }

    /// Mutable access to the arrays theory slot (mirrors `arith_mut`).
    pub fn arrays_mut(&mut self) -> &mut R {
        &mut self.arrays
    }

    /// Mutable access to the string theory slot (mirrors `arrays_mut`).
    pub fn string_mut(&mut self) -> &mut S {
        &mut self.string
    }

    /// Classify and register an atom, refusing unsupported constructs (spec §9).
    pub fn register_atom(&mut self, v: Var, atom: TermId) -> Result<(), Unsupported> {
        let owner = classify(&self.terms, atom)?;
        self.atoms.register(v, atom, owner);
        // Split the ctx borrow from the theory fields (the §5.5 pattern).
        match owner {
            Owner::Euf => {
                let mut cx = TheoryCtx {
                    terms: &mut self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.euf.new_var(&mut cx, v, atom);
                // N-O boundary: if the atom contains str.len subterms (e.g.
                // `(= (str.len x) 1)` routes to EUF as an Int equality), also
                // notify the String theory so it can track len_terms for axiom
                // emission and the N-O shared-arith interface.
                if atom_contains_str_len(cx.terms, atom) {
                    self.string.new_var(&mut cx, v, atom);
                }
            }
            Owner::Arith => {
                let mut cx = TheoryCtx {
                    terms: &mut self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.arith.new_var(&mut cx, v, atom);
                // CRITICAL-2: a UF-application used directly as an operand of a
                // linear arith atom (e.g. `(- (f x0) (f x1))`) must be interned
                // into EUF so congruence applies and it joins the shared set S.
                self.euf.register_arith_uf_terms(&mut cx, atom);
                // N-O boundary: if the atom contains str.len subterms (e.g.
                // `(<= (str.len x) 1)` routes to Arith), also notify the String
                // theory so it can track len_terms for axiom emission and the
                // N-O shared-arith interface. This is required for the String↔Arith
                // seam to detect contradictions such as `len(x)=1 ∧ x=""`.
                if atom_contains_str_len(cx.terms, atom) {
                    self.string.new_var(&mut cx, v, atom);
                }
            }
            Owner::Shared => {
                // Purify first: splits mixed terms, emitting defining equalities
                // for fresh interface variables (borrow of self.terms is separate
                // from self.eq / self.iface).
                let (_pure, defs) =
                    crate::interface::purify(&mut self.terms, &mut self.iface, atom);
                for (w, def) in defs {
                    let wn = self.eq.intern(w);
                    let dn = self.eq.intern(def);
                    self.iface.mark_shared(wn);
                    // Definitional equality holds unconditionally (level 0).
                    let _ = self.eq.merge(wn, dn, crate::types::EqJust::Definitional);
                }
                // Re-borrow to notify both theories of the (purified) atom.
                let mut cx = TheoryCtx {
                    terms: &mut self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.euf.new_var(&mut cx, v, atom);
                self.arith.new_var(&mut cx, v, atom);
                self.euf.register_arith_uf_terms(&mut cx, atom);
            }
            Owner::Arrays => {
                let mut cx = TheoryCtx {
                    terms: &mut self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.euf.new_var(&mut cx, v, atom);
                self.arrays.new_var(&mut cx, v, atom);
            }
            // String atoms route to BOTH EUF (for congruence over string terms)
            // and the string theory slot.
            Owner::String => {
                let mut cx = TheoryCtx {
                    terms: &mut self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.euf.new_var(&mut cx, v, atom);
                self.string.new_var(&mut cx, v, atom);
            }
        }
        Ok(())
    }
}

/// Returns true if `atom` (or any of its subterms) is a `str.len` application.
/// Used by `register_atom` to notify the String theory about len_terms that
/// appear in Arith/EUF atoms (N-O boundary fix).
///
/// Returns false immediately for synthetic TermIds that are not interned in
/// `terms` (e.g. mock atoms from tests or split atoms from sub-theories using
/// their own Context). This is safe because any real `str.len` atom must be
/// interned before it can reach `register_atom` / `bind_fresh`.
fn atom_contains_str_len(terms: &Context, atom: TermId) -> bool {
    use shinri_core::{BuiltinOp, Op, TermNode};
    fn walk(terms: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) {
            return false;
        }
        if !terms.contains_term(t) {
            return false;
        }
        match terms.term_node(t) {
            TermNode::App { op, args, .. } => {
                if matches!(op, Op::Builtin(BuiltinOp::StrLen)) {
                    return true;
                }
                let kids = terms.children(*args).to_vec();
                kids.iter().any(|&k| walk(terms, k, seen))
            }
            TermNode::Const { .. } => false,
        }
    }
    if !terms.contains_term(atom) {
        return false;
    }
    let mut seen = rustc_hash::FxHashSet::default();
    walk(terms, atom, &mut seen)
}

impl<E: TheorySolver, A: TheorySolver, R: TheorySolver, S: TheorySolver> Theory
    for Combiner<E, A, R, S>
{
    fn assert(&mut self, lit: Lit) {
        // The SAT layer asserts EVERY trail literal, including auxiliary Tseitin
        // variables minted for Boolean connectives (And/Or/Implies/Xor/Ite/...).
        // Those carry no theory meaning — their Boolean semantics are fully
        // handled by the SAT layer via the Tseitin defining clauses — and are
        // never registered as theory atoms. Ignore them; only registered atoms
        // route to a theory. (Without this, owner() below panics on aux vars.)
        if !self.atoms.is_registered(lit.var()) {
            return;
        }
        let owner = self.atoms.owner(lit.var());
        let mut cx = TheoryCtx {
            terms: &mut self.terms,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        let conflict = match owner {
            Owner::Euf => self.euf.assert(&mut cx, lit),
            Owner::Arith => self.arith.assert(&mut cx, lit),
            Owner::Shared => {
                let e = self.euf.assert(&mut cx, lit);
                let a = self.arith.assert(&mut cx, lit);
                e.or(a)
            }
            Owner::Arrays => {
                let e = self.euf.assert(&mut cx, lit);
                let r = self.arrays.assert(&mut cx, lit);
                e.or(r)
            }
            // String atoms route to BOTH EUF (for congruence) and the string
            // theory slot.
            Owner::String => {
                let e = self.euf.assert(&mut cx, lit);
                let s = self.string.assert(&mut cx, lit);
                e.or(s)
            }
        };
        if conflict.is_some() && self.pending_conflict.is_none() {
            self.pending_conflict = conflict;
        }
    }

    fn new_var(&mut self, _v: Var) {
        // Atom registration (register_atom) is the real entry point; the SAT
        // layer's new_var carries no atom, so there is nothing to do here.
    }

    fn propagate(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
        if let Some(leaves) = self.take_pending_conflict_leaves() {
            return Some(self.expand_conflict(leaves));
        }
        if let Some(leaves) = self.drive_propagation(out) {
            return Some(self.expand_conflict(leaves));
        }
        None
    }

    fn explain(&mut self, just: TheoryJust, out: &mut Vec<Lit>) {
        let mut exp = Explainer::default();
        exp.pending.push(just);
        self.resolve(&mut exp);
        // Reason literals are the antecedents (not negated); shinri-sat's
        // analyze consumes a theory reason via the Reason::Theory path.
        let mut lits = exp.take_lits();
        lits.sort_unstable_by_key(|l| l.code());
        lits.dedup();
        out.extend(lits);
    }

    fn check(&mut self, effort: Effort) -> TheoryResult {
        if effort == Effort::Standard {
            // Standard effort is covered by propagate(); nothing extra here.
            return TheoryResult::Sat;
        }
        match self.drive_final_check() {
            FinalCheck::Sat => TheoryResult::Sat,
            FinalCheck::Conflict(leaves) => TheoryResult::Conflict(self.expand_conflict(leaves)),
            FinalCheck::Split { atoms, guard } => TheoryResult::SplitAtoms { atoms, guard },
            FinalCheck::Unknown => TheoryResult::Unknown,
        }
    }

    fn bind_fresh(&mut self, v: Var, atom: TermId) {
        // A fresh split atom: QF_LIA branch/cut atoms (Le/Ge) → Arith; QF_UFLIA
        // MBTC's interface `(= u v)` → Euf, `(< u v)`/`(> u v)` → Arith. Classify
        // and route to the owning theory, mirroring `register_atom`. Boolean
        // connectives (e.g. `(=> A B)` tautology splits emitted by String theory)
        // and synthetic TermIds (from sub-theories or mock theories in tests) are
        // SAT-layer constructs not owned by any theory. For interned Boolean
        // connectives, fall back to EUF (which harmlessly interns the term).
        // For non-interned synthetic TermIds, skip theory registration entirely.
        let classify_result = classify(&self.terms, atom);
        let is_interned = self.terms.contains_term(atom);
        let owner = match classify_result {
            Ok(o) => o,
            Err(_) if is_interned => Owner::Euf, // Boolean connective (e.g. `(=> A B)`) → EUF
            Err(_) => Owner::Arith, // Synthetic TermId (e.g. Arith branch/cut atoms) → Arith (original behavior)
        };
        self.atoms.register(v, atom, owner);
        let mut cx = TheoryCtx {
            terms: &mut self.terms,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        match owner {
            Owner::Euf => {
                self.euf.new_var(&mut cx, v, atom);
                if atom_contains_str_len(cx.terms, atom) {
                    self.string.new_var(&mut cx, v, atom);
                }
            }
            Owner::Arith => {
                self.arith.new_var(&mut cx, v, atom);
                self.euf.register_arith_uf_terms(&mut cx, atom);
                if atom_contains_str_len(cx.terms, atom) {
                    self.string.new_var(&mut cx, v, atom);
                }
            }
            Owner::Shared => {
                self.euf.new_var(&mut cx, v, atom);
                self.arith.new_var(&mut cx, v, atom);
                self.euf.register_arith_uf_terms(&mut cx, atom);
            }
            Owner::Arrays => {
                self.euf.new_var(&mut cx, v, atom);
                self.arrays.new_var(&mut cx, v, atom);
            }
            // String split atoms route to BOTH EUF (for congruence) and the
            // string theory slot.
            Owner::String => {
                self.euf.new_var(&mut cx, v, atom);
                self.string.new_var(&mut cx, v, atom);
            }
        }
    }

    fn var_for_atom(&self, atom: TermId) -> Option<Var> {
        // Reuse the existing SAT var for an already-registered atom so a re-emitted
        // split atom does not mint a SECOND, unlinked var (the duplicate-var hazard
        // that splits an atom's truth value across two vars → spurious UNSAT /
        // non-termination). Only interned, previously-registered atoms resolve here;
        // synthetic split TermIds are absent from the registry and correctly fall
        // through to a fresh var.
        self.atoms.var_of_atom(atom)
    }

    fn push(&mut self) {
        self.level += 1;
        self.eq.push();
        self.euf.push();
        self.arith.push();
        self.arrays.push();
        self.string.push();
    }

    fn pop(&mut self, n: usize) {
        let target = self.level - n;
        // Discard any pending congruence-merge notifications before popping. A merge
        // notification is a transient signal for the N-O exchange to react to in the
        // SAME `drive_final_check` round; an early return from that loop (an arith
        // conflict / split surfacing right after an `arith→EUF` interface merge, e.g.
        // a length contradiction `len(s) < 0` co-asserted with a substr/concat
        // equality) can leave the queue non-empty. The merges have already been
        // applied to the EUF structure and are about to be UNDONE by this pop, so any
        // unconsumed notification is stale — draining (discarding) it is sound and
        // satisfies the `EqualityEngine::pop` drained-queue invariant (which would
        // otherwise panic in debug builds: "pop with undrained merge events").
        self.merges.clear();
        self.eq.drain_merges(&mut self.merges);
        self.merges.clear();
        self.eq.pop(target);
        self.euf.pop(target);
        self.arith.pop(target);
        self.arrays.pop(target);
        self.string.pop(target);
        self.level = target;
    }
}

impl<E: TheorySolver, A: TheorySolver, R: TheorySolver, S: TheorySolver> Combiner<E, A, R, S> {
    /// Run both theories' Full check to a joint fixpoint over the shared engine,
    /// with BIDIRECTIONAL Nelson-Oppen equality propagation (Task 12b).
    /// Returns the conflicting antecedent leaves, or None if jointly consistent.
    ///
    /// Each round:
    ///   euf.check → arith.check → arrays.check → drain pending merges
    ///   → arith→EUF: merge arith-entailed shared equalities into EUF (closes
    ///     congruence; a violated diseq is a conflict)
    ///   → EUF→arith: feed EUF congruence classes' Real members into arith as
    ///     interface equalities (so arith can detect bound infeasibility)
    /// Re-loops while either direction makes progress; terminates at fixpoint.
    ///
    /// TERMINATION (R5): the shared term set S is finite; arith→EUF skips pairs
    /// already equal in `cx.eq` (merges are monotone — classes only ever shrink
    /// in number), and EUF→arith skips pairs already asserted this round. So the
    /// number of new merges/assertions is bounded and the loop converges.
    fn drive_final_check(&mut self) -> FinalCheck {
        // Compute the shared Real/Int-term set S once and ensure arith has a var
        // (incl. numeral pins) for every member BEFORE any arith check that
        // reads entailed equalities (R4: pins must be active during solving).
        //
        // Gate: skip the N-O exchange and MBTC entirely when EUF has no
        // uninterpreted function applications (arity ≥ 1). In that case EUF
        // congruence cannot derive any equality that arith does not already
        // decide, so the exchange and MBTC are pure overhead (observed root
        // cause of the QF_LIA B&B regression: Int vars from (dis)equality atoms
        // were populating the shared set and triggering the full exchange on
        // every Full check even for pure QF_LIA — no UF present).
        let shared: Vec<TermId> = {
            let mut cx = TheoryCtx {
                terms: &mut self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            let euf_uf = self.euf.has_uf_application(&mut cx);
            let str_lens = self.string.shared_arith_terms(&mut cx); // str.len terms (empty for the stub)
            if !euf_uf && str_lens.is_empty() {
                // No UF and no string-length terms: exchange/MBTC do nothing useful; skip entirely.
                Vec::new()
            } else {
                let mut s = self.euf.shared_arith_terms(&mut cx);
                for t in str_lens {
                    if !s.contains(&t) {
                        s.push(t);
                    }
                }
                for &t in &s {
                    self.arith.ensure_shared_var(&mut cx, t);
                }
                s
            }
        };
        // Pairs already asserted EUF→arith this check (R5 termination guard).
        let mut iface_asserted: FxHashSet<(TermId, TermId)> = FxHashSet::default();

        // Round bound (sound termination guard). The Nelson-Oppen exchange + MBTC
        // converges over the FIXED shared set in O(|shared|) rounds (each productive
        // round makes one new merge / interface assertion, and the shared set is
        // finite), but the String↔Arith length seam can feed it a degenerate arith
        // system whose `entailed_equalities` simplex probing reports a fresh entailed
        // pair every round (over ever-changing slacks) — so the fixpoint is never
        // reached in practice and the loop spins. We cap the round count to a small
        // multiple of |shared| (far above the ~2·|shared| any legitimate convergence
        // needs) and return a SOUND `Unknown` on exhaustion. The per-round cost is a
        // full simplex re-solve, so this is kept tight: a divergent length seam bails
        // to Unknown in well under a second instead of spinning for many seconds.
        let round_cap: u64 = 256 + 32 * (shared.len() as u64);
        let mut rounds: u64 = 0;
        loop {
            rounds += 1;
            if rounds > round_cap {
                return FinalCheck::Unknown;
            }
            {
                let mut cx = TheoryCtx {
                    terms: &mut self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                match self.euf.check(&mut cx, Effort::Full) {
                    TCheck::Conflict(cf) => return FinalCheck::Conflict(cf),
                    TCheck::Split { .. } => unreachable!("EUF never splits"),
                    TCheck::Sat => {}
                    TCheck::Unknown => unreachable!("EUF never returns Unknown"),
                }
                match self.arith.check(&mut cx, Effort::Full) {
                    TCheck::Conflict(cf) => return FinalCheck::Conflict(cf),
                    TCheck::Split { atoms, guard } => return FinalCheck::Split { atoms, guard },
                    TCheck::Sat => {}
                    // Arith now returns Unknown when its simplex pivot cap trips on a
                    // degenerate system (the String↔Arith substr seam). Propagate it
                    // as a sound overall Unknown rather than looping forever.
                    TCheck::Unknown => return FinalCheck::Unknown,
                }
                match self.arrays.check(&mut cx, Effort::Full) {
                    TCheck::Conflict(cf) => return FinalCheck::Conflict(cf),
                    TCheck::Split { atoms, guard } => return FinalCheck::Split { atoms, guard },
                    TCheck::Sat => {}
                    TCheck::Unknown => unreachable!("Arrays never returns Unknown"),
                }
                // String checks last (lowest priority).
                match self.string.check(&mut cx, Effort::Full) {
                    TCheck::Conflict(cf) => return FinalCheck::Conflict(cf),
                    TCheck::Split { atoms, guard } => return FinalCheck::Split { atoms, guard },
                    TCheck::Sat => {}
                    TCheck::Unknown => return FinalCheck::Unknown,
                }
            }
            // Did the existing round produce a new interface/congruence merge?
            self.merges.clear();
            self.eq.drain_merges(&mut self.merges);
            let mut progressed = !self.merges.is_empty();
            self.merges.clear();

            // ── arith → EUF: arith.check just returned Sat above, so read its
            //    entailed shared equalities and merge them into EUF. ──────────
            if !shared.is_empty() {
                let entailed: Vec<(TermId, TermId, u32)> = {
                    let mut cx = TheoryCtx {
                        terms: &mut self.terms,
                        eq: &mut self.eq,
                        atoms: &self.atoms,
                    };
                    self.arith.entailed_equalities(&mut cx, &shared)
                };
                for (a, b, tag) in entailed {
                    let mut cx = TheoryCtx {
                        terms: &mut self.terms,
                        eq: &mut self.eq,
                        atoms: &self.atoms,
                    };
                    let an = cx.eq.intern(a);
                    let bn = cx.eq.intern(b);
                    if cx.eq.are_equal(an, bn) {
                        continue; // R5: already merged — don't re-emit (no progress)
                    }
                    let just = TheoryJust {
                        theory: A::THEORY_ID,
                        tag,
                    };
                    if let Some(cf) = self.euf.consume_interface_equality(&mut cx, a, b, just) {
                        return FinalCheck::Conflict(cf);
                    }
                    progressed = true;
                }
            }

            // ── EUF → arith: feed each EUF congruence class's Real members to
            //    arith as interface equalities (needed for congruence-derived
            //    equalities, e.g. a=b ⟹ g(a)=g(b) feeding arith). ────────────
            if !shared.is_empty() {
                // Group shared terms by current congruence class representative.
                let mut classes: FxHashMap<crate::types::ENodeId, Vec<TermId>> =
                    FxHashMap::default();
                {
                    let cx = TheoryCtx {
                        terms: &mut self.terms,
                        eq: &mut self.eq,
                        atoms: &self.atoms,
                    };
                    for &t in &shared {
                        let n = cx.eq.intern(t);
                        let rep = cx.eq.find(n);
                        classes.entry(rep).or_default().push(t);
                    }
                }
                for members in classes.values() {
                    if members.len() < 2 {
                        continue;
                    }
                    // Assert each non-representative member equal to the first.
                    let rep = members[0];
                    for &m in &members[1..] {
                        let key = if rep.index() <= m.index() {
                            (rep, m)
                        } else {
                            (m, rep)
                        };
                        if !iface_asserted.insert(key) {
                            continue; // R5: already asserted this round
                        }
                        let mut cx = TheoryCtx {
                            terms: &mut self.terms,
                            eq: &mut self.eq,
                            atoms: &self.atoms,
                        };
                        // Approach (a): mint an EUF-explainable tag for rep=m so
                        // a later arith conflict citing it resolves to EUF's
                        // input-literal proof via euf.explain → cx.eq.explain.
                        let tag = self.euf.mint_eq_tag(&mut cx, rep, m);
                        let just = TheoryJust {
                            theory: E::THEORY_ID,
                            tag,
                        };
                        if let Some(cf) =
                            self.arith.consume_interface_equality(&mut cx, rep, m, just)
                        {
                            return FinalCheck::Conflict(cf);
                        }
                        progressed = true;
                    }
                }
            }

            // Drain any merges produced by the arith→EUF step before deciding.
            self.merges.clear();
            self.eq.drain_merges(&mut self.merges);
            if !self.merges.is_empty() {
                progressed = true;
            }
            self.merges.clear();

            if !progressed {
                // MBTC: decide the first undecided shared-Int arrangement. A pair
                // equal in arith's model but not merged in the shared engine is
                // resolved by an integer trichotomy split. The `=` branch merges
                // in EUF (congruence, exchanged to arith); the `<`/`>` branches
                // separate them in arith. The disjunction is integer-valid, so SAT
                // must pick a branch — and each split permanently decides one pair,
                // so the undecided set strictly shrinks (termination).
                let undecided = if shared.is_empty() {
                    None
                } else {
                    let mut cx = TheoryCtx {
                        terms: &mut self.terms,
                        eq: &mut self.eq,
                        atoms: &self.atoms,
                    };
                    let pairs = self.arith.model_equal_shared_pairs(&mut cx, &shared);
                    pairs.into_iter().find(|&(a, b)| {
                        let an = cx.eq.intern(a);
                        let bn = cx.eq.intern(b);
                        !cx.eq.are_equal(an, bn)
                    })
                };
                if let Some((u, v)) = undecided {
                    let eq = self.terms.mk_eq(u, v).expect("(= u v) well-sorted");
                    let lt = self
                        .terms
                        .mk_app(
                            shinri_core::Op::Builtin(shinri_core::BuiltinOp::Lt),
                            &[u, v],
                        )
                        .expect("(< u v) well-sorted");
                    let gt = self
                        .terms
                        .mk_app(
                            shinri_core::Op::Builtin(shinri_core::BuiltinOp::Gt),
                            &[u, v],
                        )
                        .expect("(> u v) well-sorted");
                    // MBTC trichotomy `(= u v) ∨ (< u v) ∨ (> u v)` is a tautology
                    // over a totally-ordered arith domain — no guard needed.
                    return FinalCheck::Split {
                        atoms: vec![eq, lt, gt],
                        guard: None,
                    };
                }
                return FinalCheck::Sat;
            }
        }
    }

    fn drive_propagation(
        &mut self,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<crate::types::EqLeaf>> {
        loop {
            let before = out.len();
            // 1. Theory propagation.
            {
                let mut cx = TheoryCtx {
                    terms: &mut self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                if let Some(cf) = self.euf.propagate(&mut cx, out) {
                    return Some(cf);
                }
                if let Some(cf) = self.arith.propagate(&mut cx, out) {
                    return Some(cf);
                }
                if let Some(cf) = self.arrays.propagate(&mut cx, out) {
                    return Some(cf);
                }
                if let Some(cf) = self.string.propagate(&mut cx, out) {
                    return Some(cf);
                }
            }
            // 2. Drain congruence/interface merges so each theory can react
            //    next iteration. EUF's congruence driver consumes them via the
            //    shared engine; here we only detect whether progress occurred.
            self.merges.clear();
            self.eq.drain_merges(&mut self.merges);
            let progressed = out.len() != before || !self.merges.is_empty();
            self.merges.clear();
            if !progressed {
                return None;
            }
        }
    }

    fn take_pending_conflict_leaves(&mut self) -> Option<Vec<crate::types::EqLeaf>> {
        self.pending_conflict.take()
    }

    /// Expand conflicting antecedent leaves to input literals, then negate to
    /// form the conflict clause handed to shinri-sat's analyzer.
    fn expand_conflict(&mut self, leaves: Vec<crate::types::EqLeaf>) -> Vec<Lit> {
        // A conflict is about to be handed to the SAT loop, which will backtrack
        // and pop. Any merge events queued during this round are now stale working
        // state; drain and discard them so the engine's drain-before-pop contract
        // (EqualityEngine::pop's debug_assert) holds on the conflict path too.
        self.merges.clear();
        self.eq.drain_merges(&mut self.merges);
        self.merges.clear();
        let mut exp = Explainer::default();
        for leaf in leaves {
            exp.push_leaf(leaf);
        }
        self.resolve(&mut exp);
        let antecedents = exp.take_lits();
        let mut clause: Vec<Lit> = antecedents.iter().map(|l| l.negate()).collect();
        clause.sort_unstable_by_key(|l| l.code());
        clause.dedup();
        if !antecedents.is_empty() {
            self.cert.record(&clause, &antecedents);
        }
        clause
    }

    pub fn cert_log(&self) -> &crate::proof::CertLog {
        &self.cert
    }

    #[cfg(test)]
    pub(crate) fn atoms_ref(&self) -> &AtomRegistry {
        &self.atoms
    }

    #[cfg(test)]
    pub(crate) fn arith_ref(&self) -> &A {
        &self.arith
    }

    /// Assemble the combined model (spec §7.3). Arith assigns rationals first
    /// (interface variables included); EUF fills uninterpreted classes. Arrays
    /// contributes nothing in the baseline but keeps the seam symmetric. The
    /// theories must agree on every shared term — a debug-asserted seam invariant.
    pub fn build_model(&mut self) -> ModelBuilder {
        let mut arith_m = ModelBuilder::default();
        {
            let mut cx = TheoryCtx {
                terms: &mut self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            self.arith.model(&mut cx, &mut arith_m);
        }
        let mut euf_m = ModelBuilder::default();
        {
            let mut cx = TheoryCtx {
                terms: &mut self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            self.euf.model(&mut cx, &mut euf_m);
        }
        debug_assert!(
            arith_m.merge_check(&euf_m).is_none(),
            "model seam disagreement on a shared term"
        );
        let mut arrays_m = ModelBuilder::default();
        {
            let mut cx = TheoryCtx {
                terms: &mut self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            self.arrays.model(&mut cx, &mut arrays_m);
        }
        let mut combined = arith_m;
        combined.absorb(euf_m);
        combined.absorb(arrays_m);
        // Build the string model LAST, directly into `combined`, so it can read
        // the arith-assigned `(str.len ·)` values (needed to fill free string
        // variables to their correct length) and any EUF-assigned string values.
        // A separate empty builder would hide those, yielding length-0 strings
        // that violate their own `str.len` constraint.
        {
            let mut cx = TheoryCtx {
                terms: &mut self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            self.string.model(&mut cx, &mut combined);
        }
        combined
    }

    /// Drive the Explainer to a fixpoint: expand each pending interface
    /// justification via its owning theory until only input literals remain.
    fn resolve(&mut self, exp: &mut Explainer) {
        let mut visited: FxHashSet<(u16, u32)> = FxHashSet::default();
        while let Some(j) = exp.pending.pop() {
            if !visited.insert((j.theory, j.tag)) {
                continue; // already expanded; justification DAG, so this terminates
            }
            // Build context inside the loop so the &mut self.eq borrow is released each iteration.
            let mut cx = TheoryCtx {
                terms: &mut self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            if j.theory == E::THEORY_ID {
                self.euf.explain(&mut cx, j.tag, exp);
            } else if j.theory == A::THEORY_ID {
                self.arith.explain(&mut cx, j.tag, exp);
            } else if j.theory == R::THEORY_ID {
                self.arrays.explain(&mut cx, j.tag, exp);
            } else if j.theory == S::THEORY_ID {
                self.string.explain(&mut cx, j.tag, exp);
            } else {
                debug_assert!(false, "explain: unknown theory id {}", j.theory);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver_trait::TCheck;
    use crate::types::{EqJust, EqLeaf};
    use crate::{Explainer, ModelBuilder};
    use shinri_core::Op;

    /// Records asserted literals; never conflicts. Lets us observe routing.
    #[derive(Default)]
    struct Spy {
        asserted: Vec<Lit>,
        level: usize,
    }
    impl TheorySolver for Spy {
        const THEORY_ID: u16 = 1;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
            self.asserted.push(lit);
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _out: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {
            self.level += 1;
        }
        fn pop(&mut self, level: usize) {
            self.level = level;
        }
    }

    /// Returns a conflict on its FIRST assert, then never again. Lets us drive
    /// the assert→propagate `pending_conflict` bridge.
    #[derive(Default)]
    struct AssertConflicter {
        fired: bool,
    }
    impl TheorySolver for AssertConflicter {
        const THEORY_ID: u16 = 7;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
            if !self.fired {
                self.fired = true;
                Some(vec![EqLeaf::Asserted(Lit::new(Var::new(99), true))])
            } else {
                None
            }
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _out: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _level: usize) {}
    }

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let sym = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn assert_routes_to_the_owning_theory() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let le = ctx
            .mk_app(Op::Builtin(shinri_core::BuiltinOp::Le), &[x, y])
            .unwrap();
        let mut c: Combiner<Spy, Spy, NullTheory, NullTheory> = Combiner::with_context(ctx);
        let v = Var::new(0);
        c.register_atom(v, le).unwrap();
        c.assert(Lit::new(v, true));
        assert_eq!(c.arith.asserted, vec![Lit::new(v, true)]);
        assert!(c.euf.asserted.is_empty());
    }

    #[test]
    fn push_pop_track_absolute_levels() {
        let mut c: Combiner<Spy, Spy, NullTheory, NullTheory> = Combiner::default();
        c.push();
        c.push();
        assert_eq!(c.level, 2);
        c.pop(1); // close 1 scope -> target level 1
        assert_eq!(c.level, 1);
        assert_eq!(c.arith.level, 1);
        assert_eq!(c.euf.level, 1);
    }

    #[test]
    fn unsupported_atom_is_refused() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let xy = ctx
            .mk_app(
                shinri_core::Op::Builtin(shinri_core::BuiltinOp::Mul),
                &[x, y],
            )
            .unwrap();
        let z = real_var(&mut ctx, "z");
        let le = ctx
            .mk_app(
                shinri_core::Op::Builtin(shinri_core::BuiltinOp::Le),
                &[xy, z],
            )
            .unwrap();
        let mut c: Combiner<Spy, Spy, NullTheory, NullTheory> = Combiner::with_context(ctx);
        assert!(c.register_atom(Var::new(0), le).is_err());
    }

    /// Emits one propagation `(p, just)` exactly once, to drive the fixpoint loop.
    #[derive(Default)]
    struct OneShotProp {
        fired: bool,
        p: Option<Lit>,
    }
    impl TheorySolver for OneShotProp {
        const THEORY_ID: u16 = 2;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            out: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            if !self.fired {
                self.fired = true;
                if let Some(p) = self.p {
                    out.push((p, TheoryJust { theory: 2, tag: 0 }));
                }
            }
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _level: usize) {}
    }

    #[test]
    fn propagate_collects_theory_implications_to_fixpoint() {
        let mut c: Combiner<OneShotProp, OneShotProp, NullTheory, NullTheory> = Combiner::default();
        c.euf.p = Some(Lit::new(Var::new(7), true));
        let mut out = Vec::new();
        assert!(c.propagate(&mut out).is_none());
        assert_eq!(
            out,
            vec![(
                Lit::new(Var::new(7), true),
                TheoryJust { theory: 2, tag: 0 }
            )]
        );
    }

    /// On check(Full), merges e-nodes for term(1) and term(2) once.
    #[derive(Default)]
    struct Merger {
        done: bool,
    }
    impl TheorySolver for Merger {
        const THEORY_ID: u16 = 3;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            if !self.done {
                self.done = true;
                let a = cx.eq.intern(TermId::new(1).unwrap());
                let b = cx.eq.intern(TermId::new(2).unwrap());
                let _ = cx
                    .eq
                    .merge(a, b, EqJust::Interface(TheoryJust { theory: 3, tag: 0 }));
            }
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
    }

    /// Conflicts iff term(1) and term(2) are equal in the shared engine.
    #[derive(Default)]
    struct Splitter;
    impl TheorySolver for Splitter {
        const THEORY_ID: u16 = 4;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            let a = cx.eq.intern(TermId::new(1).unwrap());
            let b = cx.eq.intern(TermId::new(2).unwrap());
            if cx.eq.are_equal(a, b) {
                TCheck::Conflict(vec![EqLeaf::Interface(TheoryJust { theory: 3, tag: 0 })])
            } else {
                TCheck::Sat
            }
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
    }

    #[test]
    fn final_check_sat_when_theories_agree() {
        let mut c: Combiner<OneShotProp, OneShotProp, NullTheory, NullTheory> = Combiner::default();
        assert!(matches!(c.check(Effort::Full), TheoryResult::Sat));
    }

    #[test]
    fn final_check_conflicts_when_an_interface_merge_violates_the_other_theory() {
        // euf = Merger (merges 1,2), arith = Splitter (conflicts if 1==2).
        let mut c: Combiner<Merger, Splitter, NullTheory, NullTheory> = Combiner::default();
        match c.check(Effort::Full) {
            TheoryResult::Conflict(lits) => assert!(
                lits.is_empty(),
                "Merger.explain is a no-op, so the conflict clause must be empty"
            ),
            other => panic!("expected conflict, got {other:?}"),
        }
    }

    /// Explains tag 0 as the single input literal `lit(50, +)`.
    #[derive(Default)]
    struct Explained;
    impl TheorySolver for Explained {
        const THEORY_ID: u16 = 3; // matches the Merger's TheoryJust.theory above
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            let a = cx.eq.intern(TermId::new(1).unwrap());
            let b = cx.eq.intern(TermId::new(2).unwrap());
            let _ = cx
                .eq
                .merge(a, b, EqJust::Interface(TheoryJust { theory: 3, tag: 0 }));
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, tag: u32, exp: &mut Explainer) {
            assert_eq!(tag, 0);
            exp.push_lit(Lit::new(Var::new(50), true));
        }
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
    }

    #[test]
    fn conflict_expands_interface_leaves_to_input_literals_and_negates() {
        // euf = Explained (merges 1,2 with an interface just it can explain),
        // arith = Splitter (conflicts when 1==2, citing that interface just).
        let mut c: Combiner<Explained, Splitter, NullTheory, NullTheory> = Combiner::default();
        match c.check(Effort::Full) {
            TheoryResult::Conflict(clause) => {
                // The interface leaf resolved to lit(50,+); the clause negates it.
                assert_eq!(clause, vec![Lit::new(Var::new(50), true).negate()]);
            }
            other => panic!("expected conflict, got {other:?}"),
        }
    }

    #[test]
    fn emitted_conflict_is_recorded_and_rechecks() {
        let mut c: Combiner<Explained, Splitter, NullTheory, NullTheory> = Combiner::default();
        let _ = c.check(Effort::Full);
        assert_eq!(c.cert_log().steps().len(), 1);
        assert_eq!(c.cert_log().recheck(), Ok(()));
    }

    /// Assigns ModelVal::Num(k) to term(1).
    #[derive(Default)]
    struct ValTheory {
        k: i64,
    }
    impl TheorySolver for ValTheory {
        const THEORY_ID: u16 = 5;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, m: &mut ModelBuilder) {
            m.assign(
                TermId::new(1).unwrap(),
                crate::types::ModelVal::Num(shinri_core::Rational::from_int(
                    (self.k as i128).into(),
                )),
            );
        }
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
    }

    #[test]
    fn build_model_collects_theory_assignments() {
        let mut c: Combiner<OneShotProp, ValTheory, NullTheory, NullTheory> = Combiner::default();
        c.arith.k = 42;
        let m = c.build_model();
        assert_eq!(
            m.get(TermId::new(1).unwrap()),
            Some(&crate::types::ModelVal::Num(
                shinri_core::Rational::from_int(42i128.into())
            ))
        );
    }

    #[test]
    fn merge_then_conflict_then_pop_does_not_panic() {
        // Merger merges term(1)/term(2) on check(Full) (queuing a MergeEvent);
        // Splitter then conflicts because they are equal. After the conflict the
        // SAT loop pops — the engine's merge queue must already be drained, else
        // EqualityEngine::pop's debug_assert fires.
        let mut c: Combiner<Merger, Splitter, NullTheory, NullTheory> = Combiner::default();
        c.push();
        match c.check(Effort::Full) {
            TheoryResult::Conflict(_) => {}
            other => panic!("expected conflict, got {other:?}"),
        }
        c.pop(1); // must not panic
    }

    #[test]
    fn assert_conflict_is_stashed_and_surfaced_by_propagate() {
        // A `Le` atom routes to `arith`; make arith the conflicter. The
        // infallible assert stashes the conflict; the next propagate surfaces
        // and drains it; a following propagate is clean.
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let le = ctx
            .mk_app(Op::Builtin(shinri_core::BuiltinOp::Le), &[x, y])
            .unwrap();
        let mut c: Combiner<Spy, AssertConflicter, NullTheory, NullTheory> =
            Combiner::with_context(ctx);
        let v = Var::new(0);
        c.register_atom(v, le).unwrap();
        c.assert(Lit::new(v, true));
        let mut out = Vec::new();
        assert!(
            c.propagate(&mut out).is_some(),
            "stashed conflict must surface"
        );
        let mut out2 = Vec::new();
        assert!(c.propagate(&mut out2).is_none(), "conflict must be drained");
    }

    // ── Task 5: Combiner lifts TCheck::Split → SplitAtoms + bind_fresh ──────

    /// Do-nothing EUF slot: always Sat, never splits.
    #[derive(Default)]
    struct NullTheory;
    impl TheorySolver for NullTheory {
        const THEORY_ID: u16 = 99;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _out: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _level: usize) {}
    }

    /// Arith-slot stub: returns Split(split_atom) on first Full check, then Sat.
    /// Records (v, atom) pairs from `new_var` for bind_fresh verification.
    #[derive(Default)]
    struct ArithSplitter {
        fired: bool,
        pub bound: Vec<(Var, TermId)>,
        /// The atom to return from the first Split; set by the test after construction.
        pub split_atom: Option<TermId>,
    }
    impl TheorySolver for ArithSplitter {
        const THEORY_ID: u16 = 7;
        fn new_var(&mut self, _cx: &mut TheoryCtx, v: Var, atom: TermId) {
            self.bound.push((v, atom));
        }
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            if !self.fired {
                self.fired = true;
                let atom = self
                    .split_atom
                    .expect("split_atom must be set before check");
                TCheck::Split {
                    atoms: vec![atom],
                    guard: None,
                }
            } else {
                TCheck::Sat
            }
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
    }

    #[test]
    fn combiner_lifts_split_and_binds_fresh() {
        use crate::types::Owner;

        // Build a real Le atom so classify() can classify it as Owner::Arith.
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let le = ctx
            .mk_app(Op::Builtin(shinri_core::BuiltinOp::Le), &[x, y])
            .unwrap();

        let mut comb: Combiner<NullTheory, ArithSplitter, NullTheory, NullTheory> =
            Combiner::with_context(ctx);
        comb.arith.split_atom = Some(le);

        // First Full check lifts the arith Split into SplitAtoms.
        match Theory::check(&mut comb, Effort::Full) {
            TheoryResult::SplitAtoms { atoms, guard } => {
                assert_eq!(atoms, vec![le]);
                assert_eq!(guard, None);
            }
            other => panic!("expected SplitAtoms, got {other:?}"),
        }
        // Solver would now allocate a var and call back bind_fresh; simulate it.
        let v = Var::new(0);
        Theory::bind_fresh(&mut comb, v, le);
        // The fresh atom is registered to the Arith owner and encoded by the arith slot.
        assert_eq!(comb.atoms_ref().owner(v), Owner::Arith);
        assert_eq!(comb.arith_ref().bound, vec![(v, le)]);
    }

    #[test]
    fn bind_fresh_routes_eq_to_euf_and_lt_to_arith() {
        use crate::types::Owner;
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let us = ctx.declare_fun("u", &[], int);
        let vs = ctx.declare_fun("v", &[], int);
        let u = ctx.mk_app(Op::Uninterpreted(us), &[]).unwrap();
        let v = ctx.mk_app(Op::Uninterpreted(vs), &[]).unwrap();
        let eq = ctx.mk_eq(u, v).unwrap();
        let lt = ctx
            .mk_app(Op::Builtin(shinri_core::BuiltinOp::Lt), &[u, v])
            .unwrap();
        let mut c: Combiner<Spy, Spy, NullTheory, NullTheory> = Combiner::with_context(ctx);
        let ve = Var::new(0);
        let vl = Var::new(1);
        Theory::bind_fresh(&mut c, ve, eq);
        Theory::bind_fresh(&mut c, vl, lt);
        assert_eq!(c.atoms_ref().owner(ve), Owner::Euf);
        assert_eq!(c.atoms_ref().owner(vl), Owner::Arith);
    }

    /// EUF stub that declares two shared terms but never merges them.
    #[derive(Default)]
    struct SharedEuf {
        t1: Option<TermId>,
        t2: Option<TermId>,
    }
    impl TheorySolver for SharedEuf {
        const THEORY_ID: u16 = 1;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
        fn shared_arith_terms(&self, _cx: &mut TheoryCtx) -> Vec<TermId> {
            vec![self.t1.unwrap(), self.t2.unwrap()]
        }
        // SharedEuf simulates an EUF that shares terms — this implies UF presence,
        // so the gate must fire. Without this override the N-O exchange is skipped
        // and the MBTC test would never see the trichotomy split.
        fn has_uf_application(&self, _cx: &mut TheoryCtx) -> bool {
            true
        }
    }

    /// Arith stub that reports its two terms as model-equal (undecided pair).
    #[derive(Default)]
    struct ModelEqArith {
        t1: Option<TermId>,
        t2: Option<TermId>,
    }
    impl TheorySolver for ModelEqArith {
        const THEORY_ID: u16 = 2;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
        fn model_equal_shared_pairs(
            &mut self,
            _cx: &mut TheoryCtx,
            _shared: &[TermId],
        ) -> Vec<(TermId, TermId)> {
            vec![(self.t1.unwrap(), self.t2.unwrap())]
        }
    }

    #[test]
    fn mbtc_emits_trichotomy_split_for_undecided_int_pair() {
        use crate::atom::classify;
        use crate::types::Owner;
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let us = ctx.declare_fun("u", &[], int);
        let vs = ctx.declare_fun("v", &[], int);
        let u = ctx.mk_app(Op::Uninterpreted(us), &[]).unwrap();
        let v = ctx.mk_app(Op::Uninterpreted(vs), &[]).unwrap();
        let mut c: Combiner<SharedEuf, ModelEqArith, NullTheory, NullTheory> =
            Combiner::with_context(ctx);
        c.euf.t1 = Some(u);
        c.euf.t2 = Some(v);
        c.arith.t1 = Some(u);
        c.arith.t2 = Some(v);
        match Theory::check(&mut c, Effort::Full) {
            TheoryResult::SplitAtoms { atoms, guard } => {
                assert_eq!(guard, None, "MBTC trichotomy is a tautology, no guard");
                assert_eq!(atoms.len(), 3, "integer trichotomy = 3 atoms");
                assert_eq!(classify(&c.terms, atoms[0]), Ok(Owner::Euf)); // (= u v)
                assert_eq!(classify(&c.terms, atoms[1]), Ok(Owner::Arith)); // (< u v)
                assert_eq!(classify(&c.terms, atoms[2]), Ok(Owner::Arith)); // (> u v)
            }
            other => panic!("expected SplitAtoms, got {other:?}"),
        }
    }

    // ── Task 5, Step 6: arrays-slot split test ────────────────────────────────

    /// Arrays-slot stub: splits once (returning its registered atom), then Sat.
    /// Records the atom from `new_var` for routing verification.
    #[derive(Default)]
    struct ArraySplitter {
        fired: bool,
        atom: Option<TermId>,
    }
    impl TheorySolver for ArraySplitter {
        const THEORY_ID: u16 = 3;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, atom: TermId) {
            self.atom = Some(atom);
        }
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            if !self.fired {
                self.fired = true;
                TCheck::Split {
                    atoms: vec![self.atom.unwrap()],
                    guard: None,
                }
            } else {
                TCheck::Sat
            }
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _x: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
    }

    #[test]
    fn arrays_slot_split_is_lifted() {
        use crate::atom::classify;
        use crate::types::Owner;

        // Build a select atom so classify() returns Owner::Arrays.
        // (declare-sort I 0) (declare-sort E 0)
        // (declare-fun a () (Array I E))
        // (declare-fun i () I)
        // (select a i) — used as a term; wrap in an equality to make an atom.
        let mut ctx = Context::new();
        let isort = ctx.declare_sort("I");
        let esort = ctx.declare_sort("E");
        let arr_sort = ctx.array_sort(isort, esort);
        let a_sym = ctx.declare_fun("a", &[], arr_sort);
        let i_sym = ctx.declare_fun("i", &[], isort);
        let a = ctx.mk_app(Op::Uninterpreted(a_sym), &[]).unwrap();
        let i = ctx.mk_app(Op::Uninterpreted(i_sym), &[]).unwrap();
        // (select a i) : E
        let sel = ctx
            .mk_app(Op::Builtin(shinri_core::BuiltinOp::Select), &[a, i])
            .unwrap();
        // Wrap in an equality: (= (select a i) (select a i)) — always-true but
        // has Owner::Arrays because select is present.
        let sel_atom = ctx.mk_eq(sel, sel).unwrap();

        // Confirm routing before building the Combiner.
        assert_eq!(
            classify(&ctx, sel_atom),
            Ok(Owner::Arrays),
            "atom with select must be classified as Owner::Arrays"
        );

        let mut comb: Combiner<NullTheory, NullTheory, ArraySplitter, NullTheory> =
            Combiner::with_context(ctx);

        // Register the arrays atom — routes to euf (for congruence) + arrays (for watching).
        let v = Var::new(0);
        comb.register_atom(v, sel_atom).unwrap();

        // The arrays stub should have received new_var; its atom field is now set.
        assert!(
            comb.arrays.atom.is_some(),
            "ArraySplitter must receive new_var for Owner::Arrays atom"
        );

        // First Full check: arrays.check returns Split — must be lifted to SplitAtoms.
        match Theory::check(&mut comb, Effort::Full) {
            TheoryResult::SplitAtoms { atoms, guard } => {
                assert_eq!(atoms, vec![sel_atom], "split atom must round-trip");
                assert_eq!(guard, None);
            }
            other => panic!("expected SplitAtoms from arrays slot, got {other:?}"),
        }

        // Second Full check: arrays.check returns Sat — combiner must be Sat.
        match Theory::check(&mut comb, Effort::Full) {
            TheoryResult::Sat => {}
            other => panic!("expected Sat on second check, got {other:?}"),
        }
    }

    // ── Task 7: 4th (String) theory slot ─────────────────────────────────────

    /// No-op stub for the String theory slot — always Sat, registers nothing.
    #[derive(Default)]
    struct StubStr;
    impl TheorySolver for StubStr {
        const THEORY_ID: u16 = 4;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _o: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
    }

    #[test]
    fn combiner_accepts_fourth_theory_slot() {
        // Construct a 4-theory combiner; a string equality registers as Owner::String.
        let mut c: Combiner<NullTheory, NullTheory, NullTheory, StubStr> = Combiner::default();
        let str_s = c.context_mut().string_sort();
        let x = {
            let s = c.context_mut().declare_fun("x", &[], str_s);
            c.context_mut().mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let y = {
            let s = c.context_mut().declare_fun("y", &[], str_s);
            c.context_mut().mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let atom = c.context_mut().mk_eq(x, y).unwrap();
        assert!(c.register_atom(Var::new(0), atom).is_ok());
    }
}
