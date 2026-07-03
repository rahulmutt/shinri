//! The congruence-closure machinery layered over `EqualityEngine`.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{Op, TermId, TermNode};
use shinri_theory::types::{ENodeId, EqConflict, EqJust, EqLeaf};
use shinri_theory::{EqualityEngine, TheoryCtx};

/// Index into `EGraph.apps`.
pub type AppId = u32;

/// A canonicalization key: operator + the representatives of the arguments.
type Signature = (Op, Vec<ENodeId>);

/// An entry in the congruence pending queue: (left node, right node, argument pairs).
type PendingEntry = (ENodeId, ENodeId, Vec<(ENodeId, ENodeId)>);

struct AppNode {
    node: ENodeId,
    op: Op,
    args: Vec<ENodeId>,
}

/// An undo entry for backtracking the EUF-owned indices.
enum Undo {
    /// `lookup[sig]` was inserted with no prior value; remove it on undo.
    LookupInsert(Signature),
    /// `lookup[sig]` overwrote `prev`; restore `prev` on undo.
    LookupOverwrite(Signature, AppId),
    /// `count` apps were appended onto `use_list[winner]` from `loser`; move
    /// them back to `loser` on undo.
    UseSplice {
        winner: usize,
        loser: usize,
        count: usize,
    },
}

/// Internal justification for a single merge step: either an asserted equality
/// or a congruence discovered by `recanonicalize_use_list`.
enum MergeJust {
    Asserted(EqJust),
    Congruence(Vec<(ENodeId, ENodeId)>),
}

#[derive(Default)]
pub struct EGraph {
    apps: Vec<AppNode>,
    /// Per-ENodeId apps that use it directly as an argument (by original node id).
    use_list: Vec<Vec<AppId>>,
    lookup: FxHashMap<Signature, AppId>,
    /// Congruence work-queue: pairs of app nodes to merge, with arg pairs.
    ///
    /// INVARIANT (slice 8, cluster C): `drain_pending` is the SOLE consumer, and
    /// it is NOT backtracked on `pop` — it is normally drained to empty each cycle,
    /// but an early conflict-return can leave stale entries whose arg equalities a
    /// later `pop` invalidates. `drain_pending` tolerates that only because it
    /// re-checks arg equality (`eq.find(pa) == eq.find(pb)`) and skips stale
    /// entries. Any NEW consumer of `pending` MUST apply the same staleness check,
    /// or reintroduce the "explain: a,b not connected" unsound-merge bug.
    pending: Vec<PendingEntry>,
    undo: shinri_core::UndoLog<Undo>,
    /// Set when an interned term is a function application (vs a plain leaf).
    is_app: Vec<bool>,
    /// Cached ⊤/⊥ sentinel e-nodes (interned once, distinct by Definitional diseq).
    truth: Option<(ENodeId, ENodeId)>,
    /// Every registered term in insertion order (one entry per distinct TermId).
    terms: Vec<(TermId, ENodeId)>,
    /// Guard to ensure each TermId is recorded in `terms` exactly once.
    seen_terms: FxHashSet<TermId>,
    /// Registered equality atoms: (var index, a_node, b_node).
    eq_atoms: Vec<(u32, ENodeId, ENodeId)>,
    /// Propagation explanation records: tag -> (a_node, b_node).
    prop_records: Vec<(ENodeId, ENodeId)>,
    /// Vars already propagated (avoid re-emitting), append-only within a solve.
    propagated: rustc_hash::FxHashSet<u32>,
}

impl EGraph {
    #[allow(dead_code)] // used in unit tests; not yet called by solver (Task 8+)
    pub fn app_count(&self) -> usize {
        self.apps.len()
    }

    /// All terms registered via `add_term`, in insertion order (one per distinct TermId).
    pub fn registered_terms(&self) -> &[(TermId, ENodeId)] {
        &self.terms
    }

    /// Cached ⊤/⊥ e-node pair, if sentinels have been interned.
    pub fn truth(&self) -> Option<(ENodeId, ENodeId)> {
        self.truth
    }

    pub fn push(&mut self) {
        self.undo.push_level();
    }

    pub fn pop(&mut self, level: usize) {
        let lookup = &mut self.lookup;
        let use_list = &mut self.use_list;
        self.undo.pop_to(level, |u| match u {
            Undo::LookupInsert(sig) => {
                lookup.remove(&sig);
            }
            Undo::LookupOverwrite(sig, prev) => {
                lookup.insert(sig, prev);
            }
            Undo::UseSplice {
                winner,
                loser,
                count,
            } => {
                debug_assert!(use_list[winner].len() >= count, "use-splice underflow");
                let total = use_list[winner].len();
                let moved = use_list[winner].split_off(total - count);
                debug_assert!(
                    use_list[loser].is_empty(),
                    "loser use-list not empty on undo"
                );
                use_list[loser] = moved;
            }
        });
    }

    fn ensure_node(&mut self, n: ENodeId) {
        let idx = n.index();
        if idx >= self.use_list.len() {
            self.use_list.resize_with(idx + 1, Vec::new);
        }
        if idx >= self.is_app.len() {
            self.is_app.resize(idx + 1, false);
        }
    }

    /// Recursively intern `t` and all subterms, recording app structure.
    /// Returns the e-node of `t`. Idempotent (interning dedups).
    pub fn add_term(&mut self, cx: &mut TheoryCtx, t: TermId) -> ENodeId {
        // Guard: process each distinct TermId exactly once.
        if !self.seen_terms.insert(t) {
            return cx.eq.intern(t);
        }
        let node = cx.eq.intern(t);
        self.terms.push((t, node));
        self.ensure_node(node);
        // Copy out op and args slice before releasing the borrow on cx.terms.
        let term_info = match cx.terms.term_node(t) {
            TermNode::App { op, args, .. } => Some((*op, *args)),
            TermNode::Const { .. } => None,
        };
        match term_info {
            Some((op, args_slice)) => {
                let child_terms: Vec<TermId> = cx.terms.children(args_slice).to_vec();
                let mut arg_nodes = Vec::with_capacity(child_terms.len());
                for ct in child_terms {
                    arg_nodes.push(self.add_term(cx, ct));
                }
                let app_id = self.apps.len() as AppId;
                for &an in &arg_nodes {
                    // Push the new app onto the use-list of the arg's CURRENT
                    // REPRESENTATIVE, not the raw arg node. Use-lists are maintained
                    // at class representatives: `recanonicalize_use_list` drains a
                    // loser's use-list into the winner on merge and records a
                    // `UseSplice` undo that asserts the loser's list is empty when
                    // unwound. If we pushed onto a raw arg node that is already a
                    // *loser* of an earlier same-level merge, that list would be
                    // non-empty at undo time → "loser use-list not empty on undo"
                    // panic. Interning a fresh app mid-search (e.g. a string F-split
                    // skolem or an empty-length-link disjunct) is exactly when this
                    // happens. Keying by the representative keeps the invariant.
                    let rep = cx.eq.find(an);
                    self.ensure_node(rep);
                    self.use_list[rep.index()].push(app_id);
                }
                self.apps.push(AppNode {
                    node,
                    op,
                    args: arg_nodes,
                });
                self.is_app[node.index()] = true;
                // Initial signature; a collision means an existing congruent app.
                let sig = self.signature(cx.eq, app_id);
                if let Some(&other) = self.lookup.get(&sig) {
                    if other != app_id {
                        self.enqueue_congruence(cx.eq, other, app_id);
                    }
                } else {
                    self.lookup.insert(sig, app_id);
                }
                node
            }
            None => node,
        }
    }

    fn signature(&self, eq: &EqualityEngine, app: AppId) -> Signature {
        let a = &self.apps[app as usize];
        let reps: Vec<ENodeId> = a.args.iter().map(|&x| eq.find(x)).collect();
        (a.op, reps)
    }

    fn enqueue_congruence(&mut self, _eq: &EqualityEngine, a: AppId, b: AppId) {
        let aa = &self.apps[a as usize];
        let bb = &self.apps[b as usize];
        debug_assert_eq!(aa.args.len(), bb.args.len());
        let pairs: Vec<(ENodeId, ENodeId)> = aa
            .args
            .iter()
            .copied()
            .zip(bb.args.iter().copied())
            .collect();
        let node_a = aa.node;
        let node_b = bb.node;
        self.pending.push((node_a, node_b, pairs));
    }

    /// Merge `a`,`b` (justified by `just`) and close congruence to a fixpoint.
    /// Returns conflict leaves if a disequality is violated.
    pub fn merge_eq(
        &mut self,
        eq: &mut EqualityEngine,
        a: ENodeId,
        b: ENodeId,
        just: EqJust,
    ) -> Option<Vec<EqLeaf>> {
        if let Some(c) = self.do_merge(eq, a, b, MergeJust::Asserted(just)) {
            return Some(c);
        }
        self.drain_pending(eq)
    }

    /// Assert `a` ≠ `b`; returns conflict leaves if they are already equal.
    pub fn assert_diseq(
        &mut self,
        eq: &mut EqualityEngine,
        a: ENodeId,
        b: ENodeId,
        just: EqJust,
    ) -> Option<Vec<EqLeaf>> {
        match eq.assert_diseq(a, b, just) {
            Ok(()) => None,
            Err(conflict) => {
                // a and b are already equal; explain why via the proof forest,
                // then add the diseq literal.
                let mut out = Vec::new();
                eq.explain(conflict.a, conflict.b, &mut out);
                match conflict.diseq {
                    EqJust::Asserted(l) => out.push(EqLeaf::Asserted(l)),
                    EqJust::Interface(j) => out.push(EqLeaf::Interface(j)),
                    EqJust::Congruence(_) | EqJust::Definitional => {}
                }
                Some(out)
            }
        }
    }

    /// Intern the ⊤/⊥ sentinels once and assert them distinct (level 0, Definitional).
    /// Idempotent: subsequent calls return the cached pair.
    pub fn truth_nodes(
        &mut self,
        cx: &mut TheoryCtx,
        t_true: TermId,
        t_false: TermId,
    ) -> (ENodeId, ENodeId) {
        if let Some(tf) = self.truth {
            return tf;
        }
        let tn = cx.eq.intern(t_true);
        let fln = cx.eq.intern(t_false);
        // Ensure the EGraph's use_list and is_app arrays cover these nodes.
        self.ensure_node(tn);
        self.ensure_node(fln);
        // Fresh, distinct sentinels can never already be equal, so this cannot
        // conflict — but don't silently drop the Result: if it ever did conflict,
        // that signals a real soundness problem. (Always perform the assert, even
        // in release builds; only the success check is debug-gated.)
        let diseq_res = cx.eq.assert_diseq(tn, fln, EqJust::Definitional);
        debug_assert!(
            diseq_res.is_ok(),
            "fresh ⊤/⊥ sentinels must not already be equal"
        );
        let _ = diseq_res;
        self.truth = Some((tn, fln));
        (tn, fln)
    }

    fn drain_pending(&mut self, eq: &mut EqualityEngine) -> Option<Vec<EqLeaf>> {
        while let Some((na, nb, pairs)) = self.pending.pop() {
            if eq.find(na) == eq.find(nb) {
                continue;
            }
            // Skip a STALE congruence: one whose argument pairs are no longer all
            // equal. `pending` is NOT backtracked on `pop` (it is normally drained
            // to empty each cycle), but when a prior `drain_pending` returned early
            // on a conflict it left the remaining entries in the queue; a later
            // `pop` can then invalidate their arg equalities. Draining such an entry
            // would fabricate an unsound `f(..) = f(..)` congruence merge whose
            // conflict explanation later calls `eq.explain` over now-disconnected
            // args (the eq_engine "explain: a,b not connected" panic — cluster C).
            //
            // SOUND + COMPLETE: within a single drain-to-fixpoint no arg pair can go
            // from equal to unequal (merges only add equalities), and a signature
            // collision only enqueues a congruence when every arg pair is already
            // equal — so an unequal arg pair here PROVES a backtrack has invalidated
            // this entry, and the congruence no longer holds. Completeness is kept:
            // if the args re-merge later, `recanonicalize_use_list` re-detects the
            // signature collision and re-enqueues the congruence.
            if pairs.iter().any(|&(pa, pb)| eq.find(pa) != eq.find(pb)) {
                continue;
            }
            if let Some(c) = self.do_merge(eq, na, nb, MergeJust::Congruence(pairs)) {
                return Some(c);
            }
        }
        None
    }

    fn do_merge(
        &mut self,
        eq: &mut EqualityEngine,
        a: ENodeId,
        b: ENodeId,
        mj: MergeJust,
    ) -> Option<Vec<EqLeaf>> {
        let ra = eq.find(a);
        let rb = eq.find(b);
        if ra == rb {
            return None;
        }
        let res = match &mj {
            MergeJust::Asserted(j) => eq.merge(a, b, *j),
            MergeJust::Congruence(pairs) => eq.merge_congruence(a, b, pairs),
        };
        if let Err(conflict) = res {
            return Some(self.conflict_leaves(eq, &mj, conflict));
        }
        // Determine winner/loser by post-merge representative.
        let nr = eq.find(a);
        let loser = if nr == ra { rb } else { ra };
        self.recanonicalize_use_list(eq, nr, loser);
        None
    }

    /// Move `loser`'s use-list into `winner`'s, re-canonicalizing each app;
    /// a signature collision enqueues a congruence.
    fn recanonicalize_use_list(&mut self, eq: &EqualityEngine, winner: ENodeId, loser: ENodeId) {
        // Both endpoints may be e-nodes the EGraph has never interned as apps
        // (e.g. a node that exists only in the shared EqualityEngine because an
        // arith/interface merge created it — its `str.len`/numeral term was never
        // added to the EGraph's use-list arrays). Accessing `use_list[idx]` for
        // such a node would index out of bounds; ensure both are covered first.
        self.ensure_node(winner);
        self.ensure_node(loser);
        let moved: Vec<AppId> = std::mem::take(&mut self.use_list[loser.index()]);
        let count = moved.len();
        for app in moved.iter().copied() {
            let sig = self.signature(eq, app);
            match self.lookup.get(&sig).copied() {
                Some(other) if other != app => {
                    self.enqueue_congruence(eq, other, app);
                    self.undo.record(Undo::LookupOverwrite(sig.clone(), other));
                    self.lookup.insert(sig, app);
                }
                Some(_) => {}
                None => {
                    self.undo.record(Undo::LookupInsert(sig.clone()));
                    self.lookup.insert(sig, app);
                }
            }
        }
        self.use_list[winner.index()].extend(moved);
        self.undo.record(Undo::UseSplice {
            winner: winner.index(),
            loser: loser.index(),
            count,
        });
    }

    /// Register an equality atom for propagation scanning.
    pub fn register_eq_atom(&mut self, var_index: u32, a: ENodeId, b: ENodeId) {
        self.eq_atoms.push((var_index, a, b));
    }

    /// Emit forced-equality propagations. Returns the (lit-var, tag) pairs.
    pub fn collect_eq_propagations(&mut self, eq: &EqualityEngine) -> Vec<(u32, u32)> {
        let mut out = Vec::new();
        for &(vi, a, b) in &self.eq_atoms {
            if self.propagated.contains(&vi) {
                continue;
            }
            if eq.are_equal(a, b) {
                let tag = self.prop_records.len() as u32;
                self.prop_records.push((a, b));
                self.propagated.insert(vi);
                out.push((vi, tag));
            }
        }
        out
    }

    pub fn prop_record(&self, tag: u32) -> (ENodeId, ENodeId) {
        self.prop_records[tag as usize]
    }

    /// Mint an explanation tag for an arbitrary currently-equal pair `(a, b)`
    /// (used for EUF→arith interface equalities). The tag resolves through the
    /// SAME `prop_record`/`explain` path as a forced propagation: `explain(tag)`
    /// will call `eq.explain(a, b, …)`, expanding `a = b` to its input-literal
    /// antecedents over the live proof forest. SOUND because, at the time a
    /// conflict citing this tag is resolved, the proof forest still connects
    /// `a` and `b` (the equality holds at the conflict's decision level).
    pub fn record_interface_pair(&mut self, a: ENodeId, b: ENodeId) -> u32 {
        let tag = self.prop_records.len() as u32;
        self.prop_records.push((a, b));
        tag
    }

    /// Build a SOUND, SUFFICIENT conflict clause for a violated disequality.
    ///
    /// When `merge` or `merge_congruence` returns `Err`, the proof forest does
    /// NOT contain a path between `conflict.a` and `conflict.b` (the merge was
    /// rejected before any edge was added). The leaf set has three parts:
    ///
    /// 1. The "why a = b is forced" antecedents, reconstructed from `MergeJust`:
    ///    - Asserted(j): the literal `j` itself justifies `a = b`.
    ///    - Congruence(pairs): each pair (ai, bi) was already equal; explain each.
    /// 2. The BRIDGE. The violated diseq `d_lhs ≠ d_rhs` was asserted between
    ///    nodes that may differ from the merged nodes `a`,`b`, but they share
    ///    classes: {find(d_lhs), find(d_rhs)} == {find(a), find(b)}. We must add
    ///    `explain(a, d_lhs)` and `explain(b, d_rhs)` (oriented by representative)
    ///    so the conjunction actually entails `d_lhs = d_rhs`. Without this
    ///    bridge the clause is satisfiable and NOT a valid conflict. Both
    ///    endpoints are in-class with a (resp. b) and are forest-connected at
    ///    conflict time (a,b not yet unioned), so `explain`'s precondition holds.
    /// 3. The disequality leaf itself (Asserted→literal, Interface→interface,
    ///    Congruence/Definitional→none).
    ///
    /// The resulting conjunction entails `d_lhs = a = b = d_rhs`, contradicting
    /// the `d_lhs ≠ d_rhs` disequality — a valid conflict for every case
    /// (Congruence merge, Asserted merge, and the assert_diseq direct path,
    /// where the endpoints equal a,b so the bridge is a no-op).
    fn conflict_leaves(
        &self,
        eq: &EqualityEngine,
        mj: &MergeJust,
        conflict: EqConflict,
    ) -> Vec<EqLeaf> {
        let mut out = Vec::new();
        // Part 1: reconstruct why a = b was being merged.
        match mj {
            MergeJust::Asserted(j) => match *j {
                EqJust::Asserted(l) => out.push(EqLeaf::Asserted(l)),
                EqJust::Interface(j) => out.push(EqLeaf::Interface(j)),
                EqJust::Congruence(_) | EqJust::Definitional => {}
            },
            MergeJust::Congruence(pairs) => {
                for &(pa, pb) in pairs {
                    eq.explain(pa, pb, &mut out);
                }
            }
        }
        // Part 2: bridge the merged nodes to the diseq's asserted endpoints.
        // Orient by representative: pair `a` with whichever endpoint is in a's
        // class, and `b` with the other.
        let ra = eq.find(conflict.a);
        let (a_end, b_end) = if eq.find(conflict.diseq_lhs) == ra {
            (conflict.diseq_lhs, conflict.diseq_rhs)
        } else {
            (conflict.diseq_rhs, conflict.diseq_lhs)
        };
        eq.explain(conflict.a, a_end, &mut out);
        eq.explain(conflict.b, b_end, &mut out);
        // Part 3: the disequality that was violated.
        match conflict.diseq {
            EqJust::Asserted(l) => out.push(EqLeaf::Asserted(l)),
            EqJust::Interface(j) => out.push(EqLeaf::Interface(j)),
            EqJust::Congruence(_) | EqJust::Definitional => {}
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Context, Op};
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx};

    fn uconst(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> shinri_core::TermId {
        let sym = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn add_term_registers_apps_and_args() {
        let mut ctx = Context::new();
        let u = ctx.declare_sort("U");
        let a = uconst(&mut ctx, "a", u);
        let b = uconst(&mut ctx, "b", u);
        let f = ctx.declare_fun("f", &[u], u);
        let fa = ctx.mk_app(Op::Uninterpreted(f), &[a]).unwrap();
        let fb = ctx.mk_app(Op::Uninterpreted(f), &[b]).unwrap();

        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut g = EGraph::default();
        {
            let mut cx = TheoryCtx {
                terms: &mut ctx,
                eq: &mut eq,
                atoms: &atoms,
            };
            g.add_term(&mut cx, fa);
            g.add_term(&mut cx, fb);
        }
        // f(a) and f(b) are distinct apps (a,b in different classes): no congruence.
        let na = eq.intern(fa);
        let nb = eq.intern(fb);
        assert!(!eq.are_equal(na, nb));
        assert_eq!(g.app_count(), 4); // a, b, f(a), f(b) all recorded as apps
    }

    #[test]
    fn stale_pending_congruence_not_drained_after_backtrack() {
        // Cluster C (slice 8) root cause: `pending` is NOT backtracked on `pop`.
        // When a prior `drain_pending` returns early on a conflict it leaves the
        // remaining congruence entries in the queue; a later `pop` can invalidate
        // their argument equalities. Draining such a STALE entry fabricates an
        // unsound `f(..) = f(..)` congruence merge whose conflict explanation calls
        // `eq.explain` over now-disconnected args → the eq_engine
        // "explain: a,b not connected" panic (and, in release, a fabricated
        // conflict / unsound merge).
        //
        // This reproduces the mechanism directly: enqueue a congruence `na = nb`
        // justified by `x = y` while x=y holds (level 1), backtrack to level 0 so
        // x and y are no longer equal (entry now stale), then drive a drain. The
        // guard must SKIP the stale entry — no panic, no fabricated conflict, and
        // the pre-existing `na != nb` disequality is left exactly intact.
        use shinri_core::{Lit, Var};
        let asserted = |s: u32| EqJust::Asserted(Lit::new(Var::new(s), true));

        let mut eq = EqualityEngine::default();
        let x = eq.intern(shinri_core::TermId::new(1).unwrap());
        let y = eq.intern(shinri_core::TermId::new(2).unwrap());
        let na = eq.intern(shinri_core::TermId::new(3).unwrap());
        let nb = eq.intern(shinri_core::TermId::new(4).unwrap());

        // Level-0 disequality na ≠ nb (with its ORIGINAL justification asserted(1)).
        eq.assert_diseq(na, nb, asserted(1)).unwrap();

        let mut g = EGraph::default();

        // Level 1: x = y holds, so a congruence na = nb keyed on the pair (x, y)
        // is legitimately enqueued.
        eq.push();
        eq.merge(x, y, asserted(9)).unwrap();
        let mut ev = Vec::new();
        eq.drain_merges(&mut ev);
        assert!(eq.are_equal(x, y), "x=y must hold at level 1");
        g.pending.push((na, nb, vec![(x, y)]));

        // Backtrack to level 0: x and y are distinct again, so the queued
        // congruence entry is now STALE (its only justification no longer holds).
        eq.pop(0);
        assert!(!eq.are_equal(x, y), "x=y must be undone after pop");

        // Drive a drain (the no-op merge_eq(x, x) returns immediately, then drains
        // the pending queue). Pre-fix: `do_merge(na, nb)` conflicts on na≠nb and
        // `conflict_leaves` calls `eq.explain(x, y)` over the disconnected pair —
        // PANIC. Post-fix: the stale entry is skipped.
        let res = g.merge_eq(&mut eq, x, x, asserted(2));

        // Provenance: the stale congruence must NOT have been applied.
        assert!(res.is_none(), "stale congruence must not fabricate a conflict");
        assert!(
            !eq.are_equal(na, nb),
            "stale congruence must not unsoundly merge na and nb"
        );
        // And the ORIGINAL level-0 na≠nb record must be intact (right provenance).
        let err = eq
            .merge(na, nb, asserted(5))
            .expect_err("na≠nb must still be live after the stale-drain");
        assert_eq!(
            err.diseq,
            asserted(1),
            "diseq map must carry the ORIGINAL justification, uncorrupted"
        );
    }
}
