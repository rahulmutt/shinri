//! The shared equality engine: backtrackable union-find + (Tasks 3–5)
//! disequalities, proof forest, and merge events. The single source of
//! equality truth for all theories (spec §4).

use crate::types::{ENodeId, EqConflict, EqJust, EqLeaf};
use shinri_core::{TermId, UndoLog};

/// One e-node: its union-find parent and class size (for union-by-size).
struct ENode {
    parent: ENodeId,
    size: u32,
}

/// An undo entry: `child` was re-parented onto `root` during a merge; undoing
/// makes `child` its own root again and restores `root`'s size.
struct UfUndo {
    child: ENodeId,
    root: ENodeId,
    root_size_before: u32,
}

/// A stored disequality: its justification plus the endpoint nodes exactly as
/// passed to `assert_diseq` (so a conflict can cite the asserted endpoints, not
/// the class representatives the diseq is keyed on).
#[derive(Clone, Copy)]
struct DiseqRecord {
    just: EqJust,
    lhs: ENodeId,
    rhs: ENodeId,
}

/// Undo entry for the diseq map.
enum DiseqUndo {
    /// A fresh key was inserted; remove it on undo.
    Insert((ENodeId, ENodeId)),
    /// A key was re-keyed (from `old` to `new`) during a merge; restore `old`
    /// (with the same record) and remove `new` on undo.
    Rekey {
        old: (ENodeId, ENodeId),
        new: (ENodeId, ENodeId),
        rec: DiseqRecord,
    },
}

#[derive(Default)]
pub struct EqualityEngine {
    nodes: Vec<ENode>,
    term_to_node: shinri_core_map::Map,
    undo: UndoLog<UfUndo>,
    /// Disequal *representative* pairs (canonical order min,max by index), each
    /// with the justification that asserted them AND the two endpoint nodes as
    /// originally passed to `assert_diseq` (NOT their representatives), so a
    /// later merge conflict can bridge the merged nodes to the diseq endpoints.
    /// Backtracked via `diseq_undo`.
    diseqs: rustc_hash::FxHashMap<(ENodeId, ENodeId), DiseqRecord>,
    diseq_undo: UndoLog<DiseqUndo>,
    /// Proof forest: `fparent[n]` and the label of the edge n→fparent[n].
    /// `fparent[n] == n` means n is a forest root. Backtracked via `forest_undo`.
    fparent: Vec<ENodeId>,
    flabel: Vec<EqJust>,
    forest_undo: UndoLog<ENodeId>, // the node whose forest edge was added
    merges: Vec<crate::types::MergeEvent>,
    /// Arena of congruence argument pairs; `EqJust::Congruence` indexes into it.
    cong_pairs: Vec<(ENodeId, ENodeId)>,
    /// Backtracks `cong_pairs`: each entry is the arena length before a level.
    cong_undo: UndoLog<usize>,
}

impl EqualityEngine {
    /// Register `t`, returning its (stable) e-node. Idempotent.
    pub fn intern(&mut self, t: TermId) -> ENodeId {
        if let Some(n) = self.term_to_node.get(t) {
            return n;
        }
        debug_assert!(
            self.nodes.len() < u32::MAX as usize,
            "ENodeId space exhausted"
        );
        let id = ENodeId::new(self.nodes.len() as u32);
        self.nodes.push(ENode {
            parent: id,
            size: 1,
        });
        self.fparent.push(id);
        self.flabel.push(EqJust::Definitional); // placeholder for a root node; never read
        self.term_to_node.insert(t, id);
        id
    }

    /// Class representative. Union-by-size keeps depth O(log n); no path
    /// compression (it would require logging every redirected pointer on the
    /// hottest read — spec §4.1).
    pub fn find(&self, mut n: ENodeId) -> ENodeId {
        while self.nodes[n.index()].parent != n {
            n = self.nodes[n.index()].parent;
        }
        n
    }

    #[inline]
    pub fn are_equal(&self, a: ENodeId, b: ENodeId) -> bool {
        self.find(a) == self.find(b)
    }

    #[inline]
    fn pair(a: ENodeId, b: ENodeId) -> (ENodeId, ENodeId) {
        if a.index() <= b.index() {
            (a, b)
        } else {
            (b, a)
        }
    }

    /// Record `a != b`. Conflict if they are already equal.
    pub fn assert_diseq(&mut self, a: ENodeId, b: ENodeId, j: EqJust) -> Result<(), EqConflict> {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            // a,b are already equal: they ARE the diseq endpoints here.
            return Err(EqConflict {
                a,
                b,
                diseq: j,
                diseq_lhs: a,
                diseq_rhs: b,
            });
        }
        let key = Self::pair(ra, rb);
        let record = DiseqRecord {
            just: j,
            lhs: a,
            rhs: b,
        };
        if self.diseqs.insert(key, record).is_none() {
            self.diseq_undo.record(DiseqUndo::Insert(key));
        }
        Ok(())
    }

    /// Union the classes of `a` and `b`. `j` is recorded by the proof forest.
    pub fn merge(&mut self, a: ENodeId, b: ENodeId, j: EqJust) -> Result<(), EqConflict> {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return Ok(());
        }
        // Guard the single unsoundness vector: uniting a known-disequal pair.
        if let Some(&rec) = self.diseqs.get(&Self::pair(ra, rb)) {
            return Err(EqConflict {
                a,
                b,
                diseq: rec.just,
                diseq_lhs: rec.lhs,
                diseq_rhs: rec.rhs,
            });
        }
        // Splice the explanation edge a—b labelled j into the proof forest.
        self.reroot_forest(a);
        self.fparent[a.index()] = b;
        self.flabel[a.index()] = j;
        self.forest_undo.record(a);
        let (root, child) = if self.nodes[ra.index()].size >= self.nodes[rb.index()].size {
            (ra, rb)
        } else {
            (rb, ra)
        };
        let root_size_before = self.nodes[root.index()].size;
        self.undo.record(UfUndo {
            child,
            root,
            root_size_before,
        });
        self.nodes[child.index()].parent = root;
        self.nodes[root.index()].size += self.nodes[child.index()].size;
        self.merges.push(crate::types::MergeEvent { a, b });
        // Re-key any disequalities involving `child` to use `root` instead,
        // so the representative-keyed lookup stays valid after the union.
        let stale_keys: Vec<(ENodeId, ENodeId)> = self
            .diseqs
            .keys()
            .filter(|&&(ka, kb)| ka == child || kb == child)
            .copied()
            .collect();
        for old_key in stale_keys {
            let rec = self.diseqs.remove(&old_key).expect("key present by filter");
            let (ka, kb) = old_key;
            let new_a = if ka == child { root } else { ka };
            let new_b = if kb == child { root } else { kb };
            let new_key = Self::pair(new_a, new_b);
            self.diseqs.insert(new_key, rec);
            self.diseq_undo.record(DiseqUndo::Rekey {
                old: old_key,
                new: new_key,
                rec,
            });
        }
        Ok(())
    }

    /// Like `merge`, but the equality is justified by congruence over the given
    /// argument pairs (stored in the arena; the edge label references the range).
    pub fn merge_congruence(
        &mut self,
        a: ENodeId,
        b: ENodeId,
        pairs: &[(ENodeId, ENodeId)],
    ) -> Result<(), EqConflict> {
        self.cong_undo.record(self.cong_pairs.len());
        debug_assert!(
            self.cong_pairs.len() < u32::MAX as usize,
            "cong_pairs arena overflow"
        );
        debug_assert!(
            pairs.len() <= u32::MAX as usize - self.cong_pairs.len(),
            "cong_pairs arena overflow"
        );
        let start = self.cong_pairs.len() as u32;
        self.cong_pairs.extend_from_slice(pairs);
        let cref = crate::types::CongRef {
            start,
            len: pairs.len() as u32,
        };
        self.merge(a, b, EqJust::Congruence(cref))
    }

    /// Reverse the forest path from `n` up to its root so `n` becomes a root.
    fn reroot_forest(&mut self, n: ENodeId) {
        let mut prev = n;
        let mut prev_label = self.flabel[n.index()];
        let mut cur = self.fparent[n.index()];
        self.fparent[n.index()] = n; // n is now a root
        while cur != prev {
            let next = self.fparent[cur.index()];
            let next_label = self.flabel[cur.index()];
            self.fparent[cur.index()] = prev;
            self.flabel[cur.index()] = prev_label;
            prev = cur;
            prev_label = next_label;
            if next == cur {
                break;
            }
            cur = next;
        }
    }

    /// Forest root of `n` (distinct from the union-find representative).
    fn forest_root(&self, mut n: ENodeId) -> ENodeId {
        while self.fparent[n.index()] != n {
            n = self.fparent[n.index()];
        }
        n
    }

    /// Path from `n` toward the forest root (inclusive of edges, exclusive of
    /// the root node), pushing each (node) whose edge we cross.
    fn forest_path(&self, mut n: ENodeId, stop: ENodeId, acc: &mut Vec<ENodeId>) {
        while n != stop {
            acc.push(n);
            let p = self.fparent[n.index()];
            if p == n {
                break;
            }
            n = p;
        }
    }

    /// Collect the explanation leaves entailing `a = b` (spec §4.2). Walks each
    /// node up to their nearest common ancestor in the proof forest, so the
    /// returned leaf set is minimal (no edges above the NCA are included).
    pub fn explain(&self, a: ENodeId, b: ENodeId, out: &mut Vec<EqLeaf>) {
        if a == b {
            return;
        }
        debug_assert_eq!(
            self.forest_root(a),
            self.forest_root(b),
            "explain: a,b not connected"
        );
        let nca = self.forest_nca(a, b);
        let mut path_a = Vec::new();
        let mut path_b = Vec::new();
        self.forest_path(a, nca, &mut path_a);
        self.forest_path(b, nca, &mut path_b);
        for n in path_a.into_iter().chain(path_b) {
            self.expand_edge(self.flabel[n.index()], out);
        }
    }

    /// Nearest common ancestor of `a` and `b` in the proof forest. The caller
    /// guarantees (debug-asserted) that they share a forest root.
    fn forest_nca(&self, a: ENodeId, b: ENodeId) -> ENodeId {
        // Mark every ancestor of `a` (inclusive), then walk `b` upward until we
        // hit a marked node — the deepest shared ancestor.
        let mut on_path_a: rustc_hash::FxHashSet<ENodeId> = rustc_hash::FxHashSet::default();
        let mut n = a;
        loop {
            on_path_a.insert(n);
            let p = self.fparent[n.index()];
            if p == n {
                break;
            }
            n = p;
        }
        let mut m = b;
        loop {
            if on_path_a.contains(&m) {
                return m;
            }
            let p = self.fparent[m.index()];
            if p == m {
                return m; // shared root (always reached for connected a,b)
            }
            m = p;
        }
    }

    /// Turn one edge label into leaves, recursing through congruences.
    fn expand_edge(&self, label: EqJust, out: &mut Vec<EqLeaf>) {
        match label {
            EqJust::Asserted(l) => out.push(EqLeaf::Asserted(l)),
            EqJust::Interface(j) => out.push(EqLeaf::Interface(j)),
            EqJust::Congruence(cref) => {
                let lo = cref.start as usize;
                let hi = lo + cref.len as usize;
                for i in lo..hi {
                    let (s, t) = self.cong_pairs[i];
                    self.explain(s, t, out);
                }
            }
            EqJust::Definitional => {}
        }
    }

    pub fn drain_merges(&mut self, out: &mut Vec<crate::types::MergeEvent>) {
        out.append(&mut self.merges);
    }

    pub fn push(&mut self) {
        self.undo.push_level();
        self.diseq_undo.push_level();
        self.forest_undo.push_level();
        self.cong_undo.push_level();
    }

    pub fn pop(&mut self, level: usize) {
        debug_assert!(self.merges.is_empty(), "pop with undrained merge events");
        let nodes = &mut self.nodes;
        self.undo.pop_to(level, |u| {
            nodes[u.child.index()].parent = u.child;
            nodes[u.root.index()].size = u.root_size_before;
        });
        let diseqs = &mut self.diseqs;
        self.diseq_undo.pop_to(level, |entry| match entry {
            DiseqUndo::Insert(key) => {
                diseqs.remove(&key);
            }
            DiseqUndo::Rekey { old, new, rec } => {
                diseqs.remove(&new);
                diseqs.insert(old, rec);
            }
        });
        let fparent = &mut self.fparent;
        self.forest_undo.pop_to(level, |n| {
            fparent[n.index()] = n; // detach the spliced edge; n becomes a root again
        });
        let cong_pairs = &mut self.cong_pairs;
        self.cong_undo.pop_to(level, |len_before| {
            cong_pairs.truncate(len_before); // truncate arena to its pre-insert length
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::EqLeaf;
    use shinri_core::{Lit, Var};

    fn term(raw: u32) -> TermId {
        TermId::new(raw).unwrap()
    }
    fn asserted(seed: u32) -> EqJust {
        EqJust::Asserted(Lit::new(Var::new(seed), true))
    }

    #[test]
    fn intern_is_idempotent() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(1));
        let c = eq.intern(term(2));
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn merge_makes_equal_and_is_transitive() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        let c = eq.intern(term(3));
        assert!(!eq.are_equal(a, c));
        eq.merge(a, b, asserted(10)).unwrap();
        eq.merge(b, c, asserted(11)).unwrap();
        assert!(eq.are_equal(a, c));
        assert_eq!(eq.find(a), eq.find(c));
    }

    #[test]
    fn pop_restores_pre_merge_state() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        eq.push(); // level 1
        eq.merge(a, b, asserted(20)).unwrap();
        assert!(eq.are_equal(a, b));
        let mut events = Vec::new();
        eq.drain_merges(&mut events); // drain before pop
        eq.pop(0); // back to level 0
        assert!(!eq.are_equal(a, b));
        assert_ne!(eq.find(a), eq.find(b));
    }

    #[test]
    fn merging_disequal_classes_conflicts() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        eq.assert_diseq(a, b, asserted(30)).unwrap();
        let err = eq.merge(a, b, asserted(31)).unwrap_err();
        assert_eq!(eq.find(err.a), eq.find(a));
        assert_eq!(eq.find(err.b), eq.find(b));
    }

    #[test]
    fn merge_conflict_surfaces_original_diseq_endpoints() {
        // Diseq asserted between p,q; later a (=p's class) and b (=q's class)
        // are merged. The conflict must surface the ORIGINAL endpoints p,q,
        // not the merged nodes a,b.
        let mut eq = EqualityEngine::default();
        let p = eq.intern(term(1));
        let q = eq.intern(term(2));
        let a = eq.intern(term(3));
        let b = eq.intern(term(4));
        // a in p's class, b in q's class.
        eq.merge(a, p, asserted(1)).unwrap();
        eq.merge(b, q, asserted(2)).unwrap();
        // Diseq asserted on p,q (the representatives may be a or b).
        eq.assert_diseq(p, q, asserted(3)).unwrap();
        // Merging a,b violates p != q.
        let err = eq.merge(a, b, asserted(4)).unwrap_err();
        assert_eq!(err.a, a);
        assert_eq!(err.b, b);
        // The conflict carries the asserted endpoints p,q (in some orientation).
        let set = [err.diseq_lhs, err.diseq_rhs];
        assert!(set.contains(&p), "diseq endpoint p missing");
        assert!(set.contains(&q), "diseq endpoint q missing");
        // And the endpoints differ from the merged nodes here.
        assert!(err.diseq_lhs != a || err.diseq_rhs != b);
    }

    #[test]
    fn asserting_diseq_on_equal_conflicts() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        eq.merge(a, b, asserted(40)).unwrap();
        assert!(eq.assert_diseq(a, b, asserted(41)).is_err());
    }

    #[test]
    fn diseq_is_backtracked() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        eq.push();
        eq.assert_diseq(a, b, asserted(50)).unwrap();
        eq.pop(0);
        // After backtrack the disequality is gone, so merge succeeds.
        assert!(eq.merge(a, b, asserted(51)).is_ok());
    }

    #[test]
    fn explain_returns_the_asserted_chain() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        let c = eq.intern(term(3));
        let ab = Lit::new(Var::new(60), true);
        let bc = Lit::new(Var::new(61), true);
        eq.merge(a, b, EqJust::Asserted(ab)).unwrap();
        eq.merge(b, c, EqJust::Asserted(bc)).unwrap();
        let mut out = Vec::new();
        eq.explain(a, c, &mut out);
        assert!(out.contains(&EqLeaf::Asserted(ab)));
        assert!(out.contains(&EqLeaf::Asserted(bc)));
    }

    #[test]
    fn explain_expands_congruence_to_its_argument_equalities() {
        // f(x1,x2) and f(y1,y2) merged by an n-ary congruence over both arg pairs.
        let mut eq = EqualityEngine::default();
        let x1 = eq.intern(term(1));
        let y1 = eq.intern(term(2));
        let x2 = eq.intern(term(3));
        let y2 = eq.intern(term(4));
        let fx = eq.intern(term(5));
        let fy = eq.intern(term(6));
        let e1 = Lit::new(Var::new(70), true);
        let e2 = Lit::new(Var::new(71), true);
        eq.merge(x1, y1, EqJust::Asserted(e1)).unwrap();
        eq.merge(x2, y2, EqJust::Asserted(e2)).unwrap();
        eq.merge_congruence(fx, fy, &[(x1, y1), (x2, y2)]).unwrap();
        let mut out = Vec::new();
        eq.explain(fx, fy, &mut out);
        assert!(out.contains(&EqLeaf::Asserted(e1)));
        assert!(out.contains(&EqLeaf::Asserted(e2)));
    }

    #[test]
    fn congruence_merge_is_undone_on_pop() {
        // Verify the arena pop path: after backtracking, the congruence merge is gone.
        let mut eq = EqualityEngine::default();
        let x = eq.intern(term(1));
        let y = eq.intern(term(2));
        let fx = eq.intern(term(3));
        let fy = eq.intern(term(4));
        // Establish x = y at level 0.
        eq.merge(x, y, asserted(100)).unwrap();
        let mut events = Vec::new();
        eq.drain_merges(&mut events);
        // Push a new level and add a congruence merge f(x) = f(y).
        eq.push();
        eq.merge_congruence(fx, fy, &[(x, y)]).unwrap();
        assert_eq!(eq.find(fx), eq.find(fy), "congruence merge must be visible");
        eq.drain_merges(&mut events);
        // Pop back: the congruence merge must be undone.
        eq.pop(0);
        assert_ne!(
            eq.find(fx),
            eq.find(fy),
            "congruence merge must be undone after pop"
        );
    }

    #[test]
    fn explain_is_minimal_for_intermediate_equality() {
        // Chain a—b—c: explaining a=b must NOT drag in the b=c edge.
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        let c = eq.intern(term(3));
        let ab = Lit::new(Var::new(62), true);
        let bc = Lit::new(Var::new(63), true);
        eq.merge(a, b, EqJust::Asserted(ab)).unwrap();
        eq.merge(b, c, EqJust::Asserted(bc)).unwrap();
        let mut out = Vec::new();
        eq.explain(a, b, &mut out);
        assert_eq!(out, vec![EqLeaf::Asserted(ab)]);
    }

    #[test]
    fn merges_are_queued_and_drained_once() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        let c = eq.intern(term(3));
        eq.merge(a, b, asserted(80)).unwrap();
        eq.merge(b, c, asserted(81)).unwrap();
        let mut events = Vec::new();
        eq.drain_merges(&mut events);
        assert_eq!(events.len(), 2);
        // Draining again yields nothing (queue emptied).
        let mut again = Vec::new();
        eq.drain_merges(&mut again);
        assert!(again.is_empty());
    }

    #[test]
    fn redundant_merge_queues_no_event() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        eq.merge(a, b, asserted(90)).unwrap();
        eq.merge(a, b, asserted(91)).unwrap(); // already equal -> no-op
        let mut events = Vec::new();
        eq.drain_merges(&mut events);
        assert_eq!(events.len(), 1);
    }

    #[test]
    fn definitional_edges_contribute_no_explanation_leaf() {
        // A definitional equality is unconditionally true: explaining across it
        // must yield no antecedent leaves (no fake Var(0) literal).
        let mut eq = EqualityEngine::default();
        let w = eq.intern(term(1));
        let d = eq.intern(term(2));
        eq.merge(w, d, EqJust::Definitional).unwrap();
        let mut drained = Vec::new();
        eq.drain_merges(&mut drained); // keep the merge-queue contract clean
        let mut out = Vec::new();
        eq.explain(w, d, &mut out);
        assert!(out.is_empty(), "definitional equality needs no antecedent");
    }
}

/// A thin `TermId`-keyed map over `FxHashMap`, isolated so the engine's
/// storage choice is a single edit point.
mod shinri_core_map {
    use super::ENodeId;
    use rustc_hash::FxHashMap;
    use shinri_core::TermId;

    #[derive(Default)]
    pub struct Map(FxHashMap<TermId, ENodeId>);

    impl Map {
        #[inline]
        pub fn get(&self, t: TermId) -> Option<ENodeId> {
            self.0.get(&t).copied()
        }
        #[inline]
        pub fn insert(&mut self, t: TermId, n: ENodeId) {
            self.0.insert(t, n);
        }
    }
}
