//! The shared equality engine: backtrackable union-find + (Tasks 3–5)
//! disequalities, proof forest, and merge events. The single source of
//! equality truth for all theories (spec §4).

use crate::types::{ENodeId, EqJust};
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

#[derive(Default)]
pub struct EqualityEngine {
    nodes: Vec<ENode>,
    term_to_node: shinri_core_map::Map,
    undo: UndoLog<UfUndo>,
}

impl EqualityEngine {
    /// Register `t`, returning its (stable) e-node. Idempotent.
    pub fn intern(&mut self, t: TermId) -> ENodeId {
        if let Some(n) = self.term_to_node.get(t) {
            return n;
        }
        let id = ENodeId::new(self.nodes.len() as u32);
        self.nodes.push(ENode {
            parent: id,
            size: 1,
        });
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

    /// Union the classes of `a` and `b`. `_j` is recorded by the proof forest
    /// in Task 4; here it is accepted but unused.
    pub fn merge(&mut self, a: ENodeId, b: ENodeId, _j: EqJust) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        // Attach the smaller class under the larger (union-by-size).
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
    }

    pub fn push(&mut self) {
        self.undo.push_level();
    }

    pub fn pop(&mut self, level: usize) {
        let nodes = &mut self.nodes;
        self.undo.pop_to(level, |u| {
            nodes[u.child.index()].parent = u.child;
            nodes[u.root.index()].size = u.root_size_before;
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        eq.merge(a, b, asserted(10));
        eq.merge(b, c, asserted(11));
        assert!(eq.are_equal(a, c));
        assert_eq!(eq.find(a), eq.find(c));
    }

    #[test]
    fn pop_restores_pre_merge_state() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        eq.push(); // level 1
        eq.merge(a, b, asserted(20));
        assert!(eq.are_equal(a, b));
        eq.pop(0); // back to level 0
        assert!(!eq.are_equal(a, b));
        assert_ne!(eq.find(a), eq.find(b));
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
