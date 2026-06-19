//! Leaf vocabulary for the theory-combination layer.

use shinri_core::{Lit, Rational, SortId, TheoryJust};

/// Dense index into `EqualityEngine`'s e-node arena.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ENodeId(u32);

impl ENodeId {
    #[inline]
    pub fn new(raw: u32) -> ENodeId {
        ENodeId(raw)
    }
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Which sub-theory owns a Boolean atom (drives `Combiner` enum routing).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Owner {
    Euf,
    Arith,
    Shared,
}

/// The justification on a proof-forest edge (spec §4.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EqJust {
    /// An input equality literal `a = b` was asserted.
    Asserted(Lit),
    /// `f(s..) = f(t..)` because each argument pair `(si, ti)` is equal.
    Congruence(ENodeId, ENodeId),
    /// An equality another theory derived; expandable via that theory's `explain`.
    Interface(TheoryJust),
    /// An unconditional definitional equality (e.g. a purification interface
    /// variable's defining equation `w := def`). Always true; contributes no
    /// antecedent to any explanation.
    Definitional,
}

/// A leaf produced by walking the proof forest: either an input literal or a
/// still-to-expand interface justification (resolved by the `Combiner`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EqLeaf {
    Asserted(Lit),
    Interface(TheoryJust),
}

/// The disequal pair a `merge` would have violated, plus the disequality's
/// own justification (so the conflict clause can cite it).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct EqConflict {
    pub a: ENodeId,
    pub b: ENodeId,
    pub diseq: EqJust,
}

/// Accumulates an explanation. `lits` are resolved input literals; `pending`
/// holds interface justifications the `Combiner` will expand to a fixpoint.
#[derive(Default, Debug)]
pub struct Explainer {
    pub lits: Vec<Lit>,
    pub pending: Vec<TheoryJust>,
}

impl Explainer {
    #[inline]
    pub fn push_lit(&mut self, l: Lit) {
        self.lits.push(l);
    }
    #[inline]
    pub fn push_leaf(&mut self, leaf: EqLeaf) {
        match leaf {
            EqLeaf::Asserted(l) => self.lits.push(l),
            EqLeaf::Interface(j) => self.pending.push(j),
        }
    }
    /// Consume the accumulated literals (dedup is the caller's concern).
    #[inline]
    pub fn take_lits(&mut self) -> Vec<Lit> {
        std::mem::take(&mut self.lits)
    }
}

/// A value in the combined model (spec §7.3).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ModelVal {
    Bool(bool),
    Num(Rational),
    /// An abstract domain element for an uninterpreted sort.
    Elem(SortId, u32),
}

/// A class-union that occurred, surfaced to consumers via `drain_merges`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct MergeEvent {
    pub a: ENodeId,
    pub b: ENodeId,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn enodeid_roundtrips() {
        let n = ENodeId::new(7);
        assert_eq!(n.index(), 7);
    }

    #[test]
    fn explainer_accumulates_lits_and_pending() {
        let mut e = Explainer::default();
        let l = Lit::new(shinri_core::Var::new(3), true);
        e.push_leaf(EqLeaf::Asserted(l));
        e.push_leaf(EqLeaf::Interface(TheoryJust { theory: 1, tag: 9 }));
        assert_eq!(e.pending.len(), 1);
        assert_eq!(e.take_lits(), vec![l]);
    }

    #[test]
    fn modelval_is_small() {
        // Bool/Elem variants stay compact; Num holds a Rational by value.
        assert!(size_of::<ModelVal>() >= size_of::<Rational>());
    }
}
