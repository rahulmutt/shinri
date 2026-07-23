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
    Arrays,
    String,
    Datatypes,
}

/// A range into `EqualityEngine`'s congruence-pair arena (keeps `EqJust` `Copy`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct CongRef {
    pub start: u32,
    pub len: u32,
}

/// The justification on a proof-forest edge (spec §4.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EqJust {
    /// An input equality literal `a = b` was asserted.
    Asserted(Lit),
    /// `f(s..) = f(t..)` because each argument pair is equal. The pairs live in
    /// `EqualityEngine.cong_pairs[start .. start+len]`.
    Congruence(CongRef),
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
///
/// `a`/`b` are the nodes passed to the operation that detected the conflict
/// (the merged app nodes for `merge`/`merge_congruence`; the just-asserted pair
/// for `assert_diseq`). `diseq_lhs`/`diseq_rhs` are the ORIGINAL endpoint nodes
/// that were passed to `assert_diseq` when the violated disequality was stored
/// (NOT their representatives). The two may differ from `a`/`b` when the diseq
/// was asserted between different class members — callers must bridge
/// `a`↔`diseq_lhs`/`diseq_rhs` (oriented by representative) to build a sound,
/// sufficient conflict clause.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct EqConflict {
    pub a: ENodeId,
    pub b: ENodeId,
    pub diseq: EqJust,
    /// The disequality's left endpoint as originally asserted.
    pub diseq_lhs: ENodeId,
    /// The disequality's right endpoint as originally asserted.
    pub diseq_rhs: ENodeId,
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
    /// A bitvector value: `(width, unsigned_value)`.
    /// `unsigned_value` is a non-negative integer in `[0, 2^width)`.
    BitVec(u32, shinri_core::Integer), // width, value
    /// A string value (QF_S / SLIA).
    String(std::string::String),
    /// A floating-point value: `(eb, sb, bits)` where `bits` is the W=eb+sb
    /// unsigned bit pattern, MSB→LSB `[sign | exp | trailing-sig]`.
    Float {
        eb: u32,
        sb: u32,
        bits: shinri_core::Integer,
    },
    /// A rounding-mode value (slice 6: RM variables get model entries).
    Rm(shinri_core::RoundingMode),
    /// A datatype value, pre-rendered as an SMT-LIB ground constructor term
    /// (e.g. `nil`, `(cons 1 nil)`). Rendered by the DT theory, which has the
    /// `Context`; `format_modelval` has none.
    Datatype(std::string::String),
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
