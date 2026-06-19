use crate::ids::{ClauseId, Lit};

/// An opaque justification a theory attaches to a lemma. Captured in Phase 1,
/// interpreted (EUF proof-forest / LRA Farkas) when proof emission lands in
/// Phase 2 (spec §8.1). `theory` identifies the producing theory; `tag` is a
/// theory-private handle into its own explanation state.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TheoryJust {
    pub theory: u16,
    pub tag: u32,
}

/// The proof-production seam (spec §8). Threaded through clause add/learn/delete
/// from day one. Methods take borrowed, already-computed data so that with the
/// `NoProof` impl every call dead-code-eliminates (zero cost when off).
/// Emission (Alethe / LRAT) is a Phase-2 consumer of what this captures.
pub trait ProofSink {
    /// An input (asserted) clause entered the database.
    fn input(&mut self, c: ClauseId, lits: &[Lit]);
    /// A learned clause, with its resolution/derivation chain (the LRAT hint),
    /// harvested from 1-UIP conflict analysis's existing antecedent walk.
    fn learn(&mut self, c: ClauseId, lits: &[Lit], chain: &[ClauseId]);
    /// A theory lemma, tagged with its theory justification.
    fn theory_lemma(&mut self, c: ClauseId, lits: &[Lit], just: TheoryJust);
    /// A clause was deleted from the database.
    fn delete(&mut self, c: ClauseId);
}

/// The default, zero-cost sink: a ZST whose methods inline to nothing.
pub struct NoProof;

impl ProofSink for NoProof {
    #[inline(always)]
    fn input(&mut self, _c: ClauseId, _lits: &[Lit]) {}
    #[inline(always)]
    fn learn(&mut self, _c: ClauseId, _lits: &[Lit], _chain: &[ClauseId]) {}
    #[inline(always)]
    fn theory_lemma(&mut self, _c: ClauseId, _lits: &[Lit], _just: TheoryJust) {}
    #[inline(always)]
    fn delete(&mut self, _c: ClauseId) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ids::{ClauseId, Lit, Var};

    // A recording sink proves the trait is object-usable and captures the chain.
    #[derive(Default)]
    struct Recorder {
        learns: Vec<(ClauseId, Vec<Lit>, Vec<ClauseId>)>,
        deletes: Vec<ClauseId>,
    }
    impl ProofSink for Recorder {
        fn input(&mut self, _c: ClauseId, _lits: &[Lit]) {}
        fn learn(&mut self, c: ClauseId, lits: &[Lit], chain: &[ClauseId]) {
            self.learns.push((c, lits.to_vec(), chain.to_vec()));
        }
        fn theory_lemma(&mut self, _c: ClauseId, _lits: &[Lit], _just: TheoryJust) {}
        fn delete(&mut self, c: ClauseId) {
            self.deletes.push(c);
        }
    }

    #[test]
    fn recorder_captures_learn_chain() {
        let mut r = Recorder::default();
        let c = ClauseId::new(3);
        let lits = [Lit::new(Var::new(0), true), Lit::new(Var::new(1), false)];
        let chain = [ClauseId::new(1), ClauseId::new(2)];
        r.learn(c, &lits, &chain);
        r.delete(c);
        assert_eq!(r.learns.len(), 1);
        assert_eq!(r.learns[0].2, vec![ClauseId::new(1), ClauseId::new(2)]);
        assert_eq!(r.deletes, vec![c]);
    }

    #[test]
    fn noproof_is_zero_sized() {
        assert_eq!(std::mem::size_of::<NoProof>(), 0);
        // Exercise the no-op methods (they must compile and do nothing).
        let mut p = NoProof;
        p.input(ClauseId::new(0), &[]);
        p.learn(ClauseId::new(0), &[], &[]);
        p.delete(ClauseId::new(0));
    }
}
