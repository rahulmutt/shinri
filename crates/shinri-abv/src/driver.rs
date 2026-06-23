//! Refinement controller + the SatBridge seam.
use shinri_core::Context;
use shinri_core::TermId;

/// A BV (dis)equality literal in a lemma: (atom term, polarity).
/// `atom` is a Bool-sorted BV equality `(= u v)` over read vars / indices /
/// elements, or an array-eq proxy. `pos=false` means the negation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LemmaLit {
    pub atom: TermId,
    pub pos: bool,
}

/// A learned clause: the disjunction of its lits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lemma(pub Vec<LemmaLit>);

/// What the controller needs from the SAT/blast layer. Implemented for real by
/// shinri-solver (Task 10) and by a fake in tests.
pub trait SatBridge {
    /// Solve the current clause set. Returns true on SAT.
    fn solve(&mut self) -> bool;
    /// Concrete value of a BV-sorted term in the latest SAT model.
    fn value_bv(&self, ctx: &Context, t: TermId) -> Option<(u32, shinri_num::Integer)>;
    /// Truth of an array-eq proxy term in the latest SAT model.
    fn value_bool(&self, t: TermId) -> Option<bool>;
    /// Ensure `atom` (a Bool-sorted BV (dis)equality) is blasted into the live
    /// solver, returning nothing; idempotent. Mints clauses for any new reads.
    fn ensure_atom(&mut self, ctx: &mut Context, atom: TermId);
    /// Add one lemma clause over already-ensured atoms.
    fn add_lemma(&mut self, ctx: &mut Context, lemma: &Lemma);
}

#[cfg(test)]
pub(crate) mod fake {
    use super::*;
    use rustc_hash::FxHashMap;
    use shinri_num::Integer;

    /// A scripted bridge: returns a fixed model, records lemmas, and (optionally)
    /// flips to a different model / UNSAT after N lemmas are added (to simulate
    /// refinement convergence).
    #[derive(Default)]
    pub struct FakeBridge {
        pub bv: FxHashMap<TermId, (u32, Integer)>,
        pub boolv: FxHashMap<TermId, bool>,
        pub added: Vec<Lemma>,
        pub ensured: Vec<TermId>,
        /// Become UNSAT once `added.len()` reaches this (None = always SAT).
        pub unsat_after: Option<usize>,
    }
    impl SatBridge for FakeBridge {
        fn solve(&mut self) -> bool {
            match self.unsat_after {
                Some(n) => self.added.len() < n,
                None => true,
            }
        }
        fn value_bv(&self, _ctx: &Context, t: TermId) -> Option<(u32, Integer)> {
            self.bv.get(&t).cloned()
        }
        fn value_bool(&self, t: TermId) -> Option<bool> {
            self.boolv.get(&t).copied()
        }
        fn ensure_atom(&mut self, _ctx: &mut Context, atom: TermId) {
            self.ensured.push(atom);
        }
        fn add_lemma(&mut self, _ctx: &mut Context, lemma: &Lemma) {
            self.added.push(lemma.clone());
        }
    }
}
