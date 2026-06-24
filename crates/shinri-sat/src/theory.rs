use crate::types::{Effort, TheoryResult};
use shinri_core::{Lit, TermId, TheoryJust, Var};

/// The theory-integration seam (spec §8.1). Implemented by `shinri-theory`.
/// `NoTheory` makes every method inline to nothing, leaving a pure CDCL solver.
pub trait Theory: Default {
    /// A Boolean literal was placed on the trail.
    fn assert(&mut self, lit: Lit);
    /// Theory propagation: push implied `(lit, justification)` pairs into `out`.
    /// Returns `Some(conflict_lits)` if the theory is inconsistent.
    fn propagate(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>>;
    /// Reconstruct the *true* antecedent literals whose conjunction implied the
    /// literal that carried `just` (lazily, only when analysis needs it).
    fn explain(&mut self, just: TheoryJust, out: &mut Vec<Lit>);
    /// Consistency check at the given effort. `Full` runs before declaring SAT.
    fn check(&mut self, effort: Effort) -> TheoryResult;
    /// Open a backtracking scope (one per SAT decision level).
    fn push(&mut self);
    /// Close `n` scopes (on backtrack). Note: variable registrations made via
    /// `new_var` are permanent and are NOT undone by `pop` — theory-preserving
    /// rebuild relies on this invariant.
    fn pop(&mut self, n: usize);
    /// A new variable was allocated.
    fn new_var(&mut self, v: Var);
    /// Bind a freshly-minted split atom to the var the solver just allocated
    /// for it (splitting on demand, QF_LIA Plan A). Called once per atom in a
    /// `TheoryResult::SplitAtoms` clause, BEFORE the clause is learnt, so the
    /// theory can register `v -> atom` and build its encoding. Default no-op:
    /// theories that never emit `SplitAtoms` need not implement it.
    fn bind_fresh(&mut self, _v: Var, _atom: TermId) {}
    /// If `atom` already has a SAT var registered with the theory, return it.
    /// The split-atom protocol calls this BEFORE minting a fresh var so an
    /// already-registered atom (e.g. an MBTC `(= u v)` that was previously
    /// asserted, or a length atom shared with String/Arith) REUSES its existing
    /// var instead of getting a second, unlinked one. Returning `None` (the
    /// default) preserves the original mint-fresh behaviour.
    fn var_for_atom(&self, _atom: TermId) -> Option<Var> {
        None
    }
}

/// The zero-cost default theory: a ZST whose methods compile to nothing.
#[derive(Default)]
pub struct NoTheory;

impl Theory for NoTheory {
    #[inline(always)]
    fn assert(&mut self, _lit: Lit) {}
    #[inline(always)]
    fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
        None
    }
    #[inline(always)]
    fn explain(&mut self, _just: TheoryJust, _out: &mut Vec<Lit>) {}
    #[inline(always)]
    fn check(&mut self, _effort: Effort) -> TheoryResult {
        TheoryResult::Sat
    }
    #[inline(always)]
    fn push(&mut self) {}
    #[inline(always)]
    fn pop(&mut self, _n: usize) {}
    #[inline(always)]
    fn new_var(&mut self, _v: Var) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bind_fresh_default_is_noop_and_overridable() {
        #[derive(Default)]
        struct Recorder {
            bound: Vec<(Var, TermId)>,
        }
        impl Theory for Recorder {
            fn new_var(&mut self, _v: Var) {}
            fn assert(&mut self, _l: Lit) {}
            fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
                None
            }
            fn check(&mut self, _e: Effort) -> TheoryResult {
                TheoryResult::Sat
            }
            fn explain(&mut self, _j: TheoryJust, _out: &mut Vec<Lit>) {}
            fn push(&mut self) {}
            fn pop(&mut self, _n: usize) {}
            fn bind_fresh(&mut self, v: Var, atom: TermId) {
                self.bound.push((v, atom));
            }
        }
        let mut r = Recorder::default();
        let v = Var::new(3);
        let t = TermId::new(9).unwrap();
        r.bind_fresh(v, t);
        assert_eq!(r.bound, vec![(v, t)]);
    }
}
