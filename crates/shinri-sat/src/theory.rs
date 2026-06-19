use crate::types::{Effort, TheoryResult};
use shinri_core::{Lit, TheoryJust, Var};

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
    /// Close `n` scopes (on backtrack).
    fn pop(&mut self, n: usize);
    /// A new variable was allocated.
    fn new_var(&mut self, v: Var);
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
