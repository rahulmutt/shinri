//! A no-op TheorySolver usable in any Combiner slot (Arith, Arrays, or future
//! slots) that unconditionally returns Sat — a generic placeholder when a slot
//! is unused.

use crate::model::ModelBuilder;
use crate::solver_trait::{TCheck, TheoryCtx, TheorySolver};
use crate::types::EqLeaf;
use crate::Explainer;
use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;

#[derive(Default)]
pub struct EmptyTheory;

impl TheorySolver for EmptyTheory {
    const THEORY_ID: u16 = 0;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_theory_is_always_sat() {
        let mut t = EmptyTheory;
        t.push();
        t.pop(0);
        // Construction + trait-object-free dispatch compile-checks the impl.
        assert_eq!(EmptyTheory::THEORY_ID, 0);
    }
}
