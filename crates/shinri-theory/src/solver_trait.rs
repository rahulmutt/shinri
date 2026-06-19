//! The per-theory abstraction (spec §5). Sub-theories see only the shared
//! context, never the SAT solver. Conflicts and explanations are expressed in
//! `EqLeaf` antecedents the Combiner expands.

use crate::eq_engine::EqualityEngine;
use crate::model::ModelBuilder;
use crate::types::EqLeaf;
use crate::AtomRegistry;
use crate::Explainer;
use shinri_core::{Context, Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;

/// The borrowed context threaded into every `TheorySolver` call (spec §5.1).
pub struct TheoryCtx<'a> {
    pub terms: &'a Context,
    pub eq: &'a mut EqualityEngine,
    pub atoms: &'a AtomRegistry,
}

/// A sub-theory consistency verdict. Convex Phase-1 theories produce conflicts,
/// never free-standing lemmas (combination lemmas are the Combiner's job).
pub enum TCheck {
    Sat,
    Conflict(Vec<EqLeaf>),
}

/// `pop(level)` uses ABSOLUTE target levels (matching `EqualityEngine`/`UndoLog`).
/// The Combiner translates the SAT seam's "close n scopes" into a target once.
pub trait TheorySolver: Default {
    const THEORY_ID: u16;

    fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId);
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>>;
    fn propagate(
        &mut self,
        cx: &mut TheoryCtx,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>>;
    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck;
    fn explain(&mut self, cx: &mut TheoryCtx, tag: u32, exp: &mut Explainer);
    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder);
    fn push(&mut self);
    fn pop(&mut self, level: usize);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A do-nothing theory: proves the trait is implementable and object-safe
    /// in the monomorphized sense (used as a Combiner stub in later tasks).
    #[derive(Default)]
    struct NullTheory;

    impl TheorySolver for NullTheory {
        const THEORY_ID: u16 = 99;
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
        fn check(&mut self, _cx: &mut TheoryCtx, _effort: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _level: usize) {}
    }

    #[test]
    fn null_theory_checks_sat() {
        let mut t = NullTheory::default();
        let terms = Context::new();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &terms,
            eq: &mut eq,
            atoms: &atoms,
        };
        assert!(matches!(t.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}
