use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct Euf {
    // Filled in across Tasks 6–11.
    #[allow(dead_code)]
    inner: crate::egraph::EGraph,
    level: usize,
}

impl TheorySolver for Euf {
    const THEORY_ID: u16 = 1;

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
    fn push(&mut self) {
        self.level += 1;
    }
    fn pop(&mut self, level: usize) {
        self.level = level;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn euf_constructs_and_has_theory_id_one() {
        let _e = Euf::default();
        assert_eq!(Euf::THEORY_ID, 1);
    }
}
