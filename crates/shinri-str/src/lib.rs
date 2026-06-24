mod collect;
mod fuel;
mod trail;
pub use fuel::Fuel;

use rustc_hash::FxHashSet;
use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct StrSolver {
    eq_true: Vec<TermId>,
    diseq_true: Vec<TermId>,
    len_terms: FxHashSet<TermId>,
    str_terms: FxHashSet<TermId>,
    #[allow(dead_code)] // used in Task 9 (len-axiom deduplication) and Task 17 (str-equality propagation)
    emitted_len_axioms: FxHashSet<TermId>,
    #[allow(dead_code)] // used in Task 12 (split lemma deduplication)
    emitted_splits: FxHashSet<(TermId, TermId)>,
    #[allow(dead_code)] // used in Task 12 (fresh skolem variable counter for splits)
    fresh_ctr: u32,
    #[allow(dead_code)] // used in Task 15 (unfolding fuel budget)
    fuel: Fuel,
    trail: trail::Trail,
}

impl TheorySolver for StrSolver {
    const THEORY_ID: u16 = 4;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        let mut seen = FxHashSet::default();
        collect::collect(cx.terms, atom, &mut self.len_terms, &mut self.str_terms, &mut seen);
    }

    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
        // Filled in Task 10 (records asserted string (dis)equalities).
        None
    }

    fn propagate(&mut self, _cx: &mut TheoryCtx, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> {
        None
    }

    fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}

    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}

    fn push(&mut self) {
        self.trail.push(self.eq_true.len(), self.diseq_true.len());
    }

    fn pop(&mut self, level: usize) {
        if let Some((e, d)) = self.trail.pop_to(level) {
            self.eq_true.truncate(e);
            self.diseq_true.truncate(d);
        }
    }

    fn shared_arith_terms(&self, _cx: &mut TheoryCtx) -> Vec<TermId> {
        self.len_terms.iter().copied().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Context, Op, Var};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    #[test]
    fn collects_len_terms_and_returns_sat_initially() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let len = ctx
            .mk_app(
                shinri_core::Op::Builtin(shinri_core::BuiltinOp::StrLen),
                &[x],
            )
            .unwrap();
        let ge = {
            // (>= (str.len x) 0) — an arith atom carrying str.len
            let zero = ctx.mk_numeral(
                shinri_core::Rational::from_int(0i128.into()),
                ctx.int_sort(),
            );
            ctx.mk_app(
                shinri_core::Op::Builtin(shinri_core::BuiltinOp::Ge),
                &[len, zero],
            )
            .unwrap()
        };
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        s.new_var(&mut cx, Var::new(0), ge);
        assert!(
            s.shared_arith_terms(&mut cx).contains(&len),
            "str.len term must be shared"
        );
        assert!(matches!(s.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}
