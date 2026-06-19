use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct Euf {
    // Filled in across Tasks 6–11.
    inner: crate::egraph::EGraph,
    level: usize,
}

impl TheorySolver for Euf {
    const THEORY_ID: u16 = 1;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        use shinri_core::{BuiltinOp, Op, TermNode};
        match cx.terms.term_node(atom) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct),
                args,
                ..
            } => {
                let args_slice = *args;
                let kids: Vec<shinri_core::TermId> = cx.terms.children(args_slice).to_vec();
                for k in kids {
                    self.inner.add_term(cx, k);
                }
            }
            _ => {
                // Predicate application (or any other EUF atom term).
                self.inner.add_term(cx, atom);
            }
        }
    }
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        use shinri_core::{BuiltinOp, Op, TermNode};
        use shinri_theory::types::EqJust;
        let atom = cx.atoms.atom(lit.var());
        let just = EqJust::Asserted(lit);
        match cx.terms.term_node(atom) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Eq),
                args,
                ..
            } => {
                let args_slice = *args;
                let kids: Vec<shinri_core::TermId> = cx.terms.children(args_slice).to_vec();
                debug_assert_eq!(kids.len(), 2, "Eq atom must be binary");
                let a = cx.eq.intern(kids[0]);
                let b = cx.eq.intern(kids[1]);
                if lit.is_positive() {
                    self.inner.merge_eq(cx.eq, a, b, just)
                } else {
                    self.inner.assert_diseq(cx.eq, a, b, just)
                }
            }
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Distinct),
                args,
                ..
            } => {
                let args_slice = *args;
                let kids: Vec<shinri_core::TermId> = cx.terms.children(args_slice).to_vec();
                debug_assert_eq!(kids.len(), 2, "Distinct lowered to binary (Task 13)");
                let a = cx.eq.intern(kids[0]);
                let b = cx.eq.intern(kids[1]);
                if lit.is_positive() {
                    self.inner.assert_diseq(cx.eq, a, b, just)
                } else {
                    self.inner.merge_eq(cx.eq, a, b, just)
                }
            }
            _ => None,
        }
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
