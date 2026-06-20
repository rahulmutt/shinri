use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct Euf {
    // Filled in across Tasks 6–11.
    inner: crate::egraph::EGraph,
    level: usize,
    /// Canonical ⊤/⊥ Bool constant TermIds; set by the owner of the mutable Context.
    truth_terms: Option<(TermId, TermId)>,
}

impl Euf {
    /// Provide the canonical Bool ⊤/⊥ terms (created by the owner of the
    /// mutable `Context`). Must be called before asserting predicate atoms.
    pub fn set_truth_terms(&mut self, t_true: TermId, t_false: TermId) {
        self.truth_terms = Some((t_true, t_false));
    }
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
                // Register the ⊤/⊥ sentinels and the Definitional ⊤≠⊥ diseq NOW,
                // at level 0 (registration always happens before solving). This
                // guarantees ⊤≠⊥ is installed exactly once at decision level 0 and
                // survives all backtracking — asserting it lazily inside `assert`
                // would record its undo at whatever level the first predicate atom
                // appears, letting a pop drop it (the I1 soundness bug). Only do so
                // when the truth terms are available (standalone EUF sets them via
                // `set_truth_terms`; the combiner registers atoms at level 0).
                if let Some((t_true, t_false)) = self.truth_terms {
                    self.inner.truth_nodes(cx, t_true, t_false);
                }
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
            _ => {
                // Uninterpreted predicate application: p(args) merged with ⊤/⊥.
                let (t_true, t_false) = self
                    .truth_terms
                    .expect("set_truth_terms must precede predicate asserts");
                let (tn, fln) = self.inner.truth_nodes(cx, t_true, t_false);
                let pnode = self.inner.add_term(cx, atom);
                let target = if lit.is_positive() { tn } else { fln };
                self.inner.merge_eq(cx.eq, pnode, target, just)
            }
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
    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        use rustc_hash::FxHashMap;
        use shinri_theory::types::ModelVal;
        let truth = self.inner.truth();
        // Collect registered terms into a local Vec to avoid borrow conflicts.
        let registered: Vec<(shinri_core::TermId, shinri_theory::types::ENodeId)> =
            self.inner.registered_terms().to_vec();
        let mut elem_of: FxHashMap<(shinri_core::SortId, shinri_theory::types::ENodeId), u32> =
            FxHashMap::default();
        for (term, _node) in registered {
            let node = cx.eq.intern(term);
            let rep = cx.eq.find(node);
            if let Some((tn, fln)) = truth {
                if cx.eq.find(tn) == rep {
                    m.assign(term, ModelVal::Bool(true));
                    continue;
                }
                if cx.eq.find(fln) == rep {
                    m.assign(term, ModelVal::Bool(false));
                    continue;
                }
            }
            let sort = cx.terms.sort_of(term);
            let next = elem_of.len() as u32;
            let id = *elem_of.entry((sort, rep)).or_insert(next);
            m.assign(term, ModelVal::Elem(sort, id));
        }
    }
    fn push(&mut self) {
        self.level += 1;
        self.inner.push();
    }
    fn pop(&mut self, level: usize) {
        self.inner.pop(level);
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
