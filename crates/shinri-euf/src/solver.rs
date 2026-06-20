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

    fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId) {
        use shinri_core::{BuiltinOp, Op, TermNode};
        match cx.terms.term_node(atom) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Eq),
                args,
                ..
            } => {
                let args_slice = *args;
                let kids: Vec<shinri_core::TermId> = cx.terms.children(args_slice).to_vec();
                let a = self.inner.add_term(cx, kids[0]);
                let b = self.inner.add_term(cx, kids[1]);
                self.inner.register_eq_atom(v.index() as u32, a, b);
            }
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Distinct),
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
        cx: &mut TheoryCtx,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        let props = self.inner.collect_eq_propagations(cx.eq);
        for (vi, tag) in props {
            let lit = Lit::new(Var::new(vi), true);
            out.push((
                lit,
                TheoryJust {
                    theory: Self::THEORY_ID,
                    tag,
                },
            ));
        }
        None
    }
    fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        TCheck::Sat
    }
    fn explain(&mut self, cx: &mut TheoryCtx, tag: u32, exp: &mut Explainer) {
        let (a, b) = self.inner.prop_record(tag);
        let mut leaves = Vec::new();
        cx.eq.explain(a, b, &mut leaves);
        for leaf in leaves {
            exp.push_leaf(leaf);
        }
    }
    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        use rustc_hash::FxHashMap;
        use shinri_theory::types::ModelVal;
        let truth = self.inner.truth();
        // Collect registered terms into a local Vec to avoid borrow conflicts.
        let registered: Vec<(shinri_core::TermId, shinri_theory::types::ENodeId)> =
            self.inner.registered_terms().to_vec();
        let mut elem_of: FxHashMap<(shinri_core::SortId, shinri_theory::types::ENodeId), u32> =
            FxHashMap::default();
        let real_s = cx.terms.real_sort();
        let int_s = cx.terms.int_sort();
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
            // Skip Real/Int-sorted terms: the Arith theory assigns their numeric
            // values. EUF assigning Elem(...) for them would conflict with Arith's
            // Num(...) assignments and trigger the model seam debug_assert.
            if sort == real_s || sort == int_s {
                continue;
            }
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

    // ----- Nelson-Oppen seam (Task 12b) -------------------------------------

    /// The shared Real-sorted terms EUF reasons about: every registered term of
    /// Real sort. These are handed to arith (which interns vars / pins numerals)
    /// and used as the N-O candidate set for entailed-equality exchange.
    fn shared_real_terms(&self, cx: &mut TheoryCtx) -> Vec<TermId> {
        let real_s = cx.terms.real_sort();
        self.inner
            .registered_terms()
            .iter()
            .map(|(t, _)| *t)
            .filter(|&t| cx.terms.sort_of(t) == real_s)
            .collect()
    }

    /// Arith→EUF: an arith-entailed equality `a = b` between shared Real terms.
    /// Merge the e-nodes and close congruence (so e.g. f(a)≡f(b) is derived);
    /// a violated disequality returns conflict leaves carrying the interface
    /// justification (which the combiner resolves via arith's `explain`).
    fn consume_interface_equality(
        &mut self,
        cx: &mut TheoryCtx,
        a: TermId,
        b: TermId,
        just: TheoryJust,
    ) -> Option<Vec<EqLeaf>> {
        use shinri_theory::types::EqJust;
        let an = cx.eq.intern(a);
        let bn = cx.eq.intern(b);
        self.inner.merge_eq(cx.eq, an, bn, EqJust::Interface(just))
    }

    /// EUF→arith: mint an explanation tag for a currently-equal pair `(a, b)`.
    /// PRECONDITION: `a` and `b` are equal in `cx.eq` (the combiner checks
    /// `are_equal` first). Resolvable via this theory's `explain`, which expands
    /// `a = b` to its input-literal antecedents over the live proof forest.
    fn mint_eq_tag(&mut self, cx: &mut TheoryCtx, a: TermId, b: TermId) -> u32 {
        let an = cx.eq.intern(a);
        let bn = cx.eq.intern(b);
        debug_assert!(
            cx.eq.are_equal(an, bn),
            "mint_eq_tag requires a == b in the shared engine"
        );
        self.inner.record_interface_pair(an, bn)
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
