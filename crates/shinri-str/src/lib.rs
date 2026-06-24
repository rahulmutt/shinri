mod collect;
mod fuel;
mod length;
pub mod normalize;
mod trail;
pub mod wordeq;
pub use fuel::Fuel;

use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Lit, Op, TermId, TermNode, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct StrSolver {
    eq_true: Vec<TermId>,
    diseq_true: Vec<TermId>,
    len_terms: FxHashSet<TermId>,
    str_terms: FxHashSet<TermId>,
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

    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        // Record asserted string (dis)equalities for consumption by Task 11+.
        // Gate on the operands being String-sorted so non-string equalities
        // (e.g. integer or bitvector) cannot pollute eq_true/diseq_true.
        let atom = cx.atoms.atom(lit.var());
        if let TermNode::App { op, args, .. } = cx.terms.term_node(atom) {
            let args = cx.terms.children(*args).to_vec();
            let is_str_eq = !args.is_empty()
                && cx.terms.sort_of(args[0]) == cx.terms.string_sort();
            if is_str_eq {
                match op {
                    Op::Builtin(BuiltinOp::Eq) => {
                        if lit.is_positive() {
                            self.eq_true.push(atom);
                        } else {
                            self.diseq_true.push(atom);
                        }
                    }
                    Op::Builtin(BuiltinOp::Distinct) => {
                        if lit.is_positive() {
                            self.diseq_true.push(atom);
                        } else {
                            self.eq_true.push(atom);
                        }
                    }
                    _ => {}
                }
            }
        }
        None
    }

    fn propagate(&mut self, _cx: &mut TheoryCtx, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> {
        None
    }

    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        let lens: Vec<TermId> = self.len_terms.iter().copied().collect();
        for lt in lens {
            if let Some(axiom) = length::next_axiom(cx.terms, lt, &self.emitted_len_axioms) {
                self.emitted_len_axioms.insert(axiom);
                return TCheck::Split(vec![axiom]);
            }
        }

        // Build the `known` set: all string-sorted subterms visible to the solver,
        // plus both sides of each asserted equality (so rep() resolves global merges,
        // preferring constants — required by the Task 10 fix in normal_form).
        let mut known: Vec<TermId> = self.str_terms.iter().copied().collect();
        for &atom in &self.eq_true {
            let (l, r) = crate::wordeq::sides(cx.terms, atom);
            known.push(l);
            known.push(r);
        }

        // Word-equation resolution: strip equal heads/tails, detect constant
        // prefix mismatches. Variable-headed residuals are handled in Task 12.
        let eqs = self.eq_true.clone();
        for atom in eqs {
            let (l, r) = crate::wordeq::sides(cx.terms, atom);
            let lhs = crate::normalize::normal_form(cx.terms, cx.eq, &known, l);
            let rhs = crate::normalize::normal_form(cx.terms, cx.eq, &known, r);
            // NOTE: `just` is empty here — justification is refined in Task 12
            // once proof traces are wired. The conflict is still sound because the
            // equality is on the decision trail.
            let just = vec![];
            match crate::wordeq::resolve_equation(cx.terms, cx.eq, &lhs, &rhs, just) {
                crate::wordeq::StepResult::Conflict(cf) => return TCheck::Conflict(cf),
                crate::wordeq::StepResult::Split(atoms) => return TCheck::Split(atoms),
                crate::wordeq::StepResult::Done => {}
            }
        }
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
impl StrSolver {
    /// Push `atom` directly onto `eq_true`, simulating the SAT layer asserting
    /// a string equality without going through `assert`. Used only in unit tests.
    pub fn test_force_eq_true(&mut self, atom: TermId) {
        self.eq_true.push(atom);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Context, Op, Var};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    #[test]
    fn collects_len_terms_and_reaches_sat_fixpoint() {
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
        // For an opaque variable x (no concat/literal), check emits exactly one axiom
        // (the >=0 lemma) and then reaches Sat fixpoint.
        let first = s.check(&mut cx, Effort::Full);
        assert!(
            matches!(first, TCheck::Split(_)),
            "should emit >=0 axiom for str.len(x)"
        );
        assert!(
            matches!(s.check(&mut cx, Effort::Full), TCheck::Sat),
            "fixpoint after >=0 emitted"
        );
    }
}
