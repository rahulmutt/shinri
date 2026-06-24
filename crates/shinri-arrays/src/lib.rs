//! QF_AX array theory: lazy read-over-write (ROW) lemma-on-demand over the
//! shared EqualityEngine. Owns no equality state; emits ROW axiom instances as
//! positive-atom clauses via TCheck::Split. Congruence-only N-O participant.

use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, TermNode, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct Arrays {
    /// Watched select(arr, idx) terms. Monotone (assignment-independent).
    selects: FxHashSet<TermId>,
    /// Watched store(arr, idx, elt) terms. Monotone.
    stores: FxHashSet<TermId>,
}

impl Arrays {
    /// Walk an atom's term DAG, recording every select/store sub-application.
    fn collect(&mut self, terms: &Context, t: TermId) {
        let (op, kids) = match terms.term_node(t) {
            TermNode::App { op, args, .. } => (*op, terms.children(*args).to_vec()),
            TermNode::Const { .. } => return,
        };
        match op {
            Op::Builtin(BuiltinOp::Select) => {
                self.selects.insert(t);
            }
            Op::Builtin(BuiltinOp::Store) => {
                self.stores.insert(t);
            }
            _ => {}
        }
        for k in kids {
            self.collect(terms, k);
        }
    }

    /// (op, children) of an App term, or None.
    fn app(terms: &Context, t: TermId) -> Option<(Op, Vec<TermId>)> {
        match terms.term_node(t) {
            TermNode::App { op, args, .. } => Some((*op, terms.children(*args).to_vec())),
            TermNode::Const { .. } => None,
        }
    }

    fn equal(cx: &mut TheoryCtx, a: TermId, b: TermId) -> bool {
        let an = cx.eq.intern(a);
        let bn = cx.eq.intern(b);
        cx.eq.are_equal(an, bn)
    }
}

impl TheorySolver for Arrays {
    const THEORY_ID: u16 = 3;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        self.collect(cx.terms, atom);
    }

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

    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        let selects: Vec<TermId> = self.selects.iter().copied().collect();
        let stores: Vec<TermId> = self.stores.iter().copied().collect();
        for sel in selects {
            let Some((_, sel_args)) = Self::app(cx.terms, sel) else {
                continue;
            };
            let (arr, j) = (sel_args[0], sel_args[1]);
            for &st in &stores {
                if !Self::equal(cx, arr, st) {
                    continue;
                }
                let Some((_, st_args)) = Self::app(cx.terms, st) else {
                    continue;
                };
                let (b, i, e) = (st_args[0], st_args[1], st_args[2]);
                if Self::equal(cx, i, j) {
                    // ROW-1: sel = e
                    if !Self::equal(cx, sel, e) {
                        let lemma = cx.terms.mk_eq(sel, e).expect("well-sorted");
                        // ROW-1 is a McCarthy-axiom T-tautology — no guard.
                        return TCheck::Split { atoms: vec![lemma], guard: None };
                    }
                } else {
                    // ROW-2: (i = j) ∨ (sel = select(b, j))
                    let selbj = cx
                        .terms
                        .mk_app(Op::Builtin(BuiltinOp::Select), &[b, j])
                        .expect("well-sorted");
                    if !Self::equal(cx, sel, selbj) {
                        let eqij = cx.terms.mk_eq(i, j).expect("well-sorted");
                        let eqsel = cx.terms.mk_eq(sel, selbj).expect("well-sorted");
                        // ROW-2 is a McCarthy-axiom T-tautology — no guard.
                        return TCheck::Split { atoms: vec![eqij, eqsel], guard: None };
                    }
                }
            }
        }
        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {
        // Arrays cites no equalities of its own; ROW lemma atoms are EUF-owned.
    }

    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}

    fn push(&mut self) {} // monotone, assignment-independent state
    fn pop(&mut self, _level: usize) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqJust, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
        let sym = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn row1_emits_select_equals_stored_value() {
        let mut ctx = Context::new();
        let i_s = ctx.declare_sort("I");
        let e_s = ctx.declare_sort("E");
        let arr_s = ctx.array_sort(i_s, e_s);
        let a = uconst(&mut ctx, "a", arr_s);
        let i = uconst(&mut ctx, "i", i_s);
        let e = uconst(&mut ctx, "e", e_s);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        // an equality atom carrying the select; arrays watches it
        let atom = ctx.mk_eq(sel, e).unwrap();

        let mut arrays = Arrays::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arrays.new_var(&mut cx, shinri_core::Var::new(0), atom);

        match arrays.check(&mut cx, Effort::Full) {
            TCheck::Split { atoms, .. } => {
                // The lemma forces sel = e (the same eq term, or a fresh equal one).
                assert!(!atoms.is_empty(), "ROW-1 must emit a lemma");
            }
            other => panic!(
                "expected Split, got {:?}",
                match other {
                    TCheck::Sat => "Sat",
                    TCheck::Conflict(_) => "Conflict",
                    TCheck::Split { .. } => unreachable!(),
                    TCheck::Unknown => unreachable!("Arrays never returns Unknown"),
                }
            ),
        }
        // Once sel and e are merged, no further lemma is emitted (fixpoint).
        let sn = cx.eq.intern(sel);
        let en = cx.eq.intern(e);
        let _ = cx.eq.merge(sn, en, EqJust::Definitional);
        assert!(matches!(arrays.check(&mut cx, Effort::Full), TCheck::Sat));
    }

    #[test]
    fn row2_emits_disjunctive_split_when_index_undecided() {
        let mut ctx = Context::new();
        let i_s = ctx.declare_sort("I");
        let e_s = ctx.declare_sort("E");
        let arr_s = ctx.array_sort(i_s, e_s);
        let a = uconst(&mut ctx, "a", arr_s);
        let i = uconst(&mut ctx, "i", i_s);
        let j = uconst(&mut ctx, "j", i_s);
        let e = uconst(&mut ctx, "e", e_s);
        let v = uconst(&mut ctx, "v", e_s);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, j])
            .unwrap();
        let atom = ctx.mk_eq(sel, v).unwrap();

        let mut arrays = Arrays::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arrays.new_var(&mut cx, shinri_core::Var::new(0), atom);

        match arrays.check(&mut cx, Effort::Full) {
            TCheck::Split { atoms, .. } => assert_eq!(atoms.len(), 2, "ROW-2 split has two disjuncts"),
            other => panic!(
                "expected 2-atom Split, got {:?}",
                match other {
                    TCheck::Sat => "Sat",
                    TCheck::Conflict(_) => "Conflict",
                    TCheck::Split { .. } => unreachable!(),
                    TCheck::Unknown => unreachable!("Arrays never returns Unknown"),
                }
            ),
        }
    }
}
