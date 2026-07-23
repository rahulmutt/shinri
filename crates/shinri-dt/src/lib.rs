//! QF_DT datatype theory: lemma-on-demand over the shared EqualityEngine.
//! Owns no equality state; emits datatype axiom instances as positive-atom
//! clauses via `TCheck::Split` and clashes via `TCheck::Conflict`.

use rustc_hash::FxHashSet;
use shinri_core::{Context, DtRole, Lit, Op, SymbolId, TermId, TermNode, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

/// Datatype theory solver. Holds no union-find: all equality state lives in the
/// shared `EqualityEngine`, and every derived fact is emitted as a lemma or a
/// conflict. Watch sets are monotone (assignment-independent), so `push`/`pop`
/// are no-ops — the `shinri-arrays` pattern.
#[derive(Default)]
pub struct DtSolver {
    /// Constructor applications `C(a1..an)` seen in registered atoms.
    ctor_apps: FxHashSet<TermId>,
    /// Selector applications `sel(t)`.
    sel_apps: FxHashSet<TermId>,
    /// Tester applications `is-C(t)`.
    testers: FxHashSet<TermId>,
    /// Every term (of any role) whose sort is a datatype sort — the superset
    /// Task 8's completeness fence needs, not just selector/tester arguments.
    dt_terms: FxHashSet<TermId>,
    /// Lemmas already emitted, so `check` reaches a fixpoint instead of
    /// re-emitting the same tautology forever.
    #[allow(dead_code)]
    emitted: FxHashSet<TermId>,
}

impl DtSolver {
    /// Walk an atom's term DAG, indexing every datatype-relevant application
    /// and every datatype-sorted term. Does not guard against revisiting
    /// shared subterms — matches `shinri-arrays::collect`, which re-walks
    /// shared subterms too; insertion into an `FxHashSet` is idempotent so
    /// this is a performance concern only, not a correctness one.
    fn collect(&mut self, terms: &Context, t: TermId) {
        if terms.is_datatype_sort(terms.sort_of(t)) {
            self.dt_terms.insert(t);
        }
        let (op, kids) = match terms.term_node(t) {
            TermNode::App { op, args, .. } => (*op, terms.children(*args).to_vec()),
            TermNode::Const { .. } => return,
        };
        if let Op::Uninterpreted(sym) = op {
            match terms.dt_role(sym) {
                Some(DtRole::Constructor { .. }) => {
                    self.ctor_apps.insert(t);
                }
                Some(DtRole::Selector { .. }) => {
                    self.sel_apps.insert(t);
                }
                Some(DtRole::Tester { .. }) => {
                    self.testers.insert(t);
                }
                None => {}
            }
        }
        for k in kids {
            self.collect(terms, k);
        }
    }

    /// `(symbol, children)` of an uninterpreted application, or `None`.
    #[allow(dead_code)]
    fn uapp(terms: &Context, t: TermId) -> Option<(SymbolId, Vec<TermId>)> {
        match terms.term_node(t) {
            TermNode::App {
                op: Op::Uninterpreted(s),
                args,
                ..
            } => Some((*s, terms.children(*args).to_vec())),
            _ => None,
        }
    }

    #[cfg(test)]
    pub(crate) fn watches_ctor(&self, t: TermId) -> bool {
        self.ctor_apps.contains(&t)
    }
    #[cfg(test)]
    pub(crate) fn watches_sel(&self, t: TermId) -> bool {
        self.sel_apps.contains(&t)
    }
    #[cfg(test)]
    pub(crate) fn watches_tester(&self, t: TermId) -> bool {
        self.testers.contains(&t)
    }
    #[cfg(test)]
    pub(crate) fn watches_dt_term(&self, t: TermId) -> bool {
        self.dt_terms.contains(&t)
    }
}

impl TheorySolver for DtSolver {
    const THEORY_ID: u16 = 5;

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

    fn check(&mut self, _cx: &mut TheoryCtx, _effort: Effort) -> TCheck {
        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {
        // DT conflicts cite EqLeafs directly; no tags of its own yet.
    }

    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}

    fn push(&mut self) {}
    fn pop(&mut self, _level: usize) {}
}

#[cfg(test)]
mod tests {
    use crate::DtSolver;
    use shinri_core::{Context, Op, SortId, SymbolId, TermId, Var};
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    /// Declare `List ::= nil | cons(head: Int, tail: List)` and return
    /// `(list_sort, nil, cons, head, tail, is_nil, is_cons)`.
    pub(crate) fn list_dt(
        ctx: &mut Context,
    ) -> (
        SortId,
        SymbolId,
        SymbolId,
        SymbolId,
        SymbolId,
        SymbolId,
        SymbolId,
    ) {
        let list = ctx.declare_datatype_sort("List");
        let int = ctx.int_sort();
        let b = ctx.bool_sort();
        let nil = ctx.declare_fun("nil", &[], list);
        let is_nil = ctx.declare_fun("is-nil", &[list], b);
        ctx.dt_add_constructor(list, nil, &[], is_nil);
        let cons = ctx.declare_fun("cons", &[int, list], list);
        let head = ctx.declare_fun("head", &[list], int);
        let tail = ctx.declare_fun("tail", &[list], list);
        let is_cons = ctx.declare_fun("is-cons", &[list], b);
        ctx.dt_add_constructor(list, cons, &[head, tail], is_cons);
        (list, nil, cons, head, tail, is_nil, is_cons)
    }

    pub(crate) fn uconst(ctx: &mut Context, name: &str, s: SortId) -> TermId {
        let sym = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn new_var_indexes_constructor_selector_and_tester_apps() {
        let mut ctx = Context::new();
        let (list, nil, cons, head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let x = uconst(&mut ctx, "x", list);
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let head_x = ctx.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();
        let atom = ctx.mk_eq(x, cons_t).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), head_x);
        dt.new_var(&mut cx, Var::new(2), is_cons_x);

        assert!(dt.watches_ctor(cons_t), "cons application must be indexed");
        assert!(dt.watches_ctor(nil_t), "nullary nil must be indexed");
        assert!(
            dt.watches_sel(head_x),
            "selector application must be indexed"
        );
        assert!(dt.watches_tester(is_cons_x), "tester must be indexed");
        assert!(dt.watches_dt_term(x), "datatype-sorted var must be indexed");
        assert!(
            dt.watches_dt_term(cons_t),
            "datatype-sorted constructor application must be indexed"
        );
    }
}
