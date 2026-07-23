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
    /// Test-only instrumentation: total `collect` invocations (including
    /// early returns on an already-seen term), so a test can pin that the
    /// `seen` guard keeps the walk linear in DAG size instead of exponential
    /// in sharing depth.
    #[cfg(test)]
    collect_calls: u32,
}

impl DtSolver {
    /// Walk an atom's term DAG, indexing every datatype-relevant application
    /// and every datatype-sorted term. `seen` guards against re-walking a
    /// shared subterm reachable via multiple paths — mirroring
    /// `shinri-str::collect::collect` (`crates/shinri-str/src/collect.rs`),
    /// not `shinri-arrays::collect` (which has no such guard). Datatype terms
    /// are the one domain here where deep, naturally-recursive, heavily-shared
    /// structure is the norm (nested lists/trees, `let`-shared subtrees), so
    /// an unmemoized walk is exponential in sharing depth rather than linear
    /// in DAG size.
    fn collect(&mut self, terms: &Context, t: TermId, seen: &mut FxHashSet<TermId>) {
        #[cfg(test)]
        {
            self.collect_calls += 1;
        }
        if !seen.insert(t) {
            return;
        }
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
            self.collect(terms, k, seen);
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
    #[cfg(test)]
    pub(crate) fn collect_calls(&self) -> u32 {
        self.collect_calls
    }
}

impl TheorySolver for DtSolver {
    const THEORY_ID: u16 = 5;

    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        let mut seen = FxHashSet::default();
        self.collect(cx.terms, atom, &mut seen);
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

        // Negative assertions: non-datatype-sorted terms must NOT land in
        // dt_terms, and head_x/is_cons_x must not be misclassified into the
        // wrong role set either.
        assert!(
            !dt.watches_dt_term(one),
            "Int-sorted term must not be indexed as a dt_term"
        );
        assert!(
            !dt.watches_dt_term(head_x),
            "Int-sorted selector output must not be indexed as a dt_term"
        );
        assert!(
            !dt.watches_ctor(head_x),
            "selector output must not be a ctor_app"
        );
        assert!(
            !dt.watches_tester(head_x),
            "selector output must not be a tester"
        );
        assert!(
            !dt.watches_dt_term(is_cons_x),
            "Bool-sorted tester application must not be indexed as a dt_term"
        );
    }

    /// The `seen` guard in `collect` must keep the walk linear in DAG size,
    /// not exponential in sharing depth. Build a chain of N `and`-doublings
    /// over `is-cons(x)`: `level_i = and(level_{i-1}, level_{i-1})`. Every
    /// level's two children are literally the SAME term, so each level is a
    /// diamond join. With the guard, `collect` on `level_N` makes exactly
    /// `2 + 2*N` calls (each level contributes one fresh recursive descent
    /// plus one immediate "already seen" return); without it, the same walk
    /// would make on the order of `2^N` calls (verified by hand: N=10 gives
    /// 22 guarded calls vs. 3071 unguarded — see task-5-report.md Fix 1).
    #[test]
    fn collect_seen_guard_keeps_shared_subterm_walk_linear() {
        let mut ctx = Context::new();
        let (list, _nil, _cons, _head, _tail, _is_nil, is_cons) = list_dt(&mut ctx);
        let x = uconst(&mut ctx, "x", list);
        let is_cons_x = ctx.mk_app(Op::Uninterpreted(is_cons), &[x]).unwrap();

        const N: u32 = 10;
        let mut level = is_cons_x;
        for _ in 0..N {
            level = ctx
                .mk_app(
                    shinri_core::Op::Builtin(shinri_core::BuiltinOp::And),
                    &[level, level],
                )
                .unwrap();
        }

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), level);

        assert_eq!(
            dt.collect_calls(),
            2 + 2 * N,
            "seen guard must keep the walk linear (2 + 2N), not exponential in sharing depth"
        );
        // Correctness survives the guard: the shared leaves are still indexed.
        assert!(
            dt.watches_tester(is_cons_x),
            "shared tester subterm still indexed once"
        );
        assert!(
            dt.watches_dt_term(x),
            "shared datatype var still indexed once"
        );
    }
}
