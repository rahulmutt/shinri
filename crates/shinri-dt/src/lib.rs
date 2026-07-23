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

    /// Selector-collapse: for `sel_i(t)` and a constructor app `C(a1..an)` in
    /// the same class as `t`, emit the TAUTOLOGY `sel_i(C(a1..an)) = a_i`.
    ///
    /// Written over the constructor application itself the lemma is
    /// unconditional — congruence supplies `sel_i(t) ≡ sel_i(C(a..))` — so no
    /// guard is needed. Fires only when `sel_i` belongs to `C`: for a foreign
    /// selector SMT-LIB leaves the value unspecified and collapsing is unsound.
    fn collapse_lemma(&mut self, cx: &mut TheoryCtx) -> Option<TCheck> {
        let sels: Vec<TermId> = self.sel_apps.iter().copied().collect();
        let ctors: Vec<TermId> = self.ctor_apps.iter().copied().collect();
        for sel in sels {
            let Some((sel_sym, sel_args)) = Self::uapp(cx.terms, sel) else {
                continue;
            };
            let Some(DtRole::Selector { ctor, index }) = cx.terms.dt_role(sel_sym) else {
                continue;
            };
            let t = sel_args[0];
            let tn = cx.eq.intern(t);
            for &capp in &ctors {
                let Some((csym, cargs)) = Self::uapp(cx.terms, capp) else {
                    continue;
                };
                // Foreign selector: value unspecified, no lemma.
                if csym != ctor {
                    continue;
                }
                let cn = cx.eq.intern(capp);
                if !cx.eq.are_equal(tn, cn) {
                    continue;
                }
                let arg = cargs[index as usize];
                let sel_on_ctor = cx
                    .terms
                    .mk_app(Op::Uninterpreted(sel_sym), &[capp])
                    .expect("selector applies to its own datatype sort");
                let sn = cx.eq.intern(sel_on_ctor);
                let an = cx.eq.intern(arg);
                if cx.eq.are_equal(sn, an) {
                    continue; // already installed — fixpoint
                }
                let lemma = cx
                    .terms
                    .mk_eq(sel_on_ctor, arg)
                    .expect("selector result sort matches the field sort");
                if !self.emitted.insert(lemma) {
                    continue; // emitted before and not yet installed; avoid a loop
                }
                return Some(TCheck::Split {
                    atoms: vec![lemma],
                    guard: None,
                    phases: Vec::new(),
                });
            }
        }
        None
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

    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        if let Some(split) = self.collapse_lemma(cx) {
            return split;
        }
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
    use shinri_core::{Context, Op, SortId, SymbolId, TermId, TermNode, Var};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqJust, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    fn tcheck_name(c: &TCheck) -> &'static str {
        match c {
            TCheck::Sat => "Sat",
            TCheck::Conflict(_) => "Conflict",
            TCheck::Split { .. } => "Split",
            TCheck::Unknown => "Unknown",
        }
    }

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

    #[test]
    fn selector_collapse_emits_tautology_for_matching_constructor() {
        let mut ctx = Context::new();
        let (list, nil, cons, head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let head_x = ctx.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
        let atom = ctx.mk_eq(head_x, one).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), cons_t);

        // Before x ≡ cons(1,nil) there is nothing to collapse.
        assert!(matches!(dt.check(&mut cx, Effort::Full), TCheck::Sat));

        // Merge x with the constructor application.
        let xn = cx.eq.intern(x);
        let cn = cx.eq.intern(cons_t);
        let _ = cx.eq.merge(xn, cn, EqJust::Definitional);

        match dt.check(&mut cx, Effort::Full) {
            TCheck::Split { atoms, guard, .. } => {
                assert_eq!(guard, None, "collapse is an unconditional tautology");
                assert_eq!(atoms.len(), 1, "collapse emits a unit lemma");
                // The lemma is `head(cons(1,nil)) = 1`.
                let expected_sel = cx.terms.mk_app(Op::Uninterpreted(head), &[cons_t]).unwrap();
                let expected = cx.terms.mk_eq(expected_sel, one).unwrap();
                assert_eq!(atoms[0], expected);
            }
            other => panic!("expected Split, got {}", tcheck_name(&other)),
        }
    }

    #[test]
    fn selector_collapse_does_not_fire_for_foreign_selector() {
        // `head` belongs to `cons`; applying it to a term equal to `nil` leaves
        // the value UNSPECIFIED. Collapsing here would be unsound.
        let mut ctx = Context::new();
        let (list, nil, _cons, head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let x = uconst(&mut ctx, "x", list);
        let head_x = ctx.mk_app(Op::Uninterpreted(head), &[x]).unwrap();
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let atom = ctx.mk_eq(head_x, one).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), nil_t);
        let xn = cx.eq.intern(x);
        let nn = cx.eq.intern(nil_t);
        let _ = cx.eq.merge(xn, nn, EqJust::Definitional);

        assert!(
            matches!(dt.check(&mut cx, Effort::Full), TCheck::Sat),
            "head over a nil-class must NOT collapse"
        );
    }

    #[test]
    fn collapse_reaches_fixpoint_after_lemma_is_installed() {
        let mut ctx = Context::new();
        let (_list, nil, cons, head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int_sort = ctx.int_sort();
        let one = uconst(&mut ctx, "one", int_sort);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let cons_t = ctx.mk_app(Op::Uninterpreted(cons), &[one, nil_t]).unwrap();
        let head_c = ctx.mk_app(Op::Uninterpreted(head), &[cons_t]).unwrap();
        let atom = ctx.mk_eq(head_c, one).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        assert!(matches!(
            dt.check(&mut cx, Effort::Full),
            TCheck::Split { .. }
        ));
        // Installing the lemma's equality must silence the rule.
        let hn = cx.eq.intern(head_c);
        let on = cx.eq.intern(one);
        let _ = cx.eq.merge(hn, on, EqJust::Definitional);
        assert!(
            matches!(dt.check(&mut cx, Effort::Full), TCheck::Sat),
            "collapse must reach a fixpoint"
        );
    }

    #[test]
    fn injectivity_is_a_consequence_of_collapse_and_congruence() {
        // cons(a, nil) ≡ cons(b, nil)  ⇒  a ≡ b, with NO dedicated injectivity
        // rule: the two collapse lemmas plus congruence on `head` suffice.
        let mut ctx = Context::new();
        let (_list, nil, cons, head, _tail, _is_nil, _is_cons) = list_dt(&mut ctx);
        let int = ctx.int_sort();
        let a = uconst(&mut ctx, "a", int);
        let b = uconst(&mut ctx, "b", int);
        let nil_t = ctx.mk_app(Op::Uninterpreted(nil), &[]).unwrap();
        let ca = ctx.mk_app(Op::Uninterpreted(cons), &[a, nil_t]).unwrap();
        let cb = ctx.mk_app(Op::Uninterpreted(cons), &[b, nil_t]).unwrap();
        let head_ca = ctx.mk_app(Op::Uninterpreted(head), &[ca]).unwrap();
        let head_cb = ctx.mk_app(Op::Uninterpreted(head), &[cb]).unwrap();
        let atom = ctx.mk_eq(ca, cb).unwrap();

        let mut dt = DtSolver::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        dt.new_var(&mut cx, Var::new(0), atom);
        dt.new_var(&mut cx, Var::new(1), head_ca);
        dt.new_var(&mut cx, Var::new(2), head_cb);

        // The SAT/EUF layer merges the two constructor apps and, by congruence,
        // their head-applications. Simulate both here.
        let (can, cbn) = (cx.eq.intern(ca), cx.eq.intern(cb));
        let _ = cx.eq.merge(can, cbn, EqJust::Definitional);
        let (hca, hcb) = (cx.eq.intern(head_ca), cx.eq.intern(head_cb));
        let _ = cx.eq.merge(hca, hcb, EqJust::Definitional);

        // Drain both collapse lemmas, installing each as the SAT layer would.
        for _ in 0..2 {
            match dt.check(&mut cx, Effort::Full) {
                TCheck::Split { atoms: lemma, .. } => {
                    let (l, r) = match cx.terms.term_node(lemma[0]) {
                        TermNode::App { args, .. } => {
                            let kids = cx.terms.children(*args).to_vec();
                            (kids[0], kids[1])
                        }
                        _ => panic!("lemma must be an equality application"),
                    };
                    let (ln, rn) = (cx.eq.intern(l), cx.eq.intern(r));
                    let _ = cx.eq.merge(ln, rn, EqJust::Definitional);
                }
                other => panic!("expected Split, got {}", tcheck_name(&other)),
            }
        }

        let (an, bn) = (cx.eq.intern(a), cx.eq.intern(b));
        assert!(
            cx.eq.are_equal(an, bn),
            "injectivity must emerge: a ≡ b after collapse + congruence"
        );
    }
}
