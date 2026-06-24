mod collect;
mod fuel;
mod length;
pub mod model;
pub mod normalize;
pub mod reduce;
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
    /// Asserted string equalities: (atom, the literal that asserted it).
    /// The `Lit` is used to build `EqLeaf::Asserted` justifications for conflicts.
    eq_true: Vec<(TermId, Lit)>,
    diseq_true: Vec<(TermId, Lit)>,
    len_terms: FxHashSet<TermId>,
    str_terms: FxHashSet<TermId>,
    emitted_len_axioms: FxHashSet<TermId>,
    /// Dedup set for F-splits: keyed on the canonical (unordered) head pair.
    /// Monotone (never cleared on backtrack); prevents re-emitting the same
    /// split after dedup (termination guarantee).
    emitted_splits: FxHashSet<(TermId, TermId)>,
    /// Counter for fresh string skolem variables minted by F-split.
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
                            self.eq_true.push((atom, lit));
                        } else {
                            self.diseq_true.push((atom, lit));
                        }
                    }
                    Op::Builtin(BuiltinOp::Distinct) => {
                        if lit.is_positive() {
                            self.diseq_true.push((atom, lit));
                        } else {
                            self.eq_true.push((atom, lit));
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

        // Build the `known` set FIRST: all string-sorted subterms visible to the
        // solver, plus both sides of each asserted equality.
        // This must be built before the len_terms loop so `next_axiom` can consult
        // EUF representatives (e.g. to detect that `str.len(x) = 0` when `x = ""`
        // was merged via the EqualityEngine — the N-O length seam).
        let mut known: Vec<TermId> = self.str_terms.iter().copied().collect();
        for &(atom, _) in &self.eq_true {
            let (l, r) = crate::wordeq::sides(cx.terms, atom);
            known.push(l);
            known.push(r);
        }

        let lens: Vec<TermId> = self.len_terms.iter().copied().collect();
        for lt in lens {
            if let Some(axiom) = length::next_axiom(cx.terms, cx.eq, &known, lt, &self.emitted_len_axioms) {
                self.emitted_len_axioms.insert(axiom);
                // Spend one unit of fuel before emitting a split. If the budget is
                // exhausted, signal Unknown (sound: neither Sat nor Unsat).
                if !self.fuel.spend() {
                    return TCheck::Unknown;
                }
                // Length axioms (e.g. (= (str.len "café") 4), len(x++y)=len x+len y,
                // len ≥ 0) are unconditionally valid over the string/length theory —
                // tautology splits, no guard.
                return TCheck::Split { atoms: vec![axiom], guard: None };
            }
        }

        // (The `known` set continues to be used below.)

        // Word-equation resolution: strip equal heads/tails, detect constant
        // prefix mismatches. Variable-headed residuals emit F-splits (Task 12).
        let eqs: Vec<(TermId, Lit)> = self.eq_true.clone();
        for (atom, lit) in eqs {
            let (l, r) = crate::wordeq::sides(cx.terms, atom);
            let lhs = crate::normalize::normal_form(cx.terms, cx.eq, &known, l);
            let rhs = crate::normalize::normal_form(cx.terms, cx.eq, &known, r);
            // Build the EqLeaf justification from the asserted equality literal.
            // This feeds `expand_conflict` so the conflict clause cites the right input literal.
            let just = vec![EqLeaf::Asserted(lit)];
            match crate::wordeq::resolve_equation(
                cx.terms,
                cx.eq,
                &lhs,
                &rhs,
                just,
                lit,
                &mut self.fresh_ctr,
                &mut self.emitted_splits,
            ) {
                crate::wordeq::StepResult::Conflict(cf) => return TCheck::Conflict(cf),
                crate::wordeq::StepResult::Split { atoms, guard } => {
                    // Register the new str.len terms produced by the F-split so
                    // their length axioms are emitted on the next check round.
                    // The F-split atoms are: [len_eq, a_pref, b_pref].
                    // len_eq = (= (str.len a) (str.len b)); extract the len sub-terms.
                    let mut seen = FxHashSet::default();
                    for &split_atom in &atoms {
                        collect::collect(
                            cx.terms,
                            split_atom,
                            &mut self.len_terms,
                            &mut self.str_terms,
                            &mut seen,
                        );
                    }
                    // Spend one unit of fuel before emitting a word-equation split.
                    // If the budget is exhausted, signal Unknown (sound).
                    if !self.fuel.spend() {
                        return TCheck::Unknown;
                    }
                    // GUARDED split: `guard = ¬eqn`. The learnt clause is
                    // `¬eqn ∨ len_eq ∨ a_pref ∨ b_pref` ≡ `eqn → (…)`, a valid
                    // implication (Nielsen lemma) — NOT the unsound bare disjunction.
                    return TCheck::Split { atoms, guard: Some(guard) };
                }
                crate::wordeq::StepResult::Done => {}
            }
        }

        // Disequality same-word conflict check (Task 14).
        //
        // For each asserted `s ≠ t`, compute the normal forms of both sides and
        // check atom-wise equality. If the normal forms are identical (the two sides
        // denote the same word), the disequality is contradicted → Conflict.
        //
        // Soundness: the conflict justification MUST include the disequality literal
        // AND any equality antecedents that caused pairs in the normal forms to be
        // merged in the EqualityEngine (e.g. `x = "a"` was asserted, so `x` and `"a"`
        // appear equal in the normal form). `nf_equal_explain` gathers those
        // antecedents via `eq.explain`, mirroring the EUF conflict pattern in
        // `shinri-euf/src/egraph.rs::conflict_leaves` (the `explain(a, b, out)` path
        // for the merge-antecedent part).
        let diseqs: Vec<(TermId, Lit)> = self.diseq_true.clone();
        for (atom, lit) in diseqs {
            let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);

            // Case 1: direct EUF class equality — `l` and `r` are in the same
            // EqualityEngine class, so they trivially denote the same word. This
            // handles e.g. `x ≠ "a"++y` when `x = "a"++y` was merged in the EUF
            // (the normal-form comparison cannot detect this since `x` is opaque).
            //
            // Soundness (mirroring EUF `egraph.rs::assert_diseq` conflict pattern):
            // The conflict cites the diseq literal PLUS the equality antecedents from
            // the proof forest (via `eq.explain`). `eq.explain` walks the path
            // between l and r in the proof forest, collecting `EqLeaf::Asserted`
            // leaves — these are the input equality literals that forced the merge.
            // If the merge was `EqJust::Definitional`, explain returns nothing (which
            // is still sound: a definitional equality is unconditionally true, so the
            // diseq literal alone is a sufficient contradiction).
            let ln = cx.eq.intern(l);
            let rn = cx.eq.intern(r);
            if cx.eq.are_equal(ln, rn) {
                let mut just = vec![EqLeaf::Asserted(lit)];
                cx.eq.explain(ln, rn, &mut just);
                return TCheck::Conflict(just);
            }

            // Case 2: same-word conflict via normal-form comparison — catches cases
            // like `"a"++x ≠ "a"++y` when `x = y` was asserted in the EUF. Here l
            // and r are NOT in the same EUF class directly, but their normal forms
            // (after substituting class representatives) are atom-wise equal.
            //
            // Extend `known` to include both sides of the disequality so that
            // normal_form can reflect any merges involving these terms.
            let mut known_d = known.clone();
            known_d.push(l);
            known_d.push(r);
            // Use `deep_normal_form` which recursively expands concat-valued class
            // representatives (e.g. when `x = "a"++y` was merged, the NF of `x`
            // should be `["a", y]` after one expansion level).
            let lhs = crate::normalize::deep_normal_form(cx.terms, cx.eq, &known_d, l);
            let rhs = crate::normalize::deep_normal_form(cx.terms, cx.eq, &known_d, r);
            if crate::wordeq::nf_equal(cx.terms, cx.eq, &lhs, &rhs) {
                // Build conflict: diseq literal + merge antecedents for each pair.
                let mut just = vec![EqLeaf::Asserted(lit)];
                crate::wordeq::nf_equal_explain(cx.terms, cx.eq, &lhs, &rhs, &mut just);
                return TCheck::Conflict(just);
            }
        }

        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}

    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        self.model_with(cx, m);
    }

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

impl StrSolver {
    /// Assemble concrete string values into the model.
    ///
    /// Called by `TheorySolver::model`; also exposed so tests can inject a
    /// pre-seeded `ModelBuilder` (e.g. with arith-model lengths already set).
    pub fn model_with(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        let str_terms: Vec<TermId> = self.str_terms.iter().copied().collect();
        model::assign(cx.terms, cx.eq, &str_terms, m);
    }
}

#[cfg(test)]
impl StrSolver {
    /// Push `atom` directly onto `eq_true`, simulating the SAT layer asserting
    /// a string equality without going through `assert`. Used only in unit tests.
    /// Uses a dummy Lit (var 0, positive) since the justification is not exercised
    /// in unit tests (no combiner expand_conflict path).
    pub fn test_force_eq_true(&mut self, atom: TermId) {
        self.eq_true.push((atom, Lit::new(Var::new(0), true)));
    }

    /// Push `atom` directly onto `diseq_true`, simulating the SAT layer asserting
    /// a string disequality. Uses a dummy Lit (var 0, positive) since the test
    /// exercises the conflict detection path, not the full conflict-expansion path.
    pub fn test_force_diseq_true(&mut self, atom: TermId) {
        self.diseq_true.push((atom, Lit::new(Var::new(0), true)));
    }

    /// Override the fuel budget. Used only in unit tests to force exhaustion.
    pub fn test_set_fuel(&mut self, n: u32) {
        self.fuel = Fuel { remaining: n };
    }

    /// Force a term into `str_terms` without going through `new_var`.
    /// Used in unit tests to seed model construction.
    pub fn test_force_str_term(&mut self, t: TermId) {
        self.str_terms.insert(t);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, ModelBuilder, TCheck, TheoryCtx, TheorySolver};
    use shinri_theory::types::ModelVal;

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
        // For an opaque variable x (no concat/literal), check emits two axioms:
        //   1. (>= (str.len x) 0)
        //   2. (=> (= (str.len x) 0) (= x ""))  [empty-length link, Task 14]
        // then reaches Sat fixpoint.
        let first = s.check(&mut cx, Effort::Full);
        assert!(
            matches!(first, TCheck::Split { .. }),
            "should emit >=0 axiom for str.len(x)"
        );
        let second = s.check(&mut cx, Effort::Full);
        assert!(
            matches!(second, TCheck::Split { .. }),
            "should emit empty-length link axiom for str.len(x)"
        );
        assert!(
            matches!(s.check(&mut cx, Effort::Full), TCheck::Sat),
            "fixpoint after all axioms emitted"
        );
    }

    #[test]
    fn fuel_exhaustion_yields_unknown_not_hang() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");
        // x ++ y = y ++ x : classic diverging word equation.
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y]).unwrap();
        let r = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[y, x]).unwrap();
        let atom = ctx.mk_eq(l, r).unwrap();
        let mut s = StrSolver::default();
        s.test_set_fuel(3); // tiny budget — exhausts before all 5 axioms/splits
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        s.test_force_eq_true(atom);
        let mut got_unknown = false;
        for _ in 0..50 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Unknown => { got_unknown = true; break; }
                TCheck::Split { .. } => continue,
                _ => break,
            }
        }
        assert!(got_unknown, "tiny fuel must force Unknown, never an infinite split loop");
    }

    // With len(x)=2 fixed and no constant constraints, x's model is "AA".
    #[test]
    fn free_var_model_filled_with_default_char() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = { let f = ctx.declare_fun("x", &[], str_s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
        let lenx = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut m = ModelBuilder::default();
        // Seed the model with len(x) = 2 (as arith would).
        m.assign(lenx, ModelVal::Num(shinri_core::Rational::from_int(2i64.into())));
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &areg };
        s.new_var(&mut cx, shinri_core::Var::new(0), lenx);
        s.test_force_str_term(x);
        s.model_with(&mut cx, &mut m);
        assert_eq!(m.get(x), Some(&ModelVal::String("AA".into())));
    }
}
