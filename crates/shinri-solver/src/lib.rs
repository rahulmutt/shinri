//! shinri-solver: the embeddable QF_UF solver entry point. Owns the term DAG,
//! Tseitin-encodes Boolean structure into the CDCL(T) SAT engine, registers EUF
//! atoms, and extracts models. No SMT-LIB parser (assert via the API).

mod model;
mod tseitin;

pub use model::{Model, SolveOutcome};

use shinri_core::{Context, Op, SortId, SymbolId, TermId};
use shinri_num::Rational;

pub struct Solver {
    ctx: Context,
    assertions: Vec<TermId>,
    scopes: Vec<usize>,
    // Canonical Bool constants; used by the Tseitin encoder to handle ⊤/⊥
    // terms. Stored here so check_sat() can pass them to the Encoder
    // without re-building them.
    t_true: TermId,
    t_false: TermId,
    last_model: Option<Model>,
}

impl Default for Solver {
    fn default() -> Self {
        Solver::new()
    }
}

impl Solver {
    pub fn new() -> Solver {
        let mut ctx = Context::new();
        let t_true = ctx.mk_const_bool(true);
        let t_false = ctx.mk_const_bool(false);
        Solver {
            ctx,
            assertions: Vec::new(),
            scopes: Vec::new(),
            t_true,
            t_false,
            last_model: None,
        }
    }

    pub fn declare_sort(&mut self, name: &str) -> SortId {
        self.ctx.declare_sort(name)
    }
    pub fn declare_fun(&mut self, name: &str, params: &[SortId], result: SortId) -> SymbolId {
        self.ctx.declare_fun(name, params, result)
    }
    pub fn bool_sort(&self) -> SortId {
        self.ctx.bool_sort()
    }
    pub fn real_sort(&self) -> SortId {
        self.ctx.real_sort()
    }
    pub fn numeral(&mut self, value: Rational, sort: SortId) -> TermId {
        self.ctx.mk_numeral(value, sort)
    }
    pub fn declare_const(&mut self, name: &str, sort: SortId) -> TermId {
        let f = self.ctx.declare_fun(name, &[], sort);
        self.ctx.mk_app(Op::Uninterpreted(f), &[]).expect("const")
    }
    pub fn app(&mut self, op: Op, args: &[TermId]) -> TermId {
        self.ctx.mk_app(op, args).expect("well-sorted application")
    }
    pub fn eq(&mut self, a: TermId, b: TermId) -> TermId {
        self.ctx.mk_eq(a, b).expect("well-sorted equality")
    }
    pub fn assert(&mut self, formula: TermId) {
        self.assertions.push(formula);
    }

    pub fn push(&mut self) {
        self.scopes.push(self.assertions.len());
    }

    pub fn pop(&mut self, n: usize) {
        for _ in 0..n {
            if let Some(mark) = self.scopes.pop() {
                self.assertions.truncate(mark);
            }
        }
        self.last_model = None;
    }

    pub fn check_sat(&mut self) -> SolveOutcome {
        use crate::tseitin::Encoder;
        use shinri_core::NoProof;
        use shinri_euf::Euf;
        use shinri_sat::{SolveResult, SolverConfig, Vmtf};
        use shinri_theory::Combiner;

        type Sat = shinri_sat::Solver<Combiner<Euf, shinri_arith::Arith>, NoProof, Vmtf>;

        // Lower n-ary distinct to pairwise binary up front (needs &mut ctx).
        let lowered: Vec<TermId> = self
            .assertions
            .clone()
            .into_iter()
            .map(|a| self.lower(a))
            .collect();

        let mut sat: Sat = shinri_sat::Solver::with_theory(
            SolverConfig::default(),
            Combiner::with_context(self.ctx.clone()),
        );
        // set_truth_terms MUST be called before any atom encoding (Euf::new_var
        // installs the level-0 ⊤≠⊥ diseq only if truth_terms is already Some,
        // and assert panics if truth terms are unset).
        sat.theory_mut()
            .euf_mut()
            .set_truth_terms(self.t_true, self.t_false);

        let atom_vars: Vec<(shinri_core::Var, TermId)>;
        let refused: bool;
        let mixed: bool;
        {
            let mut enc = Encoder::new(&self.ctx, &mut sat, self.t_true, self.t_false);
            // Phase 1: encode all formulas, registering all theory atoms with the
            // Combiner BEFORE asserting any unit clauses. This ensures every term
            // is present in the EGraph when the first merge fires, so congruence
            // closure can observe all relevant use-lists.
            let top_lits: Vec<shinri_core::Lit> = lowered.iter().map(|&a| enc.encode(a)).collect();
            // Phase 2: assert each top-level literal as a unit clause. Theory
            // assertions (merges, diseqs) now fire with the full egraph in place.
            for lit in &top_lits {
                enc.assert_top(*lit);
            }
            atom_vars = enc.atom_vars.clone();
            refused = enc.refused;
            mixed = enc.saw_shared || (enc.saw_euf && enc.saw_arith);
        }

        if refused || mixed {
            return SolveOutcome::Unknown;
        }

        match sat.solve() {
            SolveResult::Unsat { .. } => SolveOutcome::Unsat,
            SolveResult::Sat => {
                let mb = sat.theory_mut().build_model();
                let mut model = Model::default();
                for (_v, term) in &atom_vars {
                    if let Some(val) = mb.get(*term) {
                        model.values.insert(*term, val.clone());
                    }
                }
                // Also surface values for all terms assigned by the theories.
                for (term, val) in mb.iter() {
                    model.values.insert(term, val.clone());
                }
                self.last_model = Some(model);
                SolveOutcome::Sat
            }
        }
    }

    pub fn get_model(&mut self) -> Model {
        std::mem::take(&mut self.last_model).unwrap_or_default()
    }

    pub fn get_value(&self, t: TermId) -> Option<shinri_theory::types::ModelVal> {
        self.last_model.as_ref().and_then(|m| m.get(t).cloned())
    }

    /// Preprocessing pass: lowers arithmetic equalities/disequalities to
    /// inequalities, and n-ary distinct to pairwise binary. Recurses through
    /// Boolean connectives. Must run before the Tseitin encoder.
    ///
    /// Rules (Real-sorted operands only):
    ///   `(= a b)`          →  `(and (Le a b) (Ge a b))`
    ///   `(distinct a b)`   →  `(or  (Lt a b) (Gt a b))`
    ///   `(distinct a..n)`  →  `(and (lower(distinct ai aj)) ...)` for all pairs
    ///
    /// EUF/Bool `=` and binary EUF `distinct` pass through unchanged.
    fn lower(&mut self, t: TermId) -> TermId {
        use shinri_core::{BuiltinOp, Op, TermNode};
        match self.ctx.term_node(t).clone() {
            // ── Real equality: (= a b) → (and (Le a b) (Ge a b)) ─────────────
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Eq),
                args,
                ..
            } => {
                let kids: Vec<TermId> = self.ctx.children(args).to_vec();
                // Only rewrite arithmetic (Real-sorted) equalities; leave
                // EUF/Bool equalities for the theory encoder.
                if kids.len() >= 2 && self.ctx.sort_of(kids[0]) == self.ctx.real_sort() {
                    // Real-sorted (= a b c ...) : a == b == c == ...
                    // Chain adjacent pairs: (Le a b)∧(Ge a b) ∧ (Le b c)∧(Ge b c) ∧ ...
                    // Transitivity makes this equivalent to all-equal.
                    let mut conj: Vec<TermId> = Vec::with_capacity((kids.len() - 1) * 2);
                    for w in kids.windows(2) {
                        let le = self
                            .ctx
                            .mk_app(Op::Builtin(BuiltinOp::Le), &[w[0], w[1]])
                            .expect("Le well-sorted");
                        let ge = self
                            .ctx
                            .mk_app(Op::Builtin(BuiltinOp::Ge), &[w[0], w[1]])
                            .expect("Ge well-sorted");
                        conj.push(le);
                        conj.push(ge);
                    }
                    self.ctx
                        .mk_app(Op::Builtin(BuiltinOp::And), &conj)
                        .expect("and well-sorted")
                } else {
                    t
                }
            }
            // ── Distinct ──────────────────────────────────────────────────────
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Distinct),
                args,
                ..
            } => {
                let kids: Vec<TermId> = self.ctx.children(args).to_vec();
                if kids.len() <= 2 {
                    // Binary distinct: rewrite to (or (Lt a b) (Gt a b)) if Real.
                    if self.ctx.sort_of(kids[0]) == self.ctx.real_sort() {
                        let lt = self
                            .ctx
                            .mk_app(Op::Builtin(BuiltinOp::Lt), &[kids[0], kids[1]])
                            .expect("Lt well-sorted");
                        let gt = self
                            .ctx
                            .mk_app(Op::Builtin(BuiltinOp::Gt), &[kids[0], kids[1]])
                            .expect("Gt well-sorted");
                        self.ctx
                            .mk_app(Op::Builtin(BuiltinOp::Or), &[lt, gt])
                            .expect("or well-sorted")
                    } else {
                        // EUF binary distinct: pass through unchanged.
                        t
                    }
                } else {
                    // N-ary distinct: split into pairwise binary distincts, each
                    // recursively lowered (so Real pairs → Lt/Gt, EUF pairs stay).
                    let mut pairs = Vec::new();
                    for i in 0..kids.len() {
                        for j in (i + 1)..kids.len() {
                            let d = self
                                .ctx
                                .mk_app(Op::Builtin(BuiltinOp::Distinct), &[kids[i], kids[j]])
                                .expect("binary distinct well-sorted");
                            // Recurse so Real pairs become (or Lt Gt).
                            let lowered_d = self.lower(d);
                            pairs.push(lowered_d);
                        }
                    }
                    self.ctx
                        .mk_app(Op::Builtin(BuiltinOp::And), &pairs)
                        .expect("and well-sorted")
                }
            }
            // ── Boolean connectives: recurse ──────────────────────────────────
            TermNode::App {
                op: Op::Builtin(b),
                args,
                ..
            } if matches!(
                b,
                BuiltinOp::Not
                    | BuiltinOp::And
                    | BuiltinOp::Or
                    | BuiltinOp::Implies
                    | BuiltinOp::Xor
                    | BuiltinOp::Ite
            ) =>
            {
                let kids: Vec<TermId> = self.ctx.children(args).to_vec();
                let lowered: Vec<TermId> = kids.into_iter().map(|k| self.lower(k)).collect();
                self.ctx
                    .mk_app(Op::Builtin(b), &lowered)
                    .expect("well-sorted")
            }
            _ => t,
        }
    }
}

#[cfg(test)]
impl Solver {
    pub(crate) fn encode_for_test(
        &mut self,
        formula: TermId,
    ) -> (shinri_core::Lit, Vec<(shinri_core::Var, TermId)>) {
        use crate::tseitin::Encoder;
        use shinri_core::NoProof;
        use shinri_euf::Euf;
        use shinri_sat::{SolverConfig, Vmtf};
        use shinri_theory::Combiner;

        type Sat = shinri_sat::Solver<Combiner<Euf, shinri_arith::Arith>, NoProof, Vmtf>;

        let mut sat: Sat = shinri_sat::Solver::with_theory(
            SolverConfig::default(),
            Combiner::with_context(self.ctx.clone()),
        );
        let mut enc = Encoder::new(&self.ctx, &mut sat, self.t_true, self.t_false);
        let lit = enc.encode(formula);
        (lit, enc.atom_vars.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn solver_builds_terms() {
        let mut s = Solver::new();
        let u = s.declare_sort("U");
        let af = s.declare_fun("a", &[], u);
        let a = s.app(Op::Uninterpreted(af), &[]);
        let bf = s.declare_fun("b", &[], u);
        let b = s.app(Op::Uninterpreted(bf), &[]);
        let e = s.eq(a, b);
        s.assert(e);
        // a == b is satisfiable (Task 14 implements check_sat)
        assert_eq!(s.check_sat(), SolveOutcome::Sat);
    }

    #[test]
    fn unsat_x_eq_y_and_fx_neq_fy() {
        use shinri_core::{BuiltinOp, Op};
        let mut s = Solver::new();
        let u = s.declare_sort("U");
        let xf = s.declare_fun("x", &[], u);
        let x = s.app(Op::Uninterpreted(xf), &[]);
        let yf = s.declare_fun("y", &[], u);
        let y = s.app(Op::Uninterpreted(yf), &[]);
        let f = s.declare_fun("f", &[u], u);
        let fx = s.app(Op::Uninterpreted(f), &[x]);
        let fy = s.app(Op::Uninterpreted(f), &[y]);
        let xy = s.eq(x, y);
        let ffeq = s.eq(fx, fy);
        let nffeq = s.app(Op::Builtin(BuiltinOp::Not), &[ffeq]);
        s.assert(xy);
        s.assert(nffeq);
        assert_eq!(s.check_sat(), SolveOutcome::Unsat);
    }

    #[test]
    fn sat_with_model() {
        use shinri_core::Op;
        let mut s = Solver::new();
        let u = s.declare_sort("U");
        let af = s.declare_fun("a", &[], u);
        let a = s.app(Op::Uninterpreted(af), &[]);
        let bf = s.declare_fun("b", &[], u);
        let b = s.app(Op::Uninterpreted(bf), &[]);
        let ab = s.eq(a, b);
        s.assert(ab);
        assert_eq!(s.check_sat(), SolveOutcome::Sat);
        let m = s.get_model();
        assert_eq!(m.get(a), m.get(b));
    }

    // Helpers: three uninterpreted constants of a fresh sort.
    fn three_consts(s: &mut Solver) -> (TermId, TermId, TermId) {
        let u = s.declare_sort("U");
        let af = s.declare_fun("a", &[], u);
        let a = s.app(Op::Uninterpreted(af), &[]);
        let bf = s.declare_fun("b", &[], u);
        let b = s.app(Op::Uninterpreted(bf), &[]);
        let cf = s.declare_fun("c", &[], u);
        let c = s.app(Op::Uninterpreted(cf), &[]);
        (a, b, c)
    }

    /// REGRESSION (aux-var panic): a top-level `(and (= a b) (= b c))` mints an
    /// auxiliary Tseitin var for the `And`; the SAT layer asserts it during
    /// solve(), which pre-fix paniced in `Combiner::assert` (owner() on an
    /// unregistered aux var). Must now solve to Sat.
    #[test]
    fn and_of_equalities_solves_sat() {
        use shinri_core::{BuiltinOp, Op};
        let mut s = Solver::new();
        let (a, b, c) = three_consts(&mut s);
        let ab = s.eq(a, b);
        let bc = s.eq(b, c);
        let conj = s.app(Op::Builtin(BuiltinOp::And), &[ab, bc]);
        s.assert(conj);
        assert_eq!(s.check_sat(), SolveOutcome::Sat);
    }

    /// REGRESSION (n-ary distinct path): `(distinct a b c)` is lowered to an
    /// `And` of binary distincts, which mints an aux var. Pre-fix this paniced;
    /// now it solves to Sat (three distinct elements are satisfiable).
    #[test]
    fn nary_distinct_solves_sat() {
        use shinri_core::{BuiltinOp, Op};
        let mut s = Solver::new();
        let (a, b, c) = three_consts(&mut s);
        let distinct = s.app(Op::Builtin(BuiltinOp::Distinct), &[a, b, c]);
        s.assert(distinct);
        assert_eq!(s.check_sat(), SolveOutcome::Sat);
    }

    /// REGRESSION + soundness: `(distinct a b c) ∧ (= a b)` exercises the aux-var
    /// path (the distinct lowering produces an And) AND verifies distinct
    /// soundness end-to-end: a≠b is required, but a=b is asserted → Unsat.
    #[test]
    fn nary_distinct_with_conflicting_eq_is_unsat() {
        use shinri_core::{BuiltinOp, Op};
        let mut s = Solver::new();
        let (a, b, c) = three_consts(&mut s);
        let distinct = s.app(Op::Builtin(BuiltinOp::Distinct), &[a, b, c]);
        let ab = s.eq(a, b);
        s.assert(distinct);
        s.assert(ab);
        assert_eq!(s.check_sat(), SolveOutcome::Unsat);
    }
}
