//! shinri-solver: the embeddable QF_UF solver entry point. Owns the term DAG,
//! Tseitin-encodes Boolean structure into the CDCL(T) SAT engine, registers EUF
//! atoms, and extracts models. No SMT-LIB parser (assert via the API).

mod model;
mod tseitin;

pub use model::{Model, SolveOutcome};

/// The result of executing one SMT-LIB command. Model/value payloads are
/// pre-formatted as SMT-LIB text so the driver loop just writes them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandResponse {
    None,
    Sat,
    Unsat,
    Unknown,
    Model(String),
    Values(String),
    Error(String),
}

use shinri_core::{Context, Op, SortId, SymbolId, TermId};
use shinri_frontend::Command;
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

    /// Mutable access to the shared term DAG, so the parser can intern terms
    /// into the same `Context` the solver uses.
    pub fn ctx_mut(&mut self) -> &mut Context {
        &mut self.ctx
    }

    /// Execute one IR command and return the response.
    pub fn execute(&mut self, cmd: Command) -> CommandResponse {
        match cmd {
            Command::Assert(t) => {
                self.assert(t);
                CommandResponse::None
            }
            Command::CheckSat => match self.check_sat() {
                SolveOutcome::Sat => CommandResponse::Sat,
                SolveOutcome::Unsat => CommandResponse::Unsat,
                SolveOutcome::Unknown => CommandResponse::Unknown,
            },
            Command::CheckSatAssuming(_) => CommandResponse::Unknown,
            Command::Push(n) => {
                for _ in 0..n {
                    self.push();
                }
                CommandResponse::None
            }
            Command::Pop(n) => {
                self.pop(n as usize);
                CommandResponse::None
            }
            Command::GetModel => CommandResponse::Model(self.format_model()),
            Command::GetValue(ts) => {
                let mut out = String::from("(");
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    let name = crate::tseitin::display_term(&self.ctx, *t);
                    let v = self.format_value(*t).unwrap_or_else(|| "?".to_string());
                    out.push_str(&format!("({name} {v})"));
                }
                out.push(')');
                CommandResponse::Values(out)
            }
            Command::GetUnsatCore => CommandResponse::Error("unsupported".into()),
            Command::Reset => {
                self.assertions.clear();
                self.scopes.clear();
                self.last_model = None;
                CommandResponse::None
            }
            Command::SetLogic(_)
            | Command::DeclareSort { .. }
            | Command::DeclareFun { .. }
            | Command::SetOption { .. }
            | Command::SetInfo { .. }
            | Command::Exit => CommandResponse::None,
            Command::GetInfo(_) => CommandResponse::None,
            Command::Echo(s) => CommandResponse::Values(s),
            _ => CommandResponse::None,
        }
    }

    fn format_value(&self, t: TermId) -> Option<String> {
        self.last_model
            .as_ref()?
            .get(t)
            .map(crate::model::format_modelval)
    }

    fn format_model(&self) -> String {
        match &self.last_model {
            None => "()".into(),
            Some(m) => {
                let mut out = String::from("(");
                for (t, v) in m.values.iter() {
                    let name = crate::tseitin::display_term(&self.ctx, *t);
                    let val = crate::model::format_modelval(v);
                    out.push_str(&format!("({name} {val})"));
                }
                out.push(')');
                out
            }
        }
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
            // saw_shared: an atom mixes arith and non-arith sorts in one equality
            // (requires purification not yet implemented) → Unknown.
            //
            // saw_euf_nonreal && saw_arith: there are EUF atoms on a purely
            // uninterpreted sort (e.g. sort U) AND arith atoms on Real/Int.
            // Without N-O equality propagation from arith to EUF, combining these
            // two theories unsoundly. Fence to Unknown.
            //
            // NOTE: EUF atoms on Real/Int sorts (e.g. (= x:Real y:Real)) are NOT
            // fenced — they're paired with companion Le/Ge arith atoms emitted by
            // lower(), giving both theories the constraint. This is QF_UFLRA: EUF
            // handles congruence (f(x)=f(y) when x=y), Arith handles linear bounds.
            mixed = enc.saw_shared || (enc.saw_euf_nonreal && enc.saw_arith);
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
    /// Returns true if `t` is a "pure arith" term — a linear combination of
    /// nullary uninterpreted constants and numerals. Non-nullary uninterpreted
    /// applications (function calls like `f(x)`) are EUF-structure, not pure arith.
    fn is_pure_arith(ctx: &shinri_core::Context, t: TermId) -> bool {
        use shinri_core::{BuiltinOp, Op, TermNode};
        match ctx.term_node(t) {
            TermNode::Const { .. } => true, // numeral constant
            TermNode::App { op, args, .. } => {
                let children = ctx.children(*args);
                match op {
                    // Nullary uninterpreted symbol = a plain variable.
                    Op::Uninterpreted(_) if children.is_empty() => true,
                    // Non-nullary uninterpreted = function application (EUF).
                    Op::Uninterpreted(_) => false,
                    // Linear arithmetic ops: all children must be pure arith too.
                    Op::Builtin(
                        BuiltinOp::Add | BuiltinOp::Sub | BuiltinOp::Mul | BuiltinOp::Neg,
                    ) => children.iter().all(|&c| Self::is_pure_arith(ctx, c)),
                    _ => false,
                }
            }
        }
    }

    fn lower(&mut self, t: TermId) -> TermId {
        use shinri_core::{BuiltinOp, Op, TermNode};
        match self.ctx.term_node(t).clone() {
            // ── Real equality: (= a b) → (and (= a b) (Le a b) (Ge a b)) ─────
            //
            // We keep the original Eq atom so EUF can see x=y for congruence
            // (needed for QF_UFLRA: x=y must reach EUF so congruence can derive
            // f(x)=f(y)). The Le/Ge atoms are also added so arith can reason
            // about the bound constraint. Both are semantically equivalent to (= a b).
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
                    // Chain adjacent pairs:
                    //   (= a b)∧(Le a b)∧(Ge a b) ∧ (= b c)∧(Le b c)∧(Ge b c) ∧ ...
                    // The Eq atoms go to EUF for congruence; the Le/Ge go to Arith.
                    let mut conj: Vec<TermId> = Vec::with_capacity((kids.len() - 1) * 3);
                    for w in kids.windows(2) {
                        // Keep the original binary Eq for EUF.
                        let eq = self
                            .ctx
                            .mk_app(Op::Builtin(BuiltinOp::Eq), &[w[0], w[1]])
                            .expect("Eq well-sorted");
                        let le = self
                            .ctx
                            .mk_app(Op::Builtin(BuiltinOp::Le), &[w[0], w[1]])
                            .expect("Le well-sorted");
                        let ge = self
                            .ctx
                            .mk_app(Op::Builtin(BuiltinOp::Ge), &[w[0], w[1]])
                            .expect("Ge well-sorted");
                        conj.push(eq);
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
                    // Binary distinct over Real sort.
                    if self.ctx.sort_of(kids[0]) == self.ctx.real_sort() {
                        // If both args are pure arithmetic terms (nullary vars /
                        // numerals / linear combinations), lower to (or Lt Gt) so
                        // the Arith theory can reason about the disequality.
                        // If either arg contains a function application (EUF), keep
                        // it as a Distinct atom for EUF — congruence closure handles
                        // it (e.g. distinct(f x)(f y) when x=y → conflict via EUF).
                        if Self::is_pure_arith(&self.ctx, kids[0])
                            && Self::is_pure_arith(&self.ctx, kids[1])
                        {
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
                            // EUF function args: keep as Distinct atom for EUF.
                            t
                        }
                    } else {
                        // Non-Real (EUF) binary distinct: pass through unchanged.
                        t
                    }
                } else {
                    // N-ary distinct: split into pairwise binary distincts, each
                    // recursively lowered (so pure-Real pairs → Lt/Gt, EUF pairs stay).
                    let mut pairs = Vec::new();
                    for i in 0..kids.len() {
                        for j in (i + 1)..kids.len() {
                            let d = self
                                .ctx
                                .mk_app(Op::Builtin(BuiltinOp::Distinct), &[kids[i], kids[j]])
                                .expect("binary distinct well-sorted");
                            // Recurse so pure-Real pairs become (or Lt Gt).
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
mod execute_tests {
    use super::*;
    use shinri_frontend::Command;

    #[test]
    fn execute_runs_check_sat_unsat() {
        // x < 0 and x > 0 over Real -> unsat. Build via ctx_mut to mirror the parser.
        let mut s = Solver::new();
        let r = s.real_sort();
        let x = s.declare_const("x", r);
        let zero = s.numeral(shinri_num::Rational::zero(), r);
        let lt = s.app(Op::Builtin(shinri_core::BuiltinOp::Lt), &[x, zero]);
        let gt = s.app(Op::Builtin(shinri_core::BuiltinOp::Gt), &[x, zero]);
        assert!(matches!(
            s.execute(Command::Assert(lt)),
            CommandResponse::None
        ));
        assert!(matches!(
            s.execute(Command::Assert(gt)),
            CommandResponse::None
        ));
        assert!(matches!(
            s.execute(Command::CheckSat),
            CommandResponse::Unsat
        ));
    }

    #[test]
    fn get_unsat_core_is_unsupported() {
        let mut s = Solver::new();
        assert!(matches!(
            s.execute(Command::GetUnsatCore),
            CommandResponse::Error(_)
        ));
    }

    #[test]
    fn push_pop_are_noops_response() {
        let mut s = Solver::new();
        assert!(matches!(s.execute(Command::Push(2)), CommandResponse::None));
        assert!(matches!(s.execute(Command::Pop(1)), CommandResponse::None));
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
