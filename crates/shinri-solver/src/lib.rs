//! shinri-solver: the embeddable QF_UF solver entry point. Owns the term DAG,
//! Tseitin-encodes Boolean structure into the CDCL(T) SAT engine, registers EUF
//! atoms, and extracts models. No SMT-LIB parser (assert via the API).

mod model;
mod tseitin;

pub use model::{Model, SolveOutcome};

use shinri_core::{Context, Op, SortId, SymbolId, TermId};

pub struct Solver {
    ctx: Context,
    assertions: Vec<TermId>,
}

impl Default for Solver {
    fn default() -> Self {
        Solver::new()
    }
}

impl Solver {
    pub fn new() -> Solver {
        Solver {
            ctx: Context::new(),
            assertions: Vec::new(),
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
    pub fn app(&mut self, op: Op, args: &[TermId]) -> TermId {
        self.ctx.mk_app(op, args).expect("well-sorted application")
    }
    pub fn eq(&mut self, a: TermId, b: TermId) -> TermId {
        self.ctx.mk_eq(a, b).expect("well-sorted equality")
    }
    pub fn assert(&mut self, formula: TermId) {
        self.assertions.push(formula);
    }

    pub fn check_sat(&mut self) -> SolveOutcome {
        // Implemented in Task 14.
        SolveOutcome::Unknown
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
        assert_eq!(s.check_sat(), SolveOutcome::Unknown); // until Task 14
    }
}
