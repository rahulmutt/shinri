use proptest::prelude::*;
use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

fn build(num_vars: usize, clauses: &[Vec<(u32, bool)>]) -> Solver<NoTheory, NoProof, Vmtf> {
    let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
    for _ in 0..num_vars {
        s.new_var();
    }
    for c in clauses {
        let lits: Vec<Lit> = c.iter().map(|&(n, p)| Lit::new(Var::new(n), p)).collect();
        s.add_clause(&lits);
    }
    s
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]
    #[test]
    fn sat_results_satisfy_every_clause(
        clauses in prop::collection::vec(
            prop::collection::vec((0u32..6, any::<bool>()), 1..4),
            0..20,
        )
    ) {
        let mut s = build(6, &clauses);
        if s.solve() == SolveResult::Sat {
            prop_assert!(s.check_model(), "SAT model violates a clause");
        }
    }
}
