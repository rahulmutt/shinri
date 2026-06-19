use shinri_sat::{
    BranchHeuristic, Evsids, Lit, NoProof, NoTheory, RestartKind, SolveResult, Solver,
    SolverConfig, Var, Vmtf,
};

/// Tiny deterministic LCG so cases are reproducible without a rand dependency.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 16
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A random 3-CNF over `n` vars with `m` clauses.
fn random_3cnf(seed: u64, n: u64, m: u64) -> Vec<Vec<(u32, bool)>> {
    let mut rng = Lcg(seed.wrapping_add(0x9E3779B97F4A7C15));
    (0..m)
        .map(|_| {
            (0..3)
                .map(|_| ((rng.below(n)) as u32, rng.below(2) == 1))
                .collect()
        })
        .collect()
}

fn run_shinri<H: BranchHeuristic>(
    n: usize,
    clauses: &[Vec<(u32, bool)>],
    cfg: SolverConfig,
) -> (bool, Solver<NoTheory, NoProof, H>) {
    let mut s: Solver<NoTheory, NoProof, H> = Solver::new(cfg);
    for _ in 0..n {
        s.new_var();
    }
    for c in clauses {
        let lits: Vec<Lit> = c.iter().map(|&(v, p)| Lit::new(Var::new(v), p)).collect();
        s.add_clause(&lits);
    }
    (s.solve() == SolveResult::Sat, s)
}

fn to_dimacs(clauses: &[Vec<(u32, bool)>]) -> Vec<Vec<i32>> {
    clauses
        .iter()
        .map(|c| {
            c.iter()
                .map(|&(v, p)| {
                    let lit = (v + 1) as i32;
                    if p { lit } else { -lit }
                })
                .collect()
        })
        .collect()
}

// NOTE: splr 0.17's TryFrom<(Config, &[V])> has Error = SolverResult
// (i.e. Result<Certificate, SolverError>), not bare SolverError.
// When building fails with a pre-detected UNSAT (e.g. root-level conflict),
// it returns Err(Ok(Certificate::UNSAT)); an empty-clause / invalid-literal
// error returns Err(Err(SolverError::...)).
fn splr_is_sat(clauses: &[Vec<i32>]) -> Option<bool> {
    use splr::{Certificate, Config, SolveIF, Solver as SplrSolver};
    match SplrSolver::try_from((Config::default(), clauses)) {
        Ok(mut s) => match s.solve() {
            Ok(Certificate::SAT(_)) => Some(true),
            Ok(Certificate::UNSAT) => Some(false),
            Err(_) => None,
        },
        // Pre-detected UNSAT during construction (root-level conflict etc.)
        Err(Ok(Certificate::UNSAT)) => Some(false),
        Err(Ok(Certificate::SAT(_))) => Some(true),
        Err(Err(_)) => None,
    }
}

#[test]
fn differential_random_3cnf_across_configs() {
    let configs = [
        (RestartKind::Luby, false),
        (RestartKind::EmaGlucose, false),
        (RestartKind::Luby, true), // true => use Evsids
        (RestartKind::EmaGlucose, true),
    ];
    for seed in 0..200u64 {
        let n = 8;
        let m = 34; // ~4.26 ratio -> phase transition, mixes SAT/UNSAT
        let clauses = random_3cnf(seed, n as u64, m);
        let dimacs = to_dimacs(&clauses);
        let oracle = match splr_is_sat(&dimacs) {
            Some(b) => b,
            None => continue, // skip instances the oracle can't classify
        };
        for &(restart, use_evsids) in &configs {
            let cfg = SolverConfig { restart, ..SolverConfig::default() };
            // run_shinri returns Solver<_, _, H> which differs between Evsids and
            // Vmtf (they are distinct monomorphisations), so we cannot unify them
            // in a single `if/else` binding. Handle each branch separately.
            if use_evsids {
                let (sat, solver) = run_shinri::<Evsids>(n, &clauses, cfg);
                assert_eq!(
                    sat, oracle,
                    "DISAGREEMENT seed={seed} restart={restart:?} evsids={use_evsids}"
                );
                if sat {
                    assert!(solver.check_model(), "SAT but model invalid (seed {seed})");
                }
            } else {
                let (sat, solver) = run_shinri::<Vmtf>(n, &clauses, cfg);
                assert_eq!(
                    sat, oracle,
                    "DISAGREEMENT seed={seed} restart={restart:?} evsids={use_evsids}"
                );
                if sat {
                    assert!(solver.check_model(), "SAT but model invalid (seed {seed})");
                }
            }
        }
    }
}
