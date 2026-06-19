#![no_main]
use libfuzzer_sys::fuzz_target;
use shinri_core::{Lit, NoProof, Var};
use shinri_sat::{NoTheory, SolveResult, Solver, SolverConfig, Vmtf};

// Interpret raw bytes as a small CNF; cross-check shinri vs splr. Any
// SAT/UNSAT disagreement is a soundness bug (the fuzzer minimizes the input).
fuzz_target!(|data: &[u8]| {
    if data.len() < 4 {
        return;
    }
    let n = (data[0] % 8 + 1) as usize;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let mut dimacs: Vec<Vec<i32>> = Vec::new();
    let mut i = 1;
    while i + 2 < data.len() {
        let mut cl = Vec::new();
        let mut dl = Vec::new();
        for k in 0..3 {
            let b = data[i + k];
            let v = (b as usize % n) as u32;
            let pos = b & 0x80 == 0;
            cl.push(Lit::new(Var::new(v), pos));
            dl.push(if pos { (v + 1) as i32 } else { -((v + 1) as i32) });
        }
        clauses.push(cl);
        dimacs.push(dl);
        i += 3;
    }
    if clauses.is_empty() {
        return;
    }
    let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
    for _ in 0..n {
        s.new_var();
    }
    for c in &clauses {
        s.add_clause(c);
    }
    let ours = s.solve() == SolveResult::Sat;

    use splr::{Certificate, Config, SolveIF, Solver as SplrSolver};
    if let Ok(mut sp) = SplrSolver::try_from((Config::default(), dimacs.as_slice())) {
        match sp.solve() {
            Ok(Certificate::SAT(_)) => assert!(ours, "shinri UNSAT but splr SAT"),
            Ok(Certificate::UNSAT) => assert!(!ours, "shinri SAT but splr UNSAT"),
            Err(_) => {}
        }
    }
});
