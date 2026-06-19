/// Which restart schedule the solver runs (spec §6.2). Selected at runtime
/// (the restart policy is consulted only once per conflict — too cold to
/// warrant a generic, unlike the branching heuristic).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RestartKind {
    /// Luby sequence — deterministic, theory-friendly.
    Luby,
    /// Glucose-style EMA on learnt-clause LBD.
    EmaGlucose,
}

/// Runtime tuning knobs. The branching heuristic is NOT here — it is the
/// generic type parameter `H` of `Solver`, fixed at construction (spec §8.4).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SolverConfig {
    pub restart: RestartKind,
    pub reduce_interval: u32,
    pub lbd_keep_threshold: u32,
    pub random_seed: u64,
}

impl Default for SolverConfig {
    fn default() -> Self {
        SolverConfig {
            restart: RestartKind::Luby,
            reduce_interval: 2000,
            lbd_keep_threshold: 2,
            random_seed: 0,
        }
    }
}
