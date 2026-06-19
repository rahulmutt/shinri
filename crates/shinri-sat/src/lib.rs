//! shinri-sat: the CDCL(T)-ready SAT search engine of the shinri SMT solver.
//!
//! Clause database, two-watched-literals propagation, 1-UIP learning,
//! branching, restarts, incremental assumptions, and the zero-cost
//! `Theory`/`ProofSink` seams. Depends only on `shinri-core`.

pub mod analyze;
pub mod clause;
pub mod assignment;
pub mod config;
pub mod heuristic;
pub mod theory;
pub mod types;
pub mod trail;
pub mod watch;
pub mod solver;
pub mod reduce;
pub mod restart;

#[cfg(any(test, feature = "dimacs"))]
pub mod dimacs;

pub use clause::{ClauseDb, ClauseRef};
pub use config::{RestartKind, SolverConfig};
pub use types::{Conflict, Effort, LBool, Reason, SolveResult, TheoryResult};
pub use solver::Solver;
pub use heuristic::{BranchHeuristic, Evsids, Vmtf};
pub use theory::{NoTheory, Theory};

// Re-export the core vocabulary so downstream crates and integration tests can
// name these types via `shinri_sat::` without depending on `shinri-core`
// directly (integration tests cannot see a crate's regular dependencies).
pub use shinri_core::{ClauseId, Lit, NoProof, ProofSink, TheoryJust, Var};
