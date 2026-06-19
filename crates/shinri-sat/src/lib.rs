//! shinri-sat: the CDCL(T)-ready SAT search engine of the shinri SMT solver.
//!
//! Clause database, two-watched-literals propagation, 1-UIP learning,
//! branching, restarts, incremental assumptions, and the zero-cost
//! `Theory`/`ProofSink` seams. Depends only on `shinri-core`.

pub mod clause;
pub mod assignment;
pub mod config;
pub mod types;

pub use config::{RestartKind, SolverConfig};
pub use types::{Effort, LBool, Reason, SolveResult, TheoryResult};

// Re-export the core vocabulary so downstream crates and integration tests can
// name these types via `shinri_sat::` without depending on `shinri-core`
// directly (integration tests cannot see a crate's regular dependencies).
pub use shinri_core::{ClauseId, Lit, NoProof, ProofSink, TheoryJust, Var};
