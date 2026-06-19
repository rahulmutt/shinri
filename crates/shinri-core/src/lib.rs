//! shinri-core: shared vocabulary for the shinri SMT solver.
//!
//! Term/sort DAG, identity types, backtracking toolkit, rational abstraction,
//! and the proof seam. No theory, SAT, or parsing logic lives here.

pub mod ids;

pub use ids::{ClauseId, Lit, RatId, SortId, SymbolId, TermId, Var};
