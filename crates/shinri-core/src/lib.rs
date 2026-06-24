//! shinri-core: shared vocabulary for the shinri SMT solver.
//!
//! Term/sort DAG, identity types, backtracking toolkit, rational abstraction,
//! and the proof seam. No theory, SAT, or parsing logic lives here.

pub mod context;
pub mod error;
pub mod ids;
pub mod proof;
pub mod sort;
pub mod symbol;
pub mod term;
pub mod undo;

pub use context::Context;
pub use error::SortError;
pub use ids::{BvId, ClauseId, Lit, RatId, SortId, StringId, SymbolId, TermId, Var};
pub use proof::{NoProof, ProofSink, TheoryJust};
pub use shinri_num::{DeltaRational, Integer, Rational};
pub use sort::SortNode;
pub use term::{BuiltinOp, ChildSlice, ConstVal, Op, TermNode};
pub use undo::UndoLog;
