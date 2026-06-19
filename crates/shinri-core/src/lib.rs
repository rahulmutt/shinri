//! shinri-core: shared vocabulary for the shinri SMT solver.
//!
//! Term/sort DAG, identity types, backtracking toolkit, rational abstraction,
//! and the proof seam. No theory, SAT, or parsing logic lives here.

pub mod ids;
pub mod symbol;
pub mod sort;
pub mod context;
pub mod term;
pub mod error;
pub mod undo;

pub use ids::{ClauseId, Lit, RatId, SortId, SymbolId, TermId, Var};
pub use context::Context;
pub use sort::SortNode;
pub use term::{BuiltinOp, ChildSlice, ConstVal, Op, TermNode};
pub use error::SortError;
pub use undo::UndoLog;
pub use shinri_num::{DeltaRational, Rational};
