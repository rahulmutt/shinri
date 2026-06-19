//! shinri-theory: the Nelson–Oppen theory-combination framework.
//!
//! A central `EqualityEngine` is the single source of equality truth; theories
//! implement `TheorySolver` and exchange interface equalities only through it.
//! A fixed-arity, enum-routed `Combiner` presents one `shinri_sat::Theory`.
//! Depends only on `shinri-core` and `shinri-sat`.

pub mod atom;
pub mod combiner;
pub mod eq_engine;
pub mod interface;
pub mod model;
pub mod proof;
pub mod solver_trait;
pub mod types;

pub use atom::{classify, AtomRegistry, Unsupported};
pub use combiner::Combiner;
pub use eq_engine::EqualityEngine;
pub use interface::InterfaceSet;
pub use model::ModelBuilder;
pub use proof::{CertError, CertLog, CertStep};
pub use solver_trait::{TCheck, TheoryCtx, TheorySolver};
pub use types::{ENodeId, EqConflict, EqJust, EqLeaf, Explainer, MergeEvent, ModelVal, Owner};
