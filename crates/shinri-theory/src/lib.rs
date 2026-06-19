//! shinri-theory: the Nelson–Oppen theory-combination framework.
//!
//! A central `EqualityEngine` is the single source of equality truth; theories
//! implement `TheorySolver` and exchange interface equalities only through it.
//! A fixed-arity, enum-routed `Combiner` presents one `shinri_sat::Theory`.
//! Depends only on `shinri-core` and `shinri-sat`.

pub mod types;
pub mod eq_engine;
pub mod atom;

pub use types::{ENodeId, EqConflict, EqJust, EqLeaf, Explainer, MergeEvent, ModelVal, Owner};
pub use eq_engine::EqualityEngine;
pub use atom::{classify, AtomRegistry, Unsupported};
