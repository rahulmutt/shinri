//! shinri-arith: a Dutertre–de Moura simplex theory solver for QF_LRA.
//! Implements `shinri_theory::TheorySolver`; depends only on core + theory.

pub mod bounds;
pub mod diseq;
pub mod encode;
pub mod farkas;
pub mod model;
pub mod normalize;
pub mod simplex;
pub mod tableau;
pub mod vars;

pub use vars::ArithVar;
