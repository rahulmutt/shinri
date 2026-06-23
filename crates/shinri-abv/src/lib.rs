//! shinri-abv: QF_ABV (bitvector arrays) via lemmas-on-demand abstraction–refinement.
//! See docs/superpowers/specs/2026-06-23-shinri-qfabv-design.md.
pub mod abstraction;
pub mod check;
pub mod collect;
pub mod driver;
pub mod model;

pub use abstraction::{abstract_arrays, Abstraction};
pub use collect::{collect, Collected};
pub use driver::{refine, AbvOutcome, Lemma, LemmaLit, SatBridge};
pub use model::{array_model, render, ArrayModel};
