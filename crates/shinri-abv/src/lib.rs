//! shinri-abv: QF_ABV (bitvector arrays) via lemmas-on-demand abstraction–refinement.
//! See docs/superpowers/specs/2026-06-23-shinri-qfabv-design.md.
pub mod collect;

pub use collect::{collect, Collected};
