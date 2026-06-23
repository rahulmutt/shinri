//! shinri-bv: eager bit-blasting of QF_BV to CNF over a private BitVar namespace.
//! See docs/superpowers/specs/2026-06-23-shinri-qfbv-design.md.
pub mod blast;
pub use blast::{BitLit, Blaster, Cnf};
