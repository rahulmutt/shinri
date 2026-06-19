//! shinri-euf: the EUF (congruence-closure) theory solver. Adds the congruence
//! driver (signature table + use-lists) on top of shinri-theory's shared
//! `EqualityEngine` (union-find + proof forest). Depends only on core, theory,
//! and sat (for `Effort`).

mod egraph;
pub mod solver;

pub use solver::Euf;
