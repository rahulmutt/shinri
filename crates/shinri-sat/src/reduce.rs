//! Clause-database reduction (spec §6.3). The LBD computation and the
//! reduction policy currently live in `solver.rs` (they need the trail and
//! watch state); this module is reserved for extraction if that logic grows.
