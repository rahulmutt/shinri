//! shinri-num: SMT-tuned exact big-integer and rational arithmetic.
//!
//! Zero runtime dependencies. Validated against num-bigint as a dev-only oracle.

mod integer;
mod limbs;

pub use integer::Integer;
