//! shinri-num: SMT-tuned exact big-integer and rational arithmetic.
//!
//! Zero runtime dependencies. Validated against num-bigint as a dev-only oracle.

mod delta;
mod integer;
mod limbs;
mod rational;

pub use delta::DeltaRational;
pub use integer::{Integer, ParseIntegerError};
pub use rational::Rational;
