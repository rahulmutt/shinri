//! Per-atom encoding: how asserting a SAT var (true/false) becomes a bound on
//! an ArithVar. Built in `new_var`, applied in `assert`.
//!
//! Note: `Eq` atoms are eliminated by the solver's CNF encoder (rewritten to
//! `(a<=b) AND (a>=b)`) before reaching shinri-arith. Only `Ineq` and `Const`
//! encodings are produced here.

use crate::bounds::BoundKind;
use crate::vars::ArithVar;
use shinri_num::DeltaRational;

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
pub enum AtomEncoding {
    /// Inequality: one bound for the positive polarity, one for the negative.
    Ineq {
        var: ArithVar,
        pos: (BoundKind, DeltaRational),
        neg: (BoundKind, DeltaRational),
    },
    /// A constant relation (empty comb), already decided true/false.
    Const(bool),
}
