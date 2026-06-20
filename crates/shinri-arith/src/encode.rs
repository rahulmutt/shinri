//! Per-atom encoding: how asserting a SAT var (true/false) becomes a bound or
//! disequality on an ArithVar. Built in `new_var`, applied in `assert`.

use crate::bounds::BoundKind;
use crate::vars::ArithVar;
use shinri_num::DeltaRational;

#[derive(Clone, Debug)]
pub enum AtomEncoding {
    /// Inequality: one bound for the positive polarity, one for the negative.
    Ineq {
        var: ArithVar,
        pos: (BoundKind, DeltaRational),
        neg: (BoundKind, DeltaRational),
    },
    /// Equality `var ⋈ rhs`: positive installs both bounds at `rhs`; negative is
    /// a disequality `var ≠ rhs`.
    Eq { var: ArithVar, rhs: DeltaRational },
    /// A constant relation (empty comb), already decided true/false.
    Const(bool),
}
