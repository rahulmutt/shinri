use crate::ids::SortId;

/// A recoverable well-sortedness error from the term builder. Reported by the
/// parser (spec §9); never panicked.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SortError {
    /// An operator was applied to the wrong number of arguments.
    Arity { expected: usize, found: usize },
    /// An argument had an unexpected sort.
    Mismatch { expected: SortId, found: SortId },
    /// An argument sort was not one this operator accepts (e.g. non-arithmetic
    /// operand to `+`), where no single `expected` sort applies.
    NotApplicable,
    /// An uninterpreted symbol was applied but was never declared.
    UndeclaredSymbol,
    /// An argument was expected to be a BitVec sort but was not.
    NotBitVec,
    /// A bitvector indexed parameter (e.g. extract hi/lo or repeat k) is out of range.
    BvIndex,
    /// An argument was expected to be a FloatingPoint sort but was not.
    NotFloat,
    /// An argument was expected to be the RoundingMode sort but was not.
    NotRoundingMode,
    /// A floating-point indexed parameter (eb/sb/m) is out of range, or `fp`
    /// constructor operand widths are inconsistent.
    FpIndex,
}
