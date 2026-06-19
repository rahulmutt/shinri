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
}
