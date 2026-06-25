use crate::ids::SymbolId;

/// An interned sort. A small algebra; parameterized sorts are supported for
/// (_ BitVec n) (Phase 3) and (Array ...) (spec §4.3).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SortNode {
    Bool,
    Int,
    Real,
    String,
    Uninterpreted(SymbolId),
    /// (Array <index> <element>)
    Array(crate::ids::SortId, crate::ids::SortId),
    /// (_ BitVec n) — n >= 1.
    BitVec(u32),
    /// (_ FloatingPoint eb sb): eb = exponent bits, sb = significand bits
    /// (including the hidden bit). Total width eb + sb. Requires eb >= 2, sb >= 2.
    Float(u32, u32),
    /// The RoundingMode sort (5 enumerated values; see term::RoundingMode).
    RoundingMode,
}
