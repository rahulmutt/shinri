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
}
