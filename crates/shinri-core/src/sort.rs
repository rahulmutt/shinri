use crate::ids::SymbolId;

/// An interned sort. A small algebra; parameterized sorts ((_ BitVec n)) are
/// reserved for Phase 3. The Array sort is now supported (spec §4.3).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SortNode {
    Bool,
    Int,
    Real,
    Uninterpreted(SymbolId),
    /// (Array <index> <element>)
    Array(crate::ids::SortId, crate::ids::SortId),
}
