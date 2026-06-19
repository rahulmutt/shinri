use crate::ids::SymbolId;

/// An interned sort. A small algebra; parameterized sorts ((_ BitVec n),
/// (Array I E)) are reserved for Phase 3 and added as variants then (spec §4.3).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SortNode {
    Bool,
    Int,
    Real,
    Uninterpreted(SymbolId),
}
