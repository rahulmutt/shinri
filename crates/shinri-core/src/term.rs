use crate::ids::{RatId, SortId, SymbolId};

/// A (offset, len) view into `Context.children` — out-of-line child storage (SoA).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ChildSlice {
    pub off: u32,
    pub len: u32,
}

/// The operator of an application. Interpreted operators are a compact central
/// enum (fast type-safe dispatch); user functions are `Uninterpreted` (spec §4.2).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Op {
    Builtin(BuiltinOp),
    Uninterpreted(SymbolId),
}

/// Standardized SMT-LIB core + arithmetic operators. Bit-vector / array ops are
/// reserved for Phase 3 and added as variants then (spec §4.3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BuiltinOp {
    // Boolean / core
    Not,
    And,
    Or,
    Implies,
    Xor,
    Eq,
    Distinct,
    Ite,
    // Arithmetic (Int / Real)
    Neg,
    Add,
    Sub,
    Mul,
    Le,
    Lt,
    Ge,
    Gt,
    // Arrays
    Select,
    Store,
}

/// A literal constant value. Numerals reference `Context.nums` by `RatId`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ConstVal {
    Bool(bool),
    Num(RatId),
}

/// A node in the hash-consed term DAG. Fixed-size; children stored out-of-line.
/// Var/Quant variants are reserved for Phase 4 and added then (spec §4.3).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TermNode {
    App {
        op: Op,
        args: ChildSlice,
        sort: SortId,
    },
    Const {
        val: ConstVal,
        sort: SortId,
    },
}
