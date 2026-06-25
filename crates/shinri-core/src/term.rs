use crate::ids::{BvId, FpId, RatId, SortId, StringId, SymbolId};

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
    // Bitvectors — fixed-arity
    BvNot,
    BvAnd,
    BvOr,
    BvXor,
    BvNand,
    BvNor,
    BvXnor,
    BvNeg,
    BvAdd,
    BvSub,
    BvMul,
    BvUdiv,
    BvUrem,
    BvSdiv,
    BvSrem,
    BvSmod,
    BvShl,
    BvLshr,
    BvAshr,
    BvUlt,
    BvUle,
    BvUgt,
    BvUge,
    BvSlt,
    BvSle,
    BvSgt,
    BvSge,
    BvConcat,
    // Bitvectors — indexed (parameters carried in the op)
    BvExtract { hi: u32, lo: u32 },
    BvZeroExtend(u32),
    BvSignExtend(u32),
    BvRotateLeft(u32),
    BvRotateRight(u32),
    BvRepeat(u32),
    // Strings (QF_S core)
    StrConcat,
    StrLen,
    StrAt,
    StrSubstr,
}

/// The five SMT-LIB rounding modes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum RoundingMode {
    /// roundNearestTiesToEven (RNE)
    Rne,
    /// roundNearestTiesToAway (RNA)
    Rna,
    /// roundTowardPositive (RTP)
    Rtp,
    /// roundTowardNegative (RTN)
    Rtn,
    /// roundTowardZero (RTZ)
    Rtz,
}

/// A literal constant value. Numerals reference `Context.nums` by `RatId`.
/// Bitvector literals reference `Context.bvs` by `BvId`.
/// String literals reference `Context.str_lits` by `StringId`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ConstVal {
    Bool(bool),
    Num(RatId),
    /// A bitvector literal; references `Context.bvs`.
    BitVec(BvId),
    /// A string literal; references `Context.str_lits`.
    String(StringId),
    /// An FP literal; references `Context.fps`.
    Float(FpId),
    /// A rounding-mode constant.
    Rm(RoundingMode),
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
