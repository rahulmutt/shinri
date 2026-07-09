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
    BvExtract {
        hi: u32,
        lo: u32,
    },
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
    // String predicates (slice 12): String × String → Bool.
    // Arg order per SMT-LIB: prefixof/suffixof take the NEEDLE first;
    // contains takes the HAYSTACK first.
    StrPrefixOf,
    StrSuffixOf,
    StrContains,
    // Floating-point — arithmetic. Rounded ops take a RoundingMode as arg 0.
    FpAbs,
    FpNeg, // (F) -> F
    FpAdd,
    FpSub,
    FpMul,
    FpDiv, // (RM, F, F) -> F
    FpFma, // (RM, F, F, F) -> F
    FpSqrt,
    FpRoundToIntegral, // (RM, F) -> F
    FpRem,
    FpMin,
    FpMax, // (F, F) -> F
    // Floating-point — comparisons: (F, F) -> Bool
    FpLeq,
    FpLt,
    FpGeq,
    FpGt,
    FpEq,
    // Floating-point — classification: (F) -> Bool
    FpIsNormal,
    FpIsSubnormal,
    FpIsZero,
    FpIsInfinite,
    FpIsNaN,
    FpIsNegative,
    FpIsPositive,
    // Floating-point — bit constructor: (BV1, BVeb, BV(sb-1)) -> Float(eb, sb)
    FpFromBits,
    // Floating-point — conversions (indexed; parameters carried in the op).
    /// (_ to_fp eb sb): bitcast from BV(eb+sb) [1 arg], or RM-rounded from
    /// Float / signed-int BV / Real [2 args: (RM, X)].
    ToFp {
        eb: u32,
        sb: u32,
    },
    /// (_ to_fp_unsigned eb sb): (RM, BV) unsigned-int -> Float(eb, sb).
    ToFpUnsigned {
        eb: u32,
        sb: u32,
    },
    /// (_ fp.to_ubv m): (RM, Float) -> BV(m).
    FpToUbv(u32),
    /// (_ fp.to_sbv m): (RM, Float) -> BV(m).
    FpToSbv(u32),
    /// fp.to_real: (Float) -> Real.
    FpToReal,
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
