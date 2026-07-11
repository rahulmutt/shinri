use crate::error::SortError;
use crate::ids::{BvId, FpId, RatId, SortId, StringId, SymbolId, TermId};
use crate::sort::SortNode;
use crate::symbol::StringInterner;
use crate::term::{BuiltinOp, ChildSlice, ConstVal, Op, TermNode};
use rustc_hash::{FxHashMap, FxHashSet};
use shinri_num::{Integer, Rational};

/// The single owning arena for all interned sorts (and, after Task 4, terms).
#[derive(Clone)]
pub struct Context {
    sorts: Vec<SortNode>,
    sort_interner: FxHashMap<SortNode, SortId>,
    symbols: StringInterner,
    nodes: Vec<TermNode>,
    children: Vec<TermId>,
    nums: Vec<Rational>,
    term_interner: FxHashMap<TermKey, TermId>,
    fun_sigs: FxHashMap<SymbolId, (Vec<SortId>, SortId)>,
    /// Symbols minted by solver-internal passes (e.g. word_norm's `ite!<n>`
    /// nullary vars). User `declare-fun`/`declare-const` must be rejected when
    /// it names one of these, otherwise the user's app hash-conses to the same
    /// TermId as the internal symbol and silently inherits its definition
    /// (slice 5 final review: wrong-UNSAT via post-mint re-declaration).
    reserved_syms: FxHashSet<SymbolId>,
    /// BV literal table: index `BvId(i)` -> `(width, value in [0, 2^width))`.
    bvs: Vec<(u32, Integer)>,
    /// FP literal table: (eb, sb, bits) where bits is the W = eb+sb bit pattern,
    /// laid out MSB->LSB as [sign | exponent | trailing-significand].
    fps: Vec<(u32, u32, Integer)>,
    /// String literal table: index `StringId(i)` -> interned string value.
    str_lits: Vec<Box<str>>,
    bool_sort: SortId,
    int_sort: SortId,
    real_sort: SortId,
    string_sort: SortId,
}

impl Default for Context {
    fn default() -> Self {
        Context::new()
    }
}

impl Context {
    pub fn new() -> Context {
        let mut ctx = Context {
            sorts: Vec::new(),
            sort_interner: FxHashMap::default(),
            symbols: StringInterner::default(),
            nodes: Vec::new(),
            children: Vec::new(),
            nums: Vec::new(),
            term_interner: FxHashMap::default(),
            fun_sigs: FxHashMap::default(),
            reserved_syms: FxHashSet::default(),
            bvs: Vec::new(),
            fps: Vec::new(),
            str_lits: Vec::new(),
            // placeholders; overwritten immediately below
            bool_sort: SortId::from_index(0),
            int_sort: SortId::from_index(0),
            real_sort: SortId::from_index(0),
            string_sort: SortId::from_index(0),
        };
        ctx.bool_sort = ctx.intern_sort(SortNode::Bool);
        ctx.int_sort = ctx.intern_sort(SortNode::Int);
        ctx.real_sort = ctx.intern_sort(SortNode::Real);
        ctx.string_sort = ctx.intern_sort(SortNode::String);
        ctx
    }

    fn intern_sort(&mut self, node: SortNode) -> SortId {
        if let Some(&id) = self.sort_interner.get(&node) {
            return id;
        }
        let id = SortId::from_index(self.sorts.len());
        self.sorts.push(node.clone());
        self.sort_interner.insert(node, id);
        id
    }

    #[inline]
    pub fn bool_sort(&self) -> SortId {
        self.bool_sort
    }
    #[inline]
    pub fn int_sort(&self) -> SortId {
        self.int_sort
    }
    #[inline]
    pub fn real_sort(&self) -> SortId {
        self.real_sort
    }
    #[inline]
    pub fn string_sort(&self) -> SortId {
        self.string_sort
    }

    pub fn declare_sort(&mut self, name: &str) -> SortId {
        let sym = self.symbols.intern(name);
        self.intern_sort(SortNode::Uninterpreted(sym))
    }

    pub fn array_sort(&mut self, index: SortId, elem: SortId) -> SortId {
        self.intern_sort(SortNode::Array(index, elem))
    }

    /// Intern the (_ BitVec width) sort. width must be >= 1.
    pub fn bv_sort(&mut self, width: u32) -> SortId {
        debug_assert!(width >= 1, "BitVec width must be >= 1");
        self.intern_sort(SortNode::BitVec(width))
    }

    /// The width of a BitVec sort, or None if `s` is not a BitVec sort.
    pub fn bv_width(&self, s: SortId) -> Option<u32> {
        match self.sort_node(s) {
            SortNode::BitVec(n) => Some(*n),
            _ => None,
        }
    }

    /// Intern the (_ FloatingPoint eb sb) sort. Requires eb >= 2 and sb >= 2.
    pub fn fp_sort(&mut self, eb: u32, sb: u32) -> SortId {
        debug_assert!(eb >= 2 && sb >= 2, "FloatingPoint requires eb>=2, sb>=2");
        self.intern_sort(SortNode::Float(eb, sb))
    }

    /// Intern the RoundingMode sort.
    pub fn rm_sort(&mut self) -> SortId {
        self.intern_sort(SortNode::RoundingMode)
    }

    /// (eb, sb) of a Float sort, or None if `s` is not a Float sort.
    pub fn fp_widths(&self, s: SortId) -> Option<(u32, u32)> {
        match self.sort_node(s) {
            SortNode::Float(eb, sb) => Some((*eb, *sb)),
            _ => None,
        }
    }

    pub fn sort_node(&self, id: SortId) -> &SortNode {
        &self.sorts[id.index()]
    }

    pub fn symbol_name(&self, sym: SymbolId) -> &str {
        self.symbols.resolve(sym)
    }
}

impl Context {
    pub fn sort_of(&self, t: TermId) -> SortId {
        match self.term_node(t) {
            TermNode::App { sort, .. } => *sort,
            TermNode::Const { sort, .. } => *sort,
        }
    }

    pub fn declare_fun(&mut self, name: &str, params: &[SortId], result: SortId) -> SymbolId {
        let sym = self.symbols.intern(name);
        self.fun_sigs.insert(sym, (params.to_vec(), result));
        sym
    }

    /// Look up a symbol by name without interning it. Used by the solver's
    /// word-normalization pass to mint fresh names that cannot collide with
    /// user-declared symbols.
    pub fn lookup_symbol(&self, text: &str) -> Option<SymbolId> {
        self.symbols.lookup(text)
    }

    /// Mark `sym` as solver-internal (reserved). Called by solver passes that
    /// mint fresh symbols so user declarations naming them can be rejected.
    pub fn reserve_symbol(&mut self, sym: SymbolId) {
        self.reserved_syms.insert(sym);
    }

    /// Whether `sym` was minted by a solver-internal pass (see `reserve_symbol`).
    pub fn is_reserved(&self, sym: SymbolId) -> bool {
        self.reserved_syms.contains(&sym)
    }

    /// Build (and intern) `op` applied to `args`, checking well-sortedness.
    pub fn mk_app(&mut self, op: Op, args: &[TermId]) -> Result<TermId, SortError> {
        let result_sort = self.check_app(op, args)?;
        let slice = self.push_children(args);
        let key = TermKey::App {
            op,
            args: args.to_vec(),
            sort: result_sort,
        };
        Ok(self.intern_with_key(
            key,
            TermNode::App {
                op,
                args: slice,
                sort: result_sort,
            },
        ))
    }

    pub fn mk_eq(&mut self, a: TermId, b: TermId) -> Result<TermId, SortError> {
        self.mk_app(Op::Builtin(BuiltinOp::Eq), &[a, b])
    }

    /// Returns the result sort if the application is well-sorted.
    /// Takes `&mut self` because BV ops may need to intern a new BitVec result sort.
    fn check_app(&mut self, op: Op, args: &[TermId]) -> Result<SortId, SortError> {
        let bool_s = self.bool_sort();
        match op {
            Op::Uninterpreted(sym) => {
                let (params, result) =
                    self.fun_sigs.get(&sym).ok_or(SortError::UndeclaredSymbol)?;
                if args.len() != params.len() {
                    return Err(SortError::Arity {
                        expected: params.len(),
                        found: args.len(),
                    });
                }
                // Clone to avoid holding a borrow while calling sort_of.
                let params: Vec<SortId> = params.clone();
                let result = *result;
                for (&arg, &expected) in args.iter().zip(params.iter()) {
                    let found = self.sort_of(arg);
                    if found != expected {
                        return Err(SortError::Mismatch { expected, found });
                    }
                }
                Ok(result)
            }
            Op::Builtin(b) => self.check_builtin(b, args, bool_s),
        }
    }

    fn check_builtin(
        &mut self,
        b: BuiltinOp,
        args: &[TermId],
        bool_s: SortId,
    ) -> Result<SortId, SortError> {
        use BuiltinOp::*;
        let int_s = self.int_sort();
        let real_s = self.real_sort();
        let is_arith = |s: SortId| s == int_s || s == real_s;
        match b {
            // Boolean connectives: all args Bool -> Bool.
            Not => {
                expect_arity(args, 1)?;
                expect_all(self, args, bool_s)?;
                Ok(bool_s)
            }
            And | Or | Implies | Xor => {
                if args.len() < 2 {
                    return Err(SortError::Arity {
                        expected: 2,
                        found: args.len(),
                    });
                }
                expect_all(self, args, bool_s)?;
                Ok(bool_s)
            }
            Ite => {
                expect_arity(args, 3)?;
                if self.sort_of(args[0]) != bool_s {
                    return Err(SortError::Mismatch {
                        expected: bool_s,
                        found: self.sort_of(args[0]),
                    });
                }
                let then_s = self.sort_of(args[1]);
                let else_s = self.sort_of(args[2]);
                if then_s != else_s {
                    return Err(SortError::Mismatch {
                        expected: then_s,
                        found: else_s,
                    });
                }
                Ok(then_s)
            }
            // Equality / distinct: >=2 args of one common sort -> Bool.
            Eq | Distinct => {
                if args.len() < 2 {
                    return Err(SortError::Arity {
                        expected: 2,
                        found: args.len(),
                    });
                }
                let first = self.sort_of(args[0]);
                for &a in &args[1..] {
                    let s = self.sort_of(a);
                    if s != first {
                        return Err(SortError::Mismatch {
                            expected: first,
                            found: s,
                        });
                    }
                }
                Ok(bool_s)
            }
            // Arithmetic: all args one arithmetic sort.
            Neg => {
                expect_arity(args, 1)?;
                let s = self.sort_of(args[0]);
                if !is_arith(s) {
                    return Err(SortError::NotApplicable);
                }
                Ok(s)
            }
            Add | Sub | Mul => {
                if args.len() < 2 {
                    return Err(SortError::Arity {
                        expected: 2,
                        found: args.len(),
                    });
                }
                let s = self.sort_of(args[0]);
                if !is_arith(s) {
                    return Err(SortError::NotApplicable);
                }
                for &a in &args[1..] {
                    if self.sort_of(a) != s {
                        return Err(SortError::NotApplicable);
                    }
                }
                Ok(s)
            }
            Le | Lt | Ge | Gt => {
                expect_arity(args, 2)?;
                let s = self.sort_of(args[0]);
                if !is_arith(s) || self.sort_of(args[1]) != s {
                    return Err(SortError::NotApplicable);
                }
                Ok(bool_s)
            }
            Select => {
                expect_arity(args, 2)?;
                let (idx, elem) = match self.sort_node(self.sort_of(args[0])) {
                    SortNode::Array(i, e) => (*i, *e),
                    _ => return Err(SortError::NotApplicable),
                };
                let found = self.sort_of(args[1]);
                if found != idx {
                    return Err(SortError::Mismatch {
                        expected: idx,
                        found,
                    });
                }
                Ok(elem)
            }
            Store => {
                expect_arity(args, 3)?;
                let arr = self.sort_of(args[0]);
                let (idx, elem) = match self.sort_node(arr) {
                    SortNode::Array(i, e) => (*i, *e),
                    _ => return Err(SortError::NotApplicable),
                };
                let fi = self.sort_of(args[1]);
                if fi != idx {
                    return Err(SortError::Mismatch {
                        expected: idx,
                        found: fi,
                    });
                }
                let fe = self.sort_of(args[2]);
                if fe != elem {
                    return Err(SortError::Mismatch {
                        expected: elem,
                        found: fe,
                    });
                }
                Ok(arr)
            }
            // ── Bitvector operators ───────────────────────────────────────────
            BvNot | BvNeg => {
                expect_arity(args, 1)?;
                let n = self.require_bv(args[0])?;
                Ok(self.bv_sort(n))
            }
            BvAnd | BvOr | BvXor | BvNand | BvNor | BvXnor | BvAdd | BvSub | BvMul | BvUdiv
            | BvUrem | BvSdiv | BvSrem | BvSmod | BvShl | BvLshr | BvAshr => {
                expect_arity(args, 2)?;
                let n = self.require_bv(args[0])?;
                let m = self.require_bv(args[1])?;
                if n != m {
                    return Err(SortError::Mismatch {
                        expected: self.sort_of(args[0]),
                        found: self.sort_of(args[1]),
                    });
                }
                Ok(self.bv_sort(n))
            }
            BvUlt | BvUle | BvUgt | BvUge | BvSlt | BvSle | BvSgt | BvSge => {
                expect_arity(args, 2)?;
                let n = self.require_bv(args[0])?;
                let m = self.require_bv(args[1])?;
                if n != m {
                    return Err(SortError::Mismatch {
                        expected: self.sort_of(args[0]),
                        found: self.sort_of(args[1]),
                    });
                }
                Ok(bool_s)
            }
            BvConcat => {
                expect_arity(args, 2)?;
                let n = self.require_bv(args[0])?;
                let m = self.require_bv(args[1])?;
                Ok(self.bv_sort(n + m))
            }
            BvExtract { hi, lo } => {
                expect_arity(args, 1)?;
                let n = self.require_bv(args[0])?;
                // Requires: lo <= hi < n  (i.e. hi < n and lo <= hi)
                if !(hi < n && lo <= hi) {
                    return Err(SortError::BvIndex);
                }
                Ok(self.bv_sort(hi - lo + 1))
            }
            BvZeroExtend(k) | BvSignExtend(k) => {
                expect_arity(args, 1)?;
                let n = self.require_bv(args[0])?;
                Ok(self.bv_sort(n + k))
            }
            BvRotateLeft(_) | BvRotateRight(_) => {
                expect_arity(args, 1)?;
                let n = self.require_bv(args[0])?;
                Ok(self.bv_sort(n))
            }
            BvRepeat(k) => {
                expect_arity(args, 1)?;
                if k < 1 {
                    return Err(SortError::BvIndex);
                }
                let n = self.require_bv(args[0])?;
                Ok(self.bv_sort(n * k))
            }
            // ── String operators ─────────────────────────────────────────────
            StrConcat => {
                if args.len() < 2 {
                    return Err(SortError::Arity {
                        expected: 2,
                        found: args.len(),
                    });
                }
                let str_s = self.string_sort();
                expect_all(self, args, str_s)?;
                Ok(str_s)
            }
            StrLen => {
                expect_arity(args, 1)?;
                let str_s = self.string_sort();
                if self.sort_of(args[0]) != str_s {
                    return Err(SortError::Mismatch {
                        expected: str_s,
                        found: self.sort_of(args[0]),
                    });
                }
                Ok(self.int_sort())
            }
            StrAt => {
                expect_arity(args, 2)?;
                let (str_s, int_s) = (self.string_sort(), self.int_sort());
                if self.sort_of(args[0]) != str_s {
                    return Err(SortError::Mismatch {
                        expected: str_s,
                        found: self.sort_of(args[0]),
                    });
                }
                if self.sort_of(args[1]) != int_s {
                    return Err(SortError::Mismatch {
                        expected: int_s,
                        found: self.sort_of(args[1]),
                    });
                }
                Ok(str_s)
            }
            StrSubstr => {
                expect_arity(args, 3)?;
                let (str_s, int_s) = (self.string_sort(), self.int_sort());
                if self.sort_of(args[0]) != str_s {
                    return Err(SortError::Mismatch {
                        expected: str_s,
                        found: self.sort_of(args[0]),
                    });
                }
                for &a in &args[1..3] {
                    if self.sort_of(a) != int_s {
                        return Err(SortError::Mismatch {
                            expected: int_s,
                            found: self.sort_of(a),
                        });
                    }
                }
                Ok(str_s)
            }
            StrPrefixOf | StrSuffixOf | StrContains => {
                expect_arity(args, 2)?;
                let str_s = self.string_sort();
                expect_all(self, args, str_s)?;
                Ok(self.bool_sort())
            }
            StrIndexOf => {
                expect_arity(args, 3)?;
                let (str_s, int_s) = (self.string_sort(), self.int_sort());
                for &a in &args[0..2] {
                    if self.sort_of(a) != str_s {
                        return Err(SortError::Mismatch {
                            expected: str_s,
                            found: self.sort_of(a),
                        });
                    }
                }
                if self.sort_of(args[2]) != int_s {
                    return Err(SortError::Mismatch {
                        expected: int_s,
                        found: self.sort_of(args[2]),
                    });
                }
                Ok(int_s)
            }
            StrReplace | StrReplaceAll => {
                expect_arity(args, 3)?;
                let str_s = self.string_sort();
                expect_all(self, args, str_s)?;
                Ok(str_s)
            }
            StrToInt => {
                expect_arity(args, 1)?;
                let (str_s, int_s) = (self.string_sort(), self.int_sort());
                if self.sort_of(args[0]) != str_s {
                    return Err(SortError::Mismatch {
                        expected: str_s,
                        found: self.sort_of(args[0]),
                    });
                }
                Ok(int_s)
            }
            StrFromInt => {
                expect_arity(args, 1)?;
                let (str_s, int_s) = (self.string_sort(), self.int_sort());
                if self.sort_of(args[0]) != int_s {
                    return Err(SortError::Mismatch {
                        expected: int_s,
                        found: self.sort_of(args[0]),
                    });
                }
                Ok(str_s)
            }
            // ── Floating-point: arithmetic ────────────────────────────────────
            FpAbs | FpNeg => {
                expect_arity(args, 1)?;
                let (eb, sb) = self.require_fp(args[0])?;
                Ok(self.fp_sort(eb, sb))
            }
            FpAdd | FpSub | FpMul | FpDiv => {
                expect_arity(args, 3)?;
                self.require_rm(args[0])?;
                let (eb, sb) = self.require_fp(args[1])?;
                let (eb2, sb2) = self.require_fp(args[2])?;
                if (eb, sb) != (eb2, sb2) {
                    return Err(SortError::Mismatch {
                        expected: self.sort_of(args[1]),
                        found: self.sort_of(args[2]),
                    });
                }
                Ok(self.fp_sort(eb, sb))
            }
            FpFma => {
                expect_arity(args, 4)?;
                self.require_rm(args[0])?;
                let (eb, sb) = self.require_fp(args[1])?;
                for &a in &args[2..4] {
                    let (e, s) = self.require_fp(a)?;
                    if (e, s) != (eb, sb) {
                        return Err(SortError::Mismatch {
                            expected: self.sort_of(args[1]),
                            found: self.sort_of(a),
                        });
                    }
                }
                Ok(self.fp_sort(eb, sb))
            }
            FpSqrt | FpRoundToIntegral => {
                expect_arity(args, 2)?;
                self.require_rm(args[0])?;
                let (eb, sb) = self.require_fp(args[1])?;
                Ok(self.fp_sort(eb, sb))
            }
            FpRem | FpMin | FpMax => {
                expect_arity(args, 2)?;
                let (eb, sb) = self.require_fp(args[0])?;
                let (eb2, sb2) = self.require_fp(args[1])?;
                if (eb, sb) != (eb2, sb2) {
                    return Err(SortError::Mismatch {
                        expected: self.sort_of(args[0]),
                        found: self.sort_of(args[1]),
                    });
                }
                Ok(self.fp_sort(eb, sb))
            }
            // ── Floating-point: comparisons → Bool ────────────────────────────
            FpLeq | FpLt | FpGeq | FpGt | FpEq => {
                expect_arity(args, 2)?;
                let (eb, sb) = self.require_fp(args[0])?;
                let (eb2, sb2) = self.require_fp(args[1])?;
                if (eb, sb) != (eb2, sb2) {
                    return Err(SortError::Mismatch {
                        expected: self.sort_of(args[0]),
                        found: self.sort_of(args[1]),
                    });
                }
                Ok(bool_s)
            }
            // ── Floating-point: classification → Bool ─────────────────────────
            FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite | FpIsNaN | FpIsNegative
            | FpIsPositive => {
                expect_arity(args, 1)?;
                self.require_fp(args[0])?;
                Ok(bool_s)
            }
            // ── Floating-point: bit constructor ───────────────────────────────
            FpFromBits => {
                expect_arity(args, 3)?;
                let w_sign = self.require_bv(args[0])?;
                let w_exp = self.require_bv(args[1])?;
                let w_sig = self.require_bv(args[2])?;
                if w_sign != 1 {
                    return Err(SortError::FpIndex);
                }
                let eb = w_exp;
                let sb = w_sig + 1;
                if eb < 2 || sb < 2 {
                    return Err(SortError::FpIndex);
                }
                Ok(self.fp_sort(eb, sb))
            }
            // ── Floating-point: conversions ───────────────────────────────────
            ToFp { eb, sb } => {
                if eb < 2 || sb < 2 {
                    return Err(SortError::FpIndex);
                }
                match args.len() {
                    // bitcast: a single BV of width eb+sb
                    1 => {
                        let n = self.require_bv(args[0])?;
                        if n != eb + sb {
                            return Err(SortError::FpIndex);
                        }
                        Ok(self.fp_sort(eb, sb))
                    }
                    // (RM, X): X is Float, BV (signed int), or Real
                    2 => {
                        self.require_rm(args[0])?;
                        let s1 = self.sort_of(args[1]);
                        let ok = self.fp_widths(s1).is_some()
                            || self.bv_width(s1).is_some()
                            || s1 == real_s;
                        if !ok {
                            return Err(SortError::NotApplicable);
                        }
                        Ok(self.fp_sort(eb, sb))
                    }
                    n => Err(SortError::Arity {
                        expected: 2,
                        found: n,
                    }),
                }
            }
            ToFpUnsigned { eb, sb } => {
                if eb < 2 || sb < 2 {
                    return Err(SortError::FpIndex);
                }
                expect_arity(args, 2)?;
                self.require_rm(args[0])?;
                self.require_bv(args[1])?;
                Ok(self.fp_sort(eb, sb))
            }
            FpToUbv(m) | FpToSbv(m) => {
                expect_arity(args, 2)?;
                if m < 1 {
                    return Err(SortError::FpIndex);
                }
                self.require_rm(args[0])?;
                self.require_fp(args[1])?;
                Ok(self.bv_sort(m))
            }
            FpToReal => {
                expect_arity(args, 1)?;
                self.require_fp(args[0])?;
                Ok(real_s)
            }
        }
    }

    /// Return the width of a BitVec-sorted term, or `SortError::NotBitVec` if
    /// the term does not have a BitVec sort.
    fn require_bv(&self, t: TermId) -> Result<u32, SortError> {
        self.bv_width(self.sort_of(t)).ok_or(SortError::NotBitVec)
    }

    /// (eb, sb) of a Float-sorted term, or `SortError::NotFloat`.
    fn require_fp(&self, t: TermId) -> Result<(u32, u32), SortError> {
        self.fp_widths(self.sort_of(t)).ok_or(SortError::NotFloat)
    }

    /// Ok(()) iff `t` has the RoundingMode sort, else `SortError::NotRoundingMode`.
    fn require_rm(&mut self, t: TermId) -> Result<(), SortError> {
        let rm = self.rm_sort();
        if self.sort_of(t) == rm {
            Ok(())
        } else {
            Err(SortError::NotRoundingMode)
        }
    }
}

fn expect_arity(args: &[TermId], n: usize) -> Result<(), SortError> {
    if args.len() == n {
        Ok(())
    } else {
        Err(SortError::Arity {
            expected: n,
            found: args.len(),
        })
    }
}

fn expect_all(ctx: &Context, args: &[TermId], expected: SortId) -> Result<(), SortError> {
    for &a in args {
        let found = ctx.sort_of(a);
        if found != expected {
            return Err(SortError::Mismatch { expected, found });
        }
    }
    Ok(())
}

/// Reduce `value` modulo 2^width into the range `[0, 2^width)`.
///
/// Builds 2^width by repeated doubling (avoids relying on `Shl` for `Integer`)
/// then uses `div_rem` (truncated). Because `div_rem` gives a remainder with
/// the sign of the dividend, negative inputs yield a negative remainder; we add
/// the modulus once to bring it into `[0, 2^width)`.
fn reduce_mod_pow2(value: &Integer, width: u32) -> Integer {
    // Build modulus = 2^width by repeated doubling from 1.
    let mut modulus = Integer::one();
    let two = Integer::from(2i128);
    for _ in 0..width {
        modulus *= two.clone();
    }
    let (_, mut rem) = value.div_rem(&modulus);
    if rem.is_negative() {
        rem += modulus;
    }
    rem
}

/// A fully-resolved structural key for term interning. Distinct from `TermNode`
/// because `TermNode::App` stores a `ChildSlice` (offset into the arena); two
/// structurally identical apps built at different times would have different
/// slices but must intern to the same id. The key resolves children to their ids.
#[derive(Clone, PartialEq, Eq, Hash)]
enum TermKey {
    App {
        op: crate::term::Op,
        args: Vec<TermId>,
        sort: SortId,
    },
    Const {
        val: ConstVal,
        sort: SortId,
    },
}

impl Context {
    fn intern_with_key(&mut self, key: TermKey, node: TermNode) -> TermId {
        if let Some(&id) = self.term_interner.get(&key) {
            return id;
        }
        let id = TermId::from_index(self.nodes.len());
        self.nodes.push(node);
        self.term_interner.insert(key, id);
        id
    }

    pub(crate) fn push_children(&mut self, args: &[TermId]) -> ChildSlice {
        let off = self.children.len() as u32;
        self.children.extend_from_slice(args);
        ChildSlice {
            off,
            len: args.len() as u32,
        }
    }

    pub fn mk_const_bool(&mut self, b: bool) -> TermId {
        let sort = self.bool_sort();
        let val = ConstVal::Bool(b);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    pub fn mk_numeral(&mut self, value: Rational, sort: SortId) -> TermId {
        // Intern by numeric value: reuse an existing RatId if the value is present.
        let rat_id = match self.nums.iter().position(|r| *r == value) {
            Some(idx) => RatId::new(idx as u32),
            None => {
                let id = RatId::new(self.nums.len() as u32);
                self.nums.push(value);
                id
            }
        };
        let val = ConstVal::Num(rat_id);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    pub fn term_node(&self, id: TermId) -> &TermNode {
        &self.nodes[id.index()]
    }

    /// Returns `true` if `id` was interned into this context (bounds check).
    pub fn contains_term(&self, id: TermId) -> bool {
        id.index() < self.nodes.len()
    }

    /// The exact `Rational` of a numeral term, or `None` if `t` is not a numeral.
    pub fn numeral_value(&self, t: TermId) -> Option<&Rational> {
        match self.term_node(t) {
            TermNode::Const {
                val: ConstVal::Num(id),
                ..
            } => Some(&self.nums[id.index()]),
            _ => None,
        }
    }

    /// The exact `Rational` of a **constant** Real term — a numeral (literals and
    /// parser-folded `(/ lit lit)` both intern as numerals) or a unary `(- c)` of a
    /// constant Real — or `None` if `t` is symbolic (a Real variable, `(* recip x)`,
    /// nested arithmetic). SHARED by the FP `to_fp` fence (shinri-solver) and folder
    /// (shinri-fp) so they admit exactly the same set — a soundness invariant.
    pub fn const_real_value(&self, t: TermId) -> Option<Rational> {
        if let Some(r) = self.numeral_value(t) {
            return Some(r.clone());
        }
        if let TermNode::App {
            op: Op::Builtin(BuiltinOp::Neg),
            args,
            ..
        } = self.term_node(t)
        {
            let kids = self.children(*args);
            if kids.len() == 1 {
                let inner = self.const_real_value(kids[0])?;
                return Some(Rational::new(Integer::from(-1i64), Integer::one()) * inner);
            }
        }
        None
    }

    /// Intern a bitvector literal. `value` is reduced mod 2^width into `[0, 2^width)`.
    pub fn mk_bv_const(&mut self, width: u32, value: Integer) -> TermId {
        let reduced = reduce_mod_pow2(&value, width);
        let bv_id = match self
            .bvs
            .iter()
            .position(|(w, v)| *w == width && *v == reduced)
        {
            Some(idx) => BvId::new(idx as u32),
            None => {
                let id = BvId::new(self.bvs.len() as u32);
                self.bvs.push((width, reduced));
                id
            }
        };
        let sort = self.bv_sort(width);
        let val = ConstVal::BitVec(bv_id);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    /// Return the `(width, &value)` of a BV literal term, or `None` if `t` is not one.
    pub fn bv_const_value(&self, t: TermId) -> Option<(u32, &Integer)> {
        match self.term_node(t) {
            TermNode::Const {
                val: ConstVal::BitVec(id),
                ..
            } => {
                let (w, v) = &self.bvs[id.index()];
                Some((*w, v))
            }
            _ => None,
        }
    }

    /// Intern a string literal constant. Equal values hash-cons to the same `TermId`.
    pub fn mk_string_const(&mut self, value: &str) -> TermId {
        let sort = self.string_sort();
        let id = match self.str_lits.iter().position(|s| s.as_ref() == value) {
            Some(idx) => StringId::new(idx as u32),
            None => {
                let id = StringId::new(self.str_lits.len() as u32);
                self.str_lits.push(value.into());
                id
            }
        };
        let val = ConstVal::String(id);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    /// Return the string value of a string-literal term, or `None` if `t` is not one.
    pub fn string_const_value(&self, t: TermId) -> Option<&str> {
        match self.term_node(t) {
            TermNode::Const {
                val: ConstVal::String(id),
                ..
            } => Some(self.str_lits[id.index()].as_ref()),
            _ => None,
        }
    }

    /// Intern an FP literal of sort (eb, sb) with the given W = eb+sb bit pattern.
    pub fn mk_fp_const(&mut self, eb: u32, sb: u32, bits: Integer) -> TermId {
        let fp_id = match self
            .fps
            .iter()
            .position(|(e, s, v)| *e == eb && *s == sb && *v == bits)
        {
            Some(idx) => FpId::new(idx as u32),
            None => {
                let id = FpId::new(self.fps.len() as u32);
                self.fps.push((eb, sb, bits));
                id
            }
        };
        let sort = self.fp_sort(eb, sb);
        let val = ConstVal::Float(fp_id);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    /// Intern a rounding-mode constant.
    pub fn mk_rm_const(&mut self, rm: crate::term::RoundingMode) -> TermId {
        let sort = self.rm_sort();
        let val = ConstVal::Rm(rm);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    /// (eb, sb, bits) of an FP literal term, or None.
    pub fn fp_const_value(&self, t: TermId) -> Option<(u32, u32, &Integer)> {
        match self.term_node(t) {
            TermNode::Const {
                val: ConstVal::Float(id),
                ..
            } => {
                let (e, s, v) = &self.fps[id.index()];
                Some((*e, *s, v))
            }
            _ => None,
        }
    }

    /// The rounding mode of an RM constant term, or None.
    pub fn rm_const_value(&self, t: TermId) -> Option<crate::term::RoundingMode> {
        match self.term_node(t) {
            TermNode::Const {
                val: ConstVal::Rm(rm),
                ..
            } => Some(*rm),
            _ => None,
        }
    }

    pub fn children(&self, slice: ChildSlice) -> &[TermId] {
        let start = slice.off as usize;
        let end = start + slice.len as usize;
        &self.children[start..end]
    }

    /// Rebuild `t`, replacing each occurrence of `params[i]` with `args[i]`.
    /// Re-interns the result (maximal sharing preserved).
    pub fn substitute(&mut self, t: TermId, params: &[TermId], args: &[TermId]) -> TermId {
        debug_assert_eq!(
            params.len(),
            args.len(),
            "substitute: param/arg length mismatch"
        );
        // Direct replacement at this node?
        if let Some(pos) = params.iter().position(|&p| p == t) {
            return args[pos];
        }
        match self.term_node(t).clone() {
            TermNode::Const { .. } => t, // constants contain no params
            TermNode::App {
                op, args: slice, ..
            } => {
                let child_ids: Vec<TermId> = self.children(slice).to_vec();
                let mut new_children = Vec::with_capacity(child_ids.len());
                let mut changed = false;
                for c in child_ids {
                    let nc = self.substitute(c, params, args);
                    changed |= nc != c;
                    new_children.push(nc);
                }
                if !changed {
                    return t;
                }
                // A sort-consistent substitution cannot make a well-sorted term
                // ill-sorted, so this rebuild always succeeds.
                self.mk_app(op, &new_children)
                    .expect("substitute: sort-consistent rebuild cannot fail")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::SortError;
    use crate::sort::SortNode;
    use crate::term::{BuiltinOp, ConstVal, Op, TermNode};
    use shinri_num::{Integer, Rational};

    #[test]
    fn well_known_sorts_distinct_and_stable() {
        let ctx = Context::new();
        assert_ne!(ctx.bool_sort(), ctx.int_sort());
        assert_ne!(ctx.int_sort(), ctx.real_sort());
        assert_eq!(*ctx.sort_node(ctx.bool_sort()), SortNode::Bool);
        assert_eq!(*ctx.sort_node(ctx.int_sort()), SortNode::Int);
        assert_eq!(*ctx.sort_node(ctx.real_sort()), SortNode::Real);
    }

    #[test]
    fn declare_sort_interns() {
        let mut ctx = Context::new();
        let a = ctx.declare_sort("A");
        let b = ctx.declare_sort("B");
        let a2 = ctx.declare_sort("A");
        assert_eq!(a, a2);
        assert_ne!(a, b);
    }

    #[test]
    fn bool_consts_intern() {
        let mut ctx = Context::new();
        let t = ctx.mk_const_bool(true);
        let t2 = ctx.mk_const_bool(true);
        let f = ctx.mk_const_bool(false);
        assert_eq!(t, t2);
        assert_ne!(t, f);
        match ctx.term_node(t) {
            TermNode::Const {
                val: ConstVal::Bool(b),
                sort,
            } => {
                assert!(*b);
                assert_eq!(*sort, ctx.bool_sort());
            }
            _ => panic!("expected bool const"),
        }
    }

    #[test]
    fn numerals_intern_by_value() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let a = ctx.mk_numeral(Rational::from_int(7i128.into()), int);
        let b = ctx.mk_numeral(Rational::from_int(7i128.into()), int);
        let c = ctx.mk_numeral(Rational::from_int(8i128.into()), int);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn mk_app_checks_arithmetic_sorts() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let three = ctx.mk_numeral(shinri_num::Rational::from_int(3i128.into()), int);
        // 2 + 3 : Int
        let sum = ctx
            .mk_app(Op::Builtin(BuiltinOp::Add), &[two, three])
            .unwrap();
        assert_eq!(ctx.sort_of(sum), int);
        // 2 <= 3 : Bool
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[two, three])
            .unwrap();
        assert_eq!(ctx.sort_of(le), ctx.bool_sort());
    }

    #[test]
    fn mk_app_rejects_bool_in_arithmetic() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let t = ctx.mk_const_bool(true);
        let err = ctx
            .mk_app(Op::Builtin(BuiltinOp::Add), &[two, t])
            .unwrap_err();
        assert_eq!(err, SortError::NotApplicable);
    }

    #[test]
    fn mk_eq_requires_matching_sorts() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let t = ctx.mk_const_bool(true);
        assert!(ctx.mk_eq(two, two).is_ok());
        assert!(matches!(ctx.mk_eq(two, t), Err(SortError::Mismatch { .. })));
        let eq_id = ctx.mk_eq(two, two).unwrap();
        assert_eq!(ctx.sort_of(eq_id), ctx.bool_sort());
    }

    #[test]
    fn uninterpreted_application_checks_signature() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let bool_s = ctx.bool_sort();
        // declare-fun p (Int) Bool
        let p = ctx.declare_fun("p", &[int], bool_s);
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let app = ctx.mk_app(Op::Uninterpreted(p), &[two]).unwrap();
        assert_eq!(ctx.sort_of(app), bool_s);
        // wrong arity
        let err = ctx.mk_app(Op::Uninterpreted(p), &[two, two]).unwrap_err();
        assert_eq!(
            err,
            SortError::Arity {
                expected: 1,
                found: 2
            }
        );
    }

    #[test]
    fn substitute_replaces_leaves_and_reinterns() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        // body: x + 1, with x a placeholder param (an uninterpreted Int constant)
        let xsym = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xsym), &[]).unwrap();
        let one = ctx.mk_numeral(shinri_num::Rational::from_int(1i128.into()), int);
        let body = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, one]).unwrap();
        // substitute x := 5  =>  5 + 1
        let five = ctx.mk_numeral(shinri_num::Rational::from_int(5i128.into()), int);
        let result = ctx.substitute(body, &[x], &[five]);
        let expected = ctx
            .mk_app(Op::Builtin(BuiltinOp::Add), &[five, one])
            .unwrap();
        assert_eq!(result, expected); // re-interned to the same id
    }

    #[test]
    fn numeral_value_reads_back_the_rational() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let r = shinri_num::Rational::new(3i128.into(), 4i128.into()); // 3/4
        let t = ctx.mk_numeral(r.clone(), real);
        assert_eq!(ctx.numeral_value(t), Some(&r));
        // A non-numeral term returns None.
        let x = ctx.declare_fun("x", &[], real);
        let xt = ctx.mk_app(crate::term::Op::Uninterpreted(x), &[]).unwrap();
        assert_eq!(ctx.numeral_value(xt), None);
    }

    #[test]
    fn substitute_is_identity_when_no_param_occurs() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let one = ctx.mk_numeral(shinri_num::Rational::from_int(1i128.into()), int);
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let three = ctx.mk_numeral(shinri_num::Rational::from_int(3i128.into()), int);
        let sum = ctx
            .mk_app(Op::Builtin(BuiltinOp::Add), &[one, two])
            .unwrap();
        assert_eq!(ctx.substitute(sum, &[three], &[one]), sum);
    }

    #[test]
    fn bv_const_roundtrips_value_and_sort() {
        use shinri_num::Integer;
        let mut ctx = Context::new();
        let t = ctx.mk_bv_const(8, Integer::from(5u64));
        assert_eq!(ctx.sort_of(t), ctx.bv_sort(8));
        let (w, v) = ctx.bv_const_value(t).unwrap();
        assert_eq!(w, 8);
        assert_eq!(*v, Integer::from(5u64));
        // Hash-consing: identical literal interns once.
        let t2 = ctx.mk_bv_const(8, Integer::from(5u64));
        assert_eq!(t, t2);
    }

    #[test]
    fn reduce_mod_pow2_negative_and_over_width() {
        // -1 mod 2^8 = 255
        let neg_one = Integer::from(-1i128);
        let r = reduce_mod_pow2(&neg_one, 8);
        assert_eq!(r, Integer::from(255u64));
        // 300 mod 2^8 = 44
        let over = Integer::from(300i128);
        let r2 = reduce_mod_pow2(&over, 8);
        assert_eq!(r2, Integer::from(44u64));
    }

    #[test]
    fn bv_sort_interns_by_width() {
        let mut ctx = Context::new();
        let a = ctx.bv_sort(8);
        let b = ctx.bv_sort(8);
        let c = ctx.bv_sort(32);
        assert_eq!(a, b, "same width must intern to the same SortId");
        assert_ne!(a, c);
        assert_eq!(ctx.bv_width(a), Some(8));
        assert_eq!(ctx.bv_width(c), Some(32));
        assert_eq!(ctx.bv_width(ctx.bool_sort()), None);
    }

    #[test]
    fn array_select_store_sorts() {
        let mut ctx = Context::new();
        let idx = ctx.declare_sort("I");
        let elem = ctx.declare_sort("E");
        let arr_sort = ctx.array_sort(idx, elem);

        let sym_a = ctx_decl(&mut ctx, "a", arr_sort);
        let sym_i = ctx_decl(&mut ctx, "i", idx);
        let sym_e = ctx_decl(&mut ctx, "e", elem);
        let a = ctx.mk_app(Op::Uninterpreted(sym_a), &[]).unwrap();
        let i = ctx.mk_app(Op::Uninterpreted(sym_i), &[]).unwrap();
        let e = ctx.mk_app(Op::Uninterpreted(sym_e), &[]).unwrap();

        // (store a i e) : (Array I E)
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        assert_eq!(ctx.sort_of(st), arr_sort);
        // (select (store a i e) i) : E
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        assert_eq!(ctx.sort_of(sel), elem);
        // wrong index sort is rejected
        let e_as_idx = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, e]);
        assert!(e_as_idx.is_err());
    }

    #[test]
    fn bv_op_result_widths() {
        use crate::term::BuiltinOp::*;
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let x = {
            let f = ctx.declare_fun("x", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let y = {
            let f = ctx.declare_fun("y", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };

        let add = ctx.mk_app(Op::Builtin(BvAdd), &[x, y]).unwrap();
        assert_eq!(ctx.bv_width(ctx.sort_of(add)), Some(8));

        let cat = ctx.mk_app(Op::Builtin(BvConcat), &[x, y]).unwrap();
        assert_eq!(ctx.bv_width(ctx.sort_of(cat)), Some(16));

        let ext = ctx
            .mk_app(Op::Builtin(BvExtract { hi: 3, lo: 1 }), &[x])
            .unwrap();
        assert_eq!(ctx.bv_width(ctx.sort_of(ext)), Some(3));

        let ze = ctx.mk_app(Op::Builtin(BvZeroExtend(4)), &[x]).unwrap();
        assert_eq!(ctx.bv_width(ctx.sort_of(ze)), Some(12));

        let ult = ctx.mk_app(Op::Builtin(BvUlt), &[x, y]).unwrap();
        assert_eq!(ctx.sort_of(ult), ctx.bool_sort());
    }

    #[test]
    fn bv_width_mismatch_is_error() {
        use crate::term::BuiltinOp::*;
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let s16 = ctx.bv_sort(16);
        let x = {
            let f = ctx.declare_fun("x", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let z = {
            let f = ctx.declare_fun("z", &[], s16);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        assert!(ctx.mk_app(Op::Builtin(BvAdd), &[x, z]).is_err());
    }

    #[test]
    fn string_const_roundtrips_and_dedups() {
        let mut ctx = Context::new();
        let a = ctx.mk_string_const("ab\"c");
        let b = ctx.mk_string_const("ab\"c");
        let d = ctx.mk_string_const("xyz");
        assert_eq!(a, b, "equal string literals must hash-cons to one TermId");
        assert_ne!(a, d);
        assert_eq!(ctx.sort_of(a), ctx.string_sort());
        assert_eq!(ctx.string_const_value(a), Some("ab\"c"));
        assert_eq!(ctx.string_const_value(d), Some("xyz"));
    }

    #[test]
    fn string_sort_is_stable_singleton() {
        let ctx = Context::new();
        let a = ctx.string_sort();
        let b = ctx.string_sort();
        assert_eq!(a, b, "string_sort must intern to one stable SortId");
        assert_ne!(a, ctx.int_sort());
        assert_ne!(a, ctx.bool_sort());
        assert!(matches!(ctx.sort_node(a), crate::sort::SortNode::String));
    }

    #[test]
    fn string_ops_sort_check() {
        use crate::term::{BuiltinOp, Op};
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let x = {
            let s = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let y = {
            let s = ctx.declare_fun("y", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let i = {
            let s = ctx.declare_fun("i", &[], int_s);
            ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };

        let cc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        assert_eq!(ctx.sort_of(cc), str_s);
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        assert_eq!(ctx.sort_of(len), int_s);
        let at = ctx.mk_app(Op::Builtin(BuiltinOp::StrAt), &[x, i]).unwrap();
        assert_eq!(ctx.sort_of(at), str_s);
        let ss = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrSubstr), &[x, i, i])
            .unwrap();
        assert_eq!(ctx.sort_of(ss), str_s);

        // Ill-sorted: str.len on Int must fail.
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[i]).is_err());
        // Ill-sorted: str.at with String index must fail.
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrAt), &[x, y]).is_err());
    }

    #[test]
    fn string_predicate_sorts() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let bool_s = ctx.bool_sort();
        let f = ctx.declare_fun("x", &[], str_s);
        let x = ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap();
        let lit = ctx.mk_string_const("ab");
        for op in [
            BuiltinOp::StrPrefixOf,
            BuiltinOp::StrSuffixOf,
            BuiltinOp::StrContains,
        ] {
            let t = ctx.mk_app(Op::Builtin(op), &[x, lit]).unwrap();
            assert_eq!(ctx.sort_of(t), bool_s, "{op:?} must be Bool-sorted");
            // Arity 2 enforced.
            assert!(ctx.mk_app(Op::Builtin(op), &[x]).is_err());
            // Both args must be String-sorted.
            let one = ctx.mk_numeral(Rational::from_int(1i128.into()), int_s);
            assert!(ctx.mk_app(Op::Builtin(op), &[x, one]).is_err());
        }
    }

    #[test]
    fn string_indexof_replace_sorts() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let f = ctx.declare_fun("x", &[], str_s);
        let x = ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap();
        let lit = ctx.mk_string_const("ab");
        let i = ctx.mk_numeral(Rational::from_int(1i128.into()), int_s);

        // (str.indexof s sub i): String × String × Int → Int.
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, lit, i])
            .unwrap();
        assert_eq!(ctx.sort_of(idx), int_s, "indexof must be Int-sorted");
        // (str.replace s t u): String × String × String → String.
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[x, lit, lit])
            .unwrap();
        assert_eq!(ctx.sort_of(rep), str_s, "replace must be String-sorted");

        // Arity 3 enforced.
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, lit])
            .is_err());
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[x, lit])
            .is_err());
        // indexof: args 0-1 String, arg 2 Int.
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, lit, lit])
            .is_err());
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, i, i])
            .is_err());
        // replace: all three String.
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[x, lit, i])
            .is_err());
    }

    #[test]
    fn str_replace_all_sort_rule() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let f = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let lit = ctx.mk_string_const("a");
        // Well-sorted: String × String × String → String.
        let app = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[x, lit, lit])
            .unwrap();
        assert_eq!(ctx.sort_of(app), str_s);
        // Wrong arity → error.
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[x, lit])
            .is_err());
        // Int replacement operand → error.
        let i = ctx.mk_numeral(Rational::zero(), ctx.int_sort());
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[x, lit, i])
            .is_err());
    }

    #[test]
    fn fp_and_rm_constants_roundtrip() {
        use crate::term::RoundingMode;
        use shinri_num::Integer;
        let mut ctx = Context::new();

        // +zero in Float32 is all zero bits.
        let pz = ctx.mk_fp_const(8, 24, Integer::zero());
        let pz_again = ctx.mk_fp_const(8, 24, Integer::zero());
        assert_eq!(pz, pz_again, "identical FP consts must be interned equal");
        assert_eq!(ctx.sort_of(pz), ctx.fp_sort(8, 24));
        let (eb, sb, bits) = ctx.fp_const_value(pz).expect("fp const");
        assert_eq!((eb, sb), (8, 24));
        assert!(bits.is_zero());

        let r = ctx.mk_rm_const(RoundingMode::Rne);
        assert_eq!(ctx.sort_of(r), ctx.rm_sort());
        assert_eq!(ctx.rm_const_value(r), Some(RoundingMode::Rne));
        assert_eq!(ctx.rm_const_value(pz), None);
        assert_eq!(ctx.fp_const_value(r), None);
    }

    #[test]
    fn fp_and_rm_sorts_intern_and_roundtrip() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let f32_again = ctx.fp_sort(8, 24);
        let f64 = ctx.fp_sort(11, 53);
        assert_eq!(
            f32, f32_again,
            "equal FP sorts must intern to the same SortId"
        );
        assert_ne!(f32, f64, "different widths must be different sorts");
        assert_eq!(ctx.fp_widths(f32), Some((8, 24)));
        assert_eq!(ctx.fp_widths(f64), Some((11, 53)));
        assert_eq!(ctx.fp_widths(ctx.bool_sort()), None);

        let rm = ctx.rm_sort();
        let rm2 = ctx.rm_sort();
        assert_eq!(rm, rm2, "RoundingMode sort must be unique");
        assert_eq!(ctx.fp_widths(rm), None);
    }

    #[test]
    fn fp_arith_compare_classify_sortcheck() {
        use crate::term::RoundingMode;
        use crate::{BuiltinOp, Op};
        use shinri_num::Integer;
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let yf = ctx.declare_fun("y", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let rne = ctx.mk_rm_const(RoundingMode::Rne);

        // fp.add : (RM, F, F) -> F
        let add = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rne, x, y])
            .unwrap();
        assert_eq!(ctx.sort_of(add), f32);

        // fp.neg : (F) -> F ; fp.abs : (F) -> F
        let neg = ctx.mk_app(Op::Builtin(BuiltinOp::FpNeg), &[x]).unwrap();
        assert_eq!(ctx.sort_of(neg), f32);

        // fp.leq : (F, F) -> Bool ; fp.isNaN : (F) -> Bool
        let leq = ctx.mk_app(Op::Builtin(BuiltinOp::FpLeq), &[x, y]).unwrap();
        assert_eq!(ctx.sort_of(leq), ctx.bool_sort());
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        assert_eq!(ctx.sort_of(isnan), ctx.bool_sort());

        // fp : (BV1, BV8, BV23) -> Float(8,24)
        let b1 = ctx.mk_bv_const(1, Integer::zero());
        let b8 = ctx.mk_bv_const(8, Integer::zero());
        let b23 = ctx.mk_bv_const(23, Integer::zero());
        let ctor = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpFromBits), &[b1, b8, b23])
            .unwrap();
        assert_eq!(ctx.sort_of(ctor), f32);

        // width mismatch on fp.add operands must be a SortError, not a panic
        let f64 = ctx.fp_sort(11, 53);
        let zf = ctx.declare_fun("z", &[], f64);
        let z = ctx.mk_app(Op::Uninterpreted(zf), &[]).unwrap();
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rne, x, z])
            .is_err());
        // missing rounding mode (passing a Float where RM expected) must error
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::FpAdd), &[x, x, y])
            .is_err());
    }

    #[test]
    fn fp_conversion_sortcheck() {
        use crate::term::RoundingMode;
        use crate::{BuiltinOp, Op};
        use shinri_num::Integer;
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let rne = ctx.mk_rm_const(RoundingMode::Rne);

        // bitcast: (_ to_fp 8 24) over a BV32 (1 arg, no RM) -> Float(8,24)
        let b32 = ctx.mk_bv_const(32, Integer::zero());
        let cast = ctx
            .mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[b32])
            .unwrap();
        assert_eq!(ctx.sort_of(cast), f32);

        // FP->FP: (_ to_fp 11 53) RM Float32 -> Float64
        let f64 = ctx.fp_sort(11, 53);
        let widen = ctx
            .mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 11, sb: 53 }), &[rne, x])
            .unwrap();
        assert_eq!(ctx.sort_of(widen), f64);

        // fp.to_sbv 16 : (RM, Float) -> BV16
        let tosbv = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpToSbv(16)), &[rne, x])
            .unwrap();
        assert_eq!(ctx.sort_of(tosbv), ctx.bv_sort(16));

        // fp.to_real : (Float) -> Real
        let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap();
        assert_eq!(ctx.sort_of(toreal), ctx.real_sort());

        // bitcast width mismatch (BV31 into Float(8,24)=32 bits) must error
        let b31 = ctx.mk_bv_const(31, Integer::zero());
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[b31])
            .is_err());

        // boundary: eb<2 must error even if bitcast width eb+sb matches (eb=1,sb=1 -> BV2)
        let b2 = ctx.mk_bv_const(2, Integer::zero());
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 1, sb: 1 }), &[b2])
            .is_err());
    }

    #[test]
    fn const_real_value_folds_literals_and_neg() {
        use shinri_num::Rational;
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        // plain numeral 5/1
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), real);
        assert_eq!(
            ctx.const_real_value(five),
            Some(Rational::from_int(5i128.into()))
        );
        // parser already folds (/ 1 3) to a single numeral; emulate that numeral 1/3
        let third = ctx.mk_numeral(Rational::new(1i128.into(), 3i128.into()), real);
        assert_eq!(
            ctx.const_real_value(third),
            Some(Rational::new(1i128.into(), 3i128.into()))
        );
        // unary negation (- 5/2) -> -5/2
        let fivehalf = ctx.mk_numeral(Rational::new(5i128.into(), 2i128.into()), real);
        let neg = ctx
            .mk_app(Op::Builtin(BuiltinOp::Neg), &[fivehalf])
            .unwrap();
        assert_eq!(
            ctx.const_real_value(neg),
            Some(Rational::new((-5i128).into(), 2i128.into()))
        );
    }

    #[test]
    fn const_real_value_rejects_symbolic() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        // a Real variable is not constant
        let r = ctx.declare_fun("r", &[], real);
        let rt = ctx.mk_app(Op::Uninterpreted(r), &[]).unwrap();
        assert_eq!(ctx.const_real_value(rt), None);
        // (* recip r) — the shape (/ 1 r) desugars to — is not constant
        let recip = ctx.mk_numeral(shinri_num::Rational::new(1i128.into(), 2i128.into()), real);
        let prod = ctx
            .mk_app(Op::Builtin(BuiltinOp::Mul), &[recip, rt])
            .unwrap();
        assert_eq!(ctx.const_real_value(prod), None);
    }

    // helper local to the test module
    fn ctx_decl(ctx: &mut Context, name: &str, s: SortId) -> SymbolId {
        ctx.declare_fun(name, &[], s)
    }

    #[test]
    fn str_to_from_int_sort_rules() {
        // A nullary uninterpreted constant of the given sort (there is no
        // `mk_const`; this is the codebase pattern — see indexof_replace tests).
        fn nullary(ctx: &mut Context, name: &str, sort: SortId) -> TermId {
            let f = ctx.declare_fun(name, &[], sort);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        }
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let n = nullary(&mut ctx, "n", int_s);

        // str.to_int : String -> Int
        let ti = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrToInt), &[s])
            .expect("to_int well-sorted");
        assert_eq!(ctx.sort_of(ti), int_s);

        // str.from_int : Int -> String
        let fi = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrFromInt), &[n])
            .expect("from_int well-sorted");
        assert_eq!(ctx.sort_of(fi), str_s);

        // Wrong sorts rejected.
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrToInt), &[n]).is_err());
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrFromInt), &[s])
            .is_err());
        // Wrong arity rejected.
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrToInt), &[s, s])
            .is_err());
    }
}
