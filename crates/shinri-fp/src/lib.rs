//! shinri-fp: eager bit-blasting of QF_FP to CNF, reusing the shinri-bv Blaster
//! as a gate/clause factory. See
//! docs/superpowers/specs/2026-06-25-shinri-qffp-vertical-slice-design.md.

pub mod blast;
pub mod convert;
pub mod lower;
pub mod lzc;
pub mod model;
pub mod pack;
pub mod reference;
pub mod rm;
pub mod round;
pub mod unpack;

use rustc_hash::FxHashMap;
use shinri_bv::{BitLit, Blaster, WordSink};
use shinri_core::{ConstVal, Context, Op, TermId, TermNode};

/// FP-side blaster: wraps a `shinri_bv::Blaster` (used purely as a gate/clause
/// factory) with its own word cache and variable-bit map, since the Blaster's
/// internal cache is private to shinri-bv.
pub struct FpBlaster {
    pub b: Blaster,
    cache: FxHashMap<TermId, Vec<BitLit>>,
    var_bits: FxHashMap<TermId, Vec<BitLit>>,
    rm_cache: FxHashMap<TermId, [BitLit; 5]>,
}

impl FpBlaster {
    pub fn new() -> Self {
        FpBlaster { b: Blaster::new(), cache: FxHashMap::default(),
                    var_bits: FxHashMap::default(), rm_cache: FxHashMap::default() }
    }

    /// Blast an FP-sorted term to its W=eb+sb bit word (LSB→MSB), memoized.
    /// Slice 1 handles FP constants, nullary FP variables, and FpAbs/FpNeg operator nodes.
    pub fn blast_word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        <Self as WordSink>::word(self, ctx, t)
    }

    /// Blast a Bool-sorted FP atom to a single BitLit.
    pub fn blast_atom(&mut self, ctx: &Context, t: TermId) -> BitLit {
        blast_fp_atom(self, ctx, t)
    }

    /// Bits cached for every FP *variable* term (for model extraction).
    pub fn exported_var_bits(&self) -> FxHashMap<TermId, Vec<BitLit>> {
        self.var_bits.clone()
    }
}

impl Default for FpBlaster {
    fn default() -> Self { Self::new() }
}

impl WordSink for FpBlaster {
    fn word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        if let Some(v) = self.cache.get(&t) {
            return v.clone();
        }
        let bits = blast_fp_word(self, ctx, t);
        // Preserve the eager var-word recording that used to live in blast_word's
        // Uninterpreted arm: fires only on cache-miss, for exactly the FP-sorted
        // nullary vars (byte-identical var set to the pre-refactor behavior).
        if let TermNode::App { op: Op::Uninterpreted(_), args, sort } = ctx.term_node(t) {
            if ctx.children(*args).is_empty() && ctx.fp_widths(*sort).is_some() {
                self.var_bits.insert(t, bits.clone());
            }
        }
        self.cache.insert(t, bits.clone());
        bits
    }
    fn blaster(&mut self) -> &mut Blaster {
        &mut self.b
    }
    fn rm_cache(&mut self) -> &mut FxHashMap<TermId, [BitLit; 5]> {
        &mut self.rm_cache
    }
}

/// Blast a RoundingMode operand to a one-hot selector. Literal modes fold to
/// constants; a symbolic RM variable becomes 3 fresh bits (cached per TermId
/// via the sink's `rm_cache`, so a shared symbolic RM var gets one selector).
fn blast_rm<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> crate::rm::RmSel {
    if let Some(sel) = sink.rm_cache().get(&t) {
        return crate::rm::RmSel { sel: *sel };
    }
    let sel = if let Some(rm) = ctx.rm_const_value(t) {
        crate::rm::literal(sink.blaster(), rm)
    } else {
        // symbolic RoundingMode variable (nullary uninterpreted of RM sort).
        crate::rm::symbolic(sink.blaster())
    };
    sink.rm_cache().insert(t, sel.sel);
    sel
}

/// FP word dispatch, generic over the sink. Assumes `t` is FP-sorted; callers
/// (the sink's `word`) pre-classify by sort. Recurses via `sink.word`, mints
/// gates via `sink.blaster()`. Does NOT touch the word cache or `var_bits` —
/// the sink's `word` owns memoization and var-bit recording.
pub fn blast_fp_word<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> Vec<BitLit> {
    let node = ctx.term_node(t).clone();
    match node {
        TermNode::Const { val: ConstVal::Float(_), .. } => {
            let (eb, sb, bits) = ctx.fp_const_value(t).expect("FP const");
            let w = eb + sb;
            let two = shinri_num::Integer::from(2u64);
            let mut remaining = bits.clone();
            (0..w).map(|_| {
                let (q, r) = remaining.div_rem(&two);
                remaining = q;
                if r.is_zero() { sink.blaster().zero() } else { sink.blaster().one() }
            }).collect()
        }
        TermNode::App { op: Op::Uninterpreted(_), args, sort } => {
            debug_assert!(ctx.children(args).is_empty(), "non-nullary FP fn out of scope");
            let (eb, sb) = ctx.fp_widths(sort).expect("FP-sorted variable");
            (0..(eb + sb)).map(|_| sink.blaster().fresh()).collect()
        }
        TermNode::App { op: Op::Builtin(op), args, sort } => {
            use shinri_core::BuiltinOp::*;
            let (eb, sb) = ctx.fp_widths(sort).expect("FP-sorted op result");
            let kids = ctx.children(args).to_vec();
            match op {
                FpAbs => {
                    let w = sink.word(ctx, kids[0]);
                    crate::blast::structural::abs(sink.blaster(), &w, eb, sb)
                }
                FpNeg => {
                    let w = sink.word(ctx, kids[0]);
                    crate::blast::structural::neg(sink.blaster(), &w, eb, sb)
                }
                FpAdd => {
                    let rm = blast_rm(sink, ctx, kids[0]);
                    let xw = sink.word(ctx, kids[1]);
                    let yw = sink.word(ctx, kids[2]);
                    crate::blast::add::fp_add(sink.blaster(), &xw, &yw, &rm, eb, sb)
                }
                FpSub => {
                    let rm = blast_rm(sink, ctx, kids[0]);
                    let xw = sink.word(ctx, kids[1]);
                    let yw = sink.word(ctx, kids[2]);
                    let neg_y = crate::blast::structural::neg(sink.blaster(), &yw, eb, sb);
                    crate::blast::add::fp_add(sink.blaster(), &xw, &neg_y, &rm, eb, sb)
                }
                FpMul => {
                    let rm = blast_rm(sink, ctx, kids[0]);
                    let xw = sink.word(ctx, kids[1]);
                    let yw = sink.word(ctx, kids[2]);
                    crate::blast::mul::fp_mul(sink.blaster(), &xw, &yw, &rm, eb, sb)
                }
                FpDiv => {
                    let rm = blast_rm(sink, ctx, kids[0]);
                    let xw = sink.word(ctx, kids[1]);
                    let yw = sink.word(ctx, kids[2]);
                    crate::blast::div::fp_div(sink.blaster(), &xw, &yw, &rm, eb, sb)
                }
                FpSqrt => {
                    let rm = blast_rm(sink, ctx, kids[0]);
                    let xw = sink.word(ctx, kids[1]);
                    crate::blast::sqrt::fp_sqrt(sink.blaster(), &xw, &rm, eb, sb)
                }
                FpRoundToIntegral => {
                    let rm = blast_rm(sink, ctx, kids[0]);
                    let xw = sink.word(ctx, kids[1]);
                    crate::blast::roundint::fp_round_to_integral(sink.blaster(), &xw, &rm, eb, sb)
                }
                FpMin => {
                    let xw = sink.word(ctx, kids[0]);
                    let yw = sink.word(ctx, kids[1]);
                    crate::blast::minmax::fp_min(sink.blaster(), &xw, &yw, eb, sb)
                }
                FpMax => {
                    let xw = sink.word(ctx, kids[0]);
                    let yw = sink.word(ctx, kids[1]);
                    crate::blast::minmax::fp_max(sink.blaster(), &xw, &yw, eb, sb)
                }
                FpFma => {
                    let rm = blast_rm(sink, ctx, kids[0]);
                    let xw = sink.word(ctx, kids[1]);
                    let yw = sink.word(ctx, kids[2]);
                    let zw = sink.word(ctx, kids[3]);
                    crate::blast::fma::fp_fma(sink.blaster(), &xw, &yw, &zw, &rm, eb, sb)
                }
                FpRem => {
                    let xw = sink.word(ctx, kids[0]);
                    let yw = sink.word(ctx, kids[1]);
                    crate::blast::rem::fp_rem(sink.blaster(), &xw, &yw, eb, sb)
                }
                ToFp { .. } => {
                    // Non-BV faces only (fence guarantees this): 2 args (RM, X), X = Float | const Real.
                    // `eb`/`sb` here are the outer target widths (result sort); source is X's sort.
                    let rm = blast_rm(sink, ctx, kids[0]);
                    if let Some(q) = ctx.const_real_value(kids[1]) {
                        crate::convert::to_fp_real_const(sink.blaster(), &q, eb, sb, &rm)
                    } else {
                        let (eb_s, sb_s) = ctx.fp_widths(ctx.sort_of(kids[1])).expect("FP source operand");
                        let xw = sink.word(ctx, kids[1]);
                        crate::convert::to_fp_fp(sink.blaster(), &xw, eb_s, sb_s, eb, sb, &rm)
                    }
                }
                other => unreachable!("blast_word: FP op {other:?} is out of slice-1 scope"),
            }
        }
        other => unreachable!("blast_word: unsupported FP word node {other:?} (slice 1)"),
    }
}

/// FP atom (Bool-sorted predicate) dispatch, generic over the sink. No cache:
/// callers recurse into words via `sink.word`, which IS memoized.
pub fn blast_fp_atom<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> BitLit {
    use shinri_core::BuiltinOp::*;
    let node = ctx.term_node(t).clone();
    let TermNode::App { op, args, .. } = node else {
        unreachable!("FP atom must be an application");
    };
    let kids = ctx.children(args).to_vec();
    match op {
        Op::Builtin(Eq) => {
            // core = over Float operands (NaN-aware).
            let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
            let x = sink.word(ctx, kids[0]);
            let y = sink.word(ctx, kids[1]);
            crate::blast::compare::core_eq(sink.blaster(), &x, &y, eb, sb)
        }
        Op::Builtin(Distinct) => {
            let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
            let x = sink.word(ctx, kids[0]);
            let y = sink.word(ctx, kids[1]);
            let eq = crate::blast::compare::core_eq(sink.blaster(), &x, &y, eb, sb);
            sink.blaster().not1(eq)
        }
        Op::Builtin(FpEq) => {
            let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
            let x = sink.word(ctx, kids[0]);
            let y = sink.word(ctx, kids[1]);
            crate::blast::compare::fp_eq(sink.blaster(), &x, &y, eb, sb)
        }
        Op::Builtin(rel @ (FpLt | FpLeq | FpGt | FpGeq)) => {
            let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
            let x = sink.word(ctx, kids[0]);
            let y = sink.word(ctx, kids[1]);
            use crate::blast::compare as cmp;
            match rel {
                FpLt => cmp::fp_lt(sink.blaster(), &x, &y, eb, sb),
                FpLeq => cmp::fp_leq(sink.blaster(), &x, &y, eb, sb),
                FpGt => cmp::fp_gt(sink.blaster(), &x, &y, eb, sb),
                FpGeq => cmp::fp_geq(sink.blaster(), &x, &y, eb, sb),
                _ => unreachable!(),
            }
        }
        Op::Builtin(classify @ (FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite
                                | FpIsNaN | FpIsNegative | FpIsPositive)) => {
            let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operand");
            let w = sink.word(ctx, kids[0]);
            let u = crate::unpack::unpack(sink.blaster(), &w, eb, sb);
            use crate::blast::classify as c;
            match classify {
                FpIsNormal => c::is_normal(sink.blaster(), &u),
                FpIsSubnormal => c::is_subnormal(sink.blaster(), &u),
                FpIsZero => c::is_zero(sink.blaster(), &u),
                FpIsInfinite => c::is_inf(sink.blaster(), &u),
                FpIsNaN => c::is_nan(sink.blaster(), &u),
                FpIsNegative => c::is_negative(sink.blaster(), &u),
                FpIsPositive => c::is_positive(sink.blaster(), &u),
                _ => unreachable!(),
            }
        }
        other => unreachable!("blast_atom: FP atom {other:?} out of slice-1 scope"),
    }
}

/// Blast all `fp_atoms` via one FpBlaster and return a `shinri_bv::Lowered`
/// (reused so the solver's `replay_bv_cnf` applies unchanged). `atom_lit` is
/// keyed by the ORIGINAL atom TermId.
pub fn lower(ctx: &mut Context, fp_atoms: &[TermId]) -> shinri_bv::Lowered {
    let mut lw = crate::lower::Lowerer::new();
    let mut atom_lit: FxHashMap<TermId, BitLit> = FxHashMap::default();
    for &atom in fp_atoms {
        let lit = lw.atom(ctx, atom);
        atom_lit.insert(atom, lit);
    }
    // Pure-FP list: bv side is empty; take the FP map into Lowered.var_bits.
    let (_bv_vars, fp_vars) = lw.var_bits_split(ctx);
    debug_assert!(_bv_vars.is_empty(), "pure-FP lower produced no BV vars");
    shinri_bv::Lowered { cnf: lw.b.finish(), atom_lit, var_bits: fp_vars }
}

#[cfg(test)]
mod lower_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

    #[test]
    fn wordsink_generic_matches_inherent_fp_isnan() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();

        let mut fb1 = FpBlaster::new();
        let w_inherent = fb1.blast_word(&ctx, x);
        let mut fb2 = FpBlaster::new();
        let w_generic = crate::blast_fp_word(&mut fb2, &ctx, x);

        assert_eq!(w_inherent.len(), 32);
        assert_eq!(w_inherent.len(), w_generic.len());
        assert_eq!(fb1.b.num_vars(), fb2.b.num_vars(), "identical var allocation order");
    }

    #[test]
    fn lower_isnan_atom_keys_and_vars() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();

        let lo = lower(&mut ctx, &[isnan]);
        assert!(lo.atom_lit.contains_key(&isnan), "keyed by original atom TermId");
        assert!(lo.var_bits.contains_key(&x), "x exported for model extraction");
        assert_eq!(lo.var_bits[&x].len(), 32);
        assert!(lo.cnf.num_vars >= 1);
    }

    #[test]
    fn lower_core_eq_over_floats_is_an_atom() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let pz = ctx.mk_fp_const(8, 24, Integer::zero());
        let eq = ctx.mk_eq(x, pz).unwrap();
        let lo = lower(&mut ctx, &[eq]);
        assert!(lo.atom_lit.contains_key(&eq), "FP core = must be surrogated");
    }

    #[test]
    fn lower_fp_add_eq_atom() {
        use shinri_core::BuiltinOp;
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let yf = ctx.declare_fun("y", &[], f32);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rne, x, y]).unwrap();
        let two = ctx.mk_fp_const(8, 24, Integer::from(0x4000_0000u64));
        let eq = ctx.mk_eq(add, two).unwrap();
        let lo = lower(&mut ctx, &[eq]);
        assert!(lo.atom_lit.contains_key(&eq), "core = over fp.add must be surrogated");
        assert!(lo.var_bits.contains_key(&x) && lo.var_bits.contains_key(&y), "x,y exported");
    }

    #[test]
    fn lower_fp_mul_eq_atom() {
        use shinri_core::BuiltinOp;
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let yf = ctx.declare_fun("y", &[], f32);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let mul = ctx.mk_app(Op::Builtin(BuiltinOp::FpMul), &[rne, x, y]).unwrap();
        let one = ctx.mk_fp_const(8, 24, Integer::from(0x3F80_0000u64));
        let eq = ctx.mk_eq(mul, one).unwrap();
        let lo = lower(&mut ctx, &[eq]);
        assert!(lo.atom_lit.contains_key(&eq), "core = over fp.mul must be surrogated");
        assert!(lo.var_bits.contains_key(&x) && lo.var_bits.contains_key(&y), "x,y exported");
    }

    #[test]
    fn lower_fp_div_eq_atom() {
        use shinri_core::BuiltinOp;
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let yf = ctx.declare_fun("y", &[], f32);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let div = ctx.mk_app(Op::Builtin(BuiltinOp::FpDiv), &[rne, x, y]).unwrap();
        let one = ctx.mk_fp_const(8, 24, Integer::from(0x3F80_0000u64));
        let eq = ctx.mk_eq(div, one).unwrap();
        let lo = lower(&mut ctx, &[eq]);
        assert!(lo.atom_lit.contains_key(&eq), "core = over fp.div must be surrogated");
        assert!(lo.var_bits.contains_key(&x) && lo.var_bits.contains_key(&y), "x,y exported");
    }

    #[test]
    fn lower_fp_rem_eq_atom() {
        use shinri_core::BuiltinOp;
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let yf = ctx.declare_fun("y", &[], f32);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let rem = ctx.mk_app(Op::Builtin(BuiltinOp::FpRem), &[x, y]).unwrap();
        let one = ctx.mk_fp_const(8, 24, Integer::from(0x3F80_0000u64));
        let eq = ctx.mk_eq(rem, one).unwrap();
        let lo = lower(&mut ctx, &[eq]);
        assert!(lo.atom_lit.contains_key(&eq), "core = over fp.rem must be surrogated");
        assert!(lo.var_bits.contains_key(&x) && lo.var_bits.contains_key(&y), "x,y exported");
    }

    #[test]
    fn lower_to_fp_fp_and_const_real_atoms() {
        use shinri_core::BuiltinOp;
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let f64 = ctx.fp_sort(11, 53);
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        // FP->FP: widen a Float32 var to Float64.
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let widen = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 11, sb: 53 }), &[rne, x]).unwrap();
        let yf = ctx.declare_fun("y", &[], f64);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let eq1 = ctx.mk_eq(widen, y).unwrap();
        // const-Real: to_fp of numeral 1/3 into Float32.
        let real = ctx.real_sort();
        let third = ctx.mk_numeral(shinri_core::Rational::new(1i128.into(), 3i128.into()), real);
        let conv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, third]).unwrap();
        let zf = ctx.declare_fun("z", &[], f32);
        let z = ctx.mk_app(Op::Uninterpreted(zf), &[]).unwrap();
        let eq2 = ctx.mk_app(Op::Builtin(BuiltinOp::FpEq), &[conv, z]).unwrap();
        let lo = lower(&mut ctx, &[eq1, eq2]);
        assert!(lo.atom_lit.contains_key(&eq1), "core = over to_fp FP->FP must be surrogated");
        assert!(lo.atom_lit.contains_key(&eq2), "fp.eq over const-Real to_fp must be surrogated");
    }
}

#[cfg(test)]
mod blast_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

    #[test]
    fn blast_const_and_var_words_have_width_w() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        // a float constant (+zero) and a float variable
        let z = ctx.mk_fp_const(8, 24, Integer::zero());
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();

        let mut fb = FpBlaster::new();
        let zb = fb.blast_word(&ctx, z);
        let xb = fb.blast_word(&ctx, x);
        assert_eq!(zb.len(), 32, "Float32 word is W=eb+sb=32 bits");
        assert_eq!(xb.len(), 32);
        // +zero constant: every bit is the pinned-false constant (var 0, pos=false).
        for bit in &zb {
            assert_eq!(bit.var, 0, "constant bits use the pinned var 0");
            assert!(!bit.pos, "+zero bits are all false");
        }
        // the variable is exported for model extraction
        let vb = fb.exported_var_bits();
        assert!(vb.contains_key(&x));
        assert_eq!(vb[&x].len(), 32);
        assert!(!vb.contains_key(&z), "constants are not exported as variables");
    }

    #[test]
    fn blast_dispatch_relations_and_minmax_wired() {
        let mut ctx = Context::new();
        let one = ctx.mk_fp_const(8, 24, Integer::from(0x3F80_0000u64));
        let two = ctx.mk_fp_const(8, 24, Integer::from(0x4000_0000u64));
        let mut fb = FpBlaster::new();
        // Each relation atom must dispatch (no `unreachable!`):
        for rel in [BuiltinOp::FpLt, BuiltinOp::FpLeq, BuiltinOp::FpGt, BuiltinOp::FpGeq] {
            let a = ctx.mk_app(Op::Builtin(rel), &[one, two]).unwrap();
            let _lit = fb.blast_atom(&ctx, a); // must not panic
        }
        // min/max words must dispatch and yield a 32-bit word:
        let mn = ctx.mk_app(Op::Builtin(BuiltinOp::FpMin), &[one, two]).unwrap();
        let mx = ctx.mk_app(Op::Builtin(BuiltinOp::FpMax), &[one, two]).unwrap();
        assert_eq!(fb.blast_word(&ctx, mn).len(), 32);
        assert_eq!(fb.blast_word(&ctx, mx).len(), 32);
    }
}
