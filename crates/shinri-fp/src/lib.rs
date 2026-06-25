//! shinri-fp: eager bit-blasting of QF_FP to CNF, reusing the shinri-bv Blaster
//! as a gate/clause factory. See
//! docs/superpowers/specs/2026-06-25-shinri-qffp-vertical-slice-design.md.

pub mod blast;
pub mod lzc;
pub mod model;
pub mod pack;
pub mod reference;
pub mod rm;
pub mod unpack;

use rustc_hash::FxHashMap;
use shinri_bv::{BitLit, Blaster};
use shinri_core::{ConstVal, Context, Op, TermId, TermNode};

/// FP-side blaster: wraps a `shinri_bv::Blaster` (used purely as a gate/clause
/// factory) with its own word cache and variable-bit map, since the Blaster's
/// internal cache is private to shinri-bv.
pub struct FpBlaster {
    pub b: Blaster,
    cache: FxHashMap<TermId, Vec<BitLit>>,
    var_bits: FxHashMap<TermId, Vec<BitLit>>,
}

impl FpBlaster {
    pub fn new() -> Self {
        FpBlaster { b: Blaster::new(), cache: FxHashMap::default(), var_bits: FxHashMap::default() }
    }

    /// Blast an FP-sorted term to its W=eb+sb bit word (LSB→MSB), memoized.
    /// Slice 1 handles FP constants, nullary FP variables, and FpAbs/FpNeg operator nodes.
    pub fn blast_word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        if let Some(v) = self.cache.get(&t) {
            return v.clone();
        }
        let result = match ctx.term_node(t).clone() {
            TermNode::Const { val: ConstVal::Float(_), .. } => {
                let (eb, sb, bits) = ctx.fp_const_value(t).expect("FP const");
                let w = eb + sb;
                let two = shinri_num::Integer::from(2u64);
                let mut remaining = bits.clone();
                (0..w).map(|_| {
                    let (q, r) = remaining.div_rem(&two);
                    remaining = q;
                    if r.is_zero() { self.b.zero() } else { self.b.one() }
                }).collect()
            }
            TermNode::App { op: Op::Uninterpreted(_), args, sort } => {
                debug_assert!(ctx.children(args).is_empty(), "non-nullary FP fn out of scope");
                let (eb, sb) = ctx.fp_widths(sort).expect("FP-sorted variable");
                let bits: Vec<BitLit> = (0..(eb + sb)).map(|_| self.b.fresh()).collect();
                self.var_bits.insert(t, bits.clone());
                bits
            }
            TermNode::App { op: Op::Builtin(op), args, sort } => {
                use shinri_core::BuiltinOp::*;
                let (eb, sb) = ctx.fp_widths(sort).expect("FP-sorted op result");
                let kids = ctx.children(args).to_vec();
                match op {
                    FpAbs => {
                        let w = self.blast_word(ctx, kids[0]);
                        crate::blast::structural::abs(&mut self.b, &w, eb, sb)
                    }
                    FpNeg => {
                        let w = self.blast_word(ctx, kids[0]);
                        crate::blast::structural::neg(&mut self.b, &w, eb, sb)
                    }
                    other => unreachable!("blast_word: FP op {other:?} is out of slice-1 scope"),
                }
            }
            other => unreachable!("blast_word: unsupported FP word node {other:?} (slice 1)"),
        };
        self.cache.insert(t, result.clone());
        result
    }

    /// Blast a Bool-sorted FP atom to a single BitLit.
    pub fn blast_atom(&mut self, ctx: &Context, t: TermId) -> BitLit {
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
                let x = self.blast_word(ctx, kids[0]);
                let y = self.blast_word(ctx, kids[1]);
                crate::blast::compare::core_eq(&mut self.b, &x, &y, eb, sb)
            }
            Op::Builtin(Distinct) => {
                let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
                let x = self.blast_word(ctx, kids[0]);
                let y = self.blast_word(ctx, kids[1]);
                let eq = crate::blast::compare::core_eq(&mut self.b, &x, &y, eb, sb);
                self.b.not1(eq)
            }
            Op::Builtin(FpEq) => {
                let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
                let x = self.blast_word(ctx, kids[0]);
                let y = self.blast_word(ctx, kids[1]);
                crate::blast::compare::fp_eq(&mut self.b, &x, &y, eb, sb)
            }
            Op::Builtin(classify @ (FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite
                                    | FpIsNaN | FpIsNegative | FpIsPositive)) => {
                let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operand");
                let w = self.blast_word(ctx, kids[0]);
                let u = crate::unpack::unpack(&mut self.b, &w, eb, sb);
                use crate::blast::classify as c;
                match classify {
                    FpIsNormal => c::is_normal(&mut self.b, &u),
                    FpIsSubnormal => c::is_subnormal(&mut self.b, &u),
                    FpIsZero => c::is_zero(&mut self.b, &u),
                    FpIsInfinite => c::is_inf(&mut self.b, &u),
                    FpIsNaN => c::is_nan(&mut self.b, &u),
                    FpIsNegative => c::is_negative(&mut self.b, &u),
                    FpIsPositive => c::is_positive(&mut self.b, &u),
                    _ => unreachable!(),
                }
            }
            other => unreachable!("blast_atom: FP atom {other:?} out of slice-1 scope"),
        }
    }

    /// Bits cached for every FP *variable* term (for model extraction).
    pub fn exported_var_bits(&self) -> FxHashMap<TermId, Vec<BitLit>> {
        self.var_bits.clone()
    }
}

impl Default for FpBlaster {
    fn default() -> Self { Self::new() }
}

/// Blast all `fp_atoms` via one FpBlaster and return a `shinri_bv::Lowered`
/// (reused so the solver's `replay_bv_cnf` applies unchanged). `atom_lit` is
/// keyed by the ORIGINAL atom TermId.
pub fn lower(ctx: &mut Context, fp_atoms: &[TermId]) -> shinri_bv::Lowered {
    let mut fb = FpBlaster::new();
    let mut atom_lit: FxHashMap<TermId, BitLit> = FxHashMap::default();
    for &atom in fp_atoms {
        let lit = fb.blast_atom(ctx, atom);
        atom_lit.insert(atom, lit);
    }
    let var_bits = fb.exported_var_bits();
    shinri_bv::Lowered { cnf: fb.b.finish(), atom_lit, var_bits }
}

#[cfg(test)]
mod lower_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

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
}

#[cfg(test)]
mod blast_tests {
    use super::*;
    use shinri_core::{Context, Op};
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
}
