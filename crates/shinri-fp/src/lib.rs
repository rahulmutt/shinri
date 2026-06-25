//! shinri-fp: eager bit-blasting of QF_FP to CNF, reusing the shinri-bv Blaster
//! as a gate/clause factory. See
//! docs/superpowers/specs/2026-06-25-shinri-qffp-vertical-slice-design.md.

pub mod pack;
pub mod reference;
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
    /// Slice 1 handles FP constants and nullary FP variables; FP operator nodes
    /// (abs/neg) are added in Task 5 via `structural`.
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
            other => {
                // Task 5 extends this with abs/neg. Until then, unreachable for slice-1 words.
                let _ = other;
                unreachable!("blast_word: unsupported FP word node (slice 1)");
            }
        };
        self.cache.insert(t, result.clone());
        result
    }

    /// Bits cached for every FP *variable* term (for model extraction).
    pub fn exported_var_bits(&self) -> FxHashMap<TermId, Vec<BitLit>> {
        self.var_bits.clone()
    }
}

impl Default for FpBlaster {
    fn default() -> Self { Self::new() }
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
