//! Unified BV+FP lowering driver: one Blaster, one shared cache, dispatched by
//! sort. See docs/superpowers/specs/2026-07-01-shinri-qffp-slice4a-bvfp-unification-design.md.

use rustc_hash::FxHashMap;
use shinri_bv::{blast_bv_atom, blast_bv_word, BitLit, Blaster, WordSink};
use shinri_core::{Context, Op, TermId, TermNode};

pub struct Lowerer {
    pub b: Blaster,
    cache: FxHashMap<TermId, Vec<BitLit>>,
    // Per-TermId cache of blasted RoundingMode one-hot selectors. Required
    // because `blast_fp_word` routes RM operands through `blast_rm`, which
    // calls `sink.rm_cache()`; the `WordSink::rm_cache` default is
    // `unreachable!` (it assumes pure-BV lowering with no RM operands). A
    // `Lowerer` blasts real FP ops (fp.add/sub/mul/div/sqrt/
    // roundToIntegral/fma/to_fp) that carry RM operands, so it must override
    // `rm_cache` with a real backing store rather than inherit the default.
    rm_cache: FxHashMap<TermId, [BitLit; 5]>,
}

impl Lowerer {
    pub fn new() -> Self {
        Lowerer { b: Blaster::new(), cache: FxHashMap::default(), rm_cache: FxHashMap::default() }
    }
    // atom() and var_bits_split() added in Step 3.
}

impl Default for Lowerer {
    fn default() -> Self {
        Self::new()
    }
}

impl WordSink for Lowerer {
    fn word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        if let Some(v) = self.cache.get(&t) {
            return v.clone();
        }
        let sort = ctx.sort_of(t);
        let bits = if ctx.bv_width(sort).is_some() {
            // BV-sorted node. (A BV-sorted FP op — fp.to_ubv/to_sbv — is a
            // crossing op fenced in 4a, so blast_bv_word's unreachable! arm is
            // not hit; 4b adds a crossing check before this dispatch.)
            blast_bv_word(self, ctx, t)
        } else if ctx.fp_widths(sort).is_some() {
            // FP-sorted node (incl. future to_fp-from-BV, fenced in 4a).
            crate::blast_fp_word(self, ctx, t)
        } else {
            unreachable!("Lowerer::word on non-BV/non-FP sort {sort:?}");
        };
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

impl Lowerer {
    /// Blast a Bool-sorted atom (BV or FP predicate / (dis)equality) to a literal.
    pub fn atom(&mut self, ctx: &Context, t: TermId) -> BitLit {
        // Dispatch by the sort of the atom's first operand.
        let first_operand_sort = match ctx.term_node(t) {
            TermNode::App { args, .. } => {
                let kids = ctx.children(*args);
                ctx.sort_of(kids[0])
            }
            _ => unreachable!("atom must be an application"),
        };
        if ctx.bv_width(first_operand_sort).is_some() {
            blast_bv_atom(self, ctx, t)
        } else {
            crate::blast_fp_atom(self, ctx, t)
        }
    }

    /// Split the shared cache's variable words by sort for model read-back.
    /// Returns (bv_var_bits, fp_var_bits). A variable term is a nullary
    /// `Op::Uninterpreted` app; its sort decides the map.
    pub fn var_bits_split(
        &self,
        ctx: &Context,
    ) -> (FxHashMap<TermId, Vec<BitLit>>, FxHashMap<TermId, Vec<BitLit>>) {
        let mut bv = FxHashMap::default();
        let mut fp = FxHashMap::default();
        for (&tid, bits) in self.cache.iter() {
            if let TermNode::App { op: Op::Uninterpreted(_), args, sort } = ctx.term_node(tid) {
                if !ctx.children(*args).is_empty() {
                    continue;
                }
                if ctx.bv_width(*sort).is_some() {
                    bv.insert(tid, bits.clone());
                } else if ctx.fp_widths(*sort).is_some() {
                    fp.insert(tid, bits.clone());
                }
            }
        }
        (bv, fp)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::BuiltinOp;

    #[test]
    fn mixed_bv_and_fp_atoms_share_one_cache_and_split_vars() {
        // A BV atom and an FP atom in ONE lowering pass. The solver fences such
        // mixed queries in 4a; this exercises the driver machinery directly.
        let mut ctx = Context::new();
        // BV side: (= x #x05) over an 8-bit var.
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let five = ctx.mk_bv_const(8, shinri_num::Integer::from(5u64));
        let bv_eq = ctx.mk_eq(x, five).unwrap();
        // FP side: (fp.isNaN y) over a Float32 var.
        let f32 = ctx.fp_sort(8, 24);
        let yf = ctx.declare_fun("y", &[], f32);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[y]).unwrap();

        let mut lw = Lowerer::new();
        let _l_bv = lw.atom(&ctx, bv_eq);
        let _l_fp = lw.atom(&ctx, isnan);

        let (bv_vars, fp_vars) = lw.var_bits_split(&ctx);
        assert!(bv_vars.contains_key(&x) && bv_vars[&x].len() == 8, "x is an 8-bit BV var");
        assert!(fp_vars.contains_key(&y) && fp_vars[&y].len() == 32, "y is a 32-bit FP var");
        assert!(!bv_vars.contains_key(&y) && !fp_vars.contains_key(&x), "no sort cross-contamination");
    }
}
