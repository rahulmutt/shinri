//! Unified BV+FP lowering driver: one Blaster, one shared cache, dispatched by
//! sort. See docs/superpowers/specs/2026-07-01-shinri-qffp-slice4a-bvfp-unification-design.md.

use rustc_hash::FxHashMap;
use shinri_bv::{blast_bv_atom, blast_bv_word, BitLit, Blaster, FpToBvApp, UfApp, WordSink};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

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
    // FP→BV application registry for unspecified-value congruence (slice 4e).
    fp2bv_apps: Vec<FpToBvApp>,
    // Uninterpreted-application registry for Ackermann congruence (slice 44).
    // A real store, not a defaulted `unreachable!`: the unified path lowers
    // BV-sorted uninterpreted applications through `blast_bv_word`.
    uf_apps: Vec<UfApp>,
}

impl Lowerer {
    pub fn new() -> Self {
        Lowerer {
            b: Blaster::new(),
            cache: FxHashMap::default(),
            rm_cache: FxHashMap::default(),
            fp2bv_apps: Vec::new(),
            uf_apps: Vec::new(),
        }
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
            // BV-sorted node. fp.to_ubv/to_sbv are the one BV-sorted FP-op
            // family (admitted in 4e) — route them to the FP dispatch; every
            // other BV-sorted node goes to the BV blaster. (Still-crossing ops
            // are fenced before lowering, so blast_bv_word's unreachable! arm
            // stays an internal invariant.)
            if matches!(
                ctx.term_node(t),
                TermNode::App {
                    op: Op::Builtin(BuiltinOp::FpToUbv(_) | BuiltinOp::FpToSbv(_)),
                    ..
                }
            ) {
                crate::blast_fp_to_bv(self, ctx, t)
            } else {
                blast_bv_word(self, ctx, t)
            }
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
    fn fp2bv_apps(&mut self) -> &mut Vec<FpToBvApp> {
        &mut self.fp2bv_apps
    }
    fn uf_apps(&mut self) -> &mut Vec<UfApp> {
        &mut self.uf_apps
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
    ) -> (
        FxHashMap<TermId, Vec<BitLit>>,
        FxHashMap<TermId, Vec<BitLit>>,
    ) {
        let mut bv = FxHashMap::default();
        let mut fp = FxHashMap::default();
        for (&tid, bits) in self.cache.iter() {
            if let TermNode::App {
                op: Op::Uninterpreted(_),
                args,
                sort,
            } = ctx.term_node(tid)
            {
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

    /// RM-variable selectors: nullary uninterpreted RoundingMode-sorted terms
    /// → their 5-lit one-hot selectors [Rne, Rna, Rtp, Rtn, Rtz]. The RM
    /// mirror of `var_bits_split` (rm_cache is a separate store — slice 6).
    pub fn rm_var_sels(&self, ctx: &Context) -> FxHashMap<TermId, [BitLit; 5]> {
        let mut out = FxHashMap::default();
        for (&tid, sel) in self.rm_cache.iter() {
            if let TermNode::App {
                op: Op::Uninterpreted(_),
                args,
                ..
            } = ctx.term_node(tid)
            {
                if ctx.children(*args).is_empty() {
                    out.insert(tid, *sel);
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Op, RoundingMode};

    fn solve_with_units(lw: Lowerer, units: &[(BitLit, bool)]) -> shinri_sat::SolveResult {
        use shinri_sat::{Lit, NoProof, NoTheory, Solver, SolverConfig, Var, Vmtf};
        let cnf = lw.b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars {
            s.new_var();
        }
        for c in &cnf.clauses {
            let ls: Vec<Lit> = c
                .iter()
                .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
                .collect();
            s.add_clause(&ls);
        }
        for &(bl, want) in units {
            s.add_clause(&[Lit::new(Var::new(bl.var), bl.pos == want)]);
        }
        s.solve()
    }

    #[test]
    fn fp_to_bv_congruence_equal_args_force_equal_results() {
        // Spec §2 probe-2 shape: x = y (SMT value equality) ∧ isNaN x ∧
        // to_ubv(RNE,x) ≠ to_ubv(RNE,y) must be UNSAT — the two applications are
        // distinct TermIds, so only the emitted congruence clauses can close it.
        let mut ctx = Context::new();
        let f16 = ctx.fp_sort(5, 11);
        let mk = |ctx: &mut Context, n: &str, s| {
            let f = ctx.declare_fun(n, &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x", f16);
        let y = mk(&mut ctx, "y", f16);
        let rne = ctx.mk_rm_const(RoundingMode::Rne);
        let ux = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, x])
            .unwrap();
        let uy = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, y])
            .unwrap();
        let eq_xy = ctx.mk_eq(x, y).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        let eq_uv = ctx.mk_eq(ux, uy).unwrap();
        let mut lw = Lowerer::new();
        let l_eq = lw.atom(&ctx, eq_xy);
        let l_nan = lw.atom(&ctx, isnan);
        let l_uv = lw.atom(&ctx, eq_uv);
        let r = solve_with_units(lw, &[(l_eq, true), (l_nan, true), (l_uv, false)]);
        assert!(
            matches!(r, shinri_sat::SolveResult::Unsat { .. }),
            "congruence must bind equal-arg applications"
        );
    }

    #[test]
    fn fp_to_bv_unspecified_free_across_modes_and_faces() {
        // Probe-4 shape: same NaN operand, DIFFERENT rounding modes → results may
        // differ (SAT). Also different faces (ubv vs sbv) are independent functions.
        let mut ctx = Context::new();
        let f16 = ctx.fp_sort(5, 11);
        let f = ctx.declare_fun("x", &[], f16);
        let x = ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap();
        let rne = ctx.mk_rm_const(RoundingMode::Rne);
        let rtz = ctx.mk_rm_const(RoundingMode::Rtz);
        let u1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, x])
            .unwrap();
        let u2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rtz, x])
            .unwrap();
        let s1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::FpToSbv(8)), &[rne, x])
            .unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        let ne_modes = ctx.mk_eq(u1, u2).unwrap();
        let ne_faces = ctx.mk_eq(u1, s1).unwrap();
        let mut lw = Lowerer::new();
        let l_nan = lw.atom(&ctx, isnan);
        let l_m = lw.atom(&ctx, ne_modes);
        let l_f = lw.atom(&ctx, ne_faces);
        let r = solve_with_units(lw, &[(l_nan, true), (l_m, false), (l_f, false)]);
        assert!(
            matches!(r, shinri_sat::SolveResult::Sat),
            "different modes / different faces are unconstrained relative to each other"
        );
    }

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
        assert!(
            bv_vars.contains_key(&x) && bv_vars[&x].len() == 8,
            "x is an 8-bit BV var"
        );
        assert!(
            fp_vars.contains_key(&y) && fp_vars[&y].len() == 32,
            "y is a 32-bit FP var"
        );
        assert!(
            !bv_vars.contains_key(&y) && !fp_vars.contains_key(&x),
            "no sort cross-contamination"
        );
    }
}
