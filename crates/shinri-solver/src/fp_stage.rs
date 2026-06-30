//! FP lowering stage: detect QF_FP queries, collect FP atoms, enforce the
//! mixed-theory fence. Mirrors bv_stage.rs. FP gets its own Blaster (QF_BVFP
//! unification is a later plan), so BV atoms count as non-FP and trigger the fence.

use shinri_core::{BuiltinOp, ConstVal, Context, Op, SortNode, TermId, TermNode};

fn is_fp_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::Float(_, _))
}

/// True if `op` is any FP builtin (word op, predicate, classification, or conversion).
fn is_fp_op(op: &Op) -> bool {
    use BuiltinOp::*;
    matches!(op, Op::Builtin(
        FpAbs | FpNeg | FpAdd | FpSub | FpMul | FpDiv | FpFma | FpSqrt | FpRem
        | FpRoundToIntegral | FpMin | FpMax | FpLeq | FpLt | FpGeq | FpGt | FpEq
        | FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite | FpIsNaN
        | FpIsNegative | FpIsPositive | FpFromBits
        | ToFp { .. } | ToFpUnsigned { .. } | FpToUbv(_) | FpToSbv(_) | FpToReal
    ))
}

/// FP PREDICATES (Bool-sorted FP atoms): comparisons + classifications.
fn is_fp_predicate(op: &Op) -> bool {
    use BuiltinOp::*;
    matches!(op, Op::Builtin(
        FpLeq | FpLt | FpGeq | FpGt | FpEq
        | FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite | FpIsNaN
        | FpIsNegative | FpIsPositive
    ))
}

/// True if any subterm has a Float sort or an FP builtin op.
pub fn solver_uses_fp(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return false; }
        if is_fp_sorted(ctx, t) { return true; }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                if is_fp_op(op) { return true; }
                ctx.children(*args).to_vec().into_iter().any(|c| walk(ctx, c, seen))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a, &mut seen))
}

/// Collect Bool-sorted FP atoms: FP predicates, plus Eq/Distinct over Float operands.
/// SOUNDNESS-CRITICAL: FP (dis)equalities ARE included (else they route to EUF).
pub fn collect_fp_atoms(ctx: &Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::new();
    let mut in_set: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, out: &mut Vec<TermId>,
            in_set: &mut rustc_hash::FxHashSet<TermId>,
            visited: &mut rustc_hash::FxHashSet<TermId>) {
        if !visited.insert(t) { return; }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            let is_atom = match op {
                _ if is_fp_predicate(op) => true,
                Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) =>
                    kids.iter().any(|&k| is_fp_sorted(ctx, k)),
                _ => false,
            };
            if is_atom && in_set.insert(t) { out.push(t); return; }
            for k in kids { walk(ctx, k, out, in_set, visited); }
        }
    }
    for &a in assertions { walk(ctx, a, &mut out, &mut in_set, &mut visited); }
    out
}

/// Mixed-theory fence (conservative). True if any Bool-sorted atom outside the
/// FP set is not pure Boolean structure — including BV atoms (BVFP waits for
/// Plan 4) and arith/EUF/array atoms. When true, the caller returns Unknown.
pub fn has_non_fp_theory_atom(ctx: &Context, assertions: &[TermId], fp_atoms: &[TermId]) -> bool {
    let fp_set: rustc_hash::FxHashSet<TermId> = fp_atoms.iter().copied().collect();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, fp_set: &rustc_hash::FxHashSet<TermId>,
            visited: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if fp_set.contains(&t) { return false; }
        if !visited.insert(t) { return false; }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids: Vec<TermId> = ctx.children(*args).to_vec();
                let is_bool_structure = matches!(op, Op::Builtin(
                    BuiltinOp::Not | BuiltinOp::And | BuiltinOp::Or
                    | BuiltinOp::Implies | BuiltinOp::Xor | BuiltinOp::Ite));
                let is_bool_eq = matches!(op, Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct))
                    && kids.first().is_some_and(|&k| ctx.sort_of(k) == ctx.bool_sort());
                if is_bool_structure || is_bool_eq {
                    return kids.iter().any(|&k| walk(ctx, k, fp_set, visited));
                }
                if ctx.sort_of(t) == ctx.bool_sort() {
                    // Bool-sorted, not an FP atom, not Boolean structure → fence.
                    return true;
                }
                kids.iter().any(|&k| walk(ctx, k, fp_set, visited))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a, &fp_set, &mut visited))
}

/// Positively-enumerated check: is an FP-sorted `word` term one that
/// `shinri_fp::FpBlaster::blast_word` can handle in slice 1 (FpAbs/FpNeg),
/// slice 2a (FpAdd/FpSub), slice 2b (FpMul), slice 2c (FpDiv), slice 2c′ (FpSqrt),
/// slice 2e (FpRoundToIntegral/FpMin/FpMax), or slice 2f (FpFma)?
///
/// Supported: FP constants, nullary FP variables, FpAbs/FpNeg applied
/// (recursively) to supported words, FpAdd/FpSub/FpMul/FpDiv where the RM operand is a
/// RoundingMode term (literal const or nullary RM variable) and both FP operands
/// are recursively supported, FpSqrt where the RM operand is a RoundingMode
/// term and the single FP operand is recursively supported, FpRoundToIntegral with
/// RM and FP operand both recursively supported, FpMin/FpMax with both FP operands
/// recursively supported, and FpFma with RM and all three FP operands recursively
/// supported. EVERYTHING else is NOT supported (any unknown/future FP op defaults to
/// unsupported). This ensures that adding a new FP op to the core does not silently
/// route through blast_word and panic.
fn is_supported_fp_word(ctx: &Context, t: TermId) -> bool {
    match ctx.term_node(t) {
        // FP constant → supported.
        TermNode::Const { val: ConstVal::Float(_), .. } => true,
        // Nullary uninterpreted symbol (FP variable) → supported.
        TermNode::App { op: Op::Uninterpreted(_), args, .. } => {
            ctx.children(*args).is_empty()
        }
        // FpAbs / FpNeg: supported if the single child is supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpAbs | BuiltinOp::FpNeg), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 1 && is_supported_fp_word(ctx, kids[0])
        }
        // FpAdd / FpSub / FpMul / FpDiv: (RM, F, F). RM operand must be a RoundingMode term
        // (literal const or nullary RM variable); both FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpAdd | BuiltinOp::FpSub | BuiltinOp::FpMul | BuiltinOp::FpDiv), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 3
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
                && is_supported_fp_word(ctx, kids[2])
        }
        // FpSqrt / FpRoundToIntegral: (RM, F). RM operand must be a RoundingMode
        // term; FP operand supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpSqrt | BuiltinOp::FpRoundToIntegral), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
        // fp.min / fp.max: (F, F) -> F. No RM operand; both FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpMin | BuiltinOp::FpMax), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_supported_fp_word(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
        // FpFma: (RM, F, F, F) -> F. RM operand must be a RoundingMode term;
        // all three FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpFma), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 4
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
                && is_supported_fp_word(ctx, kids[2])
                && is_supported_fp_word(ctx, kids[3])
        }
        // Anything else (FpRem, Ite over FP, non-nullary UF, etc.)
        // is not in scope for slice 1, 2a, 2b, 2c, 2c′, 2e, or 2f.
        _ => false,
    }
}

/// A RoundingMode operand we can blast: a RoundingMode literal constant, or a
/// nullary uninterpreted symbol of RoundingMode sort.
fn is_rounding_mode_term(ctx: &Context, t: TermId) -> bool {
    if !matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::RoundingMode) {
        return false;
    }
    match ctx.term_node(t) {
        TermNode::Const { val: ConstVal::Rm(_), .. } => true,
        TermNode::App { op: Op::Uninterpreted(_), args, .. } => ctx.children(*args).is_empty(),
        _ => false,
    }
}

/// Soundness fence: true iff EVERY collected FP atom is fully supported by the
/// slice-1 blaster. An atom is supported iff:
/// - Its op is one of the 7 classifications, FpEq, or core Eq/Distinct with
///   Float-sorted operands, AND
/// - Every FP-sorted operand subtree is a `is_supported_fp_word`.
///
/// Call this BEFORE `shinri_fp::lower` so that `blast_atom`/`blast_word`'s
/// `unreachable!` arms remain true internal invariants rather than user-triggered
/// panics. Returns false if ANY atom is out of scope.
pub fn fp_atoms_fully_supported(ctx: &Context, fp_atoms: &[TermId]) -> bool {
    fp_atoms.iter().all(|&atom| fp_atom_is_supported(ctx, atom))
}

fn fp_atom_is_supported(ctx: &Context, atom: TermId) -> bool {
    use BuiltinOp::*;
    let TermNode::App { op, args, .. } = ctx.term_node(atom) else {
        return false;
    };
    let kids = ctx.children(*args).to_vec();
    match op {
        // 7 classification predicates: single FP-sorted operand required.
        Op::Builtin(FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite
                    | FpIsNaN | FpIsNegative | FpIsPositive) => {
            kids.len() == 1 && is_supported_fp_word(ctx, kids[0])
        }
        // fp.eq: two FP-sorted operands.
        Op::Builtin(FpEq) => {
            kids.len() == 2
                && is_supported_fp_word(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
        // core = or distinct over Float-sorted operands.
        Op::Builtin(Eq | Distinct) => {
            kids.iter().all(|&k| {
                matches!(ctx.sort_node(ctx.sort_of(k)), SortNode::Float(_, _))
                    && is_supported_fp_word(ctx, k)
            })
        }
        // fp.lt / fp.leq / fp.gt / fp.geq: two supported FP operands.
        Op::Builtin(FpLt | FpLeq | FpGt | FpGeq) => {
            kids.len() == 2
                && is_supported_fp_word(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
        // Any other op is not handled.
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Op;
    use shinri_num::Integer;

    fn fp_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.fp_sort(8, 24);
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn detects_fp_and_collects_eq_and_predicate() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        let pz = ctx.mk_fp_const(8, 24, Integer::zero());
        let eq = ctx.mk_eq(x, pz).unwrap();
        let assertions = vec![isnan, eq];
        assert!(solver_uses_fp(&ctx, &assertions));
        let atoms = collect_fp_atoms(&ctx, &assertions);
        assert!(atoms.contains(&isnan), "FP predicate collected");
        assert!(atoms.contains(&eq), "FP equality collected (soundness)");
        assert_eq!(atoms.len(), 2);
        assert!(!has_non_fp_theory_atom(&ctx, &assertions, &atoms));
    }

    #[test]
    fn fp_mixed_with_bv_is_fenced() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        // a BV atom alongside FP
        let bvs = ctx.bv_sort(8);
        let bf = ctx.declare_fun("b", &[], bvs);
        let bvar = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let ult = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[bvar, one]).unwrap();
        let assertions = vec![isnan, ult];
        let atoms = collect_fp_atoms(&ctx, &assertions);
        assert!(atoms.contains(&isnan));
        assert!(has_non_fp_theory_atom(&ctx, &assertions, &atoms),
                "BV atom alongside FP must trigger the fence");
    }

    #[test]
    fn fp_add_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rne, x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[add]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.add inside a predicate is supported");
    }

    #[test]
    fn fp_add_with_symbolic_rm_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rms = ctx.rm_sort();
        let rmf = ctx.declare_fun("rm", &[], rms);
        let rm = ctx.mk_app(Op::Uninterpreted(rmf), &[]).unwrap();
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rm, x, y]).unwrap();
        let z = fp_var(&mut ctx, "z");
        let eq = ctx.mk_eq(add, z).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[eq]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "symbolic RM operand is supported");
    }

    #[test]
    fn fp_mul_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let mul = ctx.mk_app(Op::Builtin(BuiltinOp::FpMul), &[rne, x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[mul]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.mul is in scope as of slice 2b");
    }

    #[test]
    fn fp_div_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let div = ctx.mk_app(Op::Builtin(BuiltinOp::FpDiv), &[rne, x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[div]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.div is in scope as of slice 2c");
    }

    #[test]
    fn fp_sqrt_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let sqrt = ctx.mk_app(Op::Builtin(BuiltinOp::FpSqrt), &[rne, x]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[sqrt]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.sqrt is in scope as of slice 2c'");
    }

    #[test]
    fn fp_roundtointegral_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let rti = ctx.mk_app(Op::Builtin(BuiltinOp::FpRoundToIntegral), &[rne, x]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[rti]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.roundToIntegral is in scope as of slice 2e");
        // Malformed (missing RM operand) must NOT be admitted.
        let bad = ctx.mk_app(Op::Builtin(BuiltinOp::FpRoundToIntegral), &[x]);
        if let Ok(bad) = bad {
            assert!(!super::is_supported_fp_word(&ctx, bad), "arity-1 roundToIntegral rejected");
        }
    }

    #[test]
    fn fp_fma_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let z = fp_var(&mut ctx, "z");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let fma = ctx.mk_app(Op::Builtin(BuiltinOp::FpFma), &[rne, x, y, z]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[fma]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.fma is in scope as of slice 2f");
        // Malformed (missing the third FP operand) must NOT be admitted.
        let bad = ctx.mk_app(Op::Builtin(BuiltinOp::FpFma), &[rne, x, y]);
        if let Ok(bad) = bad {
            assert!(!super::is_supported_fp_word(&ctx, bad), "arity-3 fp.fma rejected");
        }
    }

    #[test]
    fn fence_admits_relations_and_minmax() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        // relation atom
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::FpLt), &[x, y]).unwrap();
        assert!(fp_atoms_fully_supported(&ctx, &[lt]), "fp.lt admitted");
        // min/max nested inside fp.eq (word support)
        let mn = ctx.mk_app(Op::Builtin(BuiltinOp::FpMin), &[x, y]).unwrap();
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::FpEq), &[mn, x]).unwrap();
        assert!(fp_atoms_fully_supported(&ctx, &[eq]), "fp.min inside fp.eq admitted");
    }
}
