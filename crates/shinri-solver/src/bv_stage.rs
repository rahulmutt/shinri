//! BV lowering stage: detect QF_BV queries, collect BV atoms, enforce the
//! mixed-theory fence, and carry the CNF→SAT surrogate maps.
//!
//! ## Soundness contract
//! The theory's `classify_equality` routes any `(= a b)` whose operand sort is
//! neither Int nor Real to `Owner::Euf`, where BV operators are treated as
//! UNINTERPRETED functions. So `(= (bvadd x #x01) x)` would be answered SAT by
//! EUF when the true BV answer is UNSAT. Therefore EVERY BV atom — including BV
//! (dis)equalities — MUST be surrogated (intercepted by the Encoder and mapped
//! to a pre-blasted SAT literal) so it never reaches `register_atom`/`classify`.
//! `collect_bv_atoms` deliberately includes Eq/Distinct over BV operands.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Lit, Op, SortNode, TermId, TermNode, Var};

/// Surrogate maps produced by lowering BV atoms to CNF and replaying that CNF
/// into the SAT solver. The Encoder consults `atom_to_lit` so a BV atom returns
/// its pre-blasted representative literal instead of being registered as a
/// theory atom. `var_bits` is stashed for model extraction (Task 18).
pub struct BvSurrogates {
    pub atom_to_lit: FxHashMap<TermId, Lit>,
    pub var_bits: FxHashMap<TermId, Vec<Var>>,
}

/// True if `t`'s sort is a `(_ BitVec n)`.
fn is_bv_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::BitVec(_))
}

/// True if `op` is a bitvector builtin (any BV operator, predicate or not).
fn is_bv_op(op: &Op) -> bool {
    matches!(
        op,
        Op::Builtin(
            BuiltinOp::BvNot
                | BuiltinOp::BvAnd
                | BuiltinOp::BvOr
                | BuiltinOp::BvXor
                | BuiltinOp::BvNand
                | BuiltinOp::BvNor
                | BuiltinOp::BvXnor
                | BuiltinOp::BvNeg
                | BuiltinOp::BvAdd
                | BuiltinOp::BvSub
                | BuiltinOp::BvMul
                | BuiltinOp::BvUdiv
                | BuiltinOp::BvUrem
                | BuiltinOp::BvSdiv
                | BuiltinOp::BvSrem
                | BuiltinOp::BvSmod
                | BuiltinOp::BvShl
                | BuiltinOp::BvLshr
                | BuiltinOp::BvAshr
                | BuiltinOp::BvUlt
                | BuiltinOp::BvUle
                | BuiltinOp::BvUgt
                | BuiltinOp::BvUge
                | BuiltinOp::BvSlt
                | BuiltinOp::BvSle
                | BuiltinOp::BvSgt
                | BuiltinOp::BvSge
                | BuiltinOp::BvConcat
                | BuiltinOp::BvExtract { .. }
                | BuiltinOp::BvZeroExtend(_)
                | BuiltinOp::BvSignExtend(_)
                | BuiltinOp::BvRotateLeft(_)
                | BuiltinOp::BvRotateRight(_)
                | BuiltinOp::BvRepeat(_)
        )
    )
}

/// True if `op` is a bitvector PREDICATE (Bool-sorted result).
fn is_bv_predicate(op: &Op) -> bool {
    matches!(
        op,
        Op::Builtin(
            BuiltinOp::BvUlt
                | BuiltinOp::BvUle
                | BuiltinOp::BvUgt
                | BuiltinOp::BvUge
                | BuiltinOp::BvSlt
                | BuiltinOp::BvSle
                | BuiltinOp::BvSgt
                | BuiltinOp::BvSge
        )
    )
}

/// True if any subterm of any assertion has a BitVec sort or a BV builtin op.
pub fn solver_uses_bv(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(
        ctx: &Context,
        t: TermId,
        seen: &mut rustc_hash::FxHashSet<TermId>,
    ) -> bool {
        if !seen.insert(t) {
            return false;
        }
        if is_bv_sorted(ctx, t) {
            return true;
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                if is_bv_op(op) {
                    return true;
                }
                ctx.children(*args)
                    .to_vec()
                    .into_iter()
                    .any(|c| walk(ctx, c, seen))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a, &mut seen))
}

/// Collect all Bool-sorted BV atoms: subterms whose top op is a BV predicate, OR
/// an Eq/Distinct whose operands are BV-sorted.
///
/// SOUNDNESS-CRITICAL: BV (dis)equalities ARE included (see module doc).
pub fn collect_bv_atoms(ctx: &Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::new();
    let mut in_set: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(
        ctx: &Context,
        t: TermId,
        out: &mut Vec<TermId>,
        in_set: &mut rustc_hash::FxHashSet<TermId>,
        visited: &mut rustc_hash::FxHashSet<TermId>,
    ) {
        if !visited.insert(t) {
            return;
        }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            let is_atom = match op {
                _ if is_bv_predicate(op) => true,
                Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) => {
                    kids.iter().any(|&k| is_bv_sorted(ctx, k))
                }
                _ => false,
            };
            if is_atom && in_set.insert(t) {
                out.push(t);
                // A BV atom is a leaf for theory purposes: do NOT descend into its
                // BV operands looking for more atoms (they are not Bool-sorted
                // atoms anyway). Descending is harmless but unnecessary.
                return;
            }
            for k in kids {
                walk(ctx, k, out, in_set, visited);
            }
        }
    }
    for &a in assertions {
        walk(ctx, a, &mut out, &mut in_set, &mut visited);
    }
    out
}

/// Mixed-theory fence (SOUNDNESS-CRITICAL, conservative).
///
/// Given a BV query, returns true if it ALSO contains any NON-BV theory atom —
/// i.e. an atom (Eq/Distinct/arith-relation/uninterpreted-predicate/array op)
/// that is NOT one of the collected BV atoms and is not pure Boolean structure.
/// Such atoms would route to EUF/Arith/Arrays, which cannot be combined with the
/// eager BV bit-blaster here. When true, the caller returns Unknown.
///
/// Conservative bias: any non-Boolean-structure atom outside the BV set that
/// `classify` recognizes as a theory atom (EUF/Arith/Arrays/Shared) — OR that
/// `classify` refuses (Unsupported) — triggers the fence. Only pure Boolean
/// connectives over BV atoms pass.
pub fn has_non_bv_theory_atom(
    ctx: &Context,
    assertions: &[TermId],
    bv_atoms: &[TermId],
) -> bool {
    let bv_set: rustc_hash::FxHashSet<TermId> = bv_atoms.iter().copied().collect();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(
        ctx: &Context,
        t: TermId,
        bv_set: &rustc_hash::FxHashSet<TermId>,
        visited: &mut rustc_hash::FxHashSet<TermId>,
    ) -> bool {
        if bv_set.contains(&t) {
            // A BV atom is surrogated and is a leaf — do not descend.
            return false;
        }
        if !visited.insert(t) {
            return false;
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids: Vec<TermId> = ctx.children(*args).to_vec();
                // Pure Boolean structure: recurse into children, not an atom itself.
                let is_bool_structure = matches!(
                    op,
                    Op::Builtin(
                        BuiltinOp::Not
                            | BuiltinOp::And
                            | BuiltinOp::Or
                            | BuiltinOp::Implies
                            | BuiltinOp::Xor
                            | BuiltinOp::Ite
                    )
                );
                // Bool-sorted Eq/Distinct over Bool operands is also Boolean
                // structure (iff/xor), handled by the SAT skeleton.
                let is_bool_eq = matches!(
                    op,
                    Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct)
                ) && kids
                    .first()
                    .is_some_and(|&k| ctx.sort_of(k) == ctx.bool_sort());
                if is_bool_structure || is_bool_eq {
                    return kids.iter().any(|&k| walk(ctx, k, bv_set, visited));
                }
                // Any other App node that is Bool-sorted is a candidate atom.
                // (Non-Bool subterms — e.g. arith terms inside a relation — are
                // reached only as operands; we only fence on Bool-sorted atoms,
                // and arith terms are caught via their enclosing relation.)
                if ctx.sort_of(t) == ctx.bool_sort() {
                    // It is not a BV atom (checked above) and not Boolean
                    // structure: a non-BV theory atom. Conservative → fence.
                    // (classify may accept it as EUF/Arith/Arrays or refuse it;
                    // either way it must not coexist with the BV path.)
                    let _ = shinri_theory::atom::classify(ctx, t);
                    return true;
                }
                // Non-Bool App (a term, e.g. arith subexpression): descend so we
                // still find any embedded Bool atoms, but it is not itself one.
                kids.iter().any(|&k| walk(ctx, k, bv_set, visited))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions
        .iter()
        .any(|&a| walk(ctx, a, &bv_set, &mut visited))
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Op;
    use shinri_num::Integer;

    fn bv_var(ctx: &mut Context, name: &str, w: u32) -> TermId {
        let s = ctx.bv_sort(w);
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn detects_bv_and_collects_eq_and_predicate() {
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let five = ctx.mk_bv_const(8, Integer::from(5u64));
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, one]).unwrap();
        let eq = ctx.mk_eq(add, one).unwrap(); // BV equality
        let ult = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[x, five]).unwrap();
        let assertions = vec![eq, ult];
        assert!(solver_uses_bv(&ctx, &assertions));
        let atoms = collect_bv_atoms(&ctx, &assertions);
        // Both the BV equality and the BV predicate must be collected.
        assert!(atoms.contains(&eq), "BV equality must be collected (soundness)");
        assert!(atoms.contains(&ult), "BV predicate must be collected");
        assert_eq!(atoms.len(), 2);
        // No non-BV theory atom present.
        assert!(!has_non_bv_theory_atom(&ctx, &assertions, &atoms));
    }

    #[test]
    fn mixed_with_real_atom_is_fenced() {
        let mut ctx = Context::new();
        let x = bv_var(&mut ctx, "x", 8);
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let eq = ctx.mk_eq(x, one).unwrap();
        let real = ctx.real_sort();
        let yf = ctx.declare_fun("y", &[], real);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let zero = ctx.mk_numeral(shinri_core::Rational::zero(), real);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[y, zero]).unwrap();
        let assertions = vec![eq, gt];
        let atoms = collect_bv_atoms(&ctx, &assertions);
        assert!(atoms.contains(&eq));
        assert!(
            has_non_bv_theory_atom(&ctx, &assertions, &atoms),
            "Real Gt atom must trigger the mixed fence"
        );
    }
}
