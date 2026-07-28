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
    /// First SAT `Var` index of this CNF's contiguous var block (slice 6:
    /// lets callers remap other blaster-namespace `BitLit`s, e.g. RM
    /// selectors, to SAT `Lit`s without re-deriving the block start).
    pub base: u32,
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
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
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
pub fn has_non_bv_theory_atom(ctx: &Context, assertions: &[TermId], bv_atoms: &[TermId]) -> bool {
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
                let is_bool_eq = matches!(op, Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct))
                    && kids
                        .first()
                        .is_some_and(|&k| ctx.sort_of(k) == ctx.bool_sort());
                if is_bool_structure || is_bool_eq {
                    return kids.iter().any(|&k| walk(ctx, k, bv_set, visited));
                }
                // A bare declared Bool constant (0-ary uninterpreted symbol,
                // Bool-sorted — e.g. a `declare-const c Bool` used directly or
                // as an `ite`/`and` condition) needs NO theory reasoning: a
                // nullary symbol has no arguments for congruence to act on, so
                // it is Tseitin-encoded as a plain SAT variable regardless of
                // which theories are otherwise in play (see tseitin.rs's
                // `Op::Uninterpreted(_) => self.atom(t)` arm, used uniformly).
                // It is skeleton, not a foreign theory atom — exempt it from
                // the fence (slice 5: word_norm's ite-elimination exposes bare
                // condition variables like `c` here that were previously
                // buried, unreachable, inside a single opaque BV atom leaf).
                if matches!(op, Op::Uninterpreted(_))
                    && kids.is_empty()
                    && ctx.sort_of(t) == ctx.bool_sort()
                {
                    return false;
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

/// Fence 1 (slice 44 §4, SOUNDNESS-CRITICAL). Every non-nullary uninterpreted
/// application with a **BitVec result sort** reachable from `atoms` must have
/// arguments the blaster can turn into words, because `blast_bv_word`'s
/// congruence arm compares argument words pairwise.
///
/// BV-sorted arguments always qualify. FP-sorted arguments qualify only when
/// `allow_fp_args` — that is, on the FP/mixed path, where a `Lowerer` exists
/// with a `core_eq`-based `word_eq`. A `Blaster` alone cannot compare an FP
/// word (`core_eq` lives in `shinri-fp`, which depends on `shinri-bv` and not
/// the reverse).
///
/// Everything else — Int, Bool, Array, String, uninterpreted sorts,
/// RoundingMode — fences the caller to a sound `Unknown`. Without this,
/// `Lowerer::word` reaches its `unreachable!("Lowerer::word on non-BV/non-FP
/// sort")` (`crates/shinri-fp/src/lower.rs:69`) and `Blaster::word` reaches
/// `blast_bv_word`'s builtin dispatch on a non-BV term.
///
/// Walks the ATOM set rather than the assertion list: that is exactly what
/// reaches the blaster, and it stays a superset of what survives `rewrite`
/// (rewriting can fold applications away but never create them), so the
/// conservative bias every other fence in this stage has is preserved.
pub fn uf_args_supported(ctx: &Context, atoms: &[TermId], allow_fp_args: bool) -> bool {
    let mut seen = rustc_hash::FxHashSet::default();
    atoms
        .iter()
        .all(|&a| walk_uf_args(ctx, a, allow_fp_args, &mut seen))
}

fn walk_uf_args(
    ctx: &Context,
    t: TermId,
    allow_fp_args: bool,
    seen: &mut rustc_hash::FxHashSet<TermId>,
) -> bool {
    if !seen.insert(t) {
        return true; // already validated on another path
    }
    let TermNode::App { op, args, sort } = ctx.term_node(t) else {
        return true; // a constant has no arguments
    };
    let kids = ctx.children(*args).to_vec();
    if matches!(op, Op::Uninterpreted(_)) && !kids.is_empty() && ctx.bv_width(*sort).is_some() {
        for &k in &kids {
            let ks = ctx.sort_of(k);
            let wordable =
                ctx.bv_width(ks).is_some() || (allow_fp_args && ctx.fp_widths(ks).is_some());
            if !wordable {
                return false;
            }
        }
    }
    kids.iter()
        .all(|&k| walk_uf_args(ctx, k, allow_fp_args, seen))
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
        let add = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, one])
            .unwrap();
        let eq = ctx.mk_eq(add, one).unwrap(); // BV equality
        let ult = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvUlt), &[x, five])
            .unwrap();
        let assertions = vec![eq, ult];
        assert!(solver_uses_bv(&ctx, &assertions));
        let atoms = collect_bv_atoms(&ctx, &assertions);
        // Both the BV equality and the BV predicate must be collected.
        assert!(
            atoms.contains(&eq),
            "BV equality must be collected (soundness)"
        );
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

    #[test]
    fn uf_args_supported_admits_bv_arguments() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fx, c]).unwrap();
        assert!(uf_args_supported(&ctx, &[atom], false));
    }

    #[test]
    fn uf_args_supported_rejects_an_int_argument() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let int_s = ctx.int_sort();
        let h = ctx.declare_fun("h", &[int_s], s8);
        let nf = ctx.declare_fun("n", &[], int_s);
        let n = ctx.mk_app(Op::Uninterpreted(nf), &[]).unwrap();
        let hn = ctx.mk_app(Op::Uninterpreted(h), &[n]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[hn, c]).unwrap();
        assert!(
            !uf_args_supported(&ctx, &[atom], false),
            "an Int-sorted argument has no blastable word — must fence"
        );
    }

    #[test]
    fn uf_args_supported_leaves_nullary_applications_alone() {
        // A nullary uninterpreted BV symbol has no arguments to check and must
        // never be fenced — it is the ordinary BV variable case.
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(42u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, c]).unwrap();
        assert!(uf_args_supported(&ctx, &[atom], false));
    }
}
