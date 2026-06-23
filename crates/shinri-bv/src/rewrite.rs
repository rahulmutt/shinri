//! Word-level rewrite pass for QF_BV terms.
//!
//! `rewrite` performs bottom-up, semantics-preserving simplification of BV terms
//! BEFORE bit-blasting. It is purely an optimization: the blaster is the source of
//! truth. A wrong rewrite rule = a wrong SAT/UNSAT answer.
//!
//! ## Design invariants
//! - Correctness dominates coverage: it is always correct to NOT rewrite a term.
//! - Every rule implemented is blast-equivalence (miter) tested.
//! - Idempotent: `rewrite(rewrite(t)) == rewrite(t)`.
//! - Memoized via `FxHashMap<TermId, TermId>` for linearity.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_num::Integer;

/// Bottom-up, semantics-preserving simplification of a BV (or Bool) term.
/// Returns a term semantically equal to `t`. Idempotent.
pub fn rewrite(ctx: &mut Context, t: TermId) -> TermId {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    rewrite_inner(ctx, t, &mut memo)
}

fn rewrite_inner(
    ctx: &mut Context,
    t: TermId,
    memo: &mut FxHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&cached) = memo.get(&t) {
        return cached;
    }

    let result = match ctx.term_node(t).clone() {
        // Leaves: constants and nullary uninterpreted fns — return as-is.
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let child_ids: Vec<TermId> = ctx.children(args).to_vec();

            // Bottom-up: rewrite children first.
            let new_children: Vec<TermId> = child_ids
                .iter()
                .map(|&c| rewrite_inner(ctx, c, memo))
                .collect();

            // Rebuild the node if any child changed.
            let changed = new_children.iter().zip(child_ids.iter()).any(|(nc, &c)| *nc != c);
            let rebuilt = if changed {
                match ctx.mk_app(op, &new_children) {
                    Ok(id) => id,
                    // Shouldn't happen for a well-typed term, but if it does, return original.
                    Err(_) => t,
                }
            } else {
                t
            };

            // Apply local simplification rules to the (possibly rebuilt) node.
            apply_rules(ctx, rebuilt)
        }
    };

    memo.insert(t, result);
    result
}

/// Apply word-level rewrite rules to a single node.
/// Returns a semantically equal term (possibly simplified).
fn apply_rules(ctx: &mut Context, t: TermId) -> TermId {
    let node = ctx.term_node(t).clone();
    match node {
        TermNode::App { op: Op::Builtin(bv_op), args, .. } => {
            let child_ids: Vec<TermId> = ctx.children(args).to_vec();
            match bv_op {
                // ── Constant folding ─────────────────────────────────────────
                // For binary ops with both operands as BV constants:
                // compute the value over Integer, reduce mod 2^width, return constant.
                BuiltinOp::BvAdd => {
                    fold_binary_or_identity(ctx, t, &child_ids, bv_op)
                }
                BuiltinOp::BvSub => {
                    fold_binary_or_identity(ctx, t, &child_ids, bv_op)
                }
                BuiltinOp::BvMul => {
                    fold_binary_or_identity(ctx, t, &child_ids, bv_op)
                }
                BuiltinOp::BvAnd => {
                    fold_binary_or_identity(ctx, t, &child_ids, bv_op)
                }
                BuiltinOp::BvOr => {
                    fold_binary_or_identity(ctx, t, &child_ids, bv_op)
                }
                BuiltinOp::BvXor => {
                    fold_binary_or_identity(ctx, t, &child_ids, bv_op)
                }
                BuiltinOp::BvNot => {
                    // Constant fold bvnot
                    if let Some((width, val)) = ctx.bv_const_value(child_ids[0]) {
                        let width = width;
                        let val = val.clone();
                        let mask = make_all_ones(width);
                        let result_val = bitwise_xor_int(&val, &mask, width);
                        ctx.mk_bv_const(width, result_val)
                    } else {
                        t
                    }
                }
                BuiltinOp::BvNeg => {
                    // Constant fold bvneg = 0 - x
                    if let Some((width, val)) = ctx.bv_const_value(child_ids[0]) {
                        let width = width;
                        let val = val.clone();
                        let zero = Integer::zero();
                        let result_val = reduce_mod_pow2(&(zero - val), width);
                        ctx.mk_bv_const(width, result_val)
                    } else {
                        t
                    }
                }
                BuiltinOp::BvShl => {
                    fold_binary_or_identity(ctx, t, &child_ids, bv_op)
                }
                // ── Structural rules ─────────────────────────────────────────
                BuiltinOp::BvExtract { hi, lo } => {
                    apply_extract_rules(ctx, t, child_ids[0], hi, lo)
                }
                _ => t,
            }
        }
        _ => t,
    }
}

/// Handle binary ops: if both args are constants, fold; otherwise apply identity rules.
fn fold_binary_or_identity(
    ctx: &mut Context,
    t: TermId,
    child_ids: &[TermId],
    op: BuiltinOp,
) -> TermId {
    let lhs = child_ids[0];
    let rhs = child_ids[1];
    let lhs_const = ctx.bv_const_value(lhs).map(|(w, v)| (w, v.clone()));
    let rhs_const = ctx.bv_const_value(rhs).map(|(w, v)| (w, v.clone()));

    // Constant folding: both operands are constants.
    if let (Some((lw, lv)), Some((_rw, rv))) = (lhs_const.clone(), rhs_const.clone()) {
        let width = lw;
        if let Some(result_val) = fold_const_binary(op, &lv, &rv, width) {
            return ctx.mk_bv_const(width, result_val);
        }
    }

    // Identity rules (one or both operands may be constants).
    apply_identity(ctx, t, lhs, rhs, lhs_const, rhs_const, op)
}

/// Compute the result value of a binary BV op applied to two concrete constants.
/// Returns None if this op is not supported for constant folding.
fn fold_const_binary(
    op: BuiltinOp,
    lv: &Integer,
    rv: &Integer,
    width: u32,
) -> Option<Integer> {
    match op {
        BuiltinOp::BvAdd => {
            Some(reduce_mod_pow2(&(lv.clone() + rv.clone()), width))
        }
        BuiltinOp::BvSub => {
            Some(reduce_mod_pow2(&(lv.clone() - rv.clone()), width))
        }
        BuiltinOp::BvMul => {
            Some(reduce_mod_pow2(&(lv.clone() * rv.clone()), width))
        }
        BuiltinOp::BvAnd => {
            Some(bitwise_and_int(lv, rv, width))
        }
        BuiltinOp::BvOr => {
            Some(bitwise_or_int(lv, rv, width))
        }
        BuiltinOp::BvXor => {
            Some(bitwise_xor_int(lv, rv, width))
        }
        BuiltinOp::BvShl => {
            // lv << rv (mod 2^width); if rv >= width, result is 0.
            if let Some(shift_amount) = rv.to_i128() {
                if shift_amount < 0 || shift_amount >= width as i128 {
                    Some(Integer::zero())
                } else {
                    // lv * 2^shift_amount mod 2^width
                    let two = Integer::from(2i128);
                    let mut factor = Integer::one();
                    for _ in 0..shift_amount {
                        factor = factor * two.clone();
                    }
                    Some(reduce_mod_pow2(&(lv.clone() * factor), width))
                }
            } else {
                // Very large shift -> result is 0.
                Some(Integer::zero())
            }
        }
        // Signed division ops and unsigned div: skip (too subtle to fold safely here).
        // Leave to the blaster.
        _ => None,
    }
}

/// Apply identity rules (e.g., x + 0 = x, x & ~0 = x, etc.).
fn apply_identity(
    ctx: &mut Context,
    t: TermId,
    lhs: TermId,
    rhs: TermId,
    lhs_const: Option<(u32, Integer)>,
    rhs_const: Option<(u32, Integer)>,
    op: BuiltinOp,
) -> TermId {
    // Width derived from the term we already have.
    let width = match ctx.term_node(t) {
        TermNode::App { sort, .. } => ctx.bv_width(*sort).unwrap_or(0),
        _ => return t,
    };
    if width == 0 {
        return t;
    }

    let zero = Integer::zero();
    let one = Integer::one();
    let all_ones = make_all_ones(width);

    match op {
        BuiltinOp::BvAdd => {
            // x + 0 -> x  or  0 + x -> x
            if matches_const(&rhs_const, &zero) {
                return lhs;
            }
            if matches_const(&lhs_const, &zero) {
                return rhs;
            }
            t
        }
        BuiltinOp::BvSub => {
            // x - 0 -> x
            if matches_const(&rhs_const, &zero) {
                return lhs;
            }
            // x - x -> 0
            if lhs == rhs {
                return ctx.mk_bv_const(width, Integer::zero());
            }
            t
        }
        BuiltinOp::BvMul => {
            // x * 1 -> x  or  1 * x -> x
            if matches_const(&rhs_const, &one) {
                return lhs;
            }
            if matches_const(&lhs_const, &one) {
                return rhs;
            }
            // x * 0 -> 0  or  0 * x -> 0
            if matches_const(&rhs_const, &zero) || matches_const(&lhs_const, &zero) {
                return ctx.mk_bv_const(width, Integer::zero());
            }
            t
        }
        BuiltinOp::BvAnd => {
            // x & ~0 -> x  or  ~0 & x -> x
            if matches_const(&rhs_const, &all_ones) {
                return lhs;
            }
            if matches_const(&lhs_const, &all_ones) {
                return rhs;
            }
            // x & 0 -> 0  or  0 & x -> 0
            if matches_const(&rhs_const, &zero) || matches_const(&lhs_const, &zero) {
                return ctx.mk_bv_const(width, Integer::zero());
            }
            t
        }
        BuiltinOp::BvOr => {
            // x | 0 -> x  or  0 | x -> x
            if matches_const(&rhs_const, &zero) {
                return lhs;
            }
            if matches_const(&lhs_const, &zero) {
                return rhs;
            }
            // x | ~0 -> ~0  or  ~0 | x -> ~0
            if matches_const(&rhs_const, &all_ones) || matches_const(&lhs_const, &all_ones) {
                return ctx.mk_bv_const(width, all_ones);
            }
            t
        }
        BuiltinOp::BvXor => {
            // x ^ 0 -> x  or  0 ^ x -> x
            if matches_const(&rhs_const, &zero) {
                return lhs;
            }
            if matches_const(&lhs_const, &zero) {
                return rhs;
            }
            t
        }
        BuiltinOp::BvShl => {
            // x << 0 -> x
            if matches_const(&rhs_const, &zero) {
                return lhs;
            }
            t
        }
        _ => t,
    }
}

/// Apply structural rules for BvExtract.
/// Rules:
/// - extract(i, j, extract(k, l, a)) -> extract(i+l, j+l, a)
/// - extract(i, j, concat(hi, lo)):
///   - If the range is entirely within lo: extract(i, j, lo)
///   - If the range is entirely within hi: extract(i - lo_width, j - lo_width, hi)
///   (The split-across-boundary case is more complex and left to the blaster for soundness.)
fn apply_extract_rules(ctx: &mut Context, t: TermId, inner: TermId, hi: u32, lo: u32) -> TermId {
    match ctx.term_node(inner).clone() {
        TermNode::App { op: Op::Builtin(BuiltinOp::BvExtract { hi: _k, lo: l }), args, .. } => {
            // extract(hi, lo, extract(k, l, a)) -> extract(hi+l, lo+l, a)
            let inner_children: Vec<TermId> = ctx.children(args).to_vec();
            let a = inner_children[0];
            let new_hi = hi + l;
            let new_lo = lo + l;
            // Verify the new indices are within bounds (they should be for well-typed terms).
            let a_sort = ctx.sort_of(a);
            if let Some(a_width) = ctx.bv_width(a_sort) {
                if new_hi < a_width && new_lo <= new_hi {
                    match ctx.mk_app(Op::Builtin(BuiltinOp::BvExtract { hi: new_hi, lo: new_lo }), &[a]) {
                        Ok(id) => return id,
                        Err(_) => return t,
                    }
                }
            }
            t
        }
        TermNode::App { op: Op::Builtin(BuiltinOp::BvConcat), args, .. } => {
            // extract(hi, lo, concat(hi_part, lo_part))
            // concat(hi_part, lo_part): lo_part occupies bits [0, lo_width-1],
            //                          hi_part occupies bits [lo_width, total-1].
            let concat_children: Vec<TermId> = ctx.children(args).to_vec();
            let hi_part = concat_children[0];
            let lo_part = concat_children[1];
            let lo_sort = ctx.sort_of(lo_part);
            if let Some(lo_width) = ctx.bv_width(lo_sort) {
                if hi < lo_width {
                    // Entirely within lo_part.
                    match ctx.mk_app(Op::Builtin(BuiltinOp::BvExtract { hi, lo }), &[lo_part]) {
                        Ok(id) => return id,
                        Err(_) => return t,
                    }
                } else if lo >= lo_width {
                    // Entirely within hi_part.
                    let new_hi = hi - lo_width;
                    let new_lo = lo - lo_width;
                    match ctx.mk_app(Op::Builtin(BuiltinOp::BvExtract { hi: new_hi, lo: new_lo }), &[hi_part]) {
                        Ok(id) => return id,
                        Err(_) => return t,
                    }
                }
                // Crosses boundary: leave to blaster.
            }
            t
        }
        _ => t,
    }
}

// ── Integer-level bitwise helpers ───────────────────────────────────────────

/// Reduce `value` modulo 2^width.
fn reduce_mod_pow2(value: &Integer, width: u32) -> Integer {
    let mut modulus = Integer::one();
    let two = Integer::from(2i128);
    for _ in 0..width {
        modulus = modulus * two.clone();
    }
    let (_, mut rem) = value.div_rem(&modulus);
    if rem.is_negative() {
        rem = rem + modulus;
    }
    rem
}

/// Compute all-ones value for a given width: 2^width - 1.
fn make_all_ones(width: u32) -> Integer {
    let mut modulus = Integer::one();
    let two = Integer::from(2i128);
    for _ in 0..width {
        modulus = modulus * two.clone();
    }
    modulus - Integer::one()
}

/// Bitwise AND of two non-negative Integer values (both in [0, 2^width)).
/// Extracts bits using repeated div_rem by 2.
fn bitwise_and_int(a: &Integer, b: &Integer, width: u32) -> Integer {
    let two = Integer::from(2i128);
    let mut rem_a = a.clone();
    let mut rem_b = b.clone();
    let mut result = Integer::zero();
    let mut place = Integer::one();
    for _ in 0..width {
        let (qa, ra) = rem_a.div_rem(&two);
        let (qb, rb) = rem_b.div_rem(&two);
        rem_a = qa;
        rem_b = qb;
        // AND: bit is 1 only if both are 1.
        if !ra.is_zero() && !rb.is_zero() {
            result = result + place.clone();
        }
        place = place * two.clone();
    }
    result
}

/// Bitwise OR of two non-negative Integer values.
fn bitwise_or_int(a: &Integer, b: &Integer, width: u32) -> Integer {
    let two = Integer::from(2i128);
    let mut rem_a = a.clone();
    let mut rem_b = b.clone();
    let mut result = Integer::zero();
    let mut place = Integer::one();
    for _ in 0..width {
        let (qa, ra) = rem_a.div_rem(&two);
        let (qb, rb) = rem_b.div_rem(&two);
        rem_a = qa;
        rem_b = qb;
        // OR: bit is 1 if either is 1.
        if !ra.is_zero() || !rb.is_zero() {
            result = result + place.clone();
        }
        place = place * two.clone();
    }
    result
}

/// Bitwise XOR of two non-negative Integer values.
fn bitwise_xor_int(a: &Integer, b: &Integer, width: u32) -> Integer {
    let two = Integer::from(2i128);
    let mut rem_a = a.clone();
    let mut rem_b = b.clone();
    let mut result = Integer::zero();
    let mut place = Integer::one();
    for _ in 0..width {
        let (qa, ra) = rem_a.div_rem(&two);
        let (qb, rb) = rem_b.div_rem(&two);
        rem_a = qa;
        rem_b = qb;
        // XOR: bit is 1 if exactly one is 1.
        if ra.is_zero() != rb.is_zero() {
            result = result + place.clone();
        }
        place = place * two.clone();
    }
    result
}

/// Check if an optional const value matches a target.
fn matches_const(val: &Option<(u32, Integer)>, target: &Integer) -> bool {
    matches!(val, Some((_, v)) if v == target)
}

// ── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

    // ── Step 1: Failing test (basic const fold + identity) ──────────────────

    #[test]
    fn folds_constants_and_identities() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);

        // Constant fold: 20 + 22 -> 42
        let a = ctx.mk_bv_const(8, Integer::from(20u64));
        let b = ctx.mk_bv_const(8, Integer::from(22u64));
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[a, b]).unwrap();
        let r = rewrite(&mut ctx, add);
        assert_eq!(
            ctx.bv_const_value(r).unwrap().1,
            &Integer::from(42u64),
            "20 + 22 should fold to 42"
        );

        // Identity: x + 0 -> x
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, Integer::from(0u64));
        let add0 = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, zero]).unwrap();
        assert_eq!(rewrite(&mut ctx, add0), x, "x + 0 should simplify to x");
    }

    // ── Additional unit tests ────────────────────────────────────────────────

    #[test]
    fn const_fold_wrap_around() {
        let mut ctx = Context::new();
        // 200 + 100 = 300 = 44 mod 256
        let a = ctx.mk_bv_const(8, Integer::from(200u64));
        let b = ctx.mk_bv_const(8, Integer::from(100u64));
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[a, b]).unwrap();
        let r = rewrite(&mut ctx, add);
        assert_eq!(ctx.bv_const_value(r).unwrap().1, &Integer::from(44u64));
    }

    #[test]
    fn identity_sub_zero() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_sub", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, Integer::from(0u64));
        let sub0 = ctx.mk_app(Op::Builtin(BuiltinOp::BvSub), &[x, zero]).unwrap();
        assert_eq!(rewrite(&mut ctx, sub0), x, "x - 0 should be x");
    }

    #[test]
    fn identity_sub_self() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_selfsub", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let sub_xx = ctx.mk_app(Op::Builtin(BuiltinOp::BvSub), &[x, x]).unwrap();
        let r = rewrite(&mut ctx, sub_xx);
        assert_eq!(ctx.bv_const_value(r).unwrap().1, &Integer::zero(), "x - x should be 0");
    }

    #[test]
    fn identity_mul_one() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_mul1", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let mul1 = ctx.mk_app(Op::Builtin(BuiltinOp::BvMul), &[x, one]).unwrap();
        assert_eq!(rewrite(&mut ctx, mul1), x, "x * 1 should be x");
    }

    #[test]
    fn identity_mul_zero() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_mul0", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, Integer::from(0u64));
        let mul0 = ctx.mk_app(Op::Builtin(BuiltinOp::BvMul), &[x, zero]).unwrap();
        let r = rewrite(&mut ctx, mul0);
        assert_eq!(ctx.bv_const_value(r).unwrap().1, &Integer::zero(), "x * 0 should be 0");
    }

    #[test]
    fn identity_and_all_ones() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_and_ones", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let all_ones = ctx.mk_bv_const(8, Integer::from(0xFFu64));
        let and_ones = ctx.mk_app(Op::Builtin(BuiltinOp::BvAnd), &[x, all_ones]).unwrap();
        assert_eq!(rewrite(&mut ctx, and_ones), x, "x & 0xFF should be x");
    }

    #[test]
    fn identity_and_zero() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_and_zero", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, Integer::from(0u64));
        let and0 = ctx.mk_app(Op::Builtin(BuiltinOp::BvAnd), &[x, zero]).unwrap();
        let r = rewrite(&mut ctx, and0);
        assert_eq!(ctx.bv_const_value(r).unwrap().1, &Integer::zero(), "x & 0 should be 0");
    }

    #[test]
    fn identity_or_zero() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_or_zero", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, Integer::from(0u64));
        let or0 = ctx.mk_app(Op::Builtin(BuiltinOp::BvOr), &[x, zero]).unwrap();
        assert_eq!(rewrite(&mut ctx, or0), x, "x | 0 should be x");
    }

    #[test]
    fn identity_or_all_ones() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_or_ones", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let all_ones = ctx.mk_bv_const(8, Integer::from(0xFFu64));
        let or_ones = ctx.mk_app(Op::Builtin(BuiltinOp::BvOr), &[x, all_ones]).unwrap();
        let r = rewrite(&mut ctx, or_ones);
        assert_eq!(ctx.bv_const_value(r).unwrap().1, &Integer::from(0xFFu64), "x | 0xFF should be 0xFF");
    }

    #[test]
    fn identity_xor_zero() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_xor_zero", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, Integer::from(0u64));
        let xor0 = ctx.mk_app(Op::Builtin(BuiltinOp::BvXor), &[x, zero]).unwrap();
        assert_eq!(rewrite(&mut ctx, xor0), x, "x ^ 0 should be x");
    }

    #[test]
    fn identity_shl_zero() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_shl_zero", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, Integer::from(0u64));
        let shl0 = ctx.mk_app(Op::Builtin(BuiltinOp::BvShl), &[x, zero]).unwrap();
        assert_eq!(rewrite(&mut ctx, shl0), x, "x << 0 should be x");
    }

    #[test]
    fn idempotent() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        // Test with a constant fold term.
        let a = ctx.mk_bv_const(8, Integer::from(10u64));
        let b = ctx.mk_bv_const(8, Integer::from(5u64));
        let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[a, b]).unwrap();
        let r1 = rewrite(&mut ctx, add);
        let r2 = rewrite(&mut ctx, r1);
        assert_eq!(r1, r2, "rewrite(rewrite(t)) == rewrite(t)");

        // Test with a variable identity.
        let xf = ctx.declare_fun("x_idem", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, Integer::from(0u64));
        let add0 = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, zero]).unwrap();
        let r3 = rewrite(&mut ctx, add0);
        let r4 = rewrite(&mut ctx, r3);
        assert_eq!(r3, r4, "rewrite(rewrite(x+0)) == rewrite(x+0)");

        // Test with an already-simplified term.
        let r5 = rewrite(&mut ctx, x);
        assert_eq!(r5, x, "rewrite(x) == x for a variable");
        let r6 = rewrite(&mut ctx, r5);
        assert_eq!(r5, r6, "rewrite(rewrite(x)) == x");
    }

    // ── Blast-equivalence (miter) tests ─────────────────────────────────────
    //
    // For each implemented rule, we verify that blast(t) and blast(rewrite(t))
    // are equivalent. For constant-fold terms we use solve_value and assert equal.
    // For identity rules over free variables we build a miter:
    //   assert (blast(t) XOR blast(rewrite(t))) OR-reduced is UNSAT.

    #[cfg(test)]
    mod miter {
        use super::*;
        use crate::blast::Blaster;
        use crate::testkit::solve_value;
        use shinri_sat::{Lit, NoProof, NoTheory, Solver, SolveResult, SolverConfig, Var, Vmtf};

        /// Build a solver from a finished Cnf.
        fn build_solver(cnf: &crate::blast::Cnf) -> Solver<NoTheory, NoProof, Vmtf> {
            let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
            for _ in 0..cnf.num_vars {
                s.new_var();
            }
            for clause in &cnf.clauses {
                let sat_lits: Vec<Lit> = clause
                    .iter()
                    .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
                    .collect();
                s.add_clause(&sat_lits);
            }
            s
        }

        /// Assert that a formula (expressed as a single BitLit in a Blaster) is UNSAT.
        fn assert_unsat(b: Blaster, formula: crate::blast::BitLit) {
            // Add unit clause asserting the formula is TRUE.
            // If UNSAT: formula cannot be true -> our miter (t != rewrite(t)) is always false -> they're equivalent.
            let mut cnf = b.finish();
            cnf.clauses.push(vec![formula]);
            let mut s = build_solver(&cnf);
            let result = s.solve();
            assert!(
                matches!(result, SolveResult::Unsat { .. }),
                "miter is SAT — rewrite rule is UNSOUND! got {:?}", result
            );
        }

        /// Blast two BV words in the same blaster and build the miter:
        /// OR-reduce of (a[i] XOR b[i]) for all i.
        /// Returns a single BitLit representing "a and b differ on at least one bit".
        fn word_miter(
            b: &mut Blaster,
            ctx: &Context,
            t: TermId,
            rewritten: TermId,
        ) -> crate::blast::BitLit {
            let orig_bits = b.blast_word(ctx, t);
            let rw_bits = b.blast_word(ctx, rewritten);
            assert_eq!(orig_bits.len(), rw_bits.len(), "width mismatch in miter");
            // Build XOR of each pair of bits.
            let xors: Vec<crate::blast::BitLit> = orig_bits
                .iter()
                .zip(rw_bits.iter())
                .map(|(&a, &c)| b.xor2(a, c))
                .collect();
            // OR-reduce to get "any bit differs".
            let mut acc = b.zero();
            for x in xors {
                acc = b.or2(acc, x);
            }
            acc
        }

        // ── Constant fold miters (solve_value both, assert equal) ────────────

        #[test]
        fn miter_const_fold_bvadd() {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(200u64));
            let b_term = ctx.mk_bv_const(8, Integer::from(100u64));
            let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[a, b_term]).unwrap();
            let rw = rewrite(&mut ctx, add);

            // Both should produce the same value.
            let mut bl1 = Blaster::new();
            let bits1 = bl1.blast_word(&ctx, add);
            let v1 = solve_value(bl1, &bits1);

            let mut bl2 = Blaster::new();
            let bits2 = bl2.blast_word(&ctx, rw);
            let v2 = solve_value(bl2, &bits2);

            assert_eq!(v1, v2, "miter: const fold bvadd 200+100 mod 256");
        }

        #[test]
        fn miter_const_fold_bvsub() {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(5u64));
            let b_term = ctx.mk_bv_const(8, Integer::from(9u64));
            let sub = ctx.mk_app(Op::Builtin(BuiltinOp::BvSub), &[a, b_term]).unwrap();
            let rw = rewrite(&mut ctx, sub);

            let mut bl1 = Blaster::new();
            let bits1 = bl1.blast_word(&ctx, sub);
            let v1 = solve_value(bl1, &bits1);

            let mut bl2 = Blaster::new();
            let bits2 = bl2.blast_word(&ctx, rw);
            let v2 = solve_value(bl2, &bits2);

            assert_eq!(v1, v2, "miter: const fold bvsub 5-9 mod 256");
        }

        #[test]
        fn miter_const_fold_bvmul() {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(13u64));
            let b_term = ctx.mk_bv_const(8, Integer::from(20u64));
            let mul = ctx.mk_app(Op::Builtin(BuiltinOp::BvMul), &[a, b_term]).unwrap();
            let rw = rewrite(&mut ctx, mul);

            let mut bl1 = Blaster::new();
            let bits1 = bl1.blast_word(&ctx, mul);
            let v1 = solve_value(bl1, &bits1);

            let mut bl2 = Blaster::new();
            let bits2 = bl2.blast_word(&ctx, rw);
            let v2 = solve_value(bl2, &bits2);

            assert_eq!(v1, v2, "miter: const fold bvmul 13*20 mod 256");
        }

        #[test]
        fn miter_const_fold_bvand() {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(0b10110101u64));
            let b_term = ctx.mk_bv_const(8, Integer::from(0b11001100u64));
            let and = ctx.mk_app(Op::Builtin(BuiltinOp::BvAnd), &[a, b_term]).unwrap();
            let rw = rewrite(&mut ctx, and);

            let mut bl1 = Blaster::new();
            let bits1 = bl1.blast_word(&ctx, and);
            let v1 = solve_value(bl1, &bits1);

            let mut bl2 = Blaster::new();
            let bits2 = bl2.blast_word(&ctx, rw);
            let v2 = solve_value(bl2, &bits2);

            assert_eq!(v1, v2, "miter: const fold bvand");
        }

        #[test]
        fn miter_const_fold_bvor() {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(0b10110101u64));
            let b_term = ctx.mk_bv_const(8, Integer::from(0b01001100u64));
            let or = ctx.mk_app(Op::Builtin(BuiltinOp::BvOr), &[a, b_term]).unwrap();
            let rw = rewrite(&mut ctx, or);

            let mut bl1 = Blaster::new();
            let bits1 = bl1.blast_word(&ctx, or);
            let v1 = solve_value(bl1, &bits1);

            let mut bl2 = Blaster::new();
            let bits2 = bl2.blast_word(&ctx, rw);
            let v2 = solve_value(bl2, &bits2);

            assert_eq!(v1, v2, "miter: const fold bvor");
        }

        #[test]
        fn miter_const_fold_bvxor() {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(0b10110101u64));
            let b_term = ctx.mk_bv_const(8, Integer::from(0b01001100u64));
            let xor = ctx.mk_app(Op::Builtin(BuiltinOp::BvXor), &[a, b_term]).unwrap();
            let rw = rewrite(&mut ctx, xor);

            let mut bl1 = Blaster::new();
            let bits1 = bl1.blast_word(&ctx, xor);
            let v1 = solve_value(bl1, &bits1);

            let mut bl2 = Blaster::new();
            let bits2 = bl2.blast_word(&ctx, rw);
            let v2 = solve_value(bl2, &bits2);

            assert_eq!(v1, v2, "miter: const fold bvxor");
        }

        #[test]
        fn miter_const_fold_bvnot() {
            let mut ctx = Context::new();
            let a = ctx.mk_bv_const(8, Integer::from(0b10110101u64));
            let not = ctx.mk_app(Op::Builtin(BuiltinOp::BvNot), &[a]).unwrap();
            let rw = rewrite(&mut ctx, not);

            let mut bl1 = Blaster::new();
            let bits1 = bl1.blast_word(&ctx, not);
            let v1 = solve_value(bl1, &bits1);

            let mut bl2 = Blaster::new();
            let bits2 = bl2.blast_word(&ctx, rw);
            let v2 = solve_value(bl2, &bits2);

            assert_eq!(v1, v2, "miter: const fold bvnot");
        }

        #[test]
        fn miter_const_fold_bvneg() {
            let mut ctx = Context::new();
            // Test with -128 and 0 edge cases.
            for v in [0u64, 1, 128, 255] {
                let a = ctx.mk_bv_const(8, Integer::from(v));
                let neg = ctx.mk_app(Op::Builtin(BuiltinOp::BvNeg), &[a]).unwrap();
                let rw = rewrite(&mut ctx, neg);

                let mut bl1 = Blaster::new();
                let bits1 = bl1.blast_word(&ctx, neg);
                let v1 = solve_value(bl1, &bits1);

                let mut bl2 = Blaster::new();
                let bits2 = bl2.blast_word(&ctx, rw);
                let v2 = solve_value(bl2, &bits2);

                assert_eq!(v1, v2, "miter: const fold bvneg({})", v);
            }
        }

        #[test]
        fn miter_const_fold_bvshl() {
            let mut ctx = Context::new();
            // Test with various shift amounts including 0 and >=width.
            for (x, sh) in [(0b10110101u64, 2u64), (0xFF, 0), (0x80, 7), (0x01, 8)] {
                let a = ctx.mk_bv_const(8, Integer::from(x));
                let b_term = ctx.mk_bv_const(8, Integer::from(sh));
                let shl = ctx.mk_app(Op::Builtin(BuiltinOp::BvShl), &[a, b_term]).unwrap();
                let rw = rewrite(&mut ctx, shl);

                let mut bl1 = Blaster::new();
                let bits1 = bl1.blast_word(&ctx, shl);
                let v1 = solve_value(bl1, &bits1);

                let mut bl2 = Blaster::new();
                let bits2 = bl2.blast_word(&ctx, rw);
                let v2 = solve_value(bl2, &bits2);

                assert_eq!(v1, v2, "miter: const fold bvshl x={:#x} sh={}", x, sh);
            }
        }

        // ── Identity rule miters (UNSAT miter over free variable) ────────────

        #[test]
        fn miter_identity_bvadd_zero() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_add0", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let zero = ctx.mk_bv_const(8, Integer::from(0u64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, zero]).unwrap();
            let rw = rewrite(&mut ctx, t);

            // Miter: assert t != rw is UNSAT.
            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvsub_zero() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_sub0", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let zero = ctx.mk_bv_const(8, Integer::from(0u64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvSub), &[x, zero]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvsub_self() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_subsub", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvSub), &[x, x]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvmul_one() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_mul1", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let one = ctx.mk_bv_const(8, Integer::from(1u64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvMul), &[x, one]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvmul_zero() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_mul0", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let zero = ctx.mk_bv_const(8, Integer::from(0u64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvMul), &[x, zero]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvand_all_ones() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_and1", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let all_ones = ctx.mk_bv_const(8, Integer::from(0xFFu64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvAnd), &[x, all_ones]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvand_zero() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_and0", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let zero = ctx.mk_bv_const(8, Integer::from(0u64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvAnd), &[x, zero]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvor_zero() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_or0", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let zero = ctx.mk_bv_const(8, Integer::from(0u64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvOr), &[x, zero]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvor_all_ones() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_or1", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let all_ones = ctx.mk_bv_const(8, Integer::from(0xFFu64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvOr), &[x, all_ones]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvxor_zero() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_xor0", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let zero = ctx.mk_bv_const(8, Integer::from(0u64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvXor), &[x, zero]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_identity_bvshl_zero() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_shl0", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            let zero = ctx.mk_bv_const(8, Integer::from(0u64));
            let t = ctx.mk_app(Op::Builtin(BuiltinOp::BvShl), &[x, zero]).unwrap();
            let rw = rewrite(&mut ctx, t);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, t, rw);
            assert_unsat(b, diff);
        }

        // ── Structural rule miters ────────────────────────────────────────────

        #[test]
        fn miter_structural_extract_of_extract() {
            let mut ctx = Context::new();
            let s8 = ctx.bv_sort(8);
            let xf = ctx.declare_fun("x_m_exex", &[], s8);
            let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
            // extract(5, 2, extract(7, 1, x)) -> extract(5+1, 2+1, x) = extract(6, 3, x)
            let inner_ext = ctx.mk_app(Op::Builtin(BuiltinOp::BvExtract { hi: 7, lo: 1 }), &[x]).unwrap();
            let outer_ext = ctx.mk_app(Op::Builtin(BuiltinOp::BvExtract { hi: 5, lo: 2 }), &[inner_ext]).unwrap();
            let rw = rewrite(&mut ctx, outer_ext);

            // Miter: both are 4-bit results.
            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, outer_ext, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_structural_extract_entirely_in_lo() {
            let mut ctx = Context::new();
            let s4 = ctx.bv_sort(4);
            let s4b = ctx.bv_sort(4);
            let hf = ctx.declare_fun("h_m_cat", &[], s4);
            let lf = ctx.declare_fun("l_m_cat", &[], s4b);
            let hi_t = ctx.mk_app(Op::Uninterpreted(hf), &[]).unwrap();
            let lo_t = ctx.mk_app(Op::Uninterpreted(lf), &[]).unwrap();
            // concat(hi[3:0], lo[3:0]) -> 8-bit
            let cat = ctx.mk_app(Op::Builtin(BuiltinOp::BvConcat), &[hi_t, lo_t]).unwrap();
            // extract(2, 1, cat) -> lo[2:1] (entirely in lo)
            let ext = ctx.mk_app(Op::Builtin(BuiltinOp::BvExtract { hi: 2, lo: 1 }), &[cat]).unwrap();
            let rw = rewrite(&mut ctx, ext);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, ext, rw);
            assert_unsat(b, diff);
        }

        #[test]
        fn miter_structural_extract_entirely_in_hi() {
            let mut ctx = Context::new();
            let s4 = ctx.bv_sort(4);
            let s4b = ctx.bv_sort(4);
            let hf = ctx.declare_fun("h_m_cat2", &[], s4);
            let lf = ctx.declare_fun("l_m_cat2", &[], s4b);
            let hi_t = ctx.mk_app(Op::Uninterpreted(hf), &[]).unwrap();
            let lo_t = ctx.mk_app(Op::Uninterpreted(lf), &[]).unwrap();
            // concat(hi[3:0], lo[3:0]) -> 8-bit
            let cat = ctx.mk_app(Op::Builtin(BuiltinOp::BvConcat), &[hi_t, lo_t]).unwrap();
            // extract(6, 5, cat) -> hi[2:1] (entirely in hi, lo_width=4)
            let ext = ctx.mk_app(Op::Builtin(BuiltinOp::BvExtract { hi: 6, lo: 5 }), &[cat]).unwrap();
            let rw = rewrite(&mut ctx, ext);

            let mut b = Blaster::new();
            let diff = word_miter(&mut b, &ctx, ext, rw);
            assert_unsat(b, diff);
        }
    }
}
