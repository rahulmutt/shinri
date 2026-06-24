//! QF_S detection and fence for the string theory stage.
//!
//! ## Overview
//! `uses_strings`: true iff any assertion contains a String-sorted subterm or a
//! `str.*` operator (`str.++`, `str.len`, `str.at`, `str.substr`).
//!
//! `fenced`: true iff strings are mixed with an out-of-scope theory:
//!   (a) A String-sorted term appears as operand/result of an **uninterpreted
//!       function** of arity ≥ 1  (e.g. `(declare-fun f (String) String)`).
//!   (b) **BV operators** co-occur with any string term.
//!   (c) **Arrays over non-(String,String)** (i.e. `select`/`store` over an array
//!       whose index or element is NOT String). Arrays whose BOTH index AND element
//!       are String-sorted fall outside our implementation scope → also fenced.
//!       In practice ANY `select`/`store` that involves a String operand (either
//!       the array itself is over a String sort, or a BV-indexed array coexists
//!       with a String assertion) must be fenced here.
//!
//!   NOT fenced: Strings + Int/LIA (Length arithmetic) + plain String variables.
//!
//! ## Carry-forward (Task 6 / Task 18)
//! `(Array String String)` was NOT fenced by the Task-6 classify layer — it
//! routes to `Owner::Arrays`, not `Owner::String`. This module implements the
//! fence: any `select`/`store` over an array whose index or element sort is
//! String → `fenced()` returns true → caller returns Unknown.

use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

/// True if the sort is `String`.
fn is_string_sort(ctx: &Context, t: TermId) -> bool {
    ctx.sort_of(t) == ctx.string_sort()
}

/// True if `op` is any `str.*` builtin.
fn is_string_op(op: &Op) -> bool {
    matches!(
        op,
        Op::Builtin(
            BuiltinOp::StrConcat | BuiltinOp::StrLen | BuiltinOp::StrAt | BuiltinOp::StrSubstr
        )
    )
}

/// True if `op` is any bitvector builtin.
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

/// True if the sort is `(_ BitVec n)`.
fn is_bv_sort(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::BitVec(_))
}

/// True if the array sort has a String index or element.
/// `(Array String String)`, `(Array String T)`, `(Array T String)` all return true.
fn array_involves_string(ctx: &Context, sort_id: shinri_core::SortId) -> bool {
    match ctx.sort_node(sort_id) {
        SortNode::Array(i, e) => {
            *i == ctx.string_sort() || *e == ctx.string_sort()
        }
        _ => false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Walk helpers (generic visit-once traversal)
// ─────────────────────────────────────────────────────────────────────────────

/// Walk `t` and all its subterms once; call `f` on each; early-exit if `f` returns true.
fn walk_any(ctx: &Context, t: TermId, seen: &mut FxHashSet<TermId>, f: &mut impl FnMut(&Context, TermId) -> bool) -> bool {
    if !seen.insert(t) {
        return false;
    }
    if f(ctx, t) {
        return true;
    }
    match ctx.term_node(t) {
        TermNode::App { args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.iter().any(|&k| walk_any(ctx, k, seen, f))
        }
        TermNode::Const { .. } => false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public API
// ─────────────────────────────────────────────────────────────────────────────

/// True iff any assertion (or any subterm of any assertion) has a String sort or
/// a `str.*` op.  Non-string queries return false immediately (fast path).
pub fn uses_strings(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen = FxHashSet::default();
    assertions.iter().any(|&a| {
        walk_any(ctx, a, &mut seen, &mut |ctx, t| {
            is_string_sort(ctx, t)
                || match ctx.term_node(t) {
                    TermNode::App { op, .. } => is_string_op(op),
                    _ => false,
                }
        })
    })
}

/// Soundness fence (SOUNDNESS-CRITICAL, conservative).
///
/// Given that the query DOES use strings, returns `true` if it ALSO contains an
/// out-of-scope mixing that we cannot handle:
///
/// 1. **String under uninterpreted function** (arity ≥ 1): a non-nullary
///    `Op::Uninterpreted` application where the function's result or at least one
///    argument is String-sorted.
/// 2. **BV ops co-occurring with strings**: any BV builtin anywhere in the term.
/// 3. **Array over String**: any `select`/`store` where the array's sort has a
///    String index or element. This is the carry-forward from Task 6 — such
///    queries route to `Owner::Arrays` not `Owner::String` and are out of scope.
///
/// NOT fenced:
/// - Strings + LIA (Int-sorted arithmetic, str.len).
/// - Plain String variables (nullary `Op::Uninterpreted`, String-sorted).
/// - `Eq`/`Distinct` over String-sorted operands.
/// - Pure Boolean structure (And/Or/Not/Implies/Xor/Ite).
pub fn fenced(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen = FxHashSet::default();
    assertions.iter().any(|&a| walk_fence(ctx, a, &mut seen))
}

fn walk_fence(ctx: &Context, t: TermId, seen: &mut FxHashSet<TermId>) -> bool {
    if !seen.insert(t) {
        return false;
    }
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();

            // ── Fence condition 2: BV ops co-occurring with strings ───────────
            if is_bv_op(op) {
                return true;
            }
            // Also fence a BV-sorted operand (catches BV Eq/Distinct atoms).
            if kids.iter().any(|&k| is_bv_sort(ctx, k)) {
                return true;
            }

            // ── Fence condition 3: arrays over String ─────────────────────────
            // `select`/`store` whose array operand involves a String sort.
            if matches!(op, Op::Builtin(BuiltinOp::Select) | Op::Builtin(BuiltinOp::Store)) {
                if let Some(&arr) = kids.first() {
                    if array_involves_string(ctx, ctx.sort_of(arr)) {
                        return true;
                    }
                }
            }
            // Also fence any term whose sort is directly an array-over-string
            // (e.g. an array constant `(declare-fun a () (Array String String))`).
            if array_involves_string(ctx, ctx.sort_of(t)) {
                return true;
            }

            // ── Fence condition 1: String under uninterpreted function ─────────
            // A non-nullary uninterpreted application whose result or any argument
            // is String-sorted.
            if let Op::Uninterpreted(_) = op {
                if !kids.is_empty() {
                    // Non-nullary (function application).
                    let result_is_str = is_string_sort(ctx, t);
                    let arg_is_str = kids.iter().any(|&k| is_string_sort(ctx, k));
                    if result_is_str || arg_is_str {
                        return true;
                    }
                }
            }

            // ── Safe: Boolean structure, arithmetic, plain string equality ─────
            // Recurse into children.
            kids.iter().any(|&k| walk_fence(ctx, k, seen))
        }
        TermNode::Const { .. } => false,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Unit tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};

    fn str_var(ctx: &mut Context, name: &str) -> TermId {
        let str_s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], str_s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn plain_string_var_uses_strings() {
        let mut ctx = Context::new();
        let x = str_var(&mut ctx, "x");
        assert!(uses_strings(&ctx, &[x]));
    }

    #[test]
    fn non_string_query_not_detected() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xf = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_numeral(shinri_core::Rational::zero(), int);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[x, zero]).unwrap();
        assert!(!uses_strings(&ctx, &[gt]));
    }

    #[test]
    fn string_concat_detected_not_fenced() {
        let mut ctx = Context::new();
        let x = str_var(&mut ctx, "x");
        let y = str_var(&mut ctx, "y");
        let cc = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y]).unwrap();
        let a = ctx.mk_string_const("a");
        let eq = ctx.mk_eq(cc, a).unwrap();
        assert!(uses_strings(&ctx, &[eq]));
        assert!(!fenced(&ctx, &[eq]));
    }

    #[test]
    fn string_under_uf_is_fenced() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let ff = ctx.declare_fun("f", &[str_s], str_s);
        let x = str_var(&mut ctx, "x");
        let fx = ctx.mk_app(Op::Uninterpreted(ff), &[x]).unwrap();
        let eq = ctx.mk_eq(fx, x).unwrap();
        assert!(uses_strings(&ctx, &[eq]));
        assert!(fenced(&ctx, &[eq]));
    }

    #[test]
    fn array_over_string_is_fenced_carry_forward() {
        // (Array String String) select/store → fenced.
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let arr_s = ctx.array_sort(str_s, str_s);
        let af = ctx.declare_fun("a", &[], arr_s);
        let a = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
        let i = str_var(&mut ctx, "i");
        let v = str_var(&mut ctx, "v");
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let eq = ctx.mk_eq(sel, v).unwrap();
        assert!(uses_strings(&ctx, &[eq]));
        assert!(fenced(&ctx, &[eq]));
    }

    #[test]
    fn strings_with_lia_not_fenced() {
        // str.len(x) >= 0: pure String + Int arithmetic, NOT fenced.
        let mut ctx = Context::new();
        let x = str_var(&mut ctx, "x");
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        let zero = ctx.mk_numeral(shinri_core::Rational::zero(), ctx.int_sort());
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[len, zero]).unwrap();
        assert!(uses_strings(&ctx, &[ge]));
        assert!(!fenced(&ctx, &[ge]));
    }
}
