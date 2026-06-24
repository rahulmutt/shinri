//! Pre-pass: desugar `str.at` / `str.substr` into fresh variables + concat +
//! length-guard constraints before handing the query to the core string theory.
//!
//! # SMT-LIB 2.6 semantics
//!
//! `(str.substr s i l)`:
//! - If `0 <= i < |s|` AND `l > 0`: result = substring of `s` starting at
//!   index `i` of length `min(l, |s| - i)`.
//! - Otherwise (i<0, i>=|s|, or l<=0): result = `""`.
//!
//! Encoding:
//! Fresh variables `pre`, `mid`, `post` (all String-sorted).
//! Let `in_range := (0 <= i) AND (i < |s|) AND (l > 0)`.
//! Let `min_l_rem := ite(l <= (|s| - i), l, (|s| - i))` — the `min(l, |s|-i)`.
//!
//! Guard constraints appended to the assertion set:
//!   1. `s = pre ++ mid ++ post`
//!   2. `len(pre) = ite(in_range, i, 0)`
//!   3. `len(mid) = ite(in_range, min_l_rem, 0)`
//!
//! The fresh result variable equals `mid`.  Because `len(mid) = 0` in the
//! out-of-range case (and `len(x) = 0 <=> x = ""` is a length axiom), this
//! correctly yields `""` when out of range — equisatisfiable with the original.
//!
//! `(str.at s i)` is syntactic sugar for `(str.substr s i 1)`.

use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use std::sync::atomic::{AtomicU32, Ordering};

// Global counter for fresh variable names so that multiple calls across
// multiple assertions never collide.
static FRESH_CTR: AtomicU32 = AtomicU32::new(0);

fn next_fresh() -> u32 {
    FRESH_CTR.fetch_add(1, Ordering::Relaxed)
}

/// Returns `true` if the term `t` (or any subterm) is a `str.at` or
/// `str.substr` application.
pub fn contains_substr_or_at(ctx: &Context, t: TermId) -> bool {
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            if matches!(
                op,
                Op::Builtin(BuiltinOp::StrAt) | Op::Builtin(BuiltinOp::StrSubstr)
            ) {
                return true;
            }
            let children = ctx.children(*args).to_vec();
            children
                .iter()
                .any(|&c| contains_substr_or_at(ctx, c))
        }
        TermNode::Const { .. } => false,
    }
}

/// Returns `true` if any term in `assertions` (or any subterm) involves a
/// String-sorted operation (used as a guard to skip non-string queries).
pub fn any_has_string_op(ctx: &Context, assertions: &[TermId]) -> bool {
    assertions.iter().any(|&a| contains_string_op(ctx, a))
}

fn contains_string_op(ctx: &Context, t: TermId) -> bool {
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            if matches!(
                op,
                Op::Builtin(
                    BuiltinOp::StrAt
                        | BuiltinOp::StrSubstr
                        | BuiltinOp::StrConcat
                        | BuiltinOp::StrLen
                )
            ) {
                return true;
            }
            // Also check if any child is string-sorted.
            let children = ctx.children(*args).to_vec();
            if children
                .iter()
                .any(|&c| ctx.sort_of(c) == ctx.string_sort())
            {
                return true;
            }
            children.iter().any(|&c| contains_string_op(ctx, c))
        }
        TermNode::Const { .. } => {
            // String constants
            ctx.sort_of(t) == ctx.string_sort()
        }
    }
}

/// Build the full substr encoding for `str.substr(s, i, l)`:
/// - Allocates fresh `pre`, `mid`, `post` variables.
/// - Appends guard constraints to `guards`.
/// - Returns the fresh `mid` term (the result variable).
///
/// The guard set:
///   1. `(= s (str.concat pre mid post))`
///   2. `(= (str.len pre) (ite in_range i 0))`
///   3. `(= (str.len mid) (ite in_range min_l_rem 0))`
///
/// where `in_range = (and (>= i 0) (< i (str.len s)) (> l 0))`
/// and `min_l_rem = (ite (<= l (- (str.len s) i)) l (- (str.len s) i))`.
fn encode_substr(
    ctx: &mut Context,
    s: TermId,
    i: TermId,
    l: TermId,
    guards: &mut Vec<TermId>,
) -> TermId {
    let n = next_fresh();

    // Declare fresh String variables.
    let str_s = ctx.string_sort();
    let int_s = ctx.int_sort();

    let pre_sym = ctx.declare_fun(&format!("!pre{n}"), &[], str_s);
    let mid_sym = ctx.declare_fun(&format!("!mid{n}"), &[], str_s);
    let post_sym = ctx.declare_fun(&format!("!post{n}"), &[], str_s);

    let pre = ctx
        .mk_app(Op::Uninterpreted(pre_sym), &[])
        .expect("pre well-sorted");
    let mid = ctx
        .mk_app(Op::Uninterpreted(mid_sym), &[])
        .expect("mid well-sorted");
    let post = ctx
        .mk_app(Op::Uninterpreted(post_sym), &[])
        .expect("post well-sorted");

    // len(s), len(pre), len(mid)
    let len_s = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrLen), &[s])
        .expect("str.len(s)");
    let len_pre = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrLen), &[pre])
        .expect("str.len(pre)");
    let len_mid = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrLen), &[mid])
        .expect("str.len(mid)");

    // Build in_range: (and (>= i 0) (< i len_s) (> l 0))
    //   i.e. (and (>= i 0) (< i len_s) (> l 0))
    let zero_int = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);

    let ge_i_zero = ctx
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[i, zero_int])
        .expect("i >= 0");
    let lt_i_lens = ctx
        .mk_app(Op::Builtin(BuiltinOp::Lt), &[i, len_s])
        .expect("i < len_s");
    let gt_l_zero = ctx
        .mk_app(Op::Builtin(BuiltinOp::Gt), &[l, zero_int])
        .expect("l > 0");

    let in_range = ctx
        .mk_app(Op::Builtin(BuiltinOp::And), &[ge_i_zero, lt_i_lens, gt_l_zero])
        .expect("in_range");

    // Build min_l_rem = ite(l <= len_s - i, l, len_s - i)
    let rem = ctx
        .mk_app(Op::Builtin(BuiltinOp::Sub), &[len_s, i])
        .expect("len_s - i");
    let l_le_rem = ctx
        .mk_app(Op::Builtin(BuiltinOp::Le), &[l, rem])
        .expect("l <= rem");
    let min_l_rem = ctx
        .mk_app(Op::Builtin(BuiltinOp::Ite), &[l_le_rem, l, rem])
        .expect("min(l, rem)");

    // Guard 1: s = pre ++ mid ++ post
    let concat_pre_mid = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[pre, mid])
        .expect("pre ++ mid");
    let concat_all = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[concat_pre_mid, post])
        .expect("(pre++mid) ++ post");
    let guard_concat = ctx.mk_eq(s, concat_all).expect("s = pre++mid++post");

    // Guard 2: len(pre) = ite(in_range, i, 0)
    let len_pre_rhs = ctx
        .mk_app(Op::Builtin(BuiltinOp::Ite), &[in_range, i, zero_int])
        .expect("ite(in_range, i, 0)");
    let guard_len_pre = ctx
        .mk_eq(len_pre, len_pre_rhs)
        .expect("len(pre) = ite(...)");

    // Guard 3: len(mid) = ite(in_range, min_l_rem, 0)
    let len_mid_rhs = ctx
        .mk_app(
            Op::Builtin(BuiltinOp::Ite),
            &[in_range, min_l_rem, zero_int],
        )
        .expect("ite(in_range, min_l_rem, 0)");
    let guard_len_mid = ctx
        .mk_eq(len_mid, len_mid_rhs)
        .expect("len(mid) = ite(...)");

    guards.push(guard_concat);
    guards.push(guard_len_pre);
    guards.push(guard_len_mid);

    // The result is `mid`.
    mid
}

/// Bottom-up rewrite of term `t`: whenever a `str.at` or `str.substr`
/// application is encountered, replace it with a fresh `mid` variable and
/// append the guard constraints to `guards`.  Returns the rewritten term.
fn rewrite(ctx: &mut Context, t: TermId, guards: &mut Vec<TermId>) -> TermId {
    match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            // First rewrite all children bottom-up.
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> = children
                .iter()
                .map(|&c| rewrite(ctx, c, guards))
                .collect();

            match op {
                Op::Builtin(BuiltinOp::StrSubstr) => {
                    // str.substr(s, i, l) — children are [s, i, l]
                    let s = new_children[0];
                    let i = new_children[1];
                    let l = new_children[2];
                    encode_substr(ctx, s, i, l, guards)
                }
                Op::Builtin(BuiltinOp::StrAt) => {
                    // str.at(s, i) ≡ str.substr(s, i, 1)
                    let s = new_children[0];
                    let i = new_children[1];
                    let int_s = ctx.int_sort();
                    let one = ctx.mk_numeral(
                        shinri_core::Rational::from_int(1i128.into()),
                        int_s,
                    );
                    encode_substr(ctx, s, i, one, guards)
                }
                _ => {
                    // Rebuild with potentially-rewritten children.
                    let changed = new_children
                        .iter()
                        .zip(children.iter())
                        .any(|(nc, oc)| nc != oc);
                    if changed {
                        ctx.mk_app(op, &new_children)
                            .expect("rewrite: well-sorted rebuild")
                    } else {
                        t
                    }
                }
            }
        }
    }
}

/// Pre-pass entry point.
///
/// Rewrites every `str.at` / `str.substr` in `assertions` (bottom-up) to a
/// fresh String variable, collecting the guard constraints that define it.
/// Returns `(rewritten assertions) ++ (guard atoms)`.
///
/// Non-string queries (no `StrAt`/`StrSubstr`/`StrConcat`/`StrLen`) are
/// returned unchanged.
pub fn reduce_assertions(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut guards: Vec<TermId> = Vec::new();
    let rewritten: Vec<TermId> = assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut guards))
        .collect();
    let mut out = rewritten;
    out.extend(guards);
    out
}

#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};

    use crate::reduce::reduce_assertions;

    #[test]
    fn substr_is_replaced_by_fresh_var_with_guards() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = {
            let f = ctx.declare_fun("s", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let i = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), ctx.int_sort());
        let one = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), ctx.int_sort());
        let ss = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrSubstr), &[s, i, one])
            .unwrap();
        let lit = ctx.mk_string_const("b");
        let atom = ctx.mk_eq(ss, lit).unwrap();
        let out = reduce_assertions(&mut ctx, &[atom]);
        // The reduced set must contain MORE than one assertion (guards added) and
        // must no longer contain a raw str.substr application at the top of `atom`'s replacement.
        assert!(out.len() > 1, "guards must be appended");
        assert!(
            out.iter()
                .all(|&a| !crate::reduce::contains_substr_or_at(&ctx, a)),
            "no str.substr/str.at may remain after reduction"
        );
    }

    #[test]
    fn str_at_delegates_to_substr_encoding() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = {
            let f = ctx.declare_fun("s_at", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let i = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), ctx.int_sort());
        let at = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrAt), &[s, i])
            .unwrap();
        let lit = ctx.mk_string_const("a");
        let atom = ctx.mk_eq(at, lit).unwrap();
        let out = reduce_assertions(&mut ctx, &[atom]);
        assert!(out.len() > 1, "guards must be appended for str.at");
        assert!(
            out.iter()
                .all(|&a| !crate::reduce::contains_substr_or_at(&ctx, a)),
            "no str.at may remain after reduction"
        );
    }

    #[test]
    fn non_string_query_is_untouched() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let x = {
            let f = ctx.declare_fun("x_ns", &[], int);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int);
        let gt = ctx
            .mk_app(Op::Builtin(BuiltinOp::Gt), &[x, zero])
            .unwrap();
        let out = reduce_assertions(&mut ctx, &[gt]);
        assert_eq!(out.len(), 1, "non-string query must not get extra guards");
        assert_eq!(out[0], gt, "assertion must be unchanged");
    }

    #[test]
    fn nested_substr_both_replaced() {
        // (= (str.substr (str.substr s 0 3) 1 1) "x")
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let s = {
            let f = ctx.declare_fun("s_nested", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
        let one = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
        let three = ctx.mk_numeral(shinri_core::Rational::from_int(3i128.into()), int_s);
        let inner = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrSubstr), &[s, zero, three])
            .unwrap();
        let outer = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrSubstr), &[inner, one, one])
            .unwrap();
        let lit = ctx.mk_string_const("x");
        let atom = ctx.mk_eq(outer, lit).unwrap();
        let out = reduce_assertions(&mut ctx, &[atom]);
        // Two substr calls = at least 2 × 3 = 6 guards; total > 1.
        assert!(
            out.len() > 1,
            "nested substr must produce guards, got {}",
            out.len()
        );
        assert!(
            out.iter()
                .all(|&a| !crate::reduce::contains_substr_or_at(&ctx, a)),
            "no str.substr may remain after nested reduction"
        );
    }
}
