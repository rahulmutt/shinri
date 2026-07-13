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

/// If `t` is an integer numeral, return its value as `i128`. Non-integer
/// (fractional) or non-numeral terms return `None`.
pub(crate) fn int_numeral(ctx: &Context, t: TermId) -> Option<i128> {
    let r = ctx.numeral_value(t)?;
    // Reject non-integers: denominator must be exactly 1.
    if r.denom().to_i128() != Some(1) {
        return None;
    }
    r.numer().to_i128()
}

/// Concretely evaluate `(str.substr s i l)` when `s` is a string constant and
/// `i`, `l` are integer numerals — the SMT-LIB 2.6 semantics, by Unicode scalar
/// (char) index. Returns the resulting constant string, or `None` if any operand
/// is not a literal/numeral. This is the SOUND fast path that avoids the
/// (semi-decidable, diverging) Nielsen word-equation expansion the generic
/// `pre++mid++post` encoding would otherwise trigger for constant inputs.
///
/// Semantics: if `0 <= i < |s|` and `l > 0`, result = `s[i .. i+min(l, |s|-i)]`;
/// otherwise the empty string.
fn eval_substr_const(ctx: &Context, s: TermId, i: TermId, l: TermId) -> Option<String> {
    let sv = ctx.string_const_value(s)?;
    let iv = int_numeral(ctx, i)?;
    let lv = int_numeral(ctx, l)?;
    let chars: Vec<char> = sv.chars().collect();
    let n = chars.len() as i128;
    if iv < 0 || iv >= n || lv <= 0 {
        return Some(String::new());
    }
    let start = iv as usize;
    let take = std::cmp::min(lv, n - iv) as usize;
    Some(chars[start..start + take].iter().collect())
}

// Global counter for fresh variable names so that multiple calls across
// multiple assertions never collide. Relaxed ordering is sufficient here:
// the counter is used only for name uniqueness (no ordering or identity
// dependency — any unique name is acceptable regardless of sequencing).
static FRESH_CTR: AtomicU32 = AtomicU32::new(0);

pub(crate) fn next_fresh() -> u32 {
    FRESH_CTR.fetch_add(1, Ordering::Relaxed)
}

/// Returns `true` if `t` (or any subterm) is a `str.at`/`str.substr` application
/// that will NOT constant-fold — i.e. whose base is not a string constant or whose
/// index/length operands are not integer numerals.
///
/// Such applications are reduced to the generic `pre++mid++post` + length-guard
/// encoding, which the engine's String↔Arith seam does NOT decide soundly: it can
/// diverge OR report a SPURIOUS UNSAT (e.g. `(str.at s 2) = s`, sat in SMT-LIB but
/// reported unsat — a documented, pre-existing flaw). The solver fences any query
/// containing such an application to a SOUND `Unknown` rather than risk a wrong
/// verdict. Constant-base/constant-index applications (the soundly-decidable
/// fast path, e.g. `(str.substr "abc" 1 1)`) fold to a literal and are EXCLUDED
/// here, so the soundly-supported substr fragment is unaffected.
pub fn has_unfoldable_substr_or_at(ctx: &Context, t: TermId) -> bool {
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            let children = ctx.children(*args).to_vec();
            let foldable = match op {
                Op::Builtin(BuiltinOp::StrSubstr) => {
                    eval_substr_const(ctx, children[0], children[1], children[2]).is_some()
                }
                Op::Builtin(BuiltinOp::StrAt) => {
                    // str.at(s,i) ≡ str.substr(s,i,1): folds iff base const & i numeral.
                    ctx.string_const_value(children[0]).is_some()
                        && int_numeral(ctx, children[1]).is_some()
                }
                _ => true, // not a substr/at op: "foldable" is irrelevant here
            };
            let self_unfoldable =
                matches!(op, Op::Builtin(BuiltinOp::StrAt | BuiltinOp::StrSubstr)) && !foldable;
            self_unfoldable
                || children
                    .iter()
                    .any(|&c| has_unfoldable_substr_or_at(ctx, c))
        }
        TermNode::Const { .. } => false,
    }
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
            children.iter().any(|&c| contains_substr_or_at(ctx, c))
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
                        | BuiltinOp::StrPrefixOf
                        | BuiltinOp::StrSuffixOf
                        | BuiltinOp::StrContains
                        | BuiltinOp::StrIndexOf
                        | BuiltinOp::StrReplace
                        | BuiltinOp::StrToInt
                        | BuiltinOp::StrFromInt
                        | BuiltinOp::StrToCode
                        | BuiltinOp::StrFromCode
                        | BuiltinOp::StrIsDigit
                        | BuiltinOp::StrInRe
                        | BuiltinOp::StrToRe
                        | BuiltinOp::ReNone
                        | BuiltinOp::ReAll
                        | BuiltinOp::ReAllChar
                        | BuiltinOp::ReConcat
                        | BuiltinOp::ReUnion
                        | BuiltinOp::ReInter
                        | BuiltinOp::ReDiff
                        | BuiltinOp::ReStar
                        | BuiltinOp::RePlus
                        | BuiltinOp::ReOpt
                        | BuiltinOp::ReComp
                        | BuiltinOp::ReRange
                        | BuiltinOp::ReLoop { .. }
                        | BuiltinOp::RePow(_)
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
        .mk_app(
            Op::Builtin(BuiltinOp::And),
            &[ge_i_zero, lt_i_lens, gt_l_zero],
        )
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
            let new_children: Vec<TermId> =
                children.iter().map(|&c| rewrite(ctx, c, guards)).collect();

            match op {
                Op::Builtin(BuiltinOp::StrSubstr) => {
                    // str.substr(s, i, l) — children are [s, i, l]
                    let s = new_children[0];
                    let i = new_children[1];
                    let l = new_children[2];
                    // SOUND fast path: fully-constant arguments fold to a literal,
                    // sidestepping the diverging Nielsen expansion of the generic
                    // `pre++mid++post` encoding over a constant string.
                    if let Some(v) = eval_substr_const(ctx, s, i, l) {
                        ctx.mk_string_const(&v)
                    } else {
                        encode_substr(ctx, s, i, l, guards)
                    }
                }
                Op::Builtin(BuiltinOp::StrAt) => {
                    // str.at(s, i) ≡ str.substr(s, i, 1)
                    let s = new_children[0];
                    let i = new_children[1];
                    let int_s = ctx.int_sort();
                    let one = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
                    if let Some(v) = eval_substr_const(ctx, s, i, one) {
                        ctx.mk_string_const(&v)
                    } else {
                        encode_substr(ctx, s, i, one, guards)
                    }
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
/// This pre-pass triggers on ANY query that contains a String-sorted term or
/// String-sorted operation (see `any_has_string_op`). It is a no-op (returns
/// assertions unchanged, structurally) when no `str.at` / `str.substr`
/// application is present.
///
/// When `str.at` / `str.substr` are present the pass performs two rewrites:
///
/// 1. Rewrites every `str.at` / `str.substr` in `assertions` (bottom-up) to a
///    fresh String variable, collecting the guard constraints that define it.
/// 2. Eliminates every NON-Boolean `(ite c a b)` term (introduced by the substr
///    guards as `(ite in_range i 0)` etc.) into a fresh variable `w` plus the
///    implications `c → w=a` and `¬c → w=b`. The core solver does not interpret
///    term-level ITE — arith/EUF treat `(ite …)` as an opaque value, so the
///    length guards would be unconstrained (wrong SAT / divergent word-equation
///    search). This pass makes them effective using only Bool structure +
///    equalities the theories already handle.
///
/// Returns `(rewritten assertions) ++ (guard atoms) ++ (ite-defining atoms)`.
pub fn reduce_assertions(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut guards: Vec<TermId> = Vec::new();
    let rewritten: Vec<TermId> = assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut guards))
        .collect();
    let mut out = rewritten;
    out.extend(guards);

    // Eliminate non-Boolean ITE terms across the whole reduced set.
    let mut ite_defs: Vec<TermId> = Vec::new();
    let mut memo = std::collections::HashMap::new();
    let elim: Vec<TermId> = out
        .iter()
        .map(|&a| elim_term_ite(ctx, a, &mut ite_defs, &mut memo))
        .collect();
    let mut result = elim;
    result.extend(ite_defs);
    result
}

/// Bottom-up: replace every non-Boolean `(ite c a b)` subterm with a fresh
/// variable `w` (of the ITE's sort) and append `(=> c (= w a))` and
/// `(=> (not c) (= w b))` to `defs`. Boolean-sorted ITEs are left intact (the
/// Tseitin encoder handles those). Memoized on TermId so shared ITEs get one var.
fn elim_term_ite(
    ctx: &mut Context,
    t: TermId,
    defs: &mut Vec<TermId>,
    memo: &mut std::collections::HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> = children
                .iter()
                .map(|&c| elim_term_ite(ctx, c, defs, memo))
                .collect();

            if matches!(op, Op::Builtin(BuiltinOp::Ite)) && ctx.sort_of(t) != ctx.bool_sort() {
                // Non-Boolean ITE: introduce a fresh var and two implications.
                let cond = new_children[0];
                let then_b = new_children[1];
                let else_b = new_children[2];
                let sort = ctx.sort_of(t);
                let n = next_fresh();
                let w_sym = ctx.declare_fun(&format!("!ite{n}"), &[], sort);
                let w = ctx
                    .mk_app(Op::Uninterpreted(w_sym), &[])
                    .expect("fresh ite var");
                let eq_then = ctx.mk_eq(w, then_b).expect("w = then");
                let eq_else = ctx.mk_eq(w, else_b).expect("w = else");
                let not_cond = ctx
                    .mk_app(Op::Builtin(BuiltinOp::Not), &[cond])
                    .expect("not cond");
                let imp_then = ctx
                    .mk_app(Op::Builtin(BuiltinOp::Implies), &[cond, eq_then])
                    .expect("c => w=then");
                let imp_else = ctx
                    .mk_app(Op::Builtin(BuiltinOp::Implies), &[not_cond, eq_else])
                    .expect("¬c => w=else");
                defs.push(imp_then);
                defs.push(imp_else);
                w
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(nc, oc)| nc != oc);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("rebuild after ite elim")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
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
        let i = ctx.mk_numeral(
            shinri_core::Rational::from_int(1i128.into()),
            ctx.int_sort(),
        );
        let one = ctx.mk_numeral(
            shinri_core::Rational::from_int(1i128.into()),
            ctx.int_sort(),
        );
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
        let i = ctx.mk_numeral(
            shinri_core::Rational::from_int(0i128.into()),
            ctx.int_sort(),
        );
        let at = ctx.mk_app(Op::Builtin(BuiltinOp::StrAt), &[s, i]).unwrap();
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
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[x, zero]).unwrap();
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
