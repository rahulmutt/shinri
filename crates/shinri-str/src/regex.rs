//! Slice 19 pre-pass: `str.in_re` over SMT-LIB regular expressions —
//! ground evaluation by Brzozowski derivatives + presence fence.
//!
//! Decided fragment: `str.in_re(s, R)` where `s` is a string literal and `R`
//! is a CONSTANT regex (every `str.to_re` argument and every `re.range`
//! endpoint is a literal). The atom folds to true/false — evaluation, a full
//! logical equivalence at any polarity, any occurrence count. No model
//! repair, no fresh variables.
//!
//! Stages (run by the solver's string-path seam, right after code_conv):
//! 1. [`rewrite_ground_in_re`] — bottom-up memoized pass folding every ground
//!    membership atom. (Lands in Task 3.)
//! 2. [`has_unreduced_regex`] — presence fence: any surviving `str.in_re`
//!    application or RegLan-sorted subterm ⇒ the solver returns a sound
//!    `Unknown`. The solver additionally fences any query that DECLARES a
//!    RegLan-sorted symbol (`Context::any_fun_sig_mentions`).
//!
//! Above-alphabet fence: Rust literals can hold chars in
//! `0x30000..=0x10FFFF`, outside the SMT-LIB alphabet — if the ground string
//! or a range endpoint contains one, the fold is skipped (→ fence) rather
//! than guessing semantics.

use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// Largest SMT-LIB string character (inclusive): U+2FFFF.
#[allow(dead_code)] // used by the ground-evaluation fold, added in Task 2/3
const MAX_CODE: u32 = 0x2FFFF;

/// Presence fence: true iff any `str.in_re` application or RegLan-sorted
/// subterm survives in `assertions`. Any hit ⇒ sound `Unknown`.
pub fn has_unreduced_regex(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        if ctx.sort_of(t) == ctx.reglan_sort() {
            return true;
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(BuiltinOp::StrInRe))
                    || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A nullary uninterpreted constant of the given sort (codebase pattern).
    fn nullary(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn in_re(ctx: &mut Context, s: TermId, r: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, r])
            .unwrap()
    }

    fn to_re(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToRe), &[s]).unwrap()
    }

    #[test]
    fn fence_detects_in_re_and_reglan_subterms() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let re_s = ctx.reglan_sort();
        let s = nullary(&mut ctx, "s", str_s);

        // str.in_re app → fenced.
        let lit = ctx.mk_string_const("a");
        let r = to_re(&mut ctx, lit);
        let atom = in_re(&mut ctx, s, r);
        assert!(has_unreduced_regex(&ctx, &[atom]));

        // Bare RegLan equality → fenced (RegLan-sorted subterms).
        let rv = nullary(&mut ctx, "r", re_s);
        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let eq = ctx.mk_eq(rv, none).unwrap();
        assert!(has_unreduced_regex(&ctx, &[eq]));

        // Plain string assertion → NOT fenced.
        let b = ctx.mk_string_const("b");
        let seq = ctx.mk_eq(s, b).unwrap();
        assert!(!has_unreduced_regex(&ctx, &[seq]));
    }
}
