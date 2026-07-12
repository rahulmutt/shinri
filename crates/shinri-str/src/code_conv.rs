//! Slice 18 pre-pass: `str.to_code` / `str.from_code` / `str.is_digit` —
//! exact rewriting + fence.
//!
//! Every rewrite in this module is a FULL logical equivalence — sound at any
//! position, any polarity, any occurrence count. No model repair, no length
//! pins, no occurrence analysis (unlike int_conv's slice-17 stage): the
//! fragment is decided by a SINGLE bottom-up pass plus a presence fence.
//!
//! Stages (run by the solver's string-path seam, right after int_conv):
//! 1. [`rewrite_code_conv`] — bottom-up memoized rewrite applying the whole
//!    spec catalog (R1–R10): literal folds, both roundtrip rewrites,
//!    constant-RHS atom equivalences (either orientation), and `str.is_digit`
//!    expansion. (Lands in Tasks 2–3.)
//! 2. [`has_unreduced_code_conv`] — presence fence: any surviving
//!    application ⇒ the solver returns a sound `Unknown`.
//!
//! Representational fence: `Box<str>` cannot hold surrogate code points
//! (`0xD800..=0xDFFF`) even though the SMT-LIB alphabet includes them —
//! `from_code(<surrogate k>)` never folds and `to_code(s) = <surrogate k>`
//! never rewrites; both survive to the fence. Input literals cannot contain
//! surrogates (the parser does not decode `\u{...}` escapes), so the
//! literal side of an equality needs no surrogate case.

use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// Largest SMT-LIB string character (inclusive): U+2FFFF.
pub const MAX_CODE: i128 = 0x2FFFF;

/// Presence fence: true iff any `str.to_code` / `str.from_code` /
/// `str.is_digit` application survived [`rewrite_code_conv`].
pub fn has_unreduced_code_conv(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(
                    op,
                    Op::Builtin(
                        BuiltinOp::StrToCode | BuiltinOp::StrFromCode | BuiltinOp::StrIsDigit
                    )
                ) || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}
