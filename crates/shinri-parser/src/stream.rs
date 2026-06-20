//! Incremental, owning streaming parser for SMT-LIB scripts. Accumulates input
//! and emits one complete command at a time, using token-level paren-depth
//! boundary detection that reuses the real lexer (so `)` inside strings,
//! `|quoted symbols|`, and `;comments` never create a false command boundary).

use crate::lexer::{Lexer, Token};

/// Result of scanning a buffer for the end of the first top-level command.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Scan {
    /// A balanced top-level form occupies `s[..end]` (byte offset past its `)`).
    Complete(usize),
    /// An opening `(` was seen but not yet closed — feed more input.
    NeedMore,
    /// Only whitespace/comments so far — nothing to parse yet.
    Empty,
}

/// Find the end of the first complete top-level parenthesized command in `s`.
pub(crate) fn scan_command_end(s: &str) -> Scan {
    let mut lx = Lexer::new(s);
    let mut depth: i32 = 0;
    let mut saw_open = false;
    while let Some((tok, span)) = lx.next_spanned() {
        match tok {
            Ok(Token::LParen) => {
                depth += 1;
                saw_open = true;
            }
            Ok(Token::RParen) => {
                depth -= 1;
                if depth <= 0 {
                    return Scan::Complete(span.end);
                }
            }
            _ => {}
        }
    }
    if saw_open {
        Scan::NeedMore
    } else {
        Scan::Empty
    }
}

#[cfg(test)]
mod scan_tests {
    use super::*;

    #[test]
    fn complete_simple_command() {
        assert_eq!(scan_command_end("(check-sat)"), Scan::Complete(11));
    }

    #[test]
    fn nested_parens_close_at_outermost() {
        let s = "(assert (> x 0))";
        assert_eq!(scan_command_end(s), Scan::Complete(s.len()));
    }

    #[test]
    fn unclosed_is_need_more() {
        assert_eq!(scan_command_end("(assert (> x"), Scan::NeedMore);
    }

    #[test]
    fn whitespace_and_comment_only_is_empty() {
        assert_eq!(scan_command_end("  ; a comment\n  "), Scan::Empty);
    }

    #[test]
    fn close_paren_inside_string_is_not_a_boundary() {
        // The ')' lives inside a string literal; the command ends at the real ')'.
        let s = "(echo \")\")";
        assert_eq!(scan_command_end(s), Scan::Complete(s.len()));
    }

    #[test]
    fn close_paren_inside_comment_is_not_a_boundary() {
        let s = "(check-sat) ; ) trailing\n";
        assert_eq!(scan_command_end(s), Scan::Complete(11));
    }

    #[test]
    fn second_command_remains_after_first() {
        // Only the first form is reported; the caller advances and rescans.
        assert_eq!(scan_command_end("(check-sat)(exit)"), Scan::Complete(11));
    }
}
