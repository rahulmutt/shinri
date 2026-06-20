//! Incremental, owning streaming parser for SMT-LIB scripts. Accumulates input
//! and emits one complete command at a time, using token-level paren-depth
//! boundary detection that reuses the real lexer (so `)` inside strings,
//! `|quoted symbols|`, and `;comments` never create a false command boundary).

use crate::env::Env;
use crate::lexer::{Lexer, Token};
use crate::parser::{Diagnostic, Parser};
use shinri_core::Context;
use shinri_frontend::Command;

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

/// One pull from a [`StreamingParser`].
#[derive(Debug)]
pub enum StreamItem {
    /// A complete command (or the diagnostic from a malformed one).
    Command(Result<Command, Diagnostic>),
    /// The buffer holds only a partial command — feed more bytes.
    NeedMore,
    /// `(exit)` was seen, or input ended with no trailing partial command.
    Done,
}

/// An owning SMT-LIB command stream. Feed bytes with [`push_str`], pull
/// commands with [`next_command`] until `NeedMore`/`Done`, then call
/// [`finish`] once at input EOF.
///
/// [`push_str`]: StreamingParser::push_str
/// [`next_command`]: StreamingParser::next_command
/// [`finish`]: StreamingParser::finish
pub struct StreamingParser {
    buf: String,
    consumed: usize,
    env: Env,
    stopped: bool,
}

impl Default for StreamingParser {
    fn default() -> Self {
        Self::new()
    }
}

impl StreamingParser {
    pub fn new() -> Self {
        StreamingParser {
            buf: String::new(),
            consumed: 0,
            env: Env::new(),
            stopped: false,
        }
    }

    /// Append a chunk (a line, or a whole file) to the input buffer.
    pub fn push_str(&mut self, chunk: &str) {
        self.buf.push_str(chunk);
    }

    /// Pull the next complete command, or signal that more input is needed.
    pub fn next_command(&mut self, ctx: &mut Context) -> StreamItem {
        loop {
            if self.stopped {
                return StreamItem::Done;
            }
            let base = self.consumed;
            let rel_end = match scan_command_end(&self.buf[base..]) {
                Scan::Complete(end) => end,
                Scan::NeedMore | Scan::Empty => return StreamItem::NeedMore,
            };

            // Parse exactly this command's slice with a transient parser that
            // borrows the persistent env, then take the env back.
            let cmd_text = self.buf[base..base + rel_end].to_string();
            let env = std::mem::replace(&mut self.env, Env::new());
            let mut p = Parser::with_env(&cmd_text, env);
            let result = p.next_command(ctx);
            self.env = p.into_env();
            self.consumed = base + rel_end;

            match result {
                // define-fun / stray form: no IR command — advance and rescan.
                None => continue,
                Some(Ok(cmd)) => {
                    if matches!(cmd, Command::Exit) {
                        self.stopped = true;
                    }
                    return StreamItem::Command(Ok(cmd));
                }
                Some(Err(mut d)) => {
                    // Re-base the span from slice-local to buffer-global coords.
                    d.span.start += base;
                    d.span.end += base;
                    return StreamItem::Command(Err(d));
                }
            }
        }
    }

    /// Call once when input ends. If a non-whitespace partial command remains,
    /// emits exactly one error; otherwise `Done`.
    pub fn finish(&mut self, _ctx: &mut Context) -> StreamItem {
        if self.stopped {
            return StreamItem::Done;
        }
        if self.buf[self.consumed..].trim().is_empty() {
            self.stopped = true;
            StreamItem::Done
        } else {
            let at = self.buf.len();
            self.stopped = true;
            StreamItem::Command(Err(Diagnostic {
                span: at..at,
                message: "unexpected end of input".to_string(),
            }))
        }
    }
}

#[cfg(test)]
mod streaming_tests {
    use super::{StreamItem, StreamingParser};
    use shinri_core::Context;
    use shinri_frontend::Command;

    fn is_cmd(item: &StreamItem, pred: impl Fn(&Command) -> bool) -> bool {
        matches!(item, StreamItem::Command(Ok(c)) if pred(c))
    }

    #[test]
    fn command_split_across_chunks() {
        let mut ctx = Context::new();
        let mut sp = StreamingParser::new();
        sp.push_str("(check");
        assert!(matches!(sp.next_command(&mut ctx), StreamItem::NeedMore));
        sp.push_str("-sat)");
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| *c == Command::CheckSat));
    }

    #[test]
    fn env_persists_across_commands() {
        let mut ctx = Context::new();
        let mut sp = StreamingParser::new();
        sp.push_str("(declare-fun a () Bool)");
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| matches!(
            c,
            Command::DeclareFun { .. }
        )));
        // `a` resolves only if the env from the first command persisted.
        sp.push_str("(assert a)");
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| matches!(
            c,
            Command::Assert(_)
        )));
    }

    #[test]
    fn multiple_commands_in_one_chunk_drain() {
        let mut ctx = Context::new();
        let mut sp = StreamingParser::new();
        sp.push_str("(check-sat)(exit)");
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| *c == Command::CheckSat));
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| *c == Command::Exit));
        assert!(matches!(sp.next_command(&mut ctx), StreamItem::Done));
    }

    #[test]
    fn define_fun_emits_no_command_but_advances() {
        let mut ctx = Context::new();
        let mut sp = StreamingParser::new();
        // define-fun emits no IR command; the next form must still parse.
        sp.push_str("(define-fun g () Bool true)(check-sat)");
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| *c == Command::CheckSat));
    }

    #[test]
    fn finish_on_partial_reports_one_error() {
        let mut ctx = Context::new();
        let mut sp = StreamingParser::new();
        sp.push_str("(check-sat");
        assert!(matches!(sp.next_command(&mut ctx), StreamItem::NeedMore));
        match sp.finish(&mut ctx) {
            StreamItem::Command(Err(d)) => assert!(d.message.contains("end of input")),
            other => panic!("expected error, got {other:?}"),
        }
        assert!(matches!(sp.finish(&mut ctx), StreamItem::Done));
    }

    #[test]
    fn finish_on_clean_buffer_is_done() {
        let mut ctx = Context::new();
        let mut sp = StreamingParser::new();
        sp.push_str("(check-sat)\n");
        let _ = sp.next_command(&mut ctx);
        assert!(matches!(sp.finish(&mut ctx), StreamItem::Done));
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
