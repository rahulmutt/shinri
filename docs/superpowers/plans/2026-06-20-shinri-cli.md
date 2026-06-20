# shinri-cli Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `crates/shinri-cli`, a runnable `shinri` binary that streams SMT-LIB 2.6 scripts from a file or stdin through the existing parser + solver with full batch/interactive presentation semantics.

**Architecture:** A new owning `StreamingParser` in `shinri-parser` accumulates input and emits complete commands using token-level paren-depth boundary detection (reusing the real `logos` lexer). A thin `shinri-cli` driver feeds bytes (whole file, or stdin line-by-line), maps each `CommandResponse` to output, and owns all presentation state (`:print-success`, output channels). The `Solver` is untouched — it stays a pure embeddable library.

**Tech Stack:** Rust 2021, `logos` lexer, no new external dependencies (arg parsing is hand-rolled).

## Global Constraints

- **Rust edition 2021, `rust-version = "1.96.0"`** (workspace-pinned; copy `edition.workspace = true` etc. in the new crate manifest).
- **Pure-Rust, zero new external deps in the shipping build.** `shinri-cli` depends only on the path crates `shinri-solver`, `shinri-parser`, `shinri-frontend`. Argument parsing is hand-rolled. No `clap`, no micro-crates.
- **Soundness/presentation split:** `Solver` must not gain presentation state. `:print-success` and output channels live entirely in the CLI driver.
- **No panics reach the user:** the driver performs only total mappings over `StreamItem` and `CommandResponse`.
- **`:print-success` default is `true`** (SMT-LIB 2.6 standard default).
- **Binary name is `shinri`** (`[[bin]] name = "shinri"`).
- Reference spec: `docs/superpowers/specs/2026-06-20-shinri-cli-design.md`.

---

## File Structure

**Modified (parser crate):**
- `crates/shinri-parser/src/parser.rs` — fix `parse_attr` value capture; add `pub(crate)` `Parser::with_env`/`into_env`.
- `crates/shinri-parser/src/lib.rs` — declare `mod stream;` and re-export `StreamingParser`, `StreamItem`.

**Created (parser crate):**
- `crates/shinri-parser/src/stream.rs` — `scan_command_end` boundary scanner + `StreamingParser`/`StreamItem`.

**Created (new cli crate):**
- `crates/shinri-cli/Cargo.toml` — manifest + `[[bin]] name = "shinri"`.
- `crates/shinri-cli/src/main.rs` — entry: args → input selection → driver → exit code.
- `crates/shinri-cli/src/args.rs` — hand-rolled arg parser.
- `crates/shinri-cli/src/driver.rs` — `OutChannel`, `Presentation`, `Driver` streaming loop.
- `crates/shinri-cli/tests/cli.rs` — black-box integration tests over the built binary.

**Modified (workspace):**
- `Cargo.toml` — add `crates/shinri-cli` to `members`.

---

## Task 1: Fix `parse_attr` to capture semantic option values

The driver needs to read `:print-success true/false` and channel names. Today `parse_attr` stores `format!("{tok:?}")` (Debug form, e.g. the string `Symbol("true")`), which is unusable. Capture the token's *value text* instead (inner string for symbols/numerals/keywords; quote-stripped contents for strings).

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs` (the `parse_attr` method near line 706, and add a free helper)
- Test: `crates/shinri-parser/src/parser.rs` (new `#[cfg(test)] mod attr_tests`)

**Interfaces:**
- Consumes: existing `Token` enum (`crate::lexer::Token`), `shinri_frontend::AttrValue::Token(Option<String>)`.
- Produces: `Command::SetOption { keyword, value }` where `value` is `AttrValue::Token(Some("<value text>"))` — `true`/`false` for booleans, quote-stripped contents for string literals.

- [ ] **Step 1: Write the failing tests**

Add to `crates/shinri-parser/src/parser.rs`:

```rust
#[cfg(test)]
mod attr_tests {
    use super::Parser;
    use shinri_core::Context;
    use shinri_frontend::{AttrValue, Command};

    #[test]
    fn set_option_bool_value_is_semantic_text() {
        let mut ctx = Context::new();
        let mut p = Parser::new("(set-option :print-success false)");
        let cmd = p.next_command(&mut ctx).unwrap().unwrap();
        assert_eq!(
            cmd,
            Command::SetOption {
                keyword: ":print-success".into(),
                value: AttrValue::Token(Some("false".into())),
            }
        );
    }

    #[test]
    fn set_option_string_value_strips_quotes() {
        let mut ctx = Context::new();
        let mut p = Parser::new("(set-option :regular-output-channel \"out.txt\")");
        let cmd = p.next_command(&mut ctx).unwrap().unwrap();
        assert_eq!(
            cmd,
            Command::SetOption {
                keyword: ":regular-output-channel".into(),
                value: AttrValue::Token(Some("out.txt".into())),
            }
        );
    }

    #[test]
    fn set_option_bare_keyword_has_no_value() {
        let mut ctx = Context::new();
        let mut p = Parser::new("(set-info :some-flag)");
        let cmd = p.next_command(&mut ctx).unwrap().unwrap();
        assert_eq!(
            cmd,
            Command::SetInfo {
                keyword: ":some-flag".into(),
                value: AttrValue::Token(None),
            }
        );
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-parser attr_tests`
Expected: FAIL — `set_option_bool_value_is_semantic_text` gets `Some("Symbol(\"false\")")`, not `Some("false")`.

- [ ] **Step 3: Add the value-text helper**

Add this free function in `crates/shinri-parser/src/parser.rs` (e.g. just above `impl<'a> Parser<'a>`):

```rust
/// The semantic text of an attribute-value token: the inner string for
/// symbols/numerals/decimals/keywords/hex/bin, and the quote-stripped,
/// `""`-unescaped contents for string literals.
fn token_value_text(tok: &Token) -> String {
    match tok {
        Token::Symbol(s)
        | Token::Numeral(s)
        | Token::Decimal(s)
        | Token::Keyword(s)
        | Token::Hex(s)
        | Token::Bin(s) => s.clone(),
        Token::Str(s) => s[1..s.len() - 1].replace("\"\"", "\""),
        Token::LParen => "(".to_string(),
        Token::RParen => ")".to_string(),
    }
}
```

- [ ] **Step 4: Use the helper in `parse_attr`**

In `parse_attr`, replace the value-capture `match` arm. Change the block that currently reads:

```rust
        let val = match self.peek() {
            Some((Ok(Token::RParen), _)) | None => AttrValue::Token(None),
            Some((Ok(tok), _)) => {
                let text = format!("{tok:?}");
                self.bump();
                AttrValue::Token(Some(text))
            }
            Some((Err(()), sp)) => {
                return Err(Diagnostic::new(sp.clone(), "invalid attribute value"))
            }
        };
```

to:

```rust
        let val = match self.peek() {
            Some((Ok(Token::RParen), _)) | None => AttrValue::Token(None),
            Some((Err(()), sp)) => {
                return Err(Diagnostic::new(sp.clone(), "invalid attribute value"))
            }
            Some((Ok(_), _)) => {
                // A value token is present; consume it and capture its text.
                let (tok, _) = self.bump().expect("peek saw a token");
                let tok = tok.expect("peek saw Ok(token)");
                AttrValue::Token(Some(token_value_text(&tok)))
            }
        };
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-parser attr_tests`
Expected: PASS (3 passed).

- [ ] **Step 6: Run the whole parser crate to check for regressions**

Run: `cargo test -p shinri-parser`
Expected: PASS (no other test asserted the old Debug form — verified during planning).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-parser/src/parser.rs
git commit -m "fix(parser): capture semantic set-option/set-info attribute values"
```

---

## Task 2: Boundary scanner `scan_command_end`

A pure function that finds the byte offset of the first complete top-level command in a buffer, reusing the real lexer for paren-depth so strings/comments/quoted symbols cannot create false boundaries.

**Files:**
- Create: `crates/shinri-parser/src/stream.rs`
- Modify: `crates/shinri-parser/src/lib.rs` (add `mod stream;`)
- Test: `crates/shinri-parser/src/stream.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Consumes: `crate::lexer::{Lexer, Token}`.
- Produces: `pub(crate) enum Scan { Complete(usize), NeedMore, Empty }` and `pub(crate) fn scan_command_end(s: &str) -> Scan`. `Complete(end)` means a balanced top-level form occupies `s[..end]`.

- [ ] **Step 1: Create the file with the scanner and failing tests**

Create `crates/shinri-parser/src/stream.rs`:

```rust
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
```

- [ ] **Step 2: Wire the module into the crate**

In `crates/shinri-parser/src/lib.rs`, add `mod stream;` after the existing `mod parser;` line:

```rust
mod env;
mod lexer;
mod parser;
mod print;
mod stream;
```

- [ ] **Step 3: Run the scanner tests to verify they pass**

Run: `cargo test -p shinri-parser scan_tests`
Expected: PASS (7 passed). (The scanner is written and tested in one step because it is a single pure function; the tests above are the failing-then-passing cycle for it.)

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-parser/src/stream.rs crates/shinri-parser/src/lib.rs
git commit -m "feat(parser): token-level command-boundary scanner"
```

---

## Task 3: `StreamingParser` over the boundary scanner

The owning, fed-incrementally parser. Reuses `Parser` per command slice with a persistent `Env`.

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs` (add `with_env`/`into_env`)
- Modify: `crates/shinri-parser/src/stream.rs` (add `StreamingParser`, `StreamItem`)
- Modify: `crates/shinri-parser/src/lib.rs` (re-export)
- Test: `crates/shinri-parser/src/stream.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Consumes: `crate::parser::Parser::with_env(&str, Env) -> Parser`, `Parser::into_env(self) -> Env`, `Parser::next_command(&mut Context) -> Option<Result<Command, Diagnostic>>`, `scan_command_end`.
- Produces:
  - `pub struct StreamingParser` with `pub fn new()`, `pub fn push_str(&mut self, &str)`, `pub fn next_command(&mut self, &mut Context) -> StreamItem`, `pub fn finish(&mut self, &mut Context) -> StreamItem`.
  - `pub enum StreamItem { Command(Result<Command, Diagnostic>), NeedMore, Done }`.
  - **Driver contract:** call `next_command` repeatedly until it returns `NeedMore` (more bytes needed) or `Done` (`(exit)` seen); call `finish` once at input EOF.

- [ ] **Step 1: Add `with_env`/`into_env` to `Parser`**

In `crates/shinri-parser/src/parser.rs`, inside `impl<'a> Parser<'a>` (right after the existing `pub fn new`):

```rust
    /// Build a parser over `src` seeded with an existing resolution `env`.
    /// Used by `StreamingParser` to parse one command slice at a time while
    /// keeping declarations alive across commands.
    pub(crate) fn with_env(src: &'a str, env: Env) -> Self {
        Parser {
            lx: Lexer::new(src),
            peeked: None,
            env,
            eof: src.len(),
            stopped: false,
        }
    }

    /// Recover the resolution environment after parsing a command slice.
    pub(crate) fn into_env(self) -> Env {
        self.env
    }
```

- [ ] **Step 2: Write the failing `StreamingParser` tests**

Append to `crates/shinri-parser/src/stream.rs`:

```rust
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
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| matches!(c, Command::DeclareFun { .. })));
        // `a` resolves only if the env from the first command persisted.
        sp.push_str("(assert a)");
        assert!(is_cmd(&sp.next_command(&mut ctx), |c| matches!(c, Command::Assert(_))));
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
```

Note: `StreamItem` needs `#[derive(Debug)]` for the `panic!("{other:?}")` above.

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test -p shinri-parser streaming_tests`
Expected: FAIL to compile — `StreamingParser`/`StreamItem` do not exist yet.

- [ ] **Step 4: Implement `StreamingParser` and `StreamItem`**

Add to `crates/shinri-parser/src/stream.rs` (after `scan_command_end`, before the test modules). Add the imports at the top of the file alongside the existing `use crate::lexer::...`:

```rust
use crate::env::Env;
use crate::parser::{Diagnostic, Parser};
use shinri_core::Context;
use shinri_frontend::Command;
```

Then the types:

```rust
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
```

Note: `Diagnostic` is constructed via its public fields (`span`, `message`) since `Diagnostic::new` is module-private to `parser`.

- [ ] **Step 5: Re-export from the crate root**

In `crates/shinri-parser/src/lib.rs`, add:

```rust
pub use stream::{StreamItem, StreamingParser};
```

- [ ] **Step 6: Run the streaming tests to verify they pass**

Run: `cargo test -p shinri-parser streaming_tests`
Expected: PASS (6 passed).

- [ ] **Step 7: Run the whole parser crate**

Run: `cargo test -p shinri-parser`
Expected: PASS (all prior tests + new ones).

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-parser/src/parser.rs crates/shinri-parser/src/stream.rs crates/shinri-parser/src/lib.rs
git commit -m "feat(parser): StreamingParser — incremental command streaming"
```

---

## Task 4: `shinri-cli` crate scaffold + argument parsing

Create the binary crate with hand-rolled arg parsing. Deliverable: `shinri --version`, `shinri --help`, and bad-argument exit codes all work; real input is wired in Task 6.

**Files:**
- Create: `crates/shinri-cli/Cargo.toml`
- Create: `crates/shinri-cli/src/args.rs`
- Create: `crates/shinri-cli/src/main.rs`
- Create: `crates/shinri-cli/tests/cli.rs`
- Modify: `Cargo.toml` (workspace `members`)

**Interfaces:**
- Produces:
  - `args::parse_args<I: IntoIterator<Item = String>>(I) -> Result<Invocation, ArgError>`
  - `pub enum Invocation { Run { input: Input }, Help, Version }`
  - `pub enum Input { File(String), Stdin }`
  - `pub enum ArgError { Unknown(String), TooMany }`
  - `pub const USAGE: &str`
  - Note: `parse_args` receives args **without** the program name (caller passes `env::args().skip(1)`).

- [ ] **Step 1: Create the crate manifest**

Create `crates/shinri-cli/Cargo.toml`:

```toml
[package]
name = "shinri-cli"
version = "0.1.0"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[[bin]]
name = "shinri"
path = "src/main.rs"

[dependencies]
shinri-solver = { path = "../shinri-solver" }
shinri-parser = { path = "../shinri-parser" }
shinri-frontend = { path = "../shinri-frontend" }
```

- [ ] **Step 2: Add the crate to the workspace**

In the root `Cargo.toml`, add `"crates/shinri-cli"` to the `members` array:

```toml
members = ["crates/shinri-num", "crates/shinri-core", "crates/shinri-frontend", "crates/shinri-sat", "crates/shinri-theory", "crates/shinri-euf", "crates/shinri-solver", "crates/shinri-arith", "crates/shinri-parser", "crates/shinri-cli"]
```

- [ ] **Step 3: Write `args.rs` with failing unit tests**

Create `crates/shinri-cli/src/args.rs`:

```rust
//! Hand-rolled command-line argument parsing (no external deps).

#[derive(Debug, PartialEq, Eq)]
pub enum Input {
    File(String),
    Stdin,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Invocation {
    Run { input: Input },
    Help,
    Version,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ArgError {
    Unknown(String),
    TooMany,
}

pub const USAGE: &str = "\
Usage: shinri [FILE]

Read an SMT-LIB 2.6 script from FILE, or from stdin if no FILE is given.

Options:
  -h, --help       Print this help and exit
  -V, --version    Print version and exit
";

/// Parse arguments (excluding the program name).
pub fn parse_args<I: IntoIterator<Item = String>>(args: I) -> Result<Invocation, ArgError> {
    let mut file: Option<String> = None;
    for a in args {
        match a.as_str() {
            "-h" | "--help" => return Ok(Invocation::Help),
            "-V" | "--version" => return Ok(Invocation::Version),
            s if s.starts_with('-') && s != "-" => return Err(ArgError::Unknown(a)),
            _ => {
                if file.is_some() {
                    return Err(ArgError::TooMany);
                }
                file = Some(a);
            }
        }
    }
    let input = match file {
        Some(f) => Input::File(f),
        None => Input::Stdin,
    };
    Ok(Invocation::Run { input })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(args: &[&str]) -> Result<Invocation, ArgError> {
        parse_args(args.iter().map(|s| s.to_string()))
    }

    #[test]
    fn no_args_reads_stdin() {
        assert_eq!(parse(&[]), Ok(Invocation::Run { input: Input::Stdin }));
    }

    #[test]
    fn file_arg_is_file_input() {
        assert_eq!(
            parse(&["foo.smt2"]),
            Ok(Invocation::Run { input: Input::File("foo.smt2".into()) })
        );
    }

    #[test]
    fn help_and_version_flags() {
        assert_eq!(parse(&["--help"]), Ok(Invocation::Help));
        assert_eq!(parse(&["-h"]), Ok(Invocation::Help));
        assert_eq!(parse(&["--version"]), Ok(Invocation::Version));
        assert_eq!(parse(&["-V"]), Ok(Invocation::Version));
    }

    #[test]
    fn unknown_flag_errors() {
        assert_eq!(parse(&["--nope"]), Err(ArgError::Unknown("--nope".into())));
    }

    #[test]
    fn two_files_error() {
        assert_eq!(parse(&["a.smt2", "b.smt2"]), Err(ArgError::TooMany));
    }
}
```

- [ ] **Step 4: Write the minimal `main.rs`**

Create `crates/shinri-cli/src/main.rs`:

```rust
mod args;

use std::process::ExitCode;

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    match args::parse_args(argv) {
        Ok(args::Invocation::Help) => {
            print!("{}", args::USAGE);
            ExitCode::SUCCESS
        }
        Ok(args::Invocation::Version) => {
            println!("shinri {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Ok(args::Invocation::Run { input: _ }) => {
            // Wired to the streaming driver in a later task.
            ExitCode::SUCCESS
        }
        Err(e) => {
            let msg = match e {
                args::ArgError::Unknown(a) => format!("error: unknown argument '{a}'"),
                args::ArgError::TooMany => "error: more than one input file given".to_string(),
            };
            eprintln!("{msg}\n\n{}", args::USAGE);
            ExitCode::from(2)
        }
    }
}
```

- [ ] **Step 5: Write the integration test for arg behavior**

Create `crates/shinri-cli/tests/cli.rs`:

```rust
//! Black-box tests over the built `shinri` binary.
use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_shinri"))
}

#[test]
fn version_prints_and_exits_zero() {
    let out = bin().arg("--version").output().unwrap();
    assert!(out.status.success());
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.starts_with("shinri "), "got: {stdout:?}");
}

#[test]
fn help_exits_zero() {
    let out = bin().arg("--help").output().unwrap();
    assert!(out.status.success());
    assert!(String::from_utf8(out.stdout).unwrap().contains("Usage:"));
}

#[test]
fn unknown_flag_exits_two() {
    let out = bin().arg("--nope").output().unwrap();
    assert_eq!(out.status.code(), Some(2));
}
```

- [ ] **Step 6: Run the arg unit tests**

Run: `cargo test -p shinri-cli --bin shinri` (the crate is binary-only — there is no `--lib` target)
Expected: PASS — the `args::tests` module (5 passed).

- [ ] **Step 7: Run the integration tests**

Run: `cargo test -p shinri-cli --test cli`
Expected: PASS (3 passed).

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-cli/Cargo.toml crates/shinri-cli/src/args.rs crates/shinri-cli/src/main.rs crates/shinri-cli/tests/cli.rs Cargo.toml Cargo.lock
git commit -m "feat(cli): shinri-cli crate scaffold + hand-rolled arg parsing"
```

---

## Task 5: Output channels + presentation state

`OutChannel` (stdout/stderr/file with real redirection) and the driver-owned `Presentation` struct.

**Files:**
- Create: `crates/shinri-cli/src/driver.rs`
- Modify: `crates/shinri-cli/src/main.rs` (add `mod driver;`)
- Test: `crates/shinri-cli/src/driver.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Produces:
  - `pub enum OutChannel { Stdout, Stderr, File(BufWriter<File>) }` with `pub fn open(name: &str) -> io::Result<OutChannel>` and `pub fn write_line(&mut self, &str) -> io::Result<()>` (writes the line + `\n`, then flushes).
  - `pub struct Presentation { pub print_success: bool, pub regular: OutChannel }` with `Default` (`print_success = true`, `regular = Stdout`).
  - `open("stdout") -> Stdout`, `open("stderr") -> Stderr`, any other name → `File` created at that path.
  - Note: there is **no** `diagnostic` field. Phase 1 emits no diagnostic (non-response) output, and SMT-LIB `(error …)` responses go to the *regular* channel. `:diagnostic-output-channel` is accepted (falls through to the solver no-op → `success`) but not applied — see Task 6. This is the one intentional refinement from spec §3/§5, made to keep the code warning-clean and honest rather than carry a write-only field.

- [ ] **Step 1: Write the channel + presentation code with failing tests**

Create `crates/shinri-cli/src/driver.rs`:

```rust
//! The streaming driver: feeds bytes to the parser, executes commands on the
//! solver, and owns all presentation state (`:print-success`, output channels).

use std::fs::File;
use std::io::{self, BufWriter, Write};

/// An SMT-LIB output channel: a standard stream or a file.
pub enum OutChannel {
    Stdout,
    Stderr,
    File(BufWriter<File>),
}

impl OutChannel {
    /// Open a channel from an SMT-LIB channel name: `"stdout"`, `"stderr"`, or
    /// a filename (created/truncated).
    pub fn open(name: &str) -> io::Result<OutChannel> {
        match name {
            "stdout" => Ok(OutChannel::Stdout),
            "stderr" => Ok(OutChannel::Stderr),
            path => Ok(OutChannel::File(BufWriter::new(File::create(path)?))),
        }
    }

    /// Write one line (terminated by `\n`) and flush immediately, so an
    /// interactive caller sees each response without waiting on a buffer.
    pub fn write_line(&mut self, line: &str) -> io::Result<()> {
        match self {
            OutChannel::Stdout => {
                let out = io::stdout();
                let mut h = out.lock();
                writeln!(h, "{line}")?;
                h.flush()
            }
            OutChannel::Stderr => {
                let err = io::stderr();
                let mut h = err.lock();
                writeln!(h, "{line}")?;
                h.flush()
            }
            OutChannel::File(w) => {
                writeln!(w, "{line}")?;
                w.flush()
            }
        }
    }
}

/// Driver-owned presentation state. The solver never sees any of this.
///
/// Only the *regular* output channel is modeled: Phase 1 produces no diagnostic
/// (non-response) output, and SMT-LIB `(error …)` responses are written to the
/// regular channel. `:diagnostic-output-channel` is therefore accepted but not
/// applied (handled in the driver by letting it fall through to the solver).
pub struct Presentation {
    pub print_success: bool,
    pub regular: OutChannel,
}

impl Default for Presentation {
    fn default() -> Self {
        Presentation {
            print_success: true,
            regular: OutChannel::Stdout,
        }
    }
}

#[cfg(test)]
mod channel_tests {
    use super::*;

    #[test]
    fn open_maps_standard_streams() {
        assert!(matches!(OutChannel::open("stdout").unwrap(), OutChannel::Stdout));
        assert!(matches!(OutChannel::open("stderr").unwrap(), OutChannel::Stderr));
    }

    #[test]
    fn file_channel_writes_lines() {
        let path = std::env::temp_dir().join(format!("shinri_ch_{}.out", std::process::id()));
        let p = path.to_str().unwrap();
        {
            let mut ch = OutChannel::open(p).unwrap();
            ch.write_line("hello").unwrap();
            ch.write_line("world").unwrap();
        } // drop flushes/closes the file
        let body = std::fs::read_to_string(&path).unwrap();
        assert_eq!(body, "hello\nworld\n");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn default_print_success_is_true() {
        assert!(Presentation::default().print_success);
    }
}
```

- [ ] **Step 2: Declare the module**

In `crates/shinri-cli/src/main.rs`, add `mod driver;` below `mod args;`:

```rust
mod args;
mod driver;
```

This will warn about unused `driver` items until Task 6 — acceptable mid-plan. (If the crate is configured to deny warnings, the next task removes them; do not add `#![allow(dead_code)]`.)

- [ ] **Step 3: Run the channel tests to verify they pass**

Run: `cargo test -p shinri-cli channel_tests`
Expected: PASS (3 passed).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-cli/src/driver.rs crates/shinri-cli/src/main.rs
git commit -m "feat(cli): output channels + presentation state"
```

---

## Task 6: Driver streaming loop + main wiring

Tie it together: `Driver` feeds the parser, intercepts presentation options, maps `CommandResponse` to output; `main` reads a file (one chunk) or stdin (line by line).

**Files:**
- Modify: `crates/shinri-cli/src/driver.rs` (add `Driver`)
- Modify: `crates/shinri-cli/src/main.rs` (wire the `Run` arm)
- Test: `crates/shinri-cli/tests/cli.rs` (end-to-end script tests)

**Interfaces:**
- Consumes: `shinri_solver::{Solver, CommandResponse}`, `shinri_parser::{StreamingParser, StreamItem}`, `shinri_frontend::{Command, AttrValue}`, `OutChannel`/`Presentation` from Task 5.
- Produces:
  - `pub struct Driver` with `pub fn new() -> Driver`, `pub fn feed(&mut self, &str) -> io::Result<bool>` (returns `true` when `(exit)`/end reached), `pub fn finish(&mut self) -> io::Result<()>`.

- [ ] **Step 1: Write end-to-end integration tests (failing)**

Append to `crates/shinri-cli/tests/cli.rs`:

```rust
use std::io::Write;
use std::process::Stdio;

/// Run the binary with `stdin_text` piped in; return (stdout, exit code).
fn run_stdin(stdin_text: &str) -> (String, Option<i32>) {
    let mut child = bin()
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin_text.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    (String::from_utf8(out.stdout).unwrap(), out.status.code())
}

const UNSAT_SCRIPT: &str = "(set-option :print-success false)\
(set-logic QF_UF)(declare-sort U 0)(declare-fun a () U)(declare-fun b () U)\
(declare-fun f (U) U)(assert (= a b))(assert (distinct (f a) (f b)))(check-sat)";

#[test]
fn stdin_qf_uf_unsat_quiet() {
    let (stdout, code) = run_stdin(UNSAT_SCRIPT);
    assert_eq!(stdout, "unsat\n");
    assert_eq!(code, Some(0));
}

#[test]
fn print_success_emits_success_lines() {
    // No `:print-success false`: declarations and asserts each print `success`.
    let (stdout, _) = run_stdin(
        "(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 0.0))(check-sat)",
    );
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines.first(), Some(&"success")); // set-logic
    assert_eq!(lines.last(), Some(&"sat"));
    assert!(lines.iter().filter(|l| **l == "success").count() >= 3);
}

#[test]
fn parse_error_does_not_stop_the_stream() {
    let (stdout, code) = run_stdin(
        "(set-option :print-success false)(this-is-not-a-command)\
(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 0.0))(check-sat)",
    );
    assert!(stdout.contains("(error"), "expected an error line, got: {stdout:?}");
    assert!(stdout.trim_end().ends_with("sat"), "stream should continue: {stdout:?}");
    assert_eq!(code, Some(0)); // in-band error, not a process failure
}

#[test]
fn file_mode_matches_stdin_mode() {
    let path = std::env::temp_dir().join(format!("shinri_e2e_{}.smt2", std::process::id()));
    std::fs::write(&path, UNSAT_SCRIPT).unwrap();
    let out = bin().arg(&path).output().unwrap();
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "unsat\n");
    assert_eq!(out.status.code(), Some(0));
    let _ = std::fs::remove_file(&path);
}

#[test]
fn regular_output_channel_redirects_to_file() {
    let path = std::env::temp_dir().join(format!("shinri_redir_{}.out", std::process::id()));
    let p = path.to_str().unwrap();
    let script = format!(
        "(set-option :print-success false)\
(set-option :regular-output-channel \"{p}\")(echo \"hi\")"
    );
    let (stdout, _) = run_stdin(&script);
    assert_eq!(stdout, "", "output should have gone to the file, not stdout");
    let body = std::fs::read_to_string(&path).unwrap();
    assert!(body.contains("hi"), "redirected file got: {body:?}");
    let _ = std::fs::remove_file(&path);
}

#[test]
fn unreadable_file_exits_two() {
    let out = bin().arg("/no/such/shinri/file.smt2").output().unwrap();
    assert_eq!(out.status.code(), Some(2));
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p shinri-cli --test cli`
Expected: FAIL — `Driver` is not wired into `main`; the `Run` arm is a no-op, so scripts produce no output.

- [ ] **Step 3: Implement `Driver` in `driver.rs`**

Add to `crates/shinri-cli/src/driver.rs`. First, imports at the top of the file (next to the existing `use std::...`):

```rust
use shinri_frontend::{AttrValue, Command};
use shinri_parser::{StreamItem, StreamingParser};
use shinri_solver::{CommandResponse, Solver};
```

Then the driver:

```rust
/// Escape a string for inclusion inside an SMT-LIB `"..."` literal.
fn escape(s: &str) -> String {
    s.replace('"', "\"\"")
}

pub struct Driver {
    solver: Solver,
    parser: StreamingParser,
    pres: Presentation,
}

impl Default for Driver {
    fn default() -> Self {
        Self::new()
    }
}

impl Driver {
    pub fn new() -> Driver {
        Driver {
            solver: Solver::new(),
            parser: StreamingParser::new(),
            pres: Presentation::default(),
        }
    }

    /// Feed a chunk and execute every complete command it completes.
    /// Returns `Ok(true)` once `(exit)`/end-of-stream is reached.
    pub fn feed(&mut self, chunk: &str) -> io::Result<bool> {
        self.parser.push_str(chunk);
        self.drain()
    }

    /// Flush at input EOF: report a trailing partial command, if any.
    pub fn finish(&mut self) -> io::Result<()> {
        if let StreamItem::Command(Err(d)) = self.parser.finish(self.solver.ctx_mut()) {
            self.error(&d.message)?;
        }
        Ok(())
    }

    fn drain(&mut self) -> io::Result<bool> {
        loop {
            match self.parser.next_command(self.solver.ctx_mut()) {
                StreamItem::NeedMore => return Ok(false),
                StreamItem::Done => return Ok(true),
                StreamItem::Command(Err(d)) => self.error(&d.message)?,
                StreamItem::Command(Ok(cmd)) => {
                    if self.handle(cmd)? {
                        return Ok(true);
                    }
                }
            }
        }
    }

    /// Execute one command. Returns `Ok(true)` if it was `(exit)`.
    fn handle(&mut self, cmd: Command) -> io::Result<bool> {
        // Presentation-affecting options are handled here, not by the solver.
        if let Command::SetOption { keyword, value } = &cmd {
            if let Some(result) = self.try_presentation_option(keyword, value) {
                match result {
                    Ok(()) => self.success()?,
                    Err(msg) => self.error(&msg)?,
                }
                return Ok(false);
            }
        }

        let exiting = matches!(cmd, Command::Exit);
        match self.solver.execute(cmd) {
            CommandResponse::None => self.success()?,
            CommandResponse::Sat => self.pres.regular.write_line("sat")?,
            CommandResponse::Unsat => self.pres.regular.write_line("unsat")?,
            CommandResponse::Unknown => self.pres.regular.write_line("unknown")?,
            CommandResponse::Model(s) | CommandResponse::Values(s) => {
                self.pres.regular.write_line(&s)?
            }
            CommandResponse::Error(e) => self.error(&e)?,
        }
        Ok(exiting)
    }

    fn success(&mut self) -> io::Result<()> {
        if self.pres.print_success {
            self.pres.regular.write_line("success")?;
        }
        Ok(())
    }

    fn error(&mut self, msg: &str) -> io::Result<()> {
        self.pres.regular.write_line(&format!("(error \"{}\")", escape(msg)))
    }

    /// `Some(result)` if `keyword` is a presentation option handled here;
    /// `None` if it should fall through to the solver.
    fn try_presentation_option(
        &mut self,
        keyword: &str,
        value: &AttrValue,
    ) -> Option<Result<(), String>> {
        let AttrValue::Token(v) = value;
        match keyword {
            ":print-success" => Some(match v.as_deref() {
                Some("true") => {
                    self.pres.print_success = true;
                    Ok(())
                }
                Some("false") => {
                    self.pres.print_success = false;
                    Ok(())
                }
                _ => Err(":print-success expects true or false".to_string()),
            }),
            ":regular-output-channel" => Some(self.set_regular_channel(v.as_deref())),
            // `:diagnostic-output-channel` falls through (returns None) to the
            // solver no-op: accepted and `success`-acked, but not applied —
            // Phase 1 emits no diagnostic output to route. See Presentation.
            _ => None,
        }
    }

    fn set_regular_channel(&mut self, name: Option<&str>) -> Result<(), String> {
        let name = name.ok_or_else(|| "output-channel expects a string".to_string())?;
        match OutChannel::open(name) {
            Ok(ch) => {
                self.pres.regular = ch;
                Ok(())
            }
            Err(e) => Err(format!("cannot open channel {name}: {e}")),
        }
    }
}
```

- [ ] **Step 4: Wire `main.rs` to run the driver**

Edit `crates/shinri-cli/src/main.rs`. Replace the imports/top with:

```rust
mod args;
mod driver;

use std::io::{self, BufRead, Read};
use std::process::ExitCode;
```

Replace the `Run` arm so it calls `run`:

```rust
        Ok(args::Invocation::Run { input }) => run(input),
```

And add these functions below `main`:

```rust
fn run(input: args::Input) -> ExitCode {
    let mut driver = driver::Driver::new();
    let result = match input {
        args::Input::File(path) => run_file(&mut driver, &path),
        args::Input::Stdin => run_stdin(&mut driver),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(2)
        }
    }
}

fn run_file(driver: &mut driver::Driver, path: &str) -> io::Result<()> {
    let mut src = String::new();
    std::fs::File::open(path)?.read_to_string(&mut src)?;
    if driver.feed(&src)? {
        return Ok(());
    }
    driver.finish()
}

fn run_stdin(driver: &mut driver::Driver) -> io::Result<()> {
    let stdin = io::stdin();
    let mut lock = stdin.lock();
    let mut line = String::new();
    loop {
        line.clear();
        if lock.read_line(&mut line)? == 0 {
            break; // EOF (Ctrl-D / closed pipe)
        }
        if driver.feed(&line)? {
            return Ok(()); // (exit) seen
        }
    }
    driver.finish()
}
```

- [ ] **Step 5: Run the integration tests to verify they pass**

Run: `cargo test -p shinri-cli --test cli`
Expected: PASS (all arg tests + the 6 new end-to-end tests).

- [ ] **Step 6: Run the full crate test suite**

Run: `cargo test -p shinri-cli`
Expected: PASS (unit + integration).

- [ ] **Step 7: Manual smoke check**

Run: `printf '(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 0.0))(check-sat)(exit)' | cargo run -q -p shinri-cli`
Expected: `success` lines for the declarations/asserts followed by `sat`.

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-cli/src/driver.rs crates/shinri-cli/src/main.rs crates/shinri-cli/tests/cli.rs
git commit -m "feat(cli): streaming driver loop + file/stdin wiring"
```

---

## Task 7: Cross-path regression + workspace verification

Confirm the streaming path agrees with the existing whole-string oracle scripts and that the whole workspace is green and warning-clean.

**Files:**
- Modify: `crates/shinri-cli/tests/cli.rs` (add agreement test)

**Interfaces:**
- Consumes: the `run_stdin` helper from Task 6.

- [ ] **Step 1: Add a streaming/whole-string agreement test**

Append to `crates/shinri-cli/tests/cli.rs`:

```rust
#[test]
fn streaming_agrees_with_known_oracle_scripts() {
    // Mirrors crates/shinri-solver/tests/script_e2e.rs expectations, but driven
    // through the streaming CLI (whole-script fed via stdin).
    let cases = [
        ("(set-option :print-success false)(set-logic QF_UFLRA)\
(declare-fun x () Real)(declare-fun y () Real)(declare-fun f (Real) Real)\
(assert (= x y))(assert (distinct (f x) (f y)))(check-sat)", "unsat\n"),
        ("(set-option :print-success false)(set-logic QF_LRA)\
(declare-fun x () Real)(assert (< x 1.0))(assert (> x 0.0))(check-sat)", "sat\n"),
    ];
    for (script, expected) in cases {
        let (stdout, code) = run_stdin(script);
        assert_eq!(stdout, expected, "script: {script}");
        assert_eq!(code, Some(0));
    }
}
```

- [ ] **Step 2: Run the new test**

Run: `cargo test -p shinri-cli --test cli streaming_agrees_with_known_oracle_scripts`
Expected: PASS.

- [ ] **Step 3: Full workspace test run**

Run: `cargo test --workspace`
Expected: PASS (all crates).

- [ ] **Step 4: Lint clean (no warnings)**

Run: `cargo clippy --workspace --all-targets -- -D warnings`
Expected: no warnings. (In particular, no leftover dead-code warnings from Task 5's interim state.)

- [ ] **Step 5: Pure-Rust mandate still holds**

Run: `cargo deny check bans`
Expected: PASS — `shinri-cli` added no banned native-link deps.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-cli/tests/cli.rs
git commit -m "test(cli): streaming path agrees with whole-string oracle scripts"
```

---

## Self-Review Notes (for the implementer)

- **Spec §2 (crate shape):** Tasks 4 (scaffold), 5, 6 — zero external deps, binary `shinri`. ✓
- **Spec §3 (driver/presentation, intercept-not-forward):** Task 6 `handle`/`try_presentation_option` (intercepted options never reach `solver.execute`; `success` emitted once). ✓
- **Spec §4 (StreamingParser, lexer-reuse boundary scan, env persistence, finish):** Tasks 2, 3. ✓
- **Spec §5 (input sources, output channels w/ file redirection, exit codes 0/2):** Tasks 4 (args), 5 (channels), 6 (file/stdin + exit 2 on unreadable file). ✓
- **Spec §6 (three error layers, no panics):** usage→exit 2 (Task 4/6), parse error continues in-band (Task 6 `parse_error_does_not_stop_the_stream`), command error in-band exit 0. ✓
- **Spec §7 (testing):** parser unit tests (Tasks 2–3), CLI integration incl. print-success on/off, channel redirect, error continuation, file/stdin parity (Task 6), oracle agreement (Task 7). ✓
- **Hidden dependency discovered during planning:** `parse_attr` stored Debug text, not value text — Task 1 fixes it so the driver can read options. (Not in the spec; a necessary enabler.)
- **Out of scope (spec §8):** `--timeout`, `--stats`, batch mode, `check-sat-assuming`, unsat-core — not implemented. ✓
