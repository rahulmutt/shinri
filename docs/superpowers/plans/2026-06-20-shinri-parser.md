# shinri-parser (SMT-LIB 2.6 Frontend) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a pure-Rust SMT-LIB 2.6 reader (`shinri-parser`) that interns directly into the term DAG and drives `shinri-solver` incrementally, via a neutral `Command` IR crate (`shinri-frontend`).

**Architecture:** A new neutral crate `shinri-frontend` holds an inert `Command` enum. `shinri-parser` (logos lexer + hand-written recursive descent) *constructs* `Command` values, interning terms via `Context`; it depends only on `shinri-core` + `shinri-frontend` + `logos` and knows nothing about the solver. `shinri-solver` gains `ctx_mut()` + `execute(Command) -> CommandResponse`. A pull-based driver loop (`parser.next_command(solver.ctx_mut())` → `solver.execute(cmd)`) ties them together at the test/CLI layer, so parsing and solving stream command-by-command with **no parser↔solver dependency edge**.

**Tech Stack:** Rust (edition 2021, rust-version 1.96.0), `logos` lexer, `proptest` (dev), `num-bigint`/`num-rational` (dev oracle), `easy-smt` (dev oracle, needs `z3` on PATH).

**Spec:** `docs/superpowers/specs/2026-06-20-shinri-parser-design.md`

## Global Constraints

- **Pure Rust, no native-link deps in the shipping build.** `logos` is permissive (MIT/Apache) and pure-Rust; oracle crates (`num-bigint`, `easy-smt`) are **dev-dependencies only**. `cargo deny check` must stay green.
- **Soundness is existential.** Any unsupported construct, parse error, or internal uncertainty yields a recoverable `(error …)` and/or downstream `unknown` — never a wrong `sat`/`unsat`. The parser **never panics on input**.
- **Dependency direction is one-directional:** `shinri-core ← shinri-frontend ← {shinri-parser, shinri-solver}`. No `parser↔solver` runtime edge (the driver lives in tests / the future CLI, via dev-deps).
- **Crate manifest inheritance:** every new crate uses `edition.workspace = true`, `license.workspace = true`, `rust-version.workspace = true`.
- **CI gates extend automatically:** `cargo nextest run --workspace`, `cargo clippy --all-targets -- -D warnings`, `cargo fmt --check`, `cargo deny check`.

---

## File Structure

**New crate `crates/shinri-frontend/`:**
- `Cargo.toml` — depends on `shinri-core` only.
- `src/lib.rs` — `Command` enum + `AttrValue` sub-type.

**New crate `crates/shinri-parser/`:**
- `Cargo.toml` — depends on `shinri-core`, `shinri-frontend`, `logos`; dev: `proptest`.
- `src/lib.rs` — public API: `Parser`, `Diagnostic`, `Span`, re-exports.
- `src/lexer.rs` — `logos` `Token` enum + numeric/string/symbol handling.
- `src/env.rs` — scoped symbol environment (sorts, funs, let frames, define-fun macros).
- `src/parser.rs` — recursive-descent command dispatch + s-expression term parsing.
- `src/print.rs` — minimal term/command printer (round-trip test support).

**Edited `crates/shinri-num/`:**
- `src/integer.rs` — add `Integer::from_str_radix`.
- `tests/integer_differential.rs` — add a differential case.

**Edited `crates/shinri-solver/`:**
- `Cargo.toml` — add `shinri-frontend` dep; add `shinri-parser` + `shinri-frontend` dev-deps.
- `src/lib.rs` — add `ctx_mut()`, `execute()`, `CommandResponse`.
- `src/model.rs` — add SMT-LIB s-expression formatting for `Model`/`ModelVal`.
- `tests/script_e2e.rs` — driver loop + parse→solve end-to-end tests.
- `tests/oracle.rs` — extend with a differential-from-text case (feature `oracle`).

**Edited workspace `Cargo.toml`:** add the two new crates to `members`.

---

## Task 1: `Integer::from_str_radix` in `shinri-num`

**Files:**
- Modify: `crates/shinri-num/src/integer.rs`
- Test: `crates/shinri-num/src/integer.rs` (unit, in `mod tests`) + `crates/shinri-num/tests/integer_differential.rs`

**Interfaces:**
- Produces: `Integer::from_str_radix(s: &str, radix: u32) -> Result<Integer, ParseIntegerError>` where `s` is unsigned digits only (no sign, no whitespace). `pub struct ParseIntegerError;` with a `Display` impl.

- [ ] **Step 1: Write the failing unit test**

Add to the existing `mod tests` in `crates/shinri-num/src/integer.rs`:

```rust
#[test]
fn from_str_radix_small_and_big() {
    assert_eq!(Integer::from_str_radix("0", 10).unwrap(), Integer::from(0i128));
    assert_eq!(Integer::from_str_radix("42", 10).unwrap(), Integer::from(42i128));
    // 2^128 — genuinely exceeds i128, exercises the Big path.
    let two_128 = Integer::from(1i128 << 100) * Integer::from(1i128 << 28);
    assert_eq!(
        Integer::from_str_radix("340282366920938463463374607431768211456", 10).unwrap(),
        two_128
    );
    assert!(Integer::from_str_radix("", 10).is_err());
    assert!(Integer::from_str_radix("12a", 10).is_err());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-num from_str_radix_small_and_big`
Expected: FAIL — `no function or associated item named from_str_radix`.

- [ ] **Step 3: Implement `from_str_radix`**

Add to `crates/shinri-num/src/integer.rs` (new `impl` block + error type):

```rust
/// Failure parsing a decimal/radix string into an `Integer`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParseIntegerError;

impl core::fmt::Display for ParseIntegerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "invalid integer literal")
    }
}

impl Integer {
    /// Parse an unsigned digit string in `radix` (2..=16) via Horner's method.
    /// No sign, no whitespace, no prefix; empty or non-digit input is an error.
    pub fn from_str_radix(s: &str, radix: u32) -> Result<Integer, ParseIntegerError> {
        if s.is_empty() {
            return Err(ParseIntegerError);
        }
        let base = Integer::from(radix as i128);
        let mut acc = Integer::zero();
        for ch in s.chars() {
            let d = ch.to_digit(radix).ok_or(ParseIntegerError)?;
            acc = acc * base.clone() + Integer::from(d as i128);
        }
        Ok(acc)
    }
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-num from_str_radix_small_and_big`
Expected: PASS.

- [ ] **Step 5: Add a differential test vs `num-bigint`**

Append to `crates/shinri-num/tests/integer_differential.rs`:

```rust
proptest! {
    #![proptest_config(ProptestConfig::with_cases(2000))]

    #[test]
    fn from_str_radix_matches_bigint(digits in "[0-9]{1,40}") {
        let ours = shinri_num::Integer::from_str_radix(&digits, 10).unwrap();
        let theirs: num_bigint::BigInt = digits.parse().unwrap();
        prop_assert_eq!(ours.to_string(), theirs.to_string());
    }
}
```

- [ ] **Step 6: Run the differential test**

Run: `cargo test -p shinri-num from_str_radix_matches_bigint`
Expected: PASS.

- [ ] **Step 7: Export the error type and commit**

Ensure `crates/shinri-num/src/lib.rs` re-exports it (add `from_str_radix` is a method so only the error type needs exporting if referenced externally). Add to the `pub use` for integer:

```rust
pub use integer::{Integer, ParseIntegerError};
```

(Match the existing `pub use integer::Integer;` line — replace it.)

```bash
git add crates/shinri-num/src/integer.rs crates/shinri-num/src/lib.rs crates/shinri-num/tests/integer_differential.rs
git commit -m "feat(num): Integer::from_str_radix for unbounded decimal literals"
```

---

## Task 2: `shinri-frontend` crate — the `Command` IR

**Files:**
- Create: `crates/shinri-frontend/Cargo.toml`
- Create: `crates/shinri-frontend/src/lib.rs`
- Modify: `Cargo.toml` (workspace `members`)

**Interfaces:**
- Produces: the `Command` enum and `AttrValue` enum (below). Both `pub`. `Command` is `#[non_exhaustive]`.

- [ ] **Step 1: Create the crate manifest**

Create `crates/shinri-frontend/Cargo.toml`:

```toml
[package]
name = "shinri-frontend"
version = "0.1.0"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[dependencies]
shinri-core = { path = "../shinri-core" }
```

- [ ] **Step 2: Add the crate to the workspace**

In the root `Cargo.toml`, add `"crates/shinri-frontend"` to `members` (keep the list one line per existing style; insert after `shinri-core`).

- [ ] **Step 3: Write the `Command` IR with a compile/construction test**

Create `crates/shinri-frontend/src/lib.rs`:

```rust
//! The neutral SMT-LIB command IR. Constructed by `shinri-parser`, executed by
//! `shinri-solver`; neither depends on the other (design §2, §3.1).

use shinri_core::{SortId, SymbolId, TermId};

/// The value of a `set-option` / `set-info` attribute, kept as raw token text
/// (Phase 1 does not interpret most options).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AttrValue {
    /// No value (e.g. a bare flag), or an opaque token captured verbatim.
    Token(Option<String>),
}

/// One top-level SMT-LIB command, with terms already interned to `TermId`.
/// `#[non_exhaustive]` so Phase-2 commands (BV/array/quantifier) extend it
/// without breaking consumers.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum Command {
    SetLogic(String),
    DeclareSort { name: String, arity: u32 },
    DeclareFun { name: String, sym: SymbolId, params: Vec<SortId>, result: SortId },
    Assert(TermId),
    CheckSat,
    CheckSatAssuming(Vec<TermId>),
    Push(u32),
    Pop(u32),
    GetModel,
    GetValue(Vec<TermId>),
    GetUnsatCore,
    SetOption { keyword: String, value: AttrValue },
    SetInfo { keyword: String, value: AttrValue },
    GetInfo(String),
    Echo(String),
    Reset,
    Exit,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructs_and_clones() {
        let c = Command::Push(2);
        assert_eq!(c.clone(), Command::Push(2));
        assert_eq!(
            Command::SetLogic("QF_LRA".into()),
            Command::SetLogic("QF_LRA".into())
        );
    }
}
```

- [ ] **Step 4: Build and test**

Run: `cargo test -p shinri-frontend`
Expected: PASS (1 test).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-frontend/ Cargo.toml
git commit -m "feat(frontend): neutral Command IR crate"
```

---

## Task 3: `shinri-parser` scaffold + lexer

**Files:**
- Create: `crates/shinri-parser/Cargo.toml`
- Create: `crates/shinri-parser/src/lib.rs`
- Create: `crates/shinri-parser/src/lexer.rs`
- Modify: root `Cargo.toml` (`members`)

**Interfaces:**
- Produces: `Span = core::ops::Range<usize>`; `Token` enum (below); `Lexer` newtype yielding `Option<(Result<Token, ()>, Span)>` via `next_spanned`.

- [ ] **Step 1: Create the crate manifest**

Create `crates/shinri-parser/Cargo.toml`:

```toml
[package]
name = "shinri-parser"
version = "0.1.0"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-frontend = { path = "../shinri-frontend" }
logos = "0.14"

[dev-dependencies]
proptest = "1"
```

Add `"crates/shinri-parser"` to the workspace `members`.

- [ ] **Step 2: Write the failing lexer test**

Create `crates/shinri-parser/src/lexer.rs`:

```rust
use logos::Logos;

/// Byte-range span into the source, used for diagnostics.
pub type Span = core::ops::Range<usize>;

/// SMT-LIB 2.6 lexical tokens. `#x`/`#b` are lexed but rejected by the parser
/// (no bit-vectors in Phase 1). Unrecognized input yields a lexer error, which
/// the parser turns into a `Diagnostic` (never a panic).
#[derive(Logos, Clone, Debug, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]+")]      // whitespace
#[logos(skip r";[^\n]*")]         // line comments
pub enum Token {
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[regex(r"[0-9]+", |lex| lex.slice().to_owned())]
    Numeral(String),
    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice().to_owned())]
    Decimal(String),
    #[regex(r"#x[0-9a-fA-F]+", |lex| lex.slice().to_owned())]
    Hex(String),
    #[regex(r"#b[01]+", |lex| lex.slice().to_owned())]
    Bin(String),
    #[regex(r#""([^"]|"")*""#, |lex| lex.slice().to_owned())]
    Str(String),
    #[regex(r":[a-zA-Z0-9~!@$%^&*_+=<>.?/-]+", |lex| lex.slice().to_owned())]
    Keyword(String),
    // Simple symbols and quoted |...| symbols.
    #[regex(r"[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*", |lex| lex.slice().to_owned())]
    #[regex(r"\|[^|\\]*\|", |lex| { let s = lex.slice(); s[1..s.len()-1].to_owned() })]
    Symbol(String),
}

/// Thin wrapper over `logos::Lexer` yielding `(Result<Token, ()>, Span)`.
pub struct Lexer<'a> {
    inner: logos::Lexer<'a, Token>,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer { inner: Token::lexer(src) }
    }
    /// Next token with its span, or `None` at end of input.
    pub fn next_spanned(&mut self) -> Option<(Result<Token, ()>, Span)> {
        let tok = self.inner.next()?;
        let span = self.inner.span();
        Some((tok.map_err(|_| ()), span))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(src: &str) -> Vec<Token> {
        let mut lx = Lexer::new(src);
        let mut out = Vec::new();
        while let Some((t, _)) = lx.next_spanned() {
            out.push(t.expect("lexes cleanly"));
        }
        out
    }

    #[test]
    fn lexes_basic_forms() {
        assert_eq!(
            toks("(assert (= x 1.5)) ; comment\n"),
            vec![
                Token::LParen,
                Token::Symbol("assert".into()),
                Token::LParen,
                Token::Symbol("=".into()),
                Token::Symbol("x".into()),
                Token::Decimal("1.5".into()),
                Token::RParen,
                Token::RParen,
            ]
        );
        assert_eq!(toks(":produce-models"), vec![Token::Keyword(":produce-models".into())]);
        assert_eq!(toks("|quoted sym|"), vec![Token::Symbol("quoted sym".into())]);
    }

    #[test]
    fn unrecognized_byte_is_error_not_panic() {
        let mut lx = Lexer::new("\u{0}");
        assert!(matches!(lx.next_spanned(), Some((Err(()), _))));
    }
}
```

- [ ] **Step 3: Create a minimal `lib.rs` exposing the lexer module**

Create `crates/shinri-parser/src/lib.rs`:

```rust
//! SMT-LIB 2.6 frontend: logos lexer + interning recursive descent (design §9.1).

mod lexer;

pub use lexer::{Lexer, Span, Token};
```

- [ ] **Step 4: Run the lexer tests**

Run: `cargo test -p shinri-parser`
Expected: PASS (2 tests).

- [ ] **Step 5: Verify pure-Rust dependency policy still holds**

Run: `cargo deny check`
Expected: PASS (logos is permissive and pure-Rust).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-parser/ Cargo.toml Cargo.lock
git commit -m "feat(parser): crate scaffold + logos lexer"
```

---

## Task 4: Scoped symbol environment (`env.rs`)

**Files:**
- Create: `crates/shinri-parser/src/env.rs`
- Modify: `crates/shinri-parser/src/lib.rs` (add `mod env;`)

**Interfaces:**
- Consumes: `shinri_core::{SortId, SymbolId, TermId}`.
- Produces:
  - `struct FunInfo { pub sym: SymbolId }`
  - `struct Macro { pub formals: Vec<TermId>, pub body: TermId }`
  - `struct Env` with: `new()`, `add_sort(&str, SortId)`, `lookup_sort(&str) -> Option<SortId>`, `add_fun(&str, SymbolId)`, `lookup_fun(&str) -> Option<SymbolId>`, `add_macro(&str, Vec<TermId>, TermId)`, `lookup_macro(&str) -> Option<&Macro>`, `push_let(Vec<(String, TermId)>)`, `pop_let()`, `lookup_let(&str) -> Option<TermId>`.

- [ ] **Step 1: Write the failing env test**

Create `crates/shinri-parser/src/env.rs`:

```rust
use rustc_hash::FxHashMap;
use shinri_core::{SortId, SymbolId, TermId};

/// A non-recursive define-fun macro: `body` was interned against `formals`
/// (fresh placeholder consts); expansion substitutes actual args for formals.
#[derive(Clone)]
pub struct Macro {
    pub formals: Vec<TermId>,
    pub body: TermId,
}

/// Name resolution context. Lookup order at a head/leaf is enforced by the
/// parser (let → macro → fun → builtin); this type just stores the tables.
#[derive(Default)]
pub struct Env {
    sorts: FxHashMap<String, SortId>,
    funs: FxHashMap<String, SymbolId>,
    macros: FxHashMap<String, Macro>,
    let_frames: Vec<FxHashMap<String, TermId>>,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }

    pub fn add_sort(&mut self, name: &str, s: SortId) {
        self.sorts.insert(name.to_owned(), s);
    }
    pub fn lookup_sort(&self, name: &str) -> Option<SortId> {
        self.sorts.get(name).copied()
    }

    pub fn add_fun(&mut self, name: &str, sym: SymbolId) {
        self.funs.insert(name.to_owned(), sym);
    }
    pub fn lookup_fun(&self, name: &str) -> Option<SymbolId> {
        self.funs.get(name).copied()
    }

    pub fn add_macro(&mut self, name: &str, formals: Vec<TermId>, body: TermId) {
        self.macros.insert(name.to_owned(), Macro { formals, body });
    }
    pub fn lookup_macro(&self, name: &str) -> Option<&Macro> {
        self.macros.get(name)
    }

    pub fn push_let(&mut self, bindings: Vec<(String, TermId)>) {
        self.let_frames.push(bindings.into_iter().collect());
    }
    pub fn pop_let(&mut self) {
        self.let_frames.pop();
    }
    /// Innermost-first lookup of a let-bound name (shadowing).
    pub fn lookup_let(&self, name: &str) -> Option<TermId> {
        self.let_frames.iter().rev().find_map(|f| f.get(name).copied())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Context;

    #[test]
    fn let_shadowing_is_innermost_first() {
        let mut ctx = Context::new();
        let b = ctx.real_sort();
        let t1 = ctx.mk_numeral(shinri_core::Rational::one(), b);
        let t2 = ctx.mk_numeral(shinri_core::Rational::zero(), b);
        let mut env = Env::new();
        env.push_let(vec![("x".into(), t1)]);
        assert_eq!(env.lookup_let("x"), Some(t1));
        env.push_let(vec![("x".into(), t2)]);
        assert_eq!(env.lookup_let("x"), Some(t2)); // inner shadows outer
        env.pop_let();
        assert_eq!(env.lookup_let("x"), Some(t1));
    }
}
```

- [ ] **Step 2: Wire the module and dependency**

Add `mod env;` to `crates/shinri-parser/src/lib.rs`. Add `rustc-hash = "2"` to `[dependencies]` in `crates/shinri-parser/Cargo.toml` (used by `env.rs`).

- [ ] **Step 3: Run the test to verify it fails then passes**

Run: `cargo test -p shinri-parser let_shadowing_is_innermost_first`
Expected: first compile-fails if `mod env;` missing, then PASS once wired.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-parser/src/env.rs crates/shinri-parser/src/lib.rs crates/shinri-parser/Cargo.toml Cargo.lock
git commit -m "feat(parser): scoped symbol environment (sorts, funs, macros, let)"
```

---

## Task 5: Parser core — token stream, sorts, atoms (numerals/decimals/symbols)

**Files:**
- Create: `crates/shinri-parser/src/parser.rs`
- Modify: `crates/shinri-parser/src/lib.rs` (add `mod parser;`, re-exports)

**Interfaces:**
- Consumes: `Lexer`, `Token`, `Span`, `Env`, `shinri_core::Context`.
- Produces:
  - `struct Span2 = Span` (reuse `lexer::Span`).
  - `struct Diagnostic { pub span: Span, pub message: String }`.
  - `struct Parser<'a>` with `new(src: &'a str) -> Self`.
  - internal: `fn parse_sort(&mut self, ctx: &mut Context) -> Result<SortId, Diagnostic>`,
    `fn parse_atom_numeral(&mut self, ctx, text, is_decimal) -> Result<TermId, Diagnostic>`.
- Later tasks rely on: `Parser` holding a peekable token buffer (`peek`, `bump`, `expect_lparen`, `expect_rparen`, `expect_symbol`).

- [ ] **Step 1: Write the failing test for sort + numeral parsing**

Create `crates/shinri-parser/src/parser.rs`:

```rust
use crate::env::Env;
use crate::lexer::{Lexer, Span, Token};
use shinri_core::{Context, Rational, SortId, TermId};
use shinri_num::Integer;

/// A recoverable parse / well-sortedness error (design §8). Never panicked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Span,
    pub message: String,
}

impl Diagnostic {
    fn new(span: Span, msg: impl Into<String>) -> Self {
        Diagnostic { span, message: msg.into() }
    }
}

pub struct Parser<'a> {
    lx: Lexer<'a>,
    peeked: Option<(Result<Token, ()>, Span)>,
    /// Resolution context. Lives across commands (declarations persist).
    env: Env,
    eof: usize,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str) -> Self {
        Parser { lx: Lexer::new(src), peeked: None, env: Env::new(), eof: src.len() }
    }

    fn peek(&mut self) -> Option<&(Result<Token, ()>, Span)> {
        if self.peeked.is_none() {
            self.peeked = self.lx.next_spanned();
        }
        self.peeked.as_ref()
    }

    fn bump(&mut self) -> Option<(Result<Token, ()>, Span)> {
        if let Some(t) = self.peeked.take() {
            return Some(t);
        }
        self.lx.next_spanned()
    }

    fn here(&mut self) -> Span {
        match self.peek() {
            Some((_, sp)) => sp.clone(),
            None => self.eof..self.eof,
        }
    }

    fn expect_token(&mut self, want: &Token) -> Result<Span, Diagnostic> {
        match self.bump() {
            Some((Ok(t), sp)) if &t == want => Ok(sp),
            Some((_, sp)) => Err(Diagnostic::new(sp, format!("expected {want:?}"))),
            None => Err(Diagnostic::new(self.eof..self.eof, format!("expected {want:?}, found EOF"))),
        }
    }

    fn expect_symbol(&mut self) -> Result<(String, Span), Diagnostic> {
        match self.bump() {
            Some((Ok(Token::Symbol(s)), sp)) => Ok((s, sp)),
            Some((_, sp)) => Err(Diagnostic::new(sp, "expected symbol")),
            None => Err(Diagnostic::new(self.eof..self.eof, "expected symbol, found EOF")),
        }
    }

    /// Parse a sort: `Bool`/`Int`/`Real`/user-declared. Indexed/parameterized
    /// sorts (`(_ BitVec n)`, `(Array …)`) are out of scope → diagnostic.
    fn parse_sort(&mut self, ctx: &mut Context) -> Result<SortId, Diagnostic> {
        let (name, sp) = self.expect_symbol()?;
        match name.as_str() {
            "Bool" => Ok(ctx.bool_sort()),
            "Int" => Ok(ctx.int_sort()),
            "Real" => Ok(ctx.real_sort()),
            other => self
                .env
                .lookup_sort(other)
                .ok_or_else(|| Diagnostic::new(sp, format!("unknown sort {other}"))),
        }
    }

    /// Build a numeral term from literal text. `is_decimal` selects Real;
    /// integer literals default to Int (caller may re-coerce to Real later).
    fn parse_atom_numeral(
        &mut self,
        ctx: &mut Context,
        text: &str,
        is_decimal: bool,
        sp: Span,
    ) -> Result<TermId, Diagnostic> {
        if is_decimal {
            let (int_part, frac_part) = text.split_once('.').unwrap();
            let mut numer = Integer::from_str_radix(int_part, 10)
                .map_err(|_| Diagnostic::new(sp.clone(), "bad decimal"))?;
            let mut denom = Integer::one();
            for ch in frac_part.chars() {
                let d = ch.to_digit(10).ok_or_else(|| Diagnostic::new(sp.clone(), "bad decimal"))?;
                numer = numer * Integer::from(10i128) + Integer::from(d as i128);
                denom = denom * Integer::from(10i128);
            }
            let val = Rational::new(numer, denom);
            Ok(ctx.mk_numeral(val, ctx.real_sort()))
        } else {
            let n = Integer::from_str_radix(text, 10)
                .map_err(|_| Diagnostic::new(sp, "bad numeral"))?;
            let val = Rational::from_int(n);
            Ok(ctx.mk_numeral(val, ctx.int_sort()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_real_decimal_to_rational() {
        let mut ctx = Context::new();
        let mut p = Parser::new("");
        let t = p.parse_atom_numeral(&mut ctx, "1.5", true, 0..3).unwrap();
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
        assert_eq!(ctx.numeral_value(t).unwrap().clone(), Rational::new(Integer::from(3i128), Integer::from(2i128)));
    }

    #[test]
    fn parses_integer_literal_to_int() {
        let mut ctx = Context::new();
        let mut p = Parser::new("");
        let t = p.parse_atom_numeral(&mut ctx, "42", false, 0..2).unwrap();
        assert_eq!(ctx.sort_of(t), ctx.int_sort());
        assert_eq!(ctx.numeral_value(t).unwrap().clone(), Rational::from_int(Integer::from(42i128)));
    }
}
```

- [ ] **Step 2: Wire the module + `shinri-num` dep**

Add `mod parser;` and `pub use parser::{Diagnostic, Parser};` to `crates/shinri-parser/src/lib.rs`. Add `shinri-num = { path = "../shinri-num" }` to `crates/shinri-parser/Cargo.toml` `[dependencies]`.

- [ ] **Step 3: Run tests**

Run: `cargo test -p shinri-parser parses_`
Expected: PASS (2 tests).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-parser/src/parser.rs crates/shinri-parser/src/lib.rs crates/shinri-parser/Cargo.toml Cargo.lock
git commit -m "feat(parser): token buffer, sort parsing, numeral/decimal atoms"
```

---

## Task 6: Term parsing — symbols, builtins, desugaring, let, define-fun, division

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs`

**Interfaces:**
- Produces: `fn parse_term(&mut self, ctx: &mut Context) -> Result<TermId, Diagnostic>`.
- Internal helpers: `fn builtin_for(name) -> Option<BuiltinOp>`, `fn unify_arith(ctx, &mut Vec<TermId>) -> SortId`, `fn apply_builtin(ctx, name, args, sp) -> Result<TermId, Diagnostic>`.

**Desugaring rules (build the shapes `Context::mk_app` accepts):**
- `and`/`or`: `()` → `true`/`false` const; `(op x)` → `x`; else n-ary `mk_app`.
- `=>`: right-associative binary fold. `(=> a b c)` → `(=> a (=> b c))`.
- `xor`: left-associative binary fold.
- `+`/`*`: `(op x)` → `x`; else n-ary `mk_app`.
- `-`: unary → `Neg`; else left-associative binary `Sub` fold.
- `/`: see division rules below; left-associative for >2.
- `<`/`<=`/`>`/`>=`: `(< a b c)` → `(and (< a b) (< b c))` (chained, since `mk_app` requires arity 2).
- `=`: n-ary `mk_app(Eq, …)` (solver chains, commit `0c92915`).
- `distinct`: n-ary `mk_app(Distinct, …)` (solver lowers pairwise).
- `not`: arity 1; `ite`: arity 3.

**Division rules:**
- `(/ c1 c2)` both numerals → fold to one `Rational` numeral `c1 * c2.recip()`.
- `(/ x c)` constant divisor `c` → `mk_app(Mul, [numeral(c.recip()), x])`.
- non-constant divisor → `Diagnostic` "non-linear division".

**Int→Real coercion (`unify_arith`):** for an arithmetic application, if any operand is `Real`, re-mint every operand that is an *integer-literal numeral* (`sort_of == int_sort` AND `numeral_value().is_some()`) at `Real`. A genuine Int *variable* in a Real context is left as-is → `mk_app` returns `Mismatch` → diagnostic.

- [ ] **Step 1: Write failing tests for the term features**

Append to the `tests` module in `crates/shinri-parser/src/parser.rs`:

```rust
// Helper: parse a single term from `src` against a context seeded with decls.
fn parse_one(src: &str, seed: impl FnOnce(&mut Context, &mut Parser)) -> (Context, TermId) {
    let mut ctx = Context::new();
    let mut p = Parser::new(src);
    seed(&mut ctx, &mut p);
    let t = p.parse_term(&mut ctx).expect("parses");
    (ctx, t)
}

#[test]
fn folds_constant_division() {
    let (ctx, t) = parse_one("(/ 1 3)", |_, _| {});
    assert_eq!(ctx.sort_of(t), ctx.real_sort());
    assert_eq!(
        ctx.numeral_value(t).unwrap().clone(),
        Rational::new(Integer::from(1i128), Integer::from(3i128))
    );
}

#[test]
fn linear_division_by_constant_becomes_mul() {
    let (ctx, t) = parse_one("(/ x 2)", |ctx, p| {
        let r = ctx.real_sort();
        let sym = ctx.declare_fun("x", &[], r);
        p.bind_fun("x", sym); // test-only accessor (Step 3)
    });
    // (* (1/2) x)
    use shinri_core::{BuiltinOp, Op, TermNode};
    match ctx.term_node(t) {
        TermNode::App { op: Op::Builtin(BuiltinOp::Mul), .. } => {}
        other => panic!("expected Mul, got {other:?}"),
    }
    assert_eq!(ctx.sort_of(t), ctx.real_sort());
}

#[test]
fn coerces_int_literal_to_real_in_real_context() {
    // (+ x 1) where x : Real  ->  literal 1 coerced to Real, app is Real.
    let (ctx, t) = parse_one("(+ x 1)", |ctx, p| {
        let r = ctx.real_sort();
        let sym = ctx.declare_fun("x", &[], r);
        p.bind_fun("x", sym);
    });
    assert_eq!(ctx.sort_of(t), ctx.real_sort());
}

#[test]
fn let_binding_resolves() {
    let (ctx, t) = parse_one("(let ((y 1.0)) (+ y y))", |_, _| {});
    assert_eq!(ctx.sort_of(t), ctx.real_sort());
}

#[test]
fn chained_relation_desugars_to_and() {
    use shinri_core::{BuiltinOp, Op, TermNode};
    let (ctx, t) = parse_one("(< 1.0 2.0 3.0)", |_, _| {});
    match ctx.term_node(t) {
        TermNode::App { op: Op::Builtin(BuiltinOp::And), .. } => {}
        other => panic!("expected And, got {other:?}"),
    }
}

#[test]
fn unsupported_quantifier_is_error() {
    let mut ctx = Context::new();
    let mut p = Parser::new("(forall ((x Int)) true)");
    assert!(p.parse_term(&mut ctx).is_err());
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-parser`
Expected: FAIL — `parse_term` / `bind_fun` not defined.

- [ ] **Step 3: Implement `parse_term` and helpers**

Add to the `impl<'a> Parser<'a>` block in `parser.rs`:

```rust
/// Test-only: seed a declared function/constant name → symbol.
#[cfg(test)]
pub fn bind_fun(&mut self, name: &str, sym: shinri_core::SymbolId) {
    self.env.add_fun(name, sym);
}

fn builtin_for(name: &str) -> Option<shinri_core::BuiltinOp> {
    use shinri_core::BuiltinOp::*;
    Some(match name {
        "not" => Not, "and" => And, "or" => Or, "=>" => Implies, "xor" => Xor,
        "=" => Eq, "distinct" => Distinct, "ite" => Ite,
        "+" => Add, "-" => Sub, "*" => Mul, "<=" => Le, "<" => Lt, ">=" => Ge, ">" => Gt,
        _ => return None,
    })
}

/// Coerce integer-literal operands to Real when the application is Real-typed.
/// Returns the unified arithmetic sort.
fn unify_arith(ctx: &mut Context, args: &mut [TermId]) -> SortId {
    let real = ctx.real_sort();
    let int = ctx.int_sort();
    let any_real = args.iter().any(|&a| ctx.sort_of(a) == real);
    if any_real {
        for a in args.iter_mut() {
            if ctx.sort_of(*a) == int {
                if let Some(v) = ctx.numeral_value(*a).cloned() {
                    *a = ctx.mk_numeral(v, real);
                }
            }
        }
        real
    } else {
        int
    }
}

fn mk(ctx: &mut Context, op: shinri_core::Op, args: &[TermId], sp: &Span) -> Result<TermId, Diagnostic> {
    ctx.mk_app(op, args).map_err(|e| Diagnostic::new(sp.clone(), format!("sort error: {e:?}")))
}

/// Parse one s-expression term, interning bottom-up.
pub fn parse_term(&mut self, ctx: &mut Context) -> Result<TermId, Diagnostic> {
    use shinri_core::{BuiltinOp, Op};
    let (tok, sp) = self.bump().ok_or_else(|| Diagnostic::new(self.eof..self.eof, "expected term, found EOF"))?;
    let tok = tok.map_err(|_| Diagnostic::new(sp.clone(), "invalid token"))?;
    match tok {
        Token::Numeral(s) => self.parse_atom_numeral(ctx, &s, false, sp),
        Token::Decimal(s) => self.parse_atom_numeral(ctx, &s, true, sp),
        Token::Symbol(name) => self.resolve_leaf(ctx, &name, sp),
        Token::LParen => self.parse_compound(ctx, sp),
        other => Err(Diagnostic::new(sp, format!("unexpected token {other:?}"))),
    }
}

fn resolve_leaf(&mut self, ctx: &mut Context, name: &str, sp: Span) -> Result<TermId, Diagnostic> {
    use shinri_core::Op;
    if let Some(t) = self.env.lookup_let(name) {
        return Ok(t);
    }
    match name {
        "true" => return Ok(ctx.mk_const_bool(true)),
        "false" => return Ok(ctx.mk_const_bool(false)),
        _ => {}
    }
    if let Some(sym) = self.env.lookup_fun(name) {
        return Self::mk(ctx, Op::Uninterpreted(sym), &[], &sp);
    }
    Err(Diagnostic::new(sp, format!("undeclared symbol {name}")))
}

fn parse_compound(&mut self, ctx: &mut Context, open: Span) -> Result<TermId, Diagnostic> {
    // Head must be a symbol (Phase 1: no higher-order heads).
    let (head, hsp) = match self.bump() {
        Some((Ok(Token::Symbol(s)), sp)) => (s, sp),
        Some((_, sp)) => return Err(Diagnostic::new(sp, "expected an operator symbol after '('")),
        None => return Err(Diagnostic::new(self.eof..self.eof, "unexpected EOF after '('")),
    };

    match head.as_str() {
        "let" => return self.parse_let(ctx),
        "forall" | "exists" | "_" | "as" | "match" => {
            return Err(Diagnostic::new(hsp, format!("unsupported construct: {head}")));
        }
        _ => {}
    }

    // define-fun macro call?
    if let Some(m) = self.env.lookup_macro(&head).cloned() {
        let args = self.parse_arg_list(ctx)?;
        if args.len() != m.formals.len() {
            return Err(Diagnostic::new(hsp, "macro arity mismatch"));
        }
        return Ok(ctx.substitute(m.body, &m.formals, &args));
    }

    // Uninterpreted function application?
    if let Some(sym) = self.env.lookup_fun(&head) {
        let args = self.parse_arg_list(ctx)?;
        return Self::mk(ctx, shinri_core::Op::Uninterpreted(sym), &args, &open);
    }

    // Built-in operator (with desugaring).
    if head == "/" {
        let args = self.parse_arg_list(ctx)?;
        return self.apply_division(ctx, args, open);
    }
    if Self::builtin_for(&head).is_some() {
        let args = self.parse_arg_list(ctx)?;
        return self.apply_builtin(ctx, &head, args, open);
    }

    Err(Diagnostic::new(hsp, format!("unknown operator {head}")))
}

/// Parse terms until the matching ')'.
fn parse_arg_list(&mut self, ctx: &mut Context) -> Result<Vec<TermId>, Diagnostic> {
    let mut args = Vec::new();
    loop {
        match self.peek() {
            Some((Ok(Token::RParen), _)) => { self.bump(); break; }
            None => return Err(Diagnostic::new(self.eof..self.eof, "unexpected EOF in argument list")),
            _ => args.push(self.parse_term(ctx)?),
        }
    }
    Ok(args)
}

fn parse_let(&mut self, ctx: &mut Context) -> Result<TermId, Diagnostic> {
    self.expect_token(&Token::LParen)?; // bindings list
    let mut bindings = Vec::new();
    loop {
        match self.peek() {
            Some((Ok(Token::RParen), _)) => { self.bump(); break; }
            _ => {
                self.expect_token(&Token::LParen)?;
                let (name, _) = self.expect_symbol()?;
                let value = self.parse_term(ctx)?; // evaluated in OUTER scope
                self.expect_token(&Token::RParen)?;
                bindings.push((name, value));
            }
        }
    }
    self.env.push_let(bindings);
    let body = self.parse_term(ctx);
    self.env.pop_let();
    let body = body?;
    self.expect_token(&Token::RParen)?; // close the (let ...)
    Ok(body)
}

fn apply_division(&mut self, ctx: &mut Context, args: Vec<TermId>, sp: Span) -> Result<TermId, Diagnostic> {
    use shinri_core::{BuiltinOp, Op};
    if args.len() < 2 {
        return Err(Diagnostic::new(sp, "/ needs >= 2 args"));
    }
    // Left-fold pairwise.
    let mut acc = args[0];
    for &divisor in &args[1..] {
        let dv = ctx.numeral_value(divisor).cloned();
        match (ctx.numeral_value(acc).cloned(), dv) {
            (Some(n), Some(d)) => {
                // constant / constant -> fold
                acc = ctx.mk_numeral(n * d.recip(), ctx.real_sort());
            }
            (None, Some(d)) => {
                // x / const -> (* recip(d) x)
                let recip = ctx.mk_numeral(d.recip(), ctx.real_sort());
                let mut operands = vec![recip, acc];
                Self::unify_arith(ctx, &mut operands);
                acc = Self::mk(ctx, Op::Builtin(BuiltinOp::Mul), &operands, &sp)?;
            }
            (_, None) => return Err(Diagnostic::new(sp, "non-linear division (non-constant divisor)")),
        }
    }
    Ok(acc)
}

fn apply_builtin(&mut self, ctx: &mut Context, head: &str, mut args: Vec<TermId>, sp: Span) -> Result<TermId, Diagnostic> {
    use shinri_core::{BuiltinOp, Op};
    let op = Self::builtin_for(head).unwrap();
    match op {
        BuiltinOp::And | BuiltinOp::Or => {
            let unit = matches!(op, BuiltinOp::And);
            match args.len() {
                0 => Ok(ctx.mk_const_bool(unit)),
                1 => Ok(args[0]),
                _ => Self::mk(ctx, Op::Builtin(op), &args, &sp),
            }
        }
        BuiltinOp::Implies => {
            if args.len() < 2 { return Err(Diagnostic::new(sp, "=> needs >= 2 args")); }
            // right-assoc fold
            let mut acc = *args.last().unwrap();
            for &a in args[..args.len() - 1].iter().rev() {
                acc = Self::mk(ctx, Op::Builtin(BuiltinOp::Implies), &[a, acc], &sp)?;
            }
            Ok(acc)
        }
        BuiltinOp::Xor => {
            if args.len() < 2 { return Err(Diagnostic::new(sp, "xor needs >= 2 args")); }
            let mut acc = args[0];
            for &a in &args[1..] {
                acc = Self::mk(ctx, Op::Builtin(BuiltinOp::Xor), &[acc, a], &sp)?;
            }
            Ok(acc)
        }
        BuiltinOp::Add | BuiltinOp::Mul => {
            match args.len() {
                0 => Err(Diagnostic::new(sp, "arith op needs >= 1 arg")),
                1 => Ok(args[0]),
                _ => { Self::unify_arith(ctx, &mut args); Self::mk(ctx, Op::Builtin(op), &args, &sp) }
            }
        }
        BuiltinOp::Sub => {
            match args.len() {
                0 => Err(Diagnostic::new(sp, "- needs >= 1 arg")),
                1 => { Self::unify_arith(ctx, &mut args); Self::mk(ctx, Op::Builtin(BuiltinOp::Neg), &args, &sp) }
                _ => {
                    Self::unify_arith(ctx, &mut args);
                    let mut acc = args[0];
                    for &a in &args[1..] {
                        acc = Self::mk(ctx, Op::Builtin(BuiltinOp::Sub), &[acc, a], &sp)?;
                    }
                    Ok(acc)
                }
            }
        }
        BuiltinOp::Le | BuiltinOp::Lt | BuiltinOp::Ge | BuiltinOp::Gt => {
            if args.len() < 2 { return Err(Diagnostic::new(sp, "relation needs >= 2 args")); }
            Self::unify_arith(ctx, &mut args);
            // chain: (and (rel a b) (rel b c) ...)
            let mut conj = Vec::new();
            for w in args.windows(2) {
                conj.push(Self::mk(ctx, Op::Builtin(op), &[w[0], w[1]], &sp)?);
            }
            if conj.len() == 1 { Ok(conj[0]) } else { Self::mk(ctx, Op::Builtin(BuiltinOp::And), &conj, &sp) }
        }
        BuiltinOp::Eq | BuiltinOp::Distinct => {
            if args.len() < 2 { return Err(Diagnostic::new(sp, "needs >= 2 args")); }
            Self::unify_arith(ctx, &mut args); // harmless for non-arith (no int literals)
            Self::mk(ctx, Op::Builtin(op), &args, &sp)
        }
        BuiltinOp::Not => {
            if args.len() != 1 { return Err(Diagnostic::new(sp, "not needs 1 arg")); }
            Self::mk(ctx, Op::Builtin(BuiltinOp::Not), &args, &sp)
        }
        BuiltinOp::Ite => {
            if args.len() != 3 { return Err(Diagnostic::new(sp, "ite needs 3 args")); }
            Self::unify_arith(ctx, &mut args[1..]); // unify the two branches
            Self::mk(ctx, Op::Builtin(BuiltinOp::Ite), &args, &sp)
        }
        BuiltinOp::Neg => unreachable!("Neg is produced only via unary '-'"),
    }
}
```

- [ ] **Step 4: Run the term tests**

Run: `cargo test -p shinri-parser`
Expected: PASS (all term tests + earlier tests).

- [ ] **Step 5: Run clippy on the crate**

Run: `cargo clippy -p shinri-parser --all-targets -- -D warnings`
Expected: clean.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-parser/src/parser.rs
git commit -m "feat(parser): full term parsing — builtins, desugaring, let, macros, division"
```

---

## Task 7: Command parsing + `next_command` pull API + error recovery

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs`
- Modify: `crates/shinri-parser/src/lib.rs` (re-export nothing new; `Command` comes from `shinri-frontend`)

**Interfaces:**
- Produces: `pub fn next_command(&mut self, ctx: &mut Context) -> Option<Result<Command, Diagnostic>>` returning `None` at EOF / after `(exit)`. On `Err`, the parser has already skipped to the end of the offending command so the next call resumes cleanly.
- Consumes: `shinri_frontend::{Command, AttrValue}`.

- [ ] **Step 1: Write failing tests for the command loop + recovery**

Append to the `tests` module in `parser.rs`:

```rust
use shinri_frontend::Command;

fn commands(src: &str) -> Vec<Result<Command, Diagnostic>> {
    let mut ctx = Context::new();
    let mut p = Parser::new(src);
    let mut out = Vec::new();
    while let Some(c) = p.next_command(&mut ctx) {
        out.push(c);
    }
    out
}

#[test]
fn parses_a_small_script() {
    let cs = commands(
        "(set-logic QF_LRA)\n(declare-fun x () Real)\n(assert (< x 1.0))\n(check-sat)\n(exit)",
    );
    assert!(matches!(cs[0], Ok(Command::SetLogic(_))));
    assert!(matches!(cs[1], Ok(Command::DeclareFun { .. })));
    assert!(matches!(cs[2], Ok(Command::Assert(_))));
    assert!(matches!(cs[3], Ok(Command::CheckSat)));
    assert_eq!(cs.len(), 4); // (exit) ends the stream, emits Exit then None
    // Actually exit emits a command:
}

#[test]
fn error_recovers_to_next_command() {
    // Second command has a sort error; the third must still parse.
    let cs = commands(
        "(declare-fun x () Real)\n(assert (and x x))\n(check-sat)",
    );
    assert!(matches!(cs[0], Ok(Command::DeclareFun { .. })));
    assert!(cs[1].is_err()); // (and x x): x is Real, not Bool
    assert!(matches!(cs[2], Ok(Command::CheckSat)));
}

#[test]
fn define_fun_expands_and_emits_no_command() {
    let cs = commands(
        "(define-fun dbl ((a Real)) Real (+ a a))\n(declare-fun y () Real)\n(assert (= (dbl y) 0.0))\n(check-sat)",
    );
    // define-fun emits nothing; declare/assert/check-sat remain.
    assert!(matches!(cs[0], Ok(Command::DeclareFun { .. })));
    assert!(matches!(cs[1], Ok(Command::Assert(_))));
    assert!(matches!(cs[2], Ok(Command::CheckSat)));
    assert_eq!(cs.len(), 3);
}
```

Fix the first test's comment/assert: `(exit)` emits `Command::Exit`, so adjust:

```rust
#[test]
fn exit_emits_then_stops() {
    let cs = commands("(check-sat)\n(exit)\n(check-sat)");
    assert!(matches!(cs[0], Ok(Command::CheckSat)));
    assert!(matches!(cs[1], Ok(Command::Exit)));
    assert_eq!(cs.len(), 2); // nothing after (exit)
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-parser next_command`
Expected: FAIL — `next_command` not defined.

- [ ] **Step 3: Implement command parsing + recovery**

Add to `impl<'a> Parser<'a>` and a field. First add a `stopped: bool` field to the struct and initialize it `false` in `new`. Then:

```rust
/// Parse the next top-level command, interning into `ctx`. `None` at EOF or
/// after `(exit)`. On error, skips to the end of the current command so the
/// next call resumes cleanly (design §8 recovery).
pub fn next_command(&mut self, ctx: &mut Context) -> Option<Result<Command, Diagnostic>> {
    if self.stopped {
        return None;
    }
    // Skip to the next '(' (tolerate stray tokens); None at EOF.
    loop {
        match self.peek() {
            None => return None,
            Some((Ok(Token::LParen), _)) => { self.bump(); break; }
            Some((_, _)) => { self.bump(); } // stray token before a command
        }
    }
    let result = self.parse_command_body(ctx);
    if let Err(_) = &result {
        self.recover_to_command_end();
    }
    if let Ok(Command::Exit) = &result {
        self.stopped = true;
    }
    Some(result)
}

/// After the opening '(' is consumed, parse the command head + body, including
/// the closing ')'.
fn parse_command_body(&mut self, ctx: &mut Context) -> Result<Command, Diagnostic> {
    use shinri_frontend::{AttrValue, Command};
    let (head, hsp) = self.expect_symbol()?;
    let cmd = match head.as_str() {
        "set-logic" => {
            let (l, _) = self.expect_symbol()?;
            Command::SetLogic(l)
        }
        "declare-sort" => {
            let (name, _) = self.expect_symbol()?;
            let arity = self.expect_numeral_u32()?;
            if arity != 0 {
                return Err(Diagnostic::new(hsp, "declare-sort arity > 0 unsupported"));
            }
            let s = ctx.declare_sort(&name);
            self.env.add_sort(&name, s);
            Command::DeclareSort { name, arity }
        }
        "declare-const" => {
            let (name, _) = self.expect_symbol()?;
            let result = self.parse_sort(ctx)?;
            let sym = ctx.declare_fun(&name, &[], result);
            self.env.add_fun(&name, sym);
            Command::DeclareFun { name, sym, params: Vec::new(), result }
        }
        "declare-fun" => {
            let (name, _) = self.expect_symbol()?;
            self.expect_token(&Token::LParen)?;
            let mut params = Vec::new();
            while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
                params.push(self.parse_sort(ctx)?);
            }
            self.bump(); // ')'
            let result = self.parse_sort(ctx)?;
            let sym = ctx.declare_fun(&name, &params, result);
            self.env.add_fun(&name, sym);
            Command::DeclareFun { name, sym, params, result }
        }
        "define-fun" => {
            self.parse_define_fun(ctx)?;
            // No command emitted; recurse to fetch the next real command.
            // Consume nothing more here — return a sentinel by tail-calling.
            return self.parse_after_define(ctx);
        }
        "assert" => {
            let t = self.parse_term(ctx)?;
            Command::Assert(t)
        }
        "check-sat" => Command::CheckSat,
        "check-sat-assuming" => {
            self.expect_token(&Token::LParen)?;
            let mut lits = Vec::new();
            while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
                lits.push(self.parse_term(ctx)?);
            }
            self.bump();
            Command::CheckSatAssuming(lits)
        }
        "push" => Command::Push(self.opt_numeral_u32(1)?),
        "pop" => Command::Pop(self.opt_numeral_u32(1)?),
        "get-model" => Command::GetModel,
        "get-value" => {
            self.expect_token(&Token::LParen)?;
            let mut ts = Vec::new();
            while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
                ts.push(self.parse_term(ctx)?);
            }
            self.bump();
            Command::GetValue(ts)
        }
        "get-unsat-core" => Command::GetUnsatCore,
        "set-option" => { let (k, v) = self.parse_attr()?; Command::SetOption { keyword: k, value: v } }
        "set-info" => { let (k, v) = self.parse_attr()?; Command::SetInfo { keyword: k, value: v } }
        "get-info" => { let (k, _) = self.expect_keyword()?; Command::GetInfo(k) }
        "echo" => {
            match self.bump() {
                Some((Ok(Token::Str(s)), _)) => Command::Echo(s),
                Some((_, sp)) => return Err(Diagnostic::new(sp, "echo expects a string")),
                None => return Err(Diagnostic::new(self.eof..self.eof, "echo expects a string")),
            }
        }
        "reset" => Command::Reset,
        "exit" => Command::Exit,
        other => return Err(Diagnostic::new(hsp, format!("unsupported command: {other}"))),
    };
    self.expect_token(&Token::RParen)?; // close the command
    let _ = AttrValue::Token(None); // keep import used in all arms
    Ok(cmd)
}

/// `(define-fun f ((x S)…) R body)` — intern body against fresh formal consts,
/// store the macro; emits no command.
fn parse_define_fun(&mut self, ctx: &mut Context) -> Result<(), Diagnostic> {
    let (name, _) = self.expect_symbol()?;
    self.expect_token(&Token::LParen)?;
    let mut formal_names = Vec::new();
    let mut formals = Vec::new();
    while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
        self.expect_token(&Token::LParen)?;
        let (pname, _) = self.expect_symbol()?;
        let psort = self.parse_sort(ctx)?;
        // Fresh placeholder const, unique per definition to avoid clashes.
        let fresh = ctx.declare_fun(&format!("@{name}!{pname}"), &[], psort);
        let fresh_t = ctx.mk_app(shinri_core::Op::Uninterpreted(fresh), &[])
            .map_err(|e| Diagnostic::new(0..0, format!("{e:?}")))?;
        formal_names.push(pname);
        formals.push(fresh_t);
        self.expect_token(&Token::RParen)?;
    }
    self.bump(); // ')'
    let _result = self.parse_sort(ctx)?;
    // Bind formals as let-style names while parsing the body.
    self.env.push_let(formal_names.iter().cloned().zip(formals.iter().copied()).collect());
    let body = self.parse_term(ctx);
    self.env.pop_let();
    let body = body?;
    self.expect_token(&Token::RParen)?; // close (define-fun ...)
    self.env.add_macro(&name, formals, body);
    Ok(())
}

/// After a define-fun (which emits nothing), fetch the next real command.
fn parse_after_define(&mut self, ctx: &mut Context) -> Result<Command, Diagnostic> {
    match self.next_command(ctx) {
        Some(r) => r,
        None => Err(Diagnostic::new(self.eof..self.eof, "end of input after define-fun")),
    }
}

fn recover_to_command_end(&mut self) {
    // We are somewhere inside the current command; skip to the ')' that closes
    // the command's opening '(' (already consumed → depth starts at 1).
    let mut depth: i32 = 1;
    while depth > 0 {
        match self.bump() {
            None => break,
            Some((Ok(Token::LParen), _)) => depth += 1,
            Some((Ok(Token::RParen), _)) => depth -= 1,
            _ => {}
        }
    }
}

fn expect_numeral_u32(&mut self) -> Result<u32, Diagnostic> {
    match self.bump() {
        Some((Ok(Token::Numeral(s)), sp)) => s.parse().map_err(|_| Diagnostic::new(sp, "expected u32")),
        Some((_, sp)) => Err(Diagnostic::new(sp, "expected numeral")),
        None => Err(Diagnostic::new(self.eof..self.eof, "expected numeral, found EOF")),
    }
}

/// Optional trailing numeral (for `push`/`pop`); default when absent.
fn opt_numeral_u32(&mut self, default: u32) -> Result<u32, Diagnostic> {
    if let Some((Ok(Token::Numeral(s)), sp)) = self.peek().cloned() {
        self.bump();
        return s.parse().map_err(|_| Diagnostic::new(sp, "expected u32"));
    }
    Ok(default)
}

fn expect_keyword(&mut self) -> Result<(String, Span), Diagnostic> {
    match self.bump() {
        Some((Ok(Token::Keyword(k)), sp)) => Ok((k, sp)),
        Some((_, sp)) => Err(Diagnostic::new(sp, "expected :keyword")),
        None => Err(Diagnostic::new(self.eof..self.eof, "expected :keyword, found EOF")),
    }
}

/// `:keyword [value-token]` — capture the value as raw text (Phase 1).
fn parse_attr(&mut self) -> Result<(String, shinri_frontend::AttrValue), Diagnostic> {
    use shinri_frontend::AttrValue;
    let (k, _) = self.expect_keyword()?;
    // A value is present unless the next token closes the command.
    let val = match self.peek() {
        Some((Ok(Token::RParen), _)) | None => AttrValue::Token(None),
        Some((Ok(tok), _)) => {
            let text = format!("{tok:?}");
            self.bump();
            AttrValue::Token(Some(text))
        }
        Some((Err(()), sp)) => return Err(Diagnostic::new(sp.clone(), "invalid attribute value")),
    };
    Ok((k, val))
}
```

Note: `peek().cloned()` requires `Token: Clone` (it is) and the tuple to be cloneable — `Span` is `Clone`. Add `use` of `Command` at the top of `parser.rs`: `use shinri_frontend::Command;`.

- [ ] **Step 4: Run the command tests**

Run: `cargo test -p shinri-parser`
Expected: PASS.

- [ ] **Step 5: Clippy + commit**

Run: `cargo clippy -p shinri-parser --all-targets -- -D warnings`
Expected: clean.

```bash
git add crates/shinri-parser/src/parser.rs crates/shinri-parser/src/lib.rs
git commit -m "feat(parser): command parsing, pull-based next_command, error recovery"
```

---

## Task 8: Minimal printer + round-trip property test

**Files:**
- Create: `crates/shinri-parser/src/print.rs`
- Modify: `crates/shinri-parser/src/lib.rs` (`mod print;`, `pub use`)
- Test: `crates/shinri-parser/tests/roundtrip.rs`

**Interfaces:**
- Produces: `pub fn print_term(ctx: &Context, t: TermId) -> String` — emits an s-expression that re-parses to the same interned `TermId`.

- [ ] **Step 1: Write the failing round-trip test**

Create `crates/shinri-parser/tests/roundtrip.rs`:

```rust
use shinri_core::Context;
use shinri_parser::{print_term, Parser};

/// Parse `src` as a single term, print it, re-parse, and require identical ids.
fn roundtrip(src: &str, seed: impl Fn(&mut Context, &mut Parser)) {
    let mut ctx = Context::new();
    let mut p1 = Parser::new(src);
    seed(&mut ctx, &mut p1);
    let t1 = p1.parse_term_pub(&mut ctx).expect("parse 1");
    let printed = print_term(&ctx, t1);
    let mut p2 = Parser::new(&printed);
    seed(&mut ctx, &mut p2);
    let t2 = p2.parse_term_pub(&mut ctx).expect("parse 2");
    assert_eq!(t1, t2, "roundtrip changed the term: {src:?} -> {printed:?}");
}

#[test]
fn roundtrips_core_terms() {
    roundtrip("(and true false)", |_, _| {});
    roundtrip("(+ 1.0 (* 2.0 3.0))", |_, _| {});
    roundtrip("(ite true 1.0 2.0)", |_, _| {});
    roundtrip("(= 1.0 1.0)", |_, _| {});
}
```

This needs a public term-parse entry; add a thin `pub fn parse_term_pub` wrapper (Step 3).

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-parser --test roundtrip`
Expected: FAIL — `print_term` / `parse_term_pub` not found.

- [ ] **Step 3: Implement the printer + public wrapper**

Create `crates/shinri-parser/src/print.rs`:

```rust
use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermId, TermNode};

/// Print a term as an s-expression that re-parses to the same id.
pub fn print_term(ctx: &Context, t: TermId) -> String {
    let mut s = String::new();
    write_term(ctx, t, &mut s);
    s
}

fn write_term(ctx: &Context, t: TermId, out: &mut String) {
    match ctx.term_node(t).clone() {
        TermNode::Const { val, .. } => match val {
            ConstVal::Bool(b) => out.push_str(if b { "true" } else { "false" }),
            ConstVal::Num(_) => {
                let r = ctx.numeral_value(t).unwrap();
                // Print as (/ n d) when not integral, else the integer; both re-parse.
                let numer = r.numer();
                let denom = r.denom();
                if denom == shinri_num::Integer::one() {
                    out.push_str(&numer.to_string());
                } else {
                    out.push_str(&format!("(/ {numer} {denom})"));
                }
            }
        },
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            if children.is_empty() {
                if let Op::Uninterpreted(sym) = op {
                    out.push_str(symbol_name(ctx, sym));
                }
                return;
            }
            out.push('(');
            match op {
                Op::Builtin(b) => out.push_str(builtin_name(b)),
                Op::Uninterpreted(sym) => out.push_str(symbol_name(ctx, sym)),
            }
            for c in children {
                out.push(' ');
                write_term(ctx, c, out);
            }
            out.push(')');
        }
    }
}

fn builtin_name(b: BuiltinOp) -> &'static str {
    use BuiltinOp::*;
    match b {
        Not => "not", And => "and", Or => "or", Implies => "=>", Xor => "xor",
        Eq => "=", Distinct => "distinct", Ite => "ite",
        Neg => "-", Add => "+", Sub => "-", Mul => "*", Le => "<=", Lt => "<", Ge => ">=", Gt => ">",
    }
}

fn symbol_name(ctx: &Context, sym: shinri_core::SymbolId) -> &str {
    ctx.symbol_name(sym)
}
```

This needs `Context::symbol_name`. Add it to `crates/shinri-core/src/context.rs` (public accessor over the interner) and re-export nothing new:

```rust
pub fn symbol_name(&self, sym: SymbolId) -> &str {
    self.symbols.resolve(sym)
}
```

Add to `crates/shinri-parser/src/lib.rs`:

```rust
mod print;
pub use print::print_term;
```

Add the public wrapper in `parser.rs` `impl`:

```rust
/// Public single-term entry point (used by the round-trip test).
pub fn parse_term_pub(&mut self, ctx: &mut Context) -> Result<TermId, Diagnostic> {
    self.parse_term(ctx)
}
```

Add `shinri-num = { path = "../shinri-num" }` is already a dep; `print.rs` uses `shinri_num::Integer` — ensure it's imported via `shinri_core::Rational`'s `numer()`/`denom()` returning `shinri_num::Integer` (it does). Add `use shinri_num::Integer;` only if needed for `Integer::one()` — it is, so import it in `print.rs`.

- [ ] **Step 4: Run the round-trip tests**

Run: `cargo test -p shinri-parser --test roundtrip`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-parser/src/print.rs crates/shinri-parser/src/lib.rs crates/shinri-parser/src/parser.rs crates/shinri-core/src/context.rs crates/shinri-parser/tests/roundtrip.rs
git commit -m "feat(parser): minimal term printer + round-trip property test"
```

---

## Task 9: Solver edit — `ctx_mut`, `CommandResponse`, `execute`, model formatting

**Files:**
- Modify: `crates/shinri-solver/Cargo.toml` (add `shinri-frontend` dep)
- Modify: `crates/shinri-solver/src/lib.rs`
- Modify: `crates/shinri-solver/src/model.rs`

**Interfaces:**
- Consumes: `shinri_frontend::{Command, AttrValue}`.
- Produces:
  - `pub fn ctx_mut(&mut self) -> &mut Context`
  - `pub enum CommandResponse { None, Sat, Unsat, Unknown, Model(String), Values(String), Error(String) }` (model/value pre-formatted as SMT-LIB text)
  - `pub fn execute(&mut self, cmd: Command) -> CommandResponse`
  - `pub fn format_value(&self, t: TermId) -> Option<String>` in `model.rs`.

- [ ] **Step 1: Add the dependency**

In `crates/shinri-solver/Cargo.toml` `[dependencies]`, add:

```toml
shinri-frontend = { path = "../shinri-frontend" }
```

- [ ] **Step 2: Write failing tests for `execute`**

Append to `crates/shinri-solver/src/lib.rs` (in a `#[cfg(test)] mod execute_tests`):

```rust
#[cfg(test)]
mod execute_tests {
    use super::*;
    use shinri_frontend::Command;

    #[test]
    fn execute_runs_check_sat_unsat() {
        // x < 0 and x > 0 over Real -> unsat. Build via ctx_mut to mirror the parser.
        let mut s = Solver::new();
        let r = s.real_sort();
        let x = s.declare_const("x", r);
        let zero = s.numeral(shinri_num::Rational::zero(), r);
        let lt = s.app(Op::Builtin(shinri_core::BuiltinOp::Lt), &[x, zero]);
        let gt = s.app(Op::Builtin(shinri_core::BuiltinOp::Gt), &[x, zero]);
        assert!(matches!(s.execute(Command::Assert(lt)), CommandResponse::None));
        assert!(matches!(s.execute(Command::Assert(gt)), CommandResponse::None));
        assert!(matches!(s.execute(Command::CheckSat), CommandResponse::Unsat));
    }

    #[test]
    fn get_unsat_core_is_unsupported() {
        let mut s = Solver::new();
        assert!(matches!(s.execute(Command::GetUnsatCore), CommandResponse::Error(_)));
    }

    #[test]
    fn push_pop_are_noops_response() {
        let mut s = Solver::new();
        assert!(matches!(s.execute(Command::Push(2)), CommandResponse::None));
        assert!(matches!(s.execute(Command::Pop(1)), CommandResponse::None));
    }
}
```

- [ ] **Step 3: Run to verify failure**

Run: `cargo test -p shinri-solver execute_`
Expected: FAIL — `ctx_mut`/`execute`/`CommandResponse` not defined.

- [ ] **Step 4: Implement `ctx_mut`, `CommandResponse`, `execute`**

Add to `crates/shinri-solver/src/lib.rs`:

```rust
use shinri_frontend::Command;

/// The result of executing one command. Model/value payloads are pre-formatted
/// SMT-LIB text so the driver/CLI just writes them (design §3.3).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandResponse {
    None,
    Sat,
    Unsat,
    Unknown,
    Model(String),
    Values(String),
    Error(String),
}

impl Solver {
    /// Mutable access to the shared term DAG, so the parser interns into the
    /// same `Context` the solver solves over.
    pub fn ctx_mut(&mut self) -> &mut Context {
        &mut self.ctx
    }

    /// Execute one IR command, returning a response value (driver formats it).
    pub fn execute(&mut self, cmd: Command) -> CommandResponse {
        match cmd {
            Command::Assert(t) => { self.assert(t); CommandResponse::None }
            Command::CheckSat => match self.check_sat() {
                SolveOutcome::Sat => CommandResponse::Sat,
                SolveOutcome::Unsat => CommandResponse::Unsat,
                SolveOutcome::Unknown => CommandResponse::Unknown,
            },
            Command::CheckSatAssuming(_) => CommandResponse::Unknown, // not wired this milestone
            Command::Push(n) => { for _ in 0..n { self.push(); } CommandResponse::None }
            Command::Pop(n) => { self.pop(n as usize); CommandResponse::None }
            Command::GetModel => CommandResponse::Model(self.format_model()),
            Command::GetValue(ts) => {
                let mut out = String::from("(");
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 { out.push(' '); }
                    let v = self.format_value(*t).unwrap_or_else(|| "?".to_string());
                    out.push_str(&format!("({} {})", crate::tseitin::display_term(&self.ctx, *t), v));
                }
                out.push(')');
                CommandResponse::Values(out)
            }
            Command::GetUnsatCore => CommandResponse::Error("unsupported".into()),
            Command::SetLogic(_)
            | Command::DeclareSort { .. }
            | Command::DeclareFun { .. }
            | Command::SetOption { .. }
            | Command::SetInfo { .. }
            | Command::Reset
            | Command::Exit => CommandResponse::None,
            Command::GetInfo(_) => CommandResponse::None,
            Command::Echo(s) => CommandResponse::Values(s),
            _ => CommandResponse::None,
        }
    }
}
```

Note `Reset` should also clear assertions/scopes; for Phase 1 a minimal reset is acceptable but implement it: in the `Reset` arm replace with `{ self.assertions.clear(); self.scopes.clear(); self.last_model = None; CommandResponse::None }` (move `Reset` out of the grouped arm).

- [ ] **Step 5: Implement model/value formatting in `model.rs`**

Add to `crates/shinri-solver/src/model.rs`:

```rust
use shinri_num::Rational;

/// Format a `Rational` as SMT-LIB: `n` if integral, else `(/ n d)`; negatives
/// as `(- …)`.
pub fn format_rational(r: &Rational) -> String {
    let n = r.numer();
    let d = r.denom();
    let body = if d == shinri_num::Integer::one() {
        if n.is_negative() { format!("(- {})", n.abs()) } else { n.to_string() }
    } else if n.is_negative() {
        format!("(- (/ {} {}))", n.abs(), d)
    } else {
        format!("(/ {n} {d})")
    };
    body
}

/// Format a single `ModelVal`.
pub fn format_modelval(v: &ModelVal) -> String {
    match v {
        ModelVal::Bool(b) => if *b { "true".into() } else { "false".into() },
        ModelVal::Num(r) => format_rational(r),
        ModelVal::Elem(_, idx) => format!("@elem{idx}"),
    }
}
```

Add to `Solver` in `lib.rs`:

```rust
fn format_value(&self, t: TermId) -> Option<String> {
    self.last_model.as_ref()?.get(t).map(crate::model::format_modelval)
}

fn format_model(&self) -> String {
    match &self.last_model {
        None => "()".into(),
        Some(m) => {
            let mut out = String::from("(");
            for (t, v) in m.values.iter() {
                out.push_str(&format!("({} {})", crate::tseitin::display_term(&self.ctx, *t), crate::model::format_modelval(v)));
            }
            out.push(')');
            out
        }
    }
}
```

This references `crate::tseitin::display_term` and `m.values`. `values` is `pub(crate)` (already). Add a small `display_term` to `tseitin.rs` (or reuse `print`): implement a minimal term display in `tseitin.rs`:

```rust
/// Minimal term display for model/value output (id-name for consts).
pub(crate) fn display_term(ctx: &shinri_core::Context, t: shinri_core::TermId) -> String {
    use shinri_core::{Op, TermNode};
    match ctx.term_node(t) {
        TermNode::App { op: Op::Uninterpreted(sym), args, .. } if args.len == 0 => {
            ctx.symbol_name(*sym).to_string()
        }
        _ => format!("t{}", t.index()),
    }
}
```

(`TermId::index()` is `pub`; `Context::symbol_name` was added in Task 8. If `t.index()` is not public, use the existing `Debug` of `TermId` instead: `format!("{t:?}")`.)

- [ ] **Step 6: Make `format_modelval`/`format_rational` reachable**

Ensure `model.rs` items are `pub(crate)` or `pub`; the `mod model;` is private, so mark the two `fn`s `pub` and reference as `crate::model::…`.

- [ ] **Step 7: Run the solver tests**

Run: `cargo test -p shinri-solver`
Expected: PASS (new `execute_*` tests + existing tests).

- [ ] **Step 8: Clippy + commit**

Run: `cargo clippy -p shinri-solver --all-targets -- -D warnings`
Expected: clean.

```bash
git add crates/shinri-solver/Cargo.toml crates/shinri-solver/src/lib.rs crates/shinri-solver/src/model.rs crates/shinri-solver/src/tseitin.rs Cargo.lock
git commit -m "feat(solver): ctx_mut + execute(Command) -> CommandResponse + model formatting"
```

---

## Task 10: Driver loop + end-to-end parse→solve tests

**Files:**
- Modify: `crates/shinri-solver/Cargo.toml` (dev-deps: `shinri-parser`, `shinri-frontend`)
- Create: `crates/shinri-solver/tests/script_e2e.rs`

**Interfaces:**
- Consumes: `shinri_parser::Parser`, `shinri_solver::{Solver, CommandResponse}`.
- Produces (test-local): `fn run_script(src: &str) -> Vec<String>` — the driver loop, collecting one output line per producing command (`sat`/`unsat`/`unknown`/`(error …)`/model/values/echo).

- [ ] **Step 1: Add dev-dependencies**

In `crates/shinri-solver/Cargo.toml` `[dev-dependencies]`:

```toml
shinri-parser = { path = "../shinri-parser" }
shinri-frontend = { path = "../shinri-frontend" }
```

- [ ] **Step 2: Write the end-to-end tests**

Create `crates/shinri-solver/tests/script_e2e.rs`:

```rust
//! End-to-end: SMT-LIB text -> parser -> solver, command-incremental streaming.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

/// The driver loop (the seam a future shinri-cli will own). Streams: parse one
/// command, execute it, collect any output line.
fn run_script(src: &str) -> Vec<String> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut out = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match result {
            Ok(cmd) => match solver.execute(cmd) {
                CommandResponse::None => {}
                CommandResponse::Sat => out.push("sat".into()),
                CommandResponse::Unsat => out.push("unsat".into()),
                CommandResponse::Unknown => out.push("unknown".into()),
                CommandResponse::Model(s) | CommandResponse::Values(s) => out.push(s),
                CommandResponse::Error(e) => out.push(format!("(error \"{e}\")")),
            },
            Err(diag) => out.push(format!("(error \"{}\")", diag.message)),
        }
    }
    out
}

#[test]
fn qf_uf_unsat() {
    let out = run_script(
        "(set-logic QF_UF)\
         (declare-sort U 0)\
         (declare-fun a () U)\
         (declare-fun b () U)\
         (declare-fun f (U) U)\
         (assert (= a b))\
         (assert (distinct (f a) (f b)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn qf_lra_sat_and_unsat() {
    let sat = run_script(
        "(set-logic QF_LRA)(declare-fun x () Real)(assert (< x 1.0))(assert (> x 0.0))(check-sat)",
    );
    assert_eq!(sat, vec!["sat"]);
    let unsat = run_script(
        "(set-logic QF_LRA)(declare-fun x () Real)(assert (< x 0.0))(assert (> x 0.0))(check-sat)",
    );
    assert_eq!(unsat, vec!["unsat"]);
}

#[test]
fn qf_uflra_combination() {
    // f : Real -> Real, x = y => f(x) = f(y), with x = y forced by arithmetic.
    let out = run_script(
        "(set-logic QF_UFLRA)\
         (declare-fun x () Real)(declare-fun y () Real)(declare-fun f (Real) Real)\
         (assert (= x y))(assert (distinct (f x) (f y)))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn streaming_incremental_push_pop() {
    // check-sat solves at each point against assertions so far.
    let out = run_script(
        "(declare-fun x () Real)\
         (assert (> x 0.0))(check-sat)\
         (push 1)(assert (< x 0.0))(check-sat)(pop 1)\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat", "unsat", "sat"]);
}

#[test]
fn error_recovers_and_continues() {
    let out = run_script(
        "(declare-fun p () Bool)\
         (assert (+ p 1))\
         (assert p)(check-sat)",
    );
    // First assert errors (Bool + Int), second assert + check-sat still run.
    assert_eq!(out.len(), 2);
    assert!(out[0].starts_with("(error"));
    assert_eq!(out[1], "sat");
}

#[test]
fn int_arithmetic_is_unknown_not_wrong() {
    // QF_LIA fragment is fenced downstream to unknown (never a wrong answer).
    let out = run_script(
        "(declare-fun n () Int)(assert (> n 0))(assert (< n 1))(check-sat)",
    );
    assert_eq!(out, vec!["unknown"]);
}
```

- [ ] **Step 3: Run to verify failure, then implement**

Run: `cargo test -p shinri-solver --test script_e2e`
Expected: FAIL initially only if any wiring is missing; otherwise these exercise Tasks 1–9. Fix any integration mismatch surfaced here (e.g. coercion, response mapping) in the relevant earlier file, re-running until green.

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-solver --test script_e2e`
Expected: PASS (6 tests).

- [ ] **Step 5: Full workspace gate**

Run: `cargo nextest run --workspace && cargo clippy --all-targets -- -D warnings && cargo fmt --check && cargo deny check`
Expected: all green.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/Cargo.toml crates/shinri-solver/tests/script_e2e.rs Cargo.lock
git commit -m "test(solver): end-to-end SMT-LIB text -> parser -> solver streaming"
```

---

## Task 11: Differential-from-text oracle + parser fuzz target

**Files:**
- Modify: `crates/shinri-solver/tests/oracle.rs` (add a from-text case, feature `oracle`)
- Create: `crates/shinri-parser/fuzz/` (cargo-fuzz target) OR a proptest no-panic test if `cargo-fuzz` setup is out of scope

**Interfaces:**
- Consumes: existing `oracle` feature harness; `shinri_parser::Parser`.

- [ ] **Step 1: Add a no-panic property test for the parser**

Create `crates/shinri-parser/tests/no_panic.rs`:

```rust
use proptest::prelude::*;
use shinri_core::Context;
use shinri_parser::Parser;

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// The parser must never panic on arbitrary input — only return commands
    /// or diagnostics (design §8, Global Constraint: never panic on input).
    #[test]
    fn never_panics_on_arbitrary_text(src in ".{0,200}") {
        let mut ctx = Context::new();
        let mut p = Parser::new(&src);
        let mut budget = 1000;
        while let Some(_c) = p.next_command(&mut ctx) {
            budget -= 1;
            if budget == 0 { break; }
        }
    }
}
```

- [ ] **Step 2: Run the fuzz/no-panic test**

Run: `cargo test -p shinri-parser --test no_panic`
Expected: PASS (no panics).

- [ ] **Step 3: Extend the differential oracle to run from text**

Add to `crates/shinri-solver/tests/oracle.rs` (still under `#![cfg(feature = "oracle")]`), a dev-dep on the parser is needed — add to `[dev-dependencies]` (already added in Task 10). Add:

```rust
/// Render a generated QF_LRA instance to SMT-LIB text, run it through the
/// parser+solver driver, and compare against z3 — closing the loop so the
/// oracle exercises the *frontend* too, not just hand-built API terms.
#[test]
fn differential_qf_lra_from_text() {
    use shinri_parser::Parser;
    use shinri_solver::{CommandResponse, Solver};

    fn solve_text(src: &str) -> Option<bool> {
        let mut solver = Solver::new();
        let mut parser = Parser::new(src);
        let mut verdict = None;
        while let Some(Ok(cmd)) = parser.next_command(solver.ctx_mut()) {
            match solver.execute(cmd) {
                CommandResponse::Sat => verdict = Some(true),
                CommandResponse::Unsat => verdict = Some(false),
                CommandResponse::Unknown => return None,
                _ => {}
            }
        }
        verdict
    }

    let mut rng = Lcg(0xC0FFEE);
    for _ in 0..200 {
        // Reuse the existing generator to emit SMT-LIB text instead of API calls.
        let src = random_qf_lra_smt2(&mut rng); // helper below
        let ours = solve_text(&src);
        if ours.is_none() { continue; } // unknown is never a failure
        let z3 = z3_check_smt2(&src);    // existing z3 path, fed the same text
        assert_eq!(ours, z3, "disagreement on:\n{src}");
    }
}
```

Implement `random_qf_lra_smt2` and `z3_check_smt2` mirroring the existing generator/oracle helpers in `oracle.rs` (emit `(set-logic QF_LRA)`, `declare-fun`s, random linear `assert`s, `(check-sat)`; feed the same string to z3 via `easy-smt`'s raw command or a `z3 -smt2` subprocess). Keep the random structure identical to the existing `differential_qf_lra_*` test so coverage is preserved.

- [ ] **Step 4: Run the differential-from-text oracle (requires z3)**

Run: `cargo test -p shinri-solver --features oracle differential_qf_lra_from_text -- --nocapture`
Expected: PASS (or all-`unknown`/skipped if z3 absent — never a sat/unsat disagreement).

- [ ] **Step 5: Final full gate**

Run: `cargo nextest run --workspace && cargo clippy --all-targets -- -D warnings && cargo fmt --check && cargo deny check`
Expected: all green.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-parser/tests/no_panic.rs crates/shinri-solver/tests/oracle.rs
git commit -m "test(parser): no-panic fuzz + differential-from-text QF_LRA oracle"
```

---

## Self-Review

**Spec coverage:**
- §2 decision 1 (neutral Command IR, no sink) → Task 2. ✓
- §2 decision 2 (pull-based streaming) → Task 7 `next_command`, Task 10 driver + `streaming_incremental_push_pop`. ✓
- §2 decision 3 (SMT-LIB `(error …)`-and-continue) → Task 7 recovery, Task 10 `error_recovers_and_continues`. ✓
- §2 decision 4 (let / define-fun / `/`-fold / linear division) → Task 6. ✓
- §2 decision 5 (logos + interning recursive descent) → Tasks 3, 5, 6. ✓
- §3.1 frontend crate → Task 2. §3.2 parser crate → Tasks 3–8. §3.3 solver edit (`ctx_mut`/`execute`/`CommandResponse`/formatting) → Task 9. §3.4 `from_str_radix` → Task 1. ✓
- §4 command set (incl. `get-unsat-core` deferred to `Error`) → Task 7 (parse) + Task 9 (execute). ✓
- §5 lexer → Task 3. §6 env + recursive descent → Tasks 4–7. §7 term semantics (numerals, coercion, division, n-ary shapes) → Tasks 5–6. §8 error/output → Tasks 7, 9, 10. ✓
- §9 testing (unit, round-trip, fuzz, differential-from-text) → Tasks 6, 8, 11. ✓
- §10 deliverable → Tasks 1–11. ✓

**Placeholder scan:** Task 11 Step 3 intentionally points `random_qf_lra_smt2`/`z3_check_smt2` at the *existing* `oracle.rs` generator to mirror (concrete source in the same file), not invented APIs — consistent with how the arith oracle plan handled its generator. All other steps carry complete code.

**Type consistency:** `Command`/`AttrValue` (Task 2) are used with identical variants in Tasks 7 and 9. `Diagnostic { span, message }`, `Parser::{new, next_command, parse_term, parse_term_pub, bind_fun}`, `Env::{add_*, lookup_*, push_let, pop_let}`, `CommandResponse` variants, `Context::{ctx_mut via solver, symbol_name, mk_app, mk_numeral, numeral_value, sort_of, declare_fun, declare_sort, substitute, int/real/bool_sort}`, `Integer::{from_str_radix, one, abs}`, `Rational::{from_int, new, recip, numer, denom}` are introduced once and referenced consistently. `BuiltinOp` variant names match `term.rs`. `SortError` is formatted via `{:?}` (its `Debug` derive).

**Known adaptation points (flagged inline):** (a) `TermId::index()` visibility for `display_term` — fall back to `{t:?}` if not public (Task 9 Step 5); (b) `Token` value rendering in `parse_attr` uses `{:?}` as opaque text — acceptable for Phase-1 round-tripping of options, which the round-trip test does not cover; (c) the oracle generator helpers must match the existing `oracle.rs` structure (Task 11). Each is called out at its task.
