# shinri-cli — Design Specification

**The thin, runnable binary over `shinri-solver`: SMT-LIB 2.6 batch + interactive front-end**

- **Date:** 2026-06-20
- **Status:** Approved design — ready for implementation planning
- **Scope:** A new `crates/shinri-cli` binary crate (`shinri`) that streams SMT-LIB
  scripts from a file or stdin through the existing parser + solver, with full
  SMT-LIB 2.6 batch/interactive presentation semantics. Closes the Phase 1
  "runnable / SMT-COMP-submittable" deliverable gap.

---

## 1. Goal & Context

Phase 1 of shinri (QF_UF + QF_LRA + Nelson-Oppen QF_UFLRA, the `shinri-num`
backend, and the SMT-LIB 2.6 parser) is complete as a set of library crates, but
there is no binary: the solver cannot yet be invoked as `shinri benchmark.smt2`.
The streaming driver loop already exists in proof-of-concept form as `run_script`
in `crates/shinri-solver/tests/script_e2e.rs`, whose comment notes it is "the seam
a future shinri-cli will own." This design promotes that seam to a real crate and
hardens it for full SMT-LIB 2.6 batch/interactive compliance and incremental
line-streaming input.

**Primary consumers:** the SMT-COMP harness (`shinri file.smt2`, whole-benchmark
batch) and an interactive REPL (`shinri` reading stdin a line at a time, answering
each command before the next is typed).

**Non-goals (v1, explicit YAGNI):** `--timeout`, `--stats`, batch/directory
regression mode, `check-sat-assuming` (solver returns `Unknown`), `get-unsat-core`
(solver unsupported). All deferrable behind the same driver without redesign.

---

## 2. Crate Shape & Dependencies

A new binary crate `crates/shinri-cli`, added to the workspace `members`,
producing one binary named `shinri` (`[[bin]] name = "shinri"`), so SMT-COMP
invokes `shinri benchmark.smt2`.

**Shipping dependencies:** `shinri-solver`, `shinri-parser`, `shinri-frontend` —
path deps only. **Zero external crates.** Argument parsing is hand-rolled (the
flag set is tiny), keeping the binary's dependency surface consistent with the
rest of the project's tiny-surface ethos (the whole shipping build is `logos` +
`rustc-hash`). This was a deliberate decision over `clap` (large transitive tree)
and micro-crates like `lexopt`.

`fn main` holds no real logic — it is a thin shell so that all behavior lives in
unit/integration-testable modules:

```
crates/shinri-cli/src/
├── main.rs      # entry: parse args -> select input -> driver::run -> process::exit(code)
├── args.rs      # hand-rolled arg parser -> struct CliArgs (+ --help/--version text)
└── driver.rs    # the streaming loop + presentation state (print-success, output channels)
```

---

## 3. Driver & Presentation State

`driver.rs` owns the streaming loop — a hardened evolution of the `run_script`
seam in `script_e2e.rs`. It holds a `Solver`, a `StreamingParser` (see §4), and a
`Presentation` state struct consulted for all output.

**Presentation is driver-owned, not solver-owned.** `:print-success` and output
channels are presentation concerns, not solver logic; keeping them in the driver
preserves `Solver` as a pure, embeddable library that returns structured
`CommandResponse` values and treats all options as no-ops. This was an explicit
architecture decision.

```rust
enum OutChannel { Stdout, Stderr, File(BufWriter<File>) }

struct Presentation {
    print_success:  bool,        // SMT-LIB 2.6 standard default: true
    regular_out:    OutChannel,  // :regular-output-channel    (default Stdout)
    diagnostic_out: OutChannel,  // :diagnostic-output-channel  (default Stderr)
}
```

**Per-command handling:**

1. Pull a `StreamItem` from the parser (see §4 for `NeedMore`/`Done`/EOF).
2. On a parse error `Diagnostic` → write `(error "<msg>")` to the **regular**
   channel, flush, **continue** (the boundary scanner keeps the stream in sync).
3. On a complete `Command`:
   - **Intercept presentation keywords first.** If the command is
     `SetOption { keyword, value }` for `:print-success`,
     `:regular-output-channel`, or `:diagnostic-output-channel`, update
     `Presentation` accordingly and emit the single success-or-error response for
     it directly — the driver does **not** also forward these to `solver.execute`
     (which would return `None` and risk a duplicate `success` line). A bad value
     (e.g. unparseable boolean, unopenable channel file) → `(error …)` and the
     option is not applied. All other `SetOption` keywords fall through to the
     normal `solver.execute` path below (no-op → `success` under print-success).
   - Otherwise `solver.execute(cmd)` and map the `CommandResponse`:
     | `CommandResponse` | Output |
     |---|---|
     | `Sat` / `Unsat` / `Unknown` | `sat` / `unsat` / `unknown` |
     | `Model(s)` / `Values(s)` | `s` verbatim |
     | `Error(e)` | `(error "e")` |
     | `None` | nothing, **unless** `print_success` → `success` |
4. **Flush after every command** (interactive correctness — never wait on buffer
   fill before the user sees an answer).
5. On `(exit)` or input EOF → stop.

**`:print-success` defaults to `true`** (the SMT-LIB 2.6 standard default).
Scripts wanting silence emit `(set-option :print-success false)` themselves, as
SMT-COMP harnesses do.

---

## 4. Line-Streaming Input (`shinri-parser` addition)

The existing `Parser<'a>` is built on `logos::Lexer<'a, Token>`, which borrows the
**entire** source `&'a str`; `Parser` holds that borrow. True incremental
streaming (read a line, parse, answer, read the next) therefore cannot reuse it —
it needs an owning, fed-incrementally parser. This is an **additive** API in
`shinri-parser`; the existing whole-string `Parser<'a>` remains for embedders and
tests.

```rust
pub struct StreamingParser {
    buf:      String,   // owned, growing input buffer
    consumed: usize,    // byte offset past the last fully-parsed command
    env:      Env,      // persistent symbol resolution across commands
    stopped:  bool,     // set after (exit)
}

pub enum StreamItem {
    Command(Result<Command, Diagnostic>), // one complete command (or its parse error)
    NeedMore,                             // buffer holds a partial command — feed more bytes
    Done,                                 // (exit) seen, or EOF with no trailing partial
}

impl StreamingParser {
    pub fn new() -> Self;
    pub fn push_str(&mut self, chunk: &str);            // append a line/chunk
    pub fn next_command(&mut self, ctx: &mut Context) -> StreamItem;
    pub fn finish(&mut self, ctx: &mut Context) -> StreamItem; // call at input EOF
}
```

**Boundary detection reuses the real lexer — no second lexical state machine.**
`next_command` runs the existing `logos` lexer over `buf[consumed..]`, counting
`LParen`/`RParen` depth. Every SMT-LIB command is exactly one balanced
parenthesized form, so:

- **Depth opens then returns to 0** → a complete command spans those bytes. Parse
  that slice with the existing command grammar, seeded with the persistent `env`;
  advance `consumed`; return `Command(...)`. Multiple complete commands already in
  the buffer drain across successive `next_command` calls.
- **End of buffer with depth > 0** (unclosed), **only whitespace/comments**, or a
  **lexer error whose span touches the buffer end** (a possibly mid-token form,
  e.g. an unterminated `"…`) → `NeedMore`.
- **A lexer error strictly before buffer end** → a real `Diagnostic` (returned as
  `Command(Err(..))`).

Because boundary detection uses the lexer itself, a `)` inside a string literal,
a `|quoted symbol|`, or a `;comment` can never be mistaken for a command boundary.

**`finish()`** is called once at input EOF: if a non-whitespace partial remains in
`buf[consumed..]`, it emits exactly one `(error "unexpected end of input")`;
otherwise `Done`.

**Spans / diagnostics:** byte spans are reported relative to the current command
slice, offset-adjusted by `consumed` so positions remain meaningful for both file
and REPL diagnostics.

**The driver unifies on this one engine:**

- **stdin (interactive REPL):** loop — read one line via `BufRead::read_line`;
  `push_str` it; drain `next_command` until `NeedMore`; flush after each emitted
  response. A read of 0 bytes (Ctrl-D / pipe end) → `finish()`.
- **file argument:** `push_str(whole_file)` once; drain `next_command` to
  `NeedMore`; then `finish()`. A file is a stream delivered in one chunk — same
  loop, same code path.

---

## 5. Input Sources, Output Channels & Exit Codes

**Argument handling (`args.rs` → `CliArgs`):**

| Invocation | Behavior |
|---|---|
| `shinri FILE.smt2` | read the file to a `String`, feed it as one chunk |
| `shinri` (no file) | read stdin incrementally, line by line |
| `shinri --version` | print `shinri <CARGO_PKG_VERSION>`, exit `0` |
| `shinri --help` / `-h` | print usage, exit `0` |
| unknown flag / unreadable file | usage error on stderr, exit `2` |

**Output channels (`OutChannel`):** `:regular-output-channel "stdout"` and
`:diagnostic-output-channel "stderr"` map to the standard streams; a quoted
filename opens that file for writing. Full file redirection is **implemented**
(small, and required for 2.6 compliance) rather than recognized-and-ignored.
Failure to open a channel file → `(error …)` on the current regular channel; the
option is not applied.

**Exit codes:**

- `0` — script ran to completion, including any number of in-band `(error …)`
  lines (per SMT-LIB, command/semantic errors are reported in the script, not via
  process status), or a clean `(exit)`.
- `2` — CLI usage error (bad args, unreadable input file) before solving begins.

This separates "the harness was invoked wrong" (exit `2`) from "the solver
produced an in-script error" (exit `0`, `(error …)` on the channel), which is what
SMT-COMP and shell tooling expect.

---

## 6. Error Handling

Three distinct layers, never conflated:

1. **CLI/usage errors** (bad flag, unreadable file) → stderr message, exit `2`,
   before any solving.
2. **Parse errors** (per command) → `(error "<msg>")` on the regular channel,
   **continue** the stream. The boundary scanner guarantees one malformed command
   cannot desync the rest of the stream.
3. **Command errors** (`CommandResponse::Error` from the solver) → `(error
   "<msg>")` in-band, **continue**; exit code stays `0`.

**No panics reach the user.** The parser is already fuzz-hardened for no-panic,
and the driver performs only total mappings over `StreamItem` and
`CommandResponse`.

---

## 7. Testing

**`shinri-parser` unit tests for `StreamingParser`:**

- a command split across multiple `push_str` chunks yields `NeedMore` then
  `Command`;
- `)` inside string literals / `|sym|` / `;comments` never triggers a false
  boundary;
- `env` persists — a `declare-fun` in chunk 1 resolves in a term in chunk 2;
- `finish()` on a trailing partial emits exactly one error;
- multiple complete commands in one chunk drain correctly across calls.

**`shinri-cli` integration tests (`tests/`):** drive the built binary via a
hand-rolled `std::process::Command` harness (no new dev-dep), asserting exact
stdout lines and exit codes:

- file mode and stdin mode produce identical output for the same script;
- `:print-success` on/off;
- an output-channel redirect to a temp file (assert file contents);
- a parse error mid-script — the stream continues and later commands still answer;
- `--version`, `--help`, and bad-flag exit codes.

**Regression via the existing oracle seam:** the `script_e2e.rs` scripts become
inputs for the streaming path, confirming the streaming and whole-string parsing
paths agree on output.

**No-panic fuzz (optional, existing `cargo-fuzz` setup):** feed random bytes as a
stream to `StreamingParser`.

---

## 8. Out of Scope (v1)

Explicitly deferred, each addable behind the same driver without redesign:
`--timeout`, `--stats`, batch/directory regression mode, `check-sat-assuming`
wiring, and `get-unsat-core` output. True per-token (sub-line) streaming is
unnecessary — line granularity already gives interactive responsiveness.
