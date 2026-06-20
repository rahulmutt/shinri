# shinri-parser — Design Specification

**SMT-LIB 2.6 frontend for shinri**

- **Date:** 2026-06-20
- **Status:** Approved design — ready for implementation planning
- **Scope:** Phase 1 SMT-LIB 2.6 reader for QF_UF / QF_LRA / QF_UFLRA (and the
  Int-fenced fragments that flow to `unknown`). Implements roadmap step 7
  (frontend) of the north-star design (`2026-06-18-shinri-design.md` §9.1, §12).

---

## 1. Goal & Motivation

Today shinri is driven **only** through the `shinri-solver` API (the solver
crate header literally states *"No SMT-LIB parser (assert via the API)"*). Every
test and the differential z3 oracle build terms by hand. This blocks shinri from
consuming any real `.smt2` file, running benchmark families, or being wrapped in
a competition CLI.

`shinri-parser` is the highest-leverage missing Phase-1 piece: a fast,
soundness-preserving SMT-LIB 2.6 reader that interns directly into the term DAG
and **feeds** the solver. It is the natural next step now that QF_UFLRA theory
combination has landed.

**Non-goals (Phase 1):** bit-vectors, arrays, strings, quantifiers, recursive
functions, indexed (`_`) identifiers, `as`-annotations, `match`. All parse to a
recoverable `(error …)`. The `shinri-cli` binary is a *follow-on* — this spec
delivers the parser plus the solver-side `execute` glue, leaving the CLI's
stdin/file/flag plumbing to a separate small effort.

---

## 2. Design Decisions (locked during brainstorming)

1. **Neutral Command IR crate, not a sink trait.** Parsing and solving are
   decoupled through an inert `Command` data IR living in a new neutral crate
   `shinri-frontend`. The parser *constructs* `Command`s; the solver *matches*
   on them. There is **no `shinri-parser ↔ shinri-solver` dependency edge**.
2. **Pull-based, command-incremental streaming.** A driver loop parses exactly
   one command, executes it, then pulls the next. `(check-sat)` solves at that
   point against the assertions so far; nothing waits for EOF. This is the
   incremental DPLL(T) model the solver already supports.
3. **SMT-LIB-faithful error model.** On a recoverable error (parse error,
   undeclared symbol, sort mismatch, unsupported construct) the driver prints
   `(error "msg")` and **continues** at the next top-level command. Unsupported
   logics/fragments still parse; their soundness fence (Int → `unknown`) is
   downstream. The parser never panics on input.
4. **Four term features supported:** `let`-bindings (parallel + shadowing),
   non-recursive `define-fun` (expanded by substitution), constant `/`-folding
   into a `Rational`, and linear division-by-constant `(/ x c)`.
5. **`logos` lexer + hand-written recursive descent** that interns directly
   (design §9.1) — symbols → `SymbolId`, terms → interned `TermId`, well-sorted
   inline via `Context::mk_app`.

---

## 3. Crate Layout & Dependency Graph

One new neutral crate and one new parser crate; one existing crate edited.

```
shinri-core ← shinri-frontend ← shinri-parser
                       ↑
shinri-core ← shinri-frontend ← shinri-solver
```

Strictly one-directional; **no parser↔solver edge**. Added to the workspace
`members`.

### 3.1 `shinri-frontend` (new, neutral)

Holds **only** the types both the parser and the solver must name:

- `Command` — the IR enum (§4). `#[non_exhaustive]` so Phase-2 commands extend
  it without breaking consumers.
- The small sub-types `Command` embeds: `LogicId`, option/attribute value enum,
  sort-reference form.

Depends on `shinri-core` (because `Command` carries `TermId` / `SortId` /
`SymbolId` / `Rational`). Nothing else.

### 3.2 `shinri-parser` (new)

Depends on `{ shinri-core, shinri-frontend, logos }`. Knows nothing about the
solver. Modules:

```
src/lib.rs      # public API: Parser, next_command, parse_script helper, Diagnostic
src/lexer.rs    # logos Token enum + numeric/string/symbol handling
src/parser.rs   # recursive descent: command dispatch + s-expression term parsing
src/env.rs      # scoped symbol environment: sorts, funs, let frames, define-fun macros
src/print.rs    # minimal term/command printer (for the round-trip property test)
```

- `Diagnostic { span: Span, message: String }` — recoverable parse/sort error.
  Produced here, consumed by the driver/CLI. **Not** in the neutral crate (the
  solver never names it).

### 3.3 `shinri-solver` (edited — the only change outside the new crates)

- Add `ctx_mut(&mut self) -> &mut Context`.
- Add `execute(&mut self, cmd: Command) -> Option<CommandResponse>` that matches
  on the IR and calls existing methods (`assert`, `check_sat`, `push`, `pop`,
  `get_model`, `get_value`, …). `CommandResponse` (or direct stdout writing) is
  solver-side; `SolveOutcome` / `Model` stay in `shinri-solver` (the parser
  never names them).
- Add a `shinri-frontend` dependency.

---

## 4. The `Command` IR & Command Set

Phase-1 command coverage (design §9.1) plus the trivial informational commands
real benchmarks emit. Each row maps an SMT-LIB command to a `Command` variant or
to parser-internal handling.

| SMT-LIB command | Handling |
|---|---|
| `set-logic L` | `SetLogic(LogicId)` — recorded; unsupported logics still parse (soundness fence downstream) |
| `declare-sort s 0` | `DeclareSort{name}` — arity 0 only; arity > 0 → `(error …)` |
| `declare-fun` / `declare-const` | `DeclareFun{ sym, params: Vec<SortId>, result: SortId }` |
| `define-fun` (non-recursive) | parser-internal: intern body against fresh formals, store macro in `env`; **emits no Command** |
| `assert t` | `Assert(TermId)` |
| `check-sat` | `CheckSat` |
| `check-sat-assuming (l…)` | `CheckSatAssuming(Vec<TermId>)` |
| `push n` / `pop n` | `Push(u32)` / `Pop(u32)` (default n = 1) |
| `get-model` | `GetModel` |
| `get-value (t…)` | `GetValue(Vec<TermId>)` |
| `get-unsat-core` | `GetUnsatCore` |
| `set-option` / `set-info` | `SetOption{ kw, val }` / parser-internal record; unknown keys accepted silently per SMT-LIB |
| `get-info` / `echo` / `reset` / `exit` | `GetInfo{kw}` / `Echo(String)` / `Reset` / `Exit` |

`get-unsat-core` / `get-model` route to existing solver capabilities; if a
capability is not yet wired, `execute` prints `(error "unsupported")` — never a
wrong answer.

---

## 5. Lexer (`lexer.rs`)

A `logos`-derived `Token` enum over the SMT-LIB 2.6 lexical grammar, yielding
`(Token, Span)` where `Span` is a byte range used in diagnostics.

- Structural: `LParen`, `RParen`.
- `Symbol` — simple (`[a-zA-Z~!@$%^&*_+=<>.?/-][…]*`) and quoted `|…|`.
- `Keyword` — `:foo` (attributes for `set-option` / `set-info`).
- `Numeral` — `0 | [1-9][0-9]*`.
- `Decimal` — `N.0*N`.
- `Hex` / `Bin` — `#x…` / `#b…` accepted lexically, rejected with `(error …)`
  in Phase 1 (no BV).
- `String` — `"…"` with `""` escape.
- Comments `;…\n` and whitespace skipped.
- Unrecognized byte → `Token::Error` (the parser reports it; never panics).

**Streaming seam:** the lexer reads a `&str` buffer in the Phase-1 baseline
(file or piped stdin slurped into a `String`). The parser pulls tokens lazily so
that a future interactive token source — accumulate bytes until one balanced
top-level s-expression, then lex that slice — drops in without reshaping the API.

---

## 6. Parser Core (`parser.rs`) & Environment (`env.rs`)

Hand-written recursive descent over the token stream, in two layers.

### 6.1 Command layer — pull-based

```rust
impl Parser {
    /// Parse the next single top-level command, interning its terms into `ctx`.
    /// Returns None at EOF / after (exit). Consumes only this command's input.
    pub fn next_command(&mut self, ctx: &mut Context)
        -> Option<Result<Command, Diagnostic>>;
}
```

The driver owns the loop:

```rust
let mut solver = Solver::new();
let mut parser = Parser::new(source);
while let Some(result) = parser.next_command(solver.ctx_mut()) {
    match result {
        Ok(cmd)   => solver.execute(cmd),   // (check-sat) solves NOW
        Err(diag) => report_error(diag),    // (error "…"), then continue
    }
}
```

`next_command` borrows the `Context`, interns, returns an inert `Command`, and
**releases the borrow**; then `execute` borrows the solver. Sequential borrows —
no conflict, and the `Solver` keeps owning its `Context`.

### 6.2 Term layer — interning recursive descent

`parse_term(&mut env, ctx) -> Result<TermId, Diagnostic>` walks s-expressions,
interning bottom-up via `ctx.mk_app(op, &args)` / `mk_numeral` / `mk_const_bool`.

**`env` (the resolution context):**

- **Symbol tables:** declared sorts (name → `SortId`), declared funs/consts
  (name → signature), built-in operator keywords (`and`, `or`, `=`, `+`, `<=`,
  `ite`, `distinct`, …) → `BuiltinOp`.
- **`let` frames:** a stack of name → `TermId` maps. `(let ((x e1)(y e2)) body)`
  evaluates all RHS in the *outer* scope (parallel binding), pushes one frame,
  parses `body`, pops. Lookup walks frames inner-to-outer (shadowing).
- **`define-fun` macros:** stored as `(formals: Vec<TermId>, body: TermId)`,
  where formals are fresh consts the body was interned against. At a call site:
  parse argument terms, then `ctx.substitute(body, &formals, &args)` for the
  expanded interned term. Non-recursive (the name is not in scope in its body).

**Resolution order** at a head position: let-bound → define-fun macro → declared
fun → built-in op. At a leaf: let-bound → declared const → numeral/decimal.

---

## 7. Term-Construction Semantics

`mk_app` performs the sort check and returns `Result<TermId, SortError>`; the
parser converts a `SortError` into a `Diagnostic`.

- **Numerals / decimals:** `42` → `Integer::from_str_radix(s, 10)`
  *(integration point: confirm the exact `shinri-num` constructor while
  implementing)* → `Rational::from_int`. `1.5` → `3/2`. Both → `mk_numeral`.
- **Int/Real coercion:** SMT-LIB requires literal-context typing. Phase-1 rule:
  an integer literal adopts `Real` when the surrounding operator or declared
  sort demands it, else `Int`. A genuine mismatch that cannot coerce →
  `(error "sort mismatch")`.
- **`/` folding & linear division:** `(/ c1 c2)` both constant → fold to one
  `Rational` numeral. `(/ x c)` constant divisor → rewrite to `(* recip(c) x)`
  (still linear). Non-constant divisor → `(error "non-linear")` → `unknown`
  downstream.
- **n-ary shapes:** build what `mk_app` expects — left-assoc for `-` / `/`,
  chained for relations (`(< a b c)`), n-ary for `+` / `*` / `and` / `or`,
  chained for `(= a b c)` (per solver commit `0c92915`).
- **Out of scope → `(error …)`:** quantifiers, `_`-indexed identifiers, `as`,
  arrays, strings, `match`.

---

## 8. Error Handling & Output

SMT-LIB-faithful. `Diagnostic { span, message }`:

- **Recoverable** (parse error, undeclared symbol, sort mismatch, unsupported
  construct, arity error): print `(error "message")` to stdout and continue at
  the next top-level command. Recovery skips tokens to the matching close-paren
  of the current command via a paren-depth counter, so one bad command never
  corrupts the next.
- **`check-sat` output:** `sat` / `unsat` / `unknown` on stdout. `unknown` for
  any parsed-but-unsupported fragment (Int arithmetic, etc.) via the existing
  downstream fence.
- **Never panics on input.** `Token::Error`, unbalanced parens at EOF, etc. all
  become `Diagnostic`s. Internal invariant violations still `debug_assert!` /
  panic (design §10) — those are bugs, not input.

---

## 9. Testing Strategy (design §11)

- **Unit (parser):** each command; each term feature; let shadowing &
  parallel-binding; define-fun expansion; `/`-folding and linear-division
  rewrite; decimal → rational; n-ary chaining shapes; Int→Real coercion; every
  `(error …)` path; recovery-continues-correctly.
- **Round-trip property test (§11.2):** `parse → print → parse` is identity on
  the interned term DAG (uses the `print.rs` minimal printer).
- **Fuzzing (§11.4a):** `cargo-fuzz` target feeding random bytes / grammar-driven
  s-expressions → the parser **never panics**.
- **Differential / e2e (§11.3):** feed real `.smt2` text (QF_UF, QF_LRA,
  QF_UFLRA) through `parser → Solver` and compare `sat`/`unsat` against the
  existing z3 oracle harness — letting the oracle tests run from **text** rather
  than hand-built API terms. Any sat/unsat disagreement is a P0 bug; `unknown`
  is never a failure.
- **CI:** existing gates (`nextest`, `clippy -D warnings`, `fmt --check`,
  `deny check`) extend to the new crates automatically. `logos` is permissive
  (MIT/Apache) — passes `cargo deny`.

---

## 10. Deliverable

A `shinri-frontend` crate (the `Command` IR) and a `shinri-parser` crate
(`logos` lexer + interning recursive descent) that, wired to `shinri-solver`'s
new `ctx_mut` + `execute`, read SMT-LIB 2.6 text and drive the solver
incrementally:

- `set-logic`, `declare-sort/fun/const`, `define-fun`, `assert`, `check-sat`,
  `check-sat-assuming`, `push`/`pop`, `get-model`, `get-value`,
  `get-unsat-core`, `set-option`/`set-info`, `get-info`, `echo`, `reset`,
  `exit`;
- `let`, non-recursive `define-fun`, constant `/`-folding, linear
  division-by-constant;
- SMT-LIB-faithful `(error …)`-and-continue handling; never panics on input;
- pull-based command-incremental streaming;
- the full test harness (unit, round-trip property, fuzz, differential-from-text).

This closes the loop so the differential oracle can finally run from real
benchmark text, and leaves a clean seam for the follow-on `shinri-cli` binary
(stdin/file I/O, flags, resource limits) to wrap the driver loop.

---

## Appendix — Open Integration Points (resolve while implementing)

1. **`shinri-num` numeral constructor:** exact API to build an `Integer` from a
   decimal string (`from_str_radix` vs limb construction) and a `Rational` from
   a decimal — confirm against the real crate.
2. **`Rational` operator ergonomics:** `recip`, `&a * &b` vs `a * b` for the
   `/`-folding and linear-division rewrites.
3. **`Solver` capability wiring:** whether `get-unsat-core` is available yet; if
   not, `execute` returns `(error "unsupported")` rather than blocking the
   milestone.
4. **`CommandResponse` vs direct stdout:** whether `execute` returns a response
   value the driver prints, or writes competition output itself. Pick one while
   implementing the solver edit; the parser is unaffected either way.
