# Slice 51 — String literals: decode SMT-LIB 2.6 `\u` escapes

Status: design approved in chat 2026-09-30. Picks up baseline rank 3's
remaining string rows (`docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`,
`## Next slices`, rank 3: "the QF_S wrong-`unsat` is the highest value single
row") and the slice-50 carry-over of the QF_S and QF_SLIA wrong rows
(`docs/superpowers/research/2026-09-29-smtlib-2024-slice50-uflia-report.md`,
`## Queued for the next slice`).

**Area:** `shinri-core` (new leaf module `smtlib_string`), `shinri-parser`
(`Token::Str` in `parser.rs`, `ConstVal::String` in `print.rs`),
`shinri-theory` (`model.rs::format_modelval`), a comment in
`shinri-str/src/code_conv.rs`. Tests in `shinri-core`, `shinri-parser`
(`roundtrip.rs`), and `shinri-solver` (`script_e2e`, `qfs_differential`). No
lexer change, no solver or theory logic change, no `Combiner` change.
**This touches the untrusted-input edge** (`docs/threat-model.md`, trust
boundary: SMT-LIB text entering the parser).

## 1. Summary

### 1.1 The defect

The parser never decodes the escape sequences that the SMT-LIB 2.6 theory of
strings defines. `crates/shinri-parser/src/parser.rs:476` (`Token::Str`) only
un-doubles `""` to `"`. The literal `"\u{a}"` is interned as the five
characters `\`, `u`, `{`, `a`, `}` rather than one newline.

Every answer on a formula that contains an escape is therefore an answer to a
different formula. It is right only when the misread escape happens not to
matter.

### 1.2 Minimal reproducers (on `4c7ade5`)

```
(declare-const X String)
(assert (= X "\u{61}")) (assert (= X "a"))
(check-sat)                                  ; shinri: unsat   expected: sat
```

```
(declare-const X String)
(assert (= X "\u{1}"))
(assert (str.in_re X (re.++ (re.* re.allchar) (re.range "a" "z") (re.* re.allchar))))
(check-sat)                                  ; shinri: sat     expected: unsat
```

In the second, the undecoded `\u{1}` contains the letter `u`, so it matches
`Σ*[a-z]Σ*`.

### 1.3 Evidence

The two rows named by the queue:

| row | `:status` | shinri | cause |
| --- | --- | --- | --- |
| `QF_S/20230329-automatark-lu/instance10773.smt2` | `sat` | `unsat` | `X = "/\u{0}/\u{a}"` is a model. Undecoded, it contains letters, so it matches the negated `Σ*[a-z]Σ*\n` branch. |
| `QF_S/20230329-automatark-lu/instance09174.smt2` | `unsat` | `sat` | Undecoded, `"\u{a}"` gives the letter pair `am`/`PM` four trailing characters, so it matches the `..{4}` branch. |

A throwaway pre-decoder rewrote every `\u{…}` escape to its character (and
`"` to `""`) and re-ran all 39 `wrong` QF_S/QF_SLIA rows of the slice-50 run
(`bench/results/slice50/results.jsonl`) through the `4c7ade5` binary:

| rows | today | pre-decoded |
| --- | --- | --- |
| QF_S `instance10773`, `instance09174` | wrong | correct (both) |
| QF_SLIA `20230329-denghang`, 35 | wrong `sat` | 31 `unsat` (z3's answer), 4 `unknown` |
| QF_SLIA `20190311-str-small-rw-Noetzli`, 2 | wrong `sat` | wrong `sat`; they contain no escape, so this is a different defect |

### 1.4 Blast radius

17,971 of 18,940 QF_S files and 24,650 of 84,395 QF_SLIA files contain `\u`.
No corpus file contains a surrogate escape (U+D800–U+DFFF). Two files use the
4-digit form `\ud₃d₂d₁d₀`.

The output side has the mirror defect. `print.rs` and `format_modelval` escape
only `"`. A model value containing a newline is printed raw. A value
containing the characters `\u{61}` is printed so that it re-parses as `a`.

## 2. Scope

**In:**
- decoding every 2.6 escape form in string literals;
- rejecting surrogate escapes;
- encoding string values on every value-printing path, so printing and
  re-parsing gives back the same string;
- tests and measurement (§6, §7).

**Out** (queued in §10):
- surrogate support, which is §9 approach 3;
- the Noetzli pair;
- the 4 denghang rows that become `unknown`;
- SMT-LIB 2.5 escapes (`\x..`, `\n`, …), which 2.6 dropped;
- rejecting raw non-ASCII UTF-8 in input. It is accepted as today, although
  2.6 restricts literals to printable ASCII.

## 3. The shared module: `shinri_core::smtlib_string`

It is a leaf module with no dependencies inside the workspace. It lives in
`shinri-core` because that is the one crate both the parser and
`shinri-theory` depend on. Both directions of the literal syntax live in this
one place.

### 3.1 `decode_literal(body: &str) -> Result<String, LiteralError>`

`body` is the text between the outer quotes. One left-to-right pass:

1. `""` produces `"`.
2. `\ud₃d₂d₁d₀` (exactly four hex digits) produces code point `0xd₃d₂d₁d₀`.
3. `\u{d₀}` … `\u{d₃d₂d₁d₀}` (one to four hex digits) produces that code point.
4. `\u{d₄d₃d₂d₁d₀}` (five hex digits) produces that code point **only if**
   `d₄ ∈ [0-2]`, which bounds the value by U+2FFFF.
5. Hex digits are case-insensitive.
6. Any other sequence is kept **literally**, character by character, as the
   standard requires. Examples: `\u{30000}`, `\u{}`, `\u{123456}`, `\u12`,
   `\n`, a trailing `\`. The scan then continues after the `\`, so
   `\\u{61}` decodes to `\a`: the first `\` stays literal and the second
   starts a valid escape.
7. A form-2, form-3 or form-4 escape whose value is in `0xD800..=0xDFFF`
   returns `LiteralError::Surrogate { offset }`.

Code points in `0..=0x2FFFF` other than surrogates are valid Rust `char`s, so
the output is a `String` with no loss.

### 3.2 `encode_literal(s: &str) -> String`

It returns the full quoted literal, `"` … `"`. Character by character:

- `"` produces `""`;
- `\` produces `\u{5c}`. Encoding every backslash is the simplest rule that
  stops an accidental `\u…` in a value from re-parsing as an escape;
- characters in `0x20..=0x7E` are written as themselves;
- other characters up to U+2FFFF produce `\u{<lowercase hex, no padding>}`;
- characters above U+2FFFF are written raw. No valid escape exists for them,
  and `decode_literal` passes raw characters through, so the round trip still
  holds.

**Invariant:** `decode_literal(body(encode_literal(s))) == Ok(s)` for every
Rust `String` `s`, where `body` strips the outer quotes.

### 3.3 Call sites

- `parser.rs` `Token::Str` calls `decode_literal`. `LiteralError::Surrogate`
  maps to `Diagnostic` "unsupported: surrogate code point in string literal",
  with the literal's span. The driver prints `(error …)` and never gives a
  verdict for that command, which is sound.
- `print.rs` `ConstVal::String` calls `encode_literal`. This replaces the
  hand-written loop.
- `shinri-theory/src/model.rs::format_modelval` `ModelVal::String` calls
  `encode_literal`. This replaces `s.replace('"', "\"\"")`.
- `shinri-cli/src/driver.rs::escape` is unchanged. It quotes diagnostic
  messages, not string values.
- `shinri-str/src/code_conv.rs:17–22`: the representational-fence comment
  changes its reason. Input literals still cannot contain surrogates, but
  now because the parser rejects surrogate escapes. The code does not change.

### 3.4 Security (threat-model edge)

- The decoder is a single linear pass. It never allocates more than
  `body.len()` bytes, since every escape is at least as long as its UTF-8
  output.
- It has no `unsafe` code, and it builds `char`s only through
  `char::from_u32` after the range and surrogate checks. It does no indexing
  that could panic on a multi-byte boundary: it iterates over `char`s.
- The `parse_script` fuzz target and the `no_panic` proptest already cover
  this path, and the fuzz target needs no change.

## 4. What this does not change

- The lexer regex `"([^"]|"")*"` already accepts every escape as ordinary
  characters.
- `Context::mk_string_const` still takes decoded values. Internal folds keep
  calling it directly, so decoding at the core layer would decode them twice
  (§9 approach 2).
- No string-theory rule changes. Every solver-side effect in §7 comes from
  the solver now seeing the formula the file actually states.

## 5. Tasks

1. **T1: red pins.** Add to `script_e2e`:
   - the two §1.2 scripts;
   - a minimisation of `instance09174`;
   - `get-value` of a string holding `\u{0}` and a backslash, expecting the
     encoded output;
   - a surrogate-escape script, expecting `(error …)`.

   All of them fail on `main`. The surrogate pin gets a verdict there,
   because the escape is read literally.
2. **T2: `smtlib_string`.** Unit tests (§6.1) and the round-trip proptest
   (§6.2) first, then the implementation.
3. **T3: parser decode.** Wire `Token::Str` and the surrogate `Diagnostic`,
   then add string cases to `roundtrip.rs`.
4. **T4: printers.** Route `print.rs` and `format_modelval` through
   `encode_literal`, and update the `model.rs` unit tests. T1 is green after
   this task.
5. **T5: oracle.** Extend `qfs_differential`'s `ALPHABET` with `"\u{61}"`,
   `"\u{5c}"` and `"\u{0}"`, and fix the `code_conv.rs` comment. Run the
   unfiltered oracle suite.
6. **T6: measurement.** Run the QF_S and QF_SLIA bench re-run (§7) and write
   the report in `docs/superpowers/research/`.

## 6. Testing

### 6.1 Unit tests (`shinri-core`)

- every escape form, with upper- and lower-case hex;
- `\u{2FFFF}` decodes, and `\u{30000}` stays literal;
- `\u{}`, six digits, `\u12`, `\u{12` (unterminated), `\n` and a trailing `\`
  stay literal;
- `퟿` and `\u{E000}` decode;
- `\uD800`, `\u{d800}` and `\u{DFFF}` are `Surrogate`;
- `""` mixed with escapes, and `\\u{61}` decodes to `\a`;
- `encode_literal` on `"`, `\`, `\u{7F}`, `\u{0}`, U+30000 and ASCII.

### 6.2 Property (proptest, `shinri-core`)

- `decode(body(encode(s))) == Ok(s)` for arbitrary `String`, including
  control, astral and above-U+2FFFF characters;
- `encode` output contains only printable ASCII, apart from raw characters
  above U+2FFFF.

### 6.3 Parser

- `roundtrip.rs` gains string literals with escapes, `""` and backslashes.
  It keeps its parse, print, re-parse and equal-`TermId` contract.

### 6.4 End-to-end and oracle

- The T1 pins run in `script_e2e`. Select the whole binary with
  `-E 'binary(script_e2e)'`.
- In `qfs_differential`, the escaped alphabet makes every generated formula
  mix plain and escaped spellings of the same character. z3 decodes the same
  text, so a decoder mismatch shows up as a verdict disagreement.
- Run with `cargo nextest run -p shinri-solver --features oracle`, and record
  the non-zero discovered count.

## 7. Measurement

**Comparison baseline:** `bench/results/slice50/` (fixture sha `4f8f0729b4dd`,
20 s timeout, `solver_md5 b99562b3…`), logics QF_S and QF_SLIA, same fixture
settings.

### Success criteria

1. `instance10773` answers `sat`, and `instance09174` answers `unsat`.
2. None of the 35 denghang rows is `wrong`. The 31 named by §1.3 answer
   `unsat`.
3. The QF_S plus QF_SLIA `wrong` count goes from 39 to at most 2 (the Noetzli
   pair).
4. **There are 0 `correct → wrong` rows, or each one is escalated.** Decoding
   changes the formula in about 42k files, so a new `wrong` row is an existing
   solver defect that decoding has uncovered. Each one is root-caused, named
   in the report, and brought to the user for a merge decision before merge.
5. Every `correct → unknown/timeout` row is listed and triaged in the report.
   These rows are not gated: the pre-slice "correct" answer was to a formula
   the file does not state.
6. The standard gates are green: `mise run test`, `mise run lint`,
   `script_e2e`, and the unfiltered oracle suite with a non-zero count.

## 8. Named reproducers

- `bench/corpus/QF_S/20230329-automatark-lu/instance10773.smt2` (2,322 B)
- `bench/corpus/QF_S/20230329-automatark-lu/instance09174.smt2` (3,300 B)
- `bench/corpus/QF_SLIA/20230329-denghang/instance55060.smt2` (the rank-3
  denghang reproducer)
- the two §1.2 scripts, which become the T1 pins

## 9. Banked, not built

**Approach 2: decode in `Context::mk_string_const`.** Rejected. That is the
wrong layer: internal folds pass values that are already decoded, and they
would be decoded twice.

**Approach 3: full-alphabet strings (`Box<[u32]>` or similar).** This would
support surrogate escapes instead of rejecting them. It is a refactor across
`shinri-str` for zero corpus rows. **Un-bank** if a benchmark or a user needs
surrogates.

## 10. Queued for the next slice

- The Noetzli pair: `str-pred-small-rw_370.smt2` and `_458.smt2`, wrong `sat`,
  no escapes.
- The 4 denghang rows that become `unknown` once decoded. They are named in
  the T6 report.
- Surrogate support (§9 approach 3).
- Carried from slice 50, unchanged: the QF_SLIA `STRING_PATH_PIVOT_BUDGET`
  cliff; the Wisa final-check blow-up; `get-value` echoing purification
  names; the `Owner::Shared` definitional merge; `pending` is not
  backtracked; the blocksworld re-index churn measurement; the `blast_word`
  panic bucket.

## 11. References

- Baseline: `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`
  (§ Next slices, rank 3).
- Slice 50 report: `docs/superpowers/research/2026-09-29-smtlib-2024-slice50-uflia-report.md`.
- Threat model: `docs/threat-model.md`.
- Code:
  - `crates/shinri-parser/src/parser.rs:476` (`Token::Str`)
  - `crates/shinri-parser/src/print.rs:39`
  - `crates/shinri-theory/src/model.rs:129`
  - `crates/shinri-str/src/code_conv.rs:17`
  - `crates/shinri-solver/tests/qfs_differential.rs:172` (`ALPHABET`)
- SMT-LIB 2.6 theory of Unicode strings, § string literals.
