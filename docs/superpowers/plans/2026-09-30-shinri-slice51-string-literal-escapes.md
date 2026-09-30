# Slice 51 — String literals: decode SMT-LIB 2.6 `\u` escapes — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decode the SMT-LIB 2.6 `\u` escapes in string literals, reject surrogate escapes, and encode string values on output so that printing and re-parsing gives back the same string. This removes the 35 escape-caused wrong answers in QF_S and QF_SLIA.

**Architecture:** A new dependency-free leaf module, `shinri_core::smtlib_string`, holds both directions of the literal syntax:

- `decode_literal` is called by the parser at `Token::Str`;
- `encode_literal` is called by the two value printers, `shinri-parser/src/print.rs` and `shinri-theory/src/model.rs`.

No solver or theory logic changes. Every corpus effect comes from the solver now seeing the formula the file actually states.

**Tech Stack:** Rust workspace, `mise` tasks, `cargo nextest` 0.9.140, `proptest` (already a `shinri-core` dev-dependency), z3 4.16.0 from mise behind the `oracle` cargo feature, and `shinri-bench` for corpus runs.

**Spec:** `docs/superpowers/specs/2026-09-30-shinri-slice51-string-literal-escapes-design.md`. Read it alongside this plan:

- §1 gives the defect and evidence;
- §3 gives the exact decode and encode rules;
- §5 lists the tasks;
- §7 gives the measurement and success criteria.

## Global Constraints

- **Branch:** all work goes on `slice51-string-literal-escapes`, branched from `main` at the commit that adds this plan. Open a PR to `main`. Merge with a merge commit when CI is green, then delete the branch on the remote and locally.
- **Pure-Rust mandate:** no native-link dependencies. `deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys` and `cadical-rs`. This slice adds **no** dependency of any kind.
- **Untrusted-input edge:** `Token::Str` decoding is on the parser trust boundary (`docs/threat-model.md`). The decoder must:
  - never panic;
  - never index a `&str` at a position that is not a char boundary;
  - use no `unsafe`;
  - run in time linear in the literal length.
- **Oracle feature gate:** `crates/shinri-solver/tests/qfs_differential.rs` is `#![cfg(feature = "oracle")]`. Every oracle command carries `--features oracle`. **Without it the file compiles to zero tests and the run reads as green.** Always confirm a non-zero discovered count.
- **nextest filters:** use the expression form only. `-E 'test(<name>)'` selects by test name, and `-E 'binary(<name>)'` selects an integration-test binary. A positional `mod::name` filter matches nothing on nextest 0.9.140.
- **Formatting gate:** run `cargo fmt --all` before every push. CI runs `cargo fmt --check` and fails fast.
- **Lint gate:** `cargo clippy --workspace --all-targets -- -D warnings` must be clean. `mise run lint` covers fmt and clippy.
- **Test tier:** no new test may take more than 5 minutes. Never remove `#[ignore]` from the `shinri-fp` exhaustive suites.
- **Tests before fixes:** Task 1 commits tests that stay **red** on the branch until Tasks 3–4 land. Do not push before Task 6. Every "must fail" step records the verbatim failure output in the task report.
- **Never weaken a test to get green.** If a test that must pass after the fix still fails, treat the failing input as evidence. Minimise it and trace it to a named code path before changing anything.
- **Escalation rule (spec §7, criterion 4):** a `correct → wrong` row, or any `X → wrong` where X is not `wrong`, in the Task 7 measurement **blocks the merge**:
  1. root-cause it;
  2. name it in the report;
  3. stop and bring it to the user for a decision.

**Ordering note.** Spec §5 has six tasks. They map as spec T1 → plan 1, T2 → plan 2, T3 → plan 3, T4 → plan 4, T5 → plan 5 and T6 → plan 7. Plan 6 (gates + PR) and plan 8 (whole-branch review + merge) follow the repo convention of slices 47–50.

**Refinement of spec §5 T5.** The spec says to extend `qfs_differential`'s shared `ALPHABET`. That constant has hard-coded consumers that would break:

- `ALPHABET[self.rng.below(3)]` at line 615;
- character codes `97 + below(3)` at line 594;
- Rust-side witness building from the spelling at line 724.

Task 5 therefore adds a **dedicated** escaped-literal generator and test. It keeps the spec's intent: a differential that mixes plain and escaped spellings of the same character against z3. It leaves the existing families untouched.

## Review Focus

These are the input classes the spec implies but does not name. Each is the kind of input a person writing string benchmarks will hit first, and each gets a test in the task that owns the code:

1. **Escapes inside regex operands.** `(re.range "\u{61}" "\u{7a}")` must be the single-character range a–z. On `main`, both endpoints are 6-character strings, so the range is empty. → Task 1, `slice51_escaped_range_endpoints_sat`.
2. **Escapes next to doubled quotes.** The body `\u{22}""` must decode to two `"` characters, and printing it must give `""""` again. → Task 2, `decode_escape_next_to_doubled_quote`; Task 3, `parser_decodes_escape_next_to_doubled_quote`.
3. **A hostile run of unterminated `\u{`.** A 200,000-repeat `\u{` body must decode quickly, as literal text. An implementation that scans to the end of the string for each `}` is quadratic and would hang this test. → Task 2, `decode_many_unterminated_escapes_is_linear`.
4. **A surrogate escape in metadata.** `(set-info :notes "\u{d800}")` is not a string term. It must **not** turn into an error, because only `Token::Str` in term position decodes. → Task 3, `set_info_with_surrogate_escape_is_not_an_error` (a guard; green on `main`).
5. **A raw control character typed straight into the input** (an actual newline inside `"…"`). The printer must write it back as `\u{a}`, not raw. → Task 1, `slice51_get_value_encodes_raw_newline`.

## File Structure

| file | responsibility | task |
| --- | --- | --- |
| `crates/shinri-solver/tests/script_e2e.rs` | end-to-end pins: spec §1.2, the `instance09174` minimisation, printing, surrogate, Review Focus 1 and 5 | 1 |
| `crates/shinri-core/src/smtlib_string.rs` (new) | `decode_literal`, `encode_literal`, `LiteralError`; unit tests and proptest | 2 |
| `crates/shinri-core/src/lib.rs` | `pub mod smtlib_string;` | 2 |
| `crates/shinri-parser/src/parser.rs:476` | `Token::Str` calls `decode_literal`; surrogate → `Diagnostic` | 3 |
| `crates/shinri-parser/tests/string_literals.rs` (new) | parser-level decode tests | 3 |
| `crates/shinri-parser/src/print.rs:39` | `ConstVal::String` calls `encode_literal` | 4 |
| `crates/shinri-theory/src/model.rs:129` | `ModelVal::String` calls `encode_literal`; unit test | 4 |
| `crates/shinri-parser/tests/roundtrip.rs` | string-literal round-trip cases | 4 |
| `crates/shinri-solver/tests/qfs_differential.rs` | `EscGen` and `qfs_escaped_literals_match_z3` | 5 |
| `crates/shinri-str/src/code_conv.rs:17-22` | comment: why literals have no surrogates | 5 |
| `docs/superpowers/research/2026-09-30-smtlib-2024-slice51-escapes-report.md` (new) | the measured outcome | 7 |
| `docs/superpowers/specs/2026-09-30-shinri-slice51-string-literal-escapes-design.md` | append `## 12. Measured outcomes` | 7 |

---

### Task 0: Branch

- [ ] **Step 1: Commit this plan to `main`, then branch**

```bash
git checkout main
git add docs/superpowers/plans/2026-09-30-shinri-slice51-string-literal-escapes.md
git commit -m "docs(plan): slice51 - decode SMT-LIB 2.6 string literal escapes"
git checkout -b slice51-string-literal-escapes
```

---

### Task 1: Red end-to-end pins

**Files:**
- Modify: `crates/shinri-solver/tests/script_e2e.rs` (append at end of file)

**Interfaces:**
- Consumes: the file's existing `run_script(src: &str) -> Vec<String>` helper, which returns one line per response: `"sat"`/`"unsat"`/`"unknown"`, the `get-value` text, or `(error "<msg>")`.
- Produces: nothing used by later tasks. These pins are the acceptance tests for Tasks 3 and 4.

Every expected value below was checked against the `main` binary while the plan was written. The "on `main`" column is what the red run must show.

| test | expected after the fix | on `main` |
| --- | --- | --- |
| `slice51_escape_decodes_to_same_char_sat` | `["sat"]` | `["unsat"]` |
| `slice51_control_char_is_not_a_letter_unsat` | `["unsat"]` | `["sat"]` |
| `slice51_newline_escape_is_one_char_unsat` | `["unsat"]` | `["sat"]` |
| `slice51_escaped_range_endpoints_sat` | `["sat"]` | `["unsat"]` |
| `slice51_get_value_encodes_control_and_backslash` | `["sat", "((X \"\\u{0}\\u{5c}\"))"]` | `["unsat", "(error …)"]` |
| `slice51_get_value_encodes_raw_newline` | `["sat", "((X \"a\\u{a}\"))"]` | raw newline in value |
| `slice51_surrogate_escape_is_error` | first line starts `(error "unsupported: surrogate` | `["sat"]` |

- [ ] **Step 1: Write the failing tests**

Append to `crates/shinri-solver/tests/script_e2e.rs`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 51: SMT-LIB 2.6 `\u` escapes in string literals (spec §1.2, §3).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn slice51_escape_decodes_to_same_char_sat() {
    // Spec §1.2: "\u{61}" IS "a". Pre-slice the escape was 6 literal chars.
    let out = run_script(
        r#"(set-logic QF_S)(declare-const X String)
           (assert (= X "\u{61}"))(assert (= X "a"))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn slice51_control_char_is_not_a_letter_unsat() {
    // Spec §1.2, minimised from QF_S instance10773: undecoded "\u{1}" contains
    // the letter `u`, so it wrongly matched Σ*[a-z]Σ*.
    let out = run_script(
        r#"(set-logic QF_S)(declare-const X String)
           (assert (= X "\u{1}"))
           (assert (str.in_re X (re.++ (re.* re.allchar) (re.range "a" "z") (re.* re.allchar))))
           (check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn slice51_newline_escape_is_one_char_unsat() {
    // Minimised from QF_S instance09174: after the letter pair "am" only ONE
    // char ("\u{a}") follows, so ..{4} cannot match. Undecoded, five follow.
    let out = run_script(
        r#"(set-logic QF_S)(declare-const X String)
           (assert (str.in_re X (re.++ (str.to_re "1:00 am") (str.to_re "\u{a}"))))
           (assert (str.in_re X (re.++ (re.* re.allchar) (re.range "a" "z") (re.range "a" "z")
                                       ((_ re.loop 4 4) re.allchar) (re.* re.allchar))))
           (check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn slice51_escaped_range_endpoints_sat() {
    // Review Focus 1: escaped re.range endpoints are single characters.
    let out = run_script(
        r#"(set-logic QF_S)(declare-const X String)
           (assert (= X "q"))(assert (str.in_re X (re.range "\u{61}" "\u{7a}")))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn slice51_get_value_encodes_control_and_backslash() {
    // Spec §3.2: NUL and backslash print as \u{..}. The length pin makes this
    // red on main, where the literal is 12 undecoded chars.
    let out = run_script(
        r#"(set-logic QF_S)(declare-const X String)
           (assert (= X "\u{0}\u{5c}"))(assert (= (str.len X) 2))
           (check-sat)(get-value (X))"#,
    );
    assert_eq!(out, vec!["sat".to_string(), r#"((X "\u{0}\u{5c}"))"#.to_string()]);
}

#[test]
fn slice51_get_value_encodes_raw_newline() {
    // Review Focus 5: a raw newline typed inside the literal prints escaped.
    let out = run_script(
        "(set-logic QF_S)(declare-const X String)\
         (assert (= X \"a\n\"))(check-sat)(get-value (X))",
    );
    assert_eq!(out, vec!["sat".to_string(), r#"((X "a\u{a}"))"#.to_string()]);
}

#[test]
fn slice51_surrogate_escape_is_error() {
    // Spec §3.1 rule 7 / §3.3: a surrogate escape is a clean error, never a verdict.
    let out = run_script(
        r#"(set-logic QF_S)(declare-const X String)
           (assert (= X "\u{d800}"))(check-sat)"#,
    );
    assert!(
        out[0].starts_with("(error \"unsupported: surrogate"),
        "expected a surrogate error first, got {out:?}"
    );
}
```

- [ ] **Step 2: Run them and confirm all seven fail**

Run: `cargo nextest run -p shinri-solver -E 'binary(script_e2e) and test(/^slice51_/)'`

Expected: **7 tests discovered, 7 FAIL**, with the left-hand values from the "on `main`" column. `slice51_surrogate_escape_is_error` fails its `assert!` with `got ["sat"]`. Paste the failure summary into the task report. A count other than 7 means the filter is wrong. Fix the filter; do not proceed on a 0-test run.

- [ ] **Step 3: Commit (red)**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/script_e2e.rs
git commit -m "test(str): slice51 T1 - red pins for \\u escapes in string literals"
```

---

### Task 2: `shinri_core::smtlib_string`

**Files:**
- Create: `crates/shinri-core/src/smtlib_string.rs`
- Modify: `crates/shinri-core/src/lib.rs` (add `pub mod smtlib_string;` after `pub mod proof;`, keeping the list alphabetical)

**Interfaces:**
- Consumes: nothing.
- Produces, for Tasks 3–5:
  - `pub fn decode_literal(body: &str) -> Result<String, LiteralError>`. `body` is the text **between** the outer quotes.
  - `pub fn encode_literal(s: &str) -> String`. It returns the **full** literal, including the outer `"`.
  - `#[derive(Clone, Copy, Debug, PartialEq, Eq)] pub enum LiteralError { Surrogate { offset: usize } }`. `offset` is the byte offset of the escape's `\` within `body`.

- [ ] **Step 1: Write the module with its tests and a stub body**

Create `crates/shinri-core/src/smtlib_string.rs`:

```rust
//! SMT-LIB 2.6 string-literal syntax (theory of Unicode strings): decoding a
//! literal's body, `\u` escapes included, and encoding a value back into a
//! literal. Both directions live here so the parser and the model printers
//! agree on one rule set.

/// The largest code point an escape may denote: the top of the SMT-LIB
/// string alphabet. `\u{d₄d₃d₂d₁d₀}` requires `d₄ ∈ [0-2]`, which is exactly
/// this bound.
const MAX_ESCAPE: u32 = 0x2FFFF;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiteralError {
    /// A well-formed escape denotes a surrogate (U+D800..=U+DFFF). The SMT-LIB
    /// alphabet includes these, but `str` cannot hold them. `offset` is the
    /// byte offset of the escape's `\` within the body.
    Surrogate { offset: usize },
}

/// Decode the body of a string literal (the text between the outer quotes):
/// `""` → `"`, and every well-formed `\ud₃d₂d₁d₀` / `\u{d…}` escape → its
/// character. Any other sequence is kept literally, as the standard requires.
pub fn decode_literal(body: &str) -> Result<String, LiteralError> {
    let _ = body;
    unimplemented!("slice51 T2")
}

/// Encode `s` as a full SMT-LIB literal, outer quotes included. `"` → `""`;
/// `\` → `\u{5c}`, so no accidental `\u…` can re-parse as an escape; printable
/// ASCII is written as itself; any other char ≤ U+2FFFF → `\u{hex}`. Chars
/// above U+2FFFF have no escape, so they are written raw, and
/// `decode_literal` passes them through unchanged.
pub fn encode_literal(s: &str) -> String {
    let _ = s;
    unimplemented!("slice51 T2")
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn dec(body: &str) -> String {
        decode_literal(body).expect("no surrogate")
    }

    #[test]
    fn decode_plain_and_doubled_quote() {
        assert_eq!(dec("abc"), "abc");
        assert_eq!(dec(r#"a""b"#), "a\"b");
        assert_eq!(dec(""), "");
    }

    #[test]
    fn decode_every_escape_form() {
        assert_eq!(dec(r"a"), "a");
        assert_eq!(dec(r"\u{61}"), "a");
        assert_eq!(dec(r"\u{061}"), "a");
        assert_eq!(dec(r"\u{0061}"), "a");
        assert_eq!(dec(r"\u{00061}"), "a");
        assert_eq!(dec(r"\u{0}"), "\u{0}");
        assert_eq!(dec(r"\u{A}\u{a}\u000A\u000a"), "\n\n\n\n");
        assert_eq!(dec(r"x\u{5c}y"), "x\\y");
    }

    #[test]
    fn decode_alphabet_boundaries() {
        assert_eq!(dec(r"\u{2FFFF}"), "\u{2FFFF}");
        assert_eq!(dec(r"퟿"), "\u{D7FF}");
        assert_eq!(dec(r"\u{E000}"), "\u{E000}");
        // d₄ = 3: not an escape; kept literally (9 chars).
        assert_eq!(dec(r"\u{30000}"), r"\u{30000}");
    }

    #[test]
    fn decode_keeps_malformed_sequences_literally() {
        for s in [
            r"\u{}", r"\u{123456}", r"\u12", r"\u{12", r"\n", r"\", r"\u", r"\u{g}", r"\uFFFg",
        ] {
            assert_eq!(dec(s), s, "{s:?} must stay literal");
        }
    }

    #[test]
    fn decode_rescans_after_a_literal_backslash() {
        // The first `\` is literal; the second starts a valid escape.
        assert_eq!(dec(r"\\u{61}"), r"\a");
    }

    #[test]
    fn decode_escape_next_to_doubled_quote() {
        // Review Focus 2: \u{22} is `"`, then `""` is another `"`.
        assert_eq!(dec(r#"\u{22}"""#), "\"\"");
    }

    #[test]
    fn decode_rejects_surrogates_in_both_forms() {
        assert_eq!(decode_literal(r"\uD800"), Err(LiteralError::Surrogate { offset: 0 }));
        assert_eq!(decode_literal(r"ab\u{d800}"), Err(LiteralError::Surrogate { offset: 2 }));
        assert_eq!(decode_literal(r"\u{DFFF}"), Err(LiteralError::Surrogate { offset: 0 }));
        assert_eq!(decode_literal(r"é\udbff"), Err(LiteralError::Surrogate { offset: 2 }));
    }

    #[test]
    fn decode_many_unterminated_escapes_is_linear() {
        // Review Focus 3: a quadratic scan for `}` would hang here.
        let body = r"\u{".repeat(200_000);
        assert_eq!(dec(&body), body);
    }

    #[test]
    fn encode_rules() {
        assert_eq!(encode_literal("ab ~"), r#""ab ~""#);
        assert_eq!(encode_literal("a\"b"), r#""a""b""#);
        assert_eq!(encode_literal("\\"), r#""\u{5c}""#);
        assert_eq!(encode_literal("\u{0}\n\u{7f}é"), r#""\u{0}\u{a}\u{7f}\u{e9}""#);
        assert_eq!(encode_literal("\u{2FFFF}"), r#""\u{2ffff}""#);
        assert_eq!(encode_literal("\u{30000}"), "\"\u{30000}\"");
        assert_eq!(encode_literal(""), r#""""#);
    }

    fn body(lit: &str) -> &str {
        &lit[1..lit.len() - 1]
    }

    proptest! {
        #[test]
        fn encode_then_decode_roundtrips(s in any::<String>()) {
            prop_assert_eq!(decode_literal(body(&encode_literal(&s))), Ok(s));
        }

        #[test]
        fn encode_emits_printable_ascii_or_out_of_alphabet_chars(s in any::<String>()) {
            for c in encode_literal(&s).chars() {
                prop_assert!((' '..='~').contains(&c) || (c as u32) > MAX_ESCAPE, "{:?}", c);
            }
        }
    }
}
```

Add to `crates/shinri-core/src/lib.rs`, after `pub mod proof;`:

```rust
pub mod smtlib_string;
```

- [ ] **Step 2: Run the tests and confirm they fail**

Run: `cargo nextest run -p shinri-core -E 'test(/smtlib_string::/)'`

Expected: **11 tests discovered**, and every one FAILs with a panic `not implemented: slice51 T2`.

- [ ] **Step 3: Implement**

Replace the two stub bodies, and add the private helper `parse_escape` above `decode_literal`:

```rust
/// Parse an escape whose leading `\` has already been consumed. On success,
/// return its code point and how many bytes of `s` it spans. `None` means the
/// sequence is not a well-formed 2.6 escape and must be kept literally.
fn parse_escape(s: &str) -> Option<(u32, usize)> {
    let after_u = s.strip_prefix('u')?;
    if let Some(inner) = after_u.strip_prefix('{') {
        // At most 5 digits, so the `}` is within the first 6 bytes. Bounding
        // the search keeps decoding linear on hostile input (Review Focus 3).
        let close = inner.bytes().take(6).position(|b| b == b'}')?;
        let digits = &inner[..close];
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_hexdigit()) {
            return None;
        }
        let code = u32::from_str_radix(digits, 16).ok()?;
        // Only a 5-digit escape can exceed MAX_ESCAPE, and it does so exactly
        // when d₄ > 2.
        if code > MAX_ESCAPE {
            return None;
        }
        return Some((code, "u{".len() + close + "}".len()));
    }
    let digits = after_u.get(..4)?;
    if !digits.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    Some((u32::from_str_radix(digits, 16).ok()?, "u".len() + 4))
}

pub fn decode_literal(body: &str) -> Result<String, LiteralError> {
    let mut out = String::with_capacity(body.len());
    let mut rest = body;
    while let Some(ch) = rest.chars().next() {
        let offset = body.len() - rest.len();
        if ch == '"' && rest[1..].starts_with('"') {
            out.push('"');
            rest = &rest[2..];
            continue;
        }
        if ch == '\\' {
            if let Some((code, len)) = parse_escape(&rest[1..]) {
                if (0xD800..=0xDFFF).contains(&code) {
                    return Err(LiteralError::Surrogate { offset });
                }
                out.push(char::from_u32(code).expect("non-surrogate code ≤ U+2FFFF is a char"));
                rest = &rest[1 + len..];
                continue;
            }
        }
        out.push(ch);
        rest = &rest[ch.len_utf8()..];
    }
    Ok(out)
}

pub fn encode_literal(s: &str) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\"\""),
            '\\' => out.push_str(r"\u{5c}"),
            ' '..='~' => out.push(c),
            c if (c as u32) <= MAX_ESCAPE => {
                write!(out, "\\u{{{:x}}}", c as u32).expect("writing to a String cannot fail");
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
```

Keep the doc comments already written on `decode_literal` and `encode_literal`, and remove the `let _ = …; unimplemented!` stub lines.

- [ ] **Step 4: Run the tests and confirm they pass**

Run: `cargo nextest run -p shinri-core -E 'test(/smtlib_string::/)'`

Expected: 11 passed, 0 failed. The linear-time test takes well under 1 s.

- [ ] **Step 5: Clippy the crate**

Run: `cargo clippy -p shinri-core --all-targets -- -D warnings`

Expected: clean.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/shinri-core/src/smtlib_string.rs crates/shinri-core/src/lib.rs
git commit -m "feat(core): slice51 T2 - smtlib_string decode/encode for SMT-LIB 2.6 literals"
```

---

### Task 3: Parser decodes string literals

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs:476-481` (the `Token::Str` arm of the term parser)
- Create: `crates/shinri-parser/tests/string_literals.rs`

**Interfaces:**
- Consumes: `shinri_core::smtlib_string::{decode_literal, LiteralError}` from Task 2.
- Produces: string constants in the term DAG now hold **decoded** values. A surrogate escape surfaces as `Diagnostic { message: "unsupported: surrogate code point in string literal", span: <literal span> }`.

`token_value_text` (parser.rs:123, attribute values such as `set-info`) is deliberately **not** changed. It handles metadata, not string terms (Review Focus 4).

- [ ] **Step 1: Write the failing parser tests**

Create `crates/shinri-parser/tests/string_literals.rs`:

```rust
//! Slice 51: string literals decode SMT-LIB 2.6 `\u` escapes (spec §3).
use shinri_core::Context;
use shinri_parser::Parser;

/// Parse `src` as one term; return its string-constant value or the
/// diagnostic message.
fn lit(src: &str) -> Result<String, String> {
    let mut ctx = Context::new();
    let mut p = Parser::new(src);
    p.parse_term_pub(&mut ctx)
        .map(|t| ctx.string_const_value(t).expect("a string constant").to_owned())
        .map_err(|d| d.message)
}

#[test]
fn parser_decodes_escapes() {
    assert_eq!(lit(r#""\u{61}bc""#), Ok("abc".to_owned()));
    assert_eq!(lit(r#""\u{a}""#), Ok("\n".to_owned()));
}

#[test]
fn parser_escaped_and_plain_spellings_are_one_term() {
    let mut ctx = Context::new();
    let a = Parser::new(r#""a""#).parse_term_pub(&mut ctx).unwrap();
    let esc = Parser::new(r#""\u{61}""#).parse_term_pub(&mut ctx).unwrap();
    assert_eq!(a, esc, "hash-consing must see one literal");
}

#[test]
fn parser_decodes_escape_next_to_doubled_quote() {
    // Review Focus 2.
    assert_eq!(lit(r#""\u{22}""""#), Ok("\"\"".to_owned()));
}

#[test]
fn parser_keeps_invalid_escape_literally() {
    assert_eq!(lit(r#""\u{30000}""#), Ok(r"\u{30000}".to_owned()));
}

#[test]
fn parser_rejects_surrogate_escape() {
    assert_eq!(
        lit(r#""\u{d800}""#),
        Err("unsupported: surrogate code point in string literal".to_owned())
    );
}

#[test]
fn set_info_with_surrogate_escape_is_not_an_error() {
    // Review Focus 4: attribute values are metadata, not string terms.
    let mut ctx = Context::new();
    let mut p = Parser::new(r#"(set-info :notes "\u{d800}")"#);
    let cmd = p.next_command(&mut ctx).expect("one command");
    assert!(cmd.is_ok(), "set-info must not decode: {cmd:?}");
}
```

If `next_command`'s `Ok` type does not implement `Debug`, replace `{cmd:?}` in the last assert with `{:?}` over `cmd.as_ref().err().map(|d| &d.message)`.

- [ ] **Step 2: Run them and confirm the decode tests fail**

Run: `cargo nextest run -p shinri-parser -E 'binary(string_literals)'`

Expected: **6 discovered**.

- These FAIL: `parser_decodes_escapes`, `parser_escaped_and_plain_spellings_are_one_term`, `parser_decodes_escape_next_to_doubled_quote` and `parser_rejects_surrogate_escape`.
- These PASS, because they are guards: `parser_keeps_invalid_escape_literally` and `set_info_with_surrogate_escape_is_not_an_error`.

- [ ] **Step 3: Implement**

In `crates/shinri-parser/src/parser.rs`, replace the `Token::Str` arm:

```rust
            Token::Str(s) => {
                // Strip outer quotes and unescape "" -> " (SMT-LIB string literal syntax).
                let raw = &s[1..s.len() - 1];
                let val = raw.replace("\"\"", "\"");
                Ok(ctx.mk_string_const(&val))
            }
```

with:

```rust
            Token::Str(s) => {
                // Strip the outer quotes, then decode `""` and the 2.6 `\u`
                // escapes. A surrogate escape is unrepresentable in `str`, so it
                // is a clean error, never a verdict on a mis-read literal.
                let body = &s[1..s.len() - 1];
                let val = decode_literal(body).map_err(|LiteralError::Surrogate { .. }| {
                    Diagnostic::new(sp, "unsupported: surrogate code point in string literal")
                })?;
                Ok(ctx.mk_string_const(&val))
            }
```

Add `use shinri_core::smtlib_string::{decode_literal, LiteralError};` to the file's `use` block. If `sp` is moved earlier in the arm's enclosing function, use `sp.clone()`, matching the neighbouring arms.

- [ ] **Step 4: Run the parser tests and the decode pins**

Run: `cargo nextest run -p shinri-parser`

Expected: all pass, including 6/6 in `string_literals`.

Run: `cargo nextest run -p shinri-solver -E 'binary(script_e2e) and test(/^slice51_/)'`

Expected: 7 discovered. These PASS now: `escape_decodes_to_same_char_sat`, `control_char_is_not_a_letter_unsat`, `newline_escape_is_one_char_unsat`, `escaped_range_endpoints_sat` and `surrogate_escape_is_error`. The two `get_value_encodes_*` tests still FAIL, because the printer still emits raw characters. Task 4 fixes that. Record the output.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-parser/src/parser.rs crates/shinri-parser/tests/string_literals.rs
git commit -m "fix(parser): slice51 T3 - decode \\u escapes in string literals; reject surrogates"
```

---

### Task 4: Printers encode string values

**Files:**
- Modify: `crates/shinri-parser/src/print.rs:37-48` (`ConstVal::String` arm)
- Modify: `crates/shinri-theory/src/model.rs:129` (`ModelVal::String` arm) and its `format_tests` module
- Modify: `crates/shinri-parser/tests/roundtrip.rs`

**Interfaces:**
- Consumes: `shinri_core::smtlib_string::encode_literal` from Task 2.
- Produces: `print_term` and `format_modelval` output for strings that `decode_literal` inverts exactly.

- [ ] **Step 1: Write the failing tests**

Append to `crates/shinri-parser/tests/roundtrip.rs`:

```rust
#[test]
fn roundtrips_string_literals_with_escapes() {
    // Slice 51: print must re-encode so that re-parse yields the same TermId.
    roundtrip(r#""plain""#, |_, _| {});
    roundtrip(r#""a""b""#, |_, _| {});
    roundtrip(r#""\u{0}\u{a}\u{7f}é""#, |_, _| {});
    // A decoded backslash followed by `u{61}` must NOT re-parse as "a".
    roundtrip(r#""\u{5c}u{61}""#, |_, _| {});
    roundtrip(r#""\u{2FFFF}""#, |_, _| {});
}
```

In `crates/shinri-theory/src/model.rs`, extend `format_string_modelval_escapes_quotes` with:

```rust
        assert_eq!(
            format_modelval(&ModelVal::String("\n\\\u{0}".into())),
            r#""\u{a}\u{5c}\u{0}""#
        );
```

- [ ] **Step 2: Run them and confirm they fail**

Run: `cargo nextest run -p shinri-parser -E 'test(roundtrips_string_literals_with_escapes)'`

Expected: 1 discovered, FAIL on the `\u{5c}u{61}` case (`roundtrip changed the term`).

Run: `cargo nextest run -p shinri-theory -E 'test(format_string_modelval_escapes_quotes)'`

Expected: 1 discovered, FAIL. The left side holds a raw newline, backslash and NUL.

- [ ] **Step 3: Implement**

In `crates/shinri-parser/src/print.rs`, replace the `ConstVal::String` arm body:

```rust
            ConstVal::String(_) => {
                // Render as SMT-LIB string literal: "" wraps, internal " is escaped as "".
                let s = ctx.string_const_value(t).unwrap();
                out.push('"');
                for ch in s.chars() {
                    if ch == '"' {
                        out.push_str("\"\"");
                    } else {
                        out.push(ch);
                    }
                }
                out.push('"');
            }
```

with:

```rust
            ConstVal::String(_) => {
                // The inverse of the parser's decode_literal (slice 51).
                let s = ctx.string_const_value(t).unwrap();
                out.push_str(&shinri_core::smtlib_string::encode_literal(s));
            }
```

In `crates/shinri-theory/src/model.rs:129`, replace:

```rust
        ModelVal::String(s) => format!("\"{}\"", s.replace('"', "\"\"")),
```

with:

```rust
        ModelVal::String(s) => shinri_core::smtlib_string::encode_literal(s),
```

- [ ] **Step 4: Run the tests and confirm they pass**

Run: `cargo nextest run -p shinri-parser -p shinri-theory`

Expected: all pass.

Run: `cargo nextest run -p shinri-solver -E 'binary(script_e2e)'`

Expected: the whole binary passes, including **7/7** `slice51_*`. Record the discovered count (the slice-50 report had 73; it should now be 80).

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-parser/src/print.rs crates/shinri-parser/tests/roundtrip.rs crates/shinri-theory/src/model.rs
git commit -m "fix(print): slice51 T4 - encode string values as SMT-LIB 2.6 literals"
```

---

### Task 5: Escaped-literal oracle differential, and the `code_conv` comment

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (append at end of file)
- Modify: `crates/shinri-str/src/code_conv.rs:17-22` (comment only)

**Interfaces:**
- Consumes these existing helpers in `qfs_differential.rs`:
  - `Lcg`, with `next()` and `below(n)`;
  - `enum Verdict { Sat, Unsat, Unknown }`;
  - `shinri_verdict(&str) -> Verdict`;
  - `shinri_lines(&str) -> Vec<String>`, which asserts zero guard bailouts;
  - `z3_verdict(&str) -> Verdict`;
  - `parse_string_values(&str) -> Vec<(String, String)>`;
  - `z3_with_model(&str, &[(String, String)]) -> Verdict`.

  `parse_string_values` keeps the printed `\u{..}` text raw, and `smt_escape` passes printable ASCII through. The witness therefore reaches z3 still encoded, and z3 decodes it. That is exactly the path under test.
- Produces: the test `qfs_escaped_literals_match_z3`.

Every spelling in `ESC_SPELLINGS` was checked by hand against z3 4.16.0 while the plan was written, and each group decodes to one character: `(= "a" "\u{61}" "a" "\u{00061}")`, `(= "\u{0}" "\u0000")` and `(= (str.len "\u{a}\u{5c}\u{7e}") 3)` are all `sat`.

- [ ] **Step 1: Write the oracle test**

Append to `crates/shinri-solver/tests/qfs_differential.rs`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 51: escaped string literals. Each group spells ONE character several
// ways, plain and escaped, all valid SMT-LIB 2.6 that z3 decodes identically.
// A decoder mismatch between shinri and z3 surfaces as a verdict
// disagreement or a witness failure.
// ─────────────────────────────────────────────────────────────────────────────

const ESC_SPELLINGS: &[&[&str]] = &[
    &["a", "\\u{61}", "\\u0061", "\\u{00061}"],
    &["b", "\\u{62}", "\\u{0062}"],
    &["\\u{0}", "\\u0000"],
    &["\\u{a}", "\\u000A"],
    &["\\u{5c}", "\\u005c"],
];

const ESC_N_ITERS: usize = 200;

struct EscGen {
    rng: Lcg,
}

impl EscGen {
    /// One character, spelled at random.
    fn spelled_char(&mut self) -> &'static str {
        let group = ESC_SPELLINGS[self.rng.below(ESC_SPELLINGS.len() as u64) as usize];
        group[self.rng.below(group.len() as u64) as usize]
    }

    /// A quoted literal of `lo..=hi` characters.
    fn lit(&mut self, lo: u64, hi: u64) -> String {
        let n = lo + self.rng.below(hi - lo + 1);
        let body: String = (0..n).map(|_| self.spelled_char()).collect();
        format!("\"{body}\"")
    }

    fn atom(&mut self) -> String {
        let v = ["s0", "s1"][self.rng.below(2) as usize];
        match self.rng.below(7) {
            0 => {
                // Non-empty, like the base family's `lit`: `""` would reach the
                // known empty-length seam, which is not what this test is for.
                let l = self.lit(1, 3);
                format!("(= {v} {l})")
            }
            1 => {
                let (l, r) = (self.lit(1, 2), self.lit(1, 2));
                format!("(= {v} (str.++ {l} {r}))")
            }
            2 => format!("(= (str.len {v}) {})", self.rng.below(4)),
            3 => {
                let l = self.lit(1, 2);
                format!("(str.in_re {v} (re.++ (re.* re.allchar) (str.to_re {l}) (re.* re.allchar)))")
            }
            4 => {
                let c = self.lit(1, 1);
                format!("(str.in_re {v} (re.range {c} {c}))")
            }
            5 => {
                let l = self.lit(1, 2);
                format!("(str.prefixof {l} {v})")
            }
            _ => "(= s0 s1)".to_owned(),
        }
    }

    fn body(seed: u64) -> String {
        let mut g = EscGen { rng: Lcg(seed) };
        let mut s =
            String::from("(set-logic QF_S)\n(declare-const s0 String)\n(declare-const s1 String)\n");
        for _ in 0..2 + g.rng.below(3) {
            let a = g.atom();
            if g.rng.below(3) == 0 {
                s.push_str(&format!("(assert (not {a}))\n"));
            } else {
                s.push_str(&format!("(assert {a})\n"));
            }
        }
        s
    }
}

#[test]
fn qfs_escaped_literals_match_z3() {
    let mut rng = Lcg(0x51_51_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness) =
        (0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..ESC_N_ITERS {
        let seed = rng.next();
        let body = EscGen::body(seed);
        let script = format!("{body}(check-sat)\n");
        let ours = shinri_verdict(&script);
        if ours == Verdict::Unknown {
            n_unknown += 1;
            continue;
        }
        let theirs = z3_verdict(&script);
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S ESCAPED-LITERAL DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{script}"
        );
        match ours {
            Verdict::Sat => {
                n_sat += 1;
                let lines = shinri_lines(&format!("{script}(get-value (s0 s1))\n"));
                if let Some(resp) = lines.get(1) {
                    let model = parse_string_values(resp);
                    if !model.is_empty() {
                        assert_eq!(
                            z3_with_model(&body, &model),
                            Verdict::Sat,
                            "WITNESS FAILURE (iter {it}, seed {seed}): model {model:?}\n{body}"
                        );
                        n_witness += 1;
                    }
                }
            }
            Verdict::Unsat => n_unsat += 1,
            Verdict::Unknown => unreachable!(),
        }
    }

    // Equality, length, contains, single-char range and prefixof are all in
    // the decided fragment. A low decided count means the generator drifted.
    assert!(
        n_sat + n_unsat > ESC_N_ITERS / 4,
        "too few decided rows: {n_sat} sat / {n_unsat} unsat of {ESC_N_ITERS}"
    );
    println!(
        "qfs_escaped_literals_match_z3: {ESC_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown / {n_z3skip} z3-unknown; {n_witness} witnesses; 0 disagreements"
    );
}
```

- [ ] **Step 2: Run it on the branch and confirm it passes**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfs_escaped_literals_match_z3)' --no-capture`

Expected: **1 discovered**, PASS. The printed line shows a decided count above 50 and a non-zero witness count. Paste the line into the task report.

- [ ] **Step 3: Prove that the oracle catches the bug**

Temporarily revert the decode. In `crates/shinri-parser/src/parser.rs`, change the `Token::Str` arm's `let val = decode_literal(body)…?;` to:

```rust
                let val = body.replace("\"\"", "\"");
```

Run: `cargo nextest run -p shinri-solver --features oracle -E 'test(qfs_escaped_literals_match_z3)'`

Expected: FAIL with `ESCAPED-LITERAL DISAGREEMENT` or `WITNESS FAILURE`. Paste the seed and the reproducer into the task report. Then restore the file and confirm:

```bash
git checkout crates/shinri-parser/src/parser.rs
git diff --stat   # must show only qfs_differential.rs
```

If the reverted run PASSES, the generator does not exercise decoding. Stop and fix the generator; do not continue.

- [ ] **Step 4: Update the `code_conv` comment**

In `crates/shinri-str/src/code_conv.rs`, replace the last two sentences of the "Representational fence" paragraph:

```rust
//! never rewrites; both survive to the fence. Input literals cannot contain
//! surrogates (the parser does not decode `\u{...}` escapes), so the
//! literal side of an equality needs no surrogate case.
```

with:

```rust
//! never rewrites; both survive to the fence. Input literals cannot contain
//! surrogates (the parser rejects a surrogate `\u` escape as unsupported,
//! slice 51), so the literal side of an equality needs no surrogate case.
```

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/qfs_differential.rs crates/shinri-str/src/code_conv.rs
git commit -m "test(oracle): slice51 T5 - QF_S differential over escaped literal spellings"
```

---

### Task 6: Whole-branch gates and PR

**Files:** none new.

- [ ] **Step 1: Format and lint**

Run: `cargo fmt --all && mise run lint`

Expected: clean.

- [ ] **Step 2: Blocking test tier**

Run: `mise run test`

Expected: all pass. Record the total. Slice 50 recorded 1548; this branch adds 7 e2e tests, 11 core tests, 6 parser tests and 1 round-trip test, so expect about 1573.

- [ ] **Step 3: Unfiltered oracle suite**

Run: `cargo nextest run -p shinri-solver --features oracle`

Expected: all pass, with a **non-zero discovered count**: about 670 (slice 50 had 669 passed and 3 skipped, and this branch adds 1). A run with 0 discovered is a failure of the command, not a green result.

- [ ] **Step 4: Supply-chain and secrets gates**

Run: `mise run ci`

Expected: green. It covers lint, deny, secrets and test.

- [ ] **Step 5: Push and open the PR**

```bash
git push -u origin slice51-string-literal-escapes
gh pr create --base main --title "slice51: decode SMT-LIB 2.6 \\u escapes in string literals" \
  --body "Implements docs/superpowers/specs/2026-09-30-shinri-slice51-string-literal-escapes-design.md. Measurement (Task 7) lands on this branch before merge."
```

Do not merge yet. Task 7's measurement gates the merge.

---

### Task 7: Measurement and report

**Files:**
- Create: `docs/superpowers/research/2026-09-30-smtlib-2024-slice51-escapes-report.md`
- Modify: `docs/superpowers/specs/2026-09-30-shinri-slice51-string-literal-escapes-design.md` (append `## 12. Measured outcomes`)

**Baseline:** `bench/results/slice50/` (git-ignored). It was built from `4f8f072`, whose solver source is identical to `main` at `4c7ade5`: every later commit is docs only. No separate base run is needed.

- [ ] **Step 1: Confirm the baseline is present and matches**

```bash
head -c 400 bench/results/slice50/results.jsonl   # fixture: timeout_s 20, mem_mb 3072, jobs 6
git diff --stat 4f8f072 4c7ade5 -- crates/        # must print nothing
```

If either check fails, stop. Build `main` in a worktree and run a `slice51-base` with the same flags as Step 2, adding `--solver <worktree>/target/release/shinri`.

- [ ] **Step 2: Run the branch over QF_S and QF_SLIA**

This takes about 2.5 h: 103,335 instances, and slice 50's 121k took about 3 h 13 min. Run it in the background. Pin CPUs exactly as slice 50 did if `nproc` is at least 24:

```bash
BENCH_LOGICS=QF_S,QF_SLIA BENCH_RUN_ID=slice51 taskset -c 12-23 mise run bench-run
BENCH_RUN_ID=slice51 mise run bench-report
md5sum target/release/shinri   # must equal the fixture's solver_md5
```

- [ ] **Step 3: Compute transitions**

Save as a scratch script. It is **not committed**; put it in the session scratchpad:

```python
import collections, json

def load(p):
    rows = {}
    for line in open(p):
        r = json.loads(line)
        if "path" in r and r["logic"] in ("QF_S", "QF_SLIA"):
            rows[r["path"]] = r
    return rows

base = load("bench/results/slice50/results.jsonl")
br = load("bench/results/slice51/results.jsonl")
assert base.keys() == br.keys(), (len(base), len(br))

cells = collections.Counter()
moved = collections.defaultdict(list)
for p, b in base.items():
    n = br[p]
    key = (b["logic"], b["verdict"], n["verdict"])
    cells[key] += 1
    if b["verdict"] != n["verdict"]:
        moved[key].append((p, n["answers"], n["wall_ms"]))

print("changed cells:")
for k, v in sorted(cells.items()):
    if k[1] != k[2]:
        print(" ", k, v)
print("wrong: base", sum(r["verdict"] == "wrong" for r in base.values()),
      "branch", sum(r["verdict"] == "wrong" for r in br.values()))
for k, rows in moved.items():
    if k[2] == "wrong":
        print("ESCALATE", k, rows)
json.dump({"|".join(k): v for k, v in moved.items()}, open("slice51-transitions.json", "w"), indent=1)
```

Run it: `python3 <scratchpad>/transitions.py`.

- [ ] **Step 4: Check the success criteria (spec §7)**

1. `instance10773` → `correct` (`sat`), and `instance09174` → `correct` (`unsat`).
2. None of the 35 `20230329-denghang` rows is `wrong`. The 31 named by spec §1.3 answer `unsat`. List the 4 that do not.
3. The total `wrong` for QF_S plus QF_SLIA is **≤ 2**, and the only remaining rows are `str-pred-small-rw_370.smt2` and `_458.smt2`.
4. **Any `ESCALATE` line blocks the merge.** For each such row:
   - minimise it;
   - confirm with z3 that the answer is really wrong;
   - trace it to a named code path;
   - record it in the report.

   Then **stop and ask the user** whether to fix it in this slice or queue it. Do not merge on your own authority.
5. Put every `correct → unknown`/`timeout` row in a table in the report, with wall time. Triage the largest family in each direction: take one representative, and check whether it contains escapes and what they decode to.

- [ ] **Step 5: Write the report and spec §12**

Follow the structure of `docs/superpowers/research/2026-09-29-smtlib-2024-slice50-uflia-report.md`:

- run commands and fixture table (run-id, `solver_md5`, started, wall-clock);
- a criteria table (criterion, result, evidence);
- transition matrices with changed cells only;
- the `correct → unknown/timeout` triage;
- `## Queued for the next slice` (spec §10 plus anything new);
- the green gate counts from Task 6.

Append `## 12. Measured outcomes` to the spec, summarising the criteria table and linking the report.

- [ ] **Step 6: Commit and push**

```bash
git add docs/superpowers/research/2026-09-30-smtlib-2024-slice51-escapes-report.md \
        docs/superpowers/specs/2026-09-30-shinri-slice51-string-literal-escapes-design.md
git commit -m "docs(bench+spec): slice51 - QF_S/QF_SLIA re-run report and measured outcomes"
git push
```

---

### Task 8: Whole-branch review and merge

- [ ] **Step 1: Whole-branch review**

Use superpowers:requesting-code-review against `main...slice51-string-literal-escapes`. Point the reviewer at the spec's §3 rules, the Global Constraints' untrusted-input bullet, and the Review Focus list. Apply the fixes it confirms, re-run Task 6 Steps 1–3, and push.

- [ ] **Step 2: Merge when CI is green and no escalation is open**

```bash
gh pr checks --watch
gh pr merge --merge --delete-branch
git checkout main && git pull --ff-only
git branch -d slice51-string-literal-escapes 2>/dev/null || true
```
