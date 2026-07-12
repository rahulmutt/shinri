# Slice 18 — str.to_code / str.from_code / str.is_digit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decide `str.to_code`, `str.from_code`, and `str.is_digit` by exact static rewriting (a single pass of full equivalences + a presence fence), completing Spec 4's operator surface.

**Architecture:** Three new `BuiltinOp` variants flow parser → sort-check → a new `crates/shinri-str/src/code_conv.rs` pre-pass wired into the solver's string path right after the int_conv stages. One bottom-up memoized rewrite applies the whole 10-rule catalog (folds, roundtrips, constant-RHS atom equivalences, `is_digit` expansion); a presence fence sends everything else to sound `Unknown`. Fence lands FIRST (Task 1) so the workspace is sound at every commit.

**Tech Stack:** Rust workspace (crates: shinri-core, shinri-parser, shinri-str, shinri-solver). Differential testing against z3 (installed via mise) behind `--features oracle`.

**Spec:** `docs/superpowers/specs/2026-07-12-shinri-slice18-code-conv-design.md` — the rewrite-rule numbers below (R1–R10) refer to its catalog table.

## Global Constraints

- SMT-LIB alphabet is `0x0..=0x2FFFF` inclusive (`MAX_CODE = 0x2FFFF`); Rust chars above it are outside `from_code`'s range.
- Surrogate code points `0xD800..=0xDFFF` are in the SMT-LIB alphabet but unrepresentable in `Box<str>` — those cases NEVER rewrite or fold; they survive to the fence (sound `Unknown`). Never mint a literal via `char::from_u32(..).unwrap()`.
- Digit classification is exactly `'0'..='9'` — never `char::is_numeric()`.
- Every rewrite must be a full logical equivalence: both verdicts, any polarity, any occurrence count. NO demotion flags, NO model repair, NO fresh variables.
- Never perturb existing differential-oracle families or their seeds. New family seed: `0x51_62_0000_0001`.
- `cargo fmt` before EVERY commit (CI hard-fails on `cargo fmt --check`; subagents do not auto-format).
- Commit messages follow repo convention: `feat(str): … (slice 18)`, `test(str): … (slice 18)`, `feat(core): … (slice 18)`, etc.
- Do NOT run `cargo test --workspace` locally (~50 min); test per-crate as instructed. CI runs the full workspace.

---

### Task 1: Op plumbing end-to-end + universal fence

Adds the three operators to core/parser/printer, adds them to every string-op inventory, and wires a fence that sends ANY use of them to sound `Unknown`. After this task the workspace compiles, every existing test passes, and the new ops parse but always fence — sound at this commit and every later one.

**Files:**
- Modify: `crates/shinri-core/src/term.rs` (BuiltinOp enum, after `StrFromInt` ~line 101)
- Modify: `crates/shinri-core/src/context.rs` (mk_app sort-check match ~line 527; test module ~line 1676)
- Modify: `crates/shinri-parser/src/parser.rs` (symbol map ~line 332; dispatch group ~line 900; test module ~line 1995)
- Modify: `crates/shinri-parser/src/print.rs` (`builtin_name` ~line 203)
- Modify: `crates/shinri-solver/src/string_stage.rs` (`is_string_op` ~line 53; module doc line 5)
- Modify: `crates/shinri-str/src/reduce.rs` (`contains_string_op` ~line 151)
- Create: `crates/shinri-str/src/code_conv.rs` (fence only in this task)
- Modify: `crates/shinri-str/src/lib.rs` (add `pub mod code_conv;` next to `pub mod int_conv;`)
- Modify: `crates/shinri-solver/src/lib.rs` (string path, after the `has_unreduced_int_conv` check ~line 455)
- Test: `crates/shinri-core/src/context.rs`, `crates/shinri-parser/src/parser.rs`, `crates/shinri-solver/tests/qfs_differential.rs`

**Interfaces:**
- Consumes: existing `Context::mk_app`, `string_sort()`, `int_sort()`, `bool_sort()`.
- Produces: `BuiltinOp::StrToCode` (String → Int), `BuiltinOp::StrFromCode` (Int → String), `BuiltinOp::StrIsDigit` (String → Bool); `shinri_str::code_conv::has_unreduced_code_conv(ctx: &Context, assertions: &[TermId]) -> bool`. Tasks 2–3 add `rewrite_code_conv` to the same module; Task 4+ rely on the parser symbols `str.to_code`, `str.from_code`, `str.is_digit`.

- [ ] **Step 1: Write the failing core sort-rules test**

In the `#[cfg(test)] mod tests` of `crates/shinri-core/src/context.rs`, directly below `str_to_from_int_sort_rules` (ends ~line 1676):

```rust
    #[test]
    fn str_code_conv_sort_rules() {
        fn nullary(ctx: &mut Context, name: &str, sort: SortId) -> TermId {
            let f = ctx.declare_fun(name, &[], sort);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        }
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let bool_s = ctx.bool_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let n = nullary(&mut ctx, "n", int_s);

        // str.to_code : String -> Int
        let tc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrToCode), &[s])
            .expect("to_code well-sorted");
        assert_eq!(ctx.sort_of(tc), int_s);

        // str.from_code : Int -> String
        let fc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrFromCode), &[n])
            .expect("from_code well-sorted");
        assert_eq!(ctx.sort_of(fc), str_s);

        // str.is_digit : String -> Bool
        let id = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIsDigit), &[s])
            .expect("is_digit well-sorted");
        assert_eq!(ctx.sort_of(id), bool_s);

        // Wrong sorts rejected.
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrToCode), &[n]).is_err());
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrFromCode), &[s])
            .is_err());
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrIsDigit), &[n]).is_err());
        // Wrong arity rejected.
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrToCode), &[s, s])
            .is_err());
    }
```

- [ ] **Step 2: Run it to make sure it fails**

Run: `cargo test -p shinri-core str_code_conv_sort_rules`
Expected: COMPILE ERROR — `StrToCode` not found in `BuiltinOp`.

- [ ] **Step 3: Add the BuiltinOp variants and sort checks**

In `crates/shinri-core/src/term.rs`, immediately after `StrFromInt, // Int -> String` (~line 101):

```rust
    // Slice 18: character-code conversions + digit test (SMT-LIB 2.6).
    StrToCode,   // String -> Int
    StrFromCode, // Int -> String
    StrIsDigit,  // String -> Bool
```

In `crates/shinri-core/src/context.rs`, in the mk_app sort-check match: change the arm heads `StrToInt =>` (~line 527) and `StrFromInt =>` (~line 538) to merged arms, and add `StrIsDigit` after them:

```rust
            StrToInt | StrToCode => {
```
```rust
            StrFromInt | StrFromCode => {
```
```rust
            StrIsDigit => {
                expect_arity(args, 1)?;
                let str_s = self.string_sort();
                if self.sort_of(args[0]) != str_s {
                    return Err(SortError::Mismatch {
                        expected: str_s,
                        found: self.sort_of(args[0]),
                    });
                }
                Ok(self.bool_sort())
            }
```

(The bodies of the two merged arms are unchanged — only the arm heads gain `| StrToCode` / `| StrFromCode`.)

- [ ] **Step 4: Run the core test to verify it passes**

Run: `cargo test -p shinri-core str_code_conv_sort_rules`
Expected: PASS. Then run `cargo test -p shinri-core` — all tests pass.

- [ ] **Step 5: Write the failing parser test**

In the test module of `crates/shinri-parser/src/parser.rs`, directly below `parses_to_int_and_from_int` (which ends shortly after line 1995 — place the new test after its closing brace):

```rust
    /// Parse str.to_code / str.from_code / str.is_digit, verify op + result
    /// sort (slice 18). Mirrors `parses_to_int_and_from_int`.
    #[test]
    fn parses_code_conv_ops() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let src = r#"(declare-fun s () String)
(declare-fun n () Int)
(assert (= (str.to_code s) 97))
(assert (= (str.from_code n) "a"))
(assert (str.is_digit s))"#;
        let (ctx, cmds) = parse_all_ok(src);
        assert_eq!(cmds.len(), 5); // 2 declares + 3 asserts

        // The two Eq-wrapped conversions.
        for (ci, want, want_sort) in [
            (2usize, BuiltinOp::StrToCode, ctx.int_sort()),
            (3usize, BuiltinOp::StrFromCode, ctx.string_sort()),
        ] {
            let assert_term = match &cmds[ci] {
                Command::Assert(t) => *t,
                other => panic!("expected Assert, got {other:?}"),
            };
            let TermNode::App {
                op: Op::Builtin(BuiltinOp::Eq),
                args,
                ..
            } = ctx.term_node(assert_term).clone()
            else {
                panic!("expected Eq at top level");
            };
            let lhs = ctx.children(args)[0];
            let TermNode::App {
                op: Op::Builtin(got),
                ..
            } = ctx.term_node(lhs).clone()
            else {
                panic!("expected builtin app on the LHS");
            };
            assert_eq!(got, want);
            assert_eq!(ctx.sort_of(lhs), want_sort);
        }

        // is_digit: Bool-sorted app at the assert's top level.
        let assert_term = match &cmds[4] {
            Command::Assert(t) => *t,
            other => panic!("expected Assert, got {other:?}"),
        };
        let TermNode::App {
            op: Op::Builtin(BuiltinOp::StrIsDigit),
            ..
        } = ctx.term_node(assert_term).clone()
        else {
            panic!("expected str.is_digit app at top level");
        };
        assert_eq!(ctx.sort_of(assert_term), ctx.bool_sort());
    }
```

(If `parses_to_int_and_from_int` destructures the Eq differently — e.g. names the extracted child differently — copy ITS destructuring style exactly; the assertions to keep are the op and sort equalities.)

- [ ] **Step 6: Run it to make sure it fails**

Run: `cargo test -p shinri-parser parses_code_conv_ops`
Expected: COMPILE ERROR in print.rs (`builtin_name` non-exhaustive) — or, once that is stubbed, FAIL with an unknown-symbol parse error for `str.to_code`.

- [ ] **Step 7: Wire parser and printer**

In `crates/shinri-parser/src/parser.rs`, symbol map, after `"str.from_int" => StrFromInt,` (~line 332):

```rust
            "str.to_code" => StrToCode,
            "str.from_code" => StrFromCode,
            "str.is_digit" => StrIsDigit,
```

In the dispatch group ending `| BuiltinOp::StrFromInt => Self::mk(ctx, Op::Builtin(op), &args, &sp),` (~line 901), extend the group:

```rust
            | BuiltinOp::StrToInt
            | BuiltinOp::StrFromInt
            | BuiltinOp::StrToCode
            | BuiltinOp::StrFromCode
            | BuiltinOp::StrIsDigit => Self::mk(ctx, Op::Builtin(op), &args, &sp),
```

In `crates/shinri-parser/src/print.rs`, `builtin_name`, after `StrFromInt => "str.from_int".to_owned(),` (~line 203):

```rust
        // Slice 18
        StrToCode => "str.to_code".to_owned(),
        StrFromCode => "str.from_code".to_owned(),
        StrIsDigit => "str.is_digit".to_owned(),
```

- [ ] **Step 8: Run the parser tests**

Run: `cargo test -p shinri-parser`
Expected: PASS (including the new test).

- [ ] **Step 9: Compile the whole workspace to flush remaining exhaustive matches**

Run: `cargo check --workspace --all-targets`
Expected: errors ONLY in files that match exhaustively on `BuiltinOp`. For each reported site, add the three new variants to the arm that already contains `StrToInt | StrFromInt` (they are string ops and classify identically). Known sites beyond those already edited: none expected — `reduce.rs` and `string_stage.rs` use non-exhaustive `matches!` (handled next step). If cargo reports a site not listed in this plan, extend its existing `StrToInt`/`StrFromInt` arm and note the file in the commit message.

- [ ] **Step 10: Add the ops to both string-op inventories**

In `crates/shinri-solver/src/string_stage.rs`, `is_string_op` (~line 53), extend the `matches!`:

```rust
                | BuiltinOp::StrToInt
                | BuiltinOp::StrFromInt
                | BuiltinOp::StrToCode
                | BuiltinOp::StrFromCode
                | BuiltinOp::StrIsDigit
```

Also extend the module-doc operator list on line 5 to include `str.to_code`, `str.from_code`, `str.is_digit`.

In `crates/shinri-str/src/reduce.rs`, `contains_string_op` (~line 151), extend the same way:

```rust
                        | BuiltinOp::StrToInt
                        | BuiltinOp::StrFromInt
                        | BuiltinOp::StrToCode
                        | BuiltinOp::StrFromCode
                        | BuiltinOp::StrIsDigit
```

- [ ] **Step 11: Create the fence module and wire it**

Create `crates/shinri-str/src/code_conv.rs`:

```rust
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
                        BuiltinOp::StrToCode
                            | BuiltinOp::StrFromCode
                            | BuiltinOp::StrIsDigit
                    )
                ) || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}
```

In `crates/shinri-str/src/lib.rs`, next to `pub mod int_conv;`, add:

```rust
pub mod code_conv;
```

In `crates/shinri-solver/src/lib.rs`, immediately after the `has_unreduced_int_conv` early-return block (~line 455, i.e. after its closing `}` and before the substr/str.at fence comment):

```rust
            // ── Slice 18: str.to_code / str.from_code / str.is_digit ─────────
            // Universal presence fence (Task 1). Tasks 2–3 insert the exact
            // rewrite pass above this check; anything the pass leaves behind
            // (symbolic linking, inequality / nested-arith shapes, surrogate
            // code points) fences to sound Unknown.
            if shinri_str::code_conv::has_unreduced_code_conv(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

- [ ] **Step 12: Write the failing fence pins**

In `crates/shinri-solver/tests/qfs_differential.rs`, after `targeted_const_int_conv_negated_witness_model_repair` (ends ~line 1790):

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 18: str.to_code / str.from_code / str.is_digit — fence pins.
// These shapes stay OUTSIDE the decided fragment permanently (symbolic
// linking, nested arithmetic, surrogate code points): sound Unknown.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn targeted_code_conv_fences_unknown() {
    // Fully-symbolic linking.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)(declare-fun n () Int)\
             (assert (= (str.to_code s) n))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // Symbolic-RHS from_code.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)(declare-fun n () Int)\
             (assert (= (str.from_code n) s))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // Surrogate code point (0xD800 = 55296): representational fence.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (= (str.to_code s) 55296))(check-sat)"
        ),
        Verdict::Unknown,
    );
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (= (str.from_code 55296) s))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // Nested arithmetic around to_code.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (= (+ (str.to_code s) 1) 98))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // Inequality atom.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (>= (str.to_code s) 48))(check-sat)"
        ),
        Verdict::Unknown,
    );
}
```

- [ ] **Step 13: Run the fence pins**

Run: `cargo test -p shinri-solver --features oracle targeted_code_conv_fences_unknown`
Expected: PASS (the universal fence catches all six).

- [ ] **Step 14: Run both string crates' full suites**

Run: `cargo test -p shinri-str -p shinri-solver --features oracle`
Expected: all PASS (existing families untouched; new pins green).

- [ ] **Step 15: Format and commit**

```bash
cargo fmt
git add -A
git commit -m "feat(str): str.to_code/from_code/is_digit op plumbing + universal fence (slice 18)"
```

---

### Task 2: Folds + roundtrip rewrites (spec rules R1–R3)

Adds `rewrite_code_conv` with the value-level rules: literal folding for all three ops, `to_code(from_code(n))` → range ite, `from_code(to_code(s))` → length ite. Wires the pass into the solver ahead of the Task-1 fence. Constant-RHS atoms still fence (Task 3).

**Files:**
- Modify: `crates/shinri-str/src/code_conv.rs`
- Modify: `crates/shinri-str/src/int_conv.rs` (one visibility change)
- Modify: `crates/shinri-solver/src/lib.rs` (insert one line + finalize comment)
- Test: `crates/shinri-str/src/code_conv.rs` (inline `mod tests`)

**Interfaces:**
- Consumes: `BuiltinOp::StrToCode/StrFromCode/StrIsDigit` (Task 1); `Context::{string_const_value, mk_string_const, mk_numeral, mk_app, mk_eq, mk_const_bool, int_sort}`; `int_conv::int_const_value` (made `pub(crate)` here).
- Produces: `pub fn rewrite_code_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>`; private helpers `eval_to_code(s: &str) -> Option<Integer>`, `eval_from_code(k: &Integer) -> Option<String>`, `char_of_code(k: i128) -> Option<char>`, `is_surrogate(k: i128) -> bool`, and a `try_code_atom(ctx, kids: &[TermId]) -> Option<TermId>` stub returning `None` (Task 3 fills it in).

- [ ] **Step 1: Make `int_const_value` crate-visible**

In `crates/shinri-str/src/int_conv.rs` (~line 244), change:

```rust
fn int_const_value(ctx: &Context, t: TermId) -> Option<Integer> {
```

to:

```rust
pub(crate) fn int_const_value(ctx: &Context, t: TermId) -> Option<Integer> {
```

Run: `cargo test -p shinri-str` — Expected: PASS (pure visibility change).

- [ ] **Step 2: Write the failing eval + fold tests**

Append to `crates/shinri-str/src/code_conv.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*; // brings in Integer, Rational, BuiltinOp, Context, Op, TermId, TermNode

    /// A nullary uninterpreted constant of the given sort (codebase pattern —
    /// there is no `mk_const`).
    fn nullary(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }
    fn to_code(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToCode), &[s]).unwrap()
    }
    fn from_code(ctx: &mut Context, n: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrFromCode), &[n])
            .unwrap()
    }
    fn is_digit(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrIsDigit), &[s])
            .unwrap()
    }
    fn int_lit(ctx: &mut Context, v: i128) -> TermId {
        let int_s = ctx.int_sort();
        ctx.mk_numeral(Rational::from_int(Integer::from(v)), int_s)
    }

    #[test]
    fn eval_to_code_pinned_semantics() {
        assert_eq!(eval_to_code("a"), Some(Integer::from(97i128)));
        assert_eq!(eval_to_code("0"), Some(Integer::from(48i128)));
        assert_eq!(eval_to_code(""), Some(Integer::from(-1i128))); // empty
        assert_eq!(eval_to_code("ab"), Some(Integer::from(-1i128))); // multi-char
        assert_eq!(eval_to_code("\u{2FFFF}"), Some(Integer::from(0x2FFFFi128)));
        // A char ABOVE the SMT-LIB alphabet: not a valid String value — no fold.
        assert_eq!(eval_to_code("\u{30000}"), None);
    }

    #[test]
    fn eval_from_code_pinned_semantics() {
        assert_eq!(eval_from_code(&Integer::from(97i128)), Some("a".to_owned()));
        assert_eq!(eval_from_code(&Integer::from(0i128)), Some("\u{0}".to_owned()));
        assert_eq!(
            eval_from_code(&Integer::from(0x2FFFFi128)),
            Some("\u{2FFFF}".to_owned())
        );
        // Out of the alphabet (negative / too large) -> "".
        assert_eq!(eval_from_code(&Integer::from(-1i128)), Some(String::new()));
        assert_eq!(
            eval_from_code(&Integer::from(0x30000i128)),
            Some(String::new())
        );
        // A value too large for i128 is certainly out of the alphabet -> "".
        let huge = Integer::from_str_radix("1234567890123456789012345678901234567890", 10)
            .unwrap();
        assert_eq!(eval_from_code(&huge), Some(String::new()));
        // Surrogates: unrepresentable -> None (fence).
        assert_eq!(eval_from_code(&Integer::from(0xD800i128)), None);
        assert_eq!(eval_from_code(&Integer::from(0xDFFFi128)), None);
        // Surrogate-block edges DO fold.
        assert_eq!(
            eval_from_code(&Integer::from(0xD7FFi128)),
            Some("\u{D7FF}".to_owned())
        );
        assert_eq!(
            eval_from_code(&Integer::from(0xE000i128)),
            Some("\u{E000}".to_owned())
        );
    }

    #[test]
    fn folds_literal_applications() {
        let mut ctx = Context::new();
        let a_lit = ctx.mk_string_const("a");
        let tc = to_code(&mut ctx, a_lit);
        let k97 = int_lit(&mut ctx, 97);
        let fc = from_code(&mut ctx, k97);
        let idig = is_digit(&mut ctx, a_lit);
        let seven = ctx.mk_string_const("7");
        let idig7 = is_digit(&mut ctx, seven);

        let out = rewrite_code_conv(&mut ctx, &[tc, fc, idig, idig7]);
        // to_code("a") -> 97 (hash-consed: same id as the numeral).
        assert_eq!(out[0], int_lit(&mut ctx, 97));
        // from_code(97) -> "a".
        assert_eq!(out[1], ctx.mk_string_const("a"));
        // is_digit("a") -> false; is_digit("7") -> true.
        assert_eq!(out[2], ctx.mk_const_bool(false));
        assert_eq!(out[3], ctx.mk_const_bool(true));
    }

    #[test]
    fn surrogate_from_code_does_not_fold() {
        let mut ctx = Context::new();
        let k = int_lit(&mut ctx, 0xD800);
        let fc = from_code(&mut ctx, k);
        let out = rewrite_code_conv(&mut ctx, &[fc]);
        assert_eq!(out[0], fc, "surrogate from_code must survive to the fence");
        assert!(has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn roundtrip_to_code_of_from_code() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fc = from_code(&mut ctx, n);
        let tc = to_code(&mut ctx, fc);
        let out = rewrite_code_conv(&mut ctx, &[tc]);
        // ite(and(n >= 0, n <= MAX_CODE), n, -1)
        let zero = int_lit(&mut ctx, 0);
        let max = int_lit(&mut ctx, MAX_CODE);
        let neg1 = int_lit(&mut ctx, -1);
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[n, max]).unwrap();
        let in_range = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[ge, le]).unwrap();
        let want = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[in_range, n, neg1])
            .unwrap();
        assert_eq!(out[0], want);
        assert!(!has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn roundtrip_from_code_of_to_code() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);
        let fc = from_code(&mut ctx, tc);
        let out = rewrite_code_conv(&mut ctx, &[fc]);
        // ite(len(s) = 1, s, "")
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[s]).unwrap();
        let one = int_lit(&mut ctx, 1);
        let cond = ctx.mk_eq(len, one).unwrap();
        let empty = ctx.mk_string_const("");
        let want = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[cond, s, empty])
            .unwrap();
        assert_eq!(out[0], want);
        assert!(!has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn untouched_subtrees_keep_their_termids() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let t = nullary(&mut ctx, "t", str_s);
        // An assertion with NO code-conv content at all.
        let eq = ctx.mk_eq(s, t).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[eq]);
        assert_eq!(out[0], eq, "no-op inputs must keep their TermId");
    }
}
```

- [ ] **Step 3: Run to verify failure**

Run: `cargo test -p shinri-str code_conv`
Expected: COMPILE ERROR — `rewrite_code_conv`, `eval_to_code`, `eval_from_code` not found.

- [ ] **Step 4: Implement the pass (R1–R3)**

In `crates/shinri-str/src/code_conv.rs`, replace the `use` block and add below `MAX_CODE` (keep `has_unreduced_code_conv` as-is):

```rust
use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Integer, Op, Rational, TermId, TermNode};

use crate::int_conv::int_const_value;
```

```rust
fn is_surrogate(k: i128) -> bool {
    (0xD800..=0xDFFF).contains(&k)
}

/// The singleton string's char for in-alphabet, NON-surrogate `k`; None for
/// surrogates (in the SMT-LIB alphabet but unrepresentable in `Box<str>`)
/// and out-of-alphabet values.
fn char_of_code(k: i128) -> Option<char> {
    if !(0..=MAX_CODE).contains(&k) || is_surrogate(k) {
        return None;
    }
    char::from_u32(k as u32)
}

/// Concrete `str.to_code(s)` per SMT-LIB 2.6: the code point for a singleton,
/// `-1` otherwise. None (no fold) for a singleton ABOVE the SMT-LIB alphabet
/// — such a literal is not a valid String value; leave it to the fence.
fn eval_to_code(s: &str) -> Option<Integer> {
    let mut it = s.chars();
    match (it.next(), it.next()) {
        (Some(c), None) => {
            let code = c as u32 as i128;
            if code > MAX_CODE {
                return None;
            }
            Some(Integer::from(code))
        }
        _ => Some(Integer::from(-1i128)),
    }
}

/// Concrete `str.from_code(k)` per SMT-LIB 2.6: the singleton for in-alphabet
/// `k`, `""` for out-of-alphabet `k` (including values beyond i128). None
/// (no fold -> fence) for surrogates: representable in the SMT-LIB alphabet
/// but not in `Box<str>`.
fn eval_from_code(k: &Integer) -> Option<String> {
    match k.to_i128() {
        Some(v) if (0..=MAX_CODE).contains(&v) => char_of_code(v).map(String::from),
        _ => Some(String::new()),
    }
}

/// Single exact rewrite pass (spec R1–R10): bottom-up, memoized; untouched
/// subtrees keep their TermIds. Every rule is a full equivalence — no model
/// repair, no polarity tracking, no occurrence analysis.
pub fn rewrite_code_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect()
}

fn rewrite(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> =
                children.iter().map(|&c| rewrite(ctx, c, memo)).collect();
            let special = match op {
                Op::Builtin(BuiltinOp::StrToCode) => rewrite_to_code(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrFromCode) => rewrite_from_code(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrIsDigit) => rewrite_is_digit(ctx, new_children[0]),
                Op::Builtin(BuiltinOp::Eq) => try_code_atom(ctx, &new_children),
                _ => None,
            };
            if let Some(r) = special {
                r
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(n, o)| n != o);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("code_conv: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// `(str.to_code x)`, child already rewritten. R1 fold + R2 roundtrip.
/// None leaves the app in place (-> fence).
fn rewrite_to_code(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    // R1: fold a literal argument.
    if let Some(s) = ctx.string_const_value(kids[0]).map(str::to_owned) {
        let v = eval_to_code(&s)?;
        let int_s = ctx.int_sort();
        return Some(ctx.mk_numeral(Rational::from_int(v), int_s));
    }
    // R2: to_code(from_code(n)) → ite(0 <= n <= MAX_CODE, n, -1). Exact for
    // ALL n — surrogates included, since no literal is minted.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrFromCode),
        args,
        ..
    } = ctx.term_node(kids[0]).clone()
    {
        let n = ctx.children(args)[0];
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(Rational::from_int(Integer::zero()), int_s);
        let max = ctx.mk_numeral(Rational::from_int(Integer::from(MAX_CODE)), int_s);
        let neg1 = ctx.mk_numeral(Rational::from_int(Integer::from(-1i128)), int_s);
        let ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero])
            .expect("n >= 0");
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[n, max])
            .expect("n <= MAX_CODE");
        let in_range = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[ge, le])
            .expect("range conj");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[in_range, n, neg1])
                .expect("roundtrip ite"),
        );
    }
    None
}

/// `(str.from_code x)`, child already rewritten. R1 fold + R3 roundtrip.
/// None leaves the app in place (-> fence; surrogate literals land here).
fn rewrite_from_code(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    // R1: fold a numeral argument (None on a surrogate -> fence).
    if let Some(k) = int_const_value(ctx, kids[0]) {
        let s = eval_from_code(&k)?;
        return Some(ctx.mk_string_const(&s));
    }
    // R3: from_code(to_code(s)) → ite(len(s) = 1, s, ""). Exact: for a
    // singleton the code roundtrips (surrogates cannot occur in s — Box<str>);
    // otherwise to_code = -1 and from_code(-1) = "".
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrToCode),
        args,
        ..
    } = ctx.term_node(kids[0]).clone()
    {
        let s = ctx.children(args)[0];
        let len = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[s])
            .expect("len");
        let int_s = ctx.int_sort();
        let one = ctx.mk_numeral(Rational::from_int(Integer::one()), int_s);
        let cond = ctx.mk_eq(len, one).expect("len = 1");
        let empty = ctx.mk_string_const("");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[cond, s, empty])
                .expect("roundtrip ite"),
        );
    }
    None
}

/// `(str.is_digit x)`, child already rewritten. R1 literal fold in this task;
/// the R10 expansion for non-literals lands in Task 3 (returns None -> fence
/// until then).
fn rewrite_is_digit(ctx: &mut Context, t: TermId) -> Option<TermId> {
    if let Some(s) = ctx.string_const_value(t).map(str::to_owned) {
        let mut it = s.chars();
        let v = matches!((it.next(), it.next()), (Some('0'..='9'), None));
        return Some(ctx.mk_const_bool(v));
    }
    None
}

/// Constant-RHS equality atoms (R4–R9). Stub in this task — Task 3 fills it.
fn try_code_atom(_ctx: &mut Context, _kids: &[TermId]) -> Option<TermId> {
    None
}
```

- [ ] **Step 5: Run the unit tests**

Run: `cargo test -p shinri-str code_conv`
Expected: PASS (all seven tests).

- [ ] **Step 6: Wire the pass into the solver**

In `crates/shinri-solver/src/lib.rs`, replace the Task-1 block with:

```rust
            // ── Slice 18: str.to_code / str.from_code / str.is_digit ─────────
            // A SINGLE exact rewrite pass — every rule is a full equivalence
            // (no repair, no pins, no occurrence analysis): literal folds,
            // both roundtrip rewrites (elim_term_ite below eliminates the
            // minted ites), constant-RHS atom equivalences at any polarity,
            // and is_digit expansion. Any SURVIVING application (symbolic
            // linking, inequality / nested-arith shapes, surrogate code
            // points — see the module docs) fences to sound Unknown.
            assertions = shinri_str::code_conv::rewrite_code_conv(&mut self.ctx, &assertions);
            if shinri_str::code_conv::has_unreduced_code_conv(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

- [ ] **Step 7: Run the solver suite**

Run: `cargo test -p shinri-str -p shinri-solver --features oracle`
Expected: all PASS — including `targeted_code_conv_fences_unknown` (those shapes still fence: atoms are untouched until Task 3).

- [ ] **Step 8: Format and commit**

```bash
cargo fmt
git add -A
git commit -m "feat(str): code_conv folds + roundtrip rewrites, wire rewrite pass (slice 18)"
```

---

### Task 3: Constant-RHS atom equivalences + is_digit expansion (spec rules R4–R10)

Fills in `try_code_atom` (both orientations) and the `is_digit` expansion, with minted atoms routed back through the atom rules so `is_digit(from_code(n))` reduces fully in one pass.

**Files:**
- Modify: `crates/shinri-str/src/code_conv.rs`
- Test: `crates/shinri-str/src/code_conv.rs` (inline `mod tests`)

**Interfaces:**
- Consumes: Task 2's pass structure, `int_conv::int_const_value`, `Context::{mk_eq, mk_const_bool, mk_string_const, mk_numeral, mk_app}`.
- Produces: complete `rewrite_code_conv` (the public signature is unchanged); private `rw_to_code_const(ctx, s: TermId, k: &Integer) -> Option<TermId>`, `rw_from_code_const(ctx, n: TermId, lit: &str) -> TermId`.

- [ ] **Step 1: Write the failing atom tests**

Append inside `mod tests` of `crates/shinri-str/src/code_conv.rs`:

```rust
    /// Convenience: rewrite a single assertion.
    fn rw1(ctx: &mut Context, t: TermId) -> TermId {
        rewrite_code_conv(ctx, &[t])[0]
    }

    #[test]
    fn to_code_const_rhs_boundary_lattice() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);

        // R4: in-alphabet, non-surrogate k ⇒ s = "<char k>". Check the edges
        // and a digit: 0, '9' (0x39), 0xD7FF, 0xE000, MAX_CODE.
        for k in [0i128, 0x39, 0xD7FF, 0xE000, MAX_CODE] {
            let kt = int_lit(&mut ctx, k);
            let atom = ctx.mk_eq(tc, kt).unwrap();
            let lit = ctx.mk_string_const(&char::from_u32(k as u32).unwrap().to_string());
            let want = ctx.mk_eq(s, lit).unwrap();
            assert_eq!(rw1(&mut ctx, atom), want, "k = {k:#x}");
        }

        // R5: k = -1 ⇒ not (len(s) = 1).
        let neg1 = int_lit(&mut ctx, -1);
        let atom = ctx.mk_eq(tc, neg1).unwrap();
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[s]).unwrap();
        let one = int_lit(&mut ctx, 1);
        let eq1 = ctx.mk_eq(len, one).unwrap();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq1]).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);

        // R6: k <= -2 or k > MAX_CODE ⇒ false.
        for k in [-2i128, 0x30000] {
            let kt = int_lit(&mut ctx, k);
            let atom = ctx.mk_eq(tc, kt).unwrap();
            assert_eq!(rw1(&mut ctx, atom), ctx.mk_const_bool(false), "k = {k}");
        }

        // Surrogate k: representational fence — the atom must SURVIVE.
        for k in [0xD800i128, 0xDFFF] {
            let kt = int_lit(&mut ctx, k);
            let atom = ctx.mk_eq(tc, kt).unwrap();
            let out = rw1(&mut ctx, atom);
            assert_eq!(out, atom, "surrogate k = {k:#x} must fence");
            assert!(has_unreduced_code_conv(&ctx, &[out]));
        }
    }

    #[test]
    fn to_code_const_rhs_matches_either_orientation() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);
        let k = int_lit(&mut ctx, 97);
        // (= 97 (str.to_code s)) — literal on the LEFT.
        let atom = ctx.mk_eq(k, tc).unwrap();
        let a_lit = ctx.mk_string_const("a");
        let want = ctx.mk_eq(s, a_lit).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);
    }

    #[test]
    fn to_code_const_rhs_under_negation_and_or() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);
        let k = int_lit(&mut ctx, 97);
        let atom = ctx.mk_eq(tc, k).unwrap();
        let neg = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[atom]).unwrap();
        let bool_s = ctx.bool_sort();
        let t = nullary(&mut ctx, "p", bool_s);
        let or = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[neg, t]).unwrap();

        let a_lit = ctx.mk_string_const("a");
        let want_eq = ctx.mk_eq(s, a_lit).unwrap();
        let want_neg = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[want_eq]).unwrap();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[want_neg, t]).unwrap();
        assert_eq!(rw1(&mut ctx, or), want);
    }

    #[test]
    fn from_code_const_rhs_shapes() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fc = from_code(&mut ctx, n);

        // R7: singleton literal ⇒ n = code.
        let a_lit = ctx.mk_string_const("a");
        let atom = ctx.mk_eq(fc, a_lit).unwrap();
        let k97 = int_lit(&mut ctx, 97);
        let want = ctx.mk_eq(n, k97).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);

        // R8: empty literal ⇒ n < 0 ∨ n > MAX_CODE.
        let empty = ctx.mk_string_const("");
        let atom = ctx.mk_eq(fc, empty).unwrap();
        let zero = int_lit(&mut ctx, 0);
        let max = int_lit(&mut ctx, MAX_CODE);
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::Lt), &[n, zero]).unwrap();
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[n, max]).unwrap();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[lt, gt]).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);

        // R9: multi-char literal ⇒ false; above-alphabet singleton ⇒ false.
        for lit in ["ab", "\u{30000}"] {
            let l = ctx.mk_string_const(lit);
            let atom = ctx.mk_eq(fc, l).unwrap();
            assert_eq!(rw1(&mut ctx, atom), ctx.mk_const_bool(false), "lit {lit:?}");
        }
    }

    #[test]
    fn is_digit_expands_to_ten_way_disjunction() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let idig = is_digit(&mut ctx, s);
        let out = rw1(&mut ctx, idig);
        let disjuncts: Vec<TermId> = ('0'..='9')
            .map(|d| {
                let lit = ctx.mk_string_const(&d.to_string());
                ctx.mk_eq(s, lit).unwrap()
            })
            .collect();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disjuncts).unwrap();
        assert_eq!(out, want);
        assert!(!has_unreduced_code_conv(&ctx, &[out]));
    }

    #[test]
    fn is_digit_of_from_code_reduces_fully_in_one_pass() {
        // The minted-atom chain: is_digit(from_code(n)) must become a pure
        // LIA disjunction n = 48 ∨ … ∨ n = 57 — R10 routing each minted
        // equality through R7.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fc = from_code(&mut ctx, n);
        let idig = is_digit(&mut ctx, fc);
        let out = rw1(&mut ctx, idig);
        let disjuncts: Vec<TermId> = (48i128..=57)
            .map(|code| {
                let k = int_lit(&mut ctx, code);
                ctx.mk_eq(n, k).unwrap()
            })
            .collect();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disjuncts).unwrap();
        assert_eq!(out, want);
        assert!(!has_unreduced_code_conv(&ctx, &[out]));
    }

    #[test]
    fn symbolic_linking_still_fences() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let n = nullary(&mut ctx, "n", int_s);
        let tc = to_code(&mut ctx, s);
        // (= (str.to_code s) n): symbolic RHS — no rule applies.
        let atom = ctx.mk_eq(tc, n).unwrap();
        let out = rw1(&mut ctx, atom);
        assert_eq!(out, atom);
        assert!(has_unreduced_code_conv(&ctx, &[out]));
    }
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-str code_conv`
Expected: FAIL — the new tests fail (atoms survive; is_digit of a non-literal survives). The Task-2 tests must still pass.

- [ ] **Step 3: Implement R4–R10**

In `crates/shinri-str/src/code_conv.rs`, replace the `rewrite_is_digit` and `try_code_atom` stubs:

```rust
/// `(str.is_digit x)`, child already rewritten. R1 fold for a literal; R10
/// expansion otherwise: `(or (= t "0") … (= t "9"))` — each minted equality
/// is routed back through the atom rules, so `is_digit(from_code(n))`
/// reduces fully in this same pass (no fixpoint loop).
fn rewrite_is_digit(ctx: &mut Context, t: TermId) -> Option<TermId> {
    if let Some(s) = ctx.string_const_value(t).map(str::to_owned) {
        let mut it = s.chars();
        let v = matches!((it.next(), it.next()), (Some('0'..='9'), None));
        return Some(ctx.mk_const_bool(v));
    }
    let disjuncts: Vec<TermId> = ('0'..='9')
        .map(|d| {
            let lit = ctx.mk_string_const(&d.to_string());
            let kids = [t, lit];
            try_code_atom(ctx, &kids)
                .unwrap_or_else(|| ctx.mk_eq(t, lit).expect("is_digit: t = digit"))
        })
        .collect();
    Some(
        ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disjuncts)
            .expect("is_digit expansion"),
    )
}

/// R4–R9: constant-RHS equality atoms, either orientation. Children are
/// already rewritten (so a foldable side has already folded). None → not a
/// code-conv atom, or the surrogate fence.
fn try_code_atom(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    if kids.len() != 2 {
        return None;
    }
    for (a, b) in [(kids[0], kids[1]), (kids[1], kids[0])] {
        match ctx.term_node(a).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrToCode),
                args,
                ..
            } => {
                let s = ctx.children(args)[0];
                if let Some(k) = int_const_value(ctx, b) {
                    return rw_to_code_const(ctx, s, &k);
                }
            }
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrFromCode),
                args,
                ..
            } => {
                let n = ctx.children(args)[0];
                if let Some(lit) = ctx.string_const_value(b).map(str::to_owned) {
                    return Some(rw_from_code_const(ctx, n, &lit));
                }
            }
            _ => {}
        }
    }
    None
}

/// R4/R5/R6: `(= (str.to_code s) k)` — a full partition of k:
/// `-1` ⇒ `not (len(s) = 1)`; in-alphabet non-surrogate ⇒ `s = "<char k>"`;
/// surrogate ⇒ None (representational fence); anything else ⇒ `false`.
fn rw_to_code_const(ctx: &mut Context, s: TermId, k: &Integer) -> Option<TermId> {
    match k.to_i128() {
        Some(-1) => {
            let len = ctx
                .mk_app(Op::Builtin(BuiltinOp::StrLen), &[s])
                .expect("len");
            let int_s = ctx.int_sort();
            let one = ctx.mk_numeral(Rational::from_int(Integer::one()), int_s);
            let eq1 = ctx.mk_eq(len, one).expect("len = 1");
            Some(
                ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq1])
                    .expect("not singleton"),
            )
        }
        Some(v) if (0..=MAX_CODE).contains(&v) => {
            let c = char_of_code(v)?; // surrogate → fence
            let lit = ctx.mk_string_const(&c.to_string());
            Some(ctx.mk_eq(s, lit).expect("s = char"))
        }
        // k <= -2, k > MAX_CODE, or |k| beyond i128: outside to_code's range.
        _ => Some(ctx.mk_const_bool(false)),
    }
}

/// R7/R8/R9: `(= (str.from_code n) "lit")`.
fn rw_from_code_const(ctx: &mut Context, n: TermId, lit: &str) -> TermId {
    if lit.is_empty() {
        // R8: the out-of-alphabet escape — n < 0 ∨ n > MAX_CODE.
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(Rational::from_int(Integer::zero()), int_s);
        let max = ctx.mk_numeral(Rational::from_int(Integer::from(MAX_CODE)), int_s);
        let lt = ctx
            .mk_app(Op::Builtin(BuiltinOp::Lt), &[n, zero])
            .expect("n < 0");
        let gt = ctx
            .mk_app(Op::Builtin(BuiltinOp::Gt), &[n, max])
            .expect("n > MAX_CODE");
        return ctx
            .mk_app(Op::Builtin(BuiltinOp::Or), &[lt, gt])
            .expect("escape disj");
    }
    let mut it = lit.chars();
    match (it.next(), it.next()) {
        // R7: from_code is injective on the alphabet ⇒ n = code(c).
        (Some(c), None) if (c as u32 as i128) <= MAX_CODE => {
            let int_s = ctx.int_sort();
            let code = ctx.mk_numeral(
                Rational::from_int(Integer::from(c as u32 as i128)),
                int_s,
            );
            ctx.mk_eq(n, code).expect("n = code")
        }
        // R9: multi-char, or a singleton above the alphabet — outside
        // from_code's range.
        _ => ctx.mk_const_bool(false),
    }
}
```

Also update `rewrite_is_digit`'s call site in `rewrite` — it now returns `Option<TermId>` from BOTH branches; the `special` match arm stays `Op::Builtin(BuiltinOp::StrIsDigit) => rewrite_is_digit(ctx, new_children[0]),` (unchanged).

- [ ] **Step 4: Run the unit tests**

Run: `cargo test -p shinri-str code_conv`
Expected: PASS (all Task-2 and Task-3 tests).

- [ ] **Step 5: Run both crates' suites**

Run: `cargo test -p shinri-str -p shinri-solver --features oracle`
Expected: all PASS. In particular `targeted_code_conv_fences_unknown` still passes — its six shapes (symbolic linking, symbolic-RHS from_code, surrogates, nested arith, inequality) remain outside R4–R10.

- [ ] **Step 6: Format and commit**

```bash
cargo fmt
git add -A
git commit -m "feat(str): const-RHS code_conv equivalences + is_digit expansion (slice 18)"
```

---

### Task 4: End-to-end verdict pins

Solver-level sat/unsat pins for the decided fragment, including get-value on a decided-Sat instance. No canary flips exist — these ops were unparseable before this slice.

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (below `targeted_code_conv_fences_unknown`)

**Interfaces:**
- Consumes: the file's existing helpers `expect(src, want)`, `shinri_lines_counting_bailouts(src)`, `parse_string_values(resp)`, `Verdict`.
- Produces: pinned e2e behavior later tasks must not regress.

- [ ] **Step 1: Write the pins**

```rust
#[test]
fn targeted_code_conv_decided_sat() {
    // R4: to_code(s) = 97 ⇒ s = "a".
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_code s) 97))(check-sat)",
        Verdict::Sat,
    );
    // R5: the -1 escape (any non-singleton s).
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_code s) (- 1)))(check-sat)",
        Verdict::Sat,
    );
    // R7 / R8.
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.from_code n) \"a\"))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.from_code n) \"\"))(check-sat)",
        Verdict::Sat,
    );
    // R10 expansion, plus a corroborating word equation.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.is_digit s))(assert (= s \"7\"))(check-sat)",
        Verdict::Sat,
    );
    // R2 roundtrip through the ite.
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.to_code (str.from_code n)) 5))(check-sat)",
        Verdict::Sat,
    );
    // Negated atom — the equivalences are polarity-free.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (not (= (str.to_code s) 97)))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_code_conv_decided_unsat() {
    // R6: below -1 / above the alphabet.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_code s) (- 5)))(check-sat)",
        Verdict::Unsat,
    );
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_code s) 196608))(check-sat)",
        Verdict::Unsat,
    );
    // R4 + a conflicting word equation.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_code s) 97))(assert (= s \"b\"))(check-sat)",
        Verdict::Unsat,
    );
    // R9: multi-char is outside from_code's range.
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.from_code n) \"ab\"))(check-sat)",
        Verdict::Unsat,
    );
    // R1 fold: is_digit("x") = false.
    expect(
        "(set-logic QF_S)(assert (str.is_digit \"x\"))(check-sat)",
        Verdict::Unsat,
    );
    // R10 + conflicting equation.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.is_digit s))(assert (= s \"x\"))(check-sat)",
        Verdict::Unsat,
    );
    // R5 + a length pin forcing a singleton.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (= (str.to_code s) (- 1)))(assert (= (str.len s) 1))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_code_conv_get_value() {
    // A decided-Sat instance must produce a concrete, correct model:
    // to_code(s) = 97 forces s = "a" exactly (no model repair involved —
    // the rewrite IS the equivalence).
    let src = "(set-logic QF_S)(declare-fun s () String)\
               (assert (= (str.to_code s) 97))\n(check-sat)\n(get-value (s))\n";
    let (lines, bailouts) = shinri_lines_counting_bailouts(src);
    assert_eq!(bailouts, 0, "no guard bailouts expected");
    assert_eq!(lines.first().map(String::as_str), Some("sat"));
    let resp = lines.get(1).expect("get-value response");
    let model = parse_string_values(resp);
    assert_eq!(
        model,
        vec![("s".to_owned(), "a".to_owned())],
        "to_code(s) = 97 pins s to \"a\""
    );
}
```

- [ ] **Step 2: Run the pins**

Run: `cargo test -p shinri-solver --features oracle targeted_code_conv`
Expected: PASS (all four `targeted_code_conv_*` tests, including Task 1's fence pins).

If `targeted_code_conv_decided_sat`'s is_digit case or the roundtrip case returns Unknown instead: the wordeq/ite path is rejecting the rewritten form — debug with `superpowers:systematic-debugging` before touching any expected verdict. Do NOT weaken a pin to Unknown without evidence the shape is genuinely outside the engine's fragment; that is a spec deviation and must be recorded in the spec truth-up (Task 6).

- [ ] **Step 3: Format and commit**

```bash
cargo fmt
git add -A
git commit -m "test(str): slice-18 e2e verdict pins for the decided code-conv fragment (slice 18)"
```

---

### Task 5: Differential oracle family `qfs_code_conv_matches_z3`

A fresh 200-iteration z3-differential family over the slice-18 fragment: boundary code points, roundtrips, is_digit over literals/vars/from_code, ~25% negation, plus 0–1 general string assertions for cross-theory mixing. Unknown-tolerant, witness-checking, 0 disagreements.

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (Gen impl ~line 655; gen_ wrappers ~line 660; new family test after `qfs_const_int_conv_matches_z3`)

**Interfaces:**
- Consumes: `Gen` (fields `rng: Lcg`, `body: String`), helpers `var()`, `lit()`, `assertion()`, `finish_const_int_conv` (placement reference); file helpers `shinri_lines_counting_bailouts`, `z3_verdict`, `z3_with_model`, `parse_string_values`, `Verdict`, `N_VARS`.
- Produces: `gen_code_conv_body(seed: u64) -> String`; test `qfs_code_conv_matches_z3`.

- [ ] **Step 1: Add the generator**

In the `impl Gen` block, directly after `finish_const_int_conv` (~line 578):

```rust
    /// A code-point RHS for to_code (slice 18): boundary lattice (alphabet
    /// edges, surrogate block, -1 escape, out-of-range) + small in-range
    /// codes. Surrogate RHS exercises the representational fence
    /// (shinri-unknown, tolerated; z3 decides).
    fn code_rhs(&mut self) -> String {
        match self.rng.below(8) {
            0 => "(- 2)".to_owned(),
            1 => "(- 1)".to_owned(),
            2 => "0".to_owned(),
            3 => (0x30 + self.rng.below(10)).to_string(), // '0'..'9'
            4 => (97 + self.rng.below(3)).to_string(),    // 'a'..'c' (matches ALPHABET)
            5 => ["55295", "55296", "57343", "57344"][self.rng.below(4) as usize].to_owned(),
            6 => "196607".to_owned(), // MAX_CODE
            _ => "196608".to_owned(), // MAX_CODE + 1
        }
    }

    /// One slice-18 assertion: constant-RHS to_code/from_code equalities
    /// across the boundary lattice, both roundtrips, and is_digit over
    /// literal / var / from_code arguments. MAY be negated — every rewrite
    /// is a full equivalence, exact at any polarity.
    fn code_conv_assertion(&mut self) {
        let atom = match self.rng.below(6) {
            // to_code(var) = k across the lattice (R4/R5/R6 + fence).
            0 => format!("(= (str.to_code {}) {})", self.var(), self.code_rhs()),
            // to_code(<literal>) = k: the R1 fold path.
            1 => format!("(= (str.to_code {}) {})", self.lit(), self.code_rhs()),
            // from_code(n0) = target: "" / singleton / multi-char (R7/R8/R9).
            2 => {
                let target = match self.rng.below(3) {
                    0 => "\"\"".to_owned(),
                    1 => format!("\"{}\"", ALPHABET[self.rng.below(3) as usize]),
                    _ => self.lit(),
                };
                format!("(= (str.from_code n0) {target})")
            }
            // R2 roundtrip, decided via the range ite.
            3 => format!(
                "(= (str.to_code (str.from_code n0)) {})",
                self.code_rhs()
            ),
            // R3 roundtrip vs a literal: exercises elim_term_ite + wordeq.
            4 => format!(
                "(= (str.from_code (str.to_code {})) {})",
                self.var(),
                self.lit()
            ),
            // is_digit over literal / var / from_code (R1 / R10 / minted-atom
            // chain).
            _ => match self.rng.below(3) {
                0 => format!("(str.is_digit {})", self.lit()),
                1 => format!("(str.is_digit {})", self.var()),
                _ => "(str.is_digit (str.from_code n0))".to_owned(),
            },
        };
        let atom = if self.rng.below(4) == 0 {
            format!("(not {atom})")
        } else {
            atom
        };
        self.body.push_str(&format!("(assert {atom})\n"));
    }

    /// Instance body for the slice-18 family: shared string vars, an Int var
    /// `n0`, 1–2 code-conv assertions, 0–1 general assertions (cross-theory
    /// mixing keeps the SAT witness path referencing string vars).
    fn finish_code_conv(mut self) -> String {
        self.body.push_str("(declare-fun n0 () Int)\n");
        let np = 1 + self.rng.below(2);
        for _ in 0..np {
            self.code_conv_assertion();
        }
        if self.rng.below(2) == 0 {
            self.assertion();
        }
        self.body
    }
```

Next to the other `gen_*_body` wrappers (~line 660):

```rust
fn gen_code_conv_body(seed: u64) -> String {
    Gen::new(seed).finish_code_conv()
}
```

- [ ] **Step 2: Add the family test**

After `qfs_const_int_conv_matches_z3` (its closing brace, before the targeted-pin sections):

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Code-conv differential oracle (slice 18): to_code/from_code/is_digit are
// DECIDED by exact full-equivalence rewriting (both verdicts, any polarity —
// no repair, no demotion). Sat AND Unsat must agree with z3; Sat models are
// z3-verified (a wrong equivalence surfaces as a verdict disagreement or a
// WITNESS FAILURE). Out-of-fragment shapes — symbolic linking, surrogate code
// points — fence (tolerated unknown). Fresh seed — never perturb existing
// families' seeds.
// ─────────────────────────────────────────────────────────────────────────────

const CC_N_ITERS: usize = 200;
const CC_MAX_GUARD_BAILOUTS: usize = CC_N_ITERS / 10;

#[test]
fn qfs_code_conv_matches_z3() {
    let mut rng = Lcg(0x51_62_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness, mut n_guard_bailout) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..CC_N_ITERS {
        let seed = rng.next();
        let body = gen_code_conv_body(seed);

        let (lines, bailouts) = shinri_lines_counting_bailouts(&format!("{body}(check-sat)\n"));
        if bailouts > 0 {
            n_guard_bailout += 1;
            continue;
        }
        let ours = match lines.first().map(String::as_str) {
            Some("sat") => Verdict::Sat,
            Some("unsat") => Verdict::Unsat,
            _ => Verdict::Unknown,
        };
        if ours == Verdict::Unknown {
            n_unknown += 1;
            continue;
        }
        let theirs = z3_verdict(&format!("{body}(check-sat)\n"));
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S CODE_CONV SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{body}(check-sat)"
        );
        match ours {
            Verdict::Sat => {
                n_sat += 1;
                let get = format!(
                    "{body}(check-sat)\n(get-value ({}))\n",
                    (0..N_VARS)
                        .map(|k| format!("s{k}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                );
                let (lines, _b) = shinri_lines_counting_bailouts(&get);
                if let Some(resp) = lines.get(1) {
                    let model = parse_string_values(resp);
                    if !model.is_empty() {
                        let w = z3_with_model(&body, &model);
                        assert_eq!(
                            w,
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

    println!(
        "qfs_code_conv_matches_z3: {CC_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown (tolerated) / {n_z3skip} z3-unknown / \
         {n_guard_bailout} guard-bailout (tolerated); {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "code-conv family produced zero SAT instances");
    assert!(n_unsat > 0, "code-conv family produced zero UNSAT instances");
    assert!(
        n_witness > 0,
        "no witnesses checked — model path not exercised"
    );
    assert!(
        n_guard_bailout <= CC_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailout} exceed bound {CC_MAX_GUARD_BAILOUTS}"
    );
}
```

- [ ] **Step 3: Run the new family**

Run: `cargo test -p shinri-solver --features oracle qfs_code_conv_matches_z3 -- --nocapture`
Expected: PASS with 0 disagreements; the printed tally shows nonzero sat, unsat, and witnesses. Record the tally line — Task 6 pins it into the spec.

If a disagreement or witness failure fires: the failing seed and body are in the panic message — reproduce with z3 directly, then use `superpowers:systematic-debugging`. A disagreement means a rewrite rule is NOT the equivalence the spec claims; fix the rule, never the oracle.

- [ ] **Step 4: Re-run ALL string families unperturbed**

Run: `cargo test -p shinri-solver --features oracle qfs_ -- --nocapture`
Expected: all seven `qfs_*` tests PASS. The five pre-slice-18 families plus `qfs_to_from_int_matches_z3` and `qfs_const_int_conv_matches_z3` must print tallies IDENTICAL to their committed values (this slice does not touch their fragments; `git log -1 --grep="slice 17" --format=%B` and the slice-17 spec header hold the reference tallies).

- [ ] **Step 5: Format and commit**

```bash
cargo fmt
git add -A
git commit -m "test(str): qfs_code_conv_matches_z3 differential oracle family (slice 18)"
```

---

### Task 6: Gates + spec truth-up

**Files:**
- Modify: `docs/superpowers/specs/2026-07-12-shinri-slice18-code-conv-design.md` (Status header)

**Interfaces:**
- Consumes: the Task-5 tally line; any deviations noted during Tasks 1–5.
- Produces: the final slice-18 state — all gates green, spec marked IMPLEMENTED.

- [ ] **Step 1: Run the full gate set**

```bash
cargo test -p shinri-core -p shinri-parser -p shinri-str
cargo test -p shinri-solver --features oracle
cargo fmt --check
cargo clippy --workspace --all-targets
```

Expected: all green, no clippy warnings. (Do NOT run `cargo test --workspace` locally — the ~50-min shinri-fp exhaustive run stays CI-side.)

- [ ] **Step 2: Spec truth-up**

Edit the spec's Status header from:

```markdown
Status: Approved design, pre-implementation.
```

to (using the ACTUAL tally captured in Task 5 — the numbers below are the format, not predictions):

```markdown
Status: IMPLEMENTED (slice 18 landed YYYY-MM-DD).

Oracle (`qfs_code_conv_matches_z3`, fresh seed `0x51_62_0000_0001`, 200
iters): <sat> sat / <unsat> unsat / <unknown> shinri-unknown (tolerated) /
<z3skip> z3-unknown / <bailout> guard-bailout / <witness> witnesses /
**0 disagreements**. All pre-existing string families re-ran unperturbed
with tallies identical to their committed values.

**Deviations from the spec.**
<Either "None." or a numbered list of every place the implementation
deviated — e.g. an extra fence, a pin weakened with evidence, an extra
inventory site found by cargo check in Task 1 Step 9.>
```

- [ ] **Step 3: Commit**

```bash
cargo fmt --check
git add docs/superpowers/specs/2026-07-12-shinri-slice18-code-conv-design.md
git commit -m "docs: slice-18 spec truth-up — IMPLEMENTED + oracle tally"
```

- [ ] **Step 4: Verify the branch is clean and hand off**

Run: `git status && git log --oneline main..HEAD`
Expected: clean tree; the slice-18 commits in order. Use `superpowers:finishing-a-development-branch` to open the PR (repo convention: PR per slice, merged to main — see PRs #9/#10).
