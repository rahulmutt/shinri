# Slice 19 — RegLan Plumbing + Ground str.in_re Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Parse the full SMT-LIB `RegLan` operator surface and decide ground `str.in_re` atoms (literal string × constant regex, any polarity) by Brzozowski derivative + nullability, fencing everything else to sound `Unknown` — the Spec 2 (regex) kickoff.

**Architecture:** A new `SortNode::RegLan` and sixteen `BuiltinOp` variants flow parser → sort-check → a new `crates/shinri-str/src/regex.rs` pre-pass wired into the solver's string path right after code_conv. The module translates constant regex terms into a small private `Rex` AST (smart constructors keep it canonical), evaluates membership by `|s|` derivative steps + nullability under a node-count fuel cap, and folds each ground atom to `true`/`false` — a full equivalence, no polarity tracking, no fresh variables. A presence fence (any surviving `StrInRe` app or RegLan-sorted subterm) plus a RegLan-declaration fence send everything else to sound `Unknown`. Fence lands FIRST (Task 1) so the workspace is sound at every commit.

**Tech Stack:** Rust workspace (crates: shinri-core, shinri-parser, shinri-str, shinri-solver). Differential testing against z3 (installed via mise) behind `--features oracle`.

**Spec:** `docs/superpowers/specs/2026-07-13-shinri-slice19-regex-ground-design.md`.

## Global Constraints

- SMT-LIB alphabet is `0x0..=0x2FFFF` inclusive. `re.allchar` = exactly one char in that range (surrogates included — sound here because ground evaluation never instantiates a witness character; see the spec's Soundness section).
- **Above-alphabet fence:** if the ground string or any `re.range` endpoint contains a char `> 0x2FFFF`, the atom must NOT fold — it survives to the presence fence (sound `Unknown`).
- Every fold is evaluation — a full logical equivalence at any polarity, any occurrence count. NO demotion flags, NO model repair, NO fresh variables.
- Derivative fuel cap: if any intermediate derivative exceeds **10,000 nodes** the fold is abandoned (→ fence). Constant `FUEL_NODE_CAP: usize = 10_000` in `regex.rs`.
- `re.range` is EMPTY if either endpoint is not a single-char literal, or `lo > hi`. `(_ re.loop lo hi)` with `lo > hi` is EMPTY. These are DECIDED (∅), not fenced.
- **ASCII-only differential scripts:** shinri's parser reads string literals as Rust chars but does NOT decode `\u{...}` escapes, while z3 decodes escapes and treats raw UTF-8 bytes byte-wise (slice-18 witness-harness lesson). Any non-ASCII char in a script SHARED with z3 is a semantics mismatch, not a solver bug. The oracle family generates ASCII only; non-ASCII coverage lives in unit tests and shinri-only `Unknown` pins.
- Never perturb existing differential-oracle families or their seeds. New family seed: `0x51_63_0000_0001`.
- `cargo fmt` before EVERY commit (CI hard-fails on `cargo fmt --check`; subagents do not auto-format).
- Run oracle tests FOREGROUND with captured output — never claim a tally you didn't see.
- Commit messages follow repo convention: `feat(str): … (slice 19)`, `test(str): … (slice 19)`, `docs: …`.
- Do NOT run `cargo test --workspace` locally (~50 min); test per-crate as instructed. CI runs the full workspace.
- No new dependencies.

---

### Task 1: Op plumbing end-to-end + universal fence

Adds `SortNode::RegLan` + the sixteen regex `BuiltinOp`s to core/parser/printer, adds them to every string-op inventory, and wires two fences that send ANY use of them to sound `Unknown`: a presence fence (any `StrInRe` app or RegLan-sorted subterm in assertions) and a declaration fence (any declared symbol whose signature mentions RegLan). After this task the workspace compiles, every existing test passes, and the new ops parse but always fence — sound at this commit and every later one.

**Files:**
- Modify: `crates/shinri-core/src/sort.rs` (SortNode enum, after `RoundingMode` ~line 20)
- Modify: `crates/shinri-core/src/term.rs` (BuiltinOp enum, after `StrIsDigit` ~line 105)
- Modify: `crates/shinri-core/src/context.rs` (struct fields ~line 36, `new()` ~lines 60–70, sort accessors ~line 98, mk_app sort-check match after `StrIsDigit` arm ~line 559, new `any_fun_sig_mentions`, test module)
- Modify: `crates/shinri-parser/src/parser.rs` (`parse_sort` ~line 252, `builtin_for` ~line 335, `parse_indexed_op` ~line 459, string-op dispatch arm ~line 907, `resolve_leaf` ~line 512, test module ~line 2069)
- Modify: `crates/shinri-parser/src/print.rs` (`builtin_name`, after `StrIsDigit` ~line 207)
- Modify: `crates/shinri-solver/src/string_stage.rs` (`is_string_op` ~line 57, `uses_strings` ~line 151, module doc line 5)
- Modify: `crates/shinri-str/src/reduce.rs` (`contains_string_op` ~line 155)
- Create: `crates/shinri-str/src/regex.rs` (fence only in this task)
- Modify: `crates/shinri-str/src/lib.rs` (add `pub mod regex;` after `pub mod reduce;`)
- Modify: `crates/shinri-solver/src/lib.rs` (RegLan-decl fence after `word_norm.normalize` ~line 384; presence fence after the code_conv fence ~line 466)
- Test: `crates/shinri-core/src/context.rs`, `crates/shinri-parser/src/parser.rs`, `crates/shinri-str/src/regex.rs`

**Interfaces:**
- Consumes: existing `Context::mk_app`, `string_sort()`, `bool_sort()`, `intern_sort`, `expect_arity`, `expect_all`; parser helpers `expect_numeral_u32`, `Self::mk`, `parse_all_ok` (test).
- Produces (later tasks depend on these EXACT names):
  - `SortNode::RegLan`; `Context::reglan_sort(&self) -> SortId`; `Context::any_fun_sig_mentions(&self, s: SortId) -> bool`.
  - `BuiltinOp::{StrInRe, StrToRe, ReNone, ReAll, ReAllChar, ReConcat, ReUnion, ReInter, ReDiff, ReStar, RePlus, ReOpt, ReComp, ReRange, ReLoop { lo: u32, hi: u32 }, RePow(u32)}`.
  - `shinri_str::regex::has_unreduced_regex(ctx: &Context, assertions: &[TermId]) -> bool`.
  - Parser symbols: `RegLan` (sort), `str.in_re`, `str.to_re`, `re.none`, `re.all`, `re.allchar`, `re.++`, `re.union`, `re.inter`, `re.diff`, `re.*`, `re.+`, `re.opt`, `re.comp`, `re.range`, `(_ re.loop lo hi)`, `(_ re.^ n)`.

- [ ] **Step 1: Create the working branch**

```bash
cd /workspace && git checkout main && git pull && git checkout -b slice19-regex-ground
```

- [ ] **Step 2: Write the failing core sort-rules test**

In the `#[cfg(test)] mod tests` of `crates/shinri-core/src/context.rs`, directly below the `str_code_conv_sort_rules` test:

```rust
    #[test]
    fn regex_sort_rules() {
        fn nullary(ctx: &mut Context, name: &str, sort: SortId) -> TermId {
            let f = ctx.declare_fun(name, &[], sort);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        }
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let re_s = ctx.reglan_sort();
        let bool_s = ctx.bool_sort();
        let int_s = ctx.int_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let n = nullary(&mut ctx, "n", int_s);

        // Nullary RegLan constants.
        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let all = ctx.mk_app(Op::Builtin(BuiltinOp::ReAll), &[]).unwrap();
        let allchar = ctx.mk_app(Op::Builtin(BuiltinOp::ReAllChar), &[]).unwrap();
        for r in [none, all, allchar] {
            assert_eq!(ctx.sort_of(r), re_s);
        }

        // str.to_re : String -> RegLan.
        let tore = ctx.mk_app(Op::Builtin(BuiltinOp::StrToRe), &[s]).unwrap();
        assert_eq!(ctx.sort_of(tore), re_s);

        // str.in_re : String x RegLan -> Bool.
        let inre = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, tore])
            .unwrap();
        assert_eq!(ctx.sort_of(inre), bool_s);

        // n-ary combinators (>= 2 args, all RegLan).
        for op in [
            BuiltinOp::ReConcat,
            BuiltinOp::ReUnion,
            BuiltinOp::ReInter,
            BuiltinOp::ReDiff,
        ] {
            let r = ctx.mk_app(Op::Builtin(op), &[none, all, allchar]).unwrap();
            assert_eq!(ctx.sort_of(r), re_s, "{op:?}");
            assert!(ctx.mk_app(Op::Builtin(op), &[none]).is_err(), "{op:?} arity");
        }

        // Unary combinators, indexed included.
        for op in [
            BuiltinOp::ReStar,
            BuiltinOp::RePlus,
            BuiltinOp::ReOpt,
            BuiltinOp::ReComp,
            BuiltinOp::ReLoop { lo: 2, hi: 5 },
            BuiltinOp::RePow(3),
        ] {
            let r = ctx.mk_app(Op::Builtin(op), &[allchar]).unwrap();
            assert_eq!(ctx.sort_of(r), re_s, "{op:?}");
        }

        // re.range : String x String -> RegLan.
        let a = ctx.mk_string_const("a");
        let z = ctx.mk_string_const("z");
        let range = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, z])
            .unwrap();
        assert_eq!(ctx.sort_of(range), re_s);

        // Wrong sorts rejected.
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrToRe), &[n]).is_err());
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, s]).is_err());
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[none, none]).is_err());
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::ReStar), &[s]).is_err());
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, n]).is_err());
        assert!(ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[s]).is_err());

        // any_fun_sig_mentions: false before, true after a RegLan declaration.
        assert!(!ctx.any_fun_sig_mentions(re_s));
        ctx.declare_fun("r", &[], re_s);
        assert!(ctx.any_fun_sig_mentions(re_s));
    }
```

- [ ] **Step 3: Run it to verify it fails**

Run: `cargo test -p shinri-core regex_sort_rules 2>&1 | tail -20`
Expected: COMPILE ERROR — `no variant named ReNone`, `no method named reglan_sort`.

- [ ] **Step 4: Implement the core plumbing**

`crates/shinri-core/src/sort.rs` — add after `RoundingMode,`:

```rust
    /// The RegLan sort (SMT-LIB regular expressions over String, slice 19).
    RegLan,
```

`crates/shinri-core/src/term.rs` — add after `StrIsDigit,  // String -> Bool`:

```rust
    // Slice 19: regular expressions (SMT-LIB 2.6 RegLan).
    StrInRe,   // String × RegLan -> Bool
    StrToRe,   // String -> RegLan
    ReNone,    // RegLan (nullary): ∅
    ReAll,     // RegLan (nullary): Σ*
    ReAllChar, // RegLan (nullary): Σ (one char)
    ReConcat,  // RegLan^n -> RegLan, n >= 2
    ReUnion,   // RegLan^n -> RegLan, n >= 2
    ReInter,   // RegLan^n -> RegLan, n >= 2
    ReDiff,    // RegLan^n -> RegLan, n >= 2 (left-assoc difference)
    ReStar,    // RegLan -> RegLan
    RePlus,    // RegLan -> RegLan
    ReOpt,     // RegLan -> RegLan
    ReComp,    // RegLan -> RegLan
    ReRange,   // String × String -> RegLan
    // Indexed (parameters carried in the op, like BvExtract/BvRepeat).
    ReLoop { lo: u32, hi: u32 }, // (_ re.loop lo hi)
    RePow(u32),                  // (_ re.^ n) ≡ (_ re.loop n n)
```

`crates/shinri-core/src/context.rs`:

1. Add field after `string_sort: SortId,`: `reglan_sort: SortId,`
2. In `Context::new()`, add placeholder `reglan_sort: SortId::from_index(0),` next to the other placeholders, and after `ctx.string_sort = ...` add:
   `ctx.reglan_sort = ctx.intern_sort(SortNode::RegLan);`
3. Add accessor after `string_sort()`:

```rust
    #[inline]
    pub fn reglan_sort(&self) -> SortId {
        self.reglan_sort
    }
```

4. Add next to `declare_fun` (~line 165):

```rust
    /// True iff any declared function signature mentions the given sort
    /// (result or any parameter). Slice 19: fences queries that declare a
    /// RegLan-sorted symbol — RegLan must never reach model construction.
    pub fn any_fun_sig_mentions(&self, s: SortId) -> bool {
        self.fun_sigs
            .values()
            .any(|(params, ret)| *ret == s || params.contains(&s))
    }
```

5. In the mk_app sort-check `match`, add after the `StrIsDigit` arm (~line 559):

```rust
            // ── Regular expressions (slice 19) ───────────────────────────────
            StrInRe => {
                expect_arity(args, 2)?;
                let (str_s, re_s) = (self.string_sort(), self.reglan_sort());
                if self.sort_of(args[0]) != str_s {
                    return Err(SortError::Mismatch {
                        expected: str_s,
                        found: self.sort_of(args[0]),
                    });
                }
                if self.sort_of(args[1]) != re_s {
                    return Err(SortError::Mismatch {
                        expected: re_s,
                        found: self.sort_of(args[1]),
                    });
                }
                Ok(self.bool_sort())
            }
            StrToRe => {
                expect_arity(args, 1)?;
                let str_s = self.string_sort();
                if self.sort_of(args[0]) != str_s {
                    return Err(SortError::Mismatch {
                        expected: str_s,
                        found: self.sort_of(args[0]),
                    });
                }
                Ok(self.reglan_sort())
            }
            ReNone | ReAll | ReAllChar => {
                expect_arity(args, 0)?;
                Ok(self.reglan_sort())
            }
            ReConcat | ReUnion | ReInter | ReDiff => {
                if args.len() < 2 {
                    return Err(SortError::Arity {
                        expected: 2,
                        found: args.len(),
                    });
                }
                let re_s = self.reglan_sort();
                expect_all(self, args, re_s)?;
                Ok(re_s)
            }
            ReStar | RePlus | ReOpt | ReComp | ReLoop { .. } | RePow(_) => {
                expect_arity(args, 1)?;
                let re_s = self.reglan_sort();
                if self.sort_of(args[0]) != re_s {
                    return Err(SortError::Mismatch {
                        expected: re_s,
                        found: self.sort_of(args[0]),
                    });
                }
                Ok(re_s)
            }
            ReRange => {
                expect_arity(args, 2)?;
                let str_s = self.string_sort();
                expect_all(self, args, str_s)?;
                Ok(self.reglan_sort())
            }
```

- [ ] **Step 5: Run the core test to verify it passes**

Run: `cargo test -p shinri-core regex_sort_rules 2>&1 | tail -5`
Expected: `test ... regex_sort_rules ... ok`

- [ ] **Step 6: Write the failing parser test**

In the `#[cfg(test)] mod tests` of `crates/shinri-parser/src/parser.rs`, directly below `parses_code_conv_ops` (~line 2069):

```rust
    /// Parse the full RegLan operator surface (slice 19): sort name, nullary
    /// constants, n-ary/unary combinators, indexed re.loop / re.^, str.in_re,
    /// str.to_re, re.range. Mirrors `parses_code_conv_ops`.
    #[test]
    fn parses_regex_ops() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let src = r#"(declare-fun s () String)
(declare-fun r () RegLan)
(assert (str.in_re s (re.++ (str.to_re "ab") (re.union re.none re.all re.allchar))))
(assert (str.in_re s (re.inter (re.* (re.range "a" "z")) (re.comp (re.diff re.all (re.opt (re.+ (str.to_re "x"))))))))
(assert (str.in_re s ((_ re.loop 2 5) (str.to_re "a"))))
(assert (str.in_re s ((_ re.^ 3) re.allchar)))
(assert (= r re.none))"#;
        let (ctx, cmds) = parse_all_ok(src);
        assert_eq!(cmds.len(), 7); // 2 declares + 5 asserts

        // Every str.in_re assert is a Bool-sorted StrInRe app whose second
        // child is RegLan-sorted.
        for ci in 2..=5 {
            let assert_term = match &cmds[ci] {
                Command::Assert(t) => *t,
                other => panic!("expected Assert, got {other:?}"),
            };
            let TermNode::App {
                op: Op::Builtin(BuiltinOp::StrInRe),
                args,
                ..
            } = ctx.term_node(assert_term).clone()
            else {
                panic!("expected str.in_re app at top level of assert {ci}");
            };
            assert_eq!(ctx.sort_of(assert_term), ctx.bool_sort());
            let kids = ctx.children(args).to_vec();
            assert_eq!(ctx.sort_of(kids[0]), ctx.string_sort());
            assert_eq!(ctx.sort_of(kids[1]), ctx.reglan_sort());
        }

        // The indexed ops carried their parameters.
        let loop_assert = match &cmds[4] {
            Command::Assert(t) => *t,
            other => panic!("expected Assert, got {other:?}"),
        };
        let TermNode::App { args, .. } = ctx.term_node(loop_assert).clone() else {
            panic!("expected app");
        };
        let re_arg = ctx.children(args).to_vec()[1];
        match ctx.term_node(re_arg).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::ReLoop { lo: 2, hi: 5 }),
                ..
            } => {}
            other => panic!("expected (_ re.loop 2 5), got {other:?}"),
        }

        // RegLan equality parses (fenced later by the solver, not the parser).
        let eq_assert = match &cmds[6] {
            Command::Assert(t) => *t,
            other => panic!("expected Assert, got {other:?}"),
        };
        assert_eq!(ctx.sort_of(eq_assert), ctx.bool_sort());
    }

    /// Ill-sorted regex operands are diagnostics, not crashes.
    #[test]
    fn regex_wrong_sort_rejected() {
        // str.to_re arg must be String.
        let src = r#"(declare-fun n () Int)
(assert (str.in_re "a" (str.to_re n)))"#;
        let mut ctx = shinri_core::Context::new();
        let mut p = Parser::new(src);
        let mut saw_err = false;
        while let Some(r) = p.next_command(&mut ctx) {
            if r.is_err() {
                saw_err = true;
            }
        }
        assert!(saw_err, "ill-sorted str.to_re must be a diagnostic");
    }

    /// Loop/power indices above u32::MAX are diagnostics (an error is not a
    /// verdict — same discipline as the BvIndex/FpIndex range errors).
    #[test]
    fn regex_loop_index_overflow_rejected() {
        let src = r#"(assert (str.in_re "a" ((_ re.loop 0 5000000000) re.allchar)))"#;
        let mut ctx = shinri_core::Context::new();
        let mut p = Parser::new(src);
        let mut saw_err = false;
        while let Some(r) = p.next_command(&mut ctx) {
            if r.is_err() {
                saw_err = true;
            }
        }
        assert!(saw_err, "loop index beyond u32 must be a diagnostic");
    }
```

- [ ] **Step 7: Run it to verify it fails**

Run: `cargo test -p shinri-parser parses_regex_ops 2>&1 | tail -10`
Expected: FAIL — `unknown sort RegLan` (or `undeclared symbol re.none`).

- [ ] **Step 8: Implement the parser + printer plumbing**

`crates/shinri-parser/src/parser.rs`:

1. `parse_sort` (~line 252), after `"String" => Ok(ctx.string_sort()),`:

```rust
            "RegLan" => Ok(ctx.reglan_sort()),
```

2. `builtin_for` (~line 335), after `"str.is_digit" => StrIsDigit,`:

```rust
            // Regular expressions (slice 19). The nullary constants re.none /
            // re.all / re.allchar are bare symbols, resolved in resolve_leaf.
            "str.in_re" => StrInRe,
            "str.to_re" => StrToRe,
            "re.++" => ReConcat,
            "re.union" => ReUnion,
            "re.inter" => ReInter,
            "re.diff" => ReDiff,
            "re.*" => ReStar,
            "re.+" => RePlus,
            "re.opt" => ReOpt,
            "re.comp" => ReComp,
            "re.range" => ReRange,
```

3. `resolve_leaf` (~line 512), inside the leading `match name { ... }` after the `"RTZ" | "roundTowardZero"` arm:

```rust
            "re.none" => {
                return Self::mk(ctx, Op::Builtin(shinri_core::BuiltinOp::ReNone), &[], &sp);
            }
            "re.all" => {
                return Self::mk(ctx, Op::Builtin(shinri_core::BuiltinOp::ReAll), &[], &sp);
            }
            "re.allchar" => {
                return Self::mk(ctx, Op::Builtin(shinri_core::BuiltinOp::ReAllChar), &[], &sp);
            }
```

4. `parse_indexed_op` (~line 459), after the `"repeat"` arm (note: `expect_numeral_u32` already rejects numerals above `u32::MAX` with a diagnostic — the spec's loop-index overflow rule comes for free):

```rust
            // Regular-expression indexed operators (slice 19)
            "re.loop" => {
                let lo = self.expect_numeral_u32()?;
                let hi = self.expect_numeral_u32()?;
                ReLoop { lo, hi }
            }
            "re.^" => RePow(self.expect_numeral_u32()?),
```

Also extend its doc comment: `re.loop lo hi`, `re.^ n`.

5. String-op dispatch arm (~line 907) — extend the existing group so the new ops delegate to `mk_app`:

```rust
            | BuiltinOp::StrIsDigit
            | BuiltinOp::StrInRe
            | BuiltinOp::StrToRe
            | BuiltinOp::ReNone
            | BuiltinOp::ReAll
            | BuiltinOp::ReAllChar
            | BuiltinOp::ReConcat
            | BuiltinOp::ReUnion
            | BuiltinOp::ReInter
            | BuiltinOp::ReDiff
            | BuiltinOp::ReStar
            | BuiltinOp::RePlus
            | BuiltinOp::ReOpt
            | BuiltinOp::ReComp
            | BuiltinOp::ReRange
            | BuiltinOp::ReLoop { .. }
            | BuiltinOp::RePow(_) => Self::mk(ctx, Op::Builtin(op), &args, &sp),
```

`crates/shinri-parser/src/print.rs` — in `builtin_name`, after `StrIsDigit => ...`:

```rust
        // Slice 19
        StrInRe => "str.in_re".to_owned(),
        StrToRe => "str.to_re".to_owned(),
        ReNone => "re.none".to_owned(),
        ReAll => "re.all".to_owned(),
        ReAllChar => "re.allchar".to_owned(),
        ReConcat => "re.++".to_owned(),
        ReUnion => "re.union".to_owned(),
        ReInter => "re.inter".to_owned(),
        ReDiff => "re.diff".to_owned(),
        ReStar => "re.*".to_owned(),
        RePlus => "re.+".to_owned(),
        ReOpt => "re.opt".to_owned(),
        ReComp => "re.comp".to_owned(),
        ReRange => "re.range".to_owned(),
        ReLoop { lo, hi } => format!("(_ re.loop {lo} {hi})"),
        RePow(n) => format!("(_ re.^ {n})"),
```

If `builtin_name` (or any other `BuiltinOp` match) is exhaustive and the compiler reports further missing arms anywhere in the workspace, add the analogous arms there — grep-check with `cargo build --workspace 2>&1 | grep "non-exhaustive\|not covered"` and fix each site.

- [ ] **Step 9: Run parser tests to verify they pass**

Run: `cargo test -p shinri-parser parses_regex_ops regex_wrong_sort_rejected regex_loop_index_overflow_rejected 2>&1 | tail -5`
Expected: all three PASS (`expect_numeral_u32` already rejects `5000000000`).

- [ ] **Step 10: Create `crates/shinri-str/src/regex.rs` with the fence + failing fence tests**

Full file content for this task (Tasks 2–3 extend it):

```rust
//! Slice 19 pre-pass: `str.in_re` over SMT-LIB regular expressions —
//! ground evaluation by Brzozowski derivatives + presence fence.
//!
//! Decided fragment: `str.in_re(s, R)` where `s` is a string literal and `R`
//! is a CONSTANT regex (every `str.to_re` argument and every `re.range`
//! endpoint is a literal). The atom folds to true/false — evaluation, a full
//! logical equivalence at any polarity, any occurrence count. No model
//! repair, no fresh variables.
//!
//! Stages (run by the solver's string-path seam, right after code_conv):
//! 1. [`rewrite_ground_in_re`] — bottom-up memoized pass folding every ground
//!    membership atom. (Lands in Task 3.)
//! 2. [`has_unreduced_regex`] — presence fence: any surviving `str.in_re`
//!    application or RegLan-sorted subterm ⇒ the solver returns a sound
//!    `Unknown`. The solver additionally fences any query that DECLARES a
//!    RegLan-sorted symbol (`Context::any_fun_sig_mentions`).
//!
//! Above-alphabet fence: Rust literals can hold chars in
//! `0x30000..=0x10FFFF`, outside the SMT-LIB alphabet — if the ground string
//! or a range endpoint contains one, the fold is skipped (→ fence) rather
//! than guessing semantics.

use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// Largest SMT-LIB string character (inclusive): U+2FFFF.
const MAX_CODE: u32 = 0x2FFFF;

/// Presence fence: true iff any `str.in_re` application or RegLan-sorted
/// subterm survives in `assertions`. Any hit ⇒ sound `Unknown`.
pub fn has_unreduced_regex(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        if ctx.sort_of(t) == ctx.reglan_sort() {
            return true;
        }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(BuiltinOp::StrInRe))
                    || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A nullary uninterpreted constant of the given sort (codebase pattern).
    fn nullary(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn in_re(ctx: &mut Context, s: TermId, r: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, r]).unwrap()
    }

    fn to_re(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToRe), &[s]).unwrap()
    }

    #[test]
    fn fence_detects_in_re_and_reglan_subterms() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let re_s = ctx.reglan_sort();
        let s = nullary(&mut ctx, "s", str_s);

        // str.in_re app → fenced.
        let lit = ctx.mk_string_const("a");
        let r = to_re(&mut ctx, lit);
        let atom = in_re(&mut ctx, s, r);
        assert!(has_unreduced_regex(&ctx, &[atom]));

        // Bare RegLan equality → fenced (RegLan-sorted subterms).
        let rv = nullary(&mut ctx, "r", re_s);
        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let eq = ctx.mk_eq(rv, none).unwrap();
        assert!(has_unreduced_regex(&ctx, &[eq]));

        // Plain string assertion → NOT fenced.
        let b = ctx.mk_string_const("b");
        let seq = ctx.mk_eq(s, b).unwrap();
        assert!(!has_unreduced_regex(&ctx, &[seq]));
    }
}
```

Add to `crates/shinri-str/src/lib.rs` after `pub mod reduce;`:

```rust
pub mod regex;
```

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -5`
Expected: `fence_detects_in_re_and_reglan_subterms ... ok`

- [ ] **Step 11: Wire the fences into the solver + inventories**

`crates/shinri-solver/src/string_stage.rs`:

1. Extend `is_string_op` with all sixteen ops:

```rust
                | BuiltinOp::StrInRe
                | BuiltinOp::StrToRe
                | BuiltinOp::ReNone
                | BuiltinOp::ReAll
                | BuiltinOp::ReAllChar
                | BuiltinOp::ReConcat
                | BuiltinOp::ReUnion
                | BuiltinOp::ReInter
                | BuiltinOp::ReDiff
                | BuiltinOp::ReStar
                | BuiltinOp::RePlus
                | BuiltinOp::ReOpt
                | BuiltinOp::ReComp
                | BuiltinOp::ReRange
                | BuiltinOp::ReLoop { .. }
                | BuiltinOp::RePow(_)
```

2. In `uses_strings`, extend the closure so pure-RegLan assertions (e.g. `(= r re.none)`) route to the string path and hit the regex fence:

```rust
        walk_any(ctx, a, &mut seen, &mut |ctx, t| {
            is_string_sort(ctx, t)
                || ctx.sort_of(t) == ctx.reglan_sort()
                || match ctx.term_node(t) {
                    TermNode::App { op, .. } => is_string_op(op),
                    _ => false,
                }
        })
```

3. Update the module doc (line 5): append `str.in_re` + `re.*` to the operator list and note RegLan-sorted subterms also count as string usage.

`crates/shinri-str/src/reduce.rs` — extend `contains_string_op`'s `matches!` with the same sixteen variants (after `BuiltinOp::StrIsDigit`):

```rust
                        | BuiltinOp::StrInRe
                        | BuiltinOp::StrToRe
                        | BuiltinOp::ReNone
                        | BuiltinOp::ReAll
                        | BuiltinOp::ReAllChar
                        | BuiltinOp::ReConcat
                        | BuiltinOp::ReUnion
                        | BuiltinOp::ReInter
                        | BuiltinOp::ReDiff
                        | BuiltinOp::ReStar
                        | BuiltinOp::RePlus
                        | BuiltinOp::ReOpt
                        | BuiltinOp::ReComp
                        | BuiltinOp::ReRange
                        | BuiltinOp::ReLoop { .. }
                        | BuiltinOp::RePow(_)
```

`crates/shinri-solver/src/lib.rs`:

1. Immediately after `assertions = self.word_norm.normalize(&mut self.ctx, &assertions);` (~line 384):

```rust
        // ── Slice 19: RegLan declaration fence ─────────────────────────────
        // A query that DECLARES a RegLan-sorted symbol is out of the decided
        // fragment even if the symbol never appears in an assertion — RegLan
        // must never reach model construction. Sound Unknown.
        if self
            .ctx
            .any_fun_sig_mentions(self.ctx.reglan_sort())
        {
            return SolveOutcome::Unknown;
        }
```

2. After the code_conv fence block (`has_unreduced_code_conv` early-return, ~line 466), add:

```rust
            // ── Slice 19: RegLan + ground str.in_re ──────────────────────────
            // (Task 3 inserts the rewrite pass here.) Any str.in_re
            // application or RegLan-sorted subterm — symbolic string or regex
            // side, RegLan equality, above-alphabet literals, fuel exhaustion
            // — fences to sound Unknown.
            if shinri_str::regex::has_unreduced_regex(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

- [ ] **Step 12: Run the affected crates' test suites (non-oracle)**

Run: `cargo test -p shinri-core -p shinri-parser -p shinri-str -p shinri-solver 2>&1 | tail -15`
Expected: ALL PASS (the new ops parse but always fence; no existing behavior changes).

- [ ] **Step 13: Format, lint, commit**

```bash
cd /workspace && cargo fmt && cargo clippy --workspace --all-targets 2>&1 | tail -5
git add -A
git commit -m "feat(str): RegLan sort + re.* op plumbing + universal fence (slice 19)"
```

Expected: clippy clean (no new warnings), commit succeeds.

---

### Task 2: Rex AST — smart constructors, nullability, derivatives, ground evaluation

The pure derivative engine inside `regex.rs`: a private `Rex` AST with canonicalizing smart constructors, `nullable`, `deriv`, and fuel-capped `eval_membership`. No `Context` involvement — everything unit-testable in isolation.

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (add below `MAX_CODE`, above `has_unreduced_regex`)
- Test: same file, `#[cfg(test)] mod tests`

**Interfaces:**
- Consumes: nothing outside the module.
- Produces (Task 3 consumes these EXACT private names): `enum Rex { Empty, Eps, Range(u32, u32), Concat(Vec<Rex>), Union(Vec<Rex>), Inter(Vec<Rex>), Star(Box<Rex>), Comp(Box<Rex>), Loop(Box<Rex>, u32, u32) }` (derives `Clone, PartialEq, Eq, Debug`); constructors `concat(Vec<Rex>) -> Rex`, `union(Vec<Rex>) -> Rex`, `inter(Vec<Rex>) -> Rex`, `star(Rex) -> Rex`, `comp(Rex) -> Rex`, `loop_(Rex, u32, u32) -> Rex`; `nullable(&Rex) -> bool`; `deriv(u32, &Rex) -> Rex`; `node_count(&Rex) -> usize`; `eval_membership(&str, &Rex) -> Option<bool>` (None = fuel exhausted → caller fences); `const FUEL_NODE_CAP: usize = 10_000`; internal `eval_membership_capped(&str, &Rex, usize) -> Option<bool>`.

- [ ] **Step 1: Write the failing derivative-engine tests**

Append to the `tests` module in `crates/shinri-str/src/regex.rs`:

```rust
    // ── Task 2: pure derivative engine ───────────────────────────────────

    /// (regex, string, expected membership) — one row per operator + the
    /// boundary lattice from the spec.
    fn chr(c: char) -> Rex {
        Rex::Range(c as u32, c as u32)
    }

    fn lit(s: &str) -> Rex {
        concat(s.chars().map(chr).collect())
    }

    #[test]
    fn smart_constructors_canonicalize() {
        // Concat: Empty absorbs, Eps drops, nested flattens, 0/1-ary collapse.
        assert_eq!(concat(vec![lit("a"), Rex::Empty]), Rex::Empty);
        assert_eq!(concat(vec![Rex::Eps, Rex::Eps]), Rex::Eps);
        assert_eq!(concat(vec![Rex::Eps, chr('a')]), chr('a'));
        assert_eq!(
            concat(vec![concat(vec![chr('a'), chr('b')]), chr('c')]),
            Rex::Concat(vec![chr('a'), chr('b'), chr('c')])
        );
        // Union: Empty drops, duplicates dedupe, nested flattens.
        assert_eq!(union(vec![Rex::Empty, chr('a')]), chr('a'));
        assert_eq!(union(vec![chr('a'), chr('a')]), chr('a'));
        assert_eq!(union(vec![Rex::Empty, Rex::Empty]), Rex::Empty);
        // Inter: Empty annihilates, duplicates dedupe.
        assert_eq!(inter(vec![chr('a'), Rex::Empty]), Rex::Empty);
        assert_eq!(inter(vec![chr('a'), chr('a')]), chr('a'));
        // Star: ∅* = ε* = ε; (r*)* = r*.
        assert_eq!(star(Rex::Empty), Rex::Eps);
        assert_eq!(star(Rex::Eps), Rex::Eps);
        assert_eq!(star(star(chr('a'))), star(chr('a')));
        // Comp: comp(comp(r)) = r.
        assert_eq!(comp(comp(chr('a'))), chr('a'));
        // Loop: lo > hi = ∅; r{0,0} = ε; ∅{0,k} = ε; ∅{1,k} = ∅.
        assert_eq!(loop_(chr('a'), 3, 2), Rex::Empty);
        assert_eq!(loop_(chr('a'), 0, 0), Rex::Eps);
        assert_eq!(loop_(Rex::Empty, 0, 4), Rex::Eps);
        assert_eq!(loop_(Rex::Empty, 1, 4), Rex::Empty);
    }

    #[test]
    fn nullability_per_operator() {
        assert!(!nullable(&Rex::Empty));
        assert!(nullable(&Rex::Eps));
        assert!(!nullable(&chr('a')));
        assert!(nullable(&star(chr('a'))));
        assert!(!nullable(&concat(vec![chr('a'), star(chr('b'))])));
        assert!(nullable(&union(vec![chr('a'), Rex::Eps])));
        assert!(!nullable(&inter(vec![Rex::Eps, chr('a')])));
        assert!(nullable(&comp(chr('a')))); // "" ∉ {a} ⇒ "" ∈ comp
        assert!(!nullable(&comp(star(chr('a')))));
        assert!(nullable(&loop_(chr('a'), 0, 3)));
        assert!(!nullable(&loop_(chr('a'), 1, 3)));
        assert!(nullable(&loop_(union(vec![chr('a'), Rex::Eps]), 2, 3)));
    }

    #[test]
    fn ground_membership_per_operator() {
        let sigma = Rex::Range(0, MAX_CODE);
        let all = star(sigma.clone());
        let cases: Vec<(Rex, &str, bool)> = vec![
            // to_re / literal word.
            (lit("ab"), "ab", true),
            (lit("ab"), "ba", false),
            (lit(""), "", true),
            (lit(""), "a", false),
            // none / all / allchar.
            (Rex::Empty, "", false),
            (all.clone(), "", true),
            (all.clone(), "xyz", true),
            (sigma.clone(), "a", true),
            (sigma.clone(), "", false),
            (sigma.clone(), "ab", false),
            // concat / union / inter.
            (concat(vec![lit("a"), lit("b")]), "ab", true),
            (union(vec![lit("a"), lit("b")]), "b", true),
            (union(vec![lit("a"), lit("b")]), "c", false),
            (inter(vec![lit("ab"), all.clone()]), "ab", true),
            (inter(vec![lit("a"), lit("b")]), "a", false),
            // star / plus (plus = r·r*) / opt (union with ε).
            (star(lit("ab")), "", true),
            (star(lit("ab")), "ababab", true),
            (star(lit("ab")), "aba", false),
            (concat(vec![lit("a"), star(lit("a"))]), "", false),
            (concat(vec![lit("a"), star(lit("a"))]), "aaa", true),
            (union(vec![lit("a"), Rex::Eps]), "", true),
            // comp / diff (diff = inter with comp).
            (comp(lit("a")), "b", true),
            (comp(lit("a")), "a", false),
            (comp(lit("a")), "", true),
            (comp(Rex::Empty), "", true),
            (comp(Rex::Empty), "anything", true),
            (comp(all.clone()), "x", false),
            (comp(all.clone()), "", false),
            (inter(vec![sigma.clone(), comp(lit("a"))]), "b", true),
            (inter(vec![sigma.clone(), comp(lit("a"))]), "a", false),
            // range (incl. equal endpoints).
            (Rex::Range('a' as u32, 'c' as u32), "b", true),
            (Rex::Range('a' as u32, 'c' as u32), "d", false),
            (Rex::Range('a' as u32, 'a' as u32), "a", true),
            (Rex::Range('a' as u32, 'a' as u32), "b", false),
            // loop / pow.
            (loop_(lit("a"), 1, 2), "a", true),
            (loop_(lit("a"), 1, 2), "aa", true),
            (loop_(lit("a"), 1, 2), "aaa", false),
            (loop_(lit("a"), 1, 2), "", false),
            (loop_(lit("a"), 0, 2), "", true),
            (loop_(lit("ab"), 2, 2), "abab", true),
            (loop_(lit("ab"), 2, 2), "ab", false),
            // huge lazy bounds cost nothing.
            (loop_(lit("a"), 0, u32::MAX), "aaaa", true),
        ];
        for (rex, s, want) in cases {
            assert_eq!(
                eval_membership(s, &rex),
                Some(want),
                "membership of {s:?} in {rex:?}"
            );
        }
    }

    #[test]
    fn fuel_cap_aborts_instead_of_diverging() {
        // A tiny cap forces an abort on a regex whose derivative grows.
        let r = inter(vec![
            star(union(vec![lit("aa"), lit("aaa")])),
            star(union(vec![lit("aa"), lit("aaa")])),
            comp(star(lit("aaaa"))),
        ]);
        assert_eq!(eval_membership_capped("aaaaaaaa", &r, 1), None);
        // The real cap decides this easily (and correctly).
        assert!(eval_membership("aaaaaaaa", &r).is_some());
    }
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -10`
Expected: COMPILE ERROR — `cannot find type Rex`, `cannot find function concat`.

- [ ] **Step 3: Implement the derivative engine**

Insert into `crates/shinri-str/src/regex.rs` below `const MAX_CODE`:

```rust
/// Derivative-size fuel: if any intermediate derivative exceeds this many
/// AST nodes the fold is abandoned (→ presence fence → sound Unknown).
const FUEL_NODE_CAP: usize = 10_000;

/// Canonical regex AST for ground evaluation. Invariants (enforced by the
/// smart constructors, NEVER by direct construction of compound nodes):
/// - `Range(lo, hi)`: `lo <= hi <= MAX_CODE` where produced from user syntax;
///   derivatives never mint new ranges.
/// - `Concat`/`Union`/`Inter`: >= 2 elements, flattened, no identity/absorber
///   elements; `Union`/`Inter` deduped.
/// - `Star`: argument is not `Empty`/`Eps`/`Star`.
/// - `Comp`: argument is not `Comp`.
/// - `Loop(r, lo, hi)`: `lo <= hi`, `hi >= 1`, `r` not `Empty`/`Eps`.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Rex {
    /// ∅ — matches nothing.
    Empty,
    /// {ε} — matches exactly the empty string.
    Eps,
    /// One char with code point in `[lo, hi]` (inclusive).
    Range(u32, u32),
    Concat(Vec<Rex>),
    Union(Vec<Rex>),
    Inter(Vec<Rex>),
    Star(Box<Rex>),
    /// Complement w.r.t. Σ* (Σ = the SMT-LIB alphabet).
    Comp(Box<Rex>),
    /// `r{lo..=hi}` — between lo and hi copies of r.
    Loop(Box<Rex>, u32, u32),
}

fn concat(parts: Vec<Rex>) -> Rex {
    let mut out = Vec::new();
    for p in parts {
        match p {
            Rex::Empty => return Rex::Empty,
            Rex::Eps => {}
            Rex::Concat(inner) => out.extend(inner),
            other => out.push(other),
        }
    }
    match out.len() {
        0 => Rex::Eps,
        1 => out.pop().expect("len 1"),
        _ => Rex::Concat(out),
    }
}

fn union(parts: Vec<Rex>) -> Rex {
    let mut out: Vec<Rex> = Vec::new();
    for p in parts {
        match p {
            Rex::Empty => {}
            Rex::Union(inner) => {
                for q in inner {
                    if !out.contains(&q) {
                        out.push(q);
                    }
                }
            }
            other => {
                if !out.contains(&other) {
                    out.push(other);
                }
            }
        }
    }
    match out.len() {
        0 => Rex::Empty,
        1 => out.pop().expect("len 1"),
        _ => Rex::Union(out),
    }
}

fn inter(parts: Vec<Rex>) -> Rex {
    let mut out: Vec<Rex> = Vec::new();
    for p in parts {
        match p {
            Rex::Empty => return Rex::Empty,
            Rex::Inter(inner) => {
                for q in inner {
                    if !out.contains(&q) {
                        out.push(q);
                    }
                }
            }
            other => {
                if !out.contains(&other) {
                    out.push(other);
                }
            }
        }
    }
    match out.len() {
        // Unreachable from user syntax (arity >= 2, Empty short-circuits),
        // but be safe: the intersection of no languages is Σ*.
        0 => star(Rex::Range(0, MAX_CODE)),
        1 => out.pop().expect("len 1"),
        _ => Rex::Inter(out),
    }
}

fn star(r: Rex) -> Rex {
    match r {
        Rex::Empty | Rex::Eps => Rex::Eps,
        s @ Rex::Star(_) => s,
        other => Rex::Star(Box::new(other)),
    }
}

fn comp(r: Rex) -> Rex {
    match r {
        Rex::Comp(inner) => *inner,
        other => Rex::Comp(Box::new(other)),
    }
}

fn loop_(r: Rex, lo: u32, hi: u32) -> Rex {
    if lo > hi {
        return Rex::Empty;
    }
    if hi == 0 {
        return Rex::Eps; // r{0,0} = ε
    }
    match r {
        // ∅ has no words: ∅{lo..hi} = ε iff lo == 0, else ∅.
        Rex::Empty => {
            if lo == 0 {
                Rex::Eps
            } else {
                Rex::Empty
            }
        }
        Rex::Eps => Rex::Eps,
        other => Rex::Loop(Box::new(other), lo, hi),
    }
}

/// ε ∈ L(r)?
fn nullable(r: &Rex) -> bool {
    match r {
        Rex::Empty | Rex::Range(..) => false,
        Rex::Eps | Rex::Star(_) => true,
        Rex::Concat(ps) | Rex::Inter(ps) => ps.iter().all(nullable),
        Rex::Union(ps) => ps.iter().any(nullable),
        Rex::Comp(inner) => !nullable(inner),
        Rex::Loop(inner, lo, _) => *lo == 0 || nullable(inner),
    }
}

/// The Brzozowski derivative of `r` w.r.t. the char with code point `c`:
/// `L(deriv(c, r)) = { w | c·w ∈ L(r) }`. Total — every operator (comp,
/// inter, loop included) has a native rule; no automaton is built.
fn deriv(c: u32, r: &Rex) -> Rex {
    match r {
        Rex::Empty | Rex::Eps => Rex::Empty,
        Rex::Range(lo, hi) => {
            if *lo <= c && c <= *hi {
                Rex::Eps
            } else {
                Rex::Empty
            }
        }
        Rex::Concat(ps) => {
            // d(r1·rest) = d(r1)·rest  ∪  (if ε ∈ r1) d(rest)
            let head = &ps[0];
            let rest = concat(ps[1..].to_vec());
            let first = concat(vec![deriv(c, head), rest.clone()]);
            if nullable(head) {
                union(vec![first, deriv(c, &rest)])
            } else {
                first
            }
        }
        Rex::Union(ps) => union(ps.iter().map(|p| deriv(c, p)).collect()),
        Rex::Inter(ps) => inter(ps.iter().map(|p| deriv(c, p)).collect()),
        Rex::Star(inner) => concat(vec![deriv(c, inner), Rex::Star(inner.clone())]),
        Rex::Comp(inner) => comp(deriv(c, inner)),
        Rex::Loop(inner, lo, hi) => {
            // Consume one char from `inner`; the remainder completes `inner`,
            // then loops lo-1..hi-1 more times (hi >= 1 by the invariant).
            // Bounds decrement lazily — huge hi costs nothing.
            let tail = loop_((**inner).clone(), lo.saturating_sub(1), hi - 1);
            concat(vec![deriv(c, inner), tail])
        }
    }
}

fn node_count(r: &Rex) -> usize {
    1 + match r {
        Rex::Empty | Rex::Eps | Rex::Range(..) => 0,
        Rex::Concat(ps) | Rex::Union(ps) | Rex::Inter(ps) => ps.iter().map(node_count).sum(),
        Rex::Star(i) | Rex::Comp(i) | Rex::Loop(i, ..) => node_count(i),
    }
}

/// Ground membership by |s| derivative steps + nullability. `None` iff an
/// intermediate derivative exceeds `cap` nodes (→ caller fences).
fn eval_membership_capped(s: &str, r: &Rex, cap: usize) -> Option<bool> {
    let mut cur = r.clone();
    for c in s.chars() {
        cur = deriv(c as u32, &cur);
        if node_count(&cur) > cap {
            return None;
        }
    }
    Some(nullable(&cur))
}

fn eval_membership(s: &str, r: &Rex) -> Option<bool> {
    eval_membership_capped(s, r, FUEL_NODE_CAP)
}
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -10`
Expected: all four regex tests PASS (plus the Task-1 fence test).

- [ ] **Step 5: Format, lint, commit**

```bash
cd /workspace && cargo fmt && cargo clippy -p shinri-str --all-targets 2>&1 | tail -5
git add -A
git commit -m "feat(str): Rex derivatives core — smart constructors, nullability, ground eval (slice 19)"
```

Note: `eval_membership`/`extract_const_regex` are consumed in Task 3 — if clippy flags them `dead_code` at this commit, add `#[allow(dead_code)] // used by Task 3's rewrite pass` and REMOVE the allow in Task 3.

---

### Task 3: Constant-regex extraction + ground rewrite pass, wired into the solver

Translate constant `RegLan` terms into `Rex`, fold every ground `str.in_re` atom to `true`/`false` in one bottom-up memoized pass (mirroring `code_conv::rewrite_code_conv`), and wire the pass into the solver's string path directly before the Task-1 presence fence.

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (add between `eval_membership` and `has_unreduced_regex`)
- Modify: `crates/shinri-solver/src/lib.rs` (the slice-19 block from Task 1 Step 11)
- Test: `crates/shinri-str/src/regex.rs` tests module

**Interfaces:**
- Consumes: Task 2's `Rex`, constructors, `eval_membership`; Task 1's `has_unreduced_regex`; `Context::{string_const_value, mk_const_bool, mk_app, term_node, children, reglan_sort}`; `rustc_hash::FxHashMap` (already a shinri-str dependency; add `use rustc_hash::FxHashMap;` to the imports).
- Produces: `shinri_str::regex::rewrite_ground_in_re(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>` (public; the solver calls it); internal `extract_const_regex(ctx: &Context, t: TermId) -> Option<Rex>`, `lit_to_rex(&str) -> Option<Rex>`, `try_fold_in_re(ctx: &mut Context, kids: &[TermId]) -> Option<TermId>`.

- [ ] **Step 1: Write the failing extraction + rewrite tests**

Append to the `tests` module in `crates/shinri-str/src/regex.rs`:

```rust
    // ── Task 3: extraction + ground rewrite pass ─────────────────────────

    /// Build a str.in_re atom over a LITERAL string from an SMT-LIB-shaped
    /// term tree, run the rewrite pass, and expect a Bool fold.
    fn fold_of(ctx: &mut Context, atom: TermId) -> Option<bool> {
        let out = rewrite_ground_in_re(ctx, &[atom]);
        match ctx.term_node(out[0]) {
            TermNode::Const {
                val: shinri_core::ConstVal::Bool(b),
                ..
            } => Some(*b),
            _ => None,
        }
    }

    fn slit(ctx: &mut Context, s: &str) -> TermId {
        ctx.mk_string_const(s)
    }

    #[test]
    fn ground_atoms_fold_per_operator() {
        let mut ctx = Context::new();

        // ("ab", to_re("ab")) → true; ("ab", re.none) → false.
        let ab = slit(&mut ctx, "ab");
        let re_ab = to_re(&mut ctx, ab);
        let atom = in_re(&mut ctx, ab, re_ab);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let none = ctx.mk_app(Op::Builtin(BuiltinOp::ReNone), &[]).unwrap();
        let atom = in_re(&mut ctx, ab, none);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        // re.all / re.allchar.
        let all = ctx.mk_app(Op::Builtin(BuiltinOp::ReAll), &[]).unwrap();
        let atom = in_re(&mut ctx, ab, all);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let allchar = ctx.mk_app(Op::Builtin(BuiltinOp::ReAllChar), &[]).unwrap();
        let atom = in_re(&mut ctx, ab, allchar);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        let a = slit(&mut ctx, "a");
        let atom = in_re(&mut ctx, a, allchar);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        // (_ re.loop 1 2) over to_re("a"): "aa" in, "aaa" out.
        let re_a = to_re(&mut ctx, a);
        let loop12 = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: 1, hi: 2 }), &[re_a])
            .unwrap();
        let aa = slit(&mut ctx, "aa");
        let aaa = slit(&mut ctx, "aaa");
        let atom = in_re(&mut ctx, aa, loop12);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, aaa, loop12);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        // (_ re.^ 2): exactly two copies.
        let pow2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::RePow(2)), &[re_a])
            .unwrap();
        let atom = in_re(&mut ctx, aa, pow2);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, pow2);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        // re.comp / re.diff / re.inter / re.union / re.opt / re.+ / re.range.
        let b = slit(&mut ctx, "b");
        let re_b = to_re(&mut ctx, b);
        let comp_a = ctx.mk_app(Op::Builtin(BuiltinOp::ReComp), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, b, comp_a);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, comp_a);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        let diff = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReDiff), &[allchar, re_a])
            .unwrap();
        let atom = in_re(&mut ctx, b, diff);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, diff);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        let un = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReUnion), &[re_a, re_b])
            .unwrap();
        let atom = in_re(&mut ctx, b, un);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let it = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReInter), &[un, re_b])
            .unwrap();
        let atom = in_re(&mut ctx, b, it);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let atom = in_re(&mut ctx, a, it);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));

        let empty = slit(&mut ctx, "");
        let opt = ctx.mk_app(Op::Builtin(BuiltinOp::ReOpt), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, empty, opt);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let plus = ctx.mk_app(Op::Builtin(BuiltinOp::RePlus), &[re_a]).unwrap();
        let atom = in_re(&mut ctx, empty, plus);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        let atom = in_re(&mut ctx, aaa, plus);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));

        let z = slit(&mut ctx, "c");
        let range = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, z])
            .unwrap();
        let atom = in_re(&mut ctx, b, range);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
        let d = slit(&mut ctx, "d");
        let atom = in_re(&mut ctx, d, range);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
    }

    #[test]
    fn degenerate_range_and_loop_are_decided_empty() {
        let mut ctx = Context::new();
        let a = slit(&mut ctx, "a");
        // Multi-char endpoint ⇒ empty range (decided, NOT fenced).
        let ab = slit(&mut ctx, "ab");
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, ab])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // Reversed endpoints ⇒ empty.
        let c = slit(&mut ctx, "c");
        let r = ctx.mk_app(Op::Builtin(BuiltinOp::ReRange), &[c, a]).unwrap();
        let atom = in_re(&mut ctx, a, r);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // Loop lo > hi ⇒ empty.
        let re_a = to_re(&mut ctx, a);
        let l = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReLoop { lo: 3, hi: 1 }), &[re_a])
            .unwrap();
        let atom = in_re(&mut ctx, a, l);
        assert_eq!(fold_of(&mut ctx, atom), Some(false));
        // Empty-string membership of ε-shapes: "" in to_re("") → true.
        let empty = slit(&mut ctx, "");
        let re_empty = to_re(&mut ctx, empty);
        let atom = in_re(&mut ctx, empty, re_empty);
        assert_eq!(fold_of(&mut ctx, atom), Some(true));
    }

    #[test]
    fn atoms_fold_under_boolean_structure() {
        // Equivalences need no polarity tracking: fold under not/or/ite too.
        let mut ctx = Context::new();
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, a, re_a); // true
        let not = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[atom]).unwrap();
        let out = rewrite_ground_in_re(&mut ctx, &[not]);
        // not(true) — the pass does NOT simplify Boolean structure, only the
        // atom folds; check the child became const true.
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("expected Not app");
        };
        let child = ctx.children(args).to_vec()[0];
        assert!(matches!(
            ctx.term_node(child),
            TermNode::Const {
                val: shinri_core::ConstVal::Bool(true),
                ..
            }
        ));
        assert!(!has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn non_ground_shapes_survive_to_fence() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let a = slit(&mut ctx, "a");

        // Symbolic string side.
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, s, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert_eq!(out[0], atom, "must not rewrite");
        assert!(has_unreduced_regex(&ctx, &out));

        // Symbolic to_re argument.
        let re_s = to_re(&mut ctx, s);
        let atom = in_re(&mut ctx, a, re_s);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));

        // Symbolic range endpoint.
        let r = ctx.mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, s]).unwrap();
        let atom = in_re(&mut ctx, a, r);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));

        // RegLan variable in the regex.
        let reglan = ctx.reglan_sort();
        let rv = nullary(&mut ctx, "r", reglan);
        let atom = in_re(&mut ctx, a, rv);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn above_alphabet_literals_fence() {
        let mut ctx = Context::new();
        // Ground string containing U+30000 (> MAX_CODE) — no fold.
        let hi = slit(&mut ctx, "\u{30000}");
        let all = ctx.mk_app(Op::Builtin(BuiltinOp::ReAll), &[]).unwrap();
        let atom = in_re(&mut ctx, hi, all);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // Range endpoint above the alphabet — no fold.
        let a = slit(&mut ctx, "a");
        let r = ctx
            .mk_app(Op::Builtin(BuiltinOp::ReRange), &[a, hi])
            .unwrap();
        let atom = in_re(&mut ctx, a, r);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
        // to_re over an above-alphabet literal — no fold.
        let re_hi = to_re(&mut ctx, hi);
        let atom = in_re(&mut ctx, a, re_hi);
        let out = rewrite_ground_in_re(&mut ctx, &[atom]);
        assert!(has_unreduced_regex(&ctx, &out));
    }

    #[test]
    fn untouched_subtrees_keep_their_termids() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let lit = slit(&mut ctx, "xy");
        let eq = ctx.mk_eq(s, lit).unwrap();
        let a = slit(&mut ctx, "a");
        let re_a = to_re(&mut ctx, a);
        let atom = in_re(&mut ctx, a, re_a);
        let out = rewrite_ground_in_re(&mut ctx, &[eq, atom]);
        assert_eq!(out[0], eq, "unrelated assertion must keep its TermId");
        assert!(matches!(
            ctx.term_node(out[1]),
            TermNode::Const {
                val: shinri_core::ConstVal::Bool(true),
                ..
            }
        ));
    }
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -10`
Expected: COMPILE ERROR — `cannot find function rewrite_ground_in_re`.

- [ ] **Step 3: Implement extraction + the rewrite pass**

Add `use rustc_hash::FxHashMap;` to the imports of `regex.rs`, then insert between `eval_membership` and `has_unreduced_regex`:

```rust
/// A literal word as a Rex (concat of single-char ranges). None if any char
/// is above the SMT-LIB alphabet (→ fence).
fn lit_to_rex(s: &str) -> Option<Rex> {
    let mut parts = Vec::new();
    for c in s.chars() {
        let code = c as u32;
        if code > MAX_CODE {
            return None;
        }
        parts.push(Rex::Range(code, code));
    }
    Some(concat(parts)) // "" → Eps
}

/// Structural translation of a CONSTANT RegLan term. None on any
/// non-constant leaf (symbolic `str.to_re` argument, non-literal `re.range`
/// endpoint, RegLan variable / non-builtin application) or an
/// above-alphabet literal char (→ fence).
fn extract_const_regex(ctx: &Context, t: TermId) -> Option<Rex> {
    let TermNode::App { op, args, .. } = ctx.term_node(t) else {
        return None;
    };
    let Op::Builtin(b) = *op else {
        return None; // RegLan variable or uninterpreted application.
    };
    let kids: Vec<TermId> = ctx.children(*args).to_vec();
    let sub = |ctx: &Context, ids: &[TermId]| -> Option<Vec<Rex>> {
        ids.iter().map(|&k| extract_const_regex(ctx, k)).collect()
    };
    match b {
        BuiltinOp::StrToRe => lit_to_rex(ctx.string_const_value(kids[0])?),
        BuiltinOp::ReNone => Some(Rex::Empty),
        BuiltinOp::ReAll => Some(star(Rex::Range(0, MAX_CODE))),
        BuiltinOp::ReAllChar => Some(Rex::Range(0, MAX_CODE)),
        BuiltinOp::ReConcat => Some(concat(sub(ctx, &kids)?)),
        BuiltinOp::ReUnion => Some(union(sub(ctx, &kids)?)),
        BuiltinOp::ReInter => Some(inter(sub(ctx, &kids)?)),
        BuiltinOp::ReDiff => {
            // Left-associative difference: a \ b \ c = inter(a, comp(b), comp(c)).
            let mut rs = sub(ctx, &kids)?.into_iter();
            let first = rs.next().expect("arity >= 2");
            let mut parts = vec![first];
            for r in rs {
                parts.push(comp(r));
            }
            Some(inter(parts))
        }
        BuiltinOp::ReStar => Some(star(extract_const_regex(ctx, kids[0])?)),
        BuiltinOp::RePlus => {
            // r+ = r · r*.
            let r = extract_const_regex(ctx, kids[0])?;
            Some(concat(vec![r.clone(), star(r)]))
        }
        BuiltinOp::ReOpt => {
            let r = extract_const_regex(ctx, kids[0])?;
            Some(union(vec![r, Rex::Eps]))
        }
        BuiltinOp::ReComp => Some(comp(extract_const_regex(ctx, kids[0])?)),
        BuiltinOp::ReRange => {
            let a = ctx.string_const_value(kids[0])?;
            let b = ctx.string_const_value(kids[1])?;
            let single = |s: &str| -> Option<Option<u32>> {
                // Outer None = fence (above alphabet); inner None = not a
                // single char (⇒ empty range per SMT-LIB).
                let mut it = s.chars();
                match (it.next(), it.next()) {
                    (Some(c), None) => {
                        let code = c as u32;
                        if code > MAX_CODE {
                            None // fence
                        } else {
                            Some(Some(code))
                        }
                    }
                    _ => Some(None), // empty range, decided
                }
            };
            match (single(a)?, single(b)?) {
                (Some(lo), Some(hi)) if lo <= hi => Some(Rex::Range(lo, hi)),
                _ => Some(Rex::Empty), // multi-char endpoint or lo > hi
            }
        }
        BuiltinOp::ReLoop { lo, hi } => {
            Some(loop_(extract_const_regex(ctx, kids[0])?, lo, hi))
        }
        BuiltinOp::RePow(n) => Some(loop_(extract_const_regex(ctx, kids[0])?, n, n)),
        _ => None, // not a RegLan constructor
    }
}

/// `(str.in_re s R)`, children already rewritten. Some(bool-const) iff the
/// string side is a literal with no above-alphabet chars, `R` extracts as a
/// constant regex, and evaluation stays within fuel.
fn try_fold_in_re(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let s = ctx.string_const_value(kids[0])?.to_owned();
    if s.chars().any(|c| c as u32 > MAX_CODE) {
        return None; // above-alphabet fence
    }
    let rex = extract_const_regex(ctx, kids[1])?;
    let v = eval_membership(&s, &rex)?; // None = fuel → fence
    Some(ctx.mk_const_bool(v))
}

/// Bottom-up memoized pass folding every GROUND `str.in_re` atom to a Bool
/// constant. Untouched subtrees keep their TermIds. Mirrors
/// `code_conv::rewrite_code_conv`.
pub fn rewrite_ground_in_re(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
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
                Op::Builtin(BuiltinOp::StrInRe) => try_fold_in_re(ctx, &new_children),
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
                        .expect("regex: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}
```

If Task 2 added any `#[allow(dead_code)]`, remove them now.

- [ ] **Step 4: Run the module tests to verify they pass**

Run: `cargo test -p shinri-str regex:: 2>&1 | tail -10`
Expected: all regex tests PASS.

- [ ] **Step 5: Wire the rewrite into the solver**

In `crates/shinri-solver/src/lib.rs`, replace the Task-1 slice-19 comment + fence block with:

```rust
            // ── Slice 19: RegLan + ground str.in_re ──────────────────────────
            // One bottom-up pass folds every GROUND membership atom (literal
            // string × constant regex) to true/false by Brzozowski derivative
            // + nullability — full equivalences, any polarity, no fresh
            // variables. Any surviving str.in_re application or RegLan-sorted
            // subterm (symbolic string or regex side, RegLan equality,
            // above-alphabet literals, fuel exhaustion) fences to sound
            // Unknown. Queries DECLARING RegLan symbols were already fenced
            // right after word_norm.
            assertions = shinri_str::regex::rewrite_ground_in_re(&mut self.ctx, &assertions);
            if shinri_str::regex::has_unreduced_regex(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

- [ ] **Step 6: Run the affected crates' suites (non-oracle)**

Run: `cargo test -p shinri-str -p shinri-solver 2>&1 | tail -10`
Expected: ALL PASS.

- [ ] **Step 7: Format, lint, commit**

```bash
cd /workspace && cargo fmt && cargo clippy --workspace --all-targets 2>&1 | tail -5
git add -A
git commit -m "feat(str): constant-regex extraction + ground str.in_re fold, wire rewrite pass (slice 19)"
```

---

### Task 4: E2e verdict pins for the decided fragment

Sat/unsat pins through the full solver (z3 cross-checked via the existing `expect` helper) plus `Unknown` pins for every fence class. Lives in `qfs_differential.rs` beside the slice-18 pins (oracle-gated; z3 comes from mise). No canary flips are expected — these operators were previously unparseable.

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (append after `targeted_code_conv_decided_unsat`)

**Interfaces:**
- Consumes: existing test helpers `expect(src, Verdict)`, `shinri_verdict(src)`, `Verdict`.
- Produces: three test fns — `targeted_regex_ground_decided_sat`, `targeted_regex_ground_decided_unsat`, `targeted_regex_fences_unknown`.

- [ ] **Step 1: Write the pins**

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 19: ground str.in_re pins. The decided fragment is literal-string ×
// constant-regex membership at ANY polarity (evaluation — a full
// equivalence). Everything else fences: symbolic string side, symbolic regex
// leaves, RegLan equality, RegLan declarations, above-alphabet literals.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn targeted_regex_ground_decided_sat() {
    // Trivial ground fold + a live string var alongside.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re \"ab\" (str.to_re \"ab\")))(assert (= s \"x\"))(check-sat)",
        Verdict::Sat,
    );
    // Concat + star + range.
    expect(
        "(set-logic QF_S)\
         (assert (str.in_re \"abc\" (re.++ (str.to_re \"a\") (re.* (re.range \"b\" \"c\")))))(check-sat)",
        Verdict::Sat,
    );
    // Negated membership — polarity-free.
    expect(
        "(set-logic QF_S)(assert (not (str.in_re \"ab\" re.none)))(check-sat)",
        Verdict::Sat,
    );
    // Empty string in a star.
    expect(
        "(set-logic QF_S)(assert (str.in_re \"\" (re.* (str.to_re \"a\"))))(check-sat)",
        Verdict::Sat,
    );
    // Complement.
    expect(
        "(set-logic QF_S)(assert (str.in_re \"b\" (re.comp (str.to_re \"a\"))))(check-sat)",
        Verdict::Sat,
    );
    // Under or: a false fold forces the other disjunct.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (or (str.in_re \"a\" re.none) (= s \"k\")))(check-sat)",
        Verdict::Sat,
    );
    // Indexed loop.
    expect(
        "(set-logic QF_S)(assert (str.in_re \"aa\" ((_ re.loop 1 3) (str.to_re \"a\"))))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_regex_ground_decided_unsat() {
    expect(
        "(set-logic QF_S)(assert (str.in_re \"ab\" re.none))(check-sat)",
        Verdict::Unsat,
    );
    // Out of range.
    expect(
        "(set-logic QF_S)(assert (str.in_re \"d\" (re.range \"a\" \"c\")))(check-sat)",
        Verdict::Unsat,
    );
    // Negated true fold.
    expect(
        "(set-logic QF_S)(assert (not (str.in_re \"aa\" ((_ re.^ 2) (str.to_re \"a\")))))(check-sat)",
        Verdict::Unsat,
    );
    // r ∩ ¬r = ∅.
    expect(
        "(set-logic QF_S)\
         (assert (str.in_re \"ab\" (re.inter (str.to_re \"ab\") (re.comp (str.to_re \"ab\")))))(check-sat)",
        Verdict::Unsat,
    );
    // Loop upper bound.
    expect(
        "(set-logic QF_S)(assert (str.in_re \"aaa\" ((_ re.loop 1 2) (str.to_re \"a\"))))(check-sat)",
        Verdict::Unsat,
    );
    // Difference removes the word.
    expect(
        "(set-logic QF_S)(assert (str.in_re \"a\" (re.diff re.allchar (str.to_re \"a\"))))(check-sat)",
        Verdict::Unsat,
    );
    // Degenerate range (multi-char endpoint) is EMPTY — decided, not fenced.
    expect(
        "(set-logic QF_S)(assert (str.in_re \"a\" (re.range \"a\" \"ab\")))(check-sat)",
        Verdict::Unsat,
    );
    // Fold under ite: (ite true "x" "y") = "y" is unsat.
    expect(
        "(set-logic QF_S)\
         (assert (= (ite (str.in_re \"a\" (str.to_re \"a\")) \"x\" \"y\") \"y\"))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_regex_fences_unknown() {
    // Symbolic string side.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (str.in_re s re.allchar))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // Symbolic regex leaf (to_re over a var).
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (str.in_re \"a\" (str.to_re s)))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // RegLan equality.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun r () RegLan)\
             (assert (= r re.none))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // A declared-but-unused RegLan symbol fences the whole query.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun r () RegLan)(declare-fun s () String)\
             (assert (= s \"a\"))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // Above-alphabet ground literal (U+30000 raw in the script; shinri-only —
    // z3 is NOT consulted for Unknown pins, so its byte-wise reading of raw
    // UTF-8 does not matter here).
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(assert (str.in_re \"\u{30000}\" re.all))(check-sat)"
        ),
        Verdict::Unknown,
    );
}
```

- [ ] **Step 2: Run the pins FOREGROUND to verify they pass**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_regex -- --nocapture 2>&1 | tail -10`
Expected: 3 tests PASS. If a sat/unsat pin fails on the z3 side, the z3 binary may predate SMT-LIB 2.6 regex names — check `z3 --version` (mise pins it) before touching shinri code.

- [ ] **Step 3: Re-run the whole non-oracle solver suite**

Run: `cargo test -p shinri-solver 2>&1 | tail -5`
Expected: PASS (pins are oracle-gated; nothing else changed).

- [ ] **Step 4: Format, lint, commit**

```bash
cd /workspace && cargo fmt && cargo clippy --workspace --all-targets 2>&1 | tail -5
git add -A
git commit -m "test(str): slice-19 e2e verdict pins for the ground str.in_re fragment (slice 19)"
```

---

### Task 5: qfs_regex_ground_matches_z3 differential oracle family

A 200-iteration differential family with a fresh seed: random constant-regex ASTs weighted across ALL operators × ground strings over the ASCII alphabet, positive-biased by co-generating (regex, witness-string) pairs on the comp/inter-free subset. Verifies the six existing string families re-run unperturbed.

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (generator methods inside `impl Gen`, after `finish_code_conv`; family test after `qfs_code_conv_matches_z3`; `gen_regex_ground_body` beside the other `gen_*_body` fns)

**Interfaces:**
- Consumes: `Gen` (fields `rng: Lcg`, `body: String`), `Lcg::below`, `ALPHABET`, `N_VARS`, `Gen::{var, lit, assertion}`, harness fns `shinri_lines_counting_bailouts`, `z3_verdict`, `z3_with_model`, `parse_string_values`, `Verdict`.
- Produces: `Gen::{rex_sexpr, rex_with_witness, ground_str, regex_assertion, finish_regex_ground}`, `gen_regex_ground_body(seed: u64) -> String`, test `qfs_regex_ground_matches_z3`, consts `RG_N_ITERS: usize = 200`, `RG_MAX_GUARD_BAILOUTS: usize = RG_N_ITERS / 10`.

- [ ] **Step 1: Write the generator**

Add inside `impl Gen`, after `finish_code_conv`:

```rust
    /// A ground string for the regex family: 0..=3 chars over the ASCII
    /// alphabet (ASCII ONLY — raw non-ASCII in a script shared with z3 is a
    /// parser-semantics mismatch, not a solver bug; see the slice-19 plan's
    /// global constraints). Includes "" — nullability coverage.
    fn ground_str(&mut self) -> String {
        let n = self.rng.below(4);
        let mut s = String::new();
        for _ in 0..n {
            s.push_str(ALPHABET[self.rng.below(ALPHABET.len() as u64) as usize]);
        }
        format!("\"{s}\"")
    }

    /// A random CONSTANT regex s-expression, depth-bounded, weighted across
    /// ALL slice-19 operators (comp/inter/diff/loop included). Leaves are
    /// re.none / re.allchar / to_re literals / ranges (occasionally
    /// degenerate: reversed or multi-char endpoints ⇒ empty per SMT-LIB).
    fn rex_sexpr(&mut self, depth: u64) -> String {
        if depth == 0 {
            return match self.rng.below(6) {
                0 => "re.none".to_owned(),
                1 => "re.allchar".to_owned(),
                2 => format!("(str.to_re {})", self.lit()),
                3 => "(str.to_re \"\")".to_owned(),
                4 => "(re.range \"a\" \"c\")".to_owned(),
                // Degenerate ranges: reversed / multi-char endpoint ⇒ ∅.
                _ => ["(re.range \"c\" \"a\")", "(re.range \"a\" \"ab\")"]
                    [self.rng.below(2) as usize]
                    .to_owned(),
            };
        }
        let d = depth - 1;
        match self.rng.below(10) {
            0 => format!("(re.++ {} {})", self.rex_sexpr(d), self.rex_sexpr(d)),
            1 => format!("(re.union {} {})", self.rex_sexpr(d), self.rex_sexpr(d)),
            2 => format!("(re.inter {} {})", self.rex_sexpr(d), self.rex_sexpr(d)),
            3 => format!("(re.diff {} {})", self.rex_sexpr(d), self.rex_sexpr(d)),
            4 => format!("(re.* {})", self.rex_sexpr(d)),
            5 => format!("(re.+ {})", self.rex_sexpr(d)),
            6 => format!("(re.opt {})", self.rex_sexpr(d)),
            7 => format!("(re.comp {})", self.rex_sexpr(d)),
            8 => format!(
                "((_ re.loop {} {}) {})",
                self.rng.below(3),
                self.rng.below(4),
                self.rex_sexpr(d)
            ),
            _ => format!("((_ re.^ {}) {})", self.rng.below(3), self.rex_sexpr(d)),
        }
    }

    /// Co-generate (regex-sexpr, matching word) on the comp/inter-free
    /// subset — the positive-bias sampler: `str.in_re <word> <regex>` is
    /// guaranteed to fold true, so decided-SAT shapes stay common no matter
    /// how the random shapes skew.
    fn rex_with_witness(&mut self, depth: u64) -> (String, String) {
        if depth == 0 {
            return match self.rng.below(3) {
                0 => {
                    let l = self.lit();
                    let w = l.trim_matches('"').to_owned();
                    (format!("(str.to_re {l})"), w)
                }
                1 => ("(str.to_re \"\")".to_owned(), String::new()),
                _ => {
                    let c = ALPHABET[self.rng.below(ALPHABET.len() as u64) as usize];
                    ("(re.range \"a\" \"c\")".to_owned(), c.to_owned())
                }
            };
        }
        let d = depth - 1;
        match self.rng.below(5) {
            0 => {
                let (r1, w1) = self.rex_with_witness(d);
                let (r2, w2) = self.rex_with_witness(d);
                (format!("(re.++ {r1} {r2})"), format!("{w1}{w2}"))
            }
            1 => {
                let (r1, w1) = self.rex_with_witness(d);
                let (r2, _) = self.rex_with_witness(d);
                (format!("(re.union {r1} {r2})"), w1)
            }
            2 => {
                let (r, w) = self.rex_with_witness(d);
                let k = self.rng.below(3) as usize;
                (format!("(re.* {r})"), w.repeat(k))
            }
            3 => {
                let (r, w) = self.rex_with_witness(d);
                let keep = self.rng.below(2) == 0;
                (
                    format!("(re.opt {r})"),
                    if keep { w } else { String::new() },
                )
            }
            _ => {
                let (r, w) = self.rex_with_witness(d);
                let k = 1 + self.rng.below(2);
                (format!("((_ re.^ {k}) {r})"), w.repeat(k as usize))
            }
        }
    }

    /// One slice-19 membership assertion. Half the atoms are witness-built
    /// (guaranteed ground-true before negation), half fully random; ~1 in 6
    /// uses a VARIABLE string side (fence path → shinri-unknown, tolerated).
    /// ~25% negation — the fold is polarity-free.
    fn regex_assertion(&mut self) {
        let depth = 1 + self.rng.below(3); // 1..=3
        let atom = if self.rng.below(6) == 0 {
            format!("(str.in_re {} {})", self.var(), self.rex_sexpr(depth))
        } else if self.rng.below(2) == 0 {
            let (r, w) = self.rex_with_witness(depth);
            format!("(str.in_re \"{w}\" {r})")
        } else {
            format!("(str.in_re {} {})", self.ground_str(), self.rex_sexpr(depth))
        };
        let atom = if self.rng.below(4) == 0 {
            format!("(not {atom})")
        } else {
            atom
        };
        self.body.push_str(&format!("(assert {atom})\n"));
    }

    /// Instance body for the slice-19 family: 1–2 membership assertions +
    /// 0–1 general assertions (cross-theory mixing keeps the SAT witness
    /// path referencing string vars).
    fn finish_regex_ground(mut self) -> String {
        let np = 1 + self.rng.below(2);
        for _ in 0..np {
            self.regex_assertion();
        }
        if self.rng.below(2) == 0 {
            self.assertion();
        }
        self.body
    }
```

Beside the other `gen_*_body` fns:

```rust
fn gen_regex_ground_body(seed: u64) -> String {
    Gen::new(seed).finish_regex_ground()
}
```

- [ ] **Step 2: Write the family test**

After `qfs_code_conv_matches_z3`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Ground-regex differential oracle (slice 19): literal-string × constant-regex
// str.in_re atoms are DECIDED by Brzozowski-derivative evaluation (both
// verdicts, any polarity). Sat AND Unsat must agree with z3; Sat models are
// z3-verified. Out-of-fragment shapes — variable string sides — fence
// (tolerated unknown). ASCII-only scripts (see the slice-19 plan). Fresh
// seed — never perturb existing families' seeds.
// ─────────────────────────────────────────────────────────────────────────────

const RG_N_ITERS: usize = 200;
const RG_MAX_GUARD_BAILOUTS: usize = RG_N_ITERS / 10;

#[test]
fn qfs_regex_ground_matches_z3() {
    let mut rng = Lcg(0x51_63_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness, mut n_guard_bailout) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..RG_N_ITERS {
        let seed = rng.next();
        let body = gen_regex_ground_body(seed);

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
            "QF_S REGEX_GROUND SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
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
        "qfs_regex_ground_matches_z3: {RG_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown (tolerated) / {n_z3skip} z3-unknown / \
         {n_guard_bailout} guard-bailout (tolerated); {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "regex-ground family produced zero SAT instances");
    assert!(
        n_unsat > 0,
        "regex-ground family produced zero UNSAT instances"
    );
    assert!(
        n_witness > 0,
        "no witnesses checked — model path not exercised"
    );
    assert!(
        n_guard_bailout <= RG_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailout} exceed bound {RG_MAX_GUARD_BAILOUTS}"
    );
}
```

- [ ] **Step 3: Run the new family FOREGROUND, capture the tally**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential qfs_regex_ground_matches_z3 -- --nocapture 2>&1 | tail -15`
Expected: PASS with a printed tally line (`X sat / Y unsat / … 0 disagreements`). RECORD the tally — the spec truth-up (Task 6) quotes it. If a disagreement fires, reproduce the printed body directly against z3 before changing any rewrite: the bug may be in the generator (illegal SMT-LIB), the harness, or the fold — diagnose from the reproduction, don't guess.

- [ ] **Step 4: Re-run ALL existing string families FOREGROUND — tallies must be identical to their committed values**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture 2>&1 | grep -E "matches_z3|test result" `
Expected: every family PASSES; `qfs_code_conv` prints 92/97/11 + 63 witnesses, `qfs_const_int_conv` 59/57/84, `qfs_replace_all` 51/74/75 — all identical to their committed tallies (this slice touches no shared string code path except purely-additive fences).

- [ ] **Step 5: Format, lint, commit**

```bash
cd /workspace && cargo fmt && cargo clippy --workspace --all-targets 2>&1 | tail -5
git add -A
git commit -m "test(str): qfs_regex_ground_matches_z3 differential oracle family (slice 19)"
```

---

### Task 6: Spec truth-up + PR

Update the spec to IMPLEMENTED with the observed oracle tally and any deviations discovered during implementation (the ASCII-only oracle corpus is already IN the spec — it is not a deviation). Open the PR.

**Files:**
- Modify: `docs/superpowers/specs/2026-07-13-shinri-slice19-regex-ground-design.md` (header + Testing section)

**Interfaces:**
- Consumes: Task 5's recorded tally.
- Produces: the merged slice.

- [ ] **Step 1: Truth up the spec**

Replace the `Status:` line with `Status: IMPLEMENTED (slice 19 landed 2026-07-13).` and insert after it (fill in the REAL numbers from Task 5 Step 3):

```markdown
Oracle (`qfs_regex_ground_matches_z3`, fresh seed `0x51_63_0000_0001`, 200
iters): <sat> sat / <unsat> unsat / <unk> shinri-unknown (tolerated) /
<z3skip> z3-unknown / <bail> guard-bailout / <wit> witnesses / **0
disagreements**. All pre-existing string families re-ran unperturbed with
tallies identical to their committed values.

**Deviations from the spec.**
<deviations discovered during implementation, one numbered item each with
the what and the why, or "None.">
```

- [ ] **Step 2: Commit and open the PR**

```bash
cd /workspace && cargo fmt --check && git add -A
git commit -m "docs: slice-19 spec truth-up — IMPLEMENTED + oracle tally"
git push -u origin slice19-regex-ground
gh pr create --title "Slice 19: RegLan plumbing + ground str.in_re by Brzozowski derivatives" \
  --body "$(cat <<'EOF'
## Summary
- Spec 2 (regex) kickoff: full RegLan operator surface parses; ground
  str.in_re (literal string × constant regex) is DECIDED at any polarity by
  Brzozowski derivative + nullability; everything else fences to sound
  Unknown (presence fence + RegLan-declaration fence).
- New: SortNode::RegLan, 16 BuiltinOps, crates/shinri-str/src/regex.rs
  (Rex AST, smart constructors, deriv/nullable, fuel-capped eval, extraction,
  rewrite pass, fence).
- Tests: per-operator unit tests, e2e verdict pins, and the
  qfs_regex_ground_matches_z3 differential family (200 iters, fresh seed,
  0 disagreements). Existing string families unperturbed.

Spec: docs/superpowers/specs/2026-07-13-shinri-slice19-regex-ground-design.md
Plan: docs/superpowers/plans/2026-07-13-shinri-slice19-regex-ground.md
EOF
)"
```

Expected: PR created; CI (fmt gate + full workspace + oracle) goes green.
