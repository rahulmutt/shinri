# Slice 13: str.indexof / str.replace Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit `str.indexof` and `str.replace` end-to-end — constant-fold fully-literal applications, partial-eval literal-haystack shapes via exact polarity-free rewrites, fence everything else to sound `Unknown` — per the approved spec `docs/superpowers/specs/2026-07-10-shinri-slice13-str-indexof-replace-design.md`.

**Architecture:** Two new `BuiltinOp` variants flow parser → a new `shinri-str/src/indexof_replace.rs` pre-pass (bottom-up memoized rewrite + presence fence) → wired into the solver's string path immediately after `fold_str_predicates` (crates/shinri-solver/src/lib.rs:414). The rewrites reuse already-validated machinery only: `StrConcat` word equations, and Int-sorted `Ite` chains that `reduce_assertions`' existing `elim_term_ite` eliminates downstream. The pass introduces **zero fresh variables**.

**Tech Stack:** Rust workspace (`cargo`), `rustc-hash` maps, differential oracle vs z3 (`--features oracle`, z3 on PATH via mise).

## Global Constraints

- Pure Rust, no new dependencies (spec: reuse `rustc_hash`, `shinri_core` only).
- **Code-point (Unicode scalar) indices everywhere** — never bytes. Concrete evaluation operates on `Vec<char>`, matching `eval_substr_const` (crates/shinri-str/src/reduce.rs:50).
- **Argument order (haystack-first, both ops):** `(str.indexof s sub i)` searches `sub` in `s`; `(str.replace s t u)` replaces `t` by `u` in `s`.
- **Pinned semantics (spec "Pinned SMT-LIB 2.6 semantics"):** indexof: `-1` if `i < 0 || i > |s|` (`i = |s|` is IN range); else smallest occurrence `j ≥ i`, occurrences may overlap; empty needle occurs at every `0 ≤ j ≤ |s|`. replace: leftmost occurrence replaced; needle absent → `s` unchanged; empty needle → `u ++ s`.
- `INDEXOF_CHAIN_CAP = 64` code points: the symbolic-`i` ite chain applies only when `|s| ≤ 64`; over-cap → left in place → fence. Folding has no cap.
- **Never perturb existing oracle families or seeds** (`qfs_matches_z3` @ `0x5_1_1A_0000_0001`, `qfs_predicates_matches_z3` @ `0x51_2A_0000_0001`, nary family @ `0xB000_9E38`, fp-bridge str family). The new family gets its OWN seed `0x51_3A_0000_0001`.
- House style: `cargo fmt --all` and `cargo clippy --workspace --all-targets` clean before final commit; commit subjects end with `(slice 13)`.
- Oracle tests are `#[cfg(feature = "oracle")]` and need `z3` on PATH (mise provides it: `mise exec -- <cmd>` if not activated).

## File Structure

- Modify `crates/shinri-core/src/term.rs` — two `BuiltinOp` variants.
- Modify `crates/shinri-core/src/context.rs` — sort rules + sort-rule test.
- Modify `crates/shinri-parser/src/parser.rs` — op-name table + parse tests.
- Modify `crates/shinri-parser/src/print.rs` — SMT-LIB names + print test.
- **Create `crates/shinri-str/src/indexof_replace.rs`** — the whole pre-pass: concrete evaluators, rewrite, fence, unit tests. Single-responsibility module, same shape as `predicates.rs`.
- Modify `crates/shinri-str/src/lib.rs` — `pub mod indexof_replace;`.
- Modify `crates/shinri-str/src/reduce.rs` — `int_numeral` → `pub(crate)`; add variants to `contains_string_op`.
- Modify `crates/shinri-solver/src/string_stage.rs` — add variants to `is_string_op`.
- Modify `crates/shinri-solver/src/lib.rs` — pipeline wiring (2 calls, after line 414).
- Modify `crates/shinri-solver/tests/script_e2e.rs` — decided pins + fence canaries.
- Modify `crates/shinri-solver/tests/qfs_differential.rs` — new oracle family.

---

### Task 1: Core — `StrIndexOf` / `StrReplace` variants + sort rules

**Files:**
- Modify: `crates/shinri-core/src/term.rs:92` (after `StrContains`)
- Modify: `crates/shinri-core/src/context.rs:496-501` (after the `StrPrefixOf | StrSuffixOf | StrContains` arm)
- Test: `crates/shinri-core/src/context.rs` (tests module, after `string_predicate_sorts` at :1311)

**Interfaces:**
- Consumes: existing `BuiltinOp` enum, `expect_arity`, `expect_all`, `SortError::Mismatch` (all in context.rs, see the `StrSubstr` arm at :477 for the 3-arity mixed-sort pattern).
- Produces: `BuiltinOp::StrIndexOf` (sort rule `String × String × Int → Int`), `BuiltinOp::StrReplace` (`String × String × String → String`) — every later task builds terms with these exact variant names via `ctx.mk_app(Op::Builtin(...), &[...])`.

- [ ] **Step 1: Write the failing sort-rule test**

In `crates/shinri-core/src/context.rs`, immediately after the `string_predicate_sorts` test (ends :1333), add:

```rust
    #[test]
    fn string_indexof_replace_sorts() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let f = ctx.declare_fun("x", &[], str_s);
        let x = ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap();
        let lit = ctx.mk_string_const("ab");
        let i = ctx.mk_numeral(Rational::from_int(1i128.into()), int_s);

        // (str.indexof s sub i): String × String × Int → Int.
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, lit, i])
            .unwrap();
        assert_eq!(ctx.sort_of(idx), int_s, "indexof must be Int-sorted");
        // (str.replace s t u): String × String × String → String.
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[x, lit, lit])
            .unwrap();
        assert_eq!(ctx.sort_of(rep), str_s, "replace must be String-sorted");

        // Arity 3 enforced.
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, lit])
            .is_err());
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[x, lit])
            .is_err());
        // indexof: args 0-1 String, arg 2 Int.
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, lit, lit])
            .is_err());
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, i, i])
            .is_err());
        // replace: all three String.
        assert!(ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[x, lit, i])
            .is_err());
    }
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core string_indexof_replace_sorts`
Expected: COMPILE FAILURE — `no variant named StrIndexOf` (the variant doesn't exist yet; a compile failure on the new name is this step's "red").

- [ ] **Step 3: Add the variants and sort rules**

In `crates/shinri-core/src/term.rs`, after `StrContains,` (line 92):

```rust
    // Slice 13: search/replace ops. Arg order per SMT-LIB: BOTH are
    // haystack-first — (str.indexof s sub i), (str.replace s t u).
    StrIndexOf, // String × String × Int → Int
    StrReplace, // String × String × String → String
```

In `crates/shinri-core/src/context.rs`, after the `StrPrefixOf | StrSuffixOf | StrContains` arm (ends :501):

```rust
            StrIndexOf => {
                expect_arity(args, 3)?;
                let (str_s, int_s) = (self.string_sort(), self.int_sort());
                for &a in &args[0..2] {
                    if self.sort_of(a) != str_s {
                        return Err(SortError::Mismatch {
                            expected: str_s,
                            found: self.sort_of(a),
                        });
                    }
                }
                if self.sort_of(args[2]) != int_s {
                    return Err(SortError::Mismatch {
                        expected: int_s,
                        found: self.sort_of(args[2]),
                    });
                }
                Ok(int_s)
            }
            StrReplace => {
                expect_arity(args, 3)?;
                let str_s = self.string_sort();
                expect_all(self, args, str_s)?;
                Ok(str_s)
            }
```

If the enum derives an exhaustive-match anywhere else (compiler will tell you: run `cargo build -p shinri-core -p shinri-parser -p shinri-str -p shinri-solver` and fix any non-exhaustive `match` on `BuiltinOp`), the ONLY correct fillers at this stage are: parser/print (Task 2 owns those — if they match exhaustively, add temporary arms mirroring the predicate arms now and Task 2's content supersedes), and any solver-side op classifier lists (add the two variants to the same bucket as `StrContains`).

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-core string_indexof_replace_sorts`
Expected: PASS. Also run `cargo build --workspace` — expected: clean (fix exhaustive matches as above if not).

- [ ] **Step 5: Commit**

```bash
git add -A crates
git commit -m "feat(core): StrIndexOf/StrReplace builtin ops + sort rules (slice 13)"
```

---

### Task 2: Parser + printer surface

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs:327` (op-name table, after `"str.contains"`)
- Modify: `crates/shinri-parser/src/print.rs:195` (after `StrContains`)
- Test: `crates/shinri-parser/src/parser.rs` (tests module, after `string_predicate_wrong_sort_rejected` at :1857); `crates/shinri-parser/src/print.rs` (tests module)

**Interfaces:**
- Consumes: `BuiltinOp::StrIndexOf` / `BuiltinOp::StrReplace` from Task 1; existing test helpers `parse_all_ok`, `commands` (see `parses_string_predicates` :1821 for usage).
- Produces: surface syntax `str.indexof` / `str.replace` parseable and printable — Tasks 6-7 write SMT-LIB scripts using these names.

- [ ] **Step 1: Write the failing parser tests**

In `crates/shinri-parser/src/parser.rs` tests module, after `string_predicate_wrong_sort_rejected`:

```rust
    /// Parse str.indexof / str.replace, verify op + result sort (slice 13).
    #[test]
    fn parses_indexof_and_replace() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        // Both nested under (= … …) so the asserted term is Bool.
        let src = r#"(declare-fun x () String)
(assert (= (str.indexof x "a" 0) 1))
(assert (= (str.replace x "a" "b") x))"#;
        let (ctx, cmds) = parse_all_ok(src);
        assert_eq!(cmds.len(), 3);
        for (ci, want, want_sort) in [
            (1usize, BuiltinOp::StrIndexOf, ctx.int_sort()),
            (2usize, BuiltinOp::StrReplace, ctx.string_sort()),
        ] {
            let assert_term = match &cmds[ci] {
                Command::Assert(t) => *t,
                other => panic!("expected Assert, got {other:?}"),
            };
            let TermNode::App { op: Op::Builtin(BuiltinOp::Eq), args, .. } =
                ctx.term_node(assert_term).clone()
            else {
                panic!("expected Eq at top level");
            };
            let lhs = ctx.children(args).to_vec()[0];
            match ctx.term_node(lhs).clone() {
                TermNode::App { op: Op::Builtin(got), .. } => {
                    assert_eq!(got, want, "op mismatch");
                }
                other => panic!("expected App lhs, got {other:?}"),
            }
            assert_eq!(ctx.sort_of(lhs), want_sort, "result sort for {want:?}");
        }
    }

    /// Ill-sorted operands are diagnostics, not crashes (slice 13).
    #[test]
    fn indexof_replace_wrong_sort_rejected() {
        // indexof third arg must be Int.
        let cs = commands(r#"(declare-fun x () String)(assert (= (str.indexof x "a" "b") 0))"#);
        assert!(cs[1].is_err(), "String start index must be a diagnostic");
        // replace third arg must be String.
        let cs = commands(r#"(declare-fun x () String)(assert (= (str.replace x "a" 1) x))"#);
        assert!(cs[1].is_err(), "Int replacement must be a diagnostic");
    }
```

In `crates/shinri-parser/src/print.rs` tests module, after `prints_fp_const_and_rm`:

```rust
    #[test]
    fn prints_indexof_and_replace() {
        use shinri_core::{BuiltinOp, Op, Rational};
        let mut ctx = shinri_core::Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let f = ctx.declare_fun("x", &[], str_s);
        let x = ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap();
        let a = ctx.mk_string_const("a");
        let zero = ctx.mk_numeral(Rational::from_int(0i128.into()), int_s);
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, a, zero])
            .unwrap();
        assert_eq!(print_term(&ctx, idx), r#"(str.indexof x "a" 0)"#);
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[x, a, a])
            .unwrap();
        assert_eq!(print_term(&ctx, rep), r#"(str.replace x "a" "a")"#);
    }
```

(If the printed numeral/literal spellings differ from the house format — run the test and read the actual output — match the assertion to the house format, e.g. `0` vs `0.0`: string ops take Int numerals so `0` is expected, mirroring how `str.substr` prints in existing round-trip tests.)

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-parser parses_indexof_and_replace indexof_replace_wrong_sort_rejected prints_indexof_and_replace`
Expected: FAIL — parser emits `unknown operator str.indexof` diagnostic (test panics on `parse_all_ok`), unless Task 1 Step 3 already added temporary arms, in which case tests pass — then verify the arms match Step 3 below and move on.

- [ ] **Step 3: Add the two ops to parser and printer**

`crates/shinri-parser/src/parser.rs`, after `"str.contains" => StrContains,` (:327):

```rust
            "str.indexof" => StrIndexOf,
            "str.replace" => StrReplace,
```

`crates/shinri-parser/src/print.rs`, after `StrContains => "str.contains".to_owned(),` (:195):

```rust
        // Slice 13
        StrIndexOf => "str.indexof".to_owned(),
        StrReplace => "str.replace".to_owned(),
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-parser parses_indexof_and_replace indexof_replace_wrong_sort_rejected prints_indexof_and_replace`
Expected: 3 PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-parser
git commit -m "feat(parser): parse + print str.indexof / str.replace (slice 13)"
```

---

### Task 3: `indexof_replace.rs` — concrete evaluators + all-literal fold

**Files:**
- Create: `crates/shinri-str/src/indexof_replace.rs`
- Modify: `crates/shinri-str/src/lib.rs` (add `pub mod indexof_replace;` after `pub mod fuel`-adjacent block — alphabetical: between `mod fuel;` and `mod length;` is fine as `pub mod indexof_replace;`)
- Modify: `crates/shinri-str/src/reduce.rs:32` (`fn int_numeral` → `pub(crate) fn int_numeral`)
- Test: same file (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `crate::reduce::int_numeral(ctx, t) -> Option<i128>` (made `pub(crate)` here); `ctx.string_const_value(t) -> Option<&str>`; `ctx.mk_string_const(&str) -> TermId`; `ctx.mk_numeral(Rational, SortId) -> TermId`.
- Produces:
  - `pub fn partial_eval_indexof_replace(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>` (Task 6 wires this into the solver);
  - private `fn occurrences(hay: &[char], needle: &[char]) -> Vec<usize>`, `fn eval_indexof(hay: &[char], needle: &[char], i: i128) -> i128`, `fn eval_replace(hay: &[char], t: &[char], u: &str) -> String` (Tasks 4-5 reuse `occurrences`);
  - private `fn rewrite_indexof(ctx, kids) -> Option<TermId>` / `fn rewrite_replace(ctx, kids) -> Option<TermId>` — `None` = "no case applies, leave in place" (Tasks 4-5 extend these).

- [ ] **Step 1: Write the failing tests**

Create `crates/shinri-str/src/indexof_replace.rs` with ONLY the test module first (so the test names exist), plus a `use` header — the implementation lands in Step 3:

```rust
//! Slice 13 pre-pass: `str.indexof` / `str.replace` — fold, partial-eval,
//! fence.
//!
//! Both ops are value-sorted FUNCTIONS (Int / String), so unlike the slice-12
//! predicates the rewrites here are exact at any position and polarity — no
//! polarity analysis, and the pass introduces ZERO fresh variables.
//!
//! Stages (run by the solver's string-path seam):
//! 1. [`partial_eval_indexof_replace`] — bottom-up memoized rewrite:
//!    - fold fully-literal applications to their concrete value;
//!    - `(str.replace lit lit u)` → concat decomposition around the leftmost
//!      occurrence (exact for any symbolic `u`);
//!    - `(str.indexof lit lit i)` with symbolic `i` → bounded Int-ite step
//!      chain (`INDEXOF_CHAIN_CAP`), eliminated downstream by
//!      `reduce_assertions`' `elim_term_ite`.
//! 2. [`has_unreduced_indexof_replace`] — presence fence: any surviving
//!    application (symbolic haystack/needle, over-cap literal, or a
//!    non-literal-yet-foldable operand like a constant substr — sound, just
//!    undecided) fences the query to a sound `Unknown`.
//!
//! All indices are CODE POINTS (`Vec<char>`), matching `eval_substr_const` —
//! never bytes.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// Cap on `|s|` (code points) for the symbolic-`i` indexof ite chain. Over-cap
/// applications are left in place and fence. Folding has NO cap.
const INDEXOF_CHAIN_CAP: usize = 64;
```

Then the tests (bottom of file):

```rust
#[cfg(test)]
mod tests {
    use super::*;

    // ── Concrete evaluators ──────────────────────────────────────────────

    fn chars(s: &str) -> Vec<char> {
        s.chars().collect()
    }

    #[test]
    fn occurrences_enumerates_overlaps_and_edges() {
        // Overlapping occurrences are ALL enumerated.
        assert_eq!(occurrences(&chars("aaa"), &chars("aa")), vec![0, 1]);
        // Empty needle occurs at every 0..=|s| position.
        assert_eq!(occurrences(&chars("ab"), &chars("")), vec![0, 1, 2]);
        // Needle longer than haystack: none.
        assert_eq!(occurrences(&chars("a"), &chars("ab")), Vec::<usize>::new());
        // Needle at the very end.
        assert_eq!(occurrences(&chars("abc"), &chars("c")), vec![2]);
        // Code points, not bytes: 'é' is 1 position.
        assert_eq!(occurrences(&chars("héllo"), &chars("l")), vec![2, 3]);
    }

    #[test]
    fn eval_indexof_pinned_semantics() {
        let h = chars("abcb");
        let b = chars("b");
        assert_eq!(eval_indexof(&h, &b, 0), 1);
        assert_eq!(eval_indexof(&h, &b, 2), 3); // smallest occurrence >= i
        assert_eq!(eval_indexof(&h, &b, 4), -1); // i = |s| in range, no hit
        assert_eq!(eval_indexof(&h, &b, -1), -1); // i < 0
        assert_eq!(eval_indexof(&h, &b, 5), -1); // i > |s|
        // Empty needle: result = i whenever 0 <= i <= |s| (INCLUDING |s|).
        let e = chars("");
        assert_eq!(eval_indexof(&h, &e, 4), 4);
        assert_eq!(eval_indexof(&h, &e, 0), 0);
        assert_eq!(eval_indexof(&h, &e, 5), -1);
        // Code points: indexof("héllo","l",0) = 2 (byte-based would be 3).
        assert_eq!(eval_indexof(&chars("héllo"), &chars("l"), 0), 2);
    }

    #[test]
    fn eval_replace_pinned_semantics() {
        // Leftmost occurrence only.
        assert_eq!(eval_replace(&chars("abcb"), &chars("b"), "X"), "aXcb");
        // Needle absent: haystack unchanged (u irrelevant).
        assert_eq!(eval_replace(&chars("abc"), &chars("z"), "X"), "abc");
        // Empty needle: u ++ s.
        assert_eq!(eval_replace(&chars("ab"), &chars(""), "X"), "Xab");
        // Code points.
        assert_eq!(eval_replace(&chars("héllo"), &chars("é"), "e"), "hello");
    }

    // ── Fold rewrite ─────────────────────────────────────────────────────

    fn str_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn int_lit(ctx: &mut Context, v: i128) -> TermId {
        let int_s = ctx.int_sort();
        ctx.mk_numeral(shinri_core::Rational::from_int(v.into()), int_s)
    }

    #[test]
    fn folds_all_literal_indexof_and_replace() {
        let mut ctx = Context::new();
        let abcb = ctx.mk_string_const("abcb");
        let b = ctx.mk_string_const("b");
        let x_lit = ctx.mk_string_const("X");
        let zero = int_lit(&mut ctx, 0);
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[abcb, b, zero])
            .unwrap();
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[abcb, b, x_lit])
            .unwrap();
        // Wrap in Bool atoms (assertions are Bool): (= idx 1), (= rep "aXcb").
        let one = int_lit(&mut ctx, 1);
        let a1 = ctx.mk_eq(idx, one).unwrap();
        let want_rep = ctx.mk_string_const("aXcb");
        let a2 = ctx.mk_eq(rep, want_rep).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[a1, a2]);
        // (= 1 1) and (= "aXcb" "aXcb") — both sides now the SAME TermId.
        let want1 = ctx.mk_eq(one, one).unwrap();
        let want2 = ctx.mk_eq(want_rep, want_rep).unwrap();
        assert_eq!(out, vec![want1, want2]);
    }

    #[test]
    fn folds_negative_result_indexof() {
        let mut ctx = Context::new();
        let abc = ctx.mk_string_const("abc");
        let z = ctx.mk_string_const("z");
        let zero = int_lit(&mut ctx, 0);
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[abc, z, zero])
            .unwrap();
        let neg1 = int_lit(&mut ctx, -1);
        let atom = ctx.mk_eq(idx, neg1).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let want = ctx.mk_eq(neg1, neg1).unwrap();
        assert_eq!(out, vec![want]);
    }

    #[test]
    fn symbolic_haystack_left_untouched_same_termid() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let b = ctx.mk_string_const("b");
        let zero = int_lit(&mut ctx, 0);
        let one = int_lit(&mut ctx, 1);
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[s, b, zero])
            .unwrap();
        let atom = ctx.mk_eq(idx, one).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom], "untouched subtree must keep its TermId");
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

First add to `crates/shinri-str/src/lib.rs` (after `mod fuel;`): `pub mod indexof_replace;`
Run: `cargo test -p shinri-str indexof_replace`
Expected: COMPILE FAILURE — `occurrences`, `eval_indexof`, `eval_replace`, `partial_eval_indexof_replace` not found.

- [ ] **Step 3: Implement evaluators + fold-only rewrite**

In `crates/shinri-str/src/reduce.rs:32` change `fn int_numeral` to `pub(crate) fn int_numeral` (doc comment unchanged).

In `crates/shinri-str/src/indexof_replace.rs`, between the header and the test module:

```rust
/// Every occurrence position (code-point index) of `needle` in `hay`,
/// ascending, OVERLAPS INCLUDED. The empty needle occurs at every
/// `0..=|hay|` position (SMT-LIB semantics).
fn occurrences(hay: &[char], needle: &[char]) -> Vec<usize> {
    let (n, m) = (hay.len(), needle.len());
    if m > n {
        return Vec::new();
    }
    (0..=(n - m)).filter(|&j| hay[j..j + m] == *needle).collect()
}

/// Concrete `(str.indexof s sub i)` per the pinned SMT-LIB 2.6 semantics.
fn eval_indexof(hay: &[char], needle: &[char], i: i128) -> i128 {
    let n = hay.len() as i128;
    if i < 0 || i > n {
        return -1;
    }
    occurrences(hay, needle)
        .into_iter()
        .map(|j| j as i128)
        .find(|&j| j >= i)
        .unwrap_or(-1)
}

/// Concrete `(str.replace s t u)`: replace the LEFTMOST occurrence of `t`
/// by `u`; `s` unchanged if `t` does not occur.
fn eval_replace(hay: &[char], t: &[char], u: &str) -> String {
    match occurrences(hay, t).first() {
        Some(&p) => {
            let pre: String = hay[..p].iter().collect();
            let post: String = hay[p + t.len()..].iter().collect();
            format!("{pre}{u}{post}")
        }
        None => hay.iter().collect(),
    }
}

/// Stage 1: bottom-up memoized rewrite. Folds / partial-evals every
/// `str.indexof` / `str.replace` application whose haystack AND needle are
/// string literals; anything else is left in place (the caller fences it via
/// [`has_unreduced_indexof_replace`]). Untouched subtrees keep their TermIds.
pub fn partial_eval_indexof_replace(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
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
                Op::Builtin(BuiltinOp::StrIndexOf) => rewrite_indexof(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrReplace) => rewrite_replace(ctx, &new_children),
                _ => None,
            };
            if let Some(r) = special {
                r
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(nc, oc)| nc != oc);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("rewrite: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// `(str.indexof s sub i)`, children already rewritten. Some(_) iff a fold /
/// partial-eval case applies; None leaves the app in place (→ fence).
fn rewrite_indexof(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let hay: Vec<char> = ctx.string_const_value(kids[0])?.chars().collect();
    let needle: Vec<char> = ctx.string_const_value(kids[1])?.chars().collect();
    if let Some(iv) = crate::reduce::int_numeral(ctx, kids[2]) {
        let v = eval_indexof(&hay, &needle, iv);
        let int_s = ctx.int_sort();
        return Some(ctx.mk_numeral(shinri_core::Rational::from_int(v.into()), int_s));
    }
    None // Task 5 adds the symbolic-i ite chain here.
}

/// `(str.replace s t u)`, children already rewritten. Some(_) iff haystack
/// and needle are literals; None leaves the app in place (→ fence).
fn rewrite_replace(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let hay: Vec<char> = ctx.string_const_value(kids[0])?.chars().collect();
    let t: Vec<char> = ctx.string_const_value(kids[1])?.chars().collect();
    let u = ctx.string_const_value(kids[2]).map(str::to_owned)?;
    Some(ctx.mk_string_const(&eval_replace(&hay, &t, &u)))
    // Task 4 replaces the two lines above with the symbolic-u decomposition.
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str indexof_replace`
Expected: 6 PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-str
git commit -m "feat(str): indexof_replace pre-pass — concrete evaluators + all-literal fold (slice 13)"
```

---

### Task 4: Partial-eval replace (symbolic replacement)

**Files:**
- Modify: `crates/shinri-str/src/indexof_replace.rs` (`rewrite_replace` + tests)

**Interfaces:**
- Consumes: `occurrences`, `eval_replace` from Task 3.
- Produces: `rewrite_replace` now returns `Some` whenever haystack AND needle are literals, regardless of `u`: needle absent → the literal haystack (exact, `u` irrelevant); found at `p` → `(str.++ pre u post)` with EMPTY LITERAL FLANKS DROPPED (result is bare `u` when both flanks empty; `(str.++ u s)` for the empty needle).

- [ ] **Step 1: Write the failing tests** (append inside the tests module)

```rust
    /// Destructure `(str.++ …)` into its children.
    fn concat_parts(ctx: &Context, t: TermId) -> Vec<TermId> {
        let TermNode::App { op, args, .. } = ctx.term_node(t) else {
            panic!("expected concat app");
        };
        assert!(matches!(op, Op::Builtin(BuiltinOp::StrConcat)));
        ctx.children(*args).to_vec()
    }

    #[test]
    fn replace_symbolic_u_decomposes_at_leftmost_occurrence() {
        let mut ctx = Context::new();
        let abcb = ctx.mk_string_const("abcb");
        let b = ctx.mk_string_const("b");
        let u = str_var(&mut ctx, "u");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[abcb, b, u])
            .unwrap();
        let out_s = str_var(&mut ctx, "r");
        let atom = ctx.mk_eq(rep, out_s).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        // (= (str.++ "a" u "cb") r) — leftmost "b" is at position 1.
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let eq_kids = ctx.children(args).to_vec();
        let parts = concat_parts(&ctx, eq_kids[0]);
        assert_eq!(parts.len(), 3);
        assert_eq!(ctx.string_const_value(parts[0]), Some("a"));
        assert_eq!(parts[1], u);
        assert_eq!(ctx.string_const_value(parts[2]), Some("cb"));
    }

    #[test]
    fn replace_empty_flanks_dropped() {
        let mut ctx = Context::new();
        let u = str_var(&mut ctx, "u2");
        let r = str_var(&mut ctx, "r2");
        // Whole-haystack needle: (str.replace "ab" "ab" u) → bare u.
        let ab = ctx.mk_string_const("ab");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[ab, ab, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let want = ctx.mk_eq(u, r).unwrap();
        assert_eq!(out, vec![want], "both flanks empty → result is bare u");
        // Empty needle: (str.replace "ab" "" u) → (str.++ u "ab").
        let empty = ctx.mk_string_const("");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[ab, empty, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let eq_kids = ctx.children(args).to_vec();
        let parts = concat_parts(&ctx, eq_kids[0]);
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0], u);
        assert_eq!(ctx.string_const_value(parts[1]), Some("ab"));
    }

    #[test]
    fn replace_needle_absent_drops_symbolic_u() {
        let mut ctx = Context::new();
        let abc = ctx.mk_string_const("abc");
        let z = ctx.mk_string_const("z");
        let u = str_var(&mut ctx, "u3");
        let r = str_var(&mut ctx, "r3");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[abc, z, u])
            .unwrap();
        let atom = ctx.mk_eq(rep, r).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        // Result does not depend on u: (= "abc" r).
        let want = ctx.mk_eq(abc, r).unwrap();
        assert_eq!(out, vec![want]);
    }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str indexof_replace`
Expected: the 3 new tests FAIL (symbolic `u` currently returns `None` → app left in place); the 6 Task-3 tests still PASS.

- [ ] **Step 3: Implement — replace `rewrite_replace`'s body**

```rust
/// `(str.replace s t u)`, children already rewritten. Some(_) iff haystack
/// and needle are literals — EXACT for any `u` (the decomposition point is
/// concrete). None (symbolic haystack/needle) leaves the app in place (→
/// fence).
fn rewrite_replace(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let hay: Vec<char> = ctx.string_const_value(kids[0])?.chars().collect();
    let t: Vec<char> = ctx.string_const_value(kids[1])?.chars().collect();
    let u = kids[2];
    let Some(&p) = occurrences(&hay, &t).first() else {
        // Needle absent: result is the haystack; `u` is irrelevant (exact).
        return Some(kids[0]);
    };
    if let Some(uv) = ctx.string_const_value(u).map(str::to_owned) {
        // Fully literal: fold to a single literal.
        return Some(ctx.mk_string_const(&eval_replace(&hay, &t, &uv)));
    }
    // Symbolic u: (str.++ pre u post), empty literal flanks dropped.
    let pre: String = hay[..p].iter().collect();
    let post: String = hay[p + t.len()..].iter().collect();
    let mut parts: Vec<TermId> = Vec::new();
    if !pre.is_empty() {
        parts.push(ctx.mk_string_const(&pre));
    }
    parts.push(u);
    if !post.is_empty() {
        parts.push(ctx.mk_string_const(&post));
    }
    Some(if parts.len() == 1 {
        parts[0]
    } else {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &parts)
            .expect("pre ++ u ++ post")
    })
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str indexof_replace`
Expected: 9 PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-str
git commit -m "feat(str): partial-eval str.replace with symbolic replacement (slice 13)"
```

---

### Task 5: Partial-eval indexof (symbolic start index → bounded ite chain)

**Files:**
- Modify: `crates/shinri-str/src/indexof_replace.rs` (`rewrite_indexof` + tests)

**Interfaces:**
- Consumes: `occurrences`, `INDEXOF_CHAIN_CAP` from Task 3; `BuiltinOp::{Ite, Le, Lt, Ge, And}` (all existing arith/bool builtins — see reduce.rs:225-249 for usage style).
- Produces: `rewrite_indexof` additionally handles literal haystack+needle with symbolic `i`, iff `|s| <= INDEXOF_CHAIN_CAP`; emits an Int-sorted ite chain (the string-path `reduce_assertions` → `elim_term_ite` eliminates it downstream — no new machinery).

- [ ] **Step 1: Write the failing tests** (append inside the tests module)

```rust
    fn is_ite(ctx: &Context, t: TermId) -> bool {
        matches!(
            ctx.term_node(t),
            TermNode::App { op: Op::Builtin(BuiltinOp::Ite), .. }
        )
    }

    fn contains_op(ctx: &Context, t: TermId, want: BuiltinOp) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(o) if *o == want)
                    || ctx
                        .children(*args)
                        .to_vec()
                        .iter()
                        .any(|&c| contains_op(ctx, c, want))
            }
            TermNode::Const { .. } => false,
        }
    }

    #[test]
    fn indexof_symbolic_start_becomes_ite_chain() {
        let mut ctx = Context::new();
        let abcb = ctx.mk_string_const("abcb");
        let b = ctx.mk_string_const("b");
        let int_s = ctx.int_sort();
        let i = {
            let f = ctx.declare_fun("i", &[], int_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[abcb, b, i])
            .unwrap();
        let one = int_lit(&mut ctx, 1);
        let atom = ctx.mk_eq(idx, one).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(
            !contains_op(&ctx, out[0], BuiltinOp::StrIndexOf),
            "indexof must be rewritten away"
        );
        // The eq's lhs is now the outer (ite (< i 0) -1 …) chain.
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let lhs = ctx.children(args).to_vec()[0];
        assert!(is_ite(&ctx, lhs), "expected an Int-ite chain, got {lhs:?}");
        assert_eq!(ctx.sort_of(lhs), int_s);
    }

    #[test]
    fn indexof_empty_needle_symbolic_start_is_range_ite() {
        let mut ctx = Context::new();
        let ab = ctx.mk_string_const("ab");
        let empty = ctx.mk_string_const("");
        let int_s = ctx.int_sort();
        let i = {
            let f = ctx.declare_fun("i2", &[], int_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[ab, empty, i])
            .unwrap();
        let zero = int_lit(&mut ctx, 0);
        let atom = ctx.mk_eq(idx, zero).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(!contains_op(&ctx, out[0], BuiltinOp::StrIndexOf));
        // (ite (and (>= i 0) (<= i 2)) i -1): the chain contains i itself as
        // a branch and an And condition.
        let TermNode::App { args, .. } = ctx.term_node(out[0]).clone() else {
            panic!("eq app");
        };
        let lhs = ctx.children(args).to_vec()[0];
        assert!(is_ite(&ctx, lhs));
        assert!(contains_op(&ctx, lhs, BuiltinOp::And));
    }

    #[test]
    fn indexof_over_cap_literal_left_in_place() {
        let mut ctx = Context::new();
        let big = ctx.mk_string_const(&"a".repeat(65)); // cap is 64
        let a = ctx.mk_string_const("a");
        let int_s = ctx.int_sort();
        let i = {
            let f = ctx.declare_fun("i3", &[], int_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[big, a, i])
            .unwrap();
        let zero = int_lit(&mut ctx, 0);
        let atom = ctx.mk_eq(idx, zero).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert_eq!(out, vec![atom], "over-cap must survive unchanged (→ fence)");
        // At exactly the cap it rewrites.
        let at_cap = ctx.mk_string_const(&"a".repeat(64));
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[at_cap, a, i])
            .unwrap();
        let atom = ctx.mk_eq(idx, zero).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(!contains_op(&ctx, out[0], BuiltinOp::StrIndexOf));
    }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str indexof_replace`
Expected: `indexof_symbolic_start_becomes_ite_chain` and `indexof_empty_needle_symbolic_start_is_range_ite` FAIL (symbolic `i` currently returns `None`); `indexof_over_cap_literal_left_in_place` half-passes/half-fails (the at-cap arm fails). Prior 9 tests PASS.

- [ ] **Step 3: Implement — extend `rewrite_indexof`**

Add a helper above `rewrite_indexof`:

```rust
fn int_num(ctx: &mut Context, v: i128) -> TermId {
    let int_s = ctx.int_sort();
    ctx.mk_numeral(shinri_core::Rational::from_int(v.into()), int_s)
}
```

Replace `rewrite_indexof`'s trailing `None` with:

```rust
    // Symbolic i, literal haystack+needle: the result as a function of i is a
    // STEP FUNCTION over the concrete occurrence positions o1 < … < ok:
    //   i < 0 → -1;  i ≤ o1 → o1;  o1 < i ≤ o2 → o2;  …;  i > ok → -1
    // (i > |s| needs no own arm: it also has no occurrence ≥ i → -1).
    // Emitted as an Int-ite chain; reduce_assertions' elim_term_ite eliminates
    // it downstream. Capped to bound term growth on adversarial literals.
    if hay.len() > INDEXOF_CHAIN_CAP {
        return None; // over-cap: leave in place → fence
    }
    let i = kids[2];
    let neg1 = int_num(ctx, -1);
    let zero = int_num(ctx, 0);
    if needle.is_empty() {
        // Spec §2.3 special case: (ite (and (>= i 0) (<= i |s|)) i -1).
        let n_lit = int_num(ctx, hay.len() as i128);
        let ge0 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[i, zero])
            .expect("i >= 0");
        let le_n = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[i, n_lit])
            .expect("i <= |s|");
        let in_range = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[ge0, le_n])
            .expect("in_range");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[in_range, i, neg1])
                .expect("empty-needle ite"),
        );
    }
    // Build the chain inside-out (last arm first).
    let mut chain = neg1;
    for &o in occurrences(&hay, &needle).iter().rev() {
        let ov = int_num(ctx, o as i128);
        let cond = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[i, ov])
            .expect("i <= o");
        chain = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[cond, ov, chain])
            .expect("chain ite");
    }
    let lt0 = ctx
        .mk_app(Op::Builtin(BuiltinOp::Lt), &[i, zero])
        .expect("i < 0");
    Some(
        ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[lt0, neg1, chain])
            .expect("outer ite"),
    )
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str indexof_replace`
Expected: 12 PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-str
git commit -m "feat(str): partial-eval str.indexof with symbolic start via bounded ite chain (slice 13)"
```

---

### Task 6: Fence + solver wiring + routing + e2e pins

**Files:**
- Modify: `crates/shinri-str/src/indexof_replace.rs` (add fence fn + unit test)
- Modify: `crates/shinri-str/src/reduce.rs:139-150` (`contains_string_op` op list)
- Modify: `crates/shinri-solver/src/string_stage.rs:39-53` (`is_string_op` op list)
- Modify: `crates/shinri-solver/src/lib.rs:414-417` (pipeline insertion)
- Test: `crates/shinri-solver/tests/script_e2e.rs` (after `str_prefixof_positive_decides`-family tests, i.e. after the slice-12 block ending ~:630)

**Interfaces:**
- Consumes: `partial_eval_indexof_replace` (Task 3-5); solver seam at lib.rs:414 (`fold_str_predicates` call).
- Produces: `pub fn has_unreduced_indexof_replace(ctx: &Context, assertions: &[TermId]) -> bool` in `shinri_str::indexof_replace`; end-to-end behavior Tasks 7-8 rely on.

- [ ] **Step 1: Write the failing tests**

Unit test (append in `indexof_replace.rs` tests):

```rust
    #[test]
    fn fence_predicate_classification() {
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "sf");
        let b = ctx.mk_string_const("b");
        let zero = int_lit(&mut ctx, 0);
        let one = int_lit(&mut ctx, 1);
        // Symbolic haystack survives the rewrite → fence.
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[s, b, zero])
            .unwrap();
        let atom = ctx.mk_eq(idx, one).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(has_unreduced_indexof_replace(&ctx, &out));
        // Literal haystack folds → no fence.
        let abcb = ctx.mk_string_const("abcb");
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[abcb, b, zero])
            .unwrap();
        let atom = ctx.mk_eq(idx, one).unwrap();
        let out = partial_eval_indexof_replace(&mut ctx, &[atom]);
        assert!(!has_unreduced_indexof_replace(&ctx, &out));
    }
```

E2e tests (append to `crates/shinri-solver/tests/script_e2e.rs` after the slice-12 test block):

```rust
// ── Slice 13: str.indexof / str.replace ──────────────────────────────────────

#[test]
fn str_indexof_replace_literal_folds_decide_any_polarity() {
    // All-literal applications fold to their concrete value at any polarity.
    let out =
        run_script(r#"(set-logic QF_S)(assert (= (str.indexof "abcb" "b" 0) 1))(check-sat)"#);
    assert_eq!(out, vec!["sat"]);
    // From start 2 the next "b" is at 3, not 1 → unsat.
    let out =
        run_script(r#"(set-logic QF_S)(assert (= (str.indexof "abcb" "b" 2) 1))(check-sat)"#);
    assert_eq!(out, vec!["unsat"]);
    // Negated literal replace folds too (polarity-free).
    let out = run_script(
        r#"(set-logic QF_S)(assert (not (= (str.replace "abc" "b" "X") "aXc")))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
    // Empty-needle edges: indexof at i = |s| is IN range; replace prepends.
    let out =
        run_script(r#"(set-logic QF_S)(assert (= (str.indexof "ab" "" 2) 2))(check-sat)"#);
    assert_eq!(out, vec!["sat"]);
    let out = run_script(
        r#"(set-logic QF_S)(assert (= (str.replace "ab" "" "X") "Xab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn str_replace_symbolic_replacement_decides() {
    // (str.replace "abcb" "b" u) → "a" ++ u ++ "cb" (leftmost occurrence @ 1);
    // equated to "aXcb" this forces u = "X" (z3: sat).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun u () String)
           (assert (= (str.replace "abcb" "b" u) "aXcb"))(check-sat)(get-value (u))"#,
    );
    assert_eq!(out.first().map(String::as_str), Some("sat"));
    assert!(
        out.get(1).is_some_and(|v| v.contains("\"X\"")),
        "u must be \"X\", got {out:?}"
    );
    // Length-based UNSAT: |"a" ++ u ++ "cb"| >= 3, but the target has length 2
    // (z3: unsat).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun u () String)
           (assert (= (str.replace "abcb" "b" u) "zz"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn str_indexof_symbolic_start_decides() {
    // (str.indexof "abcb" "b" i) = 3 forces i ∈ {2, 3} → sat (z3: sat).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun i () Int)
           (assert (= (str.indexof "abcb" "b" i) 3))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"]);
    // No start position yields 2 (occurrences are at 1 and 3) → unsat (z3: unsat).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun i () Int)
           (assert (= (str.indexof "abcb" "b" i) 2))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

// ── Fence canaries: flip-markers for a future symbolic-encoding slice ────────

#[test]
fn str_indexof_replace_symbolic_haystack_fences_unknown() {
    // Symbolic haystack (z3: sat) → sound Unknown.
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (= (str.indexof s "b" 0) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun s () String)
           (assert (= (str.replace s "b" "X") "aXc"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
    // Symbolic needle with literal haystack also fences (z3: sat).
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun t () String)
           (assert (= (str.indexof "abc" t 0) 1))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"]);
}

#[test]
fn str_indexof_over_cap_literal_fences_unknown() {
    // 65-char haystack with symbolic i exceeds INDEXOF_CHAIN_CAP = 64 →
    // left in place → sound Unknown (z3: sat).
    let hay = "a".repeat(65);
    let out = run_script(&format!(
        r#"(set-logic QF_S)(declare-fun i () Int)
           (assert (= (str.indexof "{hay}" "a" i) 0))(check-sat)"#
    ));
    assert_eq!(out, vec!["unknown"]);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str fence_predicate_classification`
Expected: COMPILE FAILURE (`has_unreduced_indexof_replace` not found).
Run: `cargo test -p shinri-solver --test script_e2e str_indexof`
Expected: FAIL — without wiring, indexof/replace apps flow into the downstream string machinery unhandled. Note the failure mode (wrong verdict, panic, or unknown) for the commit message; any mode is acceptable pre-wiring.

- [ ] **Step 3: Implement fence + routing + wiring**

Fence, in `indexof_replace.rs` (below `partial_eval_indexof_replace`):

```rust
/// Stage 2: presence fence. True iff any `str.indexof` / `str.replace`
/// application SURVIVED [`partial_eval_indexof_replace`] — symbolic haystack
/// or needle, an over-cap literal, or a non-literal-yet-foldable operand
/// (e.g. a constant substr, which only folds later in `reduce_assertions`).
/// The solver fences such queries to a sound `Unknown` (canary-pinned
/// flip-markers for a future symbolic-encoding slice).
pub fn has_unreduced_indexof_replace(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(
                    op,
                    Op::Builtin(BuiltinOp::StrIndexOf | BuiltinOp::StrReplace)
                ) || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}
```

Routing — `crates/shinri-str/src/reduce.rs`, in `contains_string_op`'s `matches!` list (:141-149), append after `| BuiltinOp::StrContains`:

```rust
                        | BuiltinOp::StrIndexOf
                        | BuiltinOp::StrReplace
```

Routing — `crates/shinri-solver/src/string_stage.rs`, in `is_string_op`'s `matches!` list, append after `| BuiltinOp::StrContains` likewise:

```rust
                | BuiltinOp::StrIndexOf
                | BuiltinOp::StrReplace
```

Wiring — `crates/shinri-solver/src/lib.rs`, insert BETWEEN the `fold_str_predicates` call (:414) and the `has_unrewritable_str_predicate` fence (:415):

```rust
            // ── Slice 13: str.indexof / str.replace ──────────────────────────
            // Polarity-FREE exact rewrites (value-sorted functions, not
            // predicates): fold fully-literal applications; partial-eval
            // literal-haystack shapes (replace → concat decomposition around
            // the concrete leftmost occurrence; indexof with symbolic start →
            // bounded Int-ite chain, eliminated below by reduce_assertions'
            // elim_term_ite). Zero fresh variables. Any SURVIVING application
            // (symbolic haystack/needle, over-cap literal) fences to sound
            // Unknown — canary-pinned flip-markers for a future slice.
            assertions = shinri_str::indexof_replace::partial_eval_indexof_replace(
                &mut self.ctx,
                &assertions,
            );
            if shinri_str::indexof_replace::has_unreduced_indexof_replace(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str indexof_replace && cargo test -p shinri-solver --test script_e2e str_indexof str_replace`
Expected: all PASS (13 unit + 5 e2e). If `str_replace_symbolic_replacement_decides` or `str_indexof_symbolic_start_decides` returns `unknown` instead of a verdict, that is a REAL finding about the decided fragment, not a broken pin: verify the script against z3 by hand (`z3 -smt2 <file>`), then STOP and report — do not weaken the pin to `unknown` without flagging it for review.

- [ ] **Step 5: Run the full existing suites (regression gate)**

Run: `cargo test -p shinri-str -p shinri-solver -p shinri-parser -p shinri-core`
Expected: all green — the wiring must not disturb any existing family.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str crates/shinri-solver
git commit -m "feat(str): fence + solver wiring for indexof/replace, e2e pins + canaries (slice 13)"
```

---

### Task 7: Differential oracle family `qfs_indexof_replace_matches_z3`

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (new Gen methods after `finish_predicates` :309-319; new test after `qfs_predicates_matches_z3` :664)

**Interfaces:**
- Consumes: existing harness — `Lcg`, `Gen` (`var`, `lit`, `atom_term`, `assertion`), `shinri_lines_counting_bailouts`, `z3_verdict`, `parse_string_values`, `z3_with_model`, `Verdict` (all in qfs_differential.rs).
- Produces: the slice's 0-disagreement gate. Seed `0x51_3A_0000_0001` (fresh; never reuse `0x5_1_1A…`/`0x51_2A…`).

- [ ] **Step 1: Write the generator + test**

Add after `finish_predicates` inside `impl Gen`:

```rust
    /// Slice 13: a haystack for the indexof/replace family — literal-heavy
    /// (3 in 4, 2-4 chars) so the fold / partial-eval paths dominate;
    /// occasionally a variable (fence path → shinri-unknown, tolerated).
    fn ir_haystack(&mut self) -> String {
        if self.rng.below(4) == 0 {
            self.var()
        } else {
            let n = 2 + self.rng.below(3); // 2..=4 chars
            let mut s = String::new();
            for _ in 0..n {
                s.push_str(ALPHABET[self.rng.below(ALPHABET.len() as u64) as usize]);
            }
            format!("\"{s}\"")
        }
    }

    /// One indexof/replace assertion. MAY be negated — unlike the predicate
    /// family, the slice-13 rewrites are exact at any polarity. Needle is
    /// always a literal (the decided fragment); the start index is a small
    /// numeral or the symbolic `i0`.
    fn indexof_replace_assertion(&mut self) {
        let hay = self.ir_haystack();
        let needle = self.lit();
        let atom = if self.rng.below(2) == 0 {
            let start = if self.rng.below(3) == 0 {
                "i0".to_owned()
            } else {
                self.rng.below(4).to_string()
            };
            // Result in -1..=3; -1 must be SMT-LIB-spelled (- 1).
            let v = self.rng.below(5) as i64 - 1;
            let v = if v < 0 {
                format!("(- {})", -v)
            } else {
                v.to_string()
            };
            format!("(= (str.indexof {hay} {needle} {start}) {v})")
        } else {
            let u = self.atom_term();
            let target = self.atom_term();
            format!("(= (str.replace {hay} {needle} {u}) {target})")
        };
        let atom = if self.rng.below(4) == 0 {
            format!("(not {atom})")
        } else {
            atom
        };
        self.body.push_str(&format!("(assert {atom})\n"));
    }

    /// Instance body for the slice-13 family: the shared string vars plus an
    /// Int start-index var, 1-2 indexof/replace assertions, 0-1 general
    /// assertions (word eqs / lengths) for cross-theory mixing.
    fn finish_indexof_replace(mut self) -> String {
        self.body.push_str("(declare-fun i0 () Int)\n");
        let np = 1 + self.rng.below(2);
        for _ in 0..np {
            self.indexof_replace_assertion();
        }
        if self.rng.below(2) == 0 {
            self.assertion();
        }
        self.body
    }
```

Add next to `gen_predicates_body` (:385-387):

```rust
fn gen_indexof_replace_body(seed: u64) -> String {
    Gen::new(seed).finish_indexof_replace()
}
```

Add the test after `qfs_predicates_matches_z3` (structure intentionally mirrors it — tolerant unknown/bailout counting, witness check, 0-disagreement gate):

```rust
// ─────────────────────────────────────────────────────────────────────────────
// indexof/replace differential oracle (slice 13): fold + partial-eval + fence.
// Rewrites are polarity-free, so atoms MAY be negated (unlike the predicate
// family). Symbolic-haystack instances fence to sound Unknown (tolerated,
// counted). Guard bailouts: same tolerated slice-11 retraction-leak class as
// the predicate family (the mixing `assertion()` emits word equations).
// ─────────────────────────────────────────────────────────────────────────────

const IR_N_ITERS: usize = 200;
const IR_MAX_GUARD_BAILOUTS: usize = IR_N_ITERS / 10;

#[test]
fn qfs_indexof_replace_matches_z3() {
    let mut rng = Lcg(0x51_3A_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness, mut n_guard_bailout) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..IR_N_ITERS {
        let seed = rng.next();
        let body = gen_indexof_replace_body(seed);

        let (lines, bailouts) = shinri_lines_counting_bailouts(&format!("{body}(check-sat)\n"));
        if bailouts > 0 {
            n_guard_bailout += 1;
            continue; // sound bail-to-unknown: tolerated, counted
        }
        let ours = match lines.first().map(String::as_str) {
            Some("sat") => Verdict::Sat,
            Some("unsat") => Verdict::Unsat,
            _ => Verdict::Unknown,
        };
        if ours == Verdict::Unknown {
            n_unknown += 1; // sound fence/fuel: tolerated, counted
            continue;
        }
        let theirs = z3_verdict(&format!("{body}(check-sat)\n"));
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S INDEXOF/REPLACE SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
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
                let (lines, _bailouts) = shinri_lines_counting_bailouts(&get);
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
        "qfs_indexof_replace_matches_z3: {IR_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown (tolerated) / {n_z3skip} z3-unknown / \
         {n_guard_bailout} guard-bailout (tolerated); {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "indexof/replace family produced zero SAT instances");
    assert!(
        n_unsat > 0,
        "indexof/replace family produced zero UNSAT instances"
    );
    assert!(
        n_witness > 0,
        "no witnesses checked — model path not exercised"
    );
    assert!(
        n_guard_bailout <= IR_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailout} exceed bound {IR_MAX_GUARD_BAILOUTS} — \
         investigate, do not raise the bound blindly"
    );
}
```

- [ ] **Step 2: Run the new family**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential qfs_indexof_replace_matches_z3 -- --nocapture`
(z3 must be on PATH; if not: `mise exec -- cargo test …`.)
Expected: PASS with a printed stats line: nonzero sat AND unsat AND witnesses, 0 disagreements. Known contingency: if z3 rejects `(declare-fun i0 () Int)` under `(set-logic QF_S)`, the fix is to make `finish_indexof_replace` override the body's first line to `(set-logic QF_SLIA)` — do this by having it emit a fully fresh header (replace `self.body` before appending): still declaring `s0..s2`, then `i0`. Do NOT touch `Gen::new` (the other families' bodies must stay byte-identical).

- [ ] **Step 3: Run the pre-existing oracle families (no-perturbation gate)**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture`
Expected: `qfs_matches_z3`, `qfs_predicates_matches_z3`, targeted cases, and the new family ALL pass with their usual stats (the existing families' streams are untouched — their seeds and generators did not change).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_indexof_replace_matches_z3 differential oracle family (slice 13)"
```

---

### Task 8: Full verification + spec truth-up

**Files:**
- Modify: `docs/superpowers/specs/2026-07-10-shinri-slice13-str-indexof-replace-design.md` (Status line)

**Interfaces:**
- Consumes: everything above.
- Produces: the slice's completion evidence.

- [ ] **Step 1: Format + lint**

Run: `cargo fmt --all`
Run: `cargo clippy --workspace --all-targets`
Expected: no diff beyond formatting; zero clippy warnings. Fix anything surfaced, rerun until clean.

- [ ] **Step 2: Full test sweep**

Run: `cargo test --workspace`
Expected: all green.
Run: `cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture`
Expected: all families green, 0 disagreements.

- [ ] **Step 3: Truth-up the spec status**

Edit the spec's `Status:` line from `APPROVED DESIGN (pre-implementation)` to `IMPLEMENTED (slice 13 landed <date>)` and append one sentence with the observed oracle stats (sat/unsat/unknown counts from the Step 2 `--nocapture` output), following the slice-12 spec's Status style. If any design detail changed during implementation (e.g. the QF_SLIA header contingency in Task 7), record the delta in the Status paragraph.

- [ ] **Step 4: Final commit**

```bash
git add -A
git commit -m "docs: slice-13 spec truth-up — status IMPLEMENTED + oracle stats (slice 13)"
```

---

## Self-Review (completed at plan time)

1. **Spec coverage:** Surface changes → Tasks 1-2; §2.1 fold → Task 3; §2.2 replace partial-eval → Task 4; §2.3 indexof chain + cap → Task 5; §2.4/fence + §3 wiring + e2e pins/canaries → Task 6; §4 oracle family → Task 7; Verification section → Task 8. Non-goals: nothing in any task touches replace_all/regex, predicates, substr fences, wordeq, or existing seeds.
2. **Placeholder scan:** none — every code step is complete code; the two contingencies (exhaustive-match fixups in Task 1, QF_SLIA header in Task 7) specify the exact action, not "handle appropriately".
3. **Type consistency:** `partial_eval_indexof_replace(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>` and `has_unreduced_indexof_replace(ctx: &Context, assertions: &[TermId]) -> bool` are used with identical signatures in Tasks 3, 6 (unit + wiring); `occurrences(&[char], &[char]) -> Vec<usize>` consistent across Tasks 3-5; `INDEXOF_CHAIN_CAP = 64` consistent between Task 3 (definition), Task 5 (use + boundary test), Task 6 (65-char canary).
