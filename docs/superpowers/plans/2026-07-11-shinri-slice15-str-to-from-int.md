# Slice 15 — str.to_int / str.from_int Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit `str.to_int` and `str.from_int` (today parser `unknown operator`) via constant-fold + the one exact composition rewrite (`str.to_int(str.from_int(n)) → ite(n≥0, n, -1)`) + a sound presence fence to `Unknown` for every other symbolic occurrence.

**Architecture:** Two value-sorted `BuiltinOp` variants (`String→Int`, `Int→String`), parsed/printed like the slice-13/14 ops, handled by a new bottom-up memoized pre-pass module `shinri-str/src/int_conv.rs` that mirrors `indexof_replace.rs`. The solver's string path runs the pass then fences any survivor. The roundtrip's Int-sorted `ite` is eliminated by the existing `reduce_assertions`/`elim_term_ite` seam — zero new model or get-value surface.

**Tech Stack:** Rust workspace (crates `shinri-core`, `shinri-parser`, `shinri-str`, `shinri-solver`); `cargo nextest`; differential oracle vs `z3` under `#[cfg(feature = "oracle")]`.

**Spec:** `docs/superpowers/specs/2026-07-11-shinri-slice15-str-to-from-int-design.md`

## Global Constraints

- **SMT-LIB 2.6 semantics — `str.to_int`:** returns the numeric value **iff** the string is a **non-empty sequence of ASCII digits U+0030–U+0039** (leading zeros allowed: `"007"→7`); **`-1`** for empty, any non-digit char, sign chars (`"-5"→-1`), whitespace, or any **non-ASCII** Unicode digit (`٣`, `３` → -1). Arbitrary precision — no i64/i128 overflow.
- **SMT-LIB 2.6 semantics — `str.from_int`:** `n≥0` → canonical decimal, no leading zeros (`0→"0"`); `n<0` → the **empty string** `""` (not `"-1"`, not a sign string).
- **Digit classification MUST be `char::is_ascii_digit()`** (exactly `'0'..='9'`), never `char::is_numeric()` — R1, the unsoundness trap.
- **Only the `to_int(from_int(n))` nesting may be rewritten** — the reverse `from_int(to_int(s))` is NOT identity (leading zeros) — R3.
- Structural-sharing convention: unchanged subterms keep their `TermId`.
- House gates: `cargo fmt --all --check` clean (CI fmt gate — run locally pre-push), clippy clean.
- New oracle family gets a **fresh seed**; existing families' seeds are **never perturbed**.

---

### Task 1: Core ops + sort rules (`shinri-core`)

**Files:**
- Modify: `crates/shinri-core/src/term.rs:98` (after `StrReplaceAll`)
- Modify: `crates/shinri-core/src/context.rs:526` (after the `StrReplace | StrReplaceAll` sort arm)
- Test: `crates/shinri-core/src/context.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Produces: `BuiltinOp::StrToInt` (sort `String → Int`), `BuiltinOp::StrFromInt` (sort `Int → String`).

- [ ] **Step 1: Write the failing test** — append to the tests module in `crates/shinri-core/src/context.rs`:

```rust
#[test]
fn str_to_from_int_sort_rules() {
    // A nullary uninterpreted constant of the given sort (there is no
    // `mk_const`; this is the codebase pattern — see indexof_replace tests).
    fn nullary(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let int_s = ctx.int_sort();
    let s = nullary(&mut ctx, "s", str_s);
    let n = nullary(&mut ctx, "n", int_s);

    // str.to_int : String -> Int
    let ti = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrToInt), &[s])
        .expect("to_int well-sorted");
    assert_eq!(ctx.sort_of(ti), int_s);

    // str.from_int : Int -> String
    let fi = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrFromInt), &[n])
        .expect("from_int well-sorted");
    assert_eq!(ctx.sort_of(fi), str_s);

    // Wrong sorts rejected.
    assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrToInt), &[n]).is_err());
    assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrFromInt), &[s]).is_err());
    // Wrong arity rejected.
    assert!(ctx.mk_app(Op::Builtin(BuiltinOp::StrToInt), &[s, s]).is_err());
}
```

> `Op`, `BuiltinOp`, `Context`, `TermId`, `SortId` must be in scope in the core test module — add `use` lines if the surrounding `#[cfg(test)] mod` does not already glob them.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo build -p shinri-core 2>&1 | head`
Expected: FAIL — `no variant named StrToInt` (and `StrFromInt`).

- [ ] **Step 3: Add the enum variants** — in `crates/shinri-core/src/term.rs`, immediately after the `StrReplaceAll` line (`:98`):

```rust
    // Slice 15: string <-> integer conversions (SMT-LIB 2.6).
    StrToInt,   // String -> Int
    StrFromInt, // Int -> String
```

- [ ] **Step 4: Add the sort rules** — in `crates/shinri-core/src/context.rs`, immediately after the `StrReplace | StrReplaceAll => { … }` arm (ends `:526`):

```rust
            StrToInt => {
                expect_arity(args, 1)?;
                let (str_s, int_s) = (self.string_sort(), self.int_sort());
                if self.sort_of(args[0]) != str_s {
                    return Err(SortError::Mismatch {
                        expected: str_s,
                        found: self.sort_of(args[0]),
                    });
                }
                Ok(int_s)
            }
            StrFromInt => {
                expect_arity(args, 1)?;
                let (str_s, int_s) = (self.string_sort(), self.int_sort());
                if self.sort_of(args[0]) != int_s {
                    return Err(SortError::Mismatch {
                        expected: int_s,
                        found: self.sort_of(args[0]),
                    });
                }
                Ok(str_s)
            }
```

- [ ] **Step 5: Build & fix any other exhaustive `BuiltinOp` match in `shinri-core`**

Run: `cargo build -p shinri-core 2>&1 | head -30`
Expected: builds clean. If the compiler flags a non-exhaustive `match` over `BuiltinOp` anywhere else in the crate, add a minimal arm consistent with the neighboring `Str*` ops (these two ops carry no payload, so any `_ =>`/list-style arm extends naturally).

- [ ] **Step 6: Run the test to verify it passes**

Run: `cargo nextest run -p shinri-core str_to_from_int_sort_rules`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-core/src/term.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): StrToInt/StrFromInt ops + sort rules (slice 15)"
```

---

### Task 2: Parser + printer (`shinri-parser`)

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs:330` (keyword table) and `:897` (builtin dispatch arm)
- Modify: `crates/shinri-parser/src/print.rs:200` (op-name table)
- Test: `crates/shinri-parser/src/parser.rs` and `print.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Consumes: `BuiltinOp::StrToInt`, `BuiltinOp::StrFromInt` (Task 1).
- Produces: parses `str.to_int` / `str.from_int`; `print_term` round-trips them to those exact names.

- [ ] **Step 1: Write the failing parser test** — append to the tests module in `crates/shinri-parser/src/parser.rs` (model on `parse_indexof_replace`):

```rust
/// Parse str.to_int / str.from_int, verify op + result sort (slice 15).
/// Mirrors `parses_indexof_and_replace` (uses the same `parse_all_ok` helper).
#[test]
fn parses_to_int_and_from_int() {
    use shinri_core::{BuiltinOp, Op, TermNode};
    let src = r#"(declare-fun s () String)
(declare-fun n () Int)
(assert (= (str.to_int s) 5))
(assert (= (str.from_int n) "12"))"#;
    let (ctx, cmds) = parse_all_ok(src);
    assert_eq!(cmds.len(), 4); // 2 declares + 2 asserts
    for (ci, want, want_sort) in [
        (2usize, BuiltinOp::StrToInt, ctx.int_sort()),
        (3usize, BuiltinOp::StrFromInt, ctx.string_sort()),
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
        let lhs = ctx.children(args).to_vec()[0];
        match ctx.term_node(lhs).clone() {
            TermNode::App { op: Op::Builtin(got), .. } => assert_eq!(got, want, "op mismatch"),
            other => panic!("expected App lhs, got {other:?}"),
        }
        assert_eq!(ctx.sort_of(lhs), want_sort, "result sort for {want:?}");
    }
}

/// Ill-sorted operands are diagnostics, not crashes (mirror of the slice-13 test).
#[test]
fn to_from_int_wrong_sort_rejected() {
    // str.to_int arg must be String.
    let cs = commands(r#"(declare-fun n () Int)(assert (= (str.to_int n) 0))"#);
    assert!(cs[1].is_err(), "Int arg to str.to_int must be a diagnostic");
    // str.from_int arg must be Int.
    let cs = commands(r#"(declare-fun s () String)(assert (= (str.from_int s) s))"#);
    assert!(cs[1].is_err(), "String arg to str.from_int must be a diagnostic");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo build -p shinri-parser 2>&1 | head`
Expected: FAIL — `str.to_int` parses to `unknown operator` (or the keyword arm is missing).

- [ ] **Step 3: Add keyword-table entries** — in `crates/shinri-parser/src/parser.rs`, after the `"str.replace_all" => StrReplaceAll,` line (`:330`):

```rust
            "str.to_int" => StrToInt,
            "str.from_int" => StrFromInt,
```

- [ ] **Step 4: Add the builtin dispatch arm** — in `crates/shinri-parser/src/parser.rs`, extend the `Str*` delegate arm ending at `:897` so it reads:

```rust
            BuiltinOp::StrPrefixOf
            | BuiltinOp::StrSuffixOf
            | BuiltinOp::StrContains
            | BuiltinOp::StrIndexOf
            | BuiltinOp::StrReplace
            | BuiltinOp::StrReplaceAll
            | BuiltinOp::StrToInt
            | BuiltinOp::StrFromInt => Self::mk(ctx, Op::Builtin(op), &args, &sp),
```

- [ ] **Step 5: Add printer entries** — in `crates/shinri-parser/src/print.rs`, after the `StrReplaceAll => "str.replace_all".to_owned(),` line (`:200`):

```rust
        StrToInt => "str.to_int".to_owned(),
        StrFromInt => "str.from_int".to_owned(),
```

- [ ] **Step 6: Write the failing printer round-trip test** — append to the tests module in `crates/shinri-parser/src/print.rs` (model on the `StrReplaceAll` print test at `:288`):

```rust
#[test]
fn print_to_from_int_roundtrip() {
    let mut ctx = Context::new();
    let str_s = ctx.string_sort();
    let int_s = ctx.int_sort();
    let s = ctx.mk_const("s", str_s);
    let n = ctx.mk_const("n", int_s);
    let ti = ctx.mk_app(Op::Builtin(BuiltinOp::StrToInt), &[s]).unwrap();
    assert_eq!(print_term(&ctx, ti), "(str.to_int s)");
    let fi = ctx.mk_app(Op::Builtin(BuiltinOp::StrFromInt), &[n]).unwrap();
    assert_eq!(print_term(&ctx, fi), "(str.from_int n)");
}
```

> Use the same `Context`/const constructor the neighboring print tests use.

- [ ] **Step 7: Build & fix any other exhaustive `BuiltinOp` match in `shinri-parser`**

Run: `cargo build -p shinri-parser 2>&1 | head -30`
Expected: builds clean (the op-name table in `print.rs` is the only exhaustive one; if another surfaces, add the two ops).

- [ ] **Step 8: Run the tests to verify they pass**

Run: `cargo nextest run -p shinri-parser parses_to_int_and_from_int to_from_int_wrong_sort_rejected print_to_from_int_roundtrip`
Expected: PASS.

- [ ] **Step 9: Commit**

```bash
git add crates/shinri-parser/src/parser.rs crates/shinri-parser/src/print.rs
git commit -m "feat(parser): parse + print str.to_int / str.from_int (slice 15)"
```

---

### Task 3: Fold pre-pass module (`shinri-str/src/int_conv.rs`)

**Files:**
- Create: `crates/shinri-str/src/int_conv.rs`
- Modify: `crates/shinri-str/src/lib.rs:3` (add `pub mod int_conv;`)
- Test: `crates/shinri-str/src/int_conv.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Consumes: `BuiltinOp::StrToInt` / `StrFromInt` (Task 1); `Context::{string_const_value, numeral_value, mk_string_const, mk_numeral}`; `shinri_core::{Integer, Rational}`.
- Produces:
  - `pub fn partial_eval_int_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>`
  - `pub fn has_unreduced_int_conv(ctx: &Context, assertions: &[TermId]) -> bool`
  - (private) `fn eval_to_int(s: &str) -> Integer`, `fn eval_from_int(n: &Integer) -> String`

- [ ] **Step 1: Write the failing test** — create `crates/shinri-str/src/int_conv.rs` with only the evaluators' test first (fold rewrite added after evaluators compile):

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

    #[test]
    fn eval_to_int_pinned_semantics() {
        assert_eq!(eval_to_int("0"), Integer::from(0i128));
        assert_eq!(eval_to_int("007"), Integer::from(7i128)); // leading zeros ok
        assert_eq!(eval_to_int("42"), Integer::from(42i128));
        assert_eq!(eval_to_int(""), Integer::from(-1i128)); // empty
        assert_eq!(eval_to_int("12a"), Integer::from(-1i128)); // non-digit
        assert_eq!(eval_to_int("-5"), Integer::from(-1i128)); // sign char
        assert_eq!(eval_to_int("+5"), Integer::from(-1i128));
        assert_eq!(eval_to_int(" 5"), Integer::from(-1i128)); // whitespace
        // NON-ASCII digit trap: must be -1, NOT 3.
        assert_eq!(eval_to_int("\u{0663}"), Integer::from(-1i128)); // Arabic-Indic ٣
        assert_eq!(eval_to_int("\u{FF13}"), Integer::from(-1i128)); // fullwidth ３
        // Big int (no i128 overflow): 40-digit roundtrip.
        let big = "1234567890123456789012345678901234567890";
        assert_eq!(eval_to_int(big).to_string(), big);
    }

    #[test]
    fn eval_from_int_pinned_semantics() {
        assert_eq!(eval_from_int(&Integer::from(0i128)), "0");
        assert_eq!(eval_from_int(&Integer::from(42i128)), "42");
        assert_eq!(eval_from_int(&Integer::from(-1i128)), ""); // negative -> ""
        assert_eq!(eval_from_int(&Integer::from(-5i128)), "");
    }
}
```

- [ ] **Step 2: Write the evaluators + module header** — put this above the tests module in `crates/shinri-str/src/int_conv.rs`:

```rust
//! Slice 15 pre-pass: `str.to_int` / `str.from_int` — fold + exact roundtrip
//! rewrite + fence.
//!
//! Both ops are value-sorted FUNCTIONS (Int / String), so — like the slice-13
//! indexof/replace ops — the rewrites are exact at any position and polarity;
//! zero fresh variables are introduced here (the only fresh var is the `!ite`
//! that `reduce_assertions`' `elim_term_ite` mints for the roundtrip below).
//!
//! Stages (run by the solver's string-path seam):
//! 1. [`partial_eval_int_conv`] — bottom-up memoized rewrite:
//!    - fold `str.to_int(<lit>)` / `str.from_int(<numeral>)` to a literal;
//!    - rewrite `str.to_int(str.from_int(n))` → `ite(n >= 0, n, -1)` (exact).
//! 2. [`has_unreduced_int_conv`] — presence fence: any surviving application
//!    (symbolic string to `to_int`; symbolic non-roundtrip Int to `from_int`)
//!    fences the query to a sound `Unknown`.
//!
//! Strings are handled as code points; digit classification is EXACTLY
//! `char::is_ascii_digit()` (`'0'..='9'`) — never `char::is_numeric()`, which
//! would unsoundly fold non-ASCII Unicode digits.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Integer, Op, Rational, TermId, TermNode};

/// Concrete `str.to_int(s)` per SMT-LIB 2.6: the value of `s` iff it is a
/// non-empty run of ASCII digits (leading zeros allowed); otherwise `-1`.
fn eval_to_int(s: &str) -> Integer {
    if s.is_empty() || !s.chars().all(|c| c.is_ascii_digit()) {
        return Integer::from(-1i128);
    }
    Integer::from_str_radix(s, 10).expect("validated ASCII-digit run parses")
}

/// Concrete `str.from_int(n)` per SMT-LIB 2.6: canonical decimal for `n >= 0`
/// (no leading zeros, `0 -> "0"`); the empty string for `n < 0`.
fn eval_from_int(n: &Integer) -> String {
    if n.signum() < 0 {
        String::new()
    } else {
        n.to_string()
    }
}
```

- [ ] **Step 3: Register the module** — in `crates/shinri-str/src/lib.rs`, after `pub mod indexof_replace;` (`:3`):

```rust
pub mod int_conv;
```

- [ ] **Step 4: Run the evaluator tests to verify they pass**

Run: `cargo nextest run -p shinri-str eval_to_int_pinned_semantics eval_from_int_pinned_semantics`
Expected: PASS. (If `Integer::from_str_radix`/`signum`/`Display` names differ, reconcile against `crates/shinri-num/src/integer.rs`.)

- [ ] **Step 5: Write the failing fold + fence test** — append to the tests module:

```rust
    fn to_int(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToInt), &[s]).unwrap()
    }
    fn from_int(ctx: &mut Context, n: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrFromInt), &[n]).unwrap()
    }

    #[test]
    fn fold_literal_applications() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        // str.to_int("42") folds to the numeral 42.
        let lit = ctx.mk_string_const("42");
        let app = to_int(&mut ctx, lit);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(
            ctx.numeral_value(out[0]).map(|r| r.to_string()),
            Some("42".to_string())
        );
        // str.from_int(-5) folds to "".
        let neg = ctx.mk_numeral(Rational::from_int(Integer::from(-5i128)), int_s);
        let app = from_int(&mut ctx, neg);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(ctx.string_const_value(out[0]), Some(""));
        // No survivor -> not fenced.
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn symbolic_application_survives_to_fence() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s); // symbolic string
        let app = to_int(&mut ctx, s);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert!(has_unreduced_int_conv(&ctx, &out), "symbolic to_int must fence");
    }
```

- [ ] **Step 6: Run to verify it fails**

Run: `cargo build -p shinri-str 2>&1 | head`
Expected: FAIL — `partial_eval_int_conv` / `has_unreduced_int_conv` not found.

- [ ] **Step 7: Implement the fold rewrite + fence** — add above the tests module (structure copied from `indexof_replace.rs`; the roundtrip case is a stub returning `None` here, filled in Task 4):

```rust
/// Stage 1: bottom-up memoized rewrite. Folds fully-literal applications;
/// the roundtrip case is added in Task 4. Untouched subtrees keep their TermIds.
pub fn partial_eval_int_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions.iter().map(|&a| rewrite(ctx, a, &mut memo)).collect()
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
                Op::Builtin(BuiltinOp::StrToInt) => rewrite_to_int(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrFromInt) => rewrite_from_int(ctx, &new_children),
                _ => None,
            };
            if let Some(r) = special {
                r
            } else {
                let changed = new_children.iter().zip(children.iter()).any(|(n, o)| n != o);
                if changed {
                    ctx.mk_app(op, &new_children).expect("rewrite: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// `(str.to_int x)`, child already rewritten. Folds a literal argument; the
/// roundtrip `str.to_int(str.from_int(n))` case is added in Task 4. None leaves
/// the app in place (-> fence).
fn rewrite_to_int(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    if let Some(s) = ctx.string_const_value(kids[0]).map(str::to_owned) {
        let int_s = ctx.int_sort();
        return Some(ctx.mk_numeral(Rational::from_int(eval_to_int(&s)), int_s));
    }
    None
}

/// `(str.from_int x)`, child already rewritten. Folds a numeral argument.
/// None (symbolic Int) leaves the app in place (-> fence).
fn rewrite_from_int(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let r = ctx.numeral_value(kids[0])?.clone();
    Some(ctx.mk_string_const(&eval_from_int(&r.numer())))
}

/// Stage 2: presence fence. True iff any `str.to_int` / `str.from_int`
/// application SURVIVED [`partial_eval_int_conv`].
pub fn has_unreduced_int_conv(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(BuiltinOp::StrToInt | BuiltinOp::StrFromInt))
                    || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}
```

> `Rational::numer()` returns the integer part; the arg is Int-sorted so it is always integer-valued. If `numer()` returns by value vs ref, adjust the `&r.numer()` borrow accordingly.

- [ ] **Step 8: Run to verify pass**

Run: `cargo nextest run -p shinri-str fold_literal_applications symbolic_application_survives_to_fence eval_to_int_pinned_semantics eval_from_int_pinned_semantics`
Expected: PASS.

- [ ] **Step 9: Commit**

```bash
git add crates/shinri-str/src/int_conv.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): int_conv pre-pass — fold str.to_int/from_int + fence (slice 15)"
```

---

### Task 4: Exact roundtrip rewrite `to_int(from_int(n)) → ite(n≥0, n, -1)`

**Files:**
- Modify: `crates/shinri-str/src/int_conv.rs` (`rewrite_to_int`)
- Test: `crates/shinri-str/src/int_conv.rs` (inline)

**Interfaces:**
- Consumes: `rewrite_to_int` (Task 3), `BuiltinOp::{Ge, Ite}`.
- Produces: `str.to_int(str.from_int(n))` rewrites to an Int-sorted `ite`; the two str ops no longer survive.

- [ ] **Step 1: Write the failing test** — append to the tests module:

```rust
    #[test]
    fn roundtrip_to_int_of_from_int_rewrites_to_ite() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s); // symbolic Int (helper from Task 3)
        let inner = from_int(&mut ctx, n);
        let app = to_int(&mut ctx, inner);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        // Neither str op survives -> not fenced.
        assert!(!has_unreduced_int_conv(&ctx, &out), "roundtrip must fully eliminate both ops");
        // Top node is an Int-sorted ite.
        match ctx.term_node(out[0]) {
            TermNode::App { op, .. } => {
                assert_eq!(*op, Op::Builtin(BuiltinOp::Ite), "expected ite, got {op:?}");
            }
            other => panic!("expected ite app, got {other:?}"),
        }
        assert_eq!(ctx.sort_of(out[0]), int_s);
    }

    #[test]
    fn nested_literal_roundtrip_folds_through() {
        // str.to_int(str.from_int(42)) : from_int folds to "42", then to_int folds to 42.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let k = ctx.mk_numeral(Rational::from_int(Integer::from(42i128)), int_s);
        let inner = from_int(&mut ctx, k); // split: avoid double &mut ctx in one expr
        let app = to_int(&mut ctx, inner);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(ctx.numeral_value(out[0]).map(|r| r.to_string()), Some("42".to_string()));
    }
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo nextest run -p shinri-str roundtrip_to_int_of_from_int_rewrites_to_ite`
Expected: FAIL — currently the symbolic `from_int(n)` survives, so `has_unreduced_int_conv` is `true` and the top node is `StrToInt`, not `Ite`.

- [ ] **Step 3: Add the roundtrip case to `rewrite_to_int`** — insert before the final `None`, after the literal-fold block:

```rust
    // Exact roundtrip: str.to_int(str.from_int(n)) = ite(n >= 0, n, -1).
    // For n >= 0, from_int yields canonical digits recovered exactly; for n < 0,
    // from_int = "" and to_int("") = -1. Polarity-free, exact.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrFromInt),
        args,
        ..
    } = ctx.term_node(kids[0]).clone()
    {
        let n = ctx.children(args)[0];
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(Rational::from_int(Integer::from(0i128)), int_s);
        let neg1 = ctx.mk_numeral(Rational::from_int(Integer::from(-1i128)), int_s);
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero]).expect("n >= 0");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[ge, n, neg1])
                .expect("roundtrip ite"),
        );
    }
```

- [ ] **Step 4: Run to verify pass**

Run: `cargo nextest run -p shinri-str roundtrip_to_int_of_from_int_rewrites_to_ite nested_literal_roundtrip_folds_through`
Expected: PASS.

- [ ] **Step 5: Run the whole `int_conv` module + fmt**

Run: `cargo nextest run -p shinri-str int_conv && cargo fmt --all --check`
Expected: all PASS, fmt clean.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str/src/int_conv.rs
git commit -m "feat(str): decide str.to_int(str.from_int(n)) roundtrip via ite (slice 15)"
```

---

### Task 5: Solver pipeline wiring + routing + e2e pins

**Files:**
- Modify: `crates/shinri-str/src/reduce.rs:150` (`contains_string_op` match list)
- Modify: `crates/shinri-solver/src/lib.rs:433` (insert after the indexof/replace fence)
- Test: `crates/shinri-solver/tests/qfs_differential.rs` targeted-cases section (`#[test]` fns, no oracle feature needed for these — they use the `expect`/`shinri_verdict` helpers)

**Interfaces:**
- Consumes: `shinri_str::int_conv::{partial_eval_int_conv, has_unreduced_int_conv}` (Tasks 3–4).
- Produces: pure to_int/from_int queries route onto the string path; decided folds/roundtrips return sat/unsat; survivors return `Unknown`.

- [ ] **Step 1: Write the failing e2e tests** — append to the targeted-cases section of `crates/shinri-solver/tests/qfs_differential.rs` (near the other `targeted_*` `#[test]`s). These use the existing `expect` helper (cross-checks z3) for decided cases and `shinri_verdict` for the fence canary:

```rust
#[test]
fn targeted_to_int_fold_decided() {
    // str.to_int("42") = 42 -> SAT ; = 5 -> UNSAT.
    expect(
        "(set-logic QF_S)(assert (= (str.to_int \"42\") 42))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(assert (= (str.to_int \"42\") 5))(check-sat)",
        Verdict::Unsat,
    );
    // Non-digit / empty -> -1.
    expect(
        "(set-logic QF_S)(assert (= (str.to_int \"a1\") (- 1)))(check-sat)",
        Verdict::Sat,
    );
}

#[test]
fn targeted_from_int_fold_decided() {
    // str.from_int(0) = "0" -> SAT ; negative -> "".
    expect(
        "(set-logic QF_S)(assert (= (str.from_int 0) \"0\"))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(assert (= (str.from_int (- 5)) \"\"))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(assert (= (str.from_int (- 5)) \"-5\"))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_roundtrip_decided() {
    // to_int(from_int(n)) = ite(n>=0,n,-1): reachable at 5 (n=5) -> SAT;
    // never -2 -> UNSAT.
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.to_int (str.from_int n)) 5))(check-sat)",
        Verdict::Sat,
    );
    expect(
        "(set-logic QF_S)(declare-fun n () Int)\
         (assert (= (str.to_int (str.from_int n)) (- 2)))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_symbolic_to_from_int_fences_unknown() {
    // Symbolic string to to_int, and symbolic Int to a bare from_int, both fence.
    // Flip-markers: if a future slice decides these, these canaries flip.
    assert_eq!(
        shinri_verdict("(set-logic QF_S)(declare-fun s () String)\
                        (assert (= (str.to_int s) 5))(check-sat)"),
        Verdict::Unknown,
    );
    assert_eq!(
        shinri_verdict("(set-logic QF_S)(declare-fun n () Int)\
                        (assert (= (str.from_int n) \"5\"))(check-sat)"),
        Verdict::Unknown,
    );
}
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo nextest run -p shinri-solver targeted_to_int_fold_decided targeted_from_int_fold_decided targeted_roundtrip_decided targeted_symbolic_to_from_int_fences_unknown`
Expected: FAIL — the pass is not wired, so folds are not applied and survivors are not fenced (likely a wrong verdict or a panic on the unhandled op downstream).

- [ ] **Step 3: Add routing** — in `crates/shinri-str/src/reduce.rs`, extend the `contains_string_op` match list (after `BuiltinOp::StrReplace` at `:150`):

```rust
                        | BuiltinOp::StrReplace
                        | BuiltinOp::StrToInt
                        | BuiltinOp::StrFromInt
```

> Keep it inside the existing `matches!(op, Op::Builtin( … ))`. (`StrReplaceAll` may already be absent here; if so leave it — the child-sort check catches those. Add only the two new ops.)

- [ ] **Step 4: Wire the pass into the string path** — in `crates/shinri-solver/src/lib.rs`, immediately after the indexof/replace fence block (after `:433`, before the substr fence comment at `:434`):

```rust
            // ── Slice 15: str.to_int / str.from_int ──────────────────────────
            // Polarity-FREE exact rewrites: fold all-literal applications;
            // rewrite the roundtrip str.to_int(str.from_int(n)) → ite(n≥0,n,-1)
            // (eliminated below by reduce_assertions' elim_term_ite). Any
            // SURVIVING application (symbolic string to str.to_int; symbolic /
            // non-roundtrip Int to str.from_int) fences to sound Unknown —
            // canary-pinned flip-markers for a future digit-bridge slice.
            assertions =
                shinri_str::int_conv::partial_eval_int_conv(&mut self.ctx, &assertions);
            if shinri_str::int_conv::has_unreduced_int_conv(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
```

- [ ] **Step 5: Run to verify pass**

Run: `cargo nextest run -p shinri-solver targeted_to_int_fold_decided targeted_from_int_fold_decided targeted_roundtrip_decided targeted_symbolic_to_from_int_fences_unknown`
Expected: PASS. (If `targeted_roundtrip_decided` returns `Unknown` instead of the pinned verdict, confirm `elim_term_ite` runs on the string path after this insertion — it does, via `reduce_assertions` at `:453` — and that the `Ge`/`Ite` ops are Int-sorted as built.)

- [ ] **Step 6: Regression — existing string suites still green**

Run: `cargo nextest run -p shinri-str -p shinri-solver -p shinri-parser`
Expected: PASS (no existing test perturbed).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-str/src/reduce.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "feat(str): route + wire str.to_int/from_int, e2e pins + fence canaries (slice 15)"
```

---

### Task 6: Differential oracle family `qfs_to_from_int_matches_z3`

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (new `Gen` methods, `gen_*_body`, and the family `#[test]`)

**Interfaces:**
- Consumes: the `Gen`/`Lcg`/`z3_verdict`/`shinri_lines_counting_bailouts`/`z3_with_model`/`parse_string_values` harness (existing).
- Produces: `#[test] fn qfs_to_from_int_matches_z3()` — fresh seed `0x51_5A_0000_0001`, 200 iters, 0-disagreement gate, ≥1 sat, ≥1 unsat, ≥1 witness.

- [ ] **Step 1: Add the generator methods** — in `crates/shinri-solver/tests/qfs_differential.rs`, add to `impl Gen` (after `finish_replace_all`, `:417`):

```rust
    /// A short ASCII-digit literal (0–3 digits, leading zeros allowed) — drives
    /// the to_int fold decided path. Empty and non-digit cases come via `lit()`.
    fn digit_lit(&mut self) -> String {
        let n = self.rng.below(4); // 0..=3 digits (0 -> "", exercises -1)
        let mut s = String::new();
        for _ in 0..n {
            s.push((b'0' + self.rng.below(10) as u8) as char);
        }
        format!("\"{s}\"")
    }

    /// A string term for to_int: mostly a digit literal (fold path), sometimes a
    /// letter literal (`lit()`, folds to -1), sometimes a variable (fence path).
    fn to_int_arg(&mut self) -> String {
        match self.rng.below(4) {
            0 => self.var(),      // symbolic -> fence (tolerated unknown)
            1 => self.lit(),      // letters -> folds to -1
            _ => self.digit_lit(),
        }
    }

    /// One to_int / from_int / roundtrip assertion. MAY be negated (exact at any
    /// polarity). Small Int RHS (incl. `(- 1)` and `(- 2)`) so both sat and
    /// unsat verdicts arise on the decided paths.
    fn to_from_int_assertion(&mut self) {
        let atom = match self.rng.below(3) {
            // to_int(<str>) = k : fold (or fence on a symbolic string arg).
            0 => {
                let arg = self.to_int_arg();
                let k = self.small_int_rhs();
                format!("(= (str.to_int {arg}) {k})")
            }
            // from_int(<int>) = <lit> : fold on a numeral; fence on the Int var.
            1 => {
                let n = if self.rng.below(2) == 0 {
                    "n0".to_owned() // symbolic -> fence
                } else {
                    self.small_int_rhs() // numeral -> fold
                };
                let target = if self.rng.below(2) == 0 { self.digit_lit() } else { self.lit() };
                format!("(= (str.from_int {n}) {target})")
            }
            // roundtrip to_int(from_int(n0)) = k : decided via ite.
            _ => {
                let k = self.small_int_rhs();
                format!("(= (str.to_int (str.from_int n0)) {k})")
            }
        };
        let atom = if self.rng.below(4) == 0 { format!("(not {atom})") } else { atom };
        self.body.push_str(&format!("(assert {atom})\n"));
    }

    /// A small Int literal in -2..=3; negatives SMT-LIB-spelled `(- n)`.
    fn small_int_rhs(&mut self) -> String {
        let v = self.rng.below(6) as i64 - 2; // -2..=3
        if v < 0 { format!("(- {})", -v) } else { v.to_string() }
    }

    /// Instance body for the slice-15 family: shared string vars, an Int var
    /// `n0`, 1–2 conversion assertions, 0–1 general assertions for cross-theory
    /// mixing (so the SAT witness path references string vars).
    fn finish_to_from_int(mut self) -> String {
        self.body.push_str("(declare-fun n0 () Int)\n");
        let np = 1 + self.rng.below(2);
        for _ in 0..np {
            self.to_from_int_assertion();
        }
        if self.rng.below(2) == 0 {
            self.assertion();
        }
        self.body
    }
```

- [ ] **Step 2: Add the body generator** — after `gen_replace_all_body` (`:491`):

```rust
fn gen_to_from_int_body(seed: u64) -> String {
    Gen::new(seed).finish_to_from_int()
}
```

- [ ] **Step 3: Add the family test + constants** — after `qfs_replace_all_matches_z3` (`:964`), copy the slice-14 family verbatim and change ONLY: the constant prefix (`TFI_`), the seed (`0x51_5A_0000_0001`), the generator call (`gen_to_from_int_body`), the disagreement message, and the summary label:

```rust
const TFI_N_ITERS: usize = 200;
const TFI_MAX_GUARD_BAILOUTS: usize = TFI_N_ITERS / 10;

#[test]
fn qfs_to_from_int_matches_z3() {
    let mut rng = Lcg(0x51_5A_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_z3skip, mut n_witness, mut n_guard_bailout) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..TFI_N_ITERS {
        let seed = rng.next();
        let body = gen_to_from_int_body(seed);

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
            "QF_S TO/FROM_INT SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{body}(check-sat)"
        );
        match ours {
            Verdict::Sat => {
                n_sat += 1;
                let get = format!(
                    "{body}(check-sat)\n(get-value ({}))\n",
                    (0..N_VARS).map(|k| format!("s{k}")).collect::<Vec<_>>().join(" ")
                );
                let (lines, _b) = shinri_lines_counting_bailouts(&get);
                if let Some(resp) = lines.get(1) {
                    let model = parse_string_values(resp);
                    if !model.is_empty() {
                        let w = z3_with_model(&body, &model);
                        assert_eq!(
                            w, Verdict::Sat,
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
        "qfs_to_from_int_matches_z3: {TFI_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown (tolerated) / {n_z3skip} z3-unknown / \
         {n_guard_bailout} guard-bailout (tolerated); {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "to/from_int family produced zero SAT instances");
    assert!(n_unsat > 0, "to/from_int family produced zero UNSAT instances");
    assert!(n_witness > 0, "no witnesses checked — model path not exercised");
    assert!(
        n_guard_bailout <= TFI_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailout} exceed bound {TFI_MAX_GUARD_BAILOUTS}"
    );
}
```

- [ ] **Step 4: Run the family under the oracle feature**

Run: `cargo nextest run -p shinri-solver --features oracle qfs_to_from_int_matches_z3 -- --nocapture`
Expected: PASS — prints the sat/unsat/unknown/witness tally, **0 disagreements**, ≥1 sat, ≥1 unsat, ≥1 witness. (Requires `z3` on PATH — mise provides it.)

> If z3 rejects `str.to_int`/`str.from_int` under `(set-logic QF_S)`, switch the family's logic line to `(set-logic QF_SLIA)` in `Gen::new` **only for this generator** — do not touch the shared `Gen::new`; instead post-process `body.replacen("QF_S", "QF_SLIA", 1)` inside `finish_to_from_int`. Re-run.

- [ ] **Step 5: Confirm existing oracle families are unperturbed**

Run: `cargo nextest run -p shinri-solver --features oracle qfs_matches_z3 qfs_predicates_matches_z3 qfs_indexof_replace_matches_z3 qfs_replace_all_matches_z3 -- --nocapture`
Expected: all PASS with their prior tallies (seeds untouched).

- [ ] **Step 6: fmt + clippy + commit**

```bash
cargo fmt --all --check
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_to_from_int_matches_z3 differential oracle family (slice 15)"
```

---

## Final Verification

- [ ] `cargo nextest run -p shinri-core -p shinri-parser -p shinri-str -p shinri-solver` green.
- [ ] `cargo nextest run -p shinri-solver --features oracle` → new family 0 disagreements @ 200 iters; existing families unchanged.
- [ ] `cargo fmt --all --check` clean; `cargo clippy --workspace --all-targets` clean.
- [ ] Spec truth-up: update the design doc's `Status:` line to `IMPLEMENTED` with the oracle tally (sat/unsat/unknown counts) — a separate `docs:` commit, matching the slice-13/14 convention.
