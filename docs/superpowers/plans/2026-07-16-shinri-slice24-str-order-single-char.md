# Slice 24 — single-char `str.< / str.<=` vs constant — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decide `(str.< a b)` / `(str.<= a b)` whenever exactly one side is a length-1 string constant and the other is symbolic, by rewriting each atom to a `str.in_re` membership that the existing regex engine already decides.

**Architecture:** A pure-rewrite extension of slice 23's `order.rs`. Two new match arms in `try_order_atom` (constant-on-right, constant-on-left) build a constant `Rex` from the single character and emit `(str.in_re other <rex>)`. The minted membership flows — with zero new pipeline wiring — into the regex passes that run immediately after `order.rs` in the solver (`lib.rs:493`). A small term-free `range_rex` helper, extracted from slice-22's `range_membership`, single-sources the surrogate/empty-interval endpoint policy.

**Tech Stack:** Rust; crates `shinri-str` (`order.rs`, `regex.rs`, `code_conv.rs`) and `shinri-solver` (differential/e2e tests); z3 4.16.0 on PATH for the oracle.

## Global Constraints

- **Pure rewrite, full equivalence.** Every arm is a two-way equivalence — no fresh variables, no model repair, no polarity tracking. Bottom-up + memoized handles negation/nesting for free.
- **Zero changes to** the word-equation engine, the regex core (`deriv`/`peel`/membership), the arith seam, `Fuel`, or the SAT budgets. This slice edits `order.rs`, adds one helper to `regex.rs`, and refactors one `code_conv.rs` function to delegate.
- **Scope: length-1 string constants only.** Empty-string and literal–literal and reflexive atoms are already decided by slice 23; multi-char constants and two-symbolic-side comparisons stay fenced (banked — spec §5).
- **Surrogate/empty policy is single-sourced** through `regex::range_rex`. A surrogate-interior endpoint ⇒ arm returns `None` ⇒ atom survives to `has_unreduced_str_order` ⇒ sound `Unknown` (provably unreachable for a single char, but retained).
- **Oracle tests** live in `crates/shinri-solver/tests/qfs_differential.rs`, which is entirely `#![cfg(feature = "oracle")]`. They (and the targeted pins) run **only** under `--features oracle`, **foreground with `--nocapture`**. Generated literals are **ASCII-only** (z3-CLI byte-parse artifact, spec §6).
- **CI gates `cargo fmt --check`** — format before every commit; subagents do not auto-format.
- `regex::MAX_CODE` is `u32 = 0x2FFFF`; endpoint arithmetic (`m-1`, `m+1`, `MAX+1`) is done in `i128` and passed to `range_rex(lo: i128, hi: i128)`.

---

### Task 1: `range_rex` shared endpoint helper + `range_membership` delegation

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (add `is_surrogate`, `range_rex`, and a unit test)
- Modify: `crates/shinri-str/src/code_conv.rs:416-429` (refactor `range_membership` to delegate)

**Interfaces:**
- Produces: `pub(crate) fn regex::is_surrogate(k: i128) -> bool`; `pub(crate) fn regex::range_rex(lo: i128, hi: i128) -> Option<Rex>` — `Some(Rex::Empty)` for `lo > hi`, `None` for a surrogate-interior endpoint, else `Some(Rex::Range(lo as u32, hi as u32))`.

- [ ] **Step 1: Write the failing test** — append to the `#[cfg(test)] mod tests` block in `crates/shinri-str/src/regex.rs`:

```rust
#[test]
fn range_rex_endpoint_policy() {
    // Empty interval ⇒ Rex::Empty (the caller's union/concat then drop it).
    assert_eq!(range_rex(0, -1), Some(Rex::Empty));
    assert_eq!(range_rex(98, 97), Some(Rex::Empty));
    // Ordinary in-alphabet range.
    assert_eq!(range_rex(0, 97), Some(Rex::Range(0, 97)));
    assert_eq!(range_rex(97, 97), Some(Rex::Range(97, 97)));
    // Surrogate BLOCK EDGES (0xD800 / 0xDFFF) are expressible via re.diff.
    assert_eq!(range_rex(0, 0xDFFF), Some(Rex::Range(0, 0xDFFF)));
    assert_eq!(range_rex(0xD800, 0xDFFF), Some(Rex::Range(0xD800, 0xDFFF)));
    // An endpoint STRICTLY inside the surrogate block ⇒ None (fence).
    assert_eq!(range_rex(0, 0xDA00), None);
    assert_eq!(range_rex(0xDA00, 0xE000), None);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-str --lib regex::tests::range_rex_endpoint_policy`
Expected: FAIL to compile — `cannot find function range_rex in this scope`.

- [ ] **Step 3: Add the helpers** — in `crates/shinri-str/src/regex.rs`, next to the other `pub(crate)` Rex helpers (e.g. just after `pub(crate) fn star`, around line 146):

```rust
/// True iff `k` is a UTF-16 surrogate code point — in the SMT-LIB alphabet but
/// unrepresentable as a `Box<str>` character.
pub(crate) fn is_surrogate(k: i128) -> bool {
    (0xD800..=0xDFFF).contains(&k)
}

/// A single character class `[lo, hi]` as a `Rex`, applying slice-22's endpoint
/// policy (the term-free core shared with `code_conv::range_membership`):
///   * `lo > hi`  ⇒ `Some(Rex::Empty)` (the empty interval; the caller's
///     `union`/`concat` drop it — see `regex.rs` `concat`/`union`).
///   * an endpoint STRICTLY inside the surrogate block (a surrogate other than
///     the block edges `0xD800` / `0xDFFF`, which ARE expressible) ⇒ `None`.
///   * otherwise ⇒ `Some(Rex::Range(lo as u32, hi as u32))`.
/// Takes `i128` so callers can pass `m-1` / `m+1` / `MAX+1` without under/overflow.
pub(crate) fn range_rex(lo: i128, hi: i128) -> Option<Rex> {
    if lo > hi {
        return Some(Rex::Empty);
    }
    debug_assert!((0..=MAX_CODE as i128).contains(&lo) && (0..=MAX_CODE as i128).contains(&hi));
    if (is_surrogate(lo) && lo != 0xD800) || (is_surrogate(hi) && hi != 0xDFFF) {
        return None;
    }
    Some(Rex::Range(lo as u32, hi as u32))
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-str --lib regex::tests::range_rex_endpoint_policy`
Expected: PASS.

- [ ] **Step 5: Refactor `range_membership` to delegate** — replace the body of `range_membership` in `crates/shinri-str/src/code_conv.rs:416-429` with:

```rust
fn range_membership(ctx: &mut Context, s: TermId, lo: i128, hi: i128) -> Option<TermId> {
    match crate::regex::range_rex(lo, hi)? {
        // Empty interval: the membership is unsatisfiable. Keep emitting the
        // Bool constant `false` (NOT `str.in_re s re.none`) so slice-22's
        // term-exact tests and the downstream shape are unchanged.
        Rex::Empty => Some(ctx.mk_const_bool(false)),
        r => {
            let rt = rex_to_term(ctx, &r);
            Some(
                ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, rt])
                    .expect("str.in_re well-sorted"),
            )
        }
    }
}
```

(`Rex` and `rex_to_term` are already imported at `code_conv.rs:28`. Leave `code_conv::is_surrogate` in place — `char_of_code` still uses it.)

- [ ] **Step 6: Run the slice-22 regression suite to verify delegation preserves output**

Run: `cargo test -p shinri-str --lib code_conv::`
Expected: PASS — all slice-18/22 tests green (they pin `range_membership`'s exact term output; green proves the refactor changed nothing observable).

- [ ] **Step 7: Commit**

```bash
cargo fmt
git add crates/shinri-str/src/regex.rs crates/shinri-str/src/code_conv.rs
git commit -m "refactor(str): extract range_rex endpoint helper; range_membership delegates (slice 24)"
```

---

### Task 2: constant-on-right arms — `(str.< s c)` / `(str.<= s c)`

**Files:**
- Modify: `crates/shinri-str/src/order.rs` (imports; helper fns; one match arm; unit tests)

**Interfaces:**
- Consumes: `regex::range_rex` (Task 1); `regex::{concat, union, star, rex_to_term, Rex, MAX_CODE}`.
- Produces: `fn single_char_code(&str) -> Option<i128>`; `fn sigma_star() -> Rex`; `fn sigma() -> Rex`; `fn membership(&mut Context, TermId, Rex) -> TermId`; `fn order_const_right(&mut Context, s: TermId, m: i128, reflexive: bool) -> Option<TermId>`.

- [ ] **Step 1: Write the failing tests** — append to `crates/shinri-str/src/order.rs`'s `#[cfg(test)] mod tests` block (reuses its existing `str_var` and `order` helpers):

```rust
#[test]
fn single_char_const_right_rewrites() {
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let b = ctx.mk_string_const("b"); // code 98
    // (str.< s "b") ≡ s ∈ Eps ∪ Range(0,'a')·Σ*.
    let lt = order(&mut ctx, BuiltinOp::StrLt, s, b);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    let want_lang = union(vec![
        Rex::Eps,
        concat(vec![Rex::Range(0, 97), star(Rex::Range(0, MAX_CODE))]),
    ]);
    let want = membership(&mut ctx, s, want_lang);
    assert_eq!(out, vec![want]);
    assert!(!has_unreduced_str_order(&ctx, &out));
    // (str.<= s "b") adds the singleton word "b" = Range(98,98).
    let le = order(&mut ctx, BuiltinOp::StrLeq, s, b);
    let out = rewrite_str_order(&mut ctx, &[le]);
    let want_lang = union(vec![
        Rex::Eps,
        concat(vec![Rex::Range(0, 97), star(Rex::Range(0, MAX_CODE))]),
        Rex::Range(98, 98),
    ]);
    let want = membership(&mut ctx, s, want_lang);
    assert_eq!(out, vec![want]);
}

#[test]
fn single_char_const_right_null_char_collapses_to_empty() {
    // (str.< s "\0") (m = 0): Range(0,-1) is empty ⇒ union([Eps, Empty]) = Eps ≡ s = "".
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let nul = ctx.mk_string_const("\u{0}");
    let lt = order(&mut ctx, BuiltinOp::StrLt, s, nul);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    let want = membership(&mut ctx, s, Rex::Eps);
    assert_eq!(out, vec![want]);
    assert!(!has_unreduced_str_order(&ctx, &out));
}

#[test]
fn multi_char_const_right_survives_to_fence() {
    // A length-2 constant is out of scope (banked) ⇒ the atom survives ⇒ fence.
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let bc = ctx.mk_string_const("bc");
    let lt = order(&mut ctx, BuiltinOp::StrLt, s, bc);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    assert_eq!(out, vec![lt]);
    assert!(has_unreduced_str_order(&ctx, &out));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str --lib order::tests::single_char_const_right_rewrites`
Expected: FAIL to compile — `cannot find function membership` / `union` / `concat` in this scope.

- [ ] **Step 3: Add imports** — change the top of `crates/shinri-str/src/order.rs` (line 15-16) from:

```rust
use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
```

to:

```rust
use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

use crate::regex::{concat, range_rex, rex_to_term, star, union, Rex, MAX_CODE};
```

- [ ] **Step 4: Add the shared helpers + `order_const_right`** — in `crates/shinri-str/src/order.rs`, immediately after `try_order_atom` (after its closing brace at line 111):

```rust
/// The single code point of a one-character string; None if empty or multi-char.
fn single_char_code(s: &str) -> Option<i128> {
    let mut it = s.chars();
    match (it.next(), it.next()) {
        (Some(c), None) => Some(c as u32 as i128),
        _ => None,
    }
}

/// Σ* = re.all — any string (including empty).
fn sigma_star() -> Rex {
    star(Rex::Range(0, MAX_CODE))
}

/// Σ = re.allchar — exactly one character.
fn sigma() -> Rex {
    Rex::Range(0, MAX_CODE)
}

/// `(str.in_re other <r>)`.
fn membership(ctx: &mut Context, other: TermId, r: Rex) -> TermId {
    let rt = rex_to_term(ctx, &r);
    ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[other, rt])
        .expect("str.in_re well-sorted")
}

/// `(str.< s c)` / `(str.<= s c)` for a single-character constant `c` (code `m`)
/// and symbolic `s`. `reflexive` = the `<=` case (adds the singleton `s = c`).
///
/// `s <  c` ≡ s ∈ Eps ∪ Range(0, m-1)·Σ*          (empty, or first char < m)
/// `s <= c` ≡ s ∈ Eps ∪ Range(0, m-1)·Σ* ∪ word(c) (… or s = c)
///
/// `m = 0` collapses `Range(0,-1)` to the empty interval, so `s < c` ⇒ `s = ""`.
/// None on a surrogate-interior endpoint (unreachable for a valid char — spec §3).
fn order_const_right(ctx: &mut Context, s: TermId, m: i128, reflexive: bool) -> Option<TermId> {
    let below = concat(vec![range_rex(0, m - 1)?, sigma_star()]);
    let mut branches = vec![Rex::Eps, below];
    if reflexive {
        branches.push(Rex::Range(m as u32, m as u32)); // word(c)
    }
    Some(membership(ctx, s, union(branches)))
}
```

- [ ] **Step 5: Wire the match arm** — in `try_order_atom`, replace the trailing arm (line 109):

```rust
        _ => None,
    }
```

with:

```rust
        // Single-character constant on the RIGHT: (str.< s c) / (str.<= s c).
        (None, Some(y)) => match single_char_code(&y) {
            Some(m) => order_const_right(ctx, a, m, reflexive),
            None => None, // multi-char constant ⇒ banked (spec §5)
        },
        _ => None,
    }
```

(The guarded `(None, Some(y)) if y.is_empty()` arm above still fires first for the empty-string case; this unguarded arm catches non-empty constants. `(Some(x), None)` non-empty and `(None, None)` still fall to `_ => None` until Task 3.)

- [ ] **Step 6: Run tests to verify they pass**

Run: `cargo test -p shinri-str --lib order::`
Expected: PASS — the three new tests plus slice-23's existing `order::` tests.

- [ ] **Step 7: Commit**

```bash
cargo fmt
git add crates/shinri-str/src/order.rs
git commit -m "feat(str): decide single-char (str.< s c) / (str.<= s c) via regex membership (slice 24)"
```

---

### Task 3: constant-on-left arms — `(str.< c s)` / `(str.<= c s)`

**Files:**
- Modify: `crates/shinri-str/src/order.rs` (one helper fn; one match arm; unit tests)

**Interfaces:**
- Consumes: `single_char_code`, `sigma`, `sigma_star`, `membership`, `range_rex` (Task 2).
- Produces: `fn order_const_left(&mut Context, s: TermId, m: i128, reflexive: bool) -> Option<TermId>`.

- [ ] **Step 1: Write the failing tests** — append to `order.rs`'s test module:

```rust
#[test]
fn single_char_const_left_rewrites() {
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let b = ctx.mk_string_const("b"); // code 98
    // (str.< "b" s) ≡ s ∈ Range(99,MAX)·Σ* ∪ "b"·Σ·Σ*.
    let lt = order(&mut ctx, BuiltinOp::StrLt, b, s);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    let want_lang = union(vec![
        concat(vec![Rex::Range(99, MAX_CODE), star(Rex::Range(0, MAX_CODE))]),
        concat(vec![
            Rex::Range(98, 98),
            Rex::Range(0, MAX_CODE),
            star(Rex::Range(0, MAX_CODE)),
        ]),
    ]);
    let want = membership(&mut ctx, s, want_lang);
    assert_eq!(out, vec![want]);
    assert!(!has_unreduced_str_order(&ctx, &out));
    // (str.<= "b" s) ≡ s ∈ Range(99,MAX)·Σ* ∪ "b"·Σ*.
    let le = order(&mut ctx, BuiltinOp::StrLeq, b, s);
    let out = rewrite_str_order(&mut ctx, &[le]);
    let want_lang = union(vec![
        concat(vec![Rex::Range(99, MAX_CODE), star(Rex::Range(0, MAX_CODE))]),
        concat(vec![Rex::Range(98, 98), star(Rex::Range(0, MAX_CODE))]),
    ]);
    let want = membership(&mut ctx, s, want_lang);
    assert_eq!(out, vec![want]);
}

#[test]
fn single_char_const_left_max_char_drops_range_branch() {
    // c = U+2FFFF (greatest char): Range(MAX+1, MAX) empty ⇒ only the prefix branch.
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let mx = ctx.mk_string_const("\u{2FFFF}");
    let lt = order(&mut ctx, BuiltinOp::StrLt, mx, s);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    let want_lang = concat(vec![
        Rex::Range(MAX_CODE, MAX_CODE),
        Rex::Range(0, MAX_CODE),
        star(Rex::Range(0, MAX_CODE)),
    ]);
    let want = membership(&mut ctx, s, want_lang);
    assert_eq!(out, vec![want]);
    assert!(!has_unreduced_str_order(&ctx, &out));
}

#[test]
fn single_char_const_block_edge_does_not_fence() {
    // c = U+E000 (first char above the surrogate block): the endpoint m-1 = 0xDFFF
    // is the block EDGE (expressible) ⇒ must NOT fence (spec §3: guard is
    // provably non-load-bearing for a single char).
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let c = ctx.mk_string_const("\u{E000}"); // code 0xE000
    let lt = order(&mut ctx, BuiltinOp::StrLt, s, c);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    assert!(
        !has_unreduced_str_order(&ctx, &out),
        "block-edge endpoint must not fence"
    );
    let want_lang = union(vec![
        Rex::Eps,
        concat(vec![Rex::Range(0, 0xDFFF), star(Rex::Range(0, MAX_CODE))]),
    ]);
    let want = membership(&mut ctx, s, want_lang);
    assert_eq!(out, vec![want]);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str --lib order::tests::single_char_const_left_rewrites`
Expected: FAIL — `(str.< "b" s)` currently falls to `_ => None` and survives, so `out != vec![want]` (and `has_unreduced_str_order` is true).

- [ ] **Step 3: Add `order_const_left`** — in `order.rs`, after `order_const_right`:

```rust
/// `(str.< c s)` / `(str.<= c s)` for a single-character constant `c` (code `m`)
/// and symbolic `s`. `reflexive` = the `<=` case.
///
/// `c <  s` ≡ s ∈ Range(m+1, MAX)·Σ* ∪ word(c)·Σ·Σ*  (first char > m, or c a
///                                                     PROPER prefix of s)
/// `c <= s` ≡ s ∈ Range(m+1, MAX)·Σ* ∪ word(c)·Σ*     (… or c a prefix incl. = c)
///
/// `m = MAX` collapses `Range(MAX+1, MAX)` to empty, dropping the range branch.
fn order_const_left(ctx: &mut Context, s: TermId, m: i128, reflexive: bool) -> Option<TermId> {
    let above = concat(vec![range_rex(m + 1, MAX_CODE as i128)?, sigma_star()]);
    let word_c = Rex::Range(m as u32, m as u32);
    let prefix = if reflexive {
        concat(vec![word_c, sigma_star()]) // word(c)·Σ*
    } else {
        concat(vec![word_c, sigma(), sigma_star()]) // word(c)·Σ·Σ*
    };
    Some(membership(ctx, s, union(vec![above, prefix])))
}
```

- [ ] **Step 4: Wire the match arm** — in `try_order_atom`, add an unguarded `(Some(x), None)` arm just before `_ => None` (and after the `(None, Some(y))` arm from Task 2):

```rust
        // Single-character constant on the LEFT: (str.< c s) / (str.<= c s).
        (Some(x), None) => match single_char_code(&x) {
            Some(m) => order_const_left(ctx, b, m, reflexive),
            None => None, // multi-char constant ⇒ banked (spec §5)
        },
        _ => None,
    }
```

(The guarded `(Some(x), None) if x.is_empty()` arm above still handles the empty case first. `_ => None` now only catches `(None, None)` — two symbolic sides — the still-fenced hard core.)

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-str --lib order::`
Expected: PASS — all six single-char tests plus slice-23's tests. In particular `symbolic_pair_survives_to_fence` (two free vars) must still fence.

- [ ] **Step 6: Commit**

```bash
cargo fmt
git add crates/shinri-str/src/order.rs
git commit -m "feat(str): decide single-char (str.< c s) / (str.<= c s) via regex membership (slice 24)"
```

---

### Task 4: end-to-end verdict pins (through the solver)

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (add two `#[test]` fns after `targeted_str_order_symbolic_pair_known_gap`, ~line 3682)

**Interfaces:**
- Consumes: the existing `expect(query: &str, want: Verdict)` helper and `Verdict` enum in that file.

- [ ] **Step 1: Write the tests** — insert after `targeted_str_order_symbolic_pair_known_gap` (line 3682):

```rust
#[test]
fn targeted_str_order_single_char_right_decides() {
    // (str.< s "b"): decided end-to-end (was fenced pre-slice-24).
    expect(
        "(set-logic QF_S)(declare-fun s () String)(assert (str.< s \"b\"))(check-sat)",
        Verdict::Sat, // free s (e.g. "a") — now DECIDES rather than fencing
    );
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.< s \"b\"))(assert (= s \"a\"))(check-sat)", Verdict::Sat);
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.< s \"b\"))(assert (= s \"b\"))(check-sat)", Verdict::Unsat);
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.< s \"b\"))(assert (= s \"c\"))(check-sat)", Verdict::Unsat);
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.< s \"b\"))(assert (= s \"\"))(check-sat)", Verdict::Sat);
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.< s \"b\"))(assert (= s \"aa\"))(check-sat)", Verdict::Sat);
    // (str.<= s "b"): s = "b" is now allowed.
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.<= s \"b\"))(assert (= s \"b\"))(check-sat)", Verdict::Sat);
    // Negation: ¬(s < "b") ∧ s = "a" ⇒ unsat.
    expect("(set-logic QF_S)(declare-fun s () String)(assert (not (str.< s \"b\")))(assert (= s \"a\"))(check-sat)", Verdict::Unsat);
}

#[test]
fn targeted_str_order_single_char_left_decides() {
    // (str.< "b" s): first char > 'b', or "b" a proper prefix.
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))(assert (= s \"c\"))(check-sat)", Verdict::Sat);
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))(assert (= s \"ba\"))(check-sat)", Verdict::Sat);
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))(assert (= s \"b\"))(check-sat)", Verdict::Unsat);
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.< \"b\" s))(assert (= s \"a\"))(check-sat)", Verdict::Unsat);
    // (str.<= "b" s): s = "b" is now allowed.
    expect("(set-logic QF_S)(declare-fun s () String)(assert (str.<= \"b\" s))(assert (= s \"b\"))(check-sat)", Verdict::Sat);
}
```

- [ ] **Step 2: Run to verify they pass** (the file is oracle-gated; `expect` does not call z3, but the tests only compile/run under `--features oracle`)

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_str_order_single_char -- --nocapture`
Expected: PASS — both tests. (If any returns `Unknown`, the rewrite did not fire or the minted membership did not reach/decide in the regex engine — investigate before proceeding; the pre-spec spike confirmed these exact shapes decide.)

- [ ] **Step 3: Commit**

```bash
cargo fmt
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): slice-24 e2e verdict pins — single-char order, both orientations (slice 24)"
```

---

### Task 5: differential oracle family `qfs_str_order_single_char_matches_z3`

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (a `Gen` generator method; a `gen_*` wrapper + constants + `#[test]`)

**Interfaces:**
- Consumes: `Gen`/`Gen::var`/`Gen::rng`/`Lcg`/`Verdict`/`shinri_lines_counting_bailouts`/`z3_verdict` — all existing in the file.
- Produces: `Gen::finish_str_order_single_char(self) -> String`; `#[test] fn qfs_str_order_single_char_matches_z3`.

- [ ] **Step 1: Add the generator method** — inside `impl Gen`, next to `finish_str_order` (after line 1076):

```rust
    /// A conjunction of single-char-constant-vs-symbolic `str.<` / `str.<=`
    /// atoms (constant on either side), plus a forcing equality/length
    /// constraint on a symbolic var to drive both Sat and Unsat — exactly
    /// slice 24's decided fragment. ASCII-only (z3-CLI byte-parse safety);
    /// some atoms negated. The declared string-var pool is small (see
    /// `Gen::new`), so the forcing constraint frequently binds a var used in
    /// an atom, yielding UNSAT instances as well as SAT.
    fn finish_str_order_single_char(mut self) -> String {
        const CHARS: [&str; 5] = ["a", "b", "c", "d", "e"];
        let n_atoms = 1 + self.rng.below(2); // 1..=2
        for _ in 0..n_atoms {
            let op = if self.rng.below(2) == 0 { "str.<" } else { "str.<=" };
            let v = self.var();
            let c = format!("\"{}\"", CHARS[self.rng.below(5) as usize]);
            let atom = if self.rng.below(2) == 0 {
                format!("({op} {v} {c})") // constant on the right
            } else {
                format!("({op} {c} {v})") // constant on the left
            };
            let atom = if self.rng.below(4) == 0 {
                format!("(not {atom})")
            } else {
                atom
            };
            self.body.push_str(&format!("(assert {atom})\n"));
        }
        // Force decisions on a symbolic var (some SAT, some UNSAT).
        let v = self.var();
        match self.rng.below(3) {
            0 => {
                let c = CHARS[self.rng.below(5) as usize];
                self.body.push_str(&format!("(assert (= {v} \"{c}\"))\n"));
            }
            1 => {
                let k = self.rng.below(3);
                self.body.push_str(&format!("(assert (= (str.len {v}) {k}))\n"));
            }
            _ => {}
        }
        self.body
    }
```

- [ ] **Step 2: Add the wrapper, constants, and test** — after the `qfs_str_order_matches_z3` test (line ~2420), in the "Slice 23" region or a new "Slice 24" banner:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 24: single-character str.< / str.<= vs a constant
// ─────────────────────────────────────────────────────────────────────────────

fn gen_str_order_single_char_body(seed: u64) -> String {
    Gen::new(seed).finish_str_order_single_char()
}

const SOSC_SEED: u64 = 0x53_00_0000_0004;
const SOSC_N_ITERS: usize = 200;

#[test]
fn qfs_str_order_single_char_matches_z3() {
    let mut rng = Lcg(SOSC_SEED);
    let (mut n_sat, mut n_unsat, mut n_shinri_unknown, mut n_z3_unknown, mut n_guard_bailouts) =
        (0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..SOSC_N_ITERS {
        let seed = rng.next();
        let body = gen_str_order_single_char_body(seed);

        let (lines, bailouts) = shinri_lines_counting_bailouts(&format!("{body}(check-sat)\n"));
        if bailouts > 0 {
            n_guard_bailouts += 1;
            continue;
        }
        let ours = match lines.first().map(String::as_str) {
            Some("sat") => Verdict::Sat,
            Some("unsat") => Verdict::Unsat,
            _ => Verdict::Unknown,
        };
        if ours == Verdict::Unknown {
            n_shinri_unknown += 1;
            continue;
        }
        let theirs = z3_verdict(&format!("{body}(check-sat)\n"));
        if theirs == Verdict::Unknown {
            n_z3_unknown += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_S STR_ORDER SINGLE-CHAR SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{body}(check-sat)"
        );
        match ours {
            Verdict::Sat => n_sat += 1,
            Verdict::Unsat => n_unsat += 1,
            Verdict::Unknown => unreachable!(),
        }
    }

    println!(
        "qfs_str_order_single_char_matches_z3: {SOSC_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_shinri_unknown} shinri-unknown / {n_z3_unknown} z3-unknown / {n_guard_bailouts} guard-bailout; \
         0 disagreements"
    );
    assert!(n_sat > 0, "single-char str-order family produced zero SAT instances");
    assert!(n_unsat > 0, "single-char str-order family produced zero UNSAT instances");
}
```

- [ ] **Step 3: Run the oracle family FOREGROUND with captured output**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential qfs_str_order_single_char_matches_z3 -- --nocapture`
Expected: PASS with a printed tally — **0 disagreements**, `n_sat > 0` and `n_unsat > 0`. Read the printed line: the `shinri-unknown` count should be low (this fragment now decides). If `n_unsat == 0`, bias the forcing constraint (Step 1) toward `(= v "<char>")` — do NOT relax the soundness assert.

- [ ] **Step 4: Confirm the pre-existing families are unmoved**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture`
Expected: PASS. In particular `qfs_str_order_matches_z3` (slice 23), `qfs_to_code_range`, `qfs_regex_ground/symbolic/unfold` re-run with their tallies **unchanged** — this slice adds arms and touches no existing path. Any movement is a finding to adjudicate.

- [ ] **Step 5: Commit**

```bash
cargo fmt
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_str_order_single_char_matches_z3 differential oracle family (slice 24)"
```

---

### Task 6: spec truth-up, format/lint gate, full verification

**Files:**
- Modify: `docs/superpowers/specs/2026-07-16-shinri-slice24-str-order-single-char-design.md` (status + implementation notes)

- [ ] **Step 1: Run the format gate**

Run: `cargo fmt --check`
Expected: clean (no diff). If it reports files, run `cargo fmt` and fold the result into the relevant commit.

- [ ] **Step 2: Run clippy on the touched crates**

Run: `cargo clippy -p shinri-str -p shinri-solver --all-targets -- -D warnings`
Expected: no warnings. Fix any inline (e.g. a `question_mark` or `needless_return` lint) and re-run.

- [ ] **Step 3: Run the full touched-crate test suites**

Run: `cargo test -p shinri-str --lib && cargo test -p shinri-solver --features oracle --test qfs_differential --test script_e2e -- --nocapture`
Expected: all PASS. (`shinri-str --lib` covers `order::`, `code_conv::`, `regex::`; the solver line covers oracle families + e2e.)

- [ ] **Step 4: Truth up the spec** — set the header of the slice-24 design doc to `Status: IMPLEMENTED (2026-07-16).` and add an "Implementation notes (truth-up)" block recording: the commit list (Tasks 1-5), the `qfs_str_order_single_char_matches_z3` tally (sat/unsat/unknown counts from Task 5 Step 3), and confirmation that the pre-existing oracle families re-ran unchanged. Note any deviation from the spec (there should be none of substance; if `range_membership` delegation or an arm shape differs, record it).

- [ ] **Step 5: Commit**

```bash
git add docs/superpowers/specs/2026-07-16-shinri-slice24-str-order-single-char-design.md
git commit -m "docs: slice-24 spec truth-up (IMPLEMENTED) — single-char str order (slice 24)"
```

- [ ] **Step 6: Open the PR** (matching the per-slice cadence — branch `slice24-str-order-single-char` already exists)

```bash
git push -u origin slice24-str-order-single-char
gh pr create --title "Slice 24: single-char str.< / str.<= vs constant" \
  --body "Decides single-character-constant lexicographic comparisons via regex reduction. Spec + plan under docs/superpowers/. Oracle: qfs_str_order_single_char_matches_z3, 0 disagreements."
```

---

## Self-Review

**Spec coverage:**
- Spec §Goal / §2 table (four form-families, both ops) → Tasks 2 (right) + 3 (left). ✓
- Spec "regex reduction, not str.at" premise → the reduction emits `str.in_re`; no `str.at` anywhere. ✓
- Spec §1 "no net-new surface wiring" → plan touches only `order.rs`/`regex.rs`/`code_conv.rs` + tests; no parser/term/context/print edits. ✓
- Spec §2 degenerate folds (`m=0`, `m=MAX`) → `single_char_const_right_null_char_collapses_to_empty` (Task 2), `single_char_const_left_max_char_drops_range_branch` (Task 3). ✓
- Spec §3 shared `range_rex` + surrogate/empty policy + block-edge non-fence → Task 1 + `single_char_const_block_edge_does_not_fence` (Task 3). ✓
- Spec §4 soundness → validated by the e2e verdict pins (Task 4) and the z3 differential (Task 5). ✓
- Spec §5 banked (multi-char, two-symbolic) → `multi_char_const_right_survives_to_fence` (Task 2) + slice-23's `symbolic_pair_survives_to_fence` staying green (Task 3 Step 5). ✓
- Spec §6 testing (8-form units, `--features oracle` foreground oracle, e2e pins, unchanged pre-existing families) → Tasks 2-5. ✓

**Placeholder scan:** No TBD/TODO; every code step shows complete code; every run step gives an exact command and expected outcome. ✓

**Type consistency:** `range_rex(i128,i128) -> Option<Rex>` (Task 1) is consumed identically in `order_const_right`/`order_const_left` (Tasks 2-3); `membership`/`sigma`/`sigma_star`/`single_char_code` defined in Task 2 and reused in Task 3; `MAX_CODE` is `regex`'s `u32` throughout, with `i128` arithmetic cast at the `range_rex` boundary. ✓
