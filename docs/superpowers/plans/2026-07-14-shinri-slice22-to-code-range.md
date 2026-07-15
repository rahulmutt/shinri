# Slice 22 — `str.to_code` character-range gadget — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Decide constant-RHS `str.to_code` inequality atoms — character-range constraints — by rewriting them into constant-range `str.in_re` memberships, which slices 19–21 already own.

**Architecture:** A second pass inside `crates/shinri-str/src/code_conv.rs`. Pass 1 (slice 18, unchanged) does the exact folds; pass 2 (this slice) canonicalizes every `to_code` inequality to a lower-bound threshold `to_code(s) ≥ k`, **fuses** the bounds per string term across each conjunction, and materializes **one** `str.in_re` membership per string term. It is a pure rewrite slice: every rule is a full equivalence, no fresh variables, no model repair, no polarity tracking.

**Tech Stack:** Rust, `cargo`, `shinri-str` / `shinri-solver` crates, z3 as the differential oracle.

**Spec:** `docs/superpowers/specs/2026-07-14-shinri-slice22-to-code-range-design.md`. Section references below (§1.2, §1.3, §3.1 …) point at it.

## Global Constraints

- **Soundness is absolute.** Every rule must be a full logical equivalence. Anything the gadget declines must *leave its `StrToCode` application in place*, so the existing presence fence `has_unreduced_code_conv` (`code_conv.rs:313`) turns it into a sound `Unknown`. Never guess a verdict.
- **Zero changes** to the string engine (`memb.rs`, the word-equation stepper), the regex core (`regex.rs`), the arith seam, `Fuel`, or the SAT budgets. This slice touches `code_conv.rs` and test files only.
- `MAX_CODE = 0x2FFFF` = `196607` (`code_conv.rs:30`, `i128`). `regex.rs:36` has a `u32` constant of the same value; do **not** import it (name clash) — cast at the one call site.
- Surrogate block is `0xD800..=0xDFFF` (`is_surrogate`, `code_conv.rs:32`).
- **CI runs `cargo fmt --check` and fails fast.** Run `cargo fmt` before every commit.
- Do **not** run `cargo test --workspace` — it takes ~50 minutes (the exhaustive `shinri-fp` suite). Iterate with the per-crate and per-test commands given in each task.
- Oracle tests must be run in the **foreground with output captured** (`-- --nocapture`), and the printed tally pasted into the task report. A tally is a claim; an unread tally is not.

---

### Task 1: Canonicalization and the master equivalence

Rewrites a **lone** `to_code` inequality atom into a range membership. No fusion yet — that is Task 2. At the end of this task, one-sided bounds decide and the existing inequality fence pin flips.

**Files:**
- Modify: `crates/shinri-str/src/code_conv.rs` (imports at `:24-27`; module doc at `:1-22`; `rewrite_code_conv` at `:77`; new code after `rw_from_code_const`, i.e. before `has_unreduced_code_conv` at `:311`)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs:2681-2688` (the inequality case of `targeted_code_conv_fences_unknown`)
- Test: `crates/shinri-str/src/code_conv.rs` (the `#[cfg(test)] mod tests` block at `:330`)

**Interfaces:**
- Consumes: `int_const_value(ctx, t) -> Option<Integer>` (`int_conv.rs:245`, already imported); `crate::regex::rex_to_term(ctx, &Rex) -> TermId` and `crate::regex::Rex` (both `pub(crate)`, `regex.rs:393` / `:52`); `is_surrogate(k: i128) -> bool` (`code_conv.rs:32`); `MAX_CODE: i128` (`code_conv.rs:30`).
- Produces, for Task 2:
  - `struct Bound { k: i128, negated: bool }` — a canonical `to_code(s) ≥ k`, possibly negated.
  - `fn match_code_ineq(ctx: &Context, op: BuiltinOp, kids: &[TermId]) -> Option<(TermId, Bound)>`
  - `fn range_membership(ctx: &mut Context, s: TermId, lo: i128, hi: i128) -> Option<TermId>`
  - `fn try_code_ineq_atom(ctx: &mut Context, op: Op, kids: &[TermId]) -> Option<TermId>`
  - `fn gadget(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId`

- [ ] **Step 1: Write the failing tests**

Append to the `mod tests` block in `crates/shinri-str/src/code_conv.rs` (the helpers `nullary`, `to_code`, `int_lit` already exist there at `:336-354`):

```rust
    // ── Slice 22: the character-range gadget ─────────────────────────────
    //
    // The assertions below compare TermIds directly. That is exact, not
    // fragile: the Context is hash-consed and `rex_to_term` is documented as
    // deterministic (regex.rs:387-392), so an equal Rex yields an equal
    // TermId.

    fn str_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        nullary(ctx, name, s)
    }

    /// `(<op> (str.to_code s) k)`.
    fn ineq(ctx: &mut Context, op: BuiltinOp, s: TermId, k: i128) -> TermId {
        let tc = to_code(ctx, s);
        let kk = int_lit(ctx, k);
        ctx.mk_app(Op::Builtin(op), &[tc, kk]).unwrap()
    }

    /// The expected `s ∈ Range(lo, hi)` membership term.
    fn want_range(ctx: &mut Context, s: TermId, lo: u32, hi: u32) -> TermId {
        let r = crate::regex::rex_to_term(ctx, &crate::regex::Rex::Range(lo, hi));
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, r]).unwrap()
    }

    const MAX_U32: u32 = MAX_CODE as u32;

    #[test]
    fn ge_rewrites_to_suffix_range_membership() {
        // §1.2 master equivalence: to_code(s) >= 48 ⟺ s ∈ Range(48, MAX_CODE).
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let atom = ineq(&mut ctx, BuiltinOp::Ge, s, 48);
        let out = rewrite_code_conv(&mut ctx, &[atom]);
        assert!(!has_unreduced_code_conv(&ctx, &out), "to_code must be gone");
        let want = want_range(&mut ctx, s, 48, MAX_U32);
        assert_eq!(out[0], want);
    }

    #[test]
    fn canonicalization_table() {
        // §1.1: every op, both orientations, reduced to `to_code(s) >= k*`.
        // `>  47` ≡ `>= 48`;  `<  48` ≡ ¬(>= 48);  `<= 47` ≡ ¬(>= 48).
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let want_pos = want_range(&mut ctx, s, 48, MAX_U32);
        let want_neg = ctx
            .mk_app(Op::Builtin(BuiltinOp::Not), &[want_pos])
            .unwrap();

        let gt = ineq(&mut ctx, BuiltinOp::Gt, s, 47);
        let lt = ineq(&mut ctx, BuiltinOp::Lt, s, 48);
        let le = ineq(&mut ctx, BuiltinOp::Le, s, 47);
        let out = rewrite_code_conv(&mut ctx, &[gt, lt, le]);
        assert_eq!(out[0], want_pos);
        assert_eq!(out[1], want_neg);
        assert_eq!(out[2], want_neg);

        // Mirrored orientation: `(<= k (to_code s))` ≡ `(>= (to_code s) k)`.
        let tc = to_code(&mut ctx, s);
        let k = int_lit(&mut ctx, 48);
        let mirrored = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[k, tc]).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[mirrored]);
        assert_eq!(out[0], want_pos);
    }

    #[test]
    fn zero_threshold_is_the_singleton_language() {
        // §1.2: to_code(s) >= 0 ⟺ len(s) = 1 ⟺ s ∈ Range(0, MAX_CODE)
        // (= re.allchar). Not a special case — it falls out of the formula.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let atom = ineq(&mut ctx, BuiltinOp::Ge, s, 0);
        let out = rewrite_code_conv(&mut ctx, &[atom]);
        let want = want_range(&mut ctx, s, 0, MAX_U32);
        assert_eq!(out[0], want);
    }

    #[test]
    fn degenerate_thresholds_fold_to_constants() {
        // §1.2. `to_code(s) >= -1` is a TAUTOLOGY (to_code is total into
        // {-1} ∪ [0, MAX_CODE]); `>= MAX_CODE + 1` is unsatisfiable. Negation
        // flips each.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let tt = ctx.mk_const_bool(true);
        let ff = ctx.mk_const_bool(false);

        let taut = ineq(&mut ctx, BuiltinOp::Ge, s, -1);
        let unsat = ineq(&mut ctx, BuiltinOp::Ge, s, MAX_CODE + 1);
        // `< -1` is ¬(>= -1) = false;  `<= MAX_CODE` is ¬(>= MAX_CODE+1) = true.
        let neg_taut = ineq(&mut ctx, BuiltinOp::Lt, s, -1);
        let neg_unsat = ineq(&mut ctx, BuiltinOp::Le, s, MAX_CODE);

        let out = rewrite_code_conv(&mut ctx, &[taut, unsat, neg_taut, neg_unsat]);
        assert_eq!(out[0], tt);
        assert_eq!(out[1], ff);
        assert_eq!(out[2], ff);
        assert_eq!(out[3], tt);
    }

    #[test]
    fn far_out_of_range_thresholds_fold() {
        // §1.1 clamping: a threshold too large for i128 still folds — the sign
        // decides. `>= 10^40` is unsatisfiable.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let int_s = ctx.int_sort();
        let huge = Integer::from_str_radix("1".repeat(40).as_str(), 10).unwrap();
        let k = ctx.mk_numeral(Rational::from_int(huge), int_s);
        let tc = to_code(&mut ctx, s);
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[tc, k]).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[atom]);
        assert_eq!(out[0], ctx.mk_const_bool(false));
    }

    #[test]
    fn interior_surrogate_threshold_fences() {
        // §3.1 representational fence. `range_term` encodes the FULL surrogate
        // block via `re.diff`, so 0xD800 is an admissible `lo`; a threshold
        // STRICTLY inside the block would need a lone-surrogate `re.range`
        // endpoint, which is not a `Box<str>`. Those survive to the fence.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");

        for k in [0xD801, 0xDFFF] {
            let atom = ineq(&mut ctx, BuiltinOp::Ge, s, k);
            let out = rewrite_code_conv(&mut ctx, &[atom]);
            assert!(
                has_unreduced_code_conv(&ctx, &out),
                "threshold {k:#x} must fence"
            );
        }
        // The block boundaries DO express.
        for k in [0xD7FF, 0xD800] {
            let atom = ineq(&mut ctx, BuiltinOp::Ge, s, k);
            let out = rewrite_code_conv(&mut ctx, &[atom]);
            assert!(
                !has_unreduced_code_conv(&ctx, &out),
                "threshold {k:#x} must express"
            );
        }
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

```bash
cargo test -p shinri-str code_conv 2>&1 | tail -20
```

Expected: compile errors — `str_var`, `ineq`, `want_range` reference nothing yet, and `BuiltinOp::StrInRe` / `crate::regex::Rex` are not imported. Once those resolve, the behavioural assertions fail because `rewrite_code_conv` has no inequality arm: `has_unreduced_code_conv` is still `true` and `out[0]` is still the raw atom.

- [ ] **Step 3: Add the canonicalization and materialization**

In `crates/shinri-str/src/code_conv.rs`, extend the imports at `:24-27`:

```rust
use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Integer, Op, Rational, TermId, TermNode};

use crate::int_conv::int_const_value;
use crate::regex::{rex_to_term, Rex};
```

Then insert this block after `rw_from_code_const` (i.e. after `code_conv.rs:309`, before `has_unreduced_code_conv`):

```rust
// ─── Slice 22: the str.to_code character-range gadget ────────────────────
//
// A SECOND pass over the same assertion list, run after the slice-18 pass
// above (so every foldable `str.to_code` application is already gone and only
// genuinely symbolic ones remain). Every rule is a full equivalence.

/// A `str.to_code` inequality atom canonicalized to the lower-bound form
/// `to_code(s) >= k`, possibly negated (spec §1.1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Bound {
    k: i128,
    negated: bool,
}

/// Clamp a threshold to `[-2, MAX_CODE + 1]`. Exact, because `to_code` is
/// total into `{-1} ∪ [0, MAX_CODE]`: every value below `-1` makes
/// `to_code(s) >= k` a tautology, and every value above `MAX_CODE` makes it
/// unsatisfiable. Clamping removes the i128-overflow and bignum cases in one
/// step, so the `+1` shifts below cannot overflow.
fn clamp_code(k: &Integer) -> i128 {
    match k.to_i128() {
        Some(v) => v.clamp(-2, MAX_CODE + 1),
        None if k.is_negative() => -2,
        None => MAX_CODE + 1,
    }
}

/// `(>= k (str.to_code s))` ≡ `(<= (str.to_code s) k)` — mirroring the operator
/// is how the reversed orientation joins the same canonical table.
fn mirror(op: BuiltinOp) -> BuiltinOp {
    match op {
        BuiltinOp::Ge => BuiltinOp::Le,
        BuiltinOp::Le => BuiltinOp::Ge,
        BuiltinOp::Gt => BuiltinOp::Lt,
        BuiltinOp::Lt => BuiltinOp::Gt,
        other => other,
    }
}

/// The String argument of a `(str.to_code s)` application.
fn to_code_arg(ctx: &Context, t: TermId) -> Option<TermId> {
    match ctx.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrToCode),
            args,
            ..
        } => Some(ctx.children(*args)[0]),
        _ => None,
    }
}

/// Spec §1.1: match `(⋈ (str.to_code s) k)` / `(⋈ k (str.to_code s))` for
/// `⋈ ∈ {>=, >, <=, <}` and constant Int `k`, canonicalized to
/// `to_code(s) >= b.k`. The strict/non-strict shifts are exact because
/// `to_code` is Int-valued.
fn match_code_ineq(ctx: &Context, op: BuiltinOp, kids: &[TermId]) -> Option<(TermId, Bound)> {
    if kids.len() != 2 {
        return None;
    }
    let (s, k, op) = if let Some(s) = to_code_arg(ctx, kids[0]) {
        (s, clamp_code(&int_const_value(ctx, kids[1])?), op)
    } else if let Some(s) = to_code_arg(ctx, kids[1]) {
        (s, clamp_code(&int_const_value(ctx, kids[0])?), mirror(op))
    } else {
        return None;
    };
    let b = match op {
        BuiltinOp::Ge => Bound { k, negated: false },
        BuiltinOp::Gt => Bound { k: k + 1, negated: false },
        BuiltinOp::Le => Bound { k: k + 1, negated: true },
        BuiltinOp::Lt => Bound { k, negated: true },
        _ => return None,
    };
    Some((s, b))
}

/// `s ∈ Range(lo, hi)` as a `str.in_re` term. An empty interval is `false`.
///
/// None ⇒ the representational fence (spec §3.1): `range_term` encodes the FULL
/// surrogate block via `re.diff`, so `0xD800` is an admissible `lo` and
/// `0xDFFF` an admissible `hi`, but an endpoint STRICTLY inside the block would
/// need a lone-surrogate `re.range` endpoint, which is not a `Box<str>`. The
/// caller then leaves the atom alone and `has_unreduced_code_conv` turns it into
/// a sound Unknown.
///
/// The empty-interval check comes FIRST, deliberately: `48 <= to_code(s) <= 47`
/// is unsatisfiable whatever the endpoints are, so it decides even when they
/// would not have been expressible.
fn range_membership(ctx: &mut Context, s: TermId, lo: i128, hi: i128) -> Option<TermId> {
    if lo > hi {
        return Some(ctx.mk_const_bool(false));
    }
    debug_assert!((0..=MAX_CODE).contains(&lo) && (0..=MAX_CODE).contains(&hi));
    if (is_surrogate(lo) && lo != 0xD800) || (is_surrogate(hi) && hi != 0xDFFF) {
        return None;
    }
    let r = rex_to_term(ctx, &Rex::Range(lo as u32, hi as u32));
    Some(
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[s, r])
            .expect("str.in_re well-sorted"),
    )
}

/// Spec §1.2, for a bound no fusion group claimed. None ⇒ not a `to_code`
/// inequality atom, or an inexpressible threshold (→ fence).
fn try_code_ineq_atom(ctx: &mut Context, op: Op, kids: &[TermId]) -> Option<TermId> {
    let Op::Builtin(bop) = op else { return None };
    if !matches!(
        bop,
        BuiltinOp::Ge | BuiltinOp::Gt | BuiltinOp::Le | BuiltinOp::Lt
    ) {
        return None;
    }
    let (s, b) = match_code_ineq(ctx, bop, kids)?;
    // Degenerate thresholds fold to constants, negation included.
    if b.k <= -1 {
        return Some(ctx.mk_const_bool(!b.negated)); // `>= k` is a tautology
    }
    if b.k > MAX_CODE {
        return Some(ctx.mk_const_bool(b.negated)); // `>= k` is unsatisfiable
    }
    let m = range_membership(ctx, s, b.k, MAX_CODE)?;
    Some(if b.negated {
        ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[m])
            .expect("not membership")
    } else {
        m
    })
}

/// Pass 2. Memoized. Task 2 adds the `And` fusion arm; for now every bound is
/// materialized on its own.
fn gadget(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let orig: Vec<TermId> = ctx.children(args).to_vec();
            match try_code_ineq_atom(ctx, op, &orig) {
                Some(r) => r,
                None => {
                    let kids: Vec<TermId> =
                        orig.iter().map(|&c| gadget(ctx, c, memo)).collect();
                    if kids == orig {
                        t
                    } else {
                        ctx.mk_app(op, &kids).expect("gadget: well-sorted rebuild")
                    }
                }
            }
        }
    };
    memo.insert(t, result);
    result
}
```

Now rewire `rewrite_code_conv` (`code_conv.rs:77`) to run both passes:

```rust
/// Two passes over the assertion list.
///
/// Pass 1 (slice 18, R1–R10): bottom-up, memoized; untouched subtrees keep
/// their TermIds. Every rule is a full equivalence — no model repair, no
/// polarity tracking, no occurrence analysis.
///
/// Pass 2 (slice 22): the `str.to_code` character-range gadget. It runs SECOND
/// so every foldable `to_code` application is already gone and it only ever
/// sees genuinely symbolic ones.
pub fn rewrite_code_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    let folded: Vec<TermId> = assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect();

    let mut gmemo: FxHashMap<TermId, TermId> = FxHashMap::default();
    folded
        .iter()
        .map(|&a| gadget(ctx, a, &mut gmemo))
        .collect()
}
```

- [ ] **Step 4: Run the tests to verify they pass**

```bash
cargo test -p shinri-str code_conv 2>&1 | tail -20
```

Expected: PASS, including the six pre-existing slice-18 tests (`eval_to_code_pinned_semantics`, `eval_from_code_pinned_semantics`, `folds_literal_applications`, …), which must be unaffected.

- [ ] **Step 5: Flip the inequality fence pin**

The atom `(>= (str.to_code s) 48)` now decides, so its Unknown pin is stale. In `crates/shinri-solver/tests/qfs_differential.rs`, **delete** this case from `targeted_code_conv_fences_unknown` (`:2680-2688`):

```rust
    // Inequality atom.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (>= (str.to_code s) 48))(check-sat)"
        ),
        Verdict::Unknown,
    );
```

and update that test's doc comment (`:2635-2638`) to name what still fences:

```rust
// Slice 18: str.to_code / str.from_code / str.is_digit — fence pins.
// These shapes stay OUTSIDE the decided fragment: symbolic linking, nested
// arithmetic, surrogate code points. Slice 22 REMOVED the inequality-atom pin
// from this list — those decide now (see targeted_to_code_range_decided).
```

- [ ] **Step 6: Verify the flip and the whole solver suite**

```bash
cargo test -p shinri-solver --test qfs_differential targeted_code_conv 2>&1 | tail -15
```

Expected: `targeted_code_conv_fences_unknown` and `targeted_code_conv_decided_sat` both PASS.

- [ ] **Step 7: Format and commit**

```bash
cargo fmt
cargo fmt --check
git add crates/shinri-str/src/code_conv.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "feat(str): to_code inequality atoms rewrite to range memberships (slice 22)"
```

---

### Task 2: Bound fusion

The load-bearing move (spec §1.3). Without it, a two-sided bound becomes **two** membership atoms on one string term, which is exactly slice 21's pinned intersection gap — and the digit/letter idioms this slice exists for would return Unknown.

**Files:**
- Modify: `crates/shinri-str/src/code_conv.rs` (the slice-22 block added in Task 1; `gadget`; `rewrite_code_conv`)
- Test: `crates/shinri-str/src/code_conv.rs` (`mod tests`)

**Interfaces:**
- Consumes, from Task 1: `Bound`, `match_code_ineq`, `range_membership`, `try_code_ineq_atom`, `gadget`, `rewrite_code_conv`.
- Produces:
  - `fn match_bound(ctx: &Context, t: TermId) -> Option<(TermId, Bound)>` — like `match_code_ineq`, but takes a whole conjunct and absorbs an optional `not` wrapper into `Bound::negated`.
  - `fn fuse_group(ctx: &mut Context, s: TermId, bounds: &[Bound]) -> Option<TermId>` — the interval meet.
  - `fn fuse_bounds(ctx: &mut Context, conjuncts: &[TermId]) -> Vec<TermId>` — used by `gadget`'s `And` arm **and** by `rewrite_code_conv` for the top-level assertion list.

- [ ] **Step 1: Write the failing tests**

Append to `mod tests` in `crates/shinri-str/src/code_conv.rs`:

```rust
    #[test]
    fn two_sided_bounds_fuse_to_one_range() {
        // §1.3, the whole point of the slice. 48 <= to_code(s) <= 57 must
        // produce ONE membership — s ∈ Range(48, 57) — not two. Two would land
        // on slice 21's intersection gap and return Unknown.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 48);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 57);
        // The top-level assertion list is an implicit conjunction.
        let out = rewrite_code_conv(&mut ctx, &[lo, hi]);
        let want = want_range(&mut ctx, s, 48, 57);
        let tt = ctx.mk_const_bool(true);
        assert_eq!(out[0], want);
        assert_eq!(out[1], tt);
    }

    #[test]
    fn fusion_meets_the_interval() {
        // §1.3 algebra: several lower bounds meet to their MAX, several upper
        // bounds to their MIN.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let a = ineq(&mut ctx, BuiltinOp::Ge, s, 40);
        let b = ineq(&mut ctx, BuiltinOp::Ge, s, 48); // max ⇒ lo = 48
        let c = ineq(&mut ctx, BuiltinOp::Le, s, 90);
        let d = ineq(&mut ctx, BuiltinOp::Le, s, 57); // min ⇒ hi = 57
        let out = rewrite_code_conv(&mut ctx, &[a, b, c, d]);
        let want = want_range(&mut ctx, s, 48, 57);
        assert_eq!(out[0], want);
    }

    #[test]
    fn fusion_inside_an_and_node() {
        // §1.3: `And` nodes fuse exactly like the top-level list.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 97);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 122);
        let conj = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[lo, hi]).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[conj]);
        let want = want_range(&mut ctx, s, 97, 122);
        let tt = ctx.mk_const_bool(true);
        let want_and = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[want, tt])
            .unwrap();
        assert_eq!(out[0], want_and);
    }

    #[test]
    fn fusion_absorbs_a_not_wrapper() {
        // §1.3: `(not (>= tc 58))` is the negated bound k = 58 — it must join
        // the meet, not sit outside it as a second membership.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 48);
        let raw = ineq(&mut ctx, BuiltinOp::Ge, s, 58);
        let neg = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[raw]).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[lo, neg]);
        let want = want_range(&mut ctx, s, 48, 57);
        assert_eq!(out[0], want);
    }

    #[test]
    fn crossed_bounds_fuse_to_false() {
        // §1.3: lo > hi ⇒ the empty interval ⇒ `false`.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 57);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 48);
        let out = rewrite_code_conv(&mut ctx, &[lo, hi]);
        assert_eq!(out[0], ctx.mk_const_bool(false));
    }

    #[test]
    fn crossed_bounds_beat_the_surrogate_fence() {
        // §1.3 / §3.1, ordering: the empty-interval check runs BEFORE the
        // expressibility check, so `to_code(s) >= 0xD801 ∧ to_code(s) <= 0xD7FF`
        // decides `false` even though 0xD801 is an inexpressible endpoint.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 0xD801);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 0xD7FF);
        let out = rewrite_code_conv(&mut ctx, &[lo, hi]);
        assert_eq!(out[0], ctx.mk_const_bool(false));
        assert!(!has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn upper_bounds_only_stay_a_complement() {
        // §1.3: with NO lower bound the `-1` escape survives (to_code(s) = -1
        // whenever len(s) != 1), so the constraint is genuinely a complement —
        // one NEGATED membership, still not an intersection.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let a = ineq(&mut ctx, BuiltinOp::Le, s, 90);
        let b = ineq(&mut ctx, BuiltinOp::Le, s, 57); // min ⇒ ¬(>= 58)
        let out = rewrite_code_conv(&mut ctx, &[a, b]);
        let m = want_range(&mut ctx, s, 58, MAX_U32);
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[m]).unwrap();
        assert_eq!(out[0], want);
    }

    #[test]
    fn fusion_groups_by_string_term() {
        // §1.3: bounds on DIFFERENT string terms must not be meeted together.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let t = str_var(&mut ctx, "t");
        let s_lo = ineq(&mut ctx, BuiltinOp::Ge, s, 48);
        let t_lo = ineq(&mut ctx, BuiltinOp::Ge, t, 97);
        let s_hi = ineq(&mut ctx, BuiltinOp::Le, s, 57);
        let out = rewrite_code_conv(&mut ctx, &[s_lo, t_lo, s_hi]);
        let want_s = want_range(&mut ctx, s, 48, 57);
        let want_t = want_range(&mut ctx, t, 97, MAX_U32);
        let tt = ctx.mk_const_bool(true);
        assert_eq!(out[0], want_s);
        assert_eq!(out[1], want_t);
        assert_eq!(out[2], tt);
    }

    #[test]
    fn inexpressible_fused_range_leaves_the_group_alone() {
        // §3.1: if the FUSED range has an interior-surrogate endpoint, the
        // whole group is left untouched and the presence fence catches it.
        let mut ctx = Context::new();
        let s = str_var(&mut ctx, "s");
        let lo = ineq(&mut ctx, BuiltinOp::Ge, s, 0xD801);
        let hi = ineq(&mut ctx, BuiltinOp::Le, s, 0xDF00);
        let out = rewrite_code_conv(&mut ctx, &[lo, hi]);
        assert!(has_unreduced_code_conv(&ctx, &out));
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

```bash
cargo test -p shinri-str code_conv 2>&1 | tail -25
```

Expected: the eight new tests FAIL. `two_sided_bounds_fuse_to_one_range` fails with `out[0]` being the *unfused* `s ∈ Range(48, MAX_CODE)` and `out[1]` the unfused `¬(s ∈ Range(58, MAX_CODE))` — two memberships, which is exactly the bug this task removes. The Task-1 tests still PASS.

- [ ] **Step 3: Add the fusion**

In `crates/shinri-str/src/code_conv.rs`, insert after `try_code_ineq_atom` and before `gadget`:

```rust
/// Canonicalize a whole conjunct to `(s, to_code(s) >= k)` (spec §1.1),
/// absorbing an optional `not` wrapper into the polarity. None ⇒ not a
/// `to_code` bound, so it passes through the conjunction untouched.
fn match_bound(ctx: &Context, t: TermId) -> Option<(TermId, Bound)> {
    let (inner, neg) = match ctx.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Not),
            args,
            ..
        } => (ctx.children(*args)[0], true),
        _ => (t, false),
    };
    let TermNode::App {
        op: Op::Builtin(bop),
        args,
        ..
    } = ctx.term_node(inner)
    else {
        return None;
    };
    let (bop, kids) = (*bop, ctx.children(*args).to_vec());
    let (s, mut b) = match_code_ineq(ctx, bop, &kids)?;
    if neg {
        b.negated = !b.negated;
    }
    Some((s, b))
}

/// Spec §1.3 interval meet: the bounds on ONE string term within ONE
/// conjunction collapse to a single membership. None ⇒ the fused range has an
/// inexpressible endpoint (§3.1) and the caller must leave the group alone.
fn fuse_group(ctx: &mut Context, s: TermId, bounds: &[Bound]) -> Option<TermId> {
    let mut lo: Option<i128> = None; // max of the positive thresholds
    let mut cap: Option<i128> = None; // min of the negated thresholds
    for b in bounds {
        // Degenerate thresholds fold to constants (§1.2) and so never enter the
        // meet: a tautological conjunct drops out, an unsatisfiable one
        // collapses the whole conjunction.
        if b.k <= -1 {
            // `to_code(s) >= k` is a tautology.
            if b.negated {
                return Some(ctx.mk_const_bool(false));
            }
            continue;
        }
        if b.k > MAX_CODE {
            // `to_code(s) >= k` is unsatisfiable.
            if !b.negated {
                return Some(ctx.mk_const_bool(false));
            }
            continue;
        }
        if b.negated {
            cap = Some(cap.map_or(b.k, |c| c.min(b.k)));
        } else {
            lo = Some(lo.map_or(b.k, |l| l.max(b.k)));
        }
    }
    match (lo, cap) {
        // A lower bound forces len(s) = 1, which kills the `-1` escape and
        // turns every upper bound into a clean interval cap.
        (Some(lo), cap) => range_membership(ctx, s, lo, cap.map_or(MAX_CODE, |c| c - 1)),
        // Upper bounds only: the `len != 1` escape survives, so this is a
        // genuine complement — but still ONE membership.
        (None, Some(cap)) => {
            let m = range_membership(ctx, s, cap, MAX_CODE)?;
            Some(
                ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[m])
                    .expect("not membership"),
            )
        }
        // Every bound was degenerate and dropped: vacuously true.
        (None, None) => Some(ctx.mk_const_bool(true)),
    }
}

/// Spec §1.3. Fuse the `to_code` bounds among an implicit conjunction — an
/// `And` node's children, or the top-level assertion list — into AT MOST ONE
/// membership per string term. That invariant is what keeps slice 21's
/// intersection gap out of reach.
///
/// Conjuncts that are not `to_code` bounds pass through untouched. A group
/// whose fused range is inexpressible (§3.1) is left entirely alone, so its
/// atoms survive to the presence fence.
///
/// `Or` nodes are deliberately NOT fused: SAT selects one disjunct, so only one
/// membership is ever asserted on `s` and there is nothing to intersect.
fn fuse_bounds(ctx: &mut Context, conjuncts: &[TermId]) -> Vec<TermId> {
    let mut order: Vec<TermId> = Vec::new();
    let mut groups: FxHashMap<TermId, Vec<(usize, Bound)>> = FxHashMap::default();
    for (i, &c) in conjuncts.iter().enumerate() {
        if let Some((s, b)) = match_bound(ctx, c) {
            groups
                .entry(s)
                .or_insert_with(|| {
                    order.push(s);
                    Vec::new()
                })
                .push((i, b));
        }
    }
    let mut out: Vec<TermId> = conjuncts.to_vec();
    for s in order {
        let members = &groups[&s];
        if members.len() < 2 {
            // A lone bound needs no meet — `gadget` materializes it directly.
            continue;
        }
        let bounds: Vec<Bound> = members.iter().map(|&(_, b)| b).collect();
        let Some(fused) = fuse_group(ctx, s, &bounds) else {
            continue; // inexpressible ⇒ leave the group alone ⇒ fence
        };
        out[members[0].0] = fused;
        let tt = ctx.mk_const_bool(true);
        for &(i, _) in &members[1..] {
            out[i] = tt;
        }
    }
    out
}
```

Now give `gadget` its `And` arm. Fusion happens **top-down** — before recursing — because a group's members are still raw inequality atoms at that point; recursing first would have already turned each into its own membership.

```rust
/// Pass 2 (spec §1.2 / §1.3). An `And` fuses its conjuncts BEFORE recursing
/// (top-down); every other node recurses first. Memoized: fusion happens at the
/// PARENT and never inside `gadget(atom)`, so a bound shared between an `And`
/// (fused) and an `Or` (not fused) still caches one consistent result.
fn gadget(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let orig: Vec<TermId> = ctx.children(args).to_vec();
            let conjuncts = if matches!(op, Op::Builtin(BuiltinOp::And)) {
                fuse_bounds(ctx, &orig)
            } else {
                orig.clone()
            };
            match try_code_ineq_atom(ctx, op, &conjuncts) {
                Some(r) => r,
                None => {
                    let kids: Vec<TermId> =
                        conjuncts.iter().map(|&c| gadget(ctx, c, memo)).collect();
                    if kids == orig {
                        t
                    } else {
                        ctx.mk_app(op, &kids).expect("gadget: well-sorted rebuild")
                    }
                }
            }
        }
    };
    memo.insert(t, result);
    result
}
```

Finally, fuse the top-level assertion list in `rewrite_code_conv` — it is an implicit conjunction, so it fuses exactly like an `And` node:

```rust
pub fn rewrite_code_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    let folded: Vec<TermId> = assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect();

    // The top-level assertion list is an implicit conjunction (§1.3).
    let fused = fuse_bounds(ctx, &folded);
    let mut gmemo: FxHashMap<TermId, TermId> = FxHashMap::default();
    fused.iter().map(|&a| gadget(ctx, a, &mut gmemo)).collect()
}
```

- [ ] **Step 4: Run the tests to verify they pass**

```bash
cargo test -p shinri-str code_conv 2>&1 | tail -25
```

Expected: PASS — all Task-1 and Task-2 tests, plus the pre-existing slice-18 tests.

- [ ] **Step 5: Format and commit**

```bash
cargo fmt
cargo fmt --check
git add crates/shinri-str/src/code_conv.rs
git commit -m "feat(str): fuse to_code bounds per string term per conjunction (slice 22)"
```

---

### Task 3: End-to-end verdict pins

Proves the gadget decides real idioms through the whole solver, and pins **both** downstream routes so a future change that silently reroutes them trips a test.

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (add a test after `targeted_code_conv_decided_sat`)
- Modify: `crates/shinri-solver/tests/script_e2e.rs` (add a get-value witness pin)

**Interfaces:**
- Consumes: `expect(src: &str, want: Verdict)` (`qfs_differential.rs:2176` — asserts shinri's verdict *and* cross-checks it against z3); `shinri_verdict(src) -> Verdict` (`:82`); `run_script(src) -> Vec<String>` (`script_e2e.rs:7`).
- Produces: nothing consumed by later tasks.

- [ ] **Step 1: Write the failing e2e pins**

Add to `crates/shinri-solver/tests/qfs_differential.rs`, immediately after `targeted_code_conv_decided_sat`:

```rust
/// Slice 22: the `str.to_code` character-range gadget. Inequality atoms rewrite
/// to constant-range memberships (spec §1.2), and the bounds on one string term
/// FUSE into a single membership (§1.3) — which is what keeps them off slice
/// 21's intersection gap.
///
/// No negative-threshold case here: `-` parses as `Sub`, so there is no
/// negative-numeral literal to write. The `k <= -1` degenerate folds are pinned
/// at the unit level instead (`degenerate_thresholds_fold_to_constants`).
#[test]
fn targeted_to_code_range_decided() {
    // A LONE lower bound ⇒ the wide range Range(48, MAX_CODE). ~196k words, far
    // over ENUM_WORD_CAP (256), so slice 20 declines to enumerate and slice
    // 21's engine takes it as a SINGLE character class.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (>= (str.to_code s) 48))(check-sat)",
        Verdict::Sat,
    );
    // The digit idiom ⇒ the narrow range Range(48, 57). 10 words, under
    // ENUM_WORD_CAP, so slice 20 enumerates it into `⋁ s = "0" … "9"` and the
    // word engine decides it.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (>= (str.to_code s) 48))(assert (<= (str.to_code s) 57))(check-sat)",
        Verdict::Sat,
    );
    // ... and it really is a digit constraint.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (>= (str.to_code s) 48))(assert (<= (str.to_code s) 57))\
         (assert (= s \"x\"))(check-sat)",
        Verdict::Unsat,
    );
    // Same idiom written as one `and` — `And` nodes fuse like the top-level list.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (and (>= (str.to_code s) 97) (<= (str.to_code s) 122)))\
         (assert (= s \"7\"))(check-sat)",
        Verdict::Unsat,
    );
    // Crossed bounds fuse to `false` (§1.3).
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (>= (str.to_code s) 57))(assert (<= (str.to_code s) 48))(check-sat)",
        Verdict::Unsat,
    );
    // A threshold above the alphabet is unsatisfiable (MAX_CODE = 196607).
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (> (str.to_code s) 196607))(check-sat)",
        Verdict::Unsat,
    );
    // `>= 0` is exactly `len(s) = 1` (§1.2): it rules out the empty string.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (>= (str.to_code s) 0))(assert (= s \"\"))(check-sat)",
        Verdict::Unsat,
    );
    // The `-1` sentinel, upper bound only: with NO lower bound the `len != 1`
    // escape survives, so a two-char string satisfies `to_code(s) <= 48`.
    // Mirrored orientation too.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (>= 48 (str.to_code s)))(assert (= s \"ab\"))(check-sat)",
        Verdict::Sat,
    );
    // ... but pin the length to 1 and the escape dies, so the range binds.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (<= (str.to_code s) 48))(assert (= s \"z\"))(check-sat)",
        Verdict::Unsat,
    );
}

/// Slice 22 §3.1: an interior-surrogate threshold is a PERMANENT
/// representational fence — `re.range` endpoints are `Box<str>` literals and a
/// lone surrogate is not one. The block boundaries are expressible, the inside
/// is not. Sound Unknown, never a guess.
#[test]
fn targeted_to_code_range_surrogate_fences_unknown() {
    // 0xD801 = 55297: strictly inside the surrogate block.
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (>= (str.to_code s) 55297))(check-sat)"
        ),
        Verdict::Unknown,
    );
    // 0xD800 = 55296 IS expressible — `range_term` encodes the full block.
    assert_ne!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)\
             (assert (>= (str.to_code s) 55296))(check-sat)"
        ),
        Verdict::Unknown,
    );
}

/// Slice 22 §4, KNOWN GAP: fusion sees a conjunction, and cannot see ACROSS
/// one. With the two bounds split over a disjunction, SAT can select the branch
/// that leaves two memberships asserted on `s` — slice 21's intersection gap —
/// so this saturates to a sound Unknown. Closing it needs an intersection-aware
/// conflict rule citing two membership literals, which is banked.
#[test]
fn targeted_to_code_range_split_bounds_known_gap() {
    assert_eq!(
        shinri_verdict(
            "(set-logic QF_S)(declare-fun s () String)(declare-fun p () Bool)\
             (assert (>= (str.to_code s) 48))\
             (assert (or (<= (str.to_code s) 57) p))(check-sat)"
        ),
        Verdict::Unknown,
    );
}
```

Add to `crates/shinri-solver/tests/script_e2e.rs`:

```rust
/// Slice 22: the digit range fuses to `s ∈ Range(48, 57)` (spec §1.3), which is
/// 10 words — under ENUM_WORD_CAP — so slice 20 enumerates it into
/// `⋁ s = "0" … "9"` and the word engine produces the witness.
#[test]
fn to_code_digit_range_get_value_witness() {
    let out = run_script(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (>= (str.to_code s) 48))(assert (<= (str.to_code s) 57))\
         (check-sat)(get-value (s))",
    );
    assert_eq!(out[0], "sat");
    assert!(
        ('0'..='9').any(|d| out[1].contains(&format!("\"{d}\""))),
        "expected a digit witness, got {}",
        out[1]
    );
}
```

- [ ] **Step 2: Run them and read every failure**

```bash
cargo test -p shinri-solver --test qfs_differential to_code_range 2>&1 | tail -30
cargo test -p shinri-solver --test script_e2e to_code_digit_range 2>&1 | tail -20
```

Expected after Tasks 1–2: these should mostly PASS already — the implementation is done, and these pins are the proof. **Any failure here is a real finding, not a test to bend.** In particular:
- If `targeted_to_code_range_split_bounds_known_gap` returns Sat/Unsat rather than Unknown, the intersection gap did not bite — that is *good news*, but the pin and the spec's §4 claim must both be corrected to the observed truth, and the report must say so.
- If a case pinned Sat/Unsat comes back Unknown, do **not** relax the pin. Find out which route it took (narrow ⇒ slice-20 enumeration, wide ⇒ slice-21 engine) and report it.

- [ ] **Step 3: Format and commit**

```bash
cargo fmt
cargo fmt --check
git add crates/shinri-solver/tests/qfs_differential.rs crates/shinri-solver/tests/script_e2e.rs
git commit -m "test(str): slice-22 e2e verdict pins — range gadget, fusion, fences (slice 22)"
```

---

### Task 4: Differential oracle family

Per house cadence, every slice adds a randomized family cross-checked against z3, on a fresh seed.

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (a `finish_to_code_range` method on `Gen`, near `finish_regex_unfold` at `:979`; the family itself after `qfs_regex_unfold_matches_z3`, which ends at `:2169`)

**Interfaces:**
- Consumes: `Gen::new(seed)` (`:175`), `Gen::var()` (`:185`), `Gen::regex_unfold_side_constraint(&x)` (`:947`), `Lcg`, `z3_verdict`, `shinri_lines_counting_bailouts`, `parse_string_values`, `z3_with_model`, `N_VARS` (`:165`).
- Produces: nothing consumed by later tasks.

- [ ] **Step 1: Add the generator**

In `crates/shinri-solver/tests/qfs_differential.rs`, add to the `impl Gen` block, right after `finish_regex_unfold` (which ends at `:996`):

```rust
    /// Slice 22 corpus: conjunctions of constant-RHS `str.to_code` inequality
    /// atoms over ONE symbolic string, plus the slice-21 side constraints
    /// (literal equations, concat equations, length pins). Several bounds on the
    /// same variable is the point — that is what exercises the interval meet.
    fn finish_to_code_range(mut self) -> String {
        let x = self.var();
        let n_bounds = 1 + self.rng.below(3); // 1..=3 bounds on the SAME var
        for _ in 0..n_bounds {
            let op = ["<=", "<", ">=", ">"][self.rng.below(4) as usize];
            let k = self.to_code_threshold();
            let atom = if self.rng.below(2) == 0 {
                format!("({op} (str.to_code {x}) {k})")
            } else {
                format!("({op} {k} (str.to_code {x}))") // mirrored orientation
            };
            let atom = if self.rng.below(4) == 0 {
                format!("(not {atom})")
            } else {
                atom
            };
            self.body.push_str(&format!("(assert {atom})\n"));
        }
        let n_side = self.rng.below(3); // 0..=2
        for _ in 0..n_side {
            self.regex_unfold_side_constraint(&x);
        }
        self.body
    }

    /// A NON-NEGATIVE, NON-SURROGATE Int threshold. Mostly code points around
    /// the generator's ALPHABET (so the fused ranges stay narrow and slice 20
    /// enumerates them), plus 0 and the alphabet boundary (which exercise the
    /// `len = 1` identity and the degenerate folds of spec §1.2).
    ///
    /// Surrogates are EXCLUDED: they are a permanent representational fence
    /// (§3.1), so the oracle could only ever score them as tolerated Unknowns.
    /// Negatives are excluded because `-` parses as `Sub` — there is no negative
    /// numeral literal.
    fn to_code_threshold(&mut self) -> String {
        match self.rng.below(8) {
            0 => "0".to_string(),
            1 => "196607".to_string(), // MAX_CODE
            2 => "196608".to_string(), // MAX_CODE + 1 — out of the alphabet
            _ => format!("{}", 96 + self.rng.below(30)), // 96..=125, around [a-z]
        }
    }
```

- [ ] **Step 2: Add the family**

Append after `qfs_regex_unfold_matches_z3` (i.e. after `:2169`), mirroring its structure exactly:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 22: str.to_code character-range gadget
// ─────────────────────────────────────────────────────────────────────────────

const TCR_SEED: u64 = 0x53_00_0000_0002;
const TCR_N_ITERS: usize = 200;
const TCR_MAX_GUARD_BAILOUTS: usize = TCR_N_ITERS / 10;

fn gen_to_code_range_body(seed: u64) -> String {
    Gen::new(seed).finish_to_code_range()
}

#[test]
fn qfs_to_code_range_matches_z3() {
    let mut rng = Lcg(TCR_SEED);
    let (
        mut n_sat,
        mut n_unsat,
        mut n_shinri_unknown,
        mut n_z3_unknown,
        mut n_guard_bailouts,
        mut n_witness,
    ) = (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..TCR_N_ITERS {
        let seed = rng.next();
        let body = gen_to_code_range_body(seed);

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
            "QF_S TO_CODE_RANGE SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
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
        "qfs_to_code_range_matches_z3: {TCR_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_shinri_unknown} shinri-unknown (tolerated) / {n_z3_unknown} z3-unknown / \
         {n_guard_bailouts} guard-bailout (tolerated); {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "to_code-range family produced zero SAT instances");
    assert!(
        n_unsat > 0,
        "to_code-range family produced zero UNSAT instances"
    );
    assert!(
        n_witness > 0,
        "no witnesses checked — model path not exercised"
    );
    assert!(
        n_guard_bailouts <= TCR_MAX_GUARD_BAILOUTS,
        "guard bailouts {n_guard_bailouts} exceed bound {TCR_MAX_GUARD_BAILOUTS}"
    );
}
```

- [ ] **Step 3: Run the new family IN THE FOREGROUND and read the tally**

```bash
cargo test -p shinri-solver --test qfs_differential qfs_to_code_range_matches_z3 -- --nocapture 2>&1 | tail -20
```

Expected: PASS, with a printed tally. **Copy the tally verbatim into the task report** — it is the number the spec truth-up in Task 5 records. A `SOUNDNESS DISAGREEMENT` is a hard stop: it means a rewrite rule is not an equivalence. Debug it, do not tune the generator around it.

- [ ] **Step 4: Re-run every other string family and confirm the tallies did not move**

```bash
cargo test -p shinri-solver --test qfs_differential -- --nocapture 2>&1 | grep matches_z3
```

Expected: `qfs_regex_ground`, `qfs_regex_symbolic`, and `qfs_regex_unfold` print **exactly** the tallies committed at slice-21 close (ground: 71 sat / 113 unsat / 16 shinri-unknown / 36 witnesses; symbolic: 113 sat / 76 unsat / 11 shinri-unknown / 108 witnesses; unfold: 95 sat / 88 unsat / 17 shinri-unknown / 93 witnesses). This slice does not touch the regex path, so movement is a finding to adjudicate and report — not something to wave through.

- [ ] **Step 5: Format and commit**

```bash
cargo fmt
cargo fmt --check
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): qfs_to_code_range_matches_z3 differential oracle family (slice 22)"
```

---

### Task 5: Spec truth-up

The spec currently says `Status: DESIGNED`. Make it say what actually happened — including anything that did not.

**Files:**
- Modify: `docs/superpowers/specs/2026-07-14-shinri-slice22-to-code-range-design.md`

**Interfaces:**
- Consumes: the tallies and any deviations recorded in the Task 1–4 reports.
- Produces: nothing.

- [ ] **Step 1: Update the status header and record the oracle result**

Change `Status: DESIGNED (not yet implemented).` to `Status: IMPLEMENTED (slice 22 landed 2026-07-14).`, and add an **Oracle** paragraph directly beneath it giving the `qfs_to_code_range_matches_z3` tally verbatim from Task 4 Step 3, plus the re-run result for the three regex families from Step 4 (state explicitly whether they were unchanged).

- [ ] **Step 2: Add a Deviations section**

If the implementation departed from the spec anywhere — a rule that needed a different shape, a pin whose verdict came out other than predicted, a claimed idiom that did not land — write it up under a `## Deviations from the spec` heading, in the slice-21 style: what the spec said, what was actually done, and why it is still sound. **Annotate the original claims; do not delete them.** If §4's split-bounds gap did *not* materialize (Task 3 Step 2), that goes here too — a prediction that came out better than expected is still a deviation.

If there were genuinely none, say so in one line.

- [ ] **Step 3: Commit**

```bash
git add docs/superpowers/specs/2026-07-14-shinri-slice22-to-code-range-design.md
git commit -m "docs: slice-22 spec truth-up — IMPLEMENTED + oracle tally + deviations register"
```

---

## Final gate

Before opening the PR:

```bash
cargo fmt --check
cargo clippy -p shinri-str -p shinri-solver --all-targets -- -D warnings
cargo test -p shinri-str
cargo test -p shinri-solver -- --nocapture 2>&1 | grep -E 'matches_z3|test result'
```

All four must be clean. `cargo fmt --check` is a hard CI gate that fails fast, and subagents do not auto-format.
