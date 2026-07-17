# Slice 28 — Rex intersection-emptiness refutation — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** When a string term carries ≥2 `str.in_re` memberships whose intersected language is provably empty, emit a theory `Conflict` citing exactly those literals — turning a class of sound `Unknown`s into `Unsat`.

**Architecture:** Add a three-valued derivative-BFS emptiness decision `language_empty` to `regex.rs`, then a per-term aggregation pass at the tail of `memb::memb_check` that intersects each term's (polarity-folded) membership regexes and conflicts when the intersection is certified empty. No new fuel; the emptiness caps are the bound. The conflict is sound independent of the term's structure, so no leaf/free gate.

**Tech Stack:** Rust, `rustc_hash::{FxHashMap, FxHashSet}`, the existing `Rex` algebra (`deriv`, `nullable`, `next_classes`, `node_count`, `inter`, `comp`, `extract_const_regex`) in `crates/shinri-str/src/regex.rs`.

## Global Constraints

- **Soundness is absolute.** `language_empty` returns `Empty` ONLY from a fully-explored, untainted automaton. Any cap/fuel/partition abort → `Unknown` (fall through to prior behaviour), NEVER a fabricated conflict.
- **Emptiness caps (verbatim, already defined in `regex.rs`):** `MEMB_SEARCH_STEP_CAP = 10_000` (regex.rs:410), `CLASS_SPLIT_CAP = 64` (regex.rs:408, surfaced via `next_classes` returning `None`), `FUEL_NODE_CAP = 10_000` (regex.rs:40). Do not change these in this slice.
- **`language_empty` must EXPLORE pure-surrogate classes** (unlike `search_shortest`, which skips them). Use the class's `lo` as the derivative representative; `deriv` takes a raw `u32`, so no `char` is materialised. A surrogate-only accepting path denotes a non-empty language.
- **Grouping key:** the raw string-side `TermId` from `memb_sides` (the same key `memb_seeds` uses, model.rs:470) — not an eq-class representative.
- **rustfmt clean** before every commit: `cargo fmt` then `cargo fmt --check` (CI fails fast on this — subagents do not auto-format).
- **Conflict core shape:** `TCheck::Conflict(Vec<EqLeaf>)`, each cited literal as `EqLeaf::Asserted(lit)` (identical to the Rule-G exit at memb.rs:217–219).
- Spec: `docs/superpowers/specs/2026-07-17-shinri-slice28-regex-intersection-emptiness-design.md`.

---

### Task 1: `language_empty` — three-valued emptiness certificate (`regex.rs`)

**Files:**
- Modify: `crates/shinri-str/src/regex.rs` (add `Emptiness` enum + `language_empty` fn; new unit tests in the existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: existing `nullable`, `next_classes`, `deriv`, `node_count`, `MEMB_SEARCH_STEP_CAP`, `FUEL_NODE_CAP`, `MAX_CODE`, `Rex` — all already in `regex.rs`.
- Produces:
  - `pub(crate) enum Emptiness { Empty, NonEmpty, Unknown }`
  - `pub(crate) fn language_empty(r: &Rex) -> Emptiness`

- [ ] **Step 1: Write the failing unit tests**

Add to the `#[cfg(test)] mod tests` block in `crates/shinri-str/src/regex.rs`. These use helpers already present in that module (`star`, `Rex`, `union`, `inter`, `comp`, `concat`, `MAX_CODE`); if `star` is not in scope, use `Rex::Star(Box::new(_))` directly.

```rust
#[test]
fn language_empty_basic_shapes() {
    // ∅ is empty; ε and Σ* are non-empty (both nullable).
    assert!(matches!(language_empty(&Rex::Empty), Emptiness::Empty));
    assert!(matches!(language_empty(&Rex::Eps), Emptiness::NonEmpty));
    let sigma_star = Rex::Star(Box::new(Rex::Range(0, MAX_CODE)));
    assert!(matches!(language_empty(&sigma_star), Emptiness::NonEmpty));
}

#[test]
fn language_empty_disjoint_infinite_tails() {
    // a·Σ* ∩ b·Σ* — first char must be both 'a' and 'b' ⇒ empty language.
    let sigma_star = Rex::Star(Box::new(Rex::Range(0, MAX_CODE)));
    let a_tail = concat(vec![Rex::Range('a' as u32, 'a' as u32), sigma_star.clone()]);
    let b_tail = concat(vec![Rex::Range('b' as u32, 'b' as u32), sigma_star]);
    let goal = inter(vec![a_tail, b_tail]);
    assert!(matches!(language_empty(&goal), Emptiness::Empty));
}

#[test]
fn language_empty_r_inter_comp_r_is_empty() {
    // R ∩ comp(R) = ∅ — exercises the derivative over `Comp` and confirms
    // negative-polarity folding is decided empty.
    let sigma_star = Rex::Star(Box::new(Rex::Range(0, MAX_CODE)));
    let r = concat(vec![Rex::Range('a' as u32, 'a' as u32), sigma_star]);
    let goal = inter(vec![r.clone(), comp(r)]);
    assert!(matches!(language_empty(&goal), Emptiness::Empty));
}

#[test]
fn language_empty_explores_surrogate_only_path() {
    // A single-surrogate range is NON-empty: `search_word` skips this class
    // (no Rust char), but a surrogate is a valid SMT-LIB code point, so the
    // emptiness certificate must EXPLORE it and report NonEmpty.
    let surr = Rex::Range(0xD800, 0xD800);
    assert!(matches!(language_empty(&surr), Emptiness::NonEmpty));
}

#[test]
fn language_empty_class_split_overflow_taints_to_unknown() {
    // > CLASS_SPLIT_CAP (64) distinct, non-adjacent first-char classes ⇒
    // `next_classes` returns None ⇒ the traversal cannot complete ⇒ Unknown
    // (a taint, NOT a false Empty).
    let ranges: Vec<Rex> = (0u32..70).map(|i| Rex::Range(2 * i, 2 * i)).collect();
    let many = union(ranges);
    assert!(matches!(language_empty(&many), Emptiness::Unknown));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str language_empty 2>&1 | tail -20`
Expected: FAIL — `cannot find function \`language_empty\`` / `cannot find type \`Emptiness\``.

- [ ] **Step 3: Implement `Emptiness` + `language_empty`**

Add near `search_shortest` (after regex.rs:748) in `crates/shinri-str/src/regex.rs`:

```rust
/// Three-valued emptiness of `L(r)`. `Empty` / `NonEmpty` are DECISIONS;
/// `Unknown` means a fuel/partition cap prevented a complete traversal (an
/// abort, NOT a verdict — the caller keeps its prior sound Unknown). `Empty`
/// is returned ONLY when the entire reachable derivative automaton was
/// explored, no reachable state is nullable, and no taint occurred.
///
/// Unlike `search_shortest`, this EXPLORES pure-surrogate character classes:
/// a surrogate is a valid SMT-LIB code point, so a state whose only accepting
/// path runs through a surrogate class denotes a NON-empty language. The
/// class's `lo` is a valid derivative representative (every code point in a
/// `next_classes` interval has identical derivative behaviour), and `deriv`
/// takes a raw `u32`, so no `char` is materialised.
pub(crate) enum Emptiness {
    Empty,
    NonEmpty,
    Unknown,
}

pub(crate) fn language_empty(r: &Rex) -> Emptiness {
    let mut steps = 0usize;
    let mut seen: FxHashSet<Rex> = FxHashSet::default();
    seen.insert(r.clone());
    let mut frontier: Vec<Rex> = vec![r.clone()];
    while !frontier.is_empty() {
        let mut next: Vec<Rex> = Vec::new();
        for state in frontier {
            if nullable(&state) {
                return Emptiness::NonEmpty;
            }
            if matches!(state, Rex::Empty) {
                continue;
            }
            if steps >= MEMB_SEARCH_STEP_CAP {
                return Emptiness::Unknown;
            }
            steps += 1;
            let Some(classes) = next_classes(&state) else {
                return Emptiness::Unknown; // CLASS_SPLIT_CAP overflow — taint
            };
            for (lo, _hi) in classes {
                let d = deriv(lo, &state);
                if node_count(&d) > FUEL_NODE_CAP {
                    return Emptiness::Unknown; // derivative blowup — taint
                }
                if seen.insert(d.clone()) {
                    next.push(d);
                }
            }
        }
        frontier = next;
    }
    Emptiness::Empty
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-str language_empty 2>&1 | tail -20`
Expected: PASS — all 5 `language_empty_*` tests green.

- [ ] **Step 5: Format and commit**

```bash
cargo fmt
cargo fmt --check
git add crates/shinri-str/src/regex.rs
git commit -m "feat(str): three-valued language_empty derivative certificate (slice 28)"
```

---

### Task 2: Per-term intersection-emptiness conflict pass (`memb.rs`)

**Files:**
- Modify: `crates/shinri-str/src/memb.rs` (add `FxHashMap` to the import at memb.rs:6; insert the aggregation pass just before the final `None` at memb.rs:543; add two unit tests to the `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `regex::language_empty`, `regex::Emptiness`, `regex::inter`, `regex::comp`, `regex::extract_const_regex` (Task 1 + existing); `memb_sides` (memb.rs:20); `s.memb_true: Vec<(TermId, Lit, bool)>`; `EqLeaf::Asserted`; `TCheck::Conflict`.
- Produces: no new public surface — `memb_check` gains a conflict exit.

- [ ] **Step 1: Write the failing unit tests**

Add to the `#[cfg(test)] mod tests` block in `crates/shinri-str/src/memb.rs` (helpers `var`, `memb_atom`, `harness`, `run_rounds` already exist there):

```rust
#[test]
fn intersection_empty_infinite_tails_conflict() {
    // Slice 28: s ∈ a·Σ* ∧ s ∈ b·Σ* — disjoint first chars ⇒ empty joint
    // language. The per-term emptiness pass must Conflict (was sound Unknown;
    // `run_rounds` panics on Unknown, so reaching Conflict is the assertion).
    let mut ctx = Context::new();
    let s_var = var(&mut ctx, "s");
    let sigma_star = Rex::Star(Box::new(Rex::Range(0, regex::MAX_CODE)));
    let a_tail = regex::concat(vec![Rex::Range('a' as u32, 'a' as u32), sigma_star.clone()]);
    let b_tail = regex::concat(vec![Rex::Range('b' as u32, 'b' as u32), sigma_star]);
    let ma = memb_atom(&mut ctx, s_var, &a_tail);
    let mb = memb_atom(&mut ctx, s_var, &b_tail);
    let (mut s, mut eq_e, atoms) = harness(&mut ctx);
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &atoms };
    s.new_var(&mut cx, shinri_core::Var::new(0), ma);
    s.new_var(&mut cx, shinri_core::Var::new(1), mb);
    s.test_force_memb_true(ma, true);
    s.test_force_memb_true(mb, true);
    let (_, terminal) = run_rounds(&mut s, &mut cx, 16);
    assert!(
        matches!(terminal, TCheck::Conflict(_)),
        "empty intersection of two infinite tails must conflict"
    );
}

#[test]
fn intersection_negative_fold_nonempty_no_conflict() {
    // Negative-polarity folding is wired (s ∉ b·Σ* ≡ s ∈ comp(b·Σ*)), but the
    // intersection a·Σ* ∩ comp(b·Σ*) is NON-empty (any a-starting word never
    // starts with b), so NO conflict — the pass leaves the verdict to the
    // existing Sat/repair flow. Reaching a non-Conflict terminal (Sat) is the
    // assertion; `run_rounds` panics on Unknown.
    let mut ctx = Context::new();
    let s_var = var(&mut ctx, "s");
    let sigma_star = Rex::Star(Box::new(Rex::Range(0, regex::MAX_CODE)));
    let a_tail = regex::concat(vec![Rex::Range('a' as u32, 'a' as u32), sigma_star.clone()]);
    let b_tail = regex::concat(vec![Rex::Range('b' as u32, 'b' as u32), sigma_star]);
    let ma = memb_atom(&mut ctx, s_var, &a_tail);
    let mb = memb_atom(&mut ctx, s_var, &b_tail);
    let (mut s, mut eq_e, atoms) = harness(&mut ctx);
    let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq_e, atoms: &atoms };
    s.new_var(&mut cx, shinri_core::Var::new(0), ma);
    s.new_var(&mut cx, shinri_core::Var::new(1), mb);
    s.test_force_memb_true(ma, true);
    s.test_force_memb_true(mb, false); // s ∉ b·Σ*  ⇒  comp(b·Σ*)
    let (_, terminal) = run_rounds(&mut s, &mut cx, 16);
    assert!(
        !matches!(terminal, TCheck::Conflict(_)),
        "non-empty intersection must NOT conflict"
    );
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-str intersection_ 2>&1 | tail -25`
Expected: `intersection_empty_infinite_tails_conflict` FAILS — `run_rounds` panics with "no fixpoint within 16 rounds" (today it saturates to Sat, never conflicts). (`intersection_negative_fold_nonempty_no_conflict` may already pass — it asserts the *absence* of a conflict.)

- [ ] **Step 3: Add the `FxHashMap` import**

In `crates/shinri-str/src/memb.rs`, change line 6:

```rust
use rustc_hash::FxHashSet;
```

to:

```rust
use rustc_hash::{FxHashMap, FxHashSet};
```

- [ ] **Step 4: Implement the aggregation pass**

In `crates/shinri-str/src/memb.rs`, replace the final `None` of `memb_check` (memb.rs:543) with the pass followed by `None`:

```rust
    // ── Slice 28: per-term intersection-emptiness conflict ───────────────
    // The per-atom loop above never intersects two memberships on the same
    // term, so a jointly-empty language (e.g. s ∈ a·Σ* ∧ s ∈ b·Σ*) escapes as
    // a sound Unknown. Group the LIVE memberships by string-side term id (the
    // same raw-`TermId` key `memb_seeds` uses), intersect their polarity-
    // folded regexes, and if the joint language is PROVABLY empty emit a
    // conflict citing exactly those literals. Sound for ANY term: L(∩ Rᵢ) = ∅
    // means `t ∈ R₁ ∧ … ∧ t ∈ Rₖ` is unsatisfiable regardless of `t`'s
    // structure (spec §5). A cap/fuel abort (`Emptiness::Unknown`) or a
    // non-empty intersection falls through to the prior Sat/repair path.
    let mut by_term: FxHashMap<TermId, Vec<(shinri_core::Lit, Rex)>> = FxHashMap::default();
    for &(atom, lit, pos) in &s.memb_true {
        let (t, re_t) = memb_sides(cx.terms, atom);
        let Some(mut rex) = regex::extract_const_regex(cx.terms, re_t) else {
            continue; // non-constant regex — fence, never guess
        };
        if !pos {
            rex = regex::comp(rex); // t ∉ R ≡ t ∈ comp(R)
        }
        by_term.entry(t).or_default().push((lit, rex));
    }
    for members in by_term.into_values() {
        if members.len() < 2 {
            continue; // single-atom empties are already folded upstream
        }
        let goal = regex::inter(members.iter().map(|(_, r)| r.clone()).collect());
        if matches!(regex::language_empty(&goal), regex::Emptiness::Empty) {
            let just = members
                .iter()
                .map(|(lit, _)| EqLeaf::Asserted(*lit))
                .collect();
            return Some(TCheck::Conflict(just));
        }
    }
    None
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-str intersection_ 2>&1 | tail -25`
Expected: PASS — both `intersection_*` tests green.

- [ ] **Step 6: Run the full `shinri-str` suite (no regressions)**

Run: `cargo test -p shinri-str 2>&1 | tail -15`
Expected: all tests pass (existing membership/regex/model tests unaffected — the pass only ADDS a conflict exit reached after the per-atom loop).

- [ ] **Step 7: Format and commit**

```bash
cargo fmt
cargo fmt --check
git add crates/shinri-str/src/memb.rs
git commit -m "feat(str): per-term intersection-emptiness conflict on the check path (slice 28)"
```

---

### Task 3: End-to-end pins — flip the gap, pin the new decisions (`qfs_differential.rs`)

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (rewrite `targeted_leaf_membership_infinite_conflict_known_gap` at line 4044; add two new `#[test]` fns nearby)

**Interfaces:**
- Consumes: `expect(src, Verdict)` (qfs_differential.rs:2548 — asserts shinri's verdict AND cross-checks z3 agreement when the verdict is not `Unknown`), `Verdict`.
- Produces: no code surface — test pins only.

- [ ] **Step 1: Flip the known-gap pin to a decided pin**

In `crates/shinri-solver/tests/qfs_differential.rs`, replace the whole `targeted_leaf_membership_infinite_conflict_known_gap` function (lines 4043–4059, including its `#[test]` attribute) with:

```rust
#[test]
fn targeted_leaf_membership_infinite_conflict_now_decides() {
    // Slice 28 CASHES the slice-26 banked gap: conflicting INFINITE leaf
    // memberships s ∈ a·Σ* ∧ s ∈ b·Σ* require the first char to be both 'a'
    // and 'b' ⇒ empty joint language ⇒ Unsat (z3: unsat). The per-term
    // intersection-emptiness pass (memb.rs) now decides it via
    // `regex::language_empty`; previously a sound Unknown (repair can never
    // produce Unsat). `expect` cross-checks z3 agreement.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.++ (str.to_re \"a\") (re.* re.allchar))))\
         (assert (str.in_re s (re.++ (str.to_re \"b\") (re.* re.allchar))))(check-sat)",
        Verdict::Unsat,
    );
}
```

- [ ] **Step 2: Add the 3-way and non-empty (Sat) pins**

Immediately after the function from Step 1, add:

```rust
#[test]
fn targeted_intersection_three_way_first_char_empty_unsat() {
    // Three infinite memberships, pairwise NON-empty first-char sets
    // ({a,b},{b,c},{a,c}) but empty three-way intersection (no char is in all
    // three) ⇒ Unsat. Each Σ*-tailed regex is infinite, so none is
    // finite-reduced to a ground equality — the emptiness pass is what
    // decides it. z3: unsat.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.++ (re.union (str.to_re \"a\") (str.to_re \"b\")) (re.* re.allchar))))\
         (assert (str.in_re s (re.++ (re.union (str.to_re \"b\") (str.to_re \"c\")) (re.* re.allchar))))\
         (assert (str.in_re s (re.++ (re.union (str.to_re \"a\") (str.to_re \"c\")) (re.* re.allchar))))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_intersection_nonempty_stays_sat() {
    // s ∈ Σ·Σ* ∧ s ∈ a·Σ* — both satisfied by any word starting with 'a'
    // (e.g. "a"), so the intersection is NON-empty. The emptiness pass must
    // NOT conflict; the verdict stays Sat. Guards against an over-eager
    // `Empty`. z3: sat.
    expect(
        "(set-logic QF_S)(declare-fun s () String)\
         (assert (str.in_re s (re.++ re.allchar (re.* re.allchar))))\
         (assert (str.in_re s (re.++ (str.to_re \"a\") (re.* re.allchar))))(check-sat)",
        Verdict::Sat,
    );
}
```

- [ ] **Step 3: Run the new/flipped pins**

Run: `cargo test -p shinri-solver --test qfs_differential targeted_intersection_ targeted_leaf_membership_infinite_conflict 2>&1 | tail -20`
Expected: PASS — `targeted_leaf_membership_infinite_conflict_now_decides`, `targeted_intersection_three_way_first_char_empty_unsat`, `targeted_intersection_nonempty_stays_sat` all green (each cross-checked against z3 inside `expect`).

- [ ] **Step 4: Confirm the old gap name is gone**

Run: `grep -rn "targeted_leaf_membership_infinite_conflict_known_gap" crates/`
Expected: no matches (the rename is complete — no stale reference).

- [ ] **Step 5: Format and commit**

```bash
cargo fmt
cargo fmt --check
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(solver): flip infinite-conflict gap to Unsat; pin 3-way + non-empty (slice 28)"
```

---

### Task 4: Differential oracle, full gate, spec truth-up, PR

**Files:**
- Modify: `docs/superpowers/specs/2026-07-17-shinri-slice28-regex-intersection-emptiness-design.md` (append truth-up; flip `Status:`)

**Interfaces:**
- Consumes: nothing new — verification + docs.
- Produces: the merged slice.

- [ ] **Step 1: Run the differential oracle (foreground, captured)**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture 2>&1 | tee /tmp/claude-1000/-workspace/7d8e9d16-ea8e-4e13-b775-8ca3a44fb3ff/scratchpad/slice28-oracle.log | tail -40`
Expected: 0 failures; **0 shinri-vs-z3 disagreements** across the fuzz families; unknown count not increased. If any family reports a disagreement, STOP — that is a soundness regression, not a pin to flip.

- [ ] **Step 2: Inspect the per-iteration diff direction**

Review `/tmp/claude-1000/-workspace/7d8e9d16-ea8e-4e13-b775-8ca3a44fb3ff/scratchpad/slice28-oracle.log`: every verdict change attributable to this slice must be `Unknown → Unsat`. Zero `decided → Unknown`, zero `sat ↔ unsat`. Record the exact flip counts for the truth-up.

- [ ] **Step 3: Run the full local gate (slice-27 lesson: include `script_e2e`)**

Run each; all must pass:
```bash
cargo test -p shinri-str 2>&1 | tail -5
cargo test -p shinri-solver --test qfs_differential 2>&1 | tail -5
cargo test -p shinri-solver --test script_e2e 2>&1 | tail -5
cargo fmt --check
```
Expected: all green. If a `script_e2e` pin flips `Unknown → Unsat` and z3 confirms unsat (capped), that is an adjudicated flip (slice-25/26 precedent) — update the pin with the mechanism in its comment and record it in the truth-up; it is NOT a blocker. Any other flip direction blocks.

- [ ] **Step 4: Truth-up the spec**

In `docs/superpowers/specs/2026-07-17-shinri-slice28-regex-intersection-emptiness-design.md`, change the `Status:` line to:

```
Status: IMPLEMENTED (2026-07-17). See "Implementation notes (truth-up)" at the end.
```

and append a `## Implementation notes (truth-up)` section recording, with commit hashes: what landed as designed; any deviations; the oracle per-iteration flip counts from Step 2; any `script_e2e` adjudicated flip from Step 3; anything newly banked.

- [ ] **Step 5: Commit the truth-up**

```bash
git add docs/superpowers/specs/2026-07-17-shinri-slice28-regex-intersection-emptiness-design.md
git commit -m "docs: slice-28 spec truth-up (IMPLEMENTED) — Rex intersection-emptiness (slice 28)"
```

- [ ] **Step 6: Push and open the PR**

```bash
git push -u origin slice28-regex-intersection-emptiness
gh pr create --title "Slice 28: Rex intersection-emptiness refutation" \
  --body "Cashes the slice-26/27 banked item: a term carrying ≥2 memberships whose intersected language is provably empty now yields Unsat instead of a sound Unknown. Adds a three-valued \`language_empty\` derivative certificate (regex.rs) and a per-term aggregation conflict pass on the check path (memb.rs), citing exactly the contributing membership literals. Flips \`targeted_leaf_membership_infinite_conflict_known_gap\` to Unsat. Spec: docs/superpowers/specs/2026-07-17-shinri-slice28-regex-intersection-emptiness-design.md"
```

- [ ] **Step 7: Merge on green (standing policy)**

When CI is green, merge (merge commit), then delete the branch remote + local and prune. If CI surfaces a `script_e2e`/oracle pin flip, adjudicate per Step 3 (z3-confirmed `Unknown → Unsat` is a flip, not a blocker), amend the truth-up, and re-push before merging.

---

## Self-Review

**Spec coverage:**
- §3 emptiness certificate (`Empty`/`NonEmpty`/`Unknown`, taint on step/class/node caps, surrogate exploration) → Task 1. ✓
- §4 check-path aggregation (raw-`TermId` grouping, polarity fold via `comp`, `inter`, conflict citing `EqLeaf::Asserted`, extraction-failure fence, ≥2 members, runs after per-atom loop) → Task 2. ✓
- §5 soundness (term-agnostic; `Empty` only untainted) → enforced by Task 1 impl + Task 2 comment; exercised by Task 2 conflict test. ✓
- §6 completeness boundary (cap → Unknown; single-atom folded upstream) → Task 1 taint test + Task 2 `members.len() < 2` guard. ✓
- §7 testing (flip pin, positive pins, non-empty Sat pin, `language_empty` units incl. surrogate + taint, oracle, `script_e2e` gate) → Tasks 1/3/4. ✓
- §8 non-goals (minimization, cross-term, cap-raising) → not implemented, correctly absent. ✓

**Placeholder scan:** No TBD/TODO/"handle edge cases"/"similar to". Every code step shows full code; every run step shows command + expected. ✓

**Type consistency:** `Emptiness { Empty, NonEmpty, Unknown }` and `language_empty(&Rex) -> Emptiness` defined in Task 1 and consumed with the same names/paths (`regex::Emptiness::Empty`, `regex::language_empty`) in Task 2. Grouping value type `(shinri_core::Lit, Rex)` matches the `s.memb_true: Vec<(TermId, Lit, bool)>` source and the `EqLeaf::Asserted(lit)` core shape. Rename `..._known_gap` → `..._now_decides` is applied at its definition (Task 3 Step 1) and its absence verified (Task 3 Step 4). ✓
