# Slice 37 — Cite the Strips (Propagate path) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Restore the one measured completeness cost slice 35 logged as approach B's un-banking trigger by citing the EUF-merge strip antecedents into a `Propagate`'s justification, then lifting the flattened-path `Propagate → Saturated` downgrade.

**Architecture:** In `resolve_inner`'s two head/tail strip loops, replace the boolean `same()` guard with a `same_explain()` variant that appends `eq.explain` leaves whenever a pair is cancelled through the EUF-class door (`eq.are_equal`), threading them into the equation's `just`. With `just` now complete, delete the `Propagate → Saturated` arm of the `resolve_equation` wrapper so the propagation flows through with a fully-justified merge. The `Conflict → Saturated` arm is left untouched (banked, no trigger). The strip-explain pass is shared by both the flattened and non-flattened paths; the non-flattened path only ever gains duplicate (already-cited) leaves, which the SAT layer dedups.

**Tech Stack:** Rust; crates `shinri-str` (word-equation resolver), `shinri-theory` (`EqualityEngine::explain`/`merge`), `shinri-solver` (differential oracle harness); `cargo nextest`, `z3`/`cvc5` via mise, `mise` task runner.

## Global Constraints

- Pure-Rust mandate: no native-link deps (`deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`). This slice adds no dependencies.
- Blocking PR test tier budget: **10–15 min wall-clock** (CI hard cap 20 min). Do not un-`#[ignore]` any `shinri-fp` exhaustive.
- Oracle differential tests are feature-gated: run with `--features oracle`. **Without it they silently run 0 tests** — a 0-test run is NOT green coverage; confirm a non-zero test count.
- DIFFDUMP dump-and-diff needs `-- --nocapture`, else `eprintln!` is swallowed on passing runs (0 lines, still "green"). **Verify the dump line count is non-zero before trusting any diff.**
- nextest filters: use `-E 'test(name)'` / `-E 'binary(name)'`, not the positional `mod::name` form; **confirm discovery** (a 0-test run reads as green).
- Run `cargo fmt --all` before any push — CI gates on `fmt --check` and fails fast. `cargo clippy --workspace --all-targets -- -D warnings` must be clean.
- Soundness bar: this slice only buys completeness **back**. Any new `sat ↔ unsat` disagreement vs z3, any `theory_conflict_analyzable` bail-count increase, or any `decided → unknown` flip is a **halt-and-adjudicate** blocker.

## File Structure

- `crates/shinri-str/src/wordeq.rs` — the only source file touched. Adds `same_explain` next to `same` (`wordeq.rs:407`); makes `resolve_inner`'s `just` parameter `mut` and swaps the two strip-loop guards (`wordeq.rs:546-555`); deletes the `Propagate` arm of the `resolve_equation` wrapper `match` (`wordeq.rs:482`); truth-ups the wrapper doc comment (items 2–3, `wordeq.rs:431-443`) and the `StepResult::Propagate` doc (`wordeq.rs:15-38`); updates two slice-35 unit tests and adds two new ones (all in the `#[cfg(test)] mod tests` block).
- `crates/shinri-solver/tests/qfs_differential.rs` — **temporary** DIFFDUMP instrumentation added in Task 2, run, then reverted with `git checkout --`. No permanent change.
- `docs/superpowers/specs/2026-07-21-shinri-slice37-strip-citation-propagate-design.md` — gains a measured-outcomes truth-up section in Task 2.

---

### Task 1: Cite the EUF-door strips and lift the flattened Propagate downgrade

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs` (helper, strip loops, wrapper arm, doc comments)
- Test: `crates/shinri-str/src/wordeq.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `EqualityEngine::intern(&mut self, TermId) -> ENodeId`, `EqualityEngine::are_equal(&self, ENodeId, ENodeId) -> bool`, `EqualityEngine::explain(&self, ENodeId, ENodeId, &mut Vec<EqLeaf>)`, `EqualityEngine::merge(&mut self, ENodeId, ENodeId, EqJust) -> Result<(), EqConflict>`, `Context::string_const_value(&self, TermId) -> Option<&str>`, `EqLeaf::Asserted(Lit)`, `EqJust::{Asserted(Lit), Definitional}`.
- Produces: `fn same_explain(terms: &mut Context, eq: &mut EqualityEngine, a: TermId, b: TermId, out: &mut Vec<EqLeaf>) -> bool` — same truth value as `same`, with the side effect of appending the merge's `explain` leaves to `out` on (and only on) the EUF-class door. After this task `resolve_equation` returns `StepResult::Propagate { var, word, just }` (with `just` carrying the strip merges) on the flattened path instead of `StepResult::Saturated`.

- [ ] **Step 1: Write the failing leaf-level test**

Add to the `mod tests` block (near the other flattened-residual tests, after `flattened_alias_residual_does_not_propagate` ~`wordeq.rs:1736`). Note `StepResult` has no `Debug`, so panic arms must not format the value.

```rust
/// Slice 37: the flattened alias residual that slice 35 downgraded now
/// PROPAGATES — and cites the EUF-door strip merge. `p ≈ q` is merged with
/// antecedent `merge_lit`; the flattened head strip cancels `p` against `q`
/// through the `eq.are_equal` door, so the propagated `x ≈ y` MUST carry
/// `merge_lit` in its justification (the under-citation slice 35 fenced).
#[test]
fn flattened_alias_residual_cites_euf_strip_merge() {
    use shinri_theory::types::EqJust;
    let mut ctx = Context::new();
    let mut eq = EqualityEngine::default();
    let p = declare_str_var(&mut ctx, "p_cite");
    let q = declare_str_var(&mut ctx, "q_cite");
    let x = declare_str_var(&mut ctx, "x_cite");
    let y = declare_str_var(&mut ctx, "y_cite");
    // Merge p ≈ q via a genuine EUF merge whose antecedent is `merge_lit`.
    let merge_lit = Lit::new(Var::new(1), true);
    let pn = eq.intern(p);
    let qn = eq.intern(q);
    let _ = eq.merge(pn, qn, EqJust::Asserted(merge_lit));
    // lhs carries a concat atom → flattened path; the head strip cancels p
    // against q via the EUF door (not same-TermId, not literal value).
    let concat = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[p, x])
        .unwrap();
    let eqn_lit = dummy_eqn_lit();
    let just = vec![EqLeaf::Asserted(eqn_lit)];
    let mut ctr = 0u32;
    let mut emitted = FxHashSet::default();
    let r = resolve_equation(
        &mut ctx,
        &mut eq,
        &[concat],
        &[q, y],
        just,
        eqn_lit,
        &mut ctr,
        &mut emitted,
    );
    match r {
        StepResult::Propagate { var, word, just } => {
            assert_eq!(var, x, "left residual must be reported as `var`");
            assert_eq!(word, y, "right residual must be reported as `word`");
            assert!(
                just.iter()
                    .any(|l| matches!(l, EqLeaf::Asserted(a) if *a == eqn_lit)),
                "must retain the asserting equation literal"
            );
            assert!(
                just.iter()
                    .any(|l| matches!(l, EqLeaf::Asserted(a) if *a == merge_lit)),
                "must CITE the EUF-door strip merge antecedent (slice-37 fix)"
            );
        }
        _ => panic!("expected Propagate carrying the cited strip merge"),
    }
}
```

- [ ] **Step 2: Run the new test to verify it fails**

Run: `cargo nextest run -p shinri-str -E 'test(flattened_alias_residual_cites_euf_strip_merge)'`
Expected: discovery = 1 test; FAIL — the pre-slice-37 wrapper downgrades the flattened `Propagate` to `Saturated`, so the `match` hits the `_ => panic!` arm ("expected Propagate carrying the cited strip merge"). (If discovery is 0, the filter is wrong — fix before proceeding.)

- [ ] **Step 3: Add the `same_explain` helper**

Insert immediately after `same` (after `wordeq.rs:417`):

```rust
/// Like [`same`], but on the EUF-class door (the pair is equal only because a
/// MERGE placed both atoms in one class) it appends the merge's antecedent
/// leaves to `out` via `eq.explain`. The same-TermId and equal-literal-value
/// doors are self-justifying and contribute no leaf (mirroring
/// `nf_equal_explain`'s two `continue` guards). Used by the strip loops so a
/// residual propagation cites every class equality a strip consumed — the
/// citation slice 35 lacked, which forced the flattened-path `Propagate`
/// downgrade.
pub(crate) fn same_explain(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    a: TermId,
    b: TermId,
    out: &mut Vec<EqLeaf>,
) -> bool {
    if a == b {
        return true; // identity: no merge, no leaf
    }
    if let (Some(x), Some(y)) = (terms.string_const_value(a), terms.string_const_value(b)) {
        return x == y; // literal-value equality: no merge antecedent
    }
    let an = eq.intern(a);
    let bn = eq.intern(b);
    if eq.are_equal(an, bn) {
        eq.explain(an, bn, out); // EUF door: cite the merge path
        true
    } else {
        false
    }
}
```

- [ ] **Step 4: Thread the citation through `resolve_inner`'s strip loops**

Change the `just` parameter of `resolve_inner` to `mut just` (`wordeq.rs:537`):

```rust
    mut just: Vec<EqLeaf>,
```

Replace the two strip loops (`wordeq.rs:545-555`) with:

```rust
    // Strip equal heads (citing any EUF-class merge each cancellation consumes).
    while i < le && j < re && same_explain(terms, eq, lhs[i], rhs[j], &mut just) {
        i += 1;
        j += 1;
    }

    // Strip equal tails (same citation).
    while le > i && re > j && same_explain(terms, eq, lhs[le - 1], rhs[re - 1], &mut just) {
        le -= 1;
        re -= 1;
    }
```

(The internal `same` calls inside `occurs_unsat` and `single_var_forced_length_conflict` are NOT changed — only the two strip loops. Every downstream `StepResult::Conflict(just)` / `StepResult::Propagate { just, .. }` site now sees the enriched `just`; on the flattened path a `Conflict` is discarded via the wrapper's `Saturated` downgrade, and on the non-flattened path a strip merge is already cited by `normal_form`, so any added leaf is a harmless duplicate.)

- [ ] **Step 5: Lift the flattened-path `Propagate` downgrade**

In `resolve_equation`'s wrapper `match` (`wordeq.rs:470-484`), delete the `Propagate → Saturated` arm so it folds into `other => other`. The `Conflict` arm is unchanged:

```rust
    match resolve_inner(
        terms, eq, &lhs_flat, &rhs_flat, just, eqn_lit, fresh_ctr, emitted,
    ) {
        // A conflict off a flattened concat rep would be under-cited → Saturate.
        // (Lifting THIS arm is separately banked — no qualifying trigger yet.)
        StepResult::Conflict(_) => StepResult::Saturated,
        // A Propagate is now passed through: the strip loops cite every
        // EUF-door merge into `just` (slice 37, un-banking approach B), so the
        // EUF merge the caller lands is fully justified. The one measured cost
        // slice 35 logged (hash 8e950d0d, qfs_predicates_matches_z3) is bought
        // back here.
        other => other,
    }
```

- [ ] **Step 6: Run the new test to verify it passes**

Run: `cargo nextest run -p shinri-str -E 'test(flattened_alias_residual_cites_euf_strip_merge)'`
Expected: discovery = 1 test; PASS.

- [ ] **Step 7: Update the two slice-35 downgrade tests to the new behavior**

These two tests asserted `Saturated`; the fixtures strip through the identity/literal door (no genuine merge), so post-slice-37 they propagate with the unchanged `just`. Replace `flattened_pure_assignment_does_not_propagate` (`wordeq.rs:1672-1701`) with:

```rust
/// Slice 37 (was slice 35's `..._does_not_propagate`): a pure-assignment
/// residual reached by FLATTENING a concat rep now PROPAGATES. This fixture's
/// only cancellation is none at all (`x` vs the constant word), so no EUF-door
/// strip runs and `just` is unchanged; the wrapper no longer downgrades it.
/// Control: `flattened_alias_residual_cites_euf_strip_merge` covers the case
/// where a strip DOES consume a merge and the leaf must appear.
#[test]
fn flattened_pure_assignment_now_propagates() {
    let mut ctx = Context::new();
    let mut eq = EqualityEngine::default();
    let x = declare_str_var(&mut ctx, "x_fpa");
    let a = ctx.mk_string_const("a");
    let b = ctx.mk_string_const("b");
    let concat = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, b])
        .unwrap();
    let lit = dummy_eqn_lit();
    let just = vec![EqLeaf::Asserted(lit)];
    let mut ctr = 0u32;
    let mut emitted = FxHashSet::default();
    let r = resolve_equation(
        &mut ctx,
        &mut eq,
        &[x],
        &[concat],
        just,
        lit,
        &mut ctr,
        &mut emitted,
    );
    match r {
        StepResult::Propagate { var, word, .. } => {
            assert_eq!(var, x, "the variable side is reported as `var`");
            assert_eq!(
                ctx.string_const_value(word),
                Some("ab"),
                "the flattened constant side folds to \"ab\""
            );
        }
        _ => panic!("a flattened pure assignment must now Propagate, not Saturate"),
    }
}
```

Replace `flattened_alias_residual_does_not_propagate` (`wordeq.rs:1707-1736`) with:

```rust
/// Slice 37 (was slice 35's `..._does_not_propagate`): the alias variant now
/// PROPAGATES. Flattening exposes a strippable constant head `"a"` that cancels
/// via the identity/literal door (no merge, no leaf), leaving the var–var
/// residual `[x] = [y]` that slice 34 merges. `just` is unchanged; the wrapper
/// passes the propagation through.
#[test]
fn flattened_alias_residual_now_propagates() {
    let mut ctx = Context::new();
    let mut eq = EqualityEngine::default();
    let x = declare_str_var(&mut ctx, "x_far");
    let y = declare_str_var(&mut ctx, "y_far");
    let a = ctx.mk_string_const("a");
    let concat = ctx
        .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, x])
        .unwrap();
    let lit = dummy_eqn_lit();
    let just = vec![EqLeaf::Asserted(lit)];
    let mut ctr = 0u32;
    let mut emitted = FxHashSet::default();
    let r = resolve_equation(
        &mut ctx,
        &mut eq,
        &[concat],
        &[a, y],
        just,
        lit,
        &mut ctr,
        &mut emitted,
    );
    assert!(
        matches!(r, StepResult::Propagate { var, word, .. } if var == x && word == y),
        "an alias residual off a flattened rep must now Propagate `x ≈ y`"
    );
}
```

Add the non-flattened invariance pin (right after the two above):

```rust
/// Slice 37: a strip through the identity/literal door must NOT enrich `just`
/// (the two self-justifying `same_explain` doors add no leaf). `[a, x] = [a, y]`
/// has no concat atom (non-flattened path) and its shared `"a"` head strips by
/// identity — the propagated `just` must be byte-identical to the input.
#[test]
fn non_flattened_literal_strip_leaves_just_unchanged() {
    let mut ctx = Context::new();
    let mut eq = EqualityEngine::default();
    let x = declare_str_var(&mut ctx, "x_inv");
    let y = declare_str_var(&mut ctx, "y_inv");
    let a = ctx.mk_string_const("a");
    let eqn_lit = dummy_eqn_lit();
    let just = vec![EqLeaf::Asserted(eqn_lit)];
    let mut ctr = 0u32;
    let mut emitted = FxHashSet::default();
    let r = resolve_equation(
        &mut ctx,
        &mut eq,
        &[a, x],
        &[a, y],
        just,
        eqn_lit,
        &mut ctr,
        &mut emitted,
    );
    match r {
        StepResult::Propagate { just, .. } => {
            assert_eq!(
                just,
                vec![EqLeaf::Asserted(eqn_lit)],
                "a self-justifying strip must leave `just` unchanged"
            );
        }
        _ => panic!("expected Propagate for the alias residual"),
    }
}
```

- [ ] **Step 8: Truth-up the doc comments**

In `resolve_equation`'s doc (`wordeq.rs:431-443`), rewrite item 3 to state the Propagate is now passed through with a strip-cited `just`, cross-referencing slice 37 / the slice-35 trigger, and note item 2 (Conflict) keeps its downgrade with its lift separately banked:

```rust
/// 2. If a concat atom WAS flattened and the inner resolver reports a CONFLICT,
///    downgrades it to `Saturated`. Such a conflict cites only the word-equation
///    literal, an under-cited global exclusion. This downgrade STAYS (slice 37
///    lifted only the Propagate sibling; the Conflict lift is separately banked
///    behind its own measured trigger). Purely structural conflicts on words
///    with NO concat atom are unaffected.
/// 3. If a concat atom WAS flattened and the inner resolver reports a PROPAGATE,
///    it is now PASSED THROUGH (slice 37, un-banking approach B). The strip
///    loops cite every EUF-class merge they consume into `just` via
///    `same_explain`, so the residual merge the caller lands is fully justified
///    — no longer the under-citation slice 35 fenced by downgrading to
///    `Saturated`. This restores the one measured completeness cost slice 35
///    logged (hash 8e950d0d, `qfs_predicates_matches_z3`).
```

In the `StepResult::Propagate` doc (`wordeq.rs:15-38`), update the sentence noting the caller merges under `EqJust::Interface` to add that `just` now includes the EUF-door strip antecedents (slice 37), not only the equation literal and normal-form antecedents.

- [ ] **Step 9: Run the whole `shinri-str` test module to verify no regression**

Run: `cargo nextest run -p shinri-str`
Expected: all tests pass, including the two renamed tests, the two new tests, and every existing `occurs_*`, `pure_assignment_*`, `alias_*`, forced-length, and skolem-fence pin. Confirm discovery count is unchanged except +2 (the two renamed tests keep the count; the two additions raise it by 2).

- [ ] **Step 10: Format and lint the crate**

Run: `cargo fmt --all` then `cargo clippy -p shinri-str --all-targets -- -D warnings`
Expected: no diff left unformatted; 0 clippy warnings.

- [ ] **Step 11: Commit**

```bash
git add crates/shinri-str/src/wordeq.rs
git commit -m "fix(str): slice37 T1 — cite EUF-door strips, lift flattened Propagate downgrade

same_explain appends eq.explain leaves for every strip cancelled through the
EUF-class door, threaded into resolve_inner's just. With the propagation now
fully justified, delete the resolve_equation wrapper's Propagate->Saturated arm
(un-banks approach B for the Propagate path; Conflict arm stays banked). Renames
the two slice-35 downgrade pins to their now-propagating behavior, adds a
leaf-level citation pin and a non-flattened invariance pin."
```

---

### Task 2: Differential measurement, full gate, and truth-up

**Files:**
- Modify (temporary, reverted): `crates/shinri-solver/tests/qfs_differential.rs`
- Modify: `docs/superpowers/specs/2026-07-21-shinri-slice37-strip-citation-propagate-design.md` (append measured outcomes)

**Interfaces:**
- Consumes: Task 1's landed behavior (flattened `Propagate` now flows through). No new symbols.
- Produces: the adjudicated measured-outcomes record; no code artifact.

- [ ] **Step 1: Capture the base commit and confirm a clean tree**

```bash
git -C /workspace status --porcelain      # expect empty
BASE=$(git -C /workspace rev-parse HEAD^)  # the commit before Task 1 (pre-slice-37 code)
echo "base=$BASE"
```

Expected: clean tree; `$BASE` is the commit immediately before Task 1's commit (identical code to `acf1bea5` for the string resolver — Task 1 is the first code change of this slice).

- [ ] **Step 2: Add temporary DIFFDUMP instrumentation on the fix side**

In `qfs_differential.rs`, in both `qfs_matches_z3` (after `ours` is computed, `~line 1391`) and `qfs_predicates_matches_z3` (after `ours` is computed, `~line 1505`), emit one dump line per iteration BEFORE any `continue`, so `unknown` verdicts are captured (essential to see the `unknown → sat` flip). Use a stable hash of the exact `body` string:

```rust
{
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    body.hash(&mut h);
    eprintln!("DIFFDUMP {:016x} {:?}", h.finish(), ours);
}
```

(The exact format is immaterial; what matters is that the SAME instrumentation is applied identically on both sides. Keep the two insertions byte-identical.)

- [ ] **Step 3: Run the fix-side dump and verify a non-zero line count**

```bash
cargo nextest run -p shinri-solver --features oracle \
  -E 'test(qfs_matches_z3) + test(qfs_predicates_matches_z3)' \
  --no-capture 2>/tmp/claude-1000/-workspace/0f25b7d5-72d3-4073-971e-58b58e422f7e/scratchpad/fix-raw.txt
grep -c '^DIFFDUMP ' /tmp/claude-1000/-workspace/0f25b7d5-72d3-4073-971e-58b58e422f7e/scratchpad/fix-raw.txt
```

Expected: discovery = 2 tests (NOT 0 — confirm the oracle feature actually enabled them); the `grep -c` line count is **non-zero** (~600: 300 + 300 iters). If it is 0, `--nocapture`/`--no-capture` did not take effect or the feature gate ran 0 tests — stop and fix before diffing. Extract and sort:

```bash
grep '^DIFFDUMP ' /tmp/.../scratchpad/fix-raw.txt | sort \
  > /tmp/.../scratchpad/fix-sorted.txt
```

- [ ] **Step 4: Revert the fix-side instrumentation**

```bash
git -C /workspace checkout -- crates/shinri-solver/tests/qfs_differential.rs
git -C /workspace status --porcelain   # expect empty
```

- [ ] **Step 5: Dump the base side in a worktree with the SAME instrumentation**

```bash
git -C /workspace worktree add /tmp/.../scratchpad/base-wt "$BASE"
```

Apply the byte-identical instrumentation from Step 2 to `base-wt/crates/shinri-solver/tests/qfs_differential.rs`, then:

```bash
cd /tmp/.../scratchpad/base-wt && cargo nextest run -p shinri-solver --features oracle \
  -E 'test(qfs_matches_z3) + test(qfs_predicates_matches_z3)' \
  --no-capture 2>/tmp/.../scratchpad/base-raw.txt
grep -c '^DIFFDUMP ' /tmp/.../scratchpad/base-raw.txt          # non-zero, ~same count
grep '^DIFFDUMP ' /tmp/.../scratchpad/base-raw.txt | sort \
  > /tmp/.../scratchpad/base-sorted.txt
```

Expected: non-zero, ~same line count as the fix side.

- [ ] **Step 6: Diff base vs fix and adjudicate**

```bash
diff /tmp/.../scratchpad/base-sorted.txt /tmp/.../scratchpad/fix-sorted.txt
```

Expected outcome to CONFIRM: the trigger hash `8e950d0d36e258cb` moves `Unknown` (base) → `Sat` (fix) in the `qfs_predicates_matches_z3` family, and z3 agrees (the surrounding test still reports `0 disagreements`). Its derived witness sub-query reappears once the primary is `Sat`.

**Halt-and-adjudicate tripwires** (any one blocks the merge pending human review):
- Any `sat ↔ unsat` disagreement panic from either `..._matches_z3` test (soundness).
- Any `bail` increase: compare the `n_guard_bailout` tallies printed by `qfs_predicates_matches_z3` on both sides — a fix-side increase is the analyzability-guard signal from spec §3c (both paths, Conflict clauses included).
- Any `decided → unknown` flip in the diff (this slice must not spend completeness).
- Any hash movement other than the expected trigger flip: enumerate each, name its family, and adjudicate before proceeding.

- [ ] **Step 7: Tear down the base worktree**

```bash
cd /workspace && git worktree remove --force /tmp/.../scratchpad/base-wt
git -C /workspace status --porcelain   # expect empty (fix-side instrumentation already reverted in Step 4)
```

- [ ] **Step 8: Run the oracle suite clean (no instrumentation) foreground**

```bash
cargo nextest run -p shinri-solver --features oracle 2>&1 | tail -30
```

Expected: a **non-zero** test count (confirm the feature gate engaged — a 0-test run is not coverage); all pass; the `..._matches_z3` families print `0 disagreements`.

- [ ] **Step 9: Run `script_e2e`**

```bash
cargo nextest run -p shinri-solver -E 'binary(script_e2e)'
```

Expected: discovery is non-zero (confirm); all pass (prior count + any this slice adds). A z3-confirmed `unknown → sat` pin flip is an adjudicated flip, not a blocker; a `sat`/`unsat` disagreement is a blocker.

- [ ] **Step 10: Full workspace gate**

```bash
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo nextest run --workspace
```

Expected: fmt clean; 0 clippy warnings; all pass, 7 skipped (the `#[ignore]`d nightly `shinri-fp` exhaustives); wall-clock within the 10–15 min blocking-tier budget.

- [ ] **Step 11: Append the measured-outcomes truth-up to the spec and commit**

Add a `## 8. Measured outcomes` section to `docs/superpowers/specs/2026-07-21-shinri-slice37-strip-citation-propagate-design.md` recording: the exact base commit, the DIFFDUMP line counts both sides, the enumerated sorted-diff (the confirmed trigger flip and its witness sub-query, plus any other adjudicated movement), the `n_guard_bailout` tallies both sides (proving no bail increase), the oracle `0 disagreements` confirmation, the `script_e2e` result, and the full-gate result with wall-clock. State the adjudication verdict (clear-to-merge or blocked-with-reason).

```bash
git add docs/superpowers/specs/2026-07-21-shinri-slice37-strip-citation-propagate-design.md
git commit -m "docs(str): slice37 truth-up — measured outcomes

Records the dump-and-diff (trigger hash 8e950d0d unknown->sat, z3-agreeing),
no bail increase on either path, oracle 0-disagreements, script_e2e, and the
full-gate result."
```

---

## Self-Review

**Spec coverage:**
- §1 trigger / mandate → Task 2 Step 6 confirms hash `8e950d0d` `unknown → sat`.
- §2 in-scope strip-explain + wrapper lift → Task 1 Steps 3–5.
- §2 out-of-scope Conflict downgrade untouched → Task 1 Step 5 keeps the `Conflict` arm; Step 8 doc says so; §7 success criterion 5.
- §3a strip-explain (two self-justifying doors) → Task 1 Step 3 (`same_explain`); pinned by Step 7's `non_flattened_literal_strip_leaves_just_unchanged`.
- §3b lift on flattened path → Task 1 Step 5.
- §3c shared, both-paths, measured (bail tripwire) → Task 2 Step 6 bail-tally comparison.
- §4a unit pins (leaf-level, invariance, passthrough, existing pins) → Task 1 Steps 1, 7, 9.
- §4b dump-and-diff both suites, `--nocapture`, line-count check → Task 2 Steps 2–6.
- §4c oracle foreground, `script_e2e`, filter discovery, full gate → Task 2 Steps 8–10.
- §7 success criteria → Task 2 Steps 6, 8–10.

**Placeholder scan:** No TBD/TODO; every code step shows complete code; commands have expected output. The `/tmp/.../scratchpad/` path is abbreviated after its first full spelling in Task 2 Step 3 — expand it to the full scratchpad path `/tmp/claude-1000/-workspace/0f25b7d5-72d3-4073-971e-58b58e422f7e/scratchpad` at execution time.

**Type consistency:** `same_explain` signature identical in the interface block, Step 3, and Step 4 call sites. `StepResult::Propagate { var, word, just }` field names match `wordeq.rs:34-38`. `EqLeaf::Asserted(Lit)` / `EqJust::Asserted(Lit)` match `types.rs:40-59`. `eq.merge(...) -> Result` (its `Err` is ignored with `let _ =`) matches the existing `same_var_via_euf_merge_forced_length_is_conflict` fixture. `StepResult` has no `Debug`, so no panic arm formats it.
