# Slice 38 — Split passthrough audit — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Guard the two word-equation F-split emission sites so a Split reached through a non-identity EUF-door strip downgrades to `Saturated`, closing an under-guarded (wrong-UNSAT-shaped) learnt clause.

**Architecture:** The fix lives entirely inside `resolve_inner` (`crates/shinri-str/src/wordeq.rs`). `same_explain` grows the `just` citation vector *only* on the EUF door (identity and equal-literal strips push nothing), so `just.len()` growing across the strip loops is an exact, free signal that a non-identity class equality was load-bearing for the residual. Snapshot the length at entry; at each F-split emission site, if `just` grew, return `Saturated` instead of `Split`, before recording the dedup key. This covers both the flattened and non-flattened resolver paths with no change to `StepResult` or the wrapper match arms.

**Tech Stack:** Rust, `cargo nextest`, `mise` tasks. String theory crate `shinri-str`; oracle differential in `shinri-solver` (feature-gated); z3/cvc5 via `mise`.

## Global Constraints

- Pure-Rust mandate: no native-link deps (`deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`). Verbatim.
- Blocking PR tier budget: **10–15 min wall-clock** (CI hard cap 20 min). Any test measured **>5 min** must be `#[ignore = "exhaustive: nightly tier (~N min in CI)"]`d.
- Never remove `#[ignore]` from the exhaustive `shinri-fp` suites.
- Oracle differential is feature-gated: `cargo nextest run -p shinri-solver --features oracle`. **Without `--features oracle` it silently runs 0 tests** — confirm a non-zero test count before reporting green.
- `cargo fmt --all` before pushing (CI gates on `fmt --check`). `cargo clippy --workspace --all-targets -- -D warnings` must be clean.
- nextest filter syntax: use `-E 'test(name)'` (the positional `mod::name` form finds 0 tests on nextest 0.9.140; a 0-test run reads as green).
- dump-and-diff instrumentation needs `--no-capture` or `eprintln` is swallowed on passing runs (0 lines, still "green"). Identify triggers by **family + direction + count**, never by an absolute `DefaultHasher` digest (digests are instrumentation-scoped).
- Feature work on a slice branch `slice38-split-passthrough-audit` with a PR to `main`; merge with a merge commit when CI green, then delete the branch remote + local + prune. The spec+plan are already committed to `main`.

---

## Preamble: create the slice branch

- [ ] **Step 1: Branch from up-to-date main**

```bash
git checkout main && git pull --ff-only
git checkout -b slice38-split-passthrough-audit
```

---

## Task 1: The just-growth guard + wrapper doc + unit fences

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs` — `resolve_inner` (entry snapshot ~`:578`; char-peel Split site ~`:911`; generic F-split site ~`:957`); wrapper doc comment ~`:469-481`.
- Test: `crates/shinri-str/src/wordeq.rs` `#[cfg(test)] mod tests` (append three tests).

**Interfaces:**
- Consumes: `resolve_equation(terms: &mut Context, eq: &mut EqualityEngine, lhs: &[TermId], rhs: &[TermId], just: Vec<EqLeaf>, eqn_lit: Lit, fresh_ctr: &mut u32, emitted: &mut FxHashSet<(TermId, TermId)>) -> StepResult`. `StepResult::{Split { atoms, guard }, Saturated, Propagate { .. }, Conflict(..), Done}`. `same_explain(terms, eq, a, b, out: &mut Vec<EqLeaf>) -> bool` pushes antecedent leaves only on the EUF door.
- Produces: no signature change. Behavioural contract: a Split whose residual was reached through an EUF-door strip (`just` grew during stripping) now returns `Saturated` and does **not** record the head-pair dedup key.

- [ ] **Step 1: Write the three failing/pinning tests**

Append to the `mod tests` block in `crates/shinri-str/src/wordeq.rs` (mirrors the existing `flattened_alias_residual_cites_euf_strip_merge` fixture at `wordeq.rs:1820`):

```rust
    /// Slice 38: a char-peel F-split reached through a NON-IDENTITY EUF-door
    /// strip is under-guarded (its `¬eqn`-only clause omits the strip's class
    /// equality `p≈q`). It must downgrade to `Saturated`, not emit `Split`.
    /// `p ≈ q` is merged (antecedent `merge_lit`); the head strip cancels p
    /// against q via the EUF door, growing `just`; the residual `[x, x2] = ["b"]`
    /// would otherwise char-peel-split on the (x, "b") pair.
    #[test]
    fn charpeel_split_after_euf_strip_downgrades_to_saturated() {
        use shinri_theory::types::EqJust;
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let p = mk_var(&mut ctx, "p_s38a");
        let q = mk_var(&mut ctx, "q_s38a");
        let x = mk_var(&mut ctx, "x_s38a");
        let x2 = mk_var(&mut ctx, "x2_s38a");
        let b = ctx.mk_string_const("b");
        let merge_lit = Lit::new(Var::new(1), true);
        let pn = eq.intern(p);
        let qn = eq.intern(q);
        let _ = eq.merge(pn, qn, EqJust::Asserted(merge_lit));
        let eqn_lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(eqn_lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx, &mut eq, &[p, x, x2], &[q, b], just, eqn_lit, &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Saturated),
            "char-peel split reached through an EUF-door strip must downgrade to Saturated, got {r:?}"
        );
        assert!(
            emitted.is_empty(),
            "downgrade must NOT record the dedup key (a later clean round must be able to split)"
        );
    }

    /// Slice 38: same under-guard, generic (two-variable-head) F-split site.
    /// Residual `[x, x2] = [w]` would otherwise emit the generic Nielsen split.
    #[test]
    fn generic_fsplit_after_euf_strip_downgrades_to_saturated() {
        use shinri_theory::types::EqJust;
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let p = mk_var(&mut ctx, "p_s38b");
        let q = mk_var(&mut ctx, "q_s38b");
        let x = mk_var(&mut ctx, "x_s38b");
        let x2 = mk_var(&mut ctx, "x2_s38b");
        let w = mk_var(&mut ctx, "w_s38b");
        let merge_lit = Lit::new(Var::new(1), true);
        let pn = eq.intern(p);
        let qn = eq.intern(q);
        let _ = eq.merge(pn, qn, EqJust::Asserted(merge_lit));
        let eqn_lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(eqn_lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx, &mut eq, &[p, x, x2], &[q, w], just, eqn_lit, &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Saturated),
            "generic F-split reached through an EUF-door strip must downgrade to Saturated, got {r:?}"
        );
        assert!(emitted.is_empty(), "downgrade must NOT record the dedup key");
    }

    /// Slice 38: the guard keys on the EUF door specifically, NOT on stripping
    /// in general. An IDENTITY strip (same TermId `x` cancels against `x`) pushes
    /// no leaf, so `just` does not grow and the residual char-peel split still
    /// fires. Pins that the guard does not over-fire (correct at base AND fix).
    #[test]
    fn identity_strip_split_still_emits() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = mk_var(&mut ctx, "x_s38c");
        let y = mk_var(&mut ctx, "y_s38c");
        let y2 = mk_var(&mut ctx, "y2_s38c");
        let b = ctx.mk_string_const("b");
        let eqn_lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(eqn_lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        // Head strip cancels x against x (identity door → no `just` growth);
        // residual [y, y2] = ["b"] char-peels on (y, "b").
        let r = resolve_equation(
            &mut ctx, &mut eq, &[x, y, y2], &[x, b], just, eqn_lit, &mut ctr,
            &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Split { .. }),
            "an identity-strip F-split must still emit Split (guard must not over-fire), got {r:?}"
        );
    }
```

- [ ] **Step 2: Run the tests to verify the two downgrade tests fail**

Run:
```bash
cargo nextest run -p shinri-str -E 'test(charpeel_split_after_euf_strip_downgrades_to_saturated) + test(generic_fsplit_after_euf_strip_downgrades_to_saturated) + test(identity_strip_split_still_emits)'
```
Expected: 3 tests discovered (confirm the count is 3, not 0). The two `..._downgrades_to_saturated` tests **FAIL** (they get `StepResult::Split { .. }` at base, assert `Saturated`). `identity_strip_split_still_emits` **PASSES** (documents current-correct behaviour that must be preserved).

- [ ] **Step 3: Add the entry snapshot in `resolve_inner`**

In `crates/shinri-str/src/wordeq.rs`, at the very start of `resolve_inner`'s body (immediately after the `let (mut i, mut j) = (0usize, 0usize);` / `let (mut le, mut re) = ...` lines, before the head-strip loop), add:

```rust
    // SLICE 38: snapshot the citation count BEFORE the strip loops. `same_explain`
    // grows `just` only on the EUF door (identity/equal-literal doors push
    // nothing — see `same_explain`), and nothing between here and the F-split
    // emission sites below pushes to `just` except the strip loops. So
    // `just.len() > incoming_just` at an F-split site means a non-identity class
    // equality was load-bearing for the residual — the F-split's `¬eqn`-only
    // clause would omit it (under-guarded, wrong-UNSAT shape). Guard both sites.
    let incoming_just = just.len();
```

- [ ] **Step 4: Guard the char-peel F-split site**

Find the char-peel emission block, `if let Some((var, cst)) = vc_pair {` (~`wordeq.rs:911`). Insert the guard as the FIRST statement inside that block, before `ch`/`key` are computed:

```rust
        if let Some((var, cst)) = vc_pair {
            // SLICE 38: under-guard check — a residual reached through an EUF-door
            // strip makes this char-peel clause depend on the stripped class
            // equality, which the `¬eqn` guard omits. Wait for SAT instead. Do
            // NOT record the dedup key: a later round whose class state no longer
            // needs the strip can emit the split cleanly.
            if just.len() > incoming_just {
                return StepResult::Saturated;
            }
            // Extract first character of the constant ...
```

- [ ] **Step 5: Guard the generic F-split site**

Find the generic emission block, `if var_head {` (~`wordeq.rs:957`). Insert the same guard as the FIRST statement inside that block, before `key`/`fsplit_atoms`:

```rust
        if var_head {
            // SLICE 38: same under-guard check as the char-peel site above.
            if just.len() > incoming_just {
                return StepResult::Saturated;
            }
            // Canonical (unordered) key for dedup.
            let key = if ha.index() <= hb.index() {
```

- [ ] **Step 6: Update the wrapper doc comment**

In the `resolve_equation` doc comment (`wordeq.rs:469-481`), append a fourth numbered point after point 3:

```rust
/// 4. `Split` (both the char-peel and generic F-split) is now guarded INSIDE
///    `resolve_inner` (slice 38): a split reached through a non-identity
///    EUF-door strip downgrades to `Saturated`, because its `¬eqn`-only learnt
///    clause omits the stripped class equality (an under-guarded, wrong-UNSAT
///    shape a learnt clause — unlike a `Propagate` merge — is not backstopped by
///    the model gate). The guard lives in the inner resolver, so it covers BOTH
///    this flattened path and the direct non-flattened path; the wrapper needs
///    no `Split` arm of its own.
```

- [ ] **Step 7: Run the three tests to verify they pass**

Run:
```bash
cargo nextest run -p shinri-str -E 'test(charpeel_split_after_euf_strip_downgrades_to_saturated) + test(generic_fsplit_after_euf_strip_downgrades_to_saturated) + test(identity_strip_split_still_emits)'
```
Expected: 3 discovered, 3 PASS.

- [ ] **Step 8: Run the full `shinri-str` suite to check for local regressions**

Run:
```bash
cargo nextest run -p shinri-str
```
Expected: all pass (the existing `variable_head_is_done_not_conflict`, `flattened_alias_residual_cites_euf_strip_merge`, and the char-peel/propagation pins are unaffected — none of them strips through the EUF door before an F-split, or they land Propagate/Conflict which are untouched). If any pre-existing test now fails, STOP: that is a measured completeness cost — record the failing test + its shape and adjudicate before continuing (do not weaken the assertion).

- [ ] **Step 9: fmt + clippy**

Run:
```bash
cargo fmt --all
cargo clippy -p shinri-str --all-targets -- -D warnings
```
Expected: fmt makes no complaint on re-run; clippy clean.

- [ ] **Step 10: Commit**

```bash
git add crates/shinri-str/src/wordeq.rs
git commit -m "fix(str): slice38 T1 — guard F-split emission through EUF-door strips

A word-equation F-split reached after a non-identity EUF-door strip has a
¬eqn-only learnt clause that omits the stripped class equality (under-guarded,
wrong-UNSAT shape; a learnt clause is not backstopped by the model gate).
Snapshot just.len() at resolve_inner entry; downgrade both the char-peel and
generic F-split sites to Saturated when just grew, before recording the dedup
key. Covers the flattened and non-flattened paths. Unit fences pin both
downgrades and that an identity strip still emits Split."
```

---

## Task 2: Measurement — dump-and-diff, oracle, script_e2e, best-effort e2e repro

**Files:**
- Temporarily modify: `crates/shinri-str/src/wordeq.rs` (instrumentation `eprintln`s at the two guard sites — reverted in Task 3).
- Possibly create: `crates/shinri-solver/tests/script_e2e.rs` (an e2e pin, only if a repro is found).

**Interfaces:**
- Consumes: the guard from Task 1.
- Produces: a measured-outcomes record (dump-and-diff tallies, oracle/script_e2e results, e2e-repro found/not-found with shapes tried) to be written into the spec in Task 3.

- [ ] **Step 1: Add temporary instrumentation at the two guard sites**

At each guard site added in Task 1, insert an `eprintln` on the line that would fire, tagged by **family + direction + count** (NOT a hash). Keep a process-local counter via a `static`:

```rust
            if just.len() > incoming_just {
                // SLICE 38 DIFFDUMP (temporary — reverted in Task 3): count how
                // often the guard fires, and on which site. Identify by family +
                // count, not by a DefaultHasher digest (instrumentation-scoped).
                eprintln!("S38GUARD site=charpeel grew={} -> saturated", just.len() - incoming_just);
                return StepResult::Saturated;
            }
```
(and analogously `site=generic` at the other site.)

- [ ] **Step 2: Run the oracle differential with `--no-capture` and confirm a non-zero test count**

Run:
```bash
cargo nextest run -p shinri-solver --features oracle --no-capture 2>&1 | tee /tmp/claude-1000/-workspace/*/scratchpad/s38-oracle.log | tail -40
```
Expected: a NON-ZERO "tests run" count (0 = the oracle gate did not engage — not coverage). Record: total tests, pass/fail, and every `S38GUARD` line (count per site). Any `sat ↔ unsat` disagreement is a HARD BLOCKER — stop and diagnose. A `decided → unknown` flip must be z3-adjudicated (see Step 4).

- [ ] **Step 3: Run `script_e2e` and confirm non-zero discovery**

Run:
```bash
cargo nextest run -p shinri-solver -E 'binary(script_e2e)' --no-capture 2>&1 | tail -30
```
Expected: non-zero discovery, all pass. Record any pin whose answer moved and confirm with z3 (adjudicated flip, not a blocker unless it is a `sat ↔ unsat` disagreement).

- [ ] **Step 4: Adjudicate any `decided → unknown` flip**

For each pin or oracle case whose answer moved from a decided verdict to `unknown` (the only regression this fix can cause — it only removes a lemma), extract the SMT script and run it through z3/cvc5 (via the oracle harness or `mise`-provided binaries). If z3 agrees the correct answer is what the fixed solver now returns, OR z3 also cannot decide, it is an accepted completeness cost — record the case shape and the z3 verdict. If the fixed solver now returns a *wrong* answer, STOP: the guard is mis-scoped.

- [ ] **Step 5: Best-effort end-to-end wrong-UNSAT repro (time-boxed)**

Attempt to construct an SMT script whose BASE (pre-Task-1) run answers a wrong `unsat` that the fixed run turns to `sat`/`unknown`, by forcing a non-identity EUF-door strip ahead of an F-split. Candidate shapes to try (record which were attempted and the outcome):
  - a prior alias propagation `(assert (= u v))` so `u`/`v` align as cancellable heads, with a residual whose F-split clause, minus the `u≈v` guard, excludes an otherwise-satisfiable assignment;
  - a flattened concat rep: `(assert (= s (str.++ t "x")))` so `rep(s)` is a CONCAT that flattens and strips against the other side via the EUF door before an F-split.

Run each candidate on the base commit and the Task-1 commit:
```bash
# on base (git stash Task 1 or checkout the pre-fix commit) and on fix:
cargo run -p shinri-solver -- /path/to/candidate.smt2   # or the project's script runner
```
If a repro is found: minimize it and hold it for Task 3's `script_e2e` pin. If none is found within the time-box, record the negative result and the shapes tried (this is the expected outcome for a never-observed window; the unit fences in Task 1 remain the mechanism proof).

- [ ] **Step 6: Commit the measurement artifacts (if any e2e pin was found)**

If a repro was found, add it to `crates/shinri-solver/tests/script_e2e.rs` as a pin asserting the corrected answer, run it, and commit:
```bash
cargo nextest run -p shinri-solver -E 'binary(script_e2e)'
git add crates/shinri-solver/tests/script_e2e.rs
git commit -m "test(str): slice38 T2 — e2e pin: wrong-UNSAT prevented by the F-split guard"
```
If no repro was found, there is nothing to commit in this step — proceed to Task 3 (the finding is recorded there).

---

## Task 3: Truth-up, de-instrument, full gate, merge prep

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs` (remove the Task-2 instrumentation `eprintln`s + `static` counter).
- Modify: `docs/superpowers/specs/2026-07-22-shinri-slice38-split-passthrough-audit-design.md` (add a measured-outcomes section).

**Interfaces:**
- Consumes: the measurement record from Task 2.
- Produces: a clean, de-instrumented tree passing the full workspace gate, and a spec whose success criteria (§7) are marked against measured results.

- [ ] **Step 1: Remove the temporary instrumentation**

Delete the `S38GUARD` `eprintln` lines and any `static` counter added in Task 2, restoring the two guard sites to the plain `if just.len() > incoming_just { return StepResult::Saturated; }` form from Task 1.

- [ ] **Step 2: Re-run the guard unit tests to confirm de-instrumentation didn't disturb them**

Run:
```bash
cargo nextest run -p shinri-str -E 'test(charpeel_split_after_euf_strip_downgrades_to_saturated) + test(generic_fsplit_after_euf_strip_downgrades_to_saturated) + test(identity_strip_split_still_emits)'
```
Expected: 3 discovered, 3 PASS.

- [ ] **Step 3: Add the measured-outcomes section to the spec**

Append a `## 8. Measured outcomes` section to `docs/superpowers/specs/2026-07-22-shinri-slice38-split-passthrough-audit-design.md` recording, verbatim from Task 2: the dump-and-diff `S38GUARD` counts per site (or "guard never fired on the suite"); the oracle differential total test count + pass/fail + any adjudicated flip with its z3 verdict; the `script_e2e` result; and the best-effort e2e-repro outcome (the found repro's file, or "not found within time-box; shapes attempted: …"). Mark each §7 success criterion satisfied / not-applicable against the measurements. Do not paste any absolute `DefaultHasher` digest as a trigger identity.

- [ ] **Step 4: Full workspace gate**

Run:
```bash
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo nextest run --workspace
```
Expected: fmt clean (exit 0); clippy 0 warnings; workspace run all pass with only the five `#[ignore]`d `shinri-fp` exhaustives skipped. Record the wall-clock — must be within the 10–15 min blocking-tier budget. If it exceeds, STOP and re-tier.

- [ ] **Step 5: Commit the truth-up + de-instrumentation**

```bash
git add crates/shinri-str/src/wordeq.rs docs/superpowers/specs/2026-07-22-shinri-slice38-split-passthrough-audit-design.md
git commit -m "docs+fix(str): slice38 T3 — truth-up measured outcomes, remove instrumentation

Records the dump-and-diff guard-fire counts, oracle/script_e2e results, and the
best-effort e2e-repro outcome; removes the temporary DIFFDUMP instrumentation."
```

- [ ] **Step 6: Push and open the PR**

```bash
git push -u origin slice38-split-passthrough-audit
gh pr create --fill --base main
```

- [ ] **Step 7: Merge on green, then clean up**

Once CI is green (per the standing merge-on-green rule), merge with a merge commit and delete the branch:
```bash
gh pr merge --merge --delete-branch
git checkout main && git pull --ff-only
git branch -d slice38-split-passthrough-audit 2>/dev/null || true
git remote prune origin
```

---

## Self-review notes (author checklist, done)

- **Spec coverage:** §2 fix → Task 1 (snapshot + two guards + wrapper doc). §5 verification → Task 2 (dump-and-diff/oracle/script_e2e) + Task 3 Step 4 (full gate). §6 testing → Task 1 unit fences (both downgrades + over-fire pin) + Task 2 Step 5 (best-effort repro). §7 success criteria → Task 3 Step 3 marks each against measurement. §3/§4 scope fence → no code touches `StepResult`, wrapper arms, or Conflict/Propagate paths (Task 1 confined to `resolve_inner` + doc).
- **Placeholder scan:** every code step shows the exact code; every run step shows the exact command + expected output; no TBD/TODO.
- **Type consistency:** `incoming_just` (usize) defined in Task 1 Step 3, consumed in Steps 4–5; `StepResult::Saturated` / `StepResult::Split { .. }` match the enum at `wordeq.rs:14`/`:51`; `mk_var`, `dummy_eqn_lit`, `EqJust::Asserted`, `eq.intern`/`eq.merge`, `Lit::new`/`Var::new` all match the existing `flattened_alias_residual_cites_euf_strip_merge` fixture.
