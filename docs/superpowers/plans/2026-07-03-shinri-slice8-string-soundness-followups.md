# Shinri slice 8 — string-soundness follow-ups Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the string differential oracle run clean (0 disagreements, 0 debug panics) at seed `0xB000_9E38`, by closing three pre-existing soundness clusters, then advance the seed.

**Architecture:** Three independent soundness fixes across three crates — `shinri-sat` (analyze/backtrack robustness), `shinri-theory` (residual diseq-map undo gap), `shinri-str` (disequality empty-length link over concats) — each isolated by an in-hand repro, each pinned, then a seed bump in the oracle harness. Panics are fixed before the wrong-verdict and the re-baseline so the debug sweep never aborts.

**Tech Stack:** Rust (workspace, edition 2021, rust-version 1.96.0), z3 4.16.0 on PATH for the `oracle` feature, `cargo test`.

## Global Constraints

- Never a wrong verdict: any theory may answer `Unknown` (sound), but must never return `Sat`/`Unsat` that disagrees with z3. A sound-Unknown is an acceptable outcome; a wrong Sat/Unsat is a bug.
- Every diseq-map / SAT-state mutation must be **exactly reversible** on `pop`/backtrack (the invariant clusters B and C both violate).
- Keep each fix's blast radius to the offending branch + its undo/reset arm, mirroring the slice-7 `InsertOverwrite`/`RekeyOverwrite` fixes.
- Debug builds must not panic on any generated string-oracle input at seed `0xB000_9E38`.
- Verification net (fence-canary memory): pre-flight canary re-grep before editing; `cargo test --workspace` 0-failed; oracle sweep 0-disagreement/0-panic; `clippy` 0 net-new; keep changes local (standing choice — no push).
- Repros for all three clusters are in `.superpowers/sdd/slice8-repro-findings.md` (git-ignored, local).
- Progress ledger: `.superpowers/sdd/progress-slice8.md` (create in Task 0; update after each task).

---

## Task 0: Pre-flight — canary hunt + progress ledger

**Files:**
- Create: `.superpowers/sdd/progress-slice8.md`
- Read only: the three fix-site files + all string/eq test files

**Interfaces:**
- Produces: a list of canary tests pinned to the CURRENT (wrong/panicking) behavior on the touched shapes, recorded in the ledger; each later task nets any that flip.

- [ ] **Step 1: Confirm clean base + the three repros still fire**

Run each repro in `.superpowers/sdd/slice8-repro-findings.md` through the debug CLI and record the panic site / verdict:

```bash
cd /workspace
git status --short   # expect clean; seed at 0xB000_9E37
# cluster C repro (seed 9E38 iter 1524-shape):
printf '%s\n' '(declare-const s1 String)(declare-const s2 String)(declare-const s3 String)' \
  '(assert (distinct (str.++ s3 "b") (str.++ s3 "a")))' \
  '(assert (and (= (str.++ s3 "a") s2) (= s1 s1 "")))' \
  '(assert (distinct (str.++ s2 "a") (str.++ s2 "b")))' \
  '(assert (not (distinct (str.++ s2 "b") "" s3 (str.++ s1 "a"))))' \
  '(check-sat)' > /tmp/c.smt2
cargo run -q -p shinri-cli -- /tmp/c.smt2 2>&1 | grep -m1 "panicked at"
```
Expected: `eq_engine.rs:379` panic (cluster C). Repeat for cluster A (task-4b §6 input → `unsat`, z3 `sat`) and cluster B (seed 9E38 iter 1013 input → `trail.rs:91` panic).

- [ ] **Step 2: Enumerate canaries pinned to current behavior**

Run: `grep -rn "empty_length_link\|constrained_len_with_diseq\|explain\|not connected\|backtrack above\|premature\|distinct" crates/*/tests crates/*/src --include=*.rs | grep -i "test\|assert\|expect"`

Record in the ledger the tests that assert the CURRENT verdict/behavior on touched shapes — especially:
- `crates/shinri-solver/tests/qfs_differential.rs::targeted_empty_length_link_unsat` (pins `len=0 ∧ x≠"" → UNSAT` — CORRECT, must stay UNSAT after cluster A).
- `crates/shinri-solver/tests/qfs_differential.rs::targeted_constrained_len_with_diseq_stays_sat` (pins `len=k>0 ∧ x≠"" → SAT` — must stay SAT).
- `crates/shinri-theory/src/eq_engine.rs` diseq-undo unit tests (must stay green after cluster C).

- [ ] **Step 3: Write the ledger and commit**

Create `.superpowers/sdd/progress-slice8.md` with: base commit, the three confirmed repros + panic sites, the canary list. (This dir is git-ignored — no commit; it is the local working ledger.)

---

## Task 1: Cluster B — `analyze`/backtrack robustness (shinri-sat)

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs` (the `TheoryResult::Conflict` arm ~559–588 and/or `analyze` ~275–348)
- Modify: `crates/shinri-sat/src/analyze.rs` (`ensure_vars`, ~14) if the guard lands there
- Test: `crates/shinri-solver/tests/qfs_differential.rs` (new `targeted_*` no-panic pin)

**Interfaces:**
- Consumes: `Solver::analyze(&mut self, Conflict) -> (Vec<Lit>, u32, Vec<ClauseId>)` (solver.rs:275); `Analyzer::ensure_vars(&mut self, n: usize)` (analyze.rs:14); `TheoryResult::Conflict(Vec<Lit>)` (solver.rs:559).
- Produces: a `Solver` that never OOBs `seen` nor returns a backjump level `> decision_level()` from a theory conflict.

- [ ] **Step 1: Add the failing no-panic pin**

In `crates/shinri-solver/tests/qfs_differential.rs`, next to the other `targeted_*` tests, add (using the existing `expect_not_unsat` helper, which calls `shinri_verdict` and panics if the solver panics):

```rust
#[test]
fn targeted_analyze_theory_conflict_no_panic() {
    // Cluster B (slice 8): a string-theory Conflict drove `analyze` to a bad
    // backjump level → `trail.rs:91` "backtrack above current level" in debug.
    // The correct verdict is SAT (z3); at minimum shinri must NOT panic and must
    // NOT return a wrong UNSAT.
    expect_not_unsat(
        "(set-logic QF_S)\
         (declare-const s1 String)(declare-const s2 String)(declare-const s3 String)\
         (assert (not (distinct (str.++ s2 \"a\") (str.++ s2 \"a\") s2 (str.++ s1 \"a\"))))\
         (assert (and (distinct (str.++ s3 \"a\") (str.++ s3 \"b\") (str.++ s2 \"a\")) (= s3 (str.++ s1 \"b\"))))\
         (assert (not (= (str.++ s3 \"a\") s1 s3)))\
         (assert (and (distinct (str.++ s3 \"b\") (str.++ s3 \"a\")) (distinct (str.++ s1 \"b\") s2 (str.++ s3 \"a\"))))\
         (check-sat)",
    );
}
```

- [ ] **Step 2: Run the pin to verify it fails (panics in debug)**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_analyze_theory_conflict_no_panic -- --nocapture`
Expected: FAIL — panic at `trail.rs:91` (or `solver.rs:293`).

- [ ] **Step 3: Root-cause — instrument the theory-conflict → analyze path**

In the `TheoryResult::Conflict(lits)` arm (solver.rs:559), temporarily log `lits`, each lit's `var().index()`, `self.assign.num_vars()`, `self.analyzer.seen.len()`, each var's `assign.level(v)`, and `self.trail.decision_level()` before `reduce_to_conflict_level` and before `analyze`. Determine which invariant breaks:
- **(i) var-range:** some `lits` var index ≥ `analyzer.seen.len()` → the OOB — a theory conflict cites a var never registered via `new_var()`.
- **(ii) level:** `reduce_to_conflict_level` leaves the conflict's max level `<` current, or `analyze`'s computed `bt` exceeds `decision_level()` after backtrack — the `trail.rs:91` assert.

Record which in the ledger. Remove instrumentation before Step 4.

- [ ] **Step 4: Implement the fix (shape decided by Step 3)**

For **(i)**: route the offending literal through registration (call `new_var()`/`ensure_vars` at the point the theory mints it), so `seen`/watches/heuristic all cover it. Defensive floor to keep regardless — at the top of the `Conflict` arm before `analyze`:

```rust
// Cluster B (slice 8): a theory conflict must only cite already-registered vars.
// Grow analyzer state defensively and assert the invariant so an unregistered
// var surfaces as a clear failure, never a silent OOB / wrong learnt clause.
self.analyzer.ensure_vars(self.assign.num_vars());
debug_assert!(
    conflict_lits.iter().all(|l| l.var().index() < self.assign.num_vars()),
    "theory Conflict cites an unregistered var"
);
```

For **(ii)**: fix `reduce_to_conflict_level` / the `bt` computation so `analyze` returns a backjump level `≤ decision_level()` and every current-level pivot exists (guard the `reduce_to_conflict_level` result path per the existing comment at solver.rs:564–573). Add `debug_assert!(bt <= self.trail.decision_level())` after `analyze`.

Keep whichever guards make the invariant structural; both are cheap and sound.

- [ ] **Step 5: Run the pin + adjacent SAT suites**

Run:
```bash
cargo test -p shinri-solver --features oracle --test qfs_differential targeted_analyze_theory_conflict_no_panic -- --nocapture
cargo test -p shinri-sat
```
Expected: the pin PASSES (no panic; not wrong-unsat); all shinri-sat unit tests green.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-sat/src/solver.rs crates/shinri-sat/src/analyze.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "fix(sat): analyze/backtrack robustness on string-theory conflicts — closes cluster B (slice 8)"
```

---

## Task 2: Cluster C — residual `eq_engine.rs:379` explain-not-connected (shinri-theory)

**Files:**
- Modify: `crates/shinri-theory/src/eq_engine.rs` (a diseq-map mutation branch + its `pop` arm, in the ranges 170 / 223–263 / 269 / 466–486)
- Test: `crates/shinri-theory/src/eq_engine.rs` `#[cfg(test)]` module (push/mutate/pop unit test)
- Test: `crates/shinri-solver/tests/qfs_differential.rs` (no-panic + not-wrong-unsat pin)

**Interfaces:**
- Consumes: `EqualityEngine::{merge, assert_diseq, merge_congruence, pop, explain}` and `enum DiseqUndo { Insert, InsertOverwrite, Rekey, RekeyOverwrite }` (eq_engine.rs:41–68).
- Produces: an `EqualityEngine` whose diseq map is byte-identical across any `push → (merge/assert_diseq)* → pop` round-trip, so `explain` is never called on unconnected nodes.

- [ ] **Step 1: Add the failing no-panic pin (solver level)**

In `crates/shinri-solver/tests/qfs_differential.rs`, add:

```rust
#[test]
fn targeted_diseq_undo_residual_no_panic() {
    // Cluster C (slice 8): a second diseq-map mutation not reversed on pop still
    // reaches the eq_engine "explain: a,b not connected" debug-assert. z3: this
    // shape is satisfiable; shinri must not panic and must not wrong-UNSAT.
    expect_not_unsat(
        "(set-logic QF_S)\
         (declare-const s1 String)(declare-const s2 String)(declare-const s3 String)\
         (assert (distinct (str.++ s3 \"b\") (str.++ s3 \"a\")))\
         (assert (and (= (str.++ s3 \"a\") s2) (= s1 s1 \"\")))\
         (assert (distinct (str.++ s2 \"a\") (str.++ s2 \"b\")))\
         (assert (not (distinct (str.++ s2 \"b\") \"\" s3 (str.++ s1 \"a\"))))\
         (check-sat)",
    );
}
```

- [ ] **Step 2: Run the pin to verify it fails (panics in debug)**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_diseq_undo_residual_no_panic -- --nocapture`
Expected: FAIL — panic at `eq_engine.rs:379` "explain: a,b not connected".

- [ ] **Step 3: Root-cause — instrument the diseq-map log across the failing pop**

In `eq_engine.rs`, temporarily log every `diseqs.insert`/`remove` (key + record) in `merge` (223–263), `assert_diseq` (170), and `merge_congruence` (269+), and every `pop` replay arm (466–486), with the current level. Run the Step-1 input via the CLI. Find the mutation whose `pop` replay does NOT restore the exact pre-mutation entry (the map at level 0 after the pop differs from before the push). Candidate causes (from the spec): multi-rekey ordering where two rekeys in one merge target overlapping keys; a `merge_congruence` mutation with no mirrored undo; or a self-key/early-conflict branch leaving a mismatched canonical key. Record the exact culprit in the ledger. Remove instrumentation before Step 5.

- [ ] **Step 4: Add the failing shinri-theory unit test for the exact invariant**

In the `#[cfg(test)] mod tests` of `eq_engine.rs`, mirroring `assert_diseq_collision_preserves_displaced_diseq_across_backtrack` (eq_engine.rs:674), add a test that reproduces the Step-3 mutation directly on `EqualityEngine`: push a level, perform the culprit merge/assert_diseq sequence, `pop`, and assert every pre-push diseq key maps to its original record (and that `explain` over the restored pair does not panic). Name it `<culprit>_preserves_diseq_map_across_backtrack`.

Run: `cargo test -p shinri-theory <culprit>_preserves_diseq_map_across_backtrack`
Expected: FAIL (map not restored / explain panics).

- [ ] **Step 5: Implement the fix — mirror the proven undo pattern**

Apply the minimal fix for the Step-3 culprit, mirroring `InsertOverwrite`/`RekeyOverwrite`:
- if a mutation records no undo (or the wrong one), record the exact inverse via a new/existing `DiseqUndo` variant and handle it in `pop` (466–486);
- if it is a multi-rekey ordering bug, make the `pop` replay order invert the `merge` mutation order (undo log is LIFO — ensure each rekey pushes its own undo entry so reverse replay is exact), or snapshot+restore the affected keys.
Keep the fast (non-colliding) path untouched.

- [ ] **Step 6: Run both new tests + the theory suite**

Run:
```bash
cargo test -p shinri-theory
cargo test -p shinri-solver --features oracle --test qfs_differential targeted_diseq_undo_residual_no_panic -- --nocapture
```
Expected: the new unit test PASSES; the solver pin PASSES; all pre-existing shinri-theory tests (incl. the slice-7 diseq-undo tests) green.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-theory/src/eq_engine.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "fix(theory): reverse residual diseq-map mutation on pop — closes cluster C explain-not-connected (slice 8)"
```

---

## Task 3: Cluster A / #1 — string distinct-over-concat wrong-UNSAT (shinri-str)

**Files:**
- Modify: `crates/shinri-str/src/lib.rs` (disequality empty-length link, 431–445; and/or `len_class_zero`, 729)
- Test: `crates/shinri-solver/tests/qfs_differential.rs` (z3-checked pin)

**Interfaces:**
- Consumes: `len_class_zero(terms, eq, len_term) -> Option<TermId>` (lib.rs:729); `Context::string_const_value`, `normalize::deep_normal_form` (used nearby in the same loop, lib.rs:481–487).
- Produces: the empty-length link never conflicts a disequality whose non-empty side has a structural length ≥ 1 (a normal form containing a non-empty string constant).

- [ ] **Step 1: Add the failing z3-checked pin**

In `crates/shinri-solver/tests/qfs_differential.rs`, add (task-4b §6 minimized input):

```rust
#[test]
fn targeted_distinct_over_concat_not_unsat() {
    // Cluster A / #1 (slice 8): distinct("", s2++"a") drove a unit conflict that
    // unsoundly forced s2++"a"="" (a concat ending in "a" is never empty). z3: sat.
    expect_not_unsat(
        "(set-logic QF_S)\
         (declare-const s2 String)(declare-const s3 String)\
         (assert (not (distinct s3 \"\" (str.++ s2 \"a\"))))\
         (assert (not (= (str.++ s3 \"a\") \"\" s3 s2)))\
         (assert (distinct s3 (str.++ s2 \"a\")))\
         (check-sat)",
    );
}
```

- [ ] **Step 2: Run the pin to verify it fails (wrong UNSAT)**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_distinct_over_concat_not_unsat -- --nocapture`
Expected: FAIL — shinri returns `unsat` (z3 `sat`).

- [ ] **Step 3: Confirm the conflict site**

Read `crates/shinri-str/src/lib.rs:431–445` (empty-length link) and `:729` (`len_class_zero`). Confirm via a temporary `eprintln!` in the empty-length loop that for `"" ≠ s2++"a"` it fires with `other = s2++"a"` and `eq.explain(len_other, 0)` produces a unit (empty-antecedent) conflict. Record. Remove instrumentation.

- [ ] **Step 4: Implement fix (A) — respect the concat ≥1 lower bound**

In the empty-length loop (lib.rs:431–445), before calling `len_class_zero`, skip the link when `other`'s normal form contains a non-empty string constant (its length is ≥ 1, so it can never equal `""`; the disequality is trivially satisfiable). Reuse the `deep_normal_form` + non-empty-const scan already used a few lines below (lib.rs:481–505):

```rust
// Cluster A / #1 (slice 8): a concat whose normal form carries a non-empty
// string constant has length ≥ 1 and can NEVER equal "", so `x ≠ ""` is
// trivially satisfiable — the empty-length link must NOT conflict it. Only the
// genuinely-entailed-zero case (len(x) EUF-merged to 0 via an asserted literal)
// is a sound conflict, and that path is preserved below.
if let Some(nf) = crate::normalize::deep_normal_form(cx.terms, cx.eq, &known, other) {
    if nf.iter().any(|&a| cx.terms.string_const_value(a).map_or(false, |s| !s.is_empty())) {
        continue;
    }
}
```

Decision rule (from the spec): if this proves insufficient/over-broad at the String↔Arith seam, fall back to (C) — narrow the link to fire only when `eq.explain(len_other, 0)` yields a NON-EMPTY antecedent set (a fully-justified, non-unit conflict), else skip → sound Unknown. Record which path was taken in the ledger.

- [ ] **Step 5: Run the pin + the canary tests it must not break**

Run:
```bash
cargo test -p shinri-solver --features oracle --test qfs_differential targeted_distinct_over_concat_not_unsat -- --nocapture
cargo test -p shinri-solver --features oracle --test qfs_differential targeted_empty_length_link_unsat targeted_empty_length_link_bounds_entailed_unsat targeted_constrained_len_with_diseq_stays_sat -- --nocapture
cargo test -p shinri-str
```
Expected: the new pin PASSES (sat, or sound unknown under (C)); the two `empty_length_link_*_unsat` canaries STILL PASS (correct UNSAT preserved — `len(x)=0` entailed by an asserted literal, no non-empty-const normal form); `constrained_len_with_diseq_stays_sat` STILL PASSES; shinri-str unit tests green.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-str/src/lib.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "fix(str): concat-with-nonempty-const never empty-length-conflicts — closes cluster A #1 wrong-UNSAT (slice 8)"
```

---

## Task 4: String-oracle re-baseline (seed bump)

**Files:**
- Modify: `crates/shinri-solver/tests/nary_oracle.rs` (seed at 227, comment 222–226)

**Interfaces:**
- Consumes: `differential_qf_s_nary` harness (nary_oracle.rs:221+), `Lcg`, `gen_script_s`.
- Produces: a clean 0-disagreement / 0-panic string-oracle baseline at seed `0xB000_9E38`.

- [ ] **Step 1: Confirm the debug sweep is clean at the new seed BEFORE editing the committed seed**

With clusters A/B/C fixed, run the sweep with a one-off env/edit at `0xB000_9E38` (temporary local edit of line 227, or a scratch copy):
Run: `cargo test -p shinri-solver --features oracle --test nary_oracle differential_qf_s_nary -- --nocapture`
Expected: PASS — prints `sat=… unsat=… unknown=… z3_checked=…`, no panic, no `DISAGREEMENT`. Record the printed counts in the ledger.

- [ ] **Step 2: Bump the committed seed + refresh the comment**

In `crates/shinri-solver/tests/nary_oracle.rs`, change line 227 `Lcg(0xB000_9E37)` → `Lcg(0xB000_9E38)`, and rewrite the 222–226 comment to state that the slice-7/8 fixes (I2 VMTF + eq_engine InsertOverwrite/residual + analyze robustness + cluster A) closed the skirted panics/disagreement, so the seed no longer needs to avoid them.

- [ ] **Step 3: Run the committed sweep**

Run: `cargo test -p shinri-solver --features oracle --test nary_oracle differential_qf_s_nary -- --nocapture`
Expected: PASS, identical counts to Step 1, 0 disagreements/panics.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/nary_oracle.rs
git commit -m "test(solver): re-baseline string oracle seed 0xB000_9E37->9E38 post cluster A/B/C fixes (slice 8)"
```

---

## Task 5: Full verification net + memory update

**Files:**
- Modify: `.superpowers/sdd/progress-slice8.md` (ledger, local)
- Modify: `/home/dev/.claude/projects/-workspace/memory/` (slice-8 landed memory + retire slice-7 follow-ups)

**Interfaces:**
- Consumes: all prior task commits.
- Produces: a landed, verified slice with updated memory.

- [ ] **Step 1: Full workspace test**

Run: `cargo test --workspace`
Expected: all suites 0-failed. (Long — run in background per the long-tests memory; do not truncate.)

- [ ] **Step 2: Full oracle sweep (feature-gated)**

Run: `cargo test -p shinri-solver --features oracle -- --nocapture`
Expected: every oracle test PASSES — 0 disagreements, 0 panics, including `differential_qf_s_nary` at the new seed and `qfs_differential`'s targeted pins.

- [ ] **Step 3: Clippy — zero net-new**

Run: `cargo clippy --workspace --all-targets 2>&1 | grep -c warning`
Expected: no net-new warnings vs. the base (compare against `git stash` base if needed).

- [ ] **Step 4: Post-fix canary re-grep**

Re-run the Task-0 canary grep; confirm no canary was left asserting the OLD (wrong/panicking) behavior — any that legitimately flipped were updated inside the task that caused the flip, with a comment citing slice 8.

- [ ] **Step 5: Update memory + ledger, mark slice landed**

Update `/home/dev/.claude/projects/-workspace/memory/`:
- Add `shinri-slice8-landed.md` (clusters A/B/C closed, seed re-baselined, counts) + `MEMORY.md` pointer.
- Update `shinri-slice7-landed.md`: retire the two OPEN follow-ups (#1 → cluster A closed; #2 → cluster B closed) and note the newly-found-and-closed cluster C (slice-7 InsertOverwrite fix was incomplete).
Finalize `.superpowers/sdd/progress-slice8.md` with the commit range and FINISH: KEEP LOCAL (standing choice).

- [ ] **Step 6: (No push) confirm clean tree**

Run: `git status --short && git log --oneline -8`
Expected: clean tree; the slice-8 commits present; branch ahead of origin (kept local).

---

## Self-review notes (author)

- **Spec coverage:** Unit 1→Task 1 (B), Unit 2→Task 2 (C), Unit 3→Task 3 (A), Unit 4→Task 4 (re-baseline); verification net → Tasks 0 (pre-flight) + 5 (post). All four spec units mapped.
- **Ordering:** panics (B, C) before wrong-verdict (A) before re-baseline (4) — matches the spec so the debug sweep never aborts.
- **Canary safety:** cluster A's fix is pinned against the two `empty_length_link_*_unsat` canaries (must stay UNSAT) and `constrained_len_with_diseq_stays_sat` (must stay SAT), explicitly re-run in Task 3 Step 5.
- **Decision rules** ((A)→(C) fallback for cluster A; guard-(i)/level-(ii) for cluster B) are recorded in the ledger at execution time so a fresh reviewer can see which path was taken.
- **Repro provenance:** every pin input is a real captured repro (task-4b §6 or seed-9E38/9E3A sweep), not fabricated.
