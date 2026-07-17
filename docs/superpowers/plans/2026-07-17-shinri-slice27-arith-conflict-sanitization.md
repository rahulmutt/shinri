# Slice 27 — Arith Conflict-Core Sanitization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Every conflict core leaving `Arith` is sanitized by one function — interface pseudo-lits resolve to `EqLeaf::Interface(just)`, all other sentinels drop — closing the slice-26 banked sentinel leak on the `assert` and `check` exits.

**Architecture:** Rename the existing, correct sanitizer `resolve_iface_leaves` → `sanitize_conflict`, route the two leaky exits (`TheorySolver::assert`, `TheorySolver::check`) through it, delete the subsumed `strip_apriori`, and enforce the invariant with a tail `debug_assert!` at the choke point. All changes in `crates/shinri-arith/src/lib.rs`.

**Tech Stack:** Rust workspace (cargo), z3 oracle via mise for differential tests.

**Spec:** `docs/superpowers/specs/2026-07-17-shinri-slice27-arith-conflict-sanitization-design.md`

## Global Constraints

- NEVER run `cargo test --workspace` (~50 min; shinri-fp exhaustive). Test per-crate: `cargo test -p shinri-arith`, `cargo test -p shinri-solver --test qfs_differential --features oracle`.
- The differential oracle file is `#![cfg(feature = "oracle")]` — without `--features oracle` it silently runs 0 tests. Always pass the flag and confirm nonzero test count in the output.
- Run all test commands FOREGROUND with captured output; paste real output into reports. Soundness claims require direct repro, not summaries.
- CI gates `cargo fmt --check` — run it locally before every push (subagents don't auto-format).
- Commit messages follow house style: `type(arith): summary (slice 27)` — e.g. `fix(arith): …`, `test(arith): …`, `docs: …`.
- Work on branch `slice27-arith-conflict-sanitization` off `main`; PR to `main` at the end.
- Line numbers below are as of commit `bb3e934c`. Verify by content, not offset, if drift occurs.
- z3 must be on PATH for oracle tasks (`z3 --version`; installed via mise per `mise.toml`).

---

### Task 1: Check-path pin + unified sanitizer

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (fn `resolve_iface_leaves` ~line 796-816; `check` exit ~line 1168; rename call sites ~lines 702, 717, 721, 778, 781, 786; new test in `mod nelson_oppen_tests`)

**Interfaces:**
- Consumes: existing `Arith::assert_interface_equality(&mut self, ctx: &Context, a: TermId, b: TermId, just: TheoryJust) -> Option<Vec<EqLeaf>>`, `TheorySolver::{new_var, assert, check}`, test helpers `real_var`/`num` in `nelson_oppen_tests`.
- Produces: `fn sanitize_conflict(&self, leaves: Vec<EqLeaf>) -> Vec<EqLeaf>` (private; Task 2 routes the `assert` exit through it and deletes `strip_apriori`).

- [ ] **Step 1: Create the branch**

```bash
git checkout -b slice27-arith-conflict-sanitization main
```

- [ ] **Step 2: Write the failing check-path test**

Append to `mod nelson_oppen_tests` in `crates/shinri-arith/src/lib.rs` (after `entailed_eq_antecedent_retains_interface_dependency`, ~line 1960):

```rust
    // ----- Slice 27: check-path sentinel leak (slice-26 banked issue i) -----
    // Interface equality a = b is installed FIRST (feasible alone), then two
    // real atoms a - c >= 1 and c - b >= 0 are asserted. Ge atoms normalize
    // with a NEGATED comb (normalize.rs), so all three constraints live on
    // three DISTINCT slack vars — no single-var bound crossing at assert
    // time. The infeasibility (a - b >= 1 vs a - b = 0) is only visible to
    // simplex: `check`'s Farkas core transitively cites the iface fixed
    // bound, whose antecedent is the sentinel pseudo-lit. Pre-slice-27,
    // `check` piped the core through `strip_apriori` only, leaking the raw
    // pseudo-lit (var index >= 1<<30) to shinri-sat's analyzability guard —
    // a sound-but-lossy Unknown. The core must instead resolve it to
    // EqLeaf::Interface(just).
    #[test]
    fn check_conflict_through_iface_bound_resolves_no_sentinel() {
        let mut ctx = Context::new();
        let a = real_var(&mut ctx, "ia");
        let b = real_var(&mut ctx, "ib");
        let c = real_var(&mut ctx, "ic");
        let one = num(&mut ctx, 1);
        let zero = num(&mut ctx, 0);
        let ac = ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[a, c]).unwrap();
        let ge_ac = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[ac, one]).unwrap(); // a - c >= 1
        let cb = ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[c, b]).unwrap();
        let ge_cb = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[cb, zero]).unwrap(); // c - b >= 0

        let mut arith = Arith::default();
        let just = TheoryJust { theory: 1, tag: 27 };
        assert!(
            arith.assert_interface_equality(&ctx, a, b, just).is_none(),
            "a = b alone is feasible"
        );

        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), ge_ac);
        arith.new_var(&mut cx, Var::new(1), ge_cb);
        assert!(
            arith.assert(&mut cx, Lit::new(Var::new(0), true)).is_none(),
            "a - c >= 1 must not cross any bound at assert time"
        );
        assert!(
            arith.assert(&mut cx, Lit::new(Var::new(1), true)).is_none(),
            "c - b >= 0 must not cross any bound at assert time"
        );

        let leaves = match arith.check(&mut cx, Effort::Full) {
            TCheck::Conflict(leaves) => leaves,
            other => panic!("a-b >= 1 against iface a=b must conflict, got {other:?}"),
        };
        assert!(
            leaves.contains(&EqLeaf::Interface(just)),
            "core must resolve the iface pseudo-lit to Interface(just), got {leaves:?}"
        );
        assert!(
            leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(0), true))),
            "core must cite the a-c>=1 lit, got {leaves:?}"
        );
        assert!(
            leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(1), true))),
            "core must cite the c-b>=0 lit, got {leaves:?}"
        );
        for leaf in &leaves {
            if let EqLeaf::Asserted(l) = leaf {
                assert!(
                    (l.var().index() as u32) < SENTINEL_VAR_BASE,
                    "raw sentinel leaked from check (slice-26 banked bug): {leaves:?}"
                );
            }
        }
    }
```

Note: `Effort`, `TCheck`, `TheoryJust`, `SENTINEL_VAR_BASE` all reach the module via `use super::*` (they are `use`-imports of the parent module). If the compiler complains about `Effort`, add `Effort` to the module's `use shinri_theory::{…}` line.

- [ ] **Step 3: Run the test to verify it fails (pre-fix leak repro)**

```bash
cargo test -p shinri-arith check_conflict_through_iface_bound_resolves_no_sentinel -- --nocapture
```

Expected: FAIL at the `Interface(just)` assertion (or the sentinel assertion), with the debug output showing a leaf whose var index is ≥ 1073741824 (1<<30). If instead one of the two `assert(...)` calls returns `Some`, or `check` returns non-Conflict, STOP — the test premise is wrong; report the actual behavior instead of adjusting assertions to pass.

- [ ] **Step 4: Rename `resolve_iface_leaves` → `sanitize_conflict` and add the choke-point assert**

Replace the function at ~line 796-816 (including its doc comment) with:

```rust
    /// Sanitize a conflict core at the theory boundary. INVARIANT (owned
    /// here, slice 27): no raw sentinel literal ever leaves `Arith` in a
    /// conflict core. An interface pseudo-lit (in `iface_lit`) resolves to
    /// `EqLeaf::Interface(just)` — interface-equality bounds are LIVE-level
    /// facts whose justification the Combiner must expand recursively
    /// (CRITICAL-1), so dropping them would under-cite the core (unsound).
    /// Every OTHER sentinel (a-priori box, FBBT, probe assumption) drops:
    /// those bounds are level-0-entailed facts, so the remaining core stays
    /// valid (the slice-8 stripping argument). Real asserted lits pass
    /// through. ALL conflict exits from this theory must route through this
    /// function; the tail assert catches any future sentinel flavor added
    /// without a resolution rule here.
    fn sanitize_conflict(&self, leaves: Vec<EqLeaf>) -> Vec<EqLeaf> {
        let mut out = Vec::new();
        for leaf in leaves {
            match leaf {
                EqLeaf::Asserted(l) => {
                    if let Some(&tag) = self.iface_lit.get(&l.code()) {
                        if let Some(j) = self.iface_justs.get(&tag) {
                            out.push(EqLeaf::Interface(*j));
                        }
                    } else if !Self::is_sentinel(l) {
                        out.push(EqLeaf::Asserted(l));
                    }
                }
                other => out.push(other),
            }
        }
        debug_assert!(
            !out.iter()
                .any(|leaf| matches!(leaf, EqLeaf::Asserted(l) if Self::is_sentinel(*l))),
            "sanitize_conflict: raw sentinel survived — a sentinel flavor lacks a resolution rule"
        );
        out
    }
```

Update every existing call site from `resolve_iface_leaves` to `sanitize_conflict` — five calls (~lines 717, 721, 778, 781, 786) plus the doc-comment mention in the probe-helper comment (~line 702). Verify none remain:

```bash
grep -n 'resolve_iface_leaves' crates/shinri-arith/src/lib.rs
```

Expected: no output.

- [ ] **Step 5: Route the `check` exit through the sanitizer**

At ~line 1168 in `TheorySolver::check`, change:

```rust
            TCheck::Conflict(leaves) => return TCheck::Conflict(self.strip_apriori(leaves)),
```

to:

```rust
            TCheck::Conflict(leaves) => return TCheck::Conflict(self.sanitize_conflict(leaves)),
```

(`strip_apriori` itself stays for now — the `assert` exit still uses it until Task 2.)

- [ ] **Step 6: Run the test to verify it passes**

```bash
cargo test -p shinri-arith check_conflict_through_iface_bound_resolves_no_sentinel -- --nocapture
```

Expected: PASS.

- [ ] **Step 7: Run the full shinri-arith suite**

```bash
cargo test -p shinri-arith
```

Expected: all tests pass, 0 failures. The existing `interface_equality_conflict` and probe tests exercise the renamed sanitizer.

- [ ] **Step 8: Commit**

```bash
cargo fmt
git add crates/shinri-arith/src/lib.rs
git commit -m "fix(arith): check-exit conflicts route through sanitize_conflict — iface pseudo-lits resolve, not leak (slice 27)"
```

---

### Task 2: Assert-path pin, delete `strip_apriori`, comment truth-ups

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (`assert` exit ~line 1146; delete `strip_apriori` ~lines 1066-1074; comments at ~lines 74, 1015, 1135-1145, 2257-2266; new test in `mod nelson_oppen_tests`)

**Interfaces:**
- Consumes: `sanitize_conflict` from Task 1 (exact signature: `fn sanitize_conflict(&self, leaves: Vec<EqLeaf>) -> Vec<EqLeaf>`).
- Produces: nothing new — after this task `strip_apriori` no longer exists and all four conflict exits route through `sanitize_conflict`.

- [ ] **Step 1: Write the failing assert-path test**

Append to `mod nelson_oppen_tests`, after the Task-1 test:

```rust
    // ----- Slice 27: assert-path sentinel leak (same bug, second exit) -----
    // The interface equality a = b installs fixed bounds [0,0] on the slack
    // var of the difference combination a - b (diff_comb). A Le input atom
    // `a - b <= -1` canonicalizes (normalize.rs) to the SAME combination —
    // (a, +1), (b, -1), sorted by var — hence the SAME slack var, so
    // `apply_bound` detects the crossing (upper -1 < lower 0) directly at
    // assert time and cites the iface bound's sentinel pseudo-lit as the
    // opposing antecedent. Pre-slice-27 `assert` piped this core through
    // `strip_apriori` only — the same leak as the check exit. (A Ge atom
    // would NOT work here: normalize negates its comb to b - a, a different
    // slack var — which is exactly why the check-path test above uses Ge
    // shapes to stay crossing-free.)
    #[test]
    fn assert_conflict_crossing_iface_bound_resolves_no_sentinel() {
        let mut ctx = Context::new();
        let a = real_var(&mut ctx, "ja");
        let b = real_var(&mut ctx, "jb");
        let neg_one = num(&mut ctx, -1);
        let ab = ctx.mk_app(Op::Builtin(BuiltinOp::Sub), &[a, b]).unwrap();
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[ab, neg_one])
            .unwrap(); // a - b <= -1

        let mut arith = Arith::default();
        let just = TheoryJust { theory: 1, tag: 272 };
        assert!(
            arith.assert_interface_equality(&ctx, a, b, just).is_none(),
            "a = b alone is feasible"
        );

        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        arith.new_var(&mut cx, Var::new(0), le);
        let leaves = arith
            .assert(&mut cx, Lit::new(Var::new(0), true))
            .expect("a-b <= -1 must cross the iface fixed bound a-b = 0 at assert time");
        assert!(
            leaves.contains(&EqLeaf::Interface(just)),
            "core must resolve the iface pseudo-lit to Interface(just), got {leaves:?}"
        );
        assert!(
            leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(0), true))),
            "core must cite the asserted a-b<=-1 lit, got {leaves:?}"
        );
        for leaf in &leaves {
            if let EqLeaf::Asserted(l) = leaf {
                assert!(
                    (l.var().index() as u32) < SENTINEL_VAR_BASE,
                    "raw sentinel leaked from assert: {leaves:?}"
                );
            }
        }
    }
```

- [ ] **Step 2: Run the test to verify it fails**

```bash
cargo test -p shinri-arith assert_conflict_crossing_iface_bound_resolves_no_sentinel -- --nocapture
```

Expected: FAIL at the `Interface(just)` assertion, output showing a raw sentinel leaf (var index ≥ 1<<30). If `assert` returns `None` instead (no crossing — the comb keyed a different slack var), STOP and report: the normalize premise needs rechecking against `normalize.rs`, do not weaken the test.

- [ ] **Step 3: Route the `assert` exit and delete `strip_apriori`**

At ~line 1146, change:

```rust
        conflict.map(|leaves| self.strip_apriori(leaves))
```

to:

```rust
        conflict.map(|leaves| self.sanitize_conflict(leaves))
```

Replace the comment block directly above it (~lines 1135-1145, starting `// Strip a-priori-box / FBBT sentinels…`) with:

```rust
        // Sanitize an assert-time conflict the same way every other exit
        // does (sanitize_conflict — see its INVARIANT comment). Two sentinel
        // flavors can appear as the crossing bound's antecedent here: an
        // a-priori-box / FBBT level-0 bound (dropped — slice 8, which first
        // hit this exit: left in the core, a sentinel lit leaks into SAT
        // `analyze`, which indexes `seen[var.index()]` sized to the real-var
        // count → OOB panic), and an interface-equality fixed bound on a
        // shared slack combination (resolved to EqLeaf::Interface — slice 27;
        // previously leaked raw and tripped shinri-sat's analyzability guard
        // to a sound-but-lossy Unknown).
```

Delete the `strip_apriori` function entirely (~lines 1066-1074, including its doc comment `/// Drop a-priori box sentinel lits…`). The compiler now enforces no remaining callers:

```bash
cargo build -p shinri-arith 2>&1 | tail -5
```

Expected: clean build, no `strip_apriori` references.

- [ ] **Step 4: Truth-up the three stale comments**

(a) `apriori_lits` field comment (~line 74). Whatever the current doc comment says, extend it with one line:

```rust
    /// Since slice 27 this set has no production reader — `sanitize_conflict`
    /// drops ALL non-iface sentinels without consulting it — but it stays for
    /// the seeding-idempotence unit pin and as documentation of which
    /// sentinels are a-priori/FBBT ones.
```

(b) Branch-and-bound level-0 comment (~line 1015): change the text `(stripped from conflicts by `strip_apriori`)` to `(stripped from conflicts by `sanitize_conflict`)`.

(c) The Bug-1 regression test doc comment (~lines 2257-2266, above `assert_conflict_against_sentinel_no_sentinel_in_core`): change the sentence

```
    /// The fix captures the conflict from `apply_bound` and pipes it through
    /// `strip_apriori` before returning. This test:
```

to:

```
    /// The fix captures the conflict from `apply_bound` and pipes it through
    /// the exit sanitizer (`strip_apriori` at the time; `sanitize_conflict`
    /// since slice 27) before returning. This test:
```

- [ ] **Step 5: Run both new pins and the full crate suite**

```bash
cargo test -p shinri-arith
```

Expected: all pass, including both slice-27 pins and the pre-existing `assert_conflict_against_sentinel_no_sentinel_in_core` (FBBT flavor, now also flowing through `sanitize_conflict`).

- [ ] **Step 6: Commit**

```bash
cargo fmt
git add crates/shinri-arith/src/lib.rs
git commit -m "fix(arith): assert-exit conflicts route through sanitize_conflict; strip_apriori deleted as subsumed (slice 27)"
```

---

### Task 3: Regression net — solver suite, oracle differential, per-iteration dump-and-diff

**Files:**
- No committed changes (temporary uncommitted instrumentation in `crates/shinri-solver/tests/qfs_differential.rs`; scratch outputs under the session scratchpad directory).

**Interfaces:**
- Consumes: the fix from Tasks 1-2 on `slice27-arith-conflict-sanitization`; baseline is the branch-point commit on `main`.
- Produces: a verdict-diff report (baseline vs fix, per query) for the truth-up in Task 5, and — if the diff surfaces one — a candidate e2e trigger query for Task 4.

- [ ] **Step 1: Confirm z3 and run the oracle differential on the fix branch**

```bash
z3 --version
cargo test -p shinri-solver --test qfs_differential --features oracle -- --nocapture 2>&1 | tail -40
```

Expected: nonzero tests run (~76), 0 failures. The `*_matches_z3` family summary lines print tallies including `guard-bailout` counts — save this output; it is the fix-side aggregate.

- [ ] **Step 2: Add the temporary per-iteration dump (NOT committed)**

All fuzz families funnel through two helpers in `crates/shinri-solver/tests/qfs_differential.rs`: `shinri_lines` (~line 56) and `shinri_lines_counting_bailouts` (~line 96). In EACH of the two, immediately before the final return, insert:

```rust
    // TEMP DIFFDUMP (slice 27 dump-and-diff — do not commit)
    if std::env::var_os("SHINRI_DIFFDUMP").is_some() {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        src.hash(&mut h);
        eprintln!(
            "DIFFDUMP {:016x} {:?} bail={}",
            h.finish(),
            lines.first(),
            bailouts
        );
    }
```

In `shinri_lines` (which has no `bailouts` binding) use the bailout expression that function already reads at ~line 74 (`solver.theory_guard_bailouts()`), binding it to a local first if needed. Fixed LCG seeds give query-text identity across runs, so the src hash is a stable join key.

- [ ] **Step 3: Dump fix-side per-iteration verdicts**

```bash
SHINRI_DIFFDUMP=1 cargo test -p shinri-solver --test qfs_differential --features oracle -- --test-threads=1 2> /tmp/claude-1000/-workspace/a3c60aad-ad65-496e-b209-787c2a0d976a/scratchpad/dump-fix.txt
grep -c DIFFDUMP /tmp/claude-1000/-workspace/a3c60aad-ad65-496e-b209-787c2a0d976a/scratchpad/dump-fix.txt
```

Expected: thousands of DIFFDUMP lines (13 fuzz families × 200 iters each, plus targeted tests).

- [ ] **Step 4: Dump baseline-side verdicts from a worktree at the branch point**

```bash
BASE=$(git merge-base main slice27-arith-conflict-sanitization)
git worktree add /tmp/claude-1000/-workspace/a3c60aad-ad65-496e-b209-787c2a0d976a/scratchpad/wt-baseline "$BASE"
```

Apply the SAME two-helper instrumentation from Step 2 to `wt-baseline/crates/shinri-solver/tests/qfs_differential.rs`, then:

```bash
cd /tmp/claude-1000/-workspace/a3c60aad-ad65-496e-b209-787c2a0d976a/scratchpad/wt-baseline
SHINRI_DIFFDUMP=1 cargo test -p shinri-solver --test qfs_differential --features oracle -- --test-threads=1 2> ../dump-base.txt
cd /workspace
```

- [ ] **Step 5: Diff per-iteration verdicts**

```bash
cd /tmp/claude-1000/-workspace/a3c60aad-ad65-496e-b209-787c2a0d976a/scratchpad
grep DIFFDUMP dump-base.txt | sort > base.sorted
grep DIFFDUMP dump-fix.txt  | sort > fix.sorted
diff base.sorted fix.sorted | head -100
join -j2 <(sort -k2 base.sorted) <(sort -k2 fix.sorted) | awk '$3 != $6 || $4 != $7' > verdict-flips.txt
wc -l verdict-flips.txt; cat verdict-flips.txt
```

Acceptance (spec §4): every flip must be `Unknown → sat/unsat` or `bail>0 → bail=0` (strict improvement), or no flips at all. **Any `sat`/`unsat` → `Unknown`, any verdict change between `sat` and `unsat`, or any bailout increase is a stop-the-line regression — do not proceed; report it.** For each `Unknown → decided` flip, note the query hash for the Task 5 truth-up; each already has its z3 cross-check inside the family loop, so no separate confirmation run is needed.

- [ ] **Step 6: Clean up instrumentation and the worktree**

```bash
git -C /workspace checkout -- crates/shinri-solver/tests/qfs_differential.rs
git worktree remove --force /tmp/claude-1000/-workspace/a3c60aad-ad65-496e-b209-787c2a0d976a/scratchpad/wt-baseline
git -C /workspace status --short
```

Expected: clean tree (keep `dump-*.txt`/`verdict-flips.txt` in the scratchpad for Task 5's report).

---

### Task 4: Best-effort e2e trigger (timebox: one focused session, ~half a day)

**Files:**
- Possibly create: one targeted test in `crates/shinri-solver/tests/qfs_differential.rs` (only if a stable trigger is found).

**Interfaces:**
- Consumes: Task 3's `verdict-flips.txt` (candidate triggers) and the fix branch.
- Produces: either a committed targeted pin, or a recorded negative result for the Task 5 truth-up. Either outcome completes this task — the slice does NOT block on an e2e pin (decided at design time).

- [ ] **Step 1: Check Task 3's diff for a free trigger**

If `verdict-flips.txt` contains a `bail>0 → bail=0` or `Unknown → decided` flip: recover the query text by re-running the flipped family with a temporary `eprintln!("{body}")` guarded by the same env var next to the existing DIFFDUMP site (match on the hash), then skip to Step 3.

- [ ] **Step 2: Otherwise, replay the it194 repro against a local revert of `aadc95ad`**

The slice-26 fix `aadc95ad` re-hid the known trajectory; reverting it (in a throwaway worktree, never on the branch) re-exposes the leak path end-to-end:

```bash
git worktree add /tmp/claude-1000/-workspace/a3c60aad-ad65-496e-b209-787c2a0d976a/scratchpad/wt-e2e slice27-arith-conflict-sanitization
cd /tmp/claude-1000/-workspace/a3c60aad-ad65-496e-b209-787c2a0d976a/scratchpad/wt-e2e
git revert --no-commit aadc95ad
cargo test -p shinri-solver --test qfs_differential --features oracle targeted_leaf_membership_equality_pinned_leaf_decides -- --nocapture
```

That targeted test (qfs_differential.rs ~line 4117) holds the exact it194 query. Expected WITH the slice-27 fix in place: PASS (`sat`) even with `aadc95ad` reverted — the extra interface-exchange rounds now produce an analyzable conflict instead of a guard bailout. Cross-check the pre-fix side: additionally revert the two slice-27 fix commits in the same worktree and re-run; expected: the test fails or reports unknown (guard bailout — the original leak). Record both observations verbatim, then:

```bash
cd /workspace
git worktree remove --force /tmp/claude-1000/-workspace/a3c60aad-ad65-496e-b209-787c2a0d976a/scratchpad/wt-e2e
```

Note: this revert-replay CONFIRMS the fix end-to-end but is not committable as a pin (it needs the revert). A committable pin requires a Step-1-style natural trigger.

- [ ] **Step 3: If (and only if) a natural trigger was found, pin it**

Add to `crates/shinri-solver/tests/qfs_differential.rs`, next to the other `targeted_*` tests, following the house pattern (`expect(query, Verdict::…)` with a comment giving provenance, the pre-fix behavior, and the z3 verdict — model on `targeted_leaf_membership_equality_pinned_leaf_decides` at ~line 4090). Name it `targeted_arith_iface_sentinel_conflict_now_decides`. Run it foreground, confirm PASS, then:

```bash
cargo fmt
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(solver): pin e2e trigger for arith iface-sentinel conflict sanitization (slice 27)"
```

If the timebox expires with no natural trigger: no commit; write the negative result down for Task 5.

---

### Task 5: Spec truth-up, fmt gate, PR

**Files:**
- Modify: `docs/superpowers/specs/2026-07-17-shinri-slice27-arith-conflict-sanitization-design.md` (status line + truth-up section)

**Interfaces:**
- Consumes: outcomes and saved outputs from Tasks 1-4.
- Produces: the merged slice.

- [ ] **Step 1: Truth-up the spec**

Change the `Status:` line to `Status: IMPLEMENTED (2026-07-17). See "Implementation notes (truth-up)" at the end.` (use the actual completion date). Append an `## Implementation notes (truth-up)` section recording, with commit hashes: what landed as designed; any deviations; the Task 3 dump-and-diff result (flip counts, or "bit-identical"); the Task 4 outcome (pin committed / revert-replay confirmed only / negative); anything newly banked.

- [ ] **Step 2: Final gates**

```bash
cargo fmt --check
cargo test -p shinri-arith
cargo test -p shinri-solver --test qfs_differential --features oracle -- --nocapture 2>&1 | tail -20
```

Expected: fmt clean; all tests pass with nonzero counts.

- [ ] **Step 3: Commit the truth-up and open the PR**

```bash
git add docs/superpowers/specs/2026-07-17-shinri-slice27-arith-conflict-sanitization-design.md
git commit -m "docs: slice-27 spec truth-up (IMPLEMENTED) — arith conflict-core sanitization (slice 27)"
git push -u origin slice27-arith-conflict-sanitization
gh pr create --title "Slice 27: arith conflict-core sanitization seam" --body "Closes the slice-26 banked sentinel leak: all conflict exits from Arith route through sanitize_conflict (iface pseudo-lits resolve to Interface leaves; a-priori/FBBT/probe sentinels drop). strip_apriori deleted as subsumed. Spec: docs/superpowers/specs/2026-07-17-shinri-slice27-arith-conflict-sanitization-design.md"
```

Then follow superpowers:finishing-a-development-branch.
