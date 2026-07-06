# Slice 11 — str retraction completeness + analyze OOB hardening: Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix the retraction bug that makes theory conflicts cite stale (retracted) literals — root-caused at plan time to `Combiner::pending_conflict` surviving `pop` — add a permanent debug-mode retraction audit, a test-visible guard-bailout counter, and the `analyze`/guard out-of-range hardening; retires both remaining slice-8 follow-ups.

**Architecture:** A debug-only `cited_lits` audit hook flows from the SAT solver's backtrack path (`shinri-sat`) through the `Theory` seam into the `Combiner`, `StrSolver`, and the shared `EqualityEngine`; the fix itself is a two-line clear of `pending_conflict` in `Combiner::pop` (same rationale as the existing merge-queue drain above it). The guard keeps its sound-Unknown bail semantics but now increments a counter that string-path harnesses assert is zero.

**Tech Stack:** Rust (workspace toolchain **1.96.0**), z3 on PATH for `--features oracle` tests.

**Spec:** `docs/superpowers/specs/2026-07-06-shinri-slice11-str-retraction-completeness-design.md`

## Global Constraints

- Toolchain pinned 1.96.0; `cargo fmt --all --check`, clippy `-D warnings` (CI), `cargo deny` must stay green.
- Clippy verification is only trustworthy on a **clean** cache (warm incremental clippy false-passes in this environment); `cargo clippy --fix` deadlocks here — never use it.
- Implementers must NOT run full-workspace or oracle sweeps inside a task; each task runs only its targeted tests. The controller runs the long gates (Task 6) in the background.
- Commit message scope prefixes follow repo convention: `fix(theory)`, `fix(sat)`, `test(solver)`, `docs`.
- All commits carry the suffix `(slice 11)`.

---

## Pre-flight findings (probed end-to-end 2026-07-06, before planning; all probes reverted — tree clean)

The spec mandated diagnosis-first. Diagnosis is now DONE — probed at plan time:

1. **Root cause CONFIRMED: `Combiner::pending_conflict` is not cleared on `pop`.**
   `assert()` stashes a conflict's `EqLeaf` leaves (`combiner.rs:262-264`); they are
   consumed only at the next `propagate()` (`combiner.rs:273`). When the SAT layer
   backtracks between those two points (a Boolean conflict during the same BCP pass),
   the stashed leaves survive the pop and the next `propagate()` expands them against
   the **post-pop** state → a malformed conflict. Probe evidence on the slice-8
   cluster-B pin input: guard bail at dl=10 citing var 18 `Unset` with stale level 11,
   immediately after `pending_conflict` survived a pop. A second malformation shape
   (sweep iter 93): the conflict cites a lit assigned **True**. Both are the same
   mechanism. Note the latent hazard beyond Unknown-bails: `expand_conflict` resolves
   congruence/interface leaves through the *current* proof forest, so a stale pending
   conflict can in principle expand into a clause that is not theory-entailed and
   *passes* the guard — the fix closes a wrong-verdict hazard, not just an
   incompleteness.
2. **Fix VALIDATED: clearing `pending_conflict` in `pop`** →
   `differential_qf_s_nary` (seed `0xB000_9E38`, 200 iters) moves
   sat=12→**13**, unknown=9→**8**, unsat=179 unchanged, z3_checked=191→**192**,
   0 disagreements, 0 guard bails. Soundness argument: the pop rewinds the theory
   state the conflict was derived from; if the inconsistency still holds at the lower
   level, the theory re-derives it at the next `propagate()`/`check()` (identical to
   the merge-queue drain rationale already documented in `pop`).
3. **Exactly 1 of the 9 sweep unknowns is a guard-bail** (iter 93; script captured in
   Task 2 below — verified `sat` with the fix, z3 agrees). The other 8 are
   fuel/budget Unknowns, untouched by this slice.
4. **The canonical slice-8 cluster-B pin input REMAINS a sound Unknown post-fix** —
   the string theory itself returns `TCheck::Unknown` on it (probed: still Unknown at
   100× fuel). Decisive-SAT recovery on that specific input is bounded by shinri-str's
   word-equation completeness → this is the spec's risk-§5.3 residue, documented as a
   new follow-up in Task 5. The spec's "repro flips to decisive verdict" acceptance is
   carried by the iter-93 pin instead.
5. **Canary hunt:** all three slice-8 `targeted_*` pins use `expect_not_unsat`
   (tolerates Sat and Unknown) → none break when verdicts improve. No test pins exact
   sweep counts (the sweep asserts coverage, not counts). The `⊤≠⊥` level-0 diseq is
   `EqJust::Definitional` → no audit false positive.
6. `eq_true`/`diseq_true` trail-mark truncation and `eq_engine` undo were NOT
   implicated on this corpus; the audit (Task 1) polices them permanently anyway.

---

### Task 1: Retraction audit (debug-only) + `pending_conflict` fix

**Files:**
- Modify: `crates/shinri-sat/src/theory.rs` (trait hook)
- Modify: `crates/shinri-sat/src/solver.rs` (audit sweep in `backtrack_to`, ~line 206; unit test in `mod tests` ~line 1044)
- Modify: `crates/shinri-theory/src/solver_trait.rs` (TheorySolver hook)
- Modify: `crates/shinri-theory/src/combiner.rs` (`pop` fix ~line 380; `Theory` impl `cited_lits` ~line 222 block)
- Modify: `crates/shinri-theory/src/eq_engine.rs` (debug accessor)
- Modify: `crates/shinri-str/src/lib.rs` (StrSolver hook impl, near `push`/`pop` ~line 703)

**Interfaces:**
- Consumes: existing `Theory` (shinri-sat) and `TheorySolver` (shinri-theory) traits; `EqualityEngine { fparent, flabel, diseqs }`.
- Produces: `Theory::cited_lits(&self, out: &mut Vec<(Lit, &'static str)>)` (debug-only, default no-op) — Task 3/4 tests rely on it existing; `EqualityEngine::debug_cited_lits(&self, out: &mut Vec<(Lit, &'static str)>)`.

- [ ] **Step 1: Add the debug-only hook to `shinri_sat::Theory`** (`crates/shinri-sat/src/theory.rs`, inside `pub trait Theory`, after `fn var_for_atom`):

```rust
    /// Debug-only retraction audit (slice 11): append every literal this theory
    /// could currently cite in a `Conflict::Lits` justification, each with a
    /// static provenance label. After every backtrack the solver asserts each
    /// returned lit is still True-assigned at a level ≤ the current one — a
    /// stale entry means state failed to retract on pop (the cluster-B class),
    /// caught at the pop that leaks instead of the later conflict that trips
    /// over it. Default: nothing cited (pure-SAT / stub theories).
    #[cfg(debug_assertions)]
    fn cited_lits(&self, _out: &mut Vec<(Lit, &'static str)>) {}
```

(No change needed to `NoTheory` or test stubs — the default covers them.)

- [ ] **Step 2: Add the audit sweep to the SAT solver** (`crates/shinri-sat/src/solver.rs`). In `backtrack_to` (line ~206), after the `self.theory.pop(...)` call:

```rust
        if from > level {
            self.theory.pop((from - level) as usize);
            #[cfg(debug_assertions)]
            self.debug_check_retraction();
        }
```

and add the method right after `backtrack_to`:

```rust
    /// Slice 11: post-pop retraction audit. Panics (debug builds only) when the
    /// theory still holds a conflict-justification literal the backtrack just
    /// retracted — localizing a retraction leak to the pop that caused it.
    #[cfg(debug_assertions)]
    fn debug_check_retraction(&self) {
        let dl = self.trail.decision_level();
        let mut cited: Vec<(Lit, &'static str)> = Vec::new();
        self.theory.cited_lits(&mut cited);
        for (l, provenance) in cited {
            assert!(
                l.var().index() < self.assign.num_vars()
                    && self.assign.lit_value(l) == LBool::True
                    && self.assign.level(l.var()) <= dl,
                "retraction audit: {provenance} holds stale lit (var {}) after pop \
                 (value {:?}, stored level {}, current dl {dl})",
                l.var().index(),
                self.assign.lit_value(l),
                self.assign.level(l.var()),
            );
        }
    }
```

- [ ] **Step 3: Add the parallel hook to `shinri_theory::TheorySolver`** (`crates/shinri-theory/src/solver_trait.rs`, inside the trait, after `fn model_equal_shared_pairs`):

```rust
    /// Debug-only retraction audit (slice 11): append every literal this theory
    /// could currently cite in a conflict justification (see
    /// `shinri_sat::Theory::cited_lits`). Default: nothing cited.
    #[cfg(debug_assertions)]
    fn cited_lits(&self, _out: &mut Vec<(shinri_core::Lit, &'static str)>) {}
```

- [ ] **Step 4: Implement for `StrSolver`** (`crates/shinri-str/src/lib.rs`, in the `impl TheorySolver for StrSolver` block, next to `push`/`pop`):

```rust
    #[cfg(debug_assertions)]
    fn cited_lits(&self, out: &mut Vec<(Lit, &'static str)>) {
        out.extend(self.eq_true.iter().map(|&(_, l)| (l, "str.eq_true")));
        out.extend(self.diseq_true.iter().map(|&(_, l)| (l, "str.diseq_true")));
    }
```

- [ ] **Step 5: Add the `EqualityEngine` accessor** (`crates/shinri-theory/src/eq_engine.rs`, in the `impl EqualityEngine` block near `push`/`pop`):

```rust
    /// Debug-only (slice 11): every `Asserted` literal live in the proof forest
    /// or the diseq map — the shared-engine provenances a conflict justification
    /// can cite. Swept by the SAT solver's post-pop retraction audit. Live
    /// forest edges only (`fparent[n] != n`); `Definitional` labels (e.g. the
    /// level-0 ⊤≠⊥ diseq) carry no literal and are skipped.
    #[cfg(debug_assertions)]
    pub fn debug_cited_lits(&self, out: &mut Vec<(Lit, &'static str)>) {
        for (n, p) in self.fparent.iter().enumerate() {
            if p.index() != n {
                if let EqJust::Asserted(l) = self.flabel[n] {
                    out.push((l, "eq.forest"));
                }
            }
        }
        for rec in self.diseqs.values() {
            if let EqJust::Asserted(l) = rec.just {
                out.push((l, "eq.diseq"));
            }
        }
    }
```

(`Lit` may need importing into scope there — it is already used in tests; add `use shinri_core::Lit;` at the top if not present in non-test code.)

- [ ] **Step 6: Implement `Theory::cited_lits` on the Combiner** (`crates/shinri-theory/src/combiner.rs`, inside the `impl … Theory for Combiner` block, next to `pop`):

```rust
    #[cfg(debug_assertions)]
    fn cited_lits(&self, out: &mut Vec<(Lit, &'static str)>) {
        // The assert→propagate conflict bridge: leaves stashed here are expanded
        // against CURRENT state at the next propagate(), so any Asserted lit it
        // holds must satisfy the retraction invariant too (the cluster-B class).
        if let Some(leaves) = &self.pending_conflict {
            for leaf in leaves {
                if let crate::types::EqLeaf::Asserted(l) = leaf {
                    out.push((*l, "combiner.pending_conflict"));
                }
            }
        }
        self.eq.debug_cited_lits(out);
        self.string.cited_lits(out);
    }
```

- [ ] **Step 7: Build and run the synthetic audit unit test — write it first, watch it pass** (it validates the audit fires). Append to `mod tests` in `crates/shinri-sat/src/solver.rs`:

```rust
    /// Slice 11: the retraction audit must fire when a theory still cites a
    /// retracted literal after a pop. StaleCiter always "holds" x1-true; the
    /// UNSAT 2-SAT instance forces a backtrack while x1 is unassigned → panic.
    #[derive(Default)]
    struct StaleCiter;
    impl Theory for StaleCiter {
        fn assert(&mut self, _lit: Lit) {}
        fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
            None
        }
        fn explain(&mut self, _j: TheoryJust, _out: &mut Vec<Lit>) {}
        fn check(&mut self, _e: Effort) -> TheoryResult {
            TheoryResult::Sat
        }
        fn push(&mut self) {}
        fn pop(&mut self, _n: usize) {}
        fn new_var(&mut self, _v: Var) {}
        #[cfg(debug_assertions)]
        fn cited_lits(&self, out: &mut Vec<(Lit, &'static str)>) {
            out.push((Lit::new(Var::new(1), true), "test.stale"));
        }
    }

    #[test]
    #[should_panic(expected = "retraction audit")]
    fn retraction_audit_catches_stale_citation() {
        let mut s: Solver<StaleCiter, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..2 {
            s.new_var();
        }
        // UNSAT 2-SAT: forces decide → conflict → backtrack with x1 unassigned.
        s.add_clause(&[lit(0, true), lit(1, true)]);
        s.add_clause(&[lit(0, true), lit(1, false)]);
        s.add_clause(&[lit(0, false), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, false)]);
        let _ = s.solve();
    }
```

Run: `cargo test -p shinri-sat retraction_audit_catches_stale_citation`
Expected: PASS (the audit panics, satisfying `should_panic`).

- [ ] **Step 8: Demonstrate the audit catches the LIVE bug (TDD red).**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_analyze_theory_conflict_no_panic -- --nocapture`
Expected: **FAIL** — panic `retraction audit: combiner.pending_conflict holds stale lit …`. This failure is the point: the audit localizes the leak to the pop. Do NOT commit yet.

- [ ] **Step 9: The fix.** In `crates/shinri-theory/src/combiner.rs`, `fn pop` (~line 380), insert immediately after `let target = self.level - n;` (i.e. before the merge-drain block):

```rust
        // Slice 11 (cluster-B root cause): a conflict stashed by `assert` is
        // expanded against CURRENT state at the next `propagate()`. If a
        // backtrack lands between the two, the stashed leaves refer to state
        // this pop is about to rewind — expanding them later resolves through
        // the post-pop proof forest and fabricates a malformed (or worse,
        // unsound-but-plausible) conflict citing retracted literals. Drop it:
        // if the inconsistency still holds at the lower level, the theory
        // re-derives it at the next propagate()/check() (same rationale as the
        // merge-queue drain below).
        self.pending_conflict = None;
```

- [ ] **Step 10: Verify green.**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_ -- --nocapture`
Expected: PASS (all `targeted_*` tests; the cluster-B pin no longer panics, verdict is a sound `unknown`).

Run: `cargo test -p shinri-solver --features oracle --test nary_oracle differential_qf_s_nary -- --nocapture`
Expected: PASS with printed counts `sat=13 unsat=179 unknown=8 z3_checked=192` and no panics. (If counts differ from these exact values, STOP and report — they were validated at plan time. If the run instead PANICS with `retraction audit: …`, that is a SECOND retraction leak the plan-time probes did not surface — a new finding, not a flaky test: STOP and report the provenance label verbatim.)

Run: `cargo test -p shinri-theory && cargo test -p shinri-str && cargo test -p shinri-sat`
Expected: PASS (audit finds no other leaks in these crates' suites).

- [ ] **Step 11: Commit.**

```bash
git add crates/shinri-sat/src/theory.rs crates/shinri-sat/src/solver.rs \
  crates/shinri-theory/src/solver_trait.rs crates/shinri-theory/src/combiner.rs \
  crates/shinri-theory/src/eq_engine.rs crates/shinri-str/src/lib.rs
git commit -m "fix(theory): clear pending_conflict on pop + debug retraction audit — root-causes cluster-B stale-conflict bails (slice 11)"
```

---

### Task 2: Pin the recovered verdict + truth-up the cluster-B pin

**Files:**
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (new test after `targeted_analyze_theory_conflict_no_panic` ~line 609; comment edit on that test)

**Interfaces:**
- Consumes: existing helpers `expect(src, Verdict)`, `expect_not_unsat(src)`, `z3_verdict(src)`, `shinri_verdict(src)` in the same file.
- Produces: `targeted_pending_conflict_pop_decides_sat` (name referenced by Task 5 docs).

- [ ] **Step 1: Add the decisive-SAT regression pin** (the exact sweep-iter-93 input captured and z3-verified `sat` at plan time — shinri decides `sat` with the Task-1 fix, was a guard-bail `unknown` before it):

```rust
#[test]
fn targeted_pending_conflict_pop_decides_sat() {
    // Slice 11: this input guard-bailed to Unknown before the pending_conflict
    // pop-clear (Combiner::pop) — the stashed conflict survived a backtrack and
    // was served stale, citing a True-valued lit. With retraction fixed it
    // DECIDES. Keep decisive: a regression back to Unknown means a retraction
    // leak reappeared (the debug audit and guard counter will say where).
    expect(
        "(set-logic QF_S)\
         (declare-const s1 String)(declare-const s2 String)(declare-const s3 String)\
         (assert (not (distinct s3 \"\" (str.++ s2 \"a\"))))\
         (assert (not (= s2 s1)))\
         (assert (not (= (str.++ s3 \"a\") \"\" s3 (str.++ s1 \"a\"))))\
         (assert (distinct s3 s2 (str.++ s2 \"a\") (str.++ s3 \"a\")))\
         (check-sat)",
        Verdict::Sat,
    );
}
```

- [ ] **Step 2: Truth-up the cluster-B pin comment.** Replace the comment inside `targeted_analyze_theory_conflict_no_panic` (keep the body unchanged):

```rust
    // Cluster B (slice 8): a string-theory Conflict drove `analyze` to a bad
    // backjump level → `trail.rs:91` "backtrack above current level" in debug.
    // Slice 11 root-caused it: Combiner::pending_conflict survived a pop and was
    // served stale (now cleared in pop; the debug retraction audit pins the
    // invariant). z3 says SAT; shinri's verdict on THIS input remains a sound
    // fuel-Unknown (the string search does not converge even at 100× fuel — the
    // wordeq-completeness follow-up), so the pin stays not-unsat rather than Sat.
```

- [ ] **Step 3: Run both tests.**

Run: `cargo test -p shinri-solver --features oracle --test qfs_differential targeted_ -- --nocapture`
Expected: PASS, including the new `targeted_pending_conflict_pop_decides_sat`.

- [ ] **Step 4: Commit.**

```bash
git add crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(solver): pin pending_conflict-pop input as decisive SAT + truth-up cluster-B pin comment (slice 11)"
```

---

### Task 3: `theory_guard_bailouts` counter + harness zero-assertions

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs` (field, increments at both bail sites ~lines 503-507 and ~609-611, accessor; unit test)
- Modify: `crates/shinri-solver/src/lib.rs` (field on outer `Solver` ~line 53, capture after `sat.solve()` ~line 747, accessor)
- Modify: `crates/shinri-solver/tests/nary_oracle.rs` (assert 0 in `shinri_outcome`)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (assert 0 in `shinri_lines`)

**Interfaces:**
- Consumes: guard-bail sites from Task 1's file state.
- Produces: `shinri_sat::Solver::theory_guard_bailouts(&self) -> u64`; `shinri_solver::Solver::theory_guard_bailouts(&self) -> u64` (cumulative across check-sats). Task 4's test uses the shinri-sat accessor.

- [ ] **Step 1: shinri-sat counter.** Add field `pub(crate) theory_guard_bailouts: u64` to the `Solver` struct and `theory_guard_bailouts: 0` in `Solver::new`. At BOTH guard-bail sites, increment before returning (propagate path shown; the check path is identical):

```rust
                    if matches!(conflict, Conflict::Lits(_))
                        && !self.theory_conflict_analyzable(&conflict_lits)
                    {
                        self.theory_guard_bailouts += 1;
                        return SolveResult::Unknown;
                    }
```

Add the accessor next to `is_unsat`:

```rust
    /// How many theory conflicts the cluster-B guard rejected as malformed
    /// (each a sound Unknown bail). Post-slice-11 this must be 0 on the
    /// differential corpus — a nonzero value is a retraction regression.
    pub fn theory_guard_bailouts(&self) -> u64 {
        self.theory_guard_bailouts
    }
```

- [ ] **Step 2: shinri-sat unit test — a malformed theory conflict returns Unknown and counts.** Append to `mod tests`:

```rust
    /// Slice 11: a malformed theory conflict must bail to a sound Unknown via
    /// the cluster-B guard AND increment the counter. Citing BOTH polarities
    /// of x1 guarantees malformation whatever the assignment: exactly one of
    /// the two lits is True at Full-check time (every var is assigned there),
    /// and a well-formed conflict clause has every cited lit False — the same
    /// shape as the real pending_conflict bail (a True-valued cited lit).
    #[derive(Default)]
    struct MalformedConflict {
        fired: bool,
    }
    impl Theory for MalformedConflict {
        fn assert(&mut self, _lit: Lit) {}
        fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
            None
        }
        fn explain(&mut self, _j: TheoryJust, _out: &mut Vec<Lit>) {}
        fn check(&mut self, _e: Effort) -> TheoryResult {
            if self.fired {
                return TheoryResult::Sat;
            }
            self.fired = true;
            TheoryResult::Conflict(vec![
                Lit::new(Var::new(1), true),
                Lit::new(Var::new(1), false),
            ])
        }
        fn push(&mut self) {}
        fn pop(&mut self, _n: usize) {}
        fn new_var(&mut self, _v: Var) {}
    }

    #[test]
    fn malformed_theory_conflict_bails_unknown_and_counts() {
        let mut s: Solver<MalformedConflict, NoProof, Vmtf> =
            Solver::new(SolverConfig::default());
        for _ in 0..3 {
            s.new_var();
        }
        // No unit clauses → the solver must DECIDE (dl > 0) before the Full
        // check, so the dl==0 top-level-Unsat arm is not taken.
        s.add_clause(&[lit(0, true), lit(2, true)]);
        assert_eq!(s.solve(), SolveResult::Unknown);
        assert_eq!(s.theory_guard_bailouts(), 1);
    }
```

Run: `cargo test -p shinri-sat malformed_theory_conflict_bails_unknown_and_counts`
Expected: PASS. (If the Full check somehow runs at dl 0 the conflict arm
returns Unsat and the first assertion catches it — report rather than weaken
the assertions.)

- [ ] **Step 3: Plumb to the outer solver.** In `crates/shinri-solver/src/lib.rs`: add field `theory_guard_bailouts: u64` to `pub struct Solver` (~line 53) and `theory_guard_bailouts: 0` in its constructor. At the solve site (~line 747), capture before matching:

```rust
        let solve_result = sat.solve();
        self.theory_guard_bailouts += sat.theory_guard_bailouts();
        match solve_result {
```

Add the accessor to the `impl Solver` block (near the other public accessors):

```rust
    /// Cumulative cluster-B guard bailouts across this solver's check-sats
    /// (see `shinri_sat::Solver::theory_guard_bailouts`). Test-visible alarm:
    /// differential harnesses assert this stays 0.
    pub fn theory_guard_bailouts(&self) -> u64 {
        self.theory_guard_bailouts
    }
```

(`grep -n "\.solve()" crates/shinri-solver/src/lib.rs` must show only the one
site; if a new one has appeared since planning, capture there identically.)

- [ ] **Step 4: Harness zero-assertions.** In `crates/shinri-solver/tests/nary_oracle.rs`, at the end of `fn shinri_outcome` before `outcome` is returned:

```rust
    assert_eq!(
        solver.theory_guard_bailouts(),
        0,
        "theory guard bailout — a conflict cited retracted state (retraction regression):\n{src}"
    );
```

In `crates/shinri-solver/tests/qfs_differential.rs`, same assertion at the end of `fn shinri_lines` before `out` is returned.

- [ ] **Step 5: Run the string-path suites.**

Run: `cargo test -p shinri-solver --features oracle --test nary_oracle -- --nocapture && cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture`
Expected: PASS, zero bailout assertions triggered.

- [ ] **Step 6: Commit.**

```bash
git add crates/shinri-sat/src/solver.rs crates/shinri-solver/src/lib.rs \
  crates/shinri-solver/tests/nary_oracle.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "feat(sat): theory_guard_bailouts counter + harness zero-assertions (slice 11)"
```

---

### Task 4: `analyze`/guard out-of-range hardening (slice-8 follow-up #2)

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs` (`theory_conflict_analyzable` ~line 257; `analyze` ~line 292; unit test)

**Interfaces:**
- Consumes: `theory_guard_bailouts()` from Task 3.
- Produces: nothing new — behavioral hardening only.

- [ ] **Step 1: Write the failing test** (append to `mod tests`; this is the `str.len`-bearing-conflict shape slice 8 deferred — a theory conflict citing a var the SAT solver never allocated):

```rust
    /// Slice 11 (slice-8 follow-up #2): a theory conflict citing a var NEVER
    /// registered with the SAT solver must bail to a sound Unknown via the
    /// guard's bounds check — not panic on an out-of-range assignment index.
    #[derive(Default)]
    struct UnregisteredVarConflict {
        fired: bool,
    }
    impl Theory for UnregisteredVarConflict {
        fn assert(&mut self, _lit: Lit) {}
        fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
            None
        }
        fn explain(&mut self, _j: TheoryJust, _out: &mut Vec<Lit>) {}
        fn check(&mut self, _e: Effort) -> TheoryResult {
            if self.fired {
                return TheoryResult::Sat;
            }
            self.fired = true;
            TheoryResult::Conflict(vec![Lit::new(Var::new(10_000), false)])
        }
        fn push(&mut self) {}
        fn pop(&mut self, _n: usize) {}
        fn new_var(&mut self, _v: Var) {}
    }

    #[test]
    fn unregistered_var_theory_conflict_bails_unknown() {
        let mut s: Solver<UnregisteredVarConflict, NoProof, Vmtf> =
            Solver::new(SolverConfig::default());
        for _ in 0..3 {
            s.new_var();
        }
        s.add_clause(&[lit(0, true), lit(2, true)]);
        assert_eq!(s.solve(), SolveResult::Unknown);
        assert_eq!(s.theory_guard_bailouts(), 1);
    }
```

- [ ] **Step 2: Run it to verify it fails.**

Run: `cargo test -p shinri-sat unregistered_var_theory_conflict_bails_unknown`
Expected: FAIL — index-out-of-bounds panic inside `theory_conflict_analyzable` (the `lit_value`/`level` reads index the assignment vectors directly).

- [ ] **Step 3: Bounds-check the guard.** Replace the closure body in `theory_conflict_analyzable` (the doc comment gains one sentence):

```rust
    /// … (existing doc comment) …
    /// An out-of-range var (a theory conflict citing a var never allocated by
    /// the SAT solver) is definitionally unanalyzable and rides the same bail.
    fn theory_conflict_analyzable(&self, conflict_lits: &[Lit]) -> bool {
        let dl = self.trail.decision_level();
        conflict_lits.iter().all(|&l| {
            l.var().index() < self.assign.num_vars()
                && self.assign.lit_value(l) == LBool::False
                && self.assign.level(l.var()) <= dl
        })
    }
```

- [ ] **Step 4: Document unreachability in `analyze`.** At the top of `analyze` (after `reason_lits` is built, ~line 302):

```rust
        // Both theory-conflict call sites run theory_conflict_analyzable first,
        // so every cited var is in range here (slice 11); stored-clause
        // conflicts only ever contain solver-allocated vars.
        debug_assert!(
            reason_lits
                .iter()
                .all(|l| l.var().index() < self.assign.num_vars()),
            "analyze: conflict cites an unregistered var"
        );
```

- [ ] **Step 5: Run tests.**

Run: `cargo test -p shinri-sat`
Expected: PASS, including both new counter/OOB tests.

- [ ] **Step 6: Commit.**

```bash
git add crates/shinri-sat/src/solver.rs
git commit -m "fix(sat): bounds-check theory conflicts in guard + analyze debug-assert — closes slice-8 OOB follow-up (slice 11)"
```

---

### Task 5: Docs truth-up + follow-up ledger

**Files:**
- Modify: `docs/superpowers/specs/2026-07-06-shinri-slice11-str-retraction-completeness-design.md` (Status line + acceptance amendment)
- Modify: `docs/superpowers/specs/2026-07-03-shinri-slice8-string-soundness-followups-design.md` (Status line)

**Interfaces:** none (docs only).

- [ ] **Step 1: Slice-11 spec Status.** Replace the `Status:` line with:

```
Status: IMPLEMENTED (slice 11 landed). Root cause: Combiner::pending_conflict
survived pop (assert→propagate bridge) — cleared in pop; debug retraction
audit added (shinri-sat sweep over str stores + shared-engine forest/diseqs +
pending_conflict); guard hardened with bounds check + bailout counter
(harness-asserted 0). Sweep: sat=13/unsat=179/unknown=8, z3_checked=192,
0 disagreements. RESIDUE (risk §5.3, new follow-up): the canonical slice-8
cluster-B input remains a sound fuel-Unknown — shinri-str's word-equation
search does not converge on it even at 100× fuel; decisive-SAT there needs
wordeq-completeness work, out of slice-11 scope. The decisive-verdict
acceptance is carried by targeted_pending_conflict_pop_decides_sat instead.
```

Also amend §2.2's first acceptance bullet to read "the **iter-93 guard-bail input** flips Unknown → decisive SAT (z3-agreed), pinned as `targeted_pending_conflict_pop_decides_sat`; the canonical slice-8 pin remains a documented sound fuel-Unknown (see Status)".

- [ ] **Step 2: Slice-8 spec Status.** Replace its `Status:` line (line 4) with:

```
Status: IMPLEMENTED (slice 8 landed 2026-07-03). Both open follow-ups retired
by slice 11: #1 root-caused (Combiner::pending_conflict not cleared on pop —
NOT a shinri-str retraction failure; fixed + debug retraction audit) with a
wordeq-completeness residue follow-up on the canonical cluster-B input; #2
closed (guard bounds check; analyze debug-assert).
```

- [ ] **Step 3: Commit.**

```bash
git add docs/superpowers/specs/2026-07-06-shinri-slice11-str-retraction-completeness-design.md \
  docs/superpowers/specs/2026-07-03-shinri-slice8-string-soundness-followups-design.md
git commit -m "docs: slice-11 spec/ledger truth-up — root cause, residue follow-up, slice-8 follow-ups retired (slice 11)"
```

---

### Task 6: Full verification nets (CONTROLLER-RUN, background — not for subagents)

**Files:** none (verification only; fix commits only if something breaks).

- [ ] **Step 1:** `cargo fmt --all --check` → clean.
- [ ] **Step 2:** `cargo test --workspace` → all suites pass, 0 failures (this also runs every debug-build test under the new retraction audit — any panic names its provenance; treat as a new finding, not a flaky test).
- [ ] **Step 3:** `cargo test -p shinri-solver --features oracle` (full oracle sweep incl. `fp_oracle`, ~915 s) → 0 disagreements, 0 panics, 0 guard-bailout assertions.
- [ ] **Step 4:** Clean-cache clippy: `cargo clean && cargo clippy --workspace --all-targets` (NO `--fix`, no `-D warnings`; ~15 min) → zero net-new warnings vs main.
- [ ] **Step 5:** `cargo deny check` → green.
- [ ] **Step 6:** Record the numbers in the slice ledger; then use superpowers:finishing-a-development-branch.
