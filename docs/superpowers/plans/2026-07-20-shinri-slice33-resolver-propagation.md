# Slice 33 — Resolver Propagation Outcome Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give the word-equation resolver a propagation outcome so an entailed pure assignment `v ≈ W` (constant `W`) merges into EUF with cited antecedents, instead of falling through to an F-split dedup hit and a sound `Unknown`.

**Architecture:** `StepResult` gains a `Propagate` variant returned *before* the variable-headed F-split path. The driver merges `v ≈ W` into the shared `EqualityEngine` using `EqJust::Interface`, backed by a new trail-scoped tag→antecedent table on `StrSolver` and the first real `StrSolver::explain`. Nothing is emitted and nothing is learnt, so E1's `input_cond_roots` gate — which halted slice 32 — has no clause to reject; branch-locality comes from `push`/`pop` instead.

**Tech Stack:** Rust, `cargo nextest`, `mise` tasks, z3/cvc5 via the `oracle` feature.

**Spec:** `docs/superpowers/specs/2026-07-20-shinri-slice33-resolver-propagation-design.md` (`50fc759c`)
**Branch:** `slice33-resolver-propagation` (already created, spec already committed)

## Global Constraints

- Pure-Rust mandate: native-link dependencies are banned (`deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`). Add no new dependency in this slice.
- `cargo fmt --all` before every push — CI gates on `fmt --check` and fails fast.
- `cargo clippy --workspace --all-targets -- -D warnings` must be clean.
- Oracle tests require `--features oracle`. **Without it they silently run 0 tests — never report that as green coverage.** Always confirm the discovered test count.
- Use `-E 'test(name)'` for nextest filters. A bare `mod::name` positional filter finds 0 tests on nextest 0.9.140, and a 0-test run reads as green.
- Blocking-tier budget 10–15 min. Everything in this slice is fast-tier; add no `#[ignore]` and remove none.
- Never remove `#[ignore]` from the exhaustive `shinri-fp` suites.
- Scope discipline: constant-word residuals only. Do **not** widen to `v ≈ W` where `W` contains other variables (spec §2) — that is the deleted E1 probe's failure mode.
- Probe C staying `unknown` is a **stated non-goal**, not a failure (spec §7).

---

### Task 1: Measure the probes (baseline pins)

**Purpose:** The spec's §7 predictions must be confirmed or falsified *before* any pin is written. This task encodes today's behaviour as an executable baseline. Tasks 2–5 change nothing about it; Task 6 flips the ones that actually moved.

**Files:**
- Create: `crates/shinri-solver/tests/slice33_probes.rs`

**Interfaces:**
- Consumes: nothing (first task).
- Produces: the probe test file that Task 6 edits. Test names `probe_e_empty_literal_concat`, `probe_g_asserted_empty_var`, `probe_c_len_zero_var` are referenced by Task 6.

- [ ] **Step 1: Write the baseline probe file**

Create `crates/shinri-solver/tests/slice33_probes.rs`. The `run_script` helper is copied from `script_e2e.rs:7-25` because Rust integration test files are separate crates and cannot share private helpers.

```rust
//! Slice 33 probes (spec §7). These pin the resolver-propagation frontier.
//!
//! Written BEFORE the implementation as a measured baseline: every probe here
//! records what the engine does TODAY. Task 6 updates the ones that actually
//! flip, and only after z3 confirms the new verdict.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

fn run_script(src: &str) -> Vec<String> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut out = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match result {
            Ok(cmd) => match solver.execute(cmd) {
                CommandResponse::None => {}
                CommandResponse::Sat => out.push("sat".into()),
                CommandResponse::Unsat => out.push("unsat".into()),
                CommandResponse::Unknown => out.push("unknown".into()),
                CommandResponse::Model(s) | CommandResponse::Values(s) => out.push(s),
                CommandResponse::Error(e) => out.push(format!("(error \"{e}\")")),
            },
            Err(e) => out.push(format!("(error \"{e}\")")),
        }
    }
    out
}

/// Probe E — the empty string is a SOURCE-LEVEL literal, so there is nothing to
/// ground. Predicted (spec §7) to flip to `unsat` once the resolver can
/// propagate `[y] = ["ab"]`.
#[test]
fn probe_e_empty_literal_concat() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun y () String)
           (assert (= (str.++ "" y) "ab"))(assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "BASELINE (pre-slice-33)");
}

/// Probe G — `x = ""` asserted by hand, strictly more than any grounding
/// mechanism could achieve. Predicted to flip to `unsat`.
#[test]
fn probe_g_asserted_empty_var() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= x ""))(assert (= (str.++ x y) "ab"))
           (assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "BASELINE (pre-slice-33)");
}

/// Probe C — needs `len(x) = 0 → x ≈ ""` grounding, i.e. the RETRACTED wall-3
/// seam. Predicted to stay `unknown`. That is a STATED NON-GOAL (spec §7), not
/// a failure: this assertion must still read `unknown` at the end of slice 33.
#[test]
fn probe_c_len_zero_var() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.len x) 0))(assert (= (str.++ x y) "ab"))
           (assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "NON-GOAL: out of scope for slice 33");
}

/// Probe F — control. The contradiction machinery is intact once the equality
/// exists. This must stay `unsat` throughout the slice.
#[test]
fn probe_f_control_direct_contradiction() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun y () String)
           (assert (= y "ab"))(assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"], "control: must never regress");
}
```

- [ ] **Step 2: Run the probes and confirm the baseline**

```bash
cargo nextest run -p shinri-solver -E 'test(probe_)' --no-fail-fast
```

Expected: `4 tests run: 4 passed`. Confirm the count is **4** — a 0-test run reads as green and means the filter missed.

If any probe does NOT match its baseline assertion, **stop**. The spec's measured starting point is wrong and the slice must be re-scoped before any implementation. Report the actual verdicts.

- [ ] **Step 3: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/slice33_probes.rs
git commit -m "test(str): slice33 T1 — measured probe baseline (C/E/F/G)"
```

---

### Task 2: Trail-scoped propagation-tag store

**Purpose:** The antecedent table must die with the branch that minted it. An under-truncated table is a stale-antecedent wrong-UNSAT (spec §9.1). `Trail` is a fixed 4-tuple, so it widens to 5.

**Files:**
- Modify: `crates/shinri-str/src/trail.rs:2-27`
- Modify: `crates/shinri-str/src/lib.rs` (struct fields, `push`, `pop`, `cited_lits`)

**Interfaces:**
- Consumes: nothing from Task 1.
- Produces:
  - `StrSolver.prop_tags: Vec<Vec<EqLeaf>>` — index is the tag, value is that tag's antecedent set.
  - `Trail::push(eq, diseq, memb, order, prop)` and `Trail::pop_to(target) -> Option<(usize, usize, usize, usize, usize)>` — 5-tuple.
  - Task 3 reads `prop_tags`; Task 5 appends to it.

- [ ] **Step 1: Write the failing backtracking test**

Append to `crates/shinri-str/src/trail.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    /// The propagation-tag length is scoped like every other store: a mark taken
    /// at level N must restore the tag count on pop to N. A leaked tag is a
    /// stale-antecedent wrong-UNSAT (spec §9.1).
    #[test]
    fn pop_restores_prop_tag_length() {
        let mut t = Trail::default();
        t.push(0, 0, 0, 0, 0); // level 1 mark: 0 tags live
        t.push(1, 0, 0, 0, 3); // level 2 mark: 3 tags live
        let restored = t.pop_to(1).expect("popped at least one scope");
        assert_eq!(restored.4, 3, "pop must report the prop-tag truncation length");
        assert_eq!(t.level(), 1, "one scope remains open");
    }
}
```

- [ ] **Step 2: Run it to verify it fails**

```bash
cargo nextest run -p shinri-str -E 'test(pop_restores_prop_tag_length)'
```

Expected: FAIL to compile — `Trail::push` takes 4 arguments, and the tuple has no field `.4`.

- [ ] **Step 3: Widen `Trail` to 5 fields**

Replace the body of `crates/shinri-str/src/trail.rs` above the test module:

```rust
#[derive(Default)]
pub struct Trail {
    // (eq_true_len, diseq_true_len, memb_true_len, order_true_len, prop_tags_len)
    marks: Vec<(usize, usize, usize, usize, usize)>,
}

impl Trail {
    pub fn push(
        &mut self,
        eq_len: usize,
        diseq_len: usize,
        memb_len: usize,
        order_len: usize,
        prop_len: usize,
    ) {
        self.marks
            .push((eq_len, diseq_len, memb_len, order_len, prop_len));
    }

    /// Current absolute decision level = number of open scopes. (Unchanged
    /// semantics — see the original doc comment.)
    pub fn level(&self) -> u32 {
        self.marks.len() as u32
    }

    /// Returns the (eq, diseq, memb, order, prop) lengths to truncate to for
    /// absolute `target`.
    pub fn pop_to(&mut self, target: usize) -> Option<(usize, usize, usize, usize, usize)> {
        let mut last = None;
        while self.marks.len() > target {
            last = self.marks.pop();
        }
        last
    }
}
```

Preserve the original `#[derive(...)]` line from `trail.rs:1` exactly as it is if it differs from `#[derive(Default)]` — read the file first and keep whatever attributes are already there.

- [ ] **Step 4: Add the `prop_tags` field to `StrSolver`**

In `crates/shinri-str/src/lib.rs`, add to the `StrSolver` struct (place it immediately after the `order_levels` field so related scoped stores stay together):

```rust
    /// Slice 33: antecedent sets for propagation merges, indexed by tag. Entry
    /// `i` is the antecedent set of `TheoryJust { theory: THEORY_ID, tag: i }`.
    /// Trail-scoped (truncated on `pop`) — a tag MUST NOT outlive the branch
    /// that minted it, or `explain` would expand it to antecedents that are no
    /// longer asserted (a stale-antecedent wrong-UNSAT).
    prop_tags: Vec<Vec<EqLeaf>>,
```

`EqLeaf` is already imported at `lib.rs:23`.

- [ ] **Step 5: Update `push`, `pop`, and `cited_lits`**

In `crates/shinri-str/src/lib.rs`, change `push` (currently `lib.rs:1225-1232`) to pass the fifth length:

```rust
    fn push(&mut self) {
        self.trail.push(
            self.eq_true.len(),
            self.diseq_true.len(),
            self.memb_true.len(),
            self.order_true.len(),
            self.prop_tags.len(),
        );
    }
```

Change `pop` (currently `lib.rs:1234-1246`):

```rust
    fn pop(&mut self, level: usize) {
        if let Some((e, d, mb, ob, pt)) = self.trail.pop_to(level) {
            self.eq_true.truncate(e);
            self.diseq_true.truncate(d);
            // Keep the parallel assertion-level records in lock-step (E1 gate).
            self.eq_levels.truncate(e);
            self.diseq_levels.truncate(d);
            self.memb_true.truncate(mb);
            self.memb_levels.truncate(mb);
            self.order_true.truncate(ob);
            self.order_levels.truncate(ob);
            // Slice 33: drop propagation tags minted inside the closed scopes.
            self.prop_tags.truncate(pt);
        }
    }
```

Extend `cited_lits` (currently `lib.rs:1248-1253`). This closes the gap `combiner.rs:442` documents — that `EqJust::Interface` justifications are not swept, so a retraction leak would pass silently (spec §9.2):

```rust
    #[cfg(debug_assertions)]
    fn cited_lits(&self, out: &mut Vec<(Lit, &'static str)>) {
        out.extend(self.eq_true.iter().map(|&(_, l)| (l, "str.eq_true")));
        out.extend(self.diseq_true.iter().map(|&(_, l)| (l, "str.diseq_true")));
        out.extend(self.memb_true.iter().map(|&(_, l, _)| (l, "str.memb_true")));
        // Slice 33: sweep propagation-tag antecedents too. Without this the
        // retraction-leak net does not see interface justifications at all
        // (combiner.rs:442) — exactly the mechanism this slice adds.
        for leaves in &self.prop_tags {
            for leaf in leaves {
                if let EqLeaf::Asserted(l) = leaf {
                    out.push((*l, "str.prop_tags"));
                }
            }
        }
    }
```

- [ ] **Step 6: Run the test and the full str suite**

```bash
cargo nextest run -p shinri-str -E 'test(pop_restores_prop_tag_length)'
```

Expected: PASS.

```bash
cargo nextest run -p shinri-str
```

Expected: all pass. This catches any other `Trail::push` caller the widening broke.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
cargo clippy -p shinri-str --all-targets -- -D warnings
git add crates/shinri-str/src/trail.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice33 T2 — trail-scoped propagation-tag store + cited_lits sweep"
```

---

### Task 3: Real `StrSolver::explain`

**Purpose:** `StrSolver::explain` is a `debug_assert!(false)` stub (`lib.rs:1214-1219`) — string theory has never minted a self-tagged interface leaf. Slice 33 is the first, so `explain` must actually expand a tag.

**Files:**
- Modify: `crates/shinri-str/src/lib.rs:1214-1219` (the `explain` method)
- Test: `crates/shinri-str/src/lib.rs` (in-crate `#[cfg(test)] mod` at the end of the file)

**Interfaces:**
- Consumes: `StrSolver.prop_tags: Vec<Vec<EqLeaf>>` (Task 2).
- Produces: `StrSolver::alloc_prop_tag(&mut self, leaves: Vec<EqLeaf>) -> u32` — Task 5 calls this to mint a tag before merging.

- [ ] **Step 1: Write the failing test**

Add to the test module at the end of `crates/shinri-str/src/lib.rs` (if no `#[cfg(test)] mod tests` exists there, create one):

```rust
#[cfg(test)]
mod slice33_explain_tests {
    use super::*;
    use shinri_theory::Explainer;

    /// A minted tag expands to exactly the leaves it was allocated with. Under-
    /// expansion here is the ce2 wrong-UNSAT shape (spec §4).
    #[test]
    fn explain_expands_prop_tag_to_its_leaves() {
        let mut s = StrSolver::default();
        let a = Lit::new(Var(7), true);
        let b = Lit::new(Var(9), false);
        let tag = s.alloc_prop_tag(vec![EqLeaf::Asserted(a), EqLeaf::Asserted(b)]);

        let mut exp = Explainer::default();
        s.expand_prop_tag(tag, &mut exp);

        let mut got = exp.lits.clone();
        got.sort_unstable_by_key(|l| l.code());
        let mut want = vec![a, b];
        want.sort_unstable_by_key(|l| l.code());
        assert_eq!(got, want, "explain must expand a tag to all its antecedents");
    }

    /// Tags are allocated densely from 0 so the trail length IS the tag count.
    #[test]
    fn prop_tags_are_dense_and_sequential() {
        let mut s = StrSolver::default();
        let t0 = s.alloc_prop_tag(vec![]);
        let t1 = s.alloc_prop_tag(vec![]);
        assert_eq!((t0, t1), (0, 1));
        assert_eq!(s.prop_tags.len(), 2);
    }
}
```

If `Lit::new(Var(7), true)` does not match this crate's constructor, read the `Lit` API in `crates/shinri-core/src/` and use the real constructor — the test's substance is the expansion, not the literal-building syntax.

- [ ] **Step 2: Run it to verify it fails**

```bash
cargo nextest run -p shinri-str -E 'test(slice33_explain)'
```

Expected: FAIL to compile — no method `alloc_prop_tag` / `expand_prop_tag`.

- [ ] **Step 3: Implement the tag helpers**

Add to the `impl StrSolver` block in `crates/shinri-str/src/lib.rs` (the inherent impl, not the `TheorySolver` impl):

```rust
    /// Slice 33: record an antecedent set and return its tag. The tag indexes
    /// `prop_tags`, which is trail-scoped, so the tag is valid only within the
    /// branch that minted it.
    fn alloc_prop_tag(&mut self, leaves: Vec<EqLeaf>) -> u32 {
        let tag = self.prop_tags.len() as u32;
        self.prop_tags.push(leaves);
        tag
    }

    /// Slice 33: expand a propagation tag into `exp`. Split out from the
    /// `TheorySolver::explain` impl so it is unit-testable without a TheoryCtx.
    fn expand_prop_tag(&self, tag: u32, exp: &mut Explainer) {
        match self.prop_tags.get(tag as usize) {
            Some(leaves) => {
                // `push_leaf` routes Asserted → lits and Interface → pending, so a
                // nested interface antecedent keeps expanding in the Combiner's
                // visited-guarded loop (combiner.rs:882-906).
                for &leaf in leaves {
                    exp.push_leaf(leaf);
                }
            }
            None => debug_assert!(
                false,
                "slice33: propagation tag {tag} expanded after its scope was popped \
                 — a stale tag means the trail truncation is broken"
            ),
        }
    }
```

- [ ] **Step 4: Replace the `explain` stub**

Replace `crates/shinri-str/src/lib.rs:1214-1219` entirely:

```rust
    fn explain(&mut self, _cx: &mut TheoryCtx, tag: u32, exp: &mut Explainer) {
        // Slice 33: the string theory now DOES mint self-tagged interface
        // (theory:4) leaves — the propagation merge's justification (spec §4.1).
        // Before slice 33 this was a `debug_assert!(false)` stub.
        self.expand_prop_tag(tag, exp);
    }
```

- [ ] **Step 5: Run the tests**

```bash
cargo nextest run -p shinri-str -E 'test(slice33_explain)'
```

Expected: `2 tests run: 2 passed`.

```bash
cargo nextest run -p shinri-str
```

Expected: all pass.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
cargo clippy -p shinri-str --all-targets -- -D warnings
git add crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice33 T3 — real StrSolver::explain over propagation tags"
```

---

### Task 4: `StepResult::Propagate` and resolver detection

**Purpose:** Detect the pure-assignment residual and report it, placed *before* the variable-headed F-split so the shape stops falling through to `Saturated`.

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs:6-24` (the `StepResult` enum)
- Modify: `crates/shinri-str/src/wordeq.rs` (insert detection after the all-constant block ~line 517, before the char-peel / F-split paths)
- Test: `crates/shinri-str/src/wordeq.rs` (existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: nothing from Tasks 2–3.
- Produces: `StepResult::Propagate { var: TermId, word: TermId, just: Vec<EqLeaf> }`. `word` is a **single interned string constant**, never a multi-atom slice. Task 5 matches on this variant.

- [ ] **Step 1: Write the failing tests**

Add to the existing `#[cfg(test)] mod tests` in `crates/shinri-str/src/wordeq.rs`. Follow the setup style of the neighbouring `occurs_*` tests in that module — read `occurs_distinct_vars_not_conflict` (`wordeq.rs:1105`) and mirror how it builds the `Context`, `EqualityEngine`, word slices, `just`, `eqn_lit`, `fresh_ctr`, and `emitted` before calling `resolve_equation`.

```rust
    // ── Slice 33: propagation outcome ────────────────────────────────────────
    // A residual pure assignment `v = W` (W all-constant) must PROPAGATE, not
    // fall through to the variable-headed F-split → dedup → Saturated path.

    /// The core shape: `[y] = ["ab"]` reports `y ≈ "ab"`.
    #[test]
    fn pure_assignment_propagates_constant_word() {
        // Build `y = "ab"` as a residual and resolve it.
        // (setup mirrors occurs_distinct_vars_not_conflict)
        let (mut terms, mut eq, y, ab, just, eqn_lit) = setup_pure_assignment("y", "ab");
        let mut fresh_ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut terms, &mut eq, &[y], &[ab], just, eqn_lit, &mut fresh_ctr, &mut emitted,
        );
        match r {
            StepResult::Propagate { var, word, .. } => {
                assert_eq!(var, y, "the variable side must be reported as `var`");
                assert_eq!(
                    terms.string_const_value(word),
                    Some("ab"),
                    "`word` must be a single interned constant"
                );
            }
            _ => panic!("expected Propagate for a pure assignment, got a different outcome"),
        }
    }

    /// A MULTI-ATOM constant side folds to ONE constant. Merging against a
    /// multi-atom CONCAT term would make the merge depend on that term's own
    /// normal form (spec §3).
    #[test]
    fn pure_assignment_folds_multi_atom_constant_side() {
        let (mut terms, mut eq, y, _unused, just, eqn_lit) = setup_pure_assignment("y", "ab");
        let a = terms.mk_string_const("a");
        let b = terms.mk_string_const("b");
        let mut fresh_ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut terms, &mut eq, &[y], &[a, b], just, eqn_lit, &mut fresh_ctr, &mut emitted,
        );
        match r {
            StepResult::Propagate { word, .. } => assert_eq!(
                terms.string_const_value(word),
                Some("ab"),
                "['a','b'] must fold to the single constant \"ab\""
            ),
            _ => panic!("expected Propagate for a multi-atom constant side"),
        }
    }

    /// Orientation-independent: the variable may sit on either side.
    #[test]
    fn pure_assignment_propagates_with_variable_on_right() {
        let (mut terms, mut eq, y, ab, just, eqn_lit) = setup_pure_assignment("y", "ab");
        let mut fresh_ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut terms, &mut eq, &[ab], &[y], just, eqn_lit, &mut fresh_ctr, &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Propagate { var, .. } if var == y),
            "the variable must be found on either side"
        );
    }

    /// SCOPE FENCE (spec §2): a constant side is required. `v = w ++ "a"` with a
    /// second VARIABLE must NOT propagate — that is the wider rule the deleted
    /// E1 probe got wrong, and it is explicitly out of scope for slice 33.
    #[test]
    fn variable_bearing_word_does_not_propagate() {
        let (mut terms, mut eq, y, _ab, just, eqn_lit) = setup_pure_assignment("y", "ab");
        let w = declare_str_var(&mut terms, "w");
        let a = terms.mk_string_const("a");
        let mut fresh_ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut terms, &mut eq, &[y], &[w, a], just, eqn_lit, &mut fresh_ctr, &mut emitted,
        );
        assert!(
            !matches!(r, StepResult::Propagate { .. }),
            "a variable-bearing word must NOT propagate in slice 33 (spec §2)"
        );
    }
```

Write the two helpers `setup_pure_assignment(var_name, const_value) -> (Context, EqualityEngine, TermId, TermId, Vec<EqLeaf>, Lit)` and `declare_str_var(&mut Context, name) -> TermId` in the same test module, factoring the setup out of the existing `occurs_*` tests rather than duplicating it.

- [ ] **Step 2: Run to verify they fail**

```bash
cargo nextest run -p shinri-str -E 'test(propagate) + test(pure_assignment) + test(variable_bearing_word)'
```

Expected: FAIL to compile — no variant `StepResult::Propagate`. Confirm **4** tests are discovered once it compiles.

- [ ] **Step 3: Add the `Propagate` variant**

In `crates/shinri-str/src/wordeq.rs`, add to the `StepResult` enum (after `Saturated`, before `Conflict`):

```rust
    /// SLICE 33. The equation entails the pure assignment `var ≈ word`, where
    /// the residual is a single variable on one side and an ALL-CONSTANT word on
    /// the other. `word` is a SINGLE interned string constant — a multi-atom
    /// constant side is folded before it is reported, so the caller's merge never
    /// depends on a CONCAT term's own normal form.
    ///
    /// This is NOT the deleted E1 probe (see the comment further down this file).
    /// That probe returned `Done` — it claimed the equation was RESOLVED and
    /// cited nothing. This reports a FACT together with `just`, its full
    /// antecedent set, which the caller merges into EUF under an
    /// `EqJust::Interface` tag. Nothing is emitted and nothing is learnt, so the
    /// E1 branch-locality gate has no clause to reject.
    Propagate {
        var: TermId,
        word: TermId,
        just: Vec<EqLeaf>,
    },
```

- [ ] **Step 4: Implement detection**

In `crates/shinri-str/src/wordeq.rs`, insert this block **after** the all-constant residual comparison block (which ends around line 517, just after the `"b" = "ba"` length-difference handling) and **before** the char-peel and generic F-split paths. Placement is the fix — reaching the F-split first is the entire defect.

```rust
    // ── SLICE 33: pure-assignment propagation ────────────────────────────────
    // A residual `[v] = [constant word]` ENTAILS `v ≈ W`. Before slice 33 this
    // fell through to the variable-headed F-split below, hit the dedup, and
    // returned `Saturated` → a sound but needless `Unknown`. Reporting it here,
    // BEFORE the F-split, is the whole fix.
    //
    // Scope (spec §2): the constant side must be ENTIRELY constant. The wider
    // rule (`W` containing other variables) is the deleted E1 probe's shape and
    // is deliberately out of scope.
    //
    // The `is_concat` guard fixes the probe's other defect: it tested
    // `string_const_value(..).is_none()`, which matches an unflattened CONCAT rep
    // as if it were a free variable. The wrapper flattens, but we do not rely on
    // that here — an atom that is still a CONCAT is never treated as a variable.
    {
        let l_res = &lhs[i..le];
        let r_res = &rhs[j..re];

        let is_concat = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrConcat),
                    ..
                }
            )
        };
        let is_free_var = |terms: &Context, t: TermId| {
            terms.string_const_value(t).is_none() && !is_concat(terms, t)
        };
        let all_const =
            |sl: &[TermId], terms: &Context| sl.iter().all(|&a| terms.string_const_value(a).is_some());

        let pair = if l_res.len() == 1 && is_free_var(terms, l_res[0]) && all_const(r_res, terms) {
            Some((l_res[0], r_res))
        } else if r_res.len() == 1 && is_free_var(terms, r_res[0]) && all_const(l_res, terms) {
            Some((r_res[0], l_res))
        } else {
            None
        };

        if let Some((var, const_side)) = pair {
            // Fold the constant side to ONE interned constant. The empty side
            // folds to "" — `v ≈ ""` is a legitimate propagation.
            let mut w = String::new();
            for &a in const_side {
                w.push_str(
                    terms
                        .string_const_value(a)
                        .expect("all_const checked every atom"),
                );
            }
            let word = terms.mk_string_const(&w);
            return StepResult::Propagate { var, word, just };
        }
    }
```

If `just` has already been moved by an earlier `return` path on some branch, the borrow checker will say so — in that case clone it at the top of this block. Do not restructure the earlier conflict paths to accommodate this one.

- [ ] **Step 5: Run the tests**

```bash
cargo nextest run -p shinri-str -E 'test(propagate) + test(pure_assignment) + test(variable_bearing_word)'
```

Expected: `4 tests run: 4 passed`.

- [ ] **Step 6: Run the whole str suite — expect a non-exhaustive-match failure**

```bash
cargo nextest run -p shinri-str
```

The new variant makes `lib.rs`'s `match` non-exhaustive. Add a temporary arm at the `StepResult::Saturated => {}` site in `crates/shinri-str/src/lib.rs` so the crate compiles; Task 5 replaces it:

```rust
                    // Slice 33 T5 wires this properly. Treating it as a no-op here
                    // is SOUND (it is exactly the pre-slice-33 behaviour) but gains
                    // nothing — the propagated fact is discarded.
                    crate::wordeq::StepResult::Propagate { .. } => {}
```

Re-run `cargo nextest run -p shinri-str`. Expected: all pass, with **no behaviour change yet**.

- [ ] **Step 7: Confirm the probes have NOT moved**

```bash
cargo nextest run -p shinri-solver -E 'test(probe_)'
```

Expected: `4 tests run: 4 passed` — still at the Task 1 baseline. If a probe flips here, the temporary no-op arm is not a no-op and something else changed; investigate before continuing.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all
cargo clippy -p shinri-str --all-targets -- -D warnings
git add crates/shinri-str/src/wordeq.rs crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice33 T4 — StepResult::Propagate + pure-assignment detection"
```

---

### Task 5: Wire the cited merge in the driver

**Purpose:** Turn the reported fact into a cited EUF merge. This is the load-bearing soundness step (spec §4).

**Files:**
- Modify: `crates/shinri-str/src/lib.rs:~660-795` (the word-equation resolution gate: the `normal_form_cited` call sites feeding `lhs`/`rhs`, the stale comment at `lib.rs:692`, and the `Propagate` match arm from Task 4)

**Interfaces:**
- Consumes: `StepResult::Propagate` (Task 4), `StrSolver::alloc_prop_tag` (Task 3), `StrSolver.prop_tags` (Task 2).
- Produces: no new API. Behaviour: probes E and G decide.

- [ ] **Step 1: Thread a live `ante` into the normal-form computation**

Find where `lhs` and `rhs` are computed for this word equation (the `normal_form_cited` calls feeding the `resolve_equation` block at `lib.rs:~693`). They currently discard antecedents. Give them a shared live vector:

```rust
                // Slice 33: the normal forms substitute EUF class representatives,
                // and a PROPAGATION merge derives a ground fact from exactly that
                // substituted material. So the antecedents must be captured — see
                // the revised comment below. Mirrors lib.rs:805-810, where the
                // disequality path already cites its substitution antecedents.
                let mut nf_ante: Vec<EqLeaf> = Vec::new();
```

Pass `&mut nf_ante` as the `ante` argument to both `normal_form_cited` calls instead of the throwaway vector they use today.

- [ ] **Step 2: Revise the now-false comment at `lib.rs:692`**

The existing comment claims no merge-antecedent citation is needed. A propagation outcome falsifies its premise. Replace it:

```rust
                // Build the EqLeaf justification from the asserted equality literal.
                // This feeds `expand_conflict` so the conflict clause cites the right
                // input literal.
                //
                // SLICE 33 REVISION. This comment used to read: "`resolve_equation`
                // never derives a ground conflict from a variable it substituted by a
                // concat class representative (it Saturates on a concat residual head
                // instead), so no extra merge-antecedent citation is needed here."
                // That premise is now FALSE. `StepResult::Propagate` derives a ground
                // FACT precisely from substituted material, so its merge cites
                // `Asserted(lit)` PLUS `nf_ante` (the normal-form substitution
                // antecedents) under an `EqJust::Interface` tag. The Conflict and
                // Split paths below are unchanged and still rely on the E1 gates.
                let just = vec![EqLeaf::Asserted(lit)];
```

- [ ] **Step 3: Replace the temporary `Propagate` arm with the real merge**

Replace the placeholder arm added in Task 4 Step 6:

```rust
                    crate::wordeq::StepResult::Propagate { var, word, mut just } => {
                        // Cite the normal-form substitution antecedents ALONGSIDE the
                        // asserted equation literal. Under-citing here is the ce2
                        // wrong-UNSAT shape (spec §4) — the merge would survive as a
                        // fact on branches where the substitution that produced it is
                        // no longer active.
                        just.extend(nf_ante.iter().copied());
                        just.sort_unstable_by_key(|l| match l {
                            EqLeaf::Asserted(x) => (0u8, x.code() as u64),
                            EqLeaf::Interface(j) => (1u8, ((j.theory as u64) << 32) | j.tag as u64),
                        });
                        just.dedup();

                        let tag = self.alloc_prop_tag(just);
                        let vn = cx.eq.intern(var);
                        let wn = cx.eq.intern(word);
                        // NO ATOM IS MINTED AND NO CLAUSE IS LEARNT, so E1's
                        // input_cond_roots / all_cond_roots gates do not apply — that
                        // gate is what halted slice 32. Branch-locality is structural:
                        // the merge is scoped by EqualityEngine::push/pop, and the tag
                        // by the str trail (Task 2).
                        match cx.eq.merge(
                            vn,
                            wn,
                            shinri_theory::types::EqJust::Interface(TheoryJust {
                                theory: <StrSolver as TheorySolver>::THEORY_ID,
                                tag,
                            }),
                        ) {
                            Ok(()) => {}
                            Err(conflict) => {
                                // The merge united a KNOWN-DISEQUAL pair — e.g.
                                // `y ≈ "ab"` against an asserted `distinct y "ab"`.
                                // Assemble the conflict in the SAME three parts as
                                // `Egraph::conflict_leaves` (shinri-euf/src/egraph.rs:441-479);
                                // this is that pattern specialised to a merge whose
                                // justification is a single Interface tag.
                                let mut cf: Vec<EqLeaf> = Vec::new();
                                // Part 1: why `var = word` was being merged. Our
                                // justification IS the interface tag, which the
                                // Combiner expands via StrSolver::explain
                                // (combiner.rs:900-901) back to `just`.
                                cf.push(EqLeaf::Interface(TheoryJust {
                                    theory: <StrSolver as TheorySolver>::THEORY_ID,
                                    tag,
                                }));
                                // Part 2: bridge the merged nodes to the disequality's
                                // ASSERTED endpoints. Orient by representative — pair
                                // `a` with whichever endpoint is already in a's class.
                                let ra = cx.eq.find(conflict.a);
                                let (a_end, b_end) = if cx.eq.find(conflict.diseq_lhs) == ra {
                                    (conflict.diseq_lhs, conflict.diseq_rhs)
                                } else {
                                    (conflict.diseq_rhs, conflict.diseq_lhs)
                                };
                                cx.eq.explain(conflict.a, a_end, &mut cf);
                                cx.eq.explain(conflict.b, b_end, &mut cf);
                                // Part 3: the disequality that was violated.
                                match conflict.diseq {
                                    shinri_theory::types::EqJust::Asserted(l) => {
                                        cf.push(EqLeaf::Asserted(l))
                                    }
                                    shinri_theory::types::EqJust::Interface(j) => {
                                        cf.push(EqLeaf::Interface(j))
                                    }
                                    shinri_theory::types::EqJust::Congruence(_)
                                    | shinri_theory::types::EqJust::Definitional => {}
                                }
                                return TCheck::Conflict(cf);
                            }
                        }
                    }
```

**Implementation note for the conflict branch:** `EqConflict` carries `a`, `b`, `diseq`, `diseq_lhs`, `diseq_rhs` (`types.rs:74-82`). Note that `shinri-str` has **no** existing conflict-assembly code to copy — every str-side `merge` today uses `EqJust::Definitional` and discards the error (`let _ = eq.merge(..)`), so this is the crate's first real one. The canonical pattern lives in `Egraph::conflict_leaves` (`crates/shinri-euf/src/egraph.rs:441-479`); read it before implementing, and keep all three parts. Dropping Part 2 is the easy mistake: without the bridge, the conflict cites `var ≈ word` and the disequality but not the chain linking them to the diseq's *asserted* endpoints, producing an under-cited (unsound) conflict clause.

Add `EqJust` to the `shinri_theory::types` import at `lib.rs:23` if you prefer the short path over the fully-qualified name.

- [ ] **Step 4: Run the probes — E and G should flip**

```bash
cargo nextest run -p shinri-solver -E 'test(probe_)' --no-fail-fast
```

Expected: `probe_e_empty_literal_concat` and `probe_g_asserted_empty_var` now **FAIL**, because their baseline assertion says `unknown` and the engine now answers `unsat`. That failure is the deliverable. `probe_c_len_zero_var` and `probe_f_control_direct_contradiction` must still **PASS**.

Record the actual verdict of all four probes — Task 6 pins them and the truth-up reports them.

If E and G do **not** flip, stop and report. The spec's §7 prediction is falsified and the diagnosis in the slice-32 retraction is incomplete.

- [ ] **Step 5: Run the full workspace suite**

```bash
cargo nextest run --workspace
```

Expected: everything passes except the two probe tests from Step 4, whose baselines Task 6 updates. Any **other** failure — especially `variable_equals_constant_splits_then_sat`, the `str_input_var_concat_length_*` family, or anything mentioning t8iter175 — is a real regression from this task and must be fixed before committing.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-str/src/lib.rs
git commit -m "feat(str): slice33 T5 — cited EUF merge for propagated pure assignments"
```

---

### Task 6: Pin, oracle-confirm, gate, truth-up, PR

**Purpose:** Turn the measured flips into pins, confirm them against z3, and close the slice honestly.

**Files:**
- Modify: `crates/shinri-solver/tests/slice33_probes.rs` (baselines → pins)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (oracle cases)
- Modify: `docs/superpowers/specs/2026-07-20-shinri-slice33-resolver-propagation-design.md` (truth-up section)

**Interfaces:**
- Consumes: the measured verdicts from Task 5 Step 4.
- Produces: the slice's final state.

- [ ] **Step 1: Oracle-confirm the flipped verdicts BEFORE pinning**

Add the flipped probes to the oracle differential suite in `crates/shinri-solver/tests/qfs_differential.rs`, following the existing case style in that file (read a neighbouring case first — the file is `#![cfg(feature = "oracle")]`, so it compiles only under the feature).

```bash
cargo nextest run -p shinri-solver --features oracle -E 'test(probe) + test(propagat)'
```

**Confirm the reported test count is non-zero.** Without `--features oracle` this suite silently runs 0 tests, and a 0-test run reads as green. If the count is 0, the filter or the feature flag is wrong — fix it before proceeding.

Expected: z3 agrees `unsat` on probes E and G.

If z3 disagrees with the engine on any query, **stop** — that is a soundness bug, not a pin update.

- [ ] **Step 2: Update the probe baselines to pins**

In `crates/shinri-solver/tests/slice33_probes.rs`, change the two flipped assertions and their doc comments:

```rust
/// Probe E — PIN (slice 33). The residual `[y] = ["ab"]` now propagates
/// `y ≈ "ab"`, which contradicts the asserted `distinct`. z3: unsat.
#[test]
fn probe_e_empty_literal_concat() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun y () String)
           (assert (= (str.++ "" y) "ab"))(assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}

/// Probe G — PIN (slice 33). The `x = ""` merge rewrites the normal form to
/// `[y]`; same propagation path as probe E. z3: unsat.
#[test]
fn probe_g_asserted_empty_var() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= x ""))(assert (= (str.++ x y) "ab"))
           (assert (distinct y "ab"))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}
```

Leave `probe_c_len_zero_var` asserting `unknown` and keep its NON-GOAL comment. If probe C *did* flip, do not quietly pin it — investigate, because the spec says it should not have, and an unexplained flip means the mechanism is wider than designed.

- [ ] **Step 3: Run the probes**

```bash
cargo nextest run -p shinri-solver -E 'test(probe_)'
```

Expected: `4 tests run: 4 passed`.

- [ ] **Step 4: Run the completeness-shifting gate**

This slice shifts completeness, so `script_e2e` runs locally before pushing:

```bash
cargo nextest run -p shinri-solver -E 'test(script_e2e)'
```

Expected: all pass. If a z3-confirmed `unknown → decided` pin flip appears here, that is an adjudicated flip, not a blocker — confirm it with the oracle and update the pin with a comment explaining the flip. A flip in the other direction (`decided → unknown`, or any `sat`/`unsat` disagreement) **is** a blocker.

- [ ] **Step 5: Full gate**

```bash
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo nextest run --workspace
cargo nextest run -p shinri-solver --features oracle
```

Expected: all clean. For the oracle run, **confirm a non-zero test count**.

- [ ] **Step 6: Truth-up the spec**

Append a `## 11. Outcome` section to `docs/superpowers/specs/2026-07-20-shinri-slice33-resolver-propagation-design.md` recording:
- The measured verdict of every probe (C/E/F/G), before and after, from the Task 1 and Task 5 runs — the **actual** values, not the predicted ones.
- Whether §7's predictions held. If any did not, say so plainly and explain what the real behaviour was.
- The oracle confirmation for each flipped pin.
- What remains open: probe C (the retracted wall-3 seam), the wider variable-bearing rule (§2), slice-31 §11 walls 1/2/4, and the standing bank.

Report what happened. Do not describe a prediction as a result.

- [ ] **Step 7: Commit and open the PR**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/slice33_probes.rs \
        crates/shinri-solver/tests/qfs_differential.rs \
        docs/superpowers/specs/2026-07-20-shinri-slice33-resolver-propagation-design.md
git commit -m "test(str): slice33 T6 — oracle-confirmed pins + truth-up"
git push -u origin slice33-resolver-propagation
gh pr create --base main --title "slice33: resolver propagation outcome" --body "$(cat <<'EOF'
Gives the word-equation resolver a propagation outcome (spec §3): an entailed
pure assignment `v ≈ W` (constant `W`) merges into EUF with cited antecedents
instead of falling through to an F-split dedup hit and a sound `Unknown`.

Closes the gap the slice-32 retraction identified by measurement — the gap was
never access to the emptiness fact, it was `StepResult` having no way to say
"this entails `y ≈ "ab"`".

- `StepResult::Propagate`, placed BEFORE the variable-headed F-split
- First real `StrSolver::explain`, over a trail-scoped tag→antecedent table
- `cited_lits` now sweeps interface justifications (closes the combiner.rs:442 gap)

No atom is minted and no clause is learnt, so E1's branch-locality gate — the
thing that halted slice 32 — does not apply.

Non-goal: probe C stays `unknown` (needs the retracted wall-3 seam).

See the spec's Outcome section for measured verdicts and oracle confirmations.
EOF
)"
```

Merge with a merge commit when CI is green, then delete the branch remote and local.

---

## Self-Review

**Spec coverage.** §1 problem → T4 (placement). §2 scope fence → T4 Step 1 `variable_bearing_word_does_not_propagate`. §3 mechanism incl. constant folding → T4 Steps 3–4 + the fold test. §4 citation → T5 Steps 1–3. §4.1 `explain` → T3. §4.2 tag lifecycle → T2. §5 why E1 doesn't apply → T5 Step 3 comment. §6 conflict path → T5 Step 3 `Err` branch. §7 measured acceptance → T1 + T5 Step 4 + T6 Steps 1–2. §8 testing → T6 Steps 3–5. §9.1 risk → T2 Step 1 backtracking test. §9.2 risk → T2 Step 5 `cited_lits`. §9.3 → T4 scope-fence test. §10 non-goals → probe C held at `unknown` in T6 Step 2. No gaps.

**Placeholder scan.** The first draft had a `push_leaf_from_diseq` stand-in in T5 Step 3 pointing at "the existing `EqConflict` handling in this file". Verification showed that pattern does not exist — `shinri-str` has no conflict assembly at all, since every str-side merge is `Definitional` with the error discarded. Replaced with the real three-part code, adapted from `Egraph::conflict_leaves`, plus a note on which part is easiest to drop and why dropping it is unsound. No placeholders remain. T4 Step 1 and T1 Step 1 direct the implementer to mirror neighbouring test setup rather than guessing at `Context`/`Lit` construction — those are deliberate, since the surrounding tests are the authority on that boilerplate.

**Type consistency.** `prop_tags: Vec<Vec<EqLeaf>>` (T2) is read by `expand_prop_tag` and appended by `alloc_prop_tag` (T3), which T5 calls. `Trail::push`/`pop_to` are 5-tuples at every call site (T2 Steps 3, 5). `StepResult::Propagate { var, word, just }` field names match between T4's definition and T5's match arm. `THEORY_ID` is reached through `<StrSolver as TheorySolver>` since it is a trait constant.
