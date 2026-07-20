# Slice 35 — Propagation Hardening Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the two soundness-shaped slice-34 bank items: downgrade `Propagate → Saturated` off wrapper-flattened words (the uncited EUF-strip window), and make `fresh_str` collision-proof in both directions (lookup-skip + `reserve_symbol`).

**Architecture:** Two independent point fixes in `crates/shinri-str/src/wordeq.rs`, each a pure restriction / freshness tightening with no new citation machinery. Spec: `docs/superpowers/specs/2026-07-20-shinri-slice35-propagation-hardening-design.md` (read it first — §1 has the hazard analysis, §3 the exact mechanisms).

**Tech Stack:** Rust workspace, cargo-nextest, z3/cvc5 oracles via mise, gh CLI.

## Global Constraints

- Feature work on a slice branch: `slice35-propagation-hardening`, PR to `main`, merge commit on green, then delete branch remote+local.
- `cargo fmt --all` before every push; CI gates on `fmt --check` and fails fast.
- `cargo clippy --workspace --all-targets -- -D warnings` must be clean.
- Oracle tests are feature-gated: ALWAYS `--features oracle`, and ALWAYS confirm a non-zero test count (without the flag they silently run 0 tests — never report that as green).
- Run oracle/gate commands in the FOREGROUND with captured output; never claim green from a backgrounded run you didn't read.
- nextest positional filters find 0 tests on nextest 0.9.140 — use `-E 'test(name)'` / `-E 'binary(name)'` and confirm discovery.
- Blocking-tier budget 10–15 min wall-clock; the new tests here are all sub-second. Never touch the `#[ignore]`d `shinri-fp` exhaustives.
- Pure-Rust mandate: no new dependencies of any kind in this slice.
- Expected dump-and-diff outcome is **zero verdict changes** (spec §4). Any `decided → unknown` is approach A's measured completeness cost: record in the truth-up, adjudicate, and it becomes the trigger for un-banking approach B (spec §2). Any `sat ↔ unsat`: BLOCKER.

---

### Task 0: Branch

**Files:** none (git only)

**Interfaces:**
- Consumes: `main` at `c301e993` (slice-35 spec commit) or later.
- Produces: branch `slice35-propagation-hardening`; all later tasks commit here.

- [ ] **Step 1: Cut the branch**

```bash
cd /workspace
git checkout main && git pull --ff-only
git checkout -b slice35-propagation-hardening
git log --oneline -1
```

Expected: branch created; tip is `c301e993` (or a later main commit — record the actual tip SHA; Task 4 uses it as the dump-and-diff BASE).

---

### Task 1: Propagate downgrade off flattened words

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs:438-444` (the `resolve_equation` wrapper match)
- Test: `crates/shinri-str/src/wordeq.rs` (`mod tests`, append after `single_concat_atom_does_not_propagate`, ~line 1622)

**Interfaces:**
- Consumes: `resolve_equation(...) -> StepResult` (existing, unchanged signature); test helpers `mk_var`/`declare_str_var`, `dummy_eqn_lit` (`wordeq.rs:920-935`).
- Produces: behavioral guarantee for Task 4's gates — `resolve_equation` never returns `Propagate` when it had to flatten a concat atom. No API change.

- [ ] **Step 1: Write the two failing tests**

Append to `mod tests` in `crates/shinri-str/src/wordeq.rs`, directly after `single_concat_atom_does_not_propagate` (~line 1622):

```rust
    /// Slice 35: a pure-assignment residual reached only by FLATTENING a
    /// concat class-rep must NOT propagate. The strip loops over flattened
    /// atoms can consume via `eq.are_equal` on class equalities cited in
    /// neither `just` nor `nf_ante`, so a `Propagate` here would land an
    /// under-justified EUF merge (wrong-UNSAT shape) — the same reason the
    /// wrapper downgrades `Conflict`. Must be `Saturated`.
    /// Control: `pure_assignment_folds_multi_atom_constant_side` pins that
    /// the identical residual WITHOUT a concat atom still propagates.
    #[test]
    fn flattened_pure_assignment_does_not_propagate() {
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
        assert!(
            matches!(r, StepResult::Saturated),
            "a Propagate off a flattened concat rep is under-cited and must \
             be downgraded to Saturated"
        );
    }

    /// Slice 35: the alias variant of the case above — flattening exposes a
    /// strippable constant head, leaving a var–var residual that slice 34
    /// would merge. Same under-citation hazard, same downgrade: `Saturated`.
    /// Control: `alias_residual_propagates` pins the no-concat alias shape.
    #[test]
    fn flattened_alias_residual_does_not_propagate() {
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
            matches!(r, StepResult::Saturated),
            "an alias residual off a flattened concat rep must be downgraded \
             to Saturated"
        );
    }
```

(`StepResult` deliberately has no `#[derive(Debug)]` — keep the assert messages plain, matching the existing tests' style; do NOT add the derive.)

- [ ] **Step 2: Run the new tests — expect FAIL**

```bash
cargo nextest run -p shinri-str -E 'test(flattened_pure_assignment_does_not_propagate) + test(flattened_alias_residual_does_not_propagate)'
```

Expected: **2 tests discovered** (confirm — 0 discovered means the filter is wrong), both FAIL: today the wrapper passes `Propagate` through, so the residuals propagate (`x ≈ "ab"` and `x ≈ y` respectively) instead of saturating.

- [ ] **Step 3: Add the downgrade arm**

In `crates/shinri-str/src/wordeq.rs`, the wrapper match currently reads (lines 438-444):

```rust
    match resolve_inner(
        terms, eq, &lhs_flat, &rhs_flat, just, eqn_lit, fresh_ctr, emitted,
    ) {
        // A conflict off a flattened concat rep would be under-cited → Saturate.
        StepResult::Conflict(_) => StepResult::Saturated,
        other => other,
    }
```

Change to:

```rust
    match resolve_inner(
        terms, eq, &lhs_flat, &rhs_flat, just, eqn_lit, fresh_ctr, emitted,
    ) {
        // A conflict off a flattened concat rep would be under-cited → Saturate.
        StepResult::Conflict(_) => StepResult::Saturated,
        // A Propagate off a flattened concat rep is under-cited the same way:
        // the strips over flattened inner atoms (never rep-substituted by
        // normal_form) can consume via `eq.are_equal` on class equalities
        // cited in neither `just` nor `nf_ante`, so the EUF merge this would
        // land is under-justified — a wrong-UNSAT shape. Saturate,
        // symmetrically with Conflict (slice 35; approach B in the spec is
        // the banked completeness-restoring alternative).
        StepResult::Propagate { .. } => StepResult::Saturated,
        other => other,
    }
```

Also update the wrapper's doc comment: in the block at `wordeq.rs:393-411`, point 2 currently ends at "…every b10bd27 constant-length exemplar still Conflicts." Append a third point:

```rust
/// 3. Symmetrically, if a concat atom WAS flattened and the inner resolver
///    reports a PROPAGATE, downgrades it to `Saturated` for the same
///    under-citation reason: the merge it would land could depend on an
///    uncited `eq.are_equal` strip (slice 35).
```

- [ ] **Step 4: Run the new tests plus the propagation controls — expect PASS**

```bash
cargo nextest run -p shinri-str -E 'test(flattened_) + test(propagat) + test(alias)'
```

Expected: all discovered tests pass — the two new tests now `Saturated`, and the slice-33/34 controls (`pure_assignment_propagates_constant_word`, `pure_assignment_folds_multi_atom_constant_side`, `pure_assignment_propagates_with_variable_on_right`, `alias_residual_propagates`, `alias_after_head_strip_propagates`, plus the does-not-propagate fences) all unchanged. Then the whole crate:

```bash
cargo nextest run -p shinri-str
```

Expected: 0 failures.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-str/src/wordeq.rs
git commit -m "fix(str): slice35 — downgrade Propagate off flattened concat reps (uncited-strip window)"
```

---

### Task 2: `fresh_str` freshness (lookup-skip + reserve)

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs:50-64` (`fresh_str`) and `wordeq.rs:66-81` (`is_minted_skolem` doc comment only)
- Test: `crates/shinri-str/src/wordeq.rs` (`mod tests`, append after Task 1's tests)

**Interfaces:**
- Consumes: `Context::lookup_symbol(&self, text: &str) -> Option<SymbolId>` (`shinri-core/src/context.rs:184`), `Context::reserve_symbol(&mut self, sym: SymbolId)` (`context.rs:190`), `Context::is_reserved(&self, sym: SymbolId) -> bool` (`context.rs:195`).
- Produces: `fresh_str(terms: &mut Context, ctr: &mut u32) -> TermId` — signature UNCHANGED; new guarantees: the returned term's symbol was not previously interned, and it is reserved (parser rejects later user declaration via `reject_reserved`, `shinri-parser/src/parser.rs:63-68`). Task 3's e2e pins rely on both.

- [ ] **Step 1: Write the two failing tests**

Append to `mod tests` in `crates/shinri-str/src/wordeq.rs` (after Task 1's tests). Note `fresh_str` is already imported at the module top via `use crate::wordeq::{...}` — extend that import if needed (`use crate::wordeq::fresh_str;`).

```rust
    /// Slice 35: a user-declared `|!strk0|` that predates minting must NOT be
    /// adopted as a skolem — `fresh_str` skips user-owned names, so the
    /// minted term is a distinct TermId under the next free name.
    #[test]
    fn fresh_str_skips_user_owned_name() {
        let mut ctx = Context::new();
        let user = declare_str_var(&mut ctx, "!strk0");
        let mut ctr = 0u32;
        let minted = fresh_str(&mut ctx, &mut ctr);
        assert_ne!(
            minted, user,
            "minting must never hash-cons onto a pre-declared user |!strk0|"
        );
        assert!(
            ctx.lookup_symbol("!strk1").is_some(),
            "the mint must have landed on the next free name !strk1"
        );
        assert_eq!(ctr, 2, "counter passed the taken name and the minted one");
    }

    /// Slice 35: a minted `!strk` name is reserved, so a later user
    /// declaration is rejected at parse time (same regime as word_norm's
    /// `ite!` names). The user-owned name from the skip case is NOT reserved.
    #[test]
    fn fresh_str_reserves_minted_name_only() {
        let mut ctx = Context::new();
        let _user = declare_str_var(&mut ctx, "!strk0");
        let mut ctr = 0u32;
        let _minted = fresh_str(&mut ctx, &mut ctr);
        let user_sym = ctx.lookup_symbol("!strk0").unwrap();
        let minted_sym = ctx.lookup_symbol("!strk1").unwrap();
        assert!(
            !ctx.is_reserved(user_sym),
            "the user-owned name must stay a normal free constant"
        );
        assert!(
            ctx.is_reserved(minted_sym),
            "the minted name must be reserved against later user declaration"
        );
    }
```

- [ ] **Step 2: Run the new tests — expect FAIL**

```bash
cargo nextest run -p shinri-str -E 'test(fresh_str_)'
```

Expected: **2 tests discovered**, both FAIL — today `fresh_str` bare-declares `!strk0`, hash-consing onto the user term (`assert_ne!` fails) and reserving nothing.

- [ ] **Step 3: Rewrite `fresh_str`**

Replace `fresh_str` (`wordeq.rs:50-64`) — keeping the BRANDING CONTRACT comment, extending it — with:

```rust
/// Mint a fresh string constant `!strk<N>` and return its term ID.
///
/// BRANDING CONTRACT (load-bearing): the `!strk` name prefix is how
/// `is_minted_skolem` below recognizes a term minted here. If this prefix
/// ever changes, `is_minted_skolem` MUST change with it — keep the two in
/// sync.
///
/// FRESHNESS (slice 35, mirrors word_norm's `ite!` mint): user-owned names
/// are skipped (a pre-declared `|!strkN|` is never adopted as a skolem),
/// and the minted name is reserved so a later user `declare-fun` naming it
/// is rejected at parse time — otherwise the user's app hash-conses to the
/// skolem and inherits its internal identity (wrong-verdict shape; see the
/// slice-5 `ite!` finding).
pub fn fresh_str(terms: &mut Context, ctr: &mut u32) -> TermId {
    let str_s = terms.string_sort();
    loop {
        let name = format!("!strk{}", *ctr);
        *ctr += 1;
        if terms.lookup_symbol(&name).is_some() {
            continue; // user (or an earlier check) owns this name
        }
        let sym = terms.declare_fun(&name, &[], str_s);
        terms.reserve_symbol(sym);
        return terms
            .mk_app(Op::Uninterpreted(sym), &[])
            .expect("well-sorted");
    }
}
```

Then narrow the `is_minted_skolem` doc comment (`wordeq.rs:66-81`): find the sentence about the false positive ("…a user symbol literally declared as `|!strkN|` would false-positive here.") and extend it in place:

```rust
/// user symbol literally declared as `|!strkN|` would false-positive here.
/// Since slice 35, `fresh_str` skips user-owned names and reserves minted
/// ones, so such a term is never ALSO a skolem — the false positive only
/// narrows completeness (the slice-34 guard declines to propagate), never
/// soundness. The tracked-TermId-set upgrade remains banked.
```

- [ ] **Step 4: Run the crate — expect PASS**

```bash
cargo nextest run -p shinri-str
```

Expected: 0 failures — the two new tests pass, and no existing test pinned a specific `!strkN` spelling against a colliding user declaration (the skolem-named tests `skolem_skolem_residual_does_not_propagate` / `mixed_var_skolem_residual_does_not_propagate` declare `!strk*` names WITHOUT calling `fresh_str`, so they are unaffected). If anything else fails, STOP and report — do not adjust unrelated pins.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-str/src/wordeq.rs
git commit -m "fix(str): slice35 — fresh_str skips user-owned !strk names and reserves minted ones"
```

---

### Task 3: e2e reservation pins (`script_e2e.rs`)

**Files:**
- Test: `crates/shinri-solver/tests/script_e2e.rs` (append after `user_ite_name_declared_before_any_mint_still_works`, ~line 166)

**Interfaces:**
- Consumes: `run_script(src: &str) -> Vec<String>` (top of `script_e2e.rs`); Task 2's reservation guarantee; the parser rejection message `"reserved for solver-internal use"` (`parser.rs:68`).
- Produces: the two e2e pins Task 4's gates run.

- [ ] **Step 1: Measure the mint script's verdicts**

The str skolem mint fires on an F-split. The probe query `(= (str.++ x "ab") (str.++ "a" y))` is variable-headed after normalization and z3-SAT (witness: `x = "a"`, `y = "ab"`). Confirm both facts before writing pins:

```bash
cat > /tmp/claude-1000/-workspace/e13672f0-c438-4992-bf4d-ee74d5821dd5/scratchpad/s35probe.smt2 <<'EOF'
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x "ab") (str.++ "a" y)))
(check-sat)
EOF
z3 /tmp/claude-1000/-workspace/e13672f0-c438-4992-bf4d-ee74d5821dd5/scratchpad/s35probe.smt2
cargo run -p shinri-cli --release -- /tmp/claude-1000/-workspace/e13672f0-c438-4992-bf4d-ee74d5821dd5/scratchpad/s35probe.smt2 2>/dev/null || true
```

Expected: z3 prints `sat`. Record shinri's verdict (`sat` or `unknown` are both acceptable; if the cli invocation form differs, run the query through a scratch `run_script` test with `--nocapture` instead — do NOT skip the measurement). If shinri prints `unsat`, STOP: that is a wrong verdict on a z3-sat query — a pre-existing blocker to report, not to code around.

Also confirm the mint actually fires with counter 0 first: after Step 2's test exists, a failing `out[1]` (no rejection error) with the reservation code in place means the script minted no `!strk0` — pick a different F-split query shape and re-measure rather than weakening the assert.

- [ ] **Step 2: Write the two e2e tests**

Append to `crates/shinri-solver/tests/script_e2e.rs` after the `ite!` pair (~line 166). In the asserts below, `V` is the Step-1 measured shinri verdict for the probe query — write it as the literal string measured (`"sat"` or `"unknown"`); the spelled-out asserts additionally hard-fail on any `unsat`:

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Slice 35 — str skolem freshness (spec §3b): `fresh_str` now mirrors the
// word_norm `ite!` regime. A user declaration naming a minted `!strk<n>` must
// be REJECTED, not silently aliased; a user `!strk<n>` declared BEFORE any
// mint stays a usable free constant (the mint skips it).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn post_mint_declaration_of_strk_name_is_rejected() {
    // check-sat #1 F-splits the variable-headed equation and mints !strk
    // skolems starting at !strk0. The later user declaration of !strk0 must
    // hit the parser's reserved-name rejection; its use is then undeclared.
    let out = run_script(
        "(declare-const x String)(declare-const y String)\
         (assert (= (str.++ x \"ab\") (str.++ \"a\" y)))\
         (check-sat)\
         (declare-const !strk0 String)\
         (assert (= !strk0 \"z\"))\
         (check-sat)",
    );
    assert_eq!(out.len(), 4, "verdict / declare-error / use-error / verdict, got {out:?}");
    assert_eq!(out[0], V, "measured base verdict for the probe query");
    assert!(
        out[1].contains("reserved for solver-internal use"),
        "declaration of the minted name must be rejected, got {:?}",
        out[1]
    );
    assert!(
        out[2].starts_with("(error"),
        "aliased use is undeclared, got {:?}",
        out[2]
    );
    assert!(
        !out.contains(&"unsat".to_string()),
        "no wrong UNSAT anywhere (z3: sat), got {out:?}"
    );
}

#[test]
fn user_strk_name_declared_before_any_mint_still_works() {
    // A user who owns !strk0 before any mint keeps a normal free constant:
    // fresh_str's probe skips the taken name and never reserves it. The
    // verdict must match the mint-free measurement — no aliasing, no
    // wrong UNSAT.
    let out = run_script(
        "(declare-const !strk0 String)\
         (declare-const x String)(declare-const y String)\
         (assert (= (str.++ x \"ab\") (str.++ \"a\" y)))\
         (assert (= !strk0 \"q\"))\
         (check-sat)",
    );
    assert_eq!(out.len(), 1, "single verdict, got {out:?}");
    assert_eq!(out[0], V, "user !strk0 must not perturb the probe verdict");
    assert!(
        !out.contains(&"unsat".to_string()),
        "no wrong UNSAT (z3: sat with !strk0 = \"q\"), got {out:?}"
    );
}
```

- [ ] **Step 3: Run the two tests — expect PASS**

```bash
cargo nextest run -p shinri-solver -E 'test(strk_name)'
```

Expected: **2 tests discovered**, both pass. If `out[1]` in the first test is not the rejection error, see Step 1's note (mint didn't fire or numbering differs) — diagnose with `--no-capture` before changing anything.

- [ ] **Step 4: Confirm the slice-33/34 probe pins are unchanged**

```bash
cargo nextest run -p shinri-solver -E 'binary(slice33_probes) + binary(slice34_probes) + binary(script_e2e)'
```

Expected: all discovered tests pass, zero pin edits needed. Probe B1 in `slice34_probes` must still read `unknown` (the fence witness). Any flip here is unexpected for this slice — STOP and report.

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/script_e2e.rs
git commit -m "test(str): slice35 — !strk reservation e2e pins (post-mint reject, pre-mint skip)"
```

---

### Task 4: Oracle gate, dump-and-diff, full gates, truth-up, PR

**Files:**
- Modify (TEMPORARY, reverted in-task): `crates/shinri-solver/tests/qfs_differential.rs` (DIFFDUMP instrumentation)
- Modify: `docs/superpowers/specs/2026-07-20-shinri-slice35-propagation-hardening-design.md` (append `## 6. Outcome`)

**Interfaces:**
- Consumes: Tasks 1–3 committed; the BASE SHA recorded in Task 0.
- Produces: the merged PR.

- [ ] **Step 1: Oracle gate (foreground, captured)**

```bash
cargo nextest run -p shinri-solver --features oracle
```

Expected: ~497 passed, 0 failed, ~3 skipped, **confirmed non-zero count**, ~20 min — run in the foreground with output captured (background it via the harness only if wall-clock forces it, and read the full output before claiming green).

- [ ] **Step 2: Add the temporary per-iteration dump (NOT committed)**

All fuzz families funnel through two helpers in `qfs_differential.rs`: `shinri_lines` (~line 56) and `shinri_lines_counting_bailouts` (~line 96). In EACH, immediately before the final return, insert:

```rust
    // TEMP DIFFDUMP (slice 35 dump-and-diff — do not commit)
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

In `shinri_lines` (no `bailouts` binding) bind the expression that function already reads (~line 74, `solver.theory_guard_bailouts()`) to a local first. Fixed LCG seeds give query-text identity across runs, so the src hash is a stable join key.

- [ ] **Step 3: Dump the fix side**

```bash
SHINRI_DIFFDUMP=1 cargo test -p shinri-solver --test qfs_differential --features oracle -- --test-threads=1 2> /tmp/claude-1000/-workspace/e13672f0-c438-4992-bf4d-ee74d5821dd5/scratchpad/dump-fix.txt
grep -c DIFFDUMP /tmp/claude-1000/-workspace/e13672f0-c438-4992-bf4d-ee74d5821dd5/scratchpad/dump-fix.txt
```

Expected: 0 test failures and **thousands** of DIFFDUMP lines (~3900). A line count near 0 means stderr was swallowed — the run is NOT a valid dump; re-check the `2>` redirection and `--test-threads=1` before trusting anything.

- [ ] **Step 4: Dump the base side from a worktree at the Task-0 BASE SHA**

```bash
git worktree add /tmp/claude-1000/-workspace/e13672f0-c438-4992-bf4d-ee74d5821dd5/scratchpad/base-wt <BASE-SHA-from-Task-0>
```

Apply the SAME Step-2 instrumentation to `base-wt/crates/shinri-solver/tests/qfs_differential.rs` (same two helpers, same code), then:

```bash
cd /tmp/claude-1000/-workspace/e13672f0-c438-4992-bf4d-ee74d5821dd5/scratchpad/base-wt
SHINRI_DIFFDUMP=1 cargo test -p shinri-solver --test qfs_differential --features oracle -- --test-threads=1 2> ../dump-base.txt
grep -c DIFFDUMP ../dump-base.txt
cd /workspace
```

Expected: line count equal to the fix side (this slice adds no qfs_differential cases).

- [ ] **Step 5: Diff — the invariant for THIS slice is zero changes**

```bash
cd /tmp/claude-1000/-workspace/e13672f0-c438-4992-bf4d-ee74d5821dd5/scratchpad
grep DIFFDUMP dump-base.txt | sort > base-sorted.txt
grep DIFFDUMP dump-fix.txt  | sort > fix-sorted.txt
diff base-sorted.txt fix-sorted.txt
cd /workspace
```

Expected (spec §4): **empty diff** — the downgraded window has never been observed firing, and `fresh_str` collisions cannot occur in oracle-generated queries. If any hash flips `decided → unknown`, that is approach A's measured completeness cost: record the hash and both verdicts in the truth-up, and note it as the trigger for un-banking approach B (spec §2). Any `sat ↔ unsat` or bailout increase: BLOCKER — stop and report.

- [ ] **Step 6: Revert the instrumentation and remove the worktree**

```bash
git status
git diff --stat
```

Confirm the ONLY uncommitted change is `qfs_differential.rs` (the two DIFFDUMP blocks — Tasks 1–3 are already committed). Then:

```bash
git checkout -- crates/shinri-solver/tests/qfs_differential.rs
git worktree remove --force /tmp/claude-1000/-workspace/e13672f0-c438-4992-bf4d-ee74d5821dd5/scratchpad/base-wt
git status
```

- [ ] **Step 7: Completeness-shifting gate**

```bash
cargo nextest run -p shinri-solver -E 'binary(script_e2e)'
```

Expected: ~69 tests discovered (67 prior + the 2 new pins), all pass. A z3-confirmed `unknown → decided` pin flip is adjudicated, not a blocker — none expected in this slice; `decided → unknown` or any `sat`/`unsat` disagreement IS a blocker.

- [ ] **Step 8: Full gate**

```bash
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo nextest run --workspace
```

Expected: fmt clean; clippy 0 warnings; ~1135 passed, 0 failed, 7 skipped (the `#[ignore]`d nightly `shinri-fp` exhaustives), ~5 min.

- [ ] **Step 9: Truth-up the spec**

Append `## 6. Outcome` to `docs/superpowers/specs/2026-07-20-shinri-slice35-propagation-hardening-design.md` recording, with measured numbers: the two unit fences and both e2e pin verdicts (the measured `V`), the oracle count, the dump-and-diff tally (expected: N hashes, 0 diffs — state N), the script_e2e count, and the full-gate counts. If anything deviated from the spec's expectations (e.g. a recorded completeness cost from Step 5), document the adjudication inline. Commit:

```bash
git add docs/superpowers/specs/2026-07-20-shinri-slice35-propagation-hardening-design.md
git commit -m "docs: slice35 truth-up — measured outcomes"
```

- [ ] **Step 10: Push, PR, merge on green**

```bash
git push -u origin slice35-propagation-hardening
gh pr create --title "fix(str): slice35 — propagation hardening (uncited-Propagate downgrade + !strk freshness)" --body "Spec: docs/superpowers/specs/2026-07-20-shinri-slice35-propagation-hardening-design.md. Closes the two soundness-shaped slice-34 bank items: Propagate is downgraded to Saturated off wrapper-flattened concat reps (symmetric with the existing Conflict downgrade), and fresh_str adopts the word_norm mint pattern (lookup-skip + reserve_symbol). Dump-and-diff: zero verdict changes. Oracle: green, non-zero count confirmed."
gh pr checks --watch
```

Standing rule: merge with a merge commit when CI is green, then delete the branch remote and local (`git checkout main && git pull --ff-only && git branch -d slice35-propagation-hardening && git push origin --delete slice35-propagation-hardening && git remote prune origin`).
