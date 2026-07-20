# Slice 34 — Alias Propagation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Propagate the alias residual `[v] = [u]` (one free variable each side) as `v ≈ u` through the slice-33 `Propagate` machinery, flipping the measured `unknown` alias probes to oracle-confirmed `unsat`.

**Architecture:** One new detection case in the slice-33 pure-assignment block of `resolve_inner` (`crates/shinri-str/src/wordeq.rs`). The driver arm, prop-tag citation, `explain`, cond_roots tracking, and conflict assembly are reused verbatim — they are shape-agnostic (`lib.rs:890-976` interns two `TermId`s and merges). No changes outside `wordeq.rs` code; tests and doc truth-ups elsewhere.

**Tech Stack:** Rust, `cargo nextest`, `mise` tasks, z3 (and cvc5 out of band) via the `oracle` feature.

**Branch:** `slice34-alias-propagation` (exists; spec committed at `bdda4cc5`).

**Spec:** `docs/superpowers/specs/2026-07-20-shinri-slice34-alias-propagation-design.md` — read it before starting any task.

## Global Constraints

- Oracle differential tests are feature-gated: **without `--features oracle` they silently run 0 tests** — never report that as green. Confirm a non-zero test count on every oracle run.
- nextest filters: use `-E 'test(name)'` / `-E 'binary(name)'`. A bare `mod::name` positional filter finds 0 tests on nextest 0.9.140 and reads as green.
- All new tests must run in seconds (blocking PR tier); no `#[ignore]` candidates in this slice.
- `cargo fmt --all` before every push; `cargo clippy --workspace --all-targets -- -D warnings` must be clean.
- Scope fence (spec §2): the MULTI-ATOM variable-bearing word must NOT propagate. Only the var–var alias case is added.
- Verdict-flip adjudication: a z3-confirmed `unknown → decided` flip is an adjudicated completeness gain, not a blocker. `decided → unknown` or any `sat ↔ unsat` disagreement IS a blocker.
- Report measurements, not predictions. If a §7 prediction fails, record what actually happened and adjudicate; do not force the predicted verdict.

---

### Task 1: Measured probe baseline (`slice34_probes.rs`)

**Files:**
- Create: `crates/shinri-solver/tests/slice34_probes.rs`

**Interfaces:**
- Consumes: `shinri_parser::Parser`, `shinri_solver::{CommandResponse, Solver}` (public API).
- Produces: probe test names `probe_a1_prefix_alias`, `probe_a2_suffix_alias`, `probe_a3_sat_control`, `probe_a4_chain`, `probe_b1_multi_atom_fence` — Task 3 re-measures and edits these pins in place.

- [ ] **Step 1: Write the baseline probe file**

The `run_script` helper is copied from `slice33_probes.rs:13-31` because Rust integration test files are separate crates and cannot share private helpers. The baseline verdicts below were measured on base `17ef967e` during brainstorming; this task re-confirms them from a committed test.

```rust
//! Slice 34 probes (spec §7). These pin the alias-propagation frontier.
//!
//! Written BEFORE the implementation as a measured baseline: A1/A2/A4 record
//! the engine's current sound-but-needless `unknown` (z3 says `unsat` for all
//! three), A3 is the SAT control, and B1 pins the §2 scope fence (the
//! multi-atom variable-bearing shape, banked — must NOT flip this slice).
//! Task 3 re-measures after the mechanism lands and flips A1/A2/A4 only after
//! oracle confirmation.
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
            Err(diag) => out.push(format!("(error \"{}\")", diag.message)),
        }
    }
    out
}

/// Probe A1 — BASELINE. `"a"·x = "a"·y` strips the shared head to the alias
/// residual `[x] = [y]`, which today falls through to F-split → dedup →
/// `Saturated` → a sound `unknown`. z3: unsat (cancellation entails x = y).
#[test]
fn probe_a1_prefix_alias() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ "a" x) (str.++ "a" y)))
           (assert (distinct x y))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "baseline; Task 3 flips this pin");
}

/// Probe A2 — BASELINE. Suffix twin of A1: tail-stripping produces the same
/// alias residual. z3: unsat.
#[test]
fn probe_a2_suffix_alias() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ x "a") (str.++ y "a")))
           (assert (distinct x y))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "baseline; Task 3 flips this pin");
}

/// Probe A3 — SAT CONTROL. The alias equation alone. A var–var merge creates
/// a string class with NO constant member (spec §5); model construction must
/// keep producing a self-check-passing model. Must stay `sat` throughout.
#[test]
fn probe_a3_sat_control() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ "a" x) (str.++ "a" y)))(check-sat)"#,
    );
    assert_eq!(out, vec!["sat"], "control: must never regress");
}

/// Probe A4 — BASELINE. Chained aliasing: two alias merges (`x ≈ y`, `y ≈ z`)
/// must compose so `distinct x z` conflicts. Exercises the §11.6 per-merge
/// eager cond_roots re-insertion on chained propagations (spec §9). z3: unsat.
#[test]
fn probe_a4_chain() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (declare-fun z () String)
           (assert (= (str.++ "a" x) (str.++ "a" y)))
           (assert (= (str.++ "b" y) (str.++ "b" z)))
           (assert (distinct x z))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "baseline; Task 3 flips this pin");
}

/// Probe B1 — SCOPE FENCE (spec §2, banked shape). After stripping, the
/// residual is `[x] = [y, "b"]` — MULTI-ATOM and variable-bearing. The fence
/// says this must NOT propagate; the pin says the verdict must NOT flip this
/// slice. z3: unsat — the gap is real and banked WITH this measurement.
#[test]
fn probe_b1_multi_atom_fence() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ "a" x) (str.++ "a" y "b")))
           (assert (distinct x (str.++ y "b")))(check-sat)"#,
    );
    assert_eq!(out, vec!["unknown"], "banked shape: must NOT flip in slice 34");
}
```

- [ ] **Step 2: Run the probes — all five must pass at base**

```bash
cargo nextest run -p shinri-solver -E 'binary(slice34_probes)'
```

Expected: `5 tests run: 5 passed`. If any baseline assertion fails, STOP — the base measurement in the spec is wrong; re-measure and reconcile with the spec before continuing.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/slice34_probes.rs
git commit -m "test(str): slice34 T1 — measured probe baseline (A1–A4, B1)"
```

---

### Task 2: Alias detection in `resolve_inner` (TDD)

**Files:**
- Modify: `crates/shinri-str/src/wordeq.rs:15-31` (the `StepResult::Propagate` doc comment)
- Modify: `crates/shinri-str/src/wordeq.rs:625-682` (the slice-33 block: header comment + new case)
- Modify: `crates/shinri-str/src/wordeq.rs:1412-1436` (rename + narrow the fence test)
- Test: `crates/shinri-str/src/wordeq.rs` (tests module, after the slice-33 propagation tests at ~line 1436)

**Interfaces:**
- Consumes: `resolve_equation(...) -> StepResult` and the tests-module helpers `declare_str_var` (`wordeq.rs:851`), `dummy_eqn_lit` (`wordeq.rs:838`); `StepResult::Propagate { var, word, just }` unchanged in shape.
- Produces: `StepResult::Propagate` now also returned for var–var residuals, with `var` = left residual atom, `word` = right residual atom (a VARIABLE `TermId`, not a constant). Task 3's e2e probes rely on this via the unchanged driver.

- [ ] **Step 1: Write the failing unit tests**

Add after `variable_bearing_word_does_not_propagate` (~line 1436), inside the existing tests module:

```rust
    // ── Slice 34: alias propagation ──────────────────────────────────────────
    // A residual `[v] = [u]` (free variable each side, distinct classes — the
    // stripping loop guarantees distinctness) entails `v ≈ u` by cancellation
    // and must PROPAGATE, not fall to the F-split → dedup → Saturated path.

    /// The core shape: `[x] = [y]` reports `x ≈ y`, left residual as `var`.
    #[test]
    fn alias_residual_propagates() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_al");
        let y = declare_str_var(&mut ctx, "y_al");
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx, &mut eq, &[x], &[y], just, lit, &mut ctr, &mut emitted,
        );
        match r {
            StepResult::Propagate { var, word, just } => {
                assert_eq!(var, x, "left residual must be reported as `var`");
                assert_eq!(word, y, "right residual must be reported as `word`");
                assert!(
                    just.iter()
                        .any(|l| matches!(l, EqLeaf::Asserted(a) if *a == lit)),
                    "alias propagation must cite the asserting equation literal"
                );
            }
            _ => panic!("expected Propagate for an alias residual"),
        }
    }

    /// The real e2e path: `"a"·x = "a"·y` strips the shared constant head,
    /// leaving the alias residual.
    #[test]
    fn alias_after_head_strip_propagates() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_hs");
        let y = declare_str_var(&mut ctx, "y_hs");
        let a = ctx.mk_string_const("a");
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx, &mut eq, &[a, x], &[a, y], just, lit, &mut ctr, &mut emitted,
        );
        assert!(
            matches!(r, StepResult::Propagate { var, word, .. } if var == x && word == y),
            "shared head must strip, then the alias residual must propagate"
        );
    }

    /// A single CONCAT atom is NOT a free variable (`is_free_var` excludes it,
    /// the deleted E1 probe's other defect): `[x] = [concat(w, z)]` must NOT
    /// propagate.
    #[test]
    fn single_concat_atom_does_not_propagate() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let x = declare_str_var(&mut ctx, "x_cc");
        let w = declare_str_var(&mut ctx, "w_cc");
        let z = declare_str_var(&mut ctx, "z_cc");
        let concat = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[w, z])
            .unwrap();
        let lit = dummy_eqn_lit();
        let just = vec![EqLeaf::Asserted(lit)];
        let mut ctr = 0u32;
        let mut emitted = FxHashSet::default();
        let r = resolve_equation(
            &mut ctx, &mut eq, &[x], &[concat], just, lit, &mut ctr, &mut emitted,
        );
        assert!(
            !matches!(r, StepResult::Propagate { .. }),
            "an unflattened CONCAT atom must never be treated as a variable"
        );
    }
```

Also rename the slice-33 fence test and narrow its doc (it currently claims
ALL variable-bearing words are fenced; after this slice only multi-atom ones
are). Replace `wordeq.rs:1412-1416` — the doc comment and signature of
`variable_bearing_word_does_not_propagate` — with:

```rust
    /// SCOPE FENCE (slice-34 spec §2): a MULTI-ATOM variable-bearing word must
    /// NOT propagate — `v = w ++ "a"` needs a CONCAT merge target and an
    /// in-word occurs-check; it is the deleted E1 probe's shape and stays
    /// fenced. (The SINGLE-variable alias residual `[v] = [u]` DOES propagate
    /// as of slice 34 — see `alias_residual_propagates`.)
    #[test]
    fn multi_atom_variable_bearing_word_does_not_propagate() {
```

The test body (lines 1417-1436) is unchanged — its `[y] = [w, "a"]` shape is
already multi-atom. Update its trailing assertion message from "slice 33" to:

```rust
        assert!(
            !matches!(r, StepResult::Propagate { .. }),
            "a MULTI-ATOM variable-bearing word must NOT propagate (slice-34 spec §2)"
        );
```

- [ ] **Step 2: Run the new tests to verify they fail correctly**

```bash
cargo nextest run -p shinri-str -E 'test(alias_) + test(single_concat_atom) + test(multi_atom_variable_bearing)'
```

Expected: `alias_residual_propagates` and `alias_after_head_strip_propagates` FAIL (the resolver currently returns a non-`Propagate` outcome for var–var residuals); `single_concat_atom_does_not_propagate` and `multi_atom_variable_bearing_word_does_not_propagate` PASS (they pin behavior that must hold both before and after).

- [ ] **Step 3: Implement the alias case**

In `wordeq.rs`, inside the slice-33 block, insert between the `all_const` closure (ends line 658) and the `let pair = ...` computation (line 660):

```rust
        // SLICE 34: alias case — BOTH residuals are a single free variable.
        // `[v] = [u]` entails `v ≈ u` by cancellation in the free monoid.
        // No occurs-check is needed here, structurally: head/tail stripping
        // removed every same-class pair, so a SURVIVING var–var residual
        // proves the two classes are distinct — the merge is never `v ≈ v`,
        // and a one-atom variable side cannot contain `v` any other way
        // (contrast the fenced multi-atom shape, where `v` can occur inside
        // the word). Left residual is `var`, fixed, for determinism; the EUF
        // merge is symmetric. `word` here is the other VARIABLE's TermId —
        // the driver's merge is a var–var class union and may create a string
        // class with NO constant member (spec §5); the driver and model paths
        // are shape-agnostic.
        if l_res.len() == 1
            && r_res.len() == 1
            && is_free_var(terms, l_res[0])
            && is_free_var(terms, r_res[0])
        {
            return StepResult::Propagate {
                var: l_res[0],
                word: r_res[0],
                just,
            };
        }
```

- [ ] **Step 4: Run the tests to verify they pass, then the full crate**

```bash
cargo nextest run -p shinri-str -E 'test(alias_) + test(single_concat_atom) + test(multi_atom_variable_bearing) + test(pure_assignment)'
cargo nextest run -p shinri-str
```

Expected: first command all pass (the three new + one renamed + three slice-33 `pure_assignment_*` tests — the constant path must be untouched). Second command: full `shinri-str` suite green.

- [ ] **Step 5: Truth up the naming (doc comments only, no behavior)**

Replace the `StepResult::Propagate` doc comment (`wordeq.rs:15-26`, the lines above `Propagate {`) with:

```rust
    /// SLICE 33 (widened in SLICE 34). The equation entails the single-atom
    /// propagation `var ≈ word`. Two residual shapes report it:
    ///
    /// - slice 33: a single variable vs an ALL-CONSTANT word. `word` is a
    ///   SINGLE interned string constant — a multi-atom constant side is
    ///   folded before it is reported, so the caller's merge never depends on
    ///   a CONCAT term's own normal form.
    /// - slice 34: BOTH residuals a single free variable (`[v] = [u]`;
    ///   stripping guarantees the classes are distinct). `word` is the other
    ///   VARIABLE's term; the merge is a var–var class union and may create a
    ///   string class with NO constant member.
    ///
    /// This is NOT the deleted E1 probe (see the comment further down this
    /// file). That probe returned `Done` — it claimed the equation was
    /// RESOLVED and cited nothing. This reports a FACT together with `just`,
    /// its full antecedent set, which the caller merges into EUF under an
    /// `EqJust::Interface` tag. Nothing is emitted and nothing is learnt, so
    /// the E1 branch-locality gate has no clause to reject. The MULTI-ATOM
    /// variable-bearing word stays fenced (slice-34 spec §2).
```

Replace the slice-33 block header comment (`wordeq.rs:625-639`, from `// ── SLICE 33: pure-assignment propagation` through the `is_concat` guard paragraph) with:

```rust
    // ── SLICE 33/34: single-atom propagation ─────────────────────────────────
    // SLICE 33: a residual `[v] = [constant word]` ENTAILS `v ≈ W` (multi-atom
    // constant sides folded to one interned term). SLICE 34: a residual
    // `[v] = [u]` (free variable each side) ENTAILS `v ≈ u` by cancellation.
    // Before these, both shapes fell through to the variable-headed F-split
    // below, hit the dedup, and returned `Saturated` → a sound but needless
    // `Unknown`. Reporting the fact here, BEFORE the F-split, is the whole fix.
    //
    // Scope (slice-34 spec §2): the MULTI-ATOM variable-bearing word stays
    // fenced — it is the deleted E1 probe's shape (needs a CONCAT merge target
    // and an in-word occurs-check) and is deliberately out of scope.
    //
    // The `is_concat` guard fixes the probe's other defect: it tested
    // `string_const_value(..).is_none()`, which matches an unflattened CONCAT
    // rep as if it were a free variable. The wrapper flattens, but we do not
    // rely on that here — an atom that is still a CONCAT is never treated as a
    // variable.
```

Then check the driver-side wording still holds: read `lib.rs:780-788` and
`lib.rs:890-935`. Both speak of "a ground FACT" and cite spec §4 — they are
shape-agnostic and stay as-is. Do not edit `lib.rs` unless a comment there
claims `word` is always a constant; none did at plan time.

- [ ] **Step 6: Run the crate suite once more, then commit**

```bash
cargo nextest run -p shinri-str
cargo fmt --all
git add crates/shinri-str/src/wordeq.rs
git commit -m "feat(str): slice34 — alias residual propagation (var–var single-atom merge)"
```

Expected: suite green, then a clean commit.

---

### Task 3: Re-measure, flip pins, oracle cases

**Files:**
- Modify: `crates/shinri-solver/tests/slice34_probes.rs` (flip A1/A2/A4 pins)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (append 3 oracle cases after the slice-33 section, ~line 2957)

**Interfaces:**
- Consumes: `expect(src, Verdict)` helper (`qfs_differential.rs:2668`) — runs shinri AND cross-checks z3 on every non-Unknown expectation; `Verdict::Unsat`.
- Produces: oracle test names `targeted_probe_a1_prefix_alias_unsat`, `targeted_probe_a2_suffix_alias_unsat`, `targeted_probe_a4_chain_unsat`.

- [ ] **Step 1: Re-measure the probes on the new tip**

```bash
cargo nextest run -p shinri-solver -E 'binary(slice34_probes)' --no-fail-fast
```

Expected: A1, A2, A4 FAIL (their baseline `unknown` assertions now see `unsat` — the predicted flips); A3 and B1 PASS unchanged. Record the actual verdict of every probe.

Contingencies (spec's adjudication rules, not blockers-by-default):
- A probe predicted to flip that stays `unknown`: record it, keep the pin at `unknown` with a comment saying the §7 prediction was falsified, and report it in the Task 4 truth-up. Do NOT force the predicted verdict.
- **B1 flips**: first re-run the Task 2 fence tests. If `multi_atom_variable_bearing_word_does_not_propagate` or `single_concat_atom_does_not_propagate` fails, the fence broke — BLOCKER, fix before proceeding. If both pass, the flip came from composition with other machinery (the slice-33 probe-C precedent): confirm with z3, adjudicate, and record the mechanism in the truth-up.
- Any `sat ↔ unsat` or `decided → unknown` movement anywhere: BLOCKER.

- [ ] **Step 2: Confirm every flip against z3 before writing pins**

For each probe that flipped (expected: A1, A2, A4), write its script to the scratchpad and run z3. Example for A1 (repeat for each flip, editing the assertions to match the probe):

```bash
cat > /tmp/claude-1000/-workspace/aec3c7c5-f94f-4432-8a86-97a36e1fff51/scratchpad/flip_a1.smt2 <<'EOF'
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ "a" x) (str.++ "a" y)))
(assert (distinct x y))
(check-sat)
EOF
z3 /tmp/claude-1000/-workspace/aec3c7c5-f94f-4432-8a86-97a36e1fff51/scratchpad/flip_a1.smt2
```

Expected: `unsat` for A1/A2/A4 (already measured at brainstorm time; this re-confirms on the record). A shinri-`unsat` that z3 calls `sat` is a soundness bug — BLOCKER, stop and debug with superpowers:systematic-debugging.

- [ ] **Step 3: Flip the pins in `slice34_probes.rs`**

For A1, replace the assertion and doc comment:

```rust
/// Probe A1 — PIN (slice 34). `"a"·x = "a"·y` strips the shared head to the
/// alias residual `[x] = [y]`, which now propagates `x ≈ y` (spec §3) and
/// collides with the asserted `distinct`. Measured `unknown → unsat` at
/// Task 3; z3 confirms unsat.
#[test]
fn probe_a1_prefix_alias() {
    let out = run_script(
        r#"(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)
           (assert (= (str.++ "a" x) (str.++ "a" y)))
           (assert (distinct x y))(check-sat)"#,
    );
    assert_eq!(out, vec!["unsat"]);
}
```

For A2, same edit shape (doc: "Suffix twin of A1: tail-stripping produces the same alias residual; same propagation path." — assertion flips to `vec!["unsat"]`).

For A4, same edit shape (doc: "Chained aliasing: `x ≈ y` and `y ≈ z` compose in EUF; `distinct x z` conflicts. Each propagation eagerly re-inserts its own post-merge root into cond_roots (slice-33 §11.6). Measured `unknown → unsat`; z3 confirms." — assertion flips to `vec!["unsat"]`).

A3 and B1 stay exactly as written in Task 1. Update the file-level doc comment's second paragraph to past tense:

```rust
//! Task 3 re-measured after the mechanism landed: A1/A2/A4 flipped
//! `unknown → unsat` (each z3-confirmed before the pin was written); A3 held
//! `sat`; B1 held `unknown` (the fence held).
```

- [ ] **Step 4: Run the probe file — all five green**

```bash
cargo nextest run -p shinri-solver -E 'binary(slice34_probes)'
```

Expected: `5 tests run: 5 passed`.

- [ ] **Step 5: Add the oracle cases**

Append to `crates/shinri-solver/tests/qfs_differential.rs` after the slice-33 targeted-probe section (after `targeted_probe_c_len_zero_var_unsat`, ~line 2957):

```rust
// ── Slice 34: alias-propagation probes — oracle-confirmed pins ───────────────
// The resolver now propagates the alias residual `[v] = [u]` (slice-34 spec
// §3): a var–var EUF merge with cited antecedents instead of a sound
// `Unknown`. These probes measured `unknown → unsat` at Task 3; `expect`
// cross-checks z3 on every call, so a shinri/z3 disagreement is a hard fail.

#[test]
fn targeted_probe_a1_prefix_alias_unsat() {
    // Probe A1 (spec §7). `"a"·x = "a"·y` strips the shared head to the alias
    // residual `[x] = [y]`, which propagates `x ≈ y` against `distinct x y`.
    expect(
        "(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)\
         (assert (= (str.++ \"a\" x) (str.++ \"a\" y)))\
         (assert (distinct x y))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_probe_a2_suffix_alias_unsat() {
    // Probe A2 (spec §7). Suffix twin: tail-stripping, same propagation path.
    expect(
        "(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)\
         (assert (= (str.++ x \"a\") (str.++ y \"a\")))\
         (assert (distinct x y))(check-sat)",
        Verdict::Unsat,
    );
}

#[test]
fn targeted_probe_a4_chain_unsat() {
    // Probe A4 (spec §7). Chained alias merges `x ≈ y`, `y ≈ z` compose in
    // EUF; `distinct x z` conflicts. Exercises per-merge eager cond_roots
    // re-insertion (slice-33 §11.6) on chained propagations.
    expect(
        "(set-logic QF_S)(declare-fun x () String)(declare-fun y () String)\
         (declare-fun z () String)\
         (assert (= (str.++ \"a\" x) (str.++ \"a\" y)))\
         (assert (= (str.++ \"b\" y) (str.++ \"b\" z)))\
         (assert (distinct x z))(check-sat)",
        Verdict::Unsat,
    );
}
```

If a probe did not actually flip in Step 1, do NOT add its oracle case — an `expect(..., Verdict::Unsat)` for an `unknown` verdict fails. Only measured flips get oracle pins.

- [ ] **Step 6: Run the new oracle cases plus the slice-33 controls**

```bash
cargo nextest run -p shinri-solver --features oracle -E 'test(targeted_probe_)'
```

Expected: non-zero count — 3 slice-33 cases + up to 3 new = up to 6 run, all pass. The slice-33 controls (`targeted_probe_e/g/c`) must be unchanged.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/slice34_probes.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(str): slice34 — oracle-confirmed pins (A1/A2/A4 unknown→unsat), fence held"
```

---

### Task 4: Dump-and-diff, full gates, truth-up, PR

**Files:**
- Modify (TEMPORARY, reverted in-task): `crates/shinri-solver/tests/qfs_differential.rs` (DIFFDUMP instrumentation)
- Modify: `docs/superpowers/specs/2026-07-20-shinri-slice34-alias-propagation-design.md` (append `## 11. Outcome`)

**Interfaces:**
- Consumes: everything landed in Tasks 1–3; the spec's §7 table.
- Produces: the merged PR.

- [ ] **Step 1: Add the temporary per-iteration dump (NOT committed)**

All fuzz families funnel through two helpers in `qfs_differential.rs`: `shinri_lines` (~line 56) and `shinri_lines_counting_bailouts` (~line 96). In EACH, immediately before the final return, insert:

```rust
    // TEMP DIFFDUMP (slice 34 dump-and-diff — do not commit)
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

- [ ] **Step 2: Dump the fix side**

```bash
SHINRI_DIFFDUMP=1 cargo test -p shinri-solver --test qfs_differential --features oracle -- --test-threads=1 2> /tmp/claude-1000/-workspace/aec3c7c5-f94f-4432-8a86-97a36e1fff51/scratchpad/dump-fix.txt
grep -c DIFFDUMP /tmp/claude-1000/-workspace/aec3c7c5-f94f-4432-8a86-97a36e1fff51/scratchpad/dump-fix.txt
```

Expected: 0 test failures, and **thousands** of DIFFDUMP lines (13 fuzz families × 200 iterations, plus targeted tests). A line count near 0 means the harness swallowed stderr — the run is NOT a valid dump; re-check the `2>` redirection and `--test-threads=1` before trusting anything.

- [ ] **Step 3: Dump the base side from a worktree at the branch point**

```bash
git worktree add /tmp/claude-1000/-workspace/aec3c7c5-f94f-4432-8a86-97a36e1fff51/scratchpad/base-wt 17ef967e
```

Apply the SAME Step-1 instrumentation to `base-wt/crates/shinri-solver/tests/qfs_differential.rs` (same two helpers, same code), then:

```bash
cd /tmp/claude-1000/-workspace/aec3c7c5-f94f-4432-8a86-97a36e1fff51/scratchpad/base-wt
SHINRI_DIFFDUMP=1 cargo test -p shinri-solver --test qfs_differential --features oracle -- --test-threads=1 2> ../dump-base.txt
grep -c DIFFDUMP ../dump-base.txt
cd /workspace
```

Expected: comparable line count to the fix side (the fix side has up to 3 extra lines from the new targeted cases).

- [ ] **Step 4: Diff and check the invariant**

```bash
cd /tmp/claude-1000/-workspace/aec3c7c5-f94f-4432-8a86-97a36e1fff51/scratchpad
grep DIFFDUMP dump-base.txt | sort > base-sorted.txt
grep DIFFDUMP dump-fix.txt  | sort > fix-sorted.txt
diff base-sorted.txt fix-sorted.txt | head -80
cd /workspace
```

The invariant (spec §8): every hash-keyed verdict flip is `unknown → {sat, unsat}`; **zero** `decided → unknown`; **zero** `sat ↔ unsat`; **zero** bailout increases on unchanged hashes. Lines present only on the fix side with no base counterpart are the new targeted cases — expected. Record the flip tally for the truth-up. Any reverse flip or sat/unsat swap: BLOCKER.

- [ ] **Step 5: Revert the instrumentation and remove the worktree**

```bash
git checkout -- crates/shinri-solver/tests/qfs_differential.rs
git worktree remove --force /tmp/claude-1000/-workspace/aec3c7c5-f94f-4432-8a86-97a36e1fff51/scratchpad/base-wt
git status
```

WAIT: `git checkout --` would also revert the Task-3 oracle cases if Step 1's instrumentation was added to the same uncommitted file. It was NOT — Task 3 committed before Task 4 began, so the only uncommitted change in that file is the instrumentation. Confirm with `git status` + `git diff --stat` BEFORE the checkout; expected: exactly one modified file, `qfs_differential.rs`, whose diff is only the two DIFFDUMP blocks.

- [ ] **Step 6: Run the completeness-shifting gate**

```bash
cargo nextest run -p shinri-solver -E 'test(script_e2e)'
```

Expected: all pass. A z3-confirmed `unknown → decided` pin flip here is an adjudicated flip, not a blocker — confirm with the oracle, update the pin with a comment explaining the flip. `decided → unknown` or any `sat`/`unsat` disagreement IS a blocker.

- [ ] **Step 7: Full gate**

```bash
cargo fmt --all -- --check
cargo clippy --workspace --all-targets -- -D warnings
cargo nextest run --workspace
cargo nextest run -p shinri-solver --features oracle
```

Expected: all clean. For the oracle run, **confirm a non-zero test count** (~489: the 486 at slice-33 close plus the new targeted cases).

- [ ] **Step 8: Truth up the spec**

Append a `## 11. Outcome` section to `docs/superpowers/specs/2026-07-20-shinri-slice34-alias-propagation-design.md` recording:
- The measured verdict of every probe (A1–A4, B1), before and after, from the Task 1 and Task 3 runs — the **actual** values, not the predicted ones.
- Whether §7's predictions held; if any did not, say so plainly and explain the real behavior.
- The z3 confirmation for each flipped pin, and the dump-and-diff tally (flip counts and directions) from Step 4.
- Whether the fence held (B1 + the two unit fence tests).
- What remains open: the multi-atom variable-bearing shape (banked with B1's measurement), and the standing bank unchanged.

Report what happened. Do not describe a prediction as a result.

- [ ] **Step 9: Commit and open the PR**

```bash
cargo fmt --all
git add docs/superpowers/specs/2026-07-20-shinri-slice34-alias-propagation-design.md
git commit -m "docs: slice34 truth-up — measured outcomes + dump-and-diff tally"
git push -u origin slice34-alias-propagation
gh pr create --base main --title "slice34: alias propagation (var–var residual merge)" --body "$(cat <<'EOF'
Widens the slice-33 propagation outcome by one step (spec §2/§3): a word-
equation residual `[v] = [u]` — one free variable per side — now propagates
`v ≈ u` into EUF with cited antecedents instead of falling through to an
F-split dedup hit and a sound `Unknown`.

- One new detection case in `resolve_inner`; the driver, prop-tag citation,
  `explain`, cond_roots tracking (T5b + §11.6), and conflict assembly are
  reused verbatim — all shape-agnostic.
- No occurs-check needed, structurally: stripping guarantees a surviving
  var–var residual is a distinct-class pair.
- New soundness fact pinned: var–var merges create constant-free string
  classes; the SAT control (probe A3) holds.
- Scope fence held: the MULTI-ATOM variable-bearing shape (the deleted E1
  probe's failure mode) stays fenced — pinned at unit tier and e2e (probe B1),
  and banked WITH its measurement.

See the spec's Outcome section for measured verdicts, oracle confirmations,
and the dump-and-diff tally.
EOF
)"
```

Merge with a merge commit when CI is green, then delete the branch remote and local (`git push origin --delete slice34-alias-propagation && git branch -d slice34-alias-propagation && git remote prune origin`).

---

## Self-Review

**Spec coverage.** §1 problem (measured gap) → T1 baseline + T3 flips. §2 in-scope alias shape → T2 Step 3; §2 out-of-scope multi-atom → T2 fence tests + T1/T3 probe B1 + T3 Step-1 B1 contingency. §3 mechanism incl. no-occurs-check argument → T2 Step 3 comment (verbatim from spec). §3 naming truth-up → T2 Step 5. §4 citation (inherited) → no new code, exercised by T3 probes; the `just`-citation assert in `alias_residual_propagates` pins the resolver side. §5 constant-free class fact → probe A3 (T1 + T3 Step 1). §6 conflict path → probes A1/A2 drive the merge-`Err` arm e2e. §7 acceptance table → T1 (before) + T3 Steps 1–4 (after, z3-confirmed). §8 testing: unit → T2; e2e pins → T1/T3; oracle cases → T3 Step 5; dump-and-diff → T4 Steps 1–5; full gates + script_e2e → T4 Steps 6–7. §9 chained-alias risk → probe A4 + oracle case; fence-regression risk → renamed unit test + B1; drift risk → T4 dump-and-diff. §10 banking → T4 Step 8 truth-up. No gaps.

**Placeholder scan.** No TBDs. Every code step shows complete code; every run step gives an exact command and expected outcome, including failure-mode instructions (baseline mismatch in T1 Step 2, non-flip and B1-flip contingencies in T3 Step 1, swallowed-stderr check in T4 Step 2, revert-safety check in T4 Step 5).

**Type consistency.** `StepResult::Propagate { var, word, just }` field names match `wordeq.rs:27-31` (read at plan time); test helpers `declare_str_var`/`dummy_eqn_lit` exist at `wordeq.rs:851`/`838`; `expect(src, Verdict)` matches `qfs_differential.rs:2668`; probe test names are consistent between T1, T3, and the truth-up instructions.
