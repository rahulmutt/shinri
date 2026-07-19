# Slice 31b — Base-case decision-phase preference (unblock the acceptance gates) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add an optional per-atom preferred decision phase to the theory→SAT
split channel, and have the order engine mark `a_eps = (= A "")` and
`clt = (< code(hA) code(hB))` preferred-TRUE, so the head-peel SAT search tries
the base case / code-compare disjuncts instead of unit-propagating the
`r_tail` recursion — making slice 31's bare/bounded acceptance pins decide.

**Architecture:** A new optional `phases: Vec<Option<bool>>` field on the
`Split` payload flows `TCheck::Split` (theory) → `FinalCheck::Split`
(combiner-private) → `TheoryResult::SplitAtoms` (sat). At the single SplitAtoms
consume site the SAT solver seeds `Assignment::phase` for each **freshly
minted** atom var whose preference is `Some(_)`. Phase preference only reorders
search — it is unconditionally sound. The order engine is the first (only)
client.

**Tech Stack:** Rust workspace `shinri`; crates `shinri-sat` (DPLL core),
`shinri-theory` (Combiner), `shinri-str` (string theory). Tests via
`cargo nextest`; oracle via `mise`.

**Spec:** `docs/superpowers/specs/2026-07-19-shinri-slice31-str-order-symbolic-pair-design.md`
§10 (the addendum — read it; it carries the root-cause + soundness argument).

**Predecessor state:** slice31 Tasks 1–6 are landed and reviewed sound on branch
`slice31-str-order-symbolic-pair` (HEAD `ff6a3109`; the code bridge, clause
families, congruence, folding). Task 7 (fence-lift + gates) was BLOCKED on the
integration gap this plan fixes.

**Continuation:** After this plan's Task 3, execution continues with the
ORIGINAL plan's Tasks 8, 9, 10
(`docs/superpowers/plans/2026-07-19-shinri-slice31-str-order-symbolic-pair.md`)
— e2e differential pins, the `qfs_str_order_symbolic_pair_matches_z3` oracle
family, and the fuel/tier/full-gate/truth-up/PR task — unchanged, except Task
10's truth-up now also documents the phase-preference capability and its oracle
timing.

## Global Constraints

- **Pure-Rust mandate:** no native-link deps (`deny.toml` bans `rug`,
  `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`). This plan adds none.
- **Soundness is absolute.** A decision-phase preference MUST only reorder the
  search — never change which assignments are legal, never a learnt clause,
  never a verdict. The seed is applied ONLY to a freshly-minted variable's
  saved phase (`Assignment::phase`), which `pick_branch` reads; it changes the
  *first* decision direction and nothing else. Existing behaviour (default
  phase FALSE + phase-saving) MUST be identical when no preference is supplied
  (empty `phases`).
- **`phases` invariant:** on any `Split`/`SplitAtoms`, `phases` is EITHER
  empty (no preferences) OR exactly `atoms.len()` long. Every no-preference
  construction site passes `Vec::new()`.
- **Hygiene before push:** `cargo fmt --all`; `cargo clippy --workspace
  --all-targets -- -D warnings` clean (`mise run lint`).
- **Oracle tests are feature-gated:** `cargo nextest run -p shinri-solver
  --features oracle`; without the flag they run 0 tests.
- **Nextest filter:** `-E 'test(<name>)'`, not positional `mod::name`; confirm
  discovery with `cargo nextest list -E 'test(<name>)'` before trusting green.
- **Acceptance bar (plan Risk):** the 5 solver pins in Task 3 — especially the
  congruence gate `lt_and_lt_swapped_bounded_len_is_unsat` and folding gate
  `lt_with_constant_pins_is_unsat_via_folding` — MUST decide (Sat/Unsat), not
  `Unknown`. If still `Unknown` after the hint, it is a length-coupling defect
  to diagnose (systematic-debugging), NOT a reason to weaken a gate or blindly
  bump fuel.

---

### Task 1: Phase-preference capability (shinri-sat + shinri-theory)

**Files:**
- Modify: `crates/shinri-sat/src/assignment.rs` (add `set_phase`)
- Modify: `crates/shinri-sat/src/types.rs` (add `phases` to `TheoryResult::SplitAtoms`, ~lines 56-68)
- Modify: `crates/shinri-sat/src/solver.rs` (apply per-atom phase in the SplitAtoms mint loop, ~lines 704-734)
- Modify: `crates/shinri-theory/src/solver_trait.rs` (add `phases` to `TCheck::Split`, ~lines 31-34; the in-file test at ~205)
- Modify: `crates/shinri-theory/src/combiner.rs` (`FinalCheck::Split` ~21-24; the TCheck→FinalCheck arms ~527/536/543; the FinalCheck→TheoryResult lift ~302)
- Modify (mechanical, add `phases: Vec::new()` to each `TCheck::Split { .. }` construction / `..` to each destructure):
  `crates/shinri-str/src/memb.rs` (construct ~89, destructure ~620),
  `crates/shinri-str/src/lib.rs` (construct ~453, 497, 649, 776, 1059; destructure ~1564),
  `crates/shinri-str/src/order_engine.rs` (construct ~327, 481; destructure test ~742),
  `crates/shinri-str/src/wordeq.rs` (destructure ~938, 990),
  `crates/shinri-theory/tests/splitting_on_demand.rs` (~88).
  (`length.rs:314/373`, `memb.rs:1179`, `wordeq.rs:1088/1452`, `lib.rs:1509/1626`, `combiner.rs:521` already use `{ .. }` and are safe.)
- Test: `crates/shinri-sat/src/assignment.rs` (unit: `set_phase`), and a SplitAtoms-seeding test (in `crates/shinri-sat/src/solver.rs` tests or `crates/shinri-theory/tests/splitting_on_demand.rs`).

**Interfaces:**
- Consumes: nothing new.
- Produces:
  - `Assignment::set_phase(&mut self, v: Var, p: bool)` — sets the saved phase of `v` without assigning it.
  - `TCheck::Split { atoms: Vec<TermId>, guard: Option<Lit>, phases: Vec<Option<bool>> }` (theory).
  - `FinalCheck::Split { atoms, guard, phases }` (combiner-private).
  - `TheoryResult::SplitAtoms { atoms, guard, phases }` (sat).
  - Solver behaviour: on a SplitAtoms with non-empty `phases`, each atom that mints a FRESH var and whose `phases[i] == Some(p)` has its saved phase seeded to `p`.

- [ ] **Step 1: Write the failing test for `set_phase`**

In `crates/shinri-sat/src/assignment.rs` tests module (find `#[cfg(test)] mod tests` / the existing phase test near line 123):

```rust
#[test]
fn set_phase_overrides_default_without_assigning() {
    let mut a = Assignment::default();
    let v = a.new_var();
    assert_eq!(a.phase(v), false); // default
    a.set_phase(v, true);
    assert_eq!(a.phase(v), true);
    // set_phase must NOT assign the variable (value stays Unset).
    assert_eq!(a.value(v), LBool::Unset);
}
```

(If `value(v)`/`LBool` accessor names differ, match the existing tests in this file — use whatever the neighbouring phase-saving test uses to read assignment state.)

- [ ] **Step 2: Run to verify it fails**

Run: `cargo nextest run -p shinri-sat -E 'test(set_phase_overrides_default_without_assigning)'`
Expected: FAIL (`set_phase` does not exist).

- [ ] **Step 3: Add `set_phase`**

In `crates/shinri-sat/src/assignment.rs`, next to the `phase` accessor (~lines 69-72):

```rust
/// Set the saved decision phase of `v` WITHOUT assigning it. Used to seed a
/// theory-preferred first-decision direction for a freshly minted split atom.
/// Sound: only affects which branch `pick_branch` tries first, never legality.
pub fn set_phase(&mut self, v: Var, p: bool) {
    self.phase[v.index()] = p;
}
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo nextest run -p shinri-sat -E 'test(set_phase_overrides_default_without_assigning)'`
Expected: PASS.

- [ ] **Step 5: Add `phases` to `TheoryResult::SplitAtoms`**

In `crates/shinri-sat/src/types.rs` (~56-68), extend the variant:

```rust
    SplitAtoms {
        atoms: Vec<TermId>,
        guard: Option<Lit>,
        /// Optional per-atom preferred decision phase. Empty = no preference.
        /// Otherwise `phases.len() == atoms.len()`; `Some(p)` seeds that atom's
        /// var phase to `p` when the var is freshly minted.
        phases: Vec<Option<bool>>,
    },
```

- [ ] **Step 6: Apply the phase seed in the SplitAtoms mint loop**

In `crates/shinri-sat/src/solver.rs`, the SplitAtoms arm (~694). Replace the
`for atom in atoms { ... }` mint/reuse loop (~704-734) so it indexes `phases`
and seeds ONLY freshly minted vars:

```rust
TheoryResult::SplitAtoms { atoms, guard, phases } => {
    let mut lits: Vec<Lit> = Vec::with_capacity(atoms.len() + 1);
    if let Some(g) = guard {
        lits.push(g);
    }
    for (i, atom) in atoms.iter().copied().enumerate() {
        let v = match self.theory.var_for_atom(atom) {
            Some(existing) => existing,
            None => {
                let v = self.new_var();
                self.theory.bind_fresh(v, atom);
                // Seed the theory-preferred first-decision phase (only on a
                // freshly minted var; a reused var keeps its saved phase).
                if let Some(Some(p)) = phases.get(i) {
                    self.assign.set_phase(v, *p);
                }
                v
            }
        };
        lits.push(Lit::new(v, true));
    }
    // ... rest of the arm unchanged (install_clause for len==1, add_learnt otherwise)
}
```

(Keep the remainder of the arm — the `lits.len() == 1` level-0 `install_clause`
path and the `add_learnt` path — exactly as it was. Only the loop and the
destructure changed. `phases.get(i)` returns `None` when `phases` is empty, so
empty = no seeding = unchanged behaviour.)

- [ ] **Step 7: Add `phases` to `TCheck::Split` and thread through the combiner**

In `crates/shinri-theory/src/solver_trait.rs` (~31-34):

```rust
    Split {
        atoms: Vec<TermId>,
        guard: Option<Lit>,
        /// Optional per-atom preferred decision phase (empty = none).
        phases: Vec<Option<bool>>,
    },
```

Fix the in-file test/doc constructor at ~205 to add `phases: Vec::new()`.

In `crates/shinri-theory/src/combiner.rs`, `FinalCheck::Split` (~21-24) gains
the same `phases: Vec<Option<bool>>` field. Thread it in the TCheck→FinalCheck
arms (~527, 536, 543 — wherever `TCheck::Split { atoms, guard }` is matched and
rebuilt as `FinalCheck::Split`, carry `phases`), and in the FinalCheck→
TheoryResult lift (~302):

```rust
FinalCheck::Split { atoms, guard, phases } => TheoryResult::SplitAtoms { atoms, guard, phases },
```

- [ ] **Step 8: Update every remaining `TCheck::Split` construction / destructure site**

Add `phases: Vec::new()` to each construction and `..` to each exhaustive
destructure that lacks it (list in **Files** above). After this step the
workspace must COMPILE. Run:

Run: `cargo build --workspace`
Expected: builds clean (no missing-field / non-exhaustive-pattern errors).

- [ ] **Step 9: Write and run the SplitAtoms-seeding test**

Add to `crates/shinri-theory/tests/splitting_on_demand.rs` (or the sat solver
tests) a test that a SplitAtoms carrying `phases = [Some(true), None]` seeds the
first atom's fresh var to phase TRUE while the second keeps default FALSE, and
that empty `phases` leaves both FALSE. Mirror the existing splitting_on_demand
harness (it already drives a theory that emits splits). Assert via the solver's
observable first-decision direction on those vars, or expose the seeded phase
through the existing test theory. If the existing harness cannot observe phase
directly, assert the end-to-end effect: a tiny theory that emits
`Split{ atoms:[p,q], phases:[Some(true),None] }` under a guard causes the solver
to try `p=true` first (observable via the model / decision trace the harness
exposes).

Run: `cargo nextest run -p shinri-theory -E 'test(<your test name>)' --no-capture`
Expected: PASS, >0 tests.

- [ ] **Step 10: Full suites green**

Run: `cargo nextest run -p shinri-sat` and `cargo nextest run -p shinri-theory` and `cargo nextest run -p shinri-str`
Expected: all green (the new field defaults empty everywhere; behaviour unchanged for all existing splits).

Run: `cargo fmt --all` then `cargo clippy --workspace --all-targets -- -D warnings`
Expected: clean.

- [ ] **Step 11: Commit**

```bash
git add crates/shinri-sat/src/assignment.rs crates/shinri-sat/src/types.rs crates/shinri-sat/src/solver.rs crates/shinri-theory/src/solver_trait.rs crates/shinri-theory/src/combiner.rs crates/shinri-theory/tests/splitting_on_demand.rs crates/shinri-str/src/memb.rs crates/shinri-str/src/lib.rs crates/shinri-str/src/order_engine.rs crates/shinri-str/src/wordeq.rs
git commit -m "feat(sat): slice31 — optional per-atom preferred decision phase on Split payload"
```

---

### Task 2: Order engine tags `a_eps` and `clt` preferred-TRUE

**Files:**
- Modify: `crates/shinri-str/src/order_engine.rs` (`OrderFamily` struct; `build_order_family`; the inline `TCheck::Split` emit at ~327)
- Test: `crates/shinri-str/src/order_engine.rs` (tests module)

**Interfaces:**
- Consumes: Task 1's `TCheck::Split { .., phases }`.
- Produces: the order family's emitted split for any clause carries
  `phases[i] = Some(true)` for atoms equal to the family's `a_eps` or `clt`
  handle, `None` otherwise.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn cmp_clause_emits_prefer_true_phases_for_a_eps_and_clt() {
    // build_order_family for (str.< s u); inspect the family so a CMP clause
    // ([a_eps, clt, tail]) yields phases [Some(true), Some(true), None] at emit.
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let u = str_var(&mut ctx, "u");
    let mut ctr = 0u32;
    let fam = build_order_family(&mut ctx, s, u, true, &mut ctr);
    // Find the CMP2 clause: 3 atoms [a_eps, clt, r_tail] where r_tail is str.<.
    let cmp = fam
        .clauses
        .iter()
        .find(|c| c.len() == 3 && is_strlt_app(&ctx, c[2]))
        .expect("CMP2 clause present");
    let phases = fam.phases_for(cmp); // the positional phase helper (Step 3)
    assert_eq!(phases, vec![Some(true), Some(true), None]);
}
```

(Reuse `str_var` / `is_strlt_app` helpers already in this test module from Task 4/5.)

- [ ] **Step 2: Run to verify it fails**

Run: `cargo nextest run -p shinri-str -E 'test(cmp_clause_emits_prefer_true_phases_for_a_eps_and_clt)'`
Expected: FAIL (`phases_for` / stored `a_eps`/`clt` do not exist).

- [ ] **Step 3: Store `a_eps` and `clt` on `OrderFamily` and add a positional phase helper**

In `crates/shinri-str/src/order_engine.rs`, extend `OrderFamily` (it already
holds `clauses`, `code_ha`, `code_hb`) with the two handles minted in
`build_order_family` (`a_eps` at ~line 112, `clt` at ~line 196):

```rust
pub(crate) struct OrderFamily {
    pub(crate) clauses: Vec<Vec<TermId>>,
    pub(crate) code_ha: TermId,
    pub(crate) code_hb: TermId,
    /// `(= A "")` base-case atom and `(< code(hA) code(hB))` compare atom —
    /// tagged preferred-TRUE at emit so the SAT search tries the base /
    /// code-compare disjuncts before the recursion tail (spec §10).
    pub(crate) a_eps: TermId,
    pub(crate) clt: TermId,
}

impl OrderFamily {
    /// Per-atom preferred phase for a clause: Some(true) for the base-case and
    /// code-compare atoms, None otherwise. Empty-or-len==clause.len() invariant.
    pub(crate) fn phases_for(&self, clause: &[TermId]) -> Vec<Option<bool>> {
        clause
            .iter()
            .map(|&t| {
                if t == self.a_eps || t == self.clt {
                    Some(true)
                } else {
                    None
                }
            })
            .collect()
    }
}
```

Set `a_eps` and `clt` in the `OrderFamily { .. }` constructor at the end of
`build_order_family` (the locals already exist).

- [ ] **Step 4: Run to verify it passes**

Run: `cargo nextest run -p shinri-str -E 'test(cmp_clause_emits_prefer_true_phases_for_a_eps_and_clt)'`
Expected: PASS.

- [ ] **Step 5: Wire `phases_for` into the emit site**

In `order_check`, the inline `TCheck::Split` emit (~327) currently:

```rust
return Some(TCheck::Split {
    atoms: clause.clone(),
    guard: Some(lit.negate()),
});
```

becomes:

```rust
let phases = fam.phases_for(&clause);
return Some(TCheck::Split {
    atoms: clause.clone(),
    guard: Some(lit.negate()),
    phases,
});
```

(`fam` is the memoized `OrderFamily` for this atom — use the same binding the
emit loop already holds. The code-fold companion emit at ~481 keeps
`phases: Vec::new()` — folding companions need no phase preference.)

- [ ] **Step 6: Full string suite green**

Run: `cargo nextest run -p shinri-str`
Expected: all green (still no symbolic pair routed until Task 3; this only
populates the phases vec, inert until the emitted splits actually reach the SAT
loop end-to-end).

Run: `cargo fmt --all` then `cargo clippy -p shinri-str --all-targets -- -D warnings`
Expected: clean.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-str/src/order_engine.rs
git commit -m "feat(str): slice31 — order engine tags a_eps and clt preferred-TRUE"
```

---

### Task 3: Narrow the fence + the 5-pin acceptance gate (the revised original Task 7)

**Files:**
- Modify: `crates/shinri-str/src/order.rs` (`has_unreduced_str_order` walk predicate ~230-238; replace `symbolic_pair_survives_to_fence` ~309)
- Modify: `crates/shinri-solver/tests/script_e2e.rs` (un-ignore the folding test; add the 4 new solver pins)

**Interfaces:**
- Consumes: Tasks 1-2 (phase-preferenced order splits); the whole slice31 engine.
- Produces: a two-symbolic-operand order atom no longer fences (routes to the
  online engine, which now DECIDES the bare/bounded idioms); a constant-operand
  order atom still fences.

- [ ] **Step 1: Write the failing fence-narrow unit tests**

In `crates/shinri-str/src/order.rs` tests, replace `symbolic_pair_survives_to_fence` with:

```rust
#[test]
fn symbolic_pair_no_longer_fenced() {
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let u = str_var(&mut ctx, "u");
    let lt = order(&mut ctx, BuiltinOp::StrLt, s, u);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    assert_eq!(out, vec![lt]);                     // still survives the rewrite
    assert!(!has_unreduced_str_order(&ctx, &out)); // but is NOT fenced now
}

#[test]
fn over_cap_constant_order_still_fences() {
    let mut ctx = Context::new();
    let s = str_var(&mut ctx, "s");
    let big = ctx.mk_string_const(&"a".repeat(257)); // > ORDER_CONST_LEN_CAP (256)
    let lt = order(&mut ctx, BuiltinOp::StrLt, s, big);
    let out = rewrite_str_order(&mut ctx, &[lt]);
    assert!(has_unreduced_str_order(&ctx, &out));
}
```

(If another existing order.rs test — e.g. one that buries a *symbolic pair*
inside `(not …)` and asserts fencing — now contradicts the narrowed fence,
rework it to bury a *constant-operand* atom, e.g. `str.< s "\u{30001}"` above
the alphabet, so it still fences and still exercises `walk`'s recursion. Report
any such rework.)

- [ ] **Step 2: Run to verify they fail**

Run: `cargo nextest run -p shinri-str -E 'test(symbolic_pair_no_longer_fenced) + test(over_cap_constant_order_still_fences)'`
Expected: `symbolic_pair_no_longer_fenced` FAILS (current fence fires on any order atom).

- [ ] **Step 3: Narrow the fence**

In `crates/shinri-str/src/order.rs`, replace the `walk` predicate (~230-238) so
an order-op node fences ONLY when an operand is a string constant:

```rust
fn walk(ctx: &Context, t: TermId) -> bool {
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            let kids = ctx.children(*args).to_vec();
            let is_order = matches!(op, Op::Builtin(BuiltinOp::StrLt | BuiltinOp::StrLeq));
            // Fence only the leftovers with a constant operand (over-cap /
            // above-alphabet words try_order_atom rejected). A pure symbolic
            // pair is now handled by the online engine.
            let fences = is_order
                && kids.iter().any(|&c| ctx.string_const_value(c).is_some());
            fences || kids.iter().any(|&c| walk(ctx, c))
        }
        TermNode::Const { .. } => false,
    }
}
```

(Preserve the actual current `walk` shape — nested fn vs closure — and its
signature.)

- [ ] **Step 4: Run to verify they pass**

Run: `cargo nextest run -p shinri-str -E 'test(symbolic_pair_no_longer_fenced) + test(over_cap_constant_order_still_fences)'`
Expected: PASS. Then `cargo nextest run -p shinri-str` → all green.

- [ ] **Step 5: Un-ignore the folding gate and add the four solver pins**

In `crates/shinri-solver/tests/script_e2e.rs`: delete the `#[ignore = "enabled
in Task 7 (fence lift)"]` line on `lt_with_constant_pins_is_unsat_via_folding`,
and add these four, using the SAME `run_script`/`assert_eq!(out, vec![...])`
helper the folding test uses in that file:

```rust
#[test]
fn bare_symbolic_lt_is_sat() {
    // Empty-prefix base case: s="" < u="a".
    assert_sat("(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
                (assert (str.< s u))(check-sat)");
}

#[test]
fn lt_and_eq_is_unsat() {
    assert_unsat("(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
                  (assert (str.< s u))(assert (= s u))(check-sat)");
}

#[test]
fn lt_and_lt_swapped_bounded_len_is_unsat() {
    // CONGRUENCE GATE: equal single-char heads ⇒ code(hs)<code(hu)<code(hs).
    assert_unsat("(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
        (assert (str.< s u))(assert (str.< u s))\
        (assert (= (str.len s) 1))(assert (= (str.len u) 1))(check-sat)");
}

#[test]
fn lt_with_len1_is_sat() {
    assert_sat("(set-logic QF_S)(declare-fun s () String)(declare-fun u () String)\
        (assert (str.< s u))(assert (= (str.len s) 1))(check-sat)");
}
```

(Match the file's actual assertion style — if it uses `run_script(...) == vec![Verdict::Sat]`
rather than `assert_sat`/`assert_unsat`, mirror that exact form. Name the
helper you use in your report.)

- [ ] **Step 6: Run the 5-pin acceptance gate FOREGROUND — THE SLICE'S BAR**

Run: `cargo nextest run -p shinri-solver --test script_e2e --no-capture`
Expected: ALL pass, INCLUDING:
- `bare_symbolic_lt_is_sat` → Sat
- `lt_and_eq_is_unsat` → Unsat
- `lt_and_lt_swapped_bounded_len_is_unsat` → **Unsat** (congruence gate)
- `lt_with_len1_is_sat` → Sat
- `lt_with_constant_pins_is_unsat_via_folding` → **Unsat** (folding gate)

**If the congruence or folding gate is still `Unknown`:** STOP. Do NOT bump
fuel blindly, do NOT weaken/`#[ignore]` the gate. Diagnose with
superpowers:systematic-debugging: trace whether, after the phase hint lands the
solver on the `clt` disjunct, the length coupling `|s|=1 → |hA|=1 → |tA|=0 →
tA=""` reaches arith so `r_tail=(str.< "" "")` is false and congruence merges
`hs=hs'`. If you cannot resolve it, report BLOCKED with the exact failing pin,
its actual verdict, and your trace. Confirm >0 tests ran
(`cargo nextest list --test script_e2e`).

- [ ] **Step 7: String-path smoke + full string suite**

Run: `cargo nextest run -p shinri-str` (all green — fence-narrow guards) and
`cargo nextest run -p shinri-solver -E 'test(str)'` (no string-path
regressions; a z3-confirmed `Unknown → decided` e2e flip is an ADJUDICATED
flip, not a blocker — report which flipped and its new verdict; a
`decided → Unknown` or `sat↔unsat` flip IS a blocker).

Run: `cargo fmt --all` then `cargo clippy -p shinri-str -p shinri-solver --all-targets -- -D warnings`
Expected: clean. (Any `#[allow(dead_code)]` on order-engine builders now
reachable end-to-end may be removable — remove what clippy no longer needs,
report it.)

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-str/src/order.rs crates/shinri-solver/tests/script_e2e.rs
git commit -m "feat(str): slice31 T7 — narrow order fence (route symbolic pair, fence constant leftovers)"
```

---

## After this plan

Continue slice31 execution with the ORIGINAL plan's Tasks 8, 9, 10
(`docs/superpowers/plans/2026-07-19-shinri-slice31-str-order-symbolic-pair.md`):
- **Task 8** — e2e differential pins (`qfs_differential.rs`): flip
  `targeted_str_order_symbolic_pair_known_gap` → `_decides` (Sat + bounded
  Unsat idioms), and bank the unbounded-antisymmetry residual `Unknown`.
- **Task 9** — the `qfs_str_order_symbolic_pair_matches_z3` oracle family
  (0 disagreements; both `n_sat>0` and `n_unsat>0`).
- **Task 10** — fuel/tier check, full gate (`shinri-str`,
  `qfs_differential --features oracle`, `script_e2e`, clippy, fmt), truth-up
  the spec (now ALSO documenting the phase-preference capability and its oracle
  timing), PR, merge on green, delete branch.

## Self-Review

**Spec coverage (§10):** the phase-preference channel (§10.2 items 1-2) →
Task 1; the order-engine client tagging `a_eps`/`clt` preferred-TRUE (§10.2
item 3) → Task 2; the fence-lift + 5-pin acceptance validation (§10.4) → Task 3
+ (oracle) original Task 9; soundness (§10.3) is a Global Constraint enforced
across Tasks 1-3; the scope delta (§10.5) is exactly Tasks 1-2 before the
fence-lift.

**Placeholder scan:** the mechanical construction-site sweep (Task 1 Step 8)
lists every file:line from the interface map; the phase-seed code (Task 1 Step
6) and `phases_for` (Task 2 Step 3) are concrete. The only deliberately-open
item is matching the exact `script_e2e.rs` assertion helper name (Task 3 Step
5) and the exact assignment-state accessor in the sat test (Task 1 Step 1) —
both direct the implementer to mirror the file's existing style and report what
they used, because those are local naming details, not design decisions.

**Type consistency:** `phases: Vec<Option<bool>>` is identical across
`TCheck::Split`, `FinalCheck::Split`, `TheoryResult::SplitAtoms`;
`Assignment::set_phase(&mut self, v: Var, p: bool)`; `OrderFamily.a_eps`/`.clt:
TermId` and `phases_for(&self, &[TermId]) -> Vec<Option<bool>>` match their
consumers in Task 2 Step 5. The empty-`phases` == no-preference invariant is
stated in the Global Constraints and honoured at the single consume site
(`phases.get(i)` → `None` when empty).

**Risk note:** Task 3 Step 6 is the acceptance bar. The phase hint is
necessary; sufficiency also rests on the Task 4/6 length-coupling machinery. A
still-`Unknown` gate is a diagnose-don't-mask signal, explicitly flagged.
