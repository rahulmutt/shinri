# Splitting-on-Demand Infrastructure Implementation Plan (Plan A of QF_LIA)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a narrow, theory-valid *splitting-on-demand* seam so a theory can return a branch/cut **lemma clause over freshly-minted atoms** that the SAT solver case-splits on — the cross-crate substrate QF_LIA branch-and-bound (Plan B) will consume.

**Architecture:** The SAT solver already learns and backtracks on `TheoryResult::Lemma`. This plan adds the *missing* upstream half: a `TCheck::Split(Vec<TermId>)` verdict from a sub-theory, a `Combiner` lift to a new `TheoryResult::SplitAtoms(Vec<TermId>)`, and a **two-phase fresh-atom protocol** — the theory names split atoms as `TermId`s; the solver allocates a fresh `Var` per atom (`Solver::new_var`), then calls back `Theory::bind_fresh(var, atom)` so the `Combiner` registers the atom (`AtomRegistry`, append-only) and encodes it into the owning sub-theory before the clause is learnt. Two-phase ordering sidesteps the borrow conflict between `Solver` (owns var allocation) and `self.theory` (owns encoding).

**Tech Stack:** Rust 2021, `cargo test`, the existing `shinri-sat` DPLL(T) loop, `shinri-theory` Nelson–Oppen `Combiner`, `rustc_hash`.

## Global Constraints

- `edition = "2021"`, `rust-version = "1.96.0"` (workspace floor — do not raise).
- Only `shinri-num` on any arithmetic shipping path; `num-bigint`/`num-rational` are dev-only oracle deps (not touched in this plan).
- The atom space is **append-only across a solve** — fresh atoms minted mid-search are *never* un-registered on backtrack (mirrors `AtomRegistry` / spec §6.5).
- The new lemma channel is **narrow**: the only permissible `TCheck::Split` payloads are theory-valid split/cut clauses. `EmptyTheory` and `Euf` MUST remain on the Sat/Conflict path (no `Split`).
- Run the full workspace build + tests after every task: `cargo test --workspace`. Format before every commit: `cargo fmt`.
- Reference design spec: `docs/superpowers/specs/2026-06-20-shinri-arith-lia-design.md` §2 (the seam) and §1 (scope).

---

## File Structure

| File | Responsibility | Change |
|---|---|---|
| `crates/shinri-sat/src/types.rs` | `TheoryResult` enum | Add `SplitAtoms(Vec<TermId>)` variant |
| `crates/shinri-sat/src/theory.rs` | `Theory` trait the solver calls | Add `bind_fresh(&mut self, v: Var, atom: TermId)` default-no-op method |
| `crates/shinri-sat/src/solver.rs` | DPLL(T) main loop | Handle `SplitAtoms`: alloc fresh vars → `bind_fresh` → learn clause → backtrack one level |
| `crates/shinri-theory/src/solver_trait.rs` | per-theory `TCheck` + `TheorySolver` | Add `TCheck::Split(Vec<TermId>)`; update stubs |
| `crates/shinri-theory/src/combiner.rs` | Nelson–Oppen driver = the `Theory` impl | Lift sub-theory `Split` → `SplitAtoms`; implement `bind_fresh` (register + encode) |

No new files; all changes extend existing modules. Each sub-theory's `check` keeps one responsibility; the split path is additive.

---

### Task 1: `TheoryResult::SplitAtoms` variant

**Files:**
- Modify: `crates/shinri-sat/src/types.rs`
- Test: `crates/shinri-sat/src/types.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Consumes: `shinri_core::TermId` (already a dependency of `shinri-sat`).
- Produces: `TheoryResult::SplitAtoms(Vec<TermId>)` — a clause of *positive* atoms to be minted and case-split; consumed by Task 3 (solver) and Task 5 (Combiner lift).

- [ ] **Step 1: Write the failing test**

In the `#[cfg(test)] mod tests` block of `crates/shinri-sat/src/types.rs`:

```rust
#[test]
fn split_atoms_holds_term_ids() {
    let t = shinri_core::TermId::new(7);
    let r = TheoryResult::SplitAtoms(vec![t]);
    match r {
        TheoryResult::SplitAtoms(atoms) => assert_eq!(atoms, vec![t]),
        _ => panic!("expected SplitAtoms"),
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-sat split_atoms_holds_term_ids`
Expected: FAIL to compile — `no variant named SplitAtoms`.

- [ ] **Step 3: Add the variant**

Add `use shinri_core::TermId;` if not already imported at the top of `types.rs`, then extend the enum:

```rust
/// The result of a theory consistency `check` (spec §8.1). `Conflict`/`Lemma`
/// carry literal sets the solver folds into conflict analysis. `SplitAtoms`
/// carries a clause of *positive atoms* (as `TermId`s) the solver must mint
/// fresh vars for, bind into the theory, then learn + case-split (splitting on
/// demand — QF_LIA Plan A).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TheoryResult {
    Sat,
    Conflict(Vec<Lit>),
    Lemma(Vec<Lit>),
    SplitAtoms(Vec<TermId>),
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-sat split_atoms_holds_term_ids`
Expected: PASS. (Other crates may now have non-exhaustive `match` warnings/errors on `TheoryResult`; Task 3 fixes the solver's match. If `Combiner` matches `TheoryResult` it is in `shinri-theory`, handled in Task 5 — the workspace may not build green until then; build `-p shinri-sat` only for now.)

Run: `cargo test -p shinri-sat`
Expected: PASS (the `shinri-sat` crate alone has no exhaustive external match on this enum).

- [ ] **Step 5: Commit**

```bash
cargo fmt -p shinri-sat
git add crates/shinri-sat/src/types.rs
git commit -m "feat(sat): TheoryResult::SplitAtoms — splitting-on-demand atom clause"
```

---

### Task 2: `Theory::bind_fresh` callback hook

**Files:**
- Modify: `crates/shinri-sat/src/theory.rs`
- Test: `crates/shinri-sat/src/theory.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Produces: `Theory::bind_fresh(&mut self, v: Var, atom: TermId)` — called by the solver (Task 3) once per freshly-allocated split var, *before* the split clause is learnt, so the theory can register `v → atom` and encode it. Default impl is a no-op (theories that never split need not implement it).
- Consumes: `shinri_core::{Var, TermId}`.

- [ ] **Step 1: Write the failing test**

In the `#[cfg(test)] mod tests` block of `crates/shinri-sat/src/theory.rs` (define or extend a minimal stub `Theory` used by existing tests; if a stub already exists, add the recording field + test against it):

```rust
#[test]
fn bind_fresh_default_is_noop_and_overridable() {
    #[derive(Default)]
    struct Recorder { bound: Vec<(Var, TermId)> }
    impl Theory for Recorder {
        fn new_var(&mut self, _v: Var) {}
        fn assert(&mut self, _l: Lit) {}
        fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> { None }
        fn check(&mut self, _e: Effort) -> TheoryResult { TheoryResult::Sat }
        fn explain(&mut self, _j: TheoryJust, _out: &mut Vec<Lit>) {}
        fn push(&mut self) {}
        fn pop(&mut self, _n: usize) {}
        fn bind_fresh(&mut self, v: Var, atom: TermId) { self.bound.push((v, atom)); }
    }
    let mut r = Recorder::default();
    let v = Var::new(3);
    let t = TermId::new(9);
    r.bind_fresh(v, t);
    assert_eq!(r.bound, vec![(v, t)]);
}
```

> NOTE: copy the *exact* current `Theory` trait method signatures from `crates/shinri-sat/src/theory.rs` into the stub above — the methods shown (`new_var`/`assert`/`propagate`/`check`/`explain`/`push`/`pop`) reflect the trait at planning time; match whatever the file currently declares so the impl is complete.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-sat bind_fresh_default_is_noop_and_overridable`
Expected: FAIL to compile — `no method named bind_fresh` / `not a member of trait Theory`.

- [ ] **Step 3: Add the trait method with a default no-op**

Add `use shinri_core::TermId;` to `theory.rs` if absent. Inside `pub trait Theory`, after the existing methods:

```rust
    /// Bind a freshly-minted split atom to the var the solver just allocated
    /// for it (splitting on demand, QF_LIA Plan A). Called once per atom in a
    /// `TheoryResult::SplitAtoms` clause, BEFORE the clause is learnt, so the
    /// theory can register `v -> atom` and build its encoding. Default no-op:
    /// theories that never emit `SplitAtoms` need not implement it.
    fn bind_fresh(&mut self, _v: Var, _atom: TermId) {}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-sat bind_fresh_default_is_noop_and_overridable`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
cargo fmt -p shinri-sat
git add crates/shinri-sat/src/theory.rs
git commit -m "feat(sat): Theory::bind_fresh hook for minting split atoms"
```

---

### Task 3: Solver handles `SplitAtoms` in the main loop

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs` (the `theory.check(Effort::Full)` match, ~line 534–579)
- Test: `crates/shinri-sat/src/solver.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Consumes: `TheoryResult::SplitAtoms` (Task 1), `Theory::bind_fresh` (Task 2), `Solver::new_var` (existing, `solver.rs:80`), `self.add_learnt`, `self.backtrack_to`, `self.trail.decision_level()`.
- Produces: the runtime behavior Plan B relies on — a split clause over fresh vars, learnt, with a one-level backtrack to force the case-split.

- [ ] **Step 1: Write the failing test**

In the `#[cfg(test)] mod tests` of `solver.rs`. This stub returns `SplitAtoms` once (the atom `TermId` is a sentinel; the stub's `bind_fresh` records which var the solver assigned), then `Sat`:

```rust
#[test]
fn solver_materializes_split_atoms_then_converges() {
    use std::cell::RefCell;
    use std::rc::Rc;

    #[derive(Default)]
    struct Splitter {
        fired: bool,
        bound_vars: Rc<RefCell<Vec<Var>>>,
    }
    impl Theory for Splitter {
        fn new_var(&mut self, _v: Var) {}
        fn assert(&mut self, _l: Lit) {}
        fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> { None }
        fn check(&mut self, _e: Effort) -> TheoryResult {
            if !self.fired {
                self.fired = true;
                // Two split atoms named by sentinel TermIds; solver mints vars.
                TheoryResult::SplitAtoms(vec![TermId::new(100), TermId::new(101)])
            } else {
                TheoryResult::Sat
            }
        }
        fn explain(&mut self, _j: TheoryJust, _out: &mut Vec<Lit>) {}
        fn push(&mut self) {}
        fn pop(&mut self, _n: usize) {}
        fn bind_fresh(&mut self, v: Var, _atom: TermId) { self.bound_vars.borrow_mut().push(v); }
    }

    // A trivially-SAT formula with one real var so search reaches the Full check.
    let mut s = Solver::<Splitter>::new();
    let a = s.new_var();
    s.add_clause(&[Lit::new(a, true)]); // forces a then a Full check

    let res = s.solve();
    assert!(matches!(res, SolveResult::Sat));
    // The two split atoms were bound to two freshly-minted vars (indices above `a`).
    let bound = s.theory_ref().bound_vars.borrow().clone();
    assert_eq!(bound.len(), 2);
    assert!(bound.iter().all(|v| v.index() > a.index()));
}
```

> NOTE: adapt constructor/driver names (`Solver::<T>::new`, `add_clause`, `solve`, and a `theory_ref()` accessor) to whatever `solver.rs` already exposes — read the file's existing tests for the exact harness. If no `theory_ref()` accessor exists, add a `#[cfg(test)] pub(crate) fn theory_ref(&self) -> &T { &self.theory }`. Use `Rc<RefCell<..>>` (as shown) to observe `bind_fresh` from outside, or an existing test accessor pattern if the file has one.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-sat solver_materializes_split_atoms_then_converges`
Expected: FAIL — non-exhaustive match on `TheoryResult` (the `SplitAtoms` arm is missing), or a panic when the solver hits the unhandled variant.

- [ ] **Step 3: Add the `SplitAtoms` arm**

In `solver.rs`, in the `match self.theory.check(Effort::Full)` block, add alongside `Sat`/`Conflict`/`Lemma`:

```rust
TheoryResult::SplitAtoms(atoms) => {
    // Two-phase fresh-atom protocol (QF_LIA Plan A). Phase 1: allocate a
    // fresh var per split atom and let the theory bind+encode it BEFORE the
    // clause exists. new_var() updates assignment/heuristic/watches/analyzer,
    // so the fresh vars are immediately usable in a learnt clause.
    let mut lits: Vec<Lit> = Vec::with_capacity(atoms.len());
    for atom in atoms {
        let v = self.new_var();
        self.theory.bind_fresh(v, atom);
        lits.push(Lit::new(v, true));
    }
    // Phase 2: learn the split clause and backtrack one level so the solver
    // must case-split on it (mirrors the existing Lemma path).
    self.add_learnt(&lits);
    let dl = self.trail.decision_level();
    if dl > 0 {
        self.backtrack_to(dl - 1);
    }
}
```

> NOTE: place this arm exactly where the existing `TheoryResult::Lemma(lits) => { self.add_learnt(&lits); ... }` arm sits (~solver.rs:573) and mirror its post-learn control flow (continue the outer search loop). If `add_learnt` returns a value the `Lemma` arm ignores, ignore it identically.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-sat solver_materializes_split_atoms_then_converges`
Expected: PASS.

Run: `cargo test -p shinri-sat`
Expected: PASS (all existing `shinri-sat` tests still green).

- [ ] **Step 5: Commit**

```bash
cargo fmt -p shinri-sat
git add crates/shinri-sat/src/solver.rs
git commit -m "feat(sat): solver mints + learns SplitAtoms (splitting on demand)"
```

---

### Task 4: `TCheck::Split` per-theory verdict

**Files:**
- Modify: `crates/shinri-theory/src/solver_trait.rs` (the `TCheck` enum + the inline stub theories `NullTheory`/any others)
- Test: `crates/shinri-theory/src/solver_trait.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Produces: `TCheck::Split(Vec<TermId>)` — a sub-theory's request to split on a clause of positive atoms; consumed by the `Combiner` in Task 5.
- Consumes: `shinri_core::TermId` (already imported in this file).

- [ ] **Step 1: Write the failing test**

In the `#[cfg(test)] mod tests` of `solver_trait.rs`:

```rust
#[test]
fn tcheck_split_carries_atoms() {
    let t = shinri_core::TermId::new(5);
    let c = TCheck::Split(vec![t]);
    match c {
        TCheck::Split(atoms) => assert_eq!(atoms, vec![t]),
        _ => panic!("expected Split"),
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-theory tcheck_split_carries_atoms`
Expected: FAIL to compile — `no variant named Split`.

- [ ] **Step 3: Add the variant**

Add `use shinri_core::TermId;` to `solver_trait.rs` if absent, then:

```rust
/// A sub-theory consistency verdict. Convex Phase-1 theories produce conflicts,
/// never free-standing lemmas. `Split` is the SINGLE sanctioned exception (QF_LIA
/// Plan A): a clause of theory-valid positive atoms (`TermId`s) the Combiner
/// lifts to `TheoryResult::SplitAtoms`. Only arithmetic emits it; EUF/Empty never do.
pub enum TCheck {
    Sat,
    Conflict(Vec<EqLeaf>),
    Split(Vec<TermId>),
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-theory tcheck_split_carries_atoms`
Expected: FAIL to compile elsewhere — any `match` on `TCheck` that was exhaustive (e.g. inside `Combiner::drive_final_check`, or the `NullTheory`/`Spy`/`AssertConflicter` test stubs that *return* `TCheck` are fine; the matches that *consume* it are not). For each exhaustive `match tcheck { TCheck::Sat => .., TCheck::Conflict(..) => .. }`, add `TCheck::Split(_) => unreachable!("only arith emits Split; lifted in Combiner::check — Task 5")` for now. (Task 5 replaces the Combiner one with real handling.)

After adding those temporary arms:

Run: `cargo test -p shinri-theory tcheck_split_carries_atoms`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
cargo fmt -p shinri-theory
git add crates/shinri-theory/src/solver_trait.rs
git commit -m "feat(theory): TCheck::Split — per-theory split-clause verdict"
```

---

### Task 5: `Combiner` lifts `Split` → `SplitAtoms` and implements `bind_fresh`

**Files:**
- Modify: `crates/shinri-theory/src/combiner.rs` (`drive_final_check`, the `Theory::check` impl ~line 170, and add a `bind_fresh` impl)
- Test: `crates/shinri-theory/src/combiner.rs` (inline `#[cfg(test)]`)

**Interfaces:**
- Consumes: `TCheck::Split` (Task 4) from `self.arith.check` / `self.euf.check`; `TheoryResult::SplitAtoms` (Task 1); `Theory::bind_fresh` (Task 2); `classify` + `AtomRegistry::register` + the per-sub-theory `new_var` (existing in `register_atom`, ~combiner.rs:59).
- Produces: `Combiner` (the `Theory` impl) emits `SplitAtoms` and, on the solver's `bind_fresh` callback, registers each fresh `(var, atom)` to its owning sub-theory and encodes it.

- [ ] **Step 1: Write the failing test**

In the `#[cfg(test)] mod tests` of `combiner.rs`. Use the existing `Spy`/stub pattern for the `E` (euf) slot and a stub `A` (arith) slot that returns `Split` once. The test drives `Combiner::check(Effort::Full)` directly and asserts it returns `SplitAtoms`, then calls `bind_fresh` and checks the atom is registered to the arith owner:

```rust
#[test]
fn combiner_lifts_split_and_binds_fresh() {
    // Arith-slot stub: returns Split(one atom) on first Full check, then Sat.
    #[derive(Default)]
    struct ArithSplitter { fired: bool, bound: Vec<(Var, TermId)> }
    impl TheorySolver for ArithSplitter {
        const THEORY_ID: u16 = 7;
        fn new_var(&mut self, _cx: &mut TheoryCtx, v: Var, atom: TermId) { self.bound.push((v, atom)); }
        fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> { None }
        fn propagate(&mut self, _cx: &mut TheoryCtx, _o: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> { None }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            if !self.fired { self.fired = true; TCheck::Split(vec![TermId::new(42)]) } else { TCheck::Sat }
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _l: usize) {}
    }

    let mut comb: Combiner<NullTheory, ArithSplitter> = Combiner::default();
    // First Full check lifts the arith Split into SplitAtoms.
    match Theory::check(&mut comb, Effort::Full) {
        TheoryResult::SplitAtoms(atoms) => assert_eq!(atoms, vec![TermId::new(42)]),
        other => panic!("expected SplitAtoms, got {other:?}"),
    }
    // Solver would now allocate a var and call back bind_fresh; simulate it.
    let v = Var::new(0);
    Theory::bind_fresh(&mut comb, v, TermId::new(42));
    // The fresh atom is registered to the Arith owner and encoded by the arith slot.
    assert_eq!(comb.atoms_ref().owner(v), Owner::Arith);
    assert_eq!(comb.arith_ref().bound, vec![(v, TermId::new(42))]);
}
```

> NOTE: `NullTheory` is the existing do-nothing stub in `solver_trait.rs` tests — re-export or define a local equivalent for the `E` slot. Add `#[cfg(test)] pub(crate)` accessors `atoms_ref(&self) -> &AtomRegistry` and `arith_ref(&self) -> &A` to `Combiner` if none exist. `bind_fresh` for a split atom must route by `Owner`; in this plan all split atoms are arithmetic, so register as `Owner::Arith` directly (do NOT call `classify`, which would reject a sentinel `TermId` with no real term node).

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-theory combiner_lifts_split_and_binds_fresh`
Expected: FAIL — `Combiner::check` never returns `SplitAtoms` (it returns Sat/Conflict only), and `bind_fresh`/accessors don't exist.

- [ ] **Step 3: Thread `Split` through `drive_final_check` and implement `bind_fresh`**

(a) Change `drive_final_check`'s return type to carry a split. Define a small private enum at the top of `combiner.rs`:

```rust
enum FinalCheck {
    Sat,
    Conflict(Vec<crate::types::EqLeaf>),
    Split(Vec<TermId>),
}
```

In `drive_final_check`, where it currently calls `self.euf.check(..)` / `self.arith.check(..)` and matches `TCheck::Conflict`, also intercept `TCheck::Split`:

```rust
match self.arith.check(&mut cx, Effort::Full) {
    TCheck::Conflict(cf) => return FinalCheck::Conflict(cf),
    TCheck::Split(atoms) => return FinalCheck::Split(atoms),
    TCheck::Sat => {}
}
```

Apply the same to the `self.euf.check(..)` site (EUF returns `Sat`/`Conflict` only, so its `Split` arm is `TCheck::Split(_) => unreachable!("EUF never splits")`). Have `drive_final_check` return `FinalCheck::Sat` where it previously returned `None`, and `FinalCheck::Conflict(..)` where it returned `Some(leaves)`.

(b) Rewrite the `Theory::check` impl to map `FinalCheck`:

```rust
fn check(&mut self, effort: Effort) -> TheoryResult {
    if effort == Effort::Standard {
        return TheoryResult::Sat;
    }
    match self.drive_final_check() {
        FinalCheck::Sat => TheoryResult::Sat,
        FinalCheck::Conflict(leaves) => TheoryResult::Conflict(self.expand_conflict(leaves)),
        FinalCheck::Split(atoms) => TheoryResult::SplitAtoms(atoms),
    }
}
```

(c) Implement `bind_fresh` on the `Combiner`'s `Theory` impl. Split atoms in this milestone are always arithmetic; register to `Owner::Arith` and encode via the arith slot, reusing the borrow-split (`§5.5`) pattern from `register_atom`:

```rust
fn bind_fresh(&mut self, v: Var, atom: TermId) {
    self.atoms.register(v, atom, Owner::Arith);
    // Borrow-split: build the ctx from the non-arith fields, then call arith.
    let mut cx = TheoryCtx { terms: &self.terms, eq: &mut self.eq, atoms: &self.atoms };
    self.arith.new_var(&mut cx, v, atom);
}
```

> NOTE: match the *exact* field names and the existing borrow-split idiom used in `register_atom` (the comment there cites "the §5.5 pattern"); `self.terms`/`self.eq`/`self.atoms` names shown reflect the file at planning time. Add the `#[cfg(test)] pub(crate)` accessors named in the test.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-theory combiner_lifts_split_and_binds_fresh`
Expected: PASS.

Run: `cargo test -p shinri-theory`
Expected: PASS (existing Combiner tests green; the temporary `unreachable!` arms from Task 4 are now replaced where the Combiner is concerned).

- [ ] **Step 5: Commit**

```bash
cargo fmt -p shinri-theory
git add crates/shinri-theory/src/combiner.rs
git commit -m "feat(theory): Combiner lifts TCheck::Split to SplitAtoms + bind_fresh wiring"
```

---

### Task 6: End-to-end split-and-converge integration test

**Files:**
- Test: `crates/shinri-theory/tests/splitting_on_demand.rs` (new integration test) — or, if `shinri-theory` has no `tests/` dir and the SAT driver lives in `shinri-sat`, place it in `crates/shinri-sat/tests/` wiring a `Combiner` as the `Theory`. Pick whichever crate can construct both a `Solver` and a `Combiner` (read `shinri-solver` for how it wires them).

**Interfaces:**
- Consumes: everything from Tasks 1–5 — proves the full loop: sub-theory `Split` → `Combiner` `SplitAtoms` → `Solver` mints vars + `bind_fresh` + learn + backtrack → search assigns the fresh literals → `Sat`.

- [ ] **Step 1: Write the failing test**

Create the integration test. Drive a real `Solver` whose `Theory` is a `Combiner<NullTheory, OneShotSplitter>` where `OneShotSplitter` returns `TCheck::Split(vec![a1, a2])` exactly once (atoms are real `TermId`s built in a `Context` so `bind_fresh`→`arith.new_var` accepts them; the splitter's own `new_var` records them and its `check` returns `Sat` after the split). Assert: solve returns `Sat`, two fresh vars were created and bound, and the learnt split clause is satisfied in the final assignment.

```rust
// crates/shinri-sat/tests/splitting_on_demand.rs  (adjust crate per the file note)
// Pseudostructure — fill with the real Solver/Combiner constructors from
// shinri-solver's wiring (see crates/shinri-solver/src/lib.rs for the canonical
// `Combiner<Euf, Arith>` + `Solver` setup; swap Arith for OneShotSplitter here).
#[test]
fn split_once_then_sat_end_to_end() {
    // 1. Build a Context with two Int consts and the atoms (x <= 0), (x >= 1).
    // 2. Solver<Combiner<NullTheory, OneShotSplitter>> seeded so a Full check runs.
    // 3. OneShotSplitter::check returns Split([le_atom, ge_atom]) once, then Sat.
    // 4. assert!(matches!(solver.solve(), SolveResult::Sat));
    // 5. assert the two split vars exist and at least one split literal is true.
}
```

> NOTE: This task's deliverable is a *real, compiling* test. Read `crates/shinri-solver/src/lib.rs` for the exact `Combiner`/`Solver` construction and `register_atom` flow, and the existing `shinri-sat` integration tests for the solve harness, then replace the pseudostructure with concrete code. The `OneShotSplitter` is the `ArithSplitter` from Task 5 with a real `new_var` that interns the atom (it can be a near-no-op that just records, since this test only exercises the *plumbing*, not real arithmetic).

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-sat --test splitting_on_demand`
Expected: FAIL (test not yet implemented / asserts unmet) — confirm it fails for the *right* reason (e.g. compiles and the assertion is what fails), not a wiring typo.

- [ ] **Step 3: Implement the test body fully**

Replace the pseudostructure with concrete construction code per the NOTE. No production code should be needed — Tasks 1–5 supply the mechanism; if production code *is* needed, that reveals a gap to fix in the relevant earlier file.

- [ ] **Step 4: Run test + full workspace**

Run: `cargo test -p shinri-sat --test splitting_on_demand`
Expected: PASS.

Run: `cargo test --workspace`
Expected: PASS — the whole workspace builds and all tests are green (this is the gate that the `TCheck`/`TheoryResult` changes didn't break any consumer).

- [ ] **Step 5: Commit**

```bash
cargo fmt --all
git add crates/shinri-sat/tests/splitting_on_demand.rs
git commit -m "test(theory): end-to-end splitting-on-demand converges to sat"
```

---

## Self-Review

**Spec coverage (vs design spec §2):**
- §2.1 "`TCheck` gains a `Split` variant" → Task 4. ✅
- §2.1 "`TheoryCtx` gains a `fresh_atom` seam / fresh var allocation mid-search" → realized as the two-phase `bind_fresh` protocol (Tasks 2,3,5) rather than a synchronous `fresh_atom` call, deliberately, to avoid the Solver↔theory borrow conflict. The spec's *intent* (theory mints atoms, solver allocates vars, atom routes to `Owner::Arith`) is fully met. ✅
- §2.1 "mid-search fresh var + atom→owner registration" → Task 3 (`new_var`) + Task 5 (`AtomRegistry::register`). ✅
- §2.1 "`Combiner` on `Split`, hand clause to SAT and continue" → Task 5 lift + Task 3 learn/backtrack. ✅
- §2.1 "`EmptyTheory`/`Euf` unaffected" → Task 4 makes their `Split` arm `unreachable!`; Task 5 EUF `Split` arm `unreachable!`. ✅
- Append-only atom space / never un-registered on backtrack (§8) → relies on existing `AtomRegistry` semantics; no `pop` change. ✅

**Out of scope for Plan A (lands in Plan B), intentionally not covered here:**
- Arith *producing* real `TCheck::Split` from a fractional-var scan; a-priori bounds; GMI cuts; narrowing the `contains_int_arith` fence; integer models. Plan A delivers only the *mechanism*, validated by stub theories.
- Making `TheoryCtx.terms` mutable so Arith can *build* branch/cut `TermId`s — deferred to Plan B (Plan A's split atoms are supplied pre-built by stubs/tests). Flag for Plan B: this is its first task.

**Placeholder scan:** Task 6's body is intentionally a guided pseudostructure with a hard requirement to produce compiling code — every other task has complete code. The two-phase protocol, enum variants, and solver arm are all spelled out in full. No "TBD"/"add error handling"/"similar to" placeholders. ✅

**Type consistency:** `TheoryResult::SplitAtoms(Vec<TermId>)` (Task 1) ↔ `TCheck::Split(Vec<TermId>)` (Task 4) ↔ `FinalCheck::Split(Vec<TermId>)` (Task 5) ↔ `bind_fresh(v: Var, atom: TermId)` (Tasks 2,3,5) — all carry `TermId`/`Var` consistently. `Lit::new(v, true)` positive-atom convention is uniform. ✅

**Known adaptation points (called out inline, not placeholders):** exact `Theory` trait method list (Task 2 NOTE), solver test harness names (Task 3 NOTE), `Combiner` borrow-split idiom + field names + test accessors (Task 5 NOTE), and the integration crate/wiring (Task 6 NOTE). These are "match the file as it exists," not undecided design.
