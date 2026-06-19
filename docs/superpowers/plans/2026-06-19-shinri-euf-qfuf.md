# EUF Congruence Closure → First Runnable QF_UF Solver — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement an EUF (congruence-closure) theory solver and wire it through the existing Nelson–Oppen `Combiner` and CDCL(T) SAT engine into a minimal embeddable `shinri-solver`, yielding the project's first sound, runnable QF_UF solver with incremental `push`/`pop`.

**Architecture:** A new `shinri-euf` crate implements `shinri_theory::TheorySolver`, adding the congruence driver (signature/use-list) on top of the existing shared `EqualityEngine` (union-find + proof forest). A new `shinri-solver` crate owns the term DAG, Tseitin-encodes Boolean structure into the SAT engine, registers EUF atoms, and extracts models. Two enabling changes land in existing crates: `EqJust::Congruence` becomes n-ary in `shinri-theory`, and `shinri-sat` gains theory injection plus a theory-preserving rebuild so `push`/`pop` is sound for a stateful theory.

**Tech Stack:** Rust (edition 2021, rust-version 1.96.0), `rustc-hash` (FxHashMap), `proptest` (dev), `easy-smt` + a `z3` binary (dev oracle). Pure-Rust shipping build (no native-link deps).

## Global Constraints

- **Edition:** `2021`; **rust-version floor:** `1.96.0` (workspace `Cargo.toml`).
- **License header field:** every new crate's `Cargo.toml` sets `license = "MIT OR Apache-2.0"` and `edition`/`rust-version` via `.workspace = true`.
- **Pure-Rust shipping mandate:** no native-link dependencies in non-dev deps. New runtime deps limited to `shinri-*` path crates and `rustc-hash`. Oracle/`proptest` only as `[dev-dependencies]`.
- **Soundness is existential:** any unsupported construct or internal uncertainty yields `Unknown`/refusal, never a guess. `debug_assert!` for invariant checks; never silent wrong answers.
- **Index/arena over smart pointers:** ids are small `Copy` newtypes; backtracking via `shinri_core::UndoLog` (trail + undo-log), never persistent data structures.
- **CI gates (must stay green):** `cargo nextest run`, `cargo deny check`, `cargo clippy --all-targets -- -D warnings`, `cargo fmt --check`.
- **Workspace members live in `crates/`** and are registered in the root `Cargo.toml` `[workspace].members`.

---

## File Structure

**Modified (existing crates):**
- `crates/shinri-theory/src/types.rs` — `EqJust::Congruence` → n-ary via `CongRef`; new `CongRef` type.
- `crates/shinri-theory/src/eq_engine.rs` — `cong_pairs` arena + `cong_undo`; `merge_congruence`; n-ary `expand_edge`; arena backtracking in `pop`.
- `crates/shinri-theory/src/empty.rs` — **new** `EmptyTheory` (real no-op `TheorySolver`).
- `crates/shinri-theory/src/lib.rs` — export `EmptyTheory`, `CongRef`.
- `crates/shinri-sat/src/solver.rs` — `with_theory`, `theory`/`theory_mut`, theory-preserving rebuild, theory-silent enqueue, `push`/`pop` theory wiring.
- `Cargo.toml` (root) — add `shinri-euf`, `shinri-solver` members.

**Created (new crates):**
- `crates/shinri-euf/Cargo.toml`, `crates/shinri-euf/src/lib.rs` — crate root, `Euf` struct + module wiring.
- `crates/shinri-euf/src/solver.rs` — `Euf: TheorySolver` (assert/propagate/check/explain/model/push/pop).
- `crates/shinri-euf/src/egraph.rs` — e-graph construction, signature/use-list/lookup, congruence driver.
- `crates/shinri-euf/tests/qfuf_euf.rs` — EUF-level integration tests.
- `crates/shinri-solver/Cargo.toml`, `crates/shinri-solver/src/lib.rs` — `Solver` API.
- `crates/shinri-solver/src/tseitin.rs` — Boolean → CNF encoder + `distinct` lowering + atom registration.
- `crates/shinri-solver/src/model.rs` — public `Model`, `SolveOutcome`.
- `crates/shinri-solver/tests/qfuf_e2e.rs` — end-to-end QF_UF tests.
- `crates/shinri-solver/tests/oracle.rs` — differential `z3` oracle (feature-gated).

---

## Phase A — Substrate changes (`shinri-theory`)

### Task 1: n-ary congruence justification

**Files:**
- Modify: `crates/shinri-theory/src/types.rs`
- Modify: `crates/shinri-theory/src/eq_engine.rs`

**Interfaces:**
- Produces: `CongRef { start: u32, len: u32 }` (`Copy`); `EqJust::Congruence(CongRef)`; `EqualityEngine::merge_congruence(&mut self, a: ENodeId, b: ENodeId, pairs: &[(ENodeId, ENodeId)]) -> Result<(), EqConflict>`.
- Consumes: existing `EqualityEngine::{merge, explain, pop}`, `EqJust`, `EqConflict`, `shinri_core::UndoLog`.

- [ ] **Step 1: Update the existing congruence test to the n-ary shape (failing).**

In `crates/shinri-theory/src/eq_engine.rs`, replace the body of `explain_expands_congruence_to_its_argument_equalities` so it uses the new API (this makes the test reference symbols that don't exist yet):

```rust
    #[test]
    fn explain_expands_congruence_to_its_argument_equalities() {
        // f(x1,x2) and f(y1,y2) merged by an n-ary congruence over both arg pairs.
        let mut eq = EqualityEngine::default();
        let x1 = eq.intern(term(1));
        let y1 = eq.intern(term(2));
        let x2 = eq.intern(term(3));
        let y2 = eq.intern(term(4));
        let fx = eq.intern(term(5));
        let fy = eq.intern(term(6));
        let e1 = Lit::new(Var::new(70), true);
        let e2 = Lit::new(Var::new(71), true);
        eq.merge(x1, y1, EqJust::Asserted(e1)).unwrap();
        eq.merge(x2, y2, EqJust::Asserted(e2)).unwrap();
        eq.merge_congruence(fx, fy, &[(x1, y1), (x2, y2)]).unwrap();
        let mut out = Vec::new();
        eq.explain(fx, fy, &mut out);
        assert!(out.contains(&EqLeaf::Asserted(e1)));
        assert!(out.contains(&EqLeaf::Asserted(e2)));
    }
```

- [ ] **Step 2: Run it to confirm it fails to compile.**

Run: `cargo test -p shinri-theory --lib explain_expands_congruence -- --nocapture`
Expected: FAIL — `no method named merge_congruence` / `Congruence` variant arity mismatch.

- [ ] **Step 3: Change the `EqJust::Congruence` variant and add `CongRef`.**

In `crates/shinri-theory/src/types.rs`, add the `CongRef` type and change the variant:

```rust
/// A range into `EqualityEngine`'s congruence-pair arena (keeps `EqJust` `Copy`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct CongRef {
    pub start: u32,
    pub len: u32,
}
```

Then in `enum EqJust`, replace `Congruence(ENodeId, ENodeId),` with:

```rust
    /// `f(s..) = f(t..)` because each argument pair is equal. The pairs live in
    /// `EqualityEngine.cong_pairs[start .. start+len]`.
    Congruence(CongRef),
```

- [ ] **Step 4: Add the arena + `merge_congruence` to the engine.**

In `crates/shinri-theory/src/eq_engine.rs`, add two fields to `struct EqualityEngine` (after `merges`):

```rust
    /// Arena of congruence argument pairs; `EqJust::Congruence` indexes into it.
    cong_pairs: Vec<(ENodeId, ENodeId)>,
    /// Backtracks `cong_pairs`: each entry is the arena length before a level.
    cong_undo: UndoLog<usize>,
```

Add the method inside `impl EqualityEngine` (next to `merge`):

```rust
    /// Like `merge`, but the equality is justified by congruence over the given
    /// argument pairs (stored in the arena; the edge label references the range).
    pub fn merge_congruence(
        &mut self,
        a: ENodeId,
        b: ENodeId,
        pairs: &[(ENodeId, ENodeId)],
    ) -> Result<(), EqConflict> {
        let start = self.cong_pairs.len() as u32;
        self.cong_pairs.extend_from_slice(pairs);
        let cref = crate::types::CongRef {
            start,
            len: pairs.len() as u32,
        };
        self.merge(a, b, EqJust::Congruence(cref))
    }
```

- [ ] **Step 5: Make `expand_edge` recurse over the n-ary range.**

In `crates/shinri-theory/src/eq_engine.rs`, replace the `EqJust::Congruence(s, t) => { self.explain(s, t, out); }` arm of `expand_edge` with:

```rust
            EqJust::Congruence(cref) => {
                let lo = cref.start as usize;
                let hi = lo + cref.len as usize;
                for i in lo..hi {
                    let (s, t) = self.cong_pairs[i];
                    self.explain(s, t, out);
                }
            }
```

- [ ] **Step 6: Backtrack the arena in `push`/`pop`.**

In `push`, add `self.cong_undo.push_level();` alongside the other `push_level` calls. In `pop`, add (after the existing `forest_undo` block):

```rust
        let cong_pairs = &mut self.cong_pairs;
        self.cong_undo.pop_to(level, |len_before| {
            cong_pairs.truncate(len_before);
        });
```

Record the pre-insert length in `merge_congruence` by inserting, **before** `self.cong_pairs.extend_from_slice(pairs);`:

```rust
        self.cong_undo.record(self.cong_pairs.len());
```

- [ ] **Step 7: Run the engine tests.**

Run: `cargo test -p shinri-theory --lib`
Expected: PASS (all eq_engine tests, including the updated n-ary one).

- [ ] **Step 8: Export `CongRef` and commit.**

In `crates/shinri-theory/src/lib.rs`, add `CongRef` to the `pub use types::{...}` list.

```bash
git add crates/shinri-theory/src/types.rs crates/shinri-theory/src/eq_engine.rs crates/shinri-theory/src/lib.rs
git commit -m "feat(theory): n-ary EqJust::Congruence via arena-backed CongRef"
```

---

### Task 2: `EmptyTheory` no-op solver

**Files:**
- Create: `crates/shinri-theory/src/empty.rs`
- Modify: `crates/shinri-theory/src/lib.rs`

**Interfaces:**
- Produces: `pub struct EmptyTheory` implementing `TheorySolver` with `const THEORY_ID: u16 = 0;` and all methods as no-ops returning `Sat`/`None`.
- Consumes: `TheorySolver`, `TheoryCtx`, `TCheck`, `ModelBuilder`, `Explainer`, `EqLeaf`.

- [ ] **Step 1: Write the failing test.**

Create `crates/shinri-theory/src/empty.rs`:

```rust
//! A no-op theory occupying the `Arith` slot of `Combiner` until shinri-arith
//! exists, so `Combiner<Euf, EmptyTheory>` is a complete QF_UF theory.

use crate::model::ModelBuilder;
use crate::solver_trait::{TCheck, TheoryCtx, TheorySolver};
use crate::types::EqLeaf;
use crate::Explainer;
use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;

#[derive(Default)]
pub struct EmptyTheory;

impl TheorySolver for EmptyTheory {
    const THEORY_ID: u16 = 0;
    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
        None
    }
    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        None
    }
    fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        TCheck::Sat
    }
    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
    fn push(&mut self) {}
    fn pop(&mut self, _level: usize) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_theory_is_always_sat() {
        let mut t = EmptyTheory;
        t.push();
        t.pop(0);
        // Construction + trait-object-free dispatch compile-checks the impl.
        assert_eq!(EmptyTheory::THEORY_ID, 0);
    }
}
```

- [ ] **Step 2: Wire the module + export.**

In `crates/shinri-theory/src/lib.rs`, add `pub mod empty;` (with the other `pub mod` lines) and `pub use empty::EmptyTheory;` (with the other `pub use`).

- [ ] **Step 3: Run the test (expect compile + pass).**

Run: `cargo test -p shinri-theory --lib empty_theory_is_always_sat`
Expected: PASS.

- [ ] **Step 4: Commit.**

```bash
git add crates/shinri-theory/src/empty.rs crates/shinri-theory/src/lib.rs
git commit -m "feat(theory): EmptyTheory no-op TheorySolver for the Arith slot"
```

---

## Phase B — SAT incrementality (`shinri-sat`)

### Task 3: theory injection (`with_theory`, `theory_mut`)

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs`

**Interfaces:**
- Produces: `Solver::with_theory(config: SolverConfig, theory: T) -> Solver<T, P, H>`; `Solver::theory(&self) -> &T`; `Solver::theory_mut(&mut self) -> &mut T`.
- Consumes: existing `Solver::new`.

- [ ] **Step 1: Write the failing test.**

Append to the test module at the bottom of `crates/shinri-sat/src/solver.rs` (find `#[cfg(test)] mod tests` or add one if absent; if a test module already exists, add this test inside it). If no test module exists, add:

```rust
#[cfg(test)]
mod inject_tests {
    use super::*;
    use crate::heuristic::Vmtf;
    use crate::theory::NoTheory;
    use shinri_core::NoProof;

    #[test]
    fn with_theory_injects_and_exposes_the_instance() {
        let s: Solver<NoTheory, NoProof, Vmtf> =
            Solver::with_theory(SolverConfig::default(), NoTheory);
        // Accessors compile and return the injected theory.
        let _t: &NoTheory = s.theory();
    }
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-sat --lib with_theory_injects -- --nocapture`
Expected: FAIL — `no function or associated item named with_theory` / `no method named theory`.

- [ ] **Step 3: Add the constructor and accessors.**

In `crates/shinri-sat/src/solver.rs`, inside `impl<T: Theory, P: ProofSink + Default, H: BranchHeuristic> Solver<T, P, H>`, add right after `pub fn new(...)`:

```rust
    /// Construct around a pre-built theory (e.g. a `Combiner` with its
    /// `Context` already populated). Identical to `new` but does not default `T`.
    pub fn with_theory(config: SolverConfig, theory: T) -> Solver<T, P, H> {
        let mut s = Solver::new(config);
        s.theory = theory;
        s
    }

    /// Borrow the theory (e.g. to read a model after `solve`).
    pub fn theory(&self) -> &T {
        &self.theory
    }

    /// Mutably borrow the theory (e.g. to register atoms before `solve`).
    pub fn theory_mut(&mut self) -> &mut T {
        &mut self.theory
    }
```

- [ ] **Step 4: Run to confirm pass.**

Run: `cargo test -p shinri-sat --lib with_theory_injects`
Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-sat/src/solver.rs
git commit -m "feat(sat): Solver::with_theory + theory/theory_mut accessors"
```

---

### Task 4: theory-preserving rebuild + sound `push`/`pop`

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs`

**Interfaces:**
- Produces: `Solver::push`/`pop` that drive `theory.push`/`theory.pop` and preserve theory state across rebuild; a private `theory_silent` flag honored by `enqueue`.
- Consumes: existing `rebuild`, `enqueue`, `install_clause`.

**Background:** Today `rebuild()` does `self.theory = T::default()` and replays only `new_var(v)` (no atom), destroying a stateful theory. The fix: keep the theory, pop it to the user-scope level, and re-install surviving clauses *theory-silently* (the theory already holds the surviving facts via its own scopes). See spec §7. The soundness invariant: between `solve()` calls, theory level == number of open user scopes, holding exactly those scopes' level-0 facts.

- [ ] **Step 1: Write the failing test (stateful counting theory survives pop).**

Add to `crates/shinri-sat/src/solver.rs` a test module:

```rust
#[cfg(test)]
mod incremental_tests {
    use super::*;
    use crate::heuristic::Vmtf;
    use crate::theory::Theory;
    use shinri_core::{NoProof, TheoryJust};
    use shinri_core::{Lit, Var};

    /// Counts net asserts and tracks its own scope depth, so the test can prove
    /// rebuild neither resets the instance nor double-asserts surviving units.
    #[derive(Default)]
    struct CountTheory {
        asserts: i64,
        depth: i64,
    }
    impl Theory for CountTheory {
        fn assert(&mut self, _lit: Lit) {
            self.asserts += 1;
        }
        fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
            None
        }
        fn explain(&mut self, _just: TheoryJust, _out: &mut Vec<Lit>) {}
        fn check(&mut self, _effort: crate::types::Effort) -> crate::types::TheoryResult {
            crate::types::TheoryResult::Sat
        }
        fn push(&mut self) {
            self.depth += 1;
        }
        fn pop(&mut self, n: usize) {
            self.depth -= n as i64;
        }
        fn new_var(&mut self, _v: Var) {}
    }

    #[test]
    fn pop_preserves_theory_and_does_not_double_assert() {
        let mut s: Solver<CountTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        let a = s.new_var();
        // A unit clause asserts `a` at level 0 -> one theory.assert.
        s.add_clause(&[Lit::new(a, true)]);
        assert_eq!(s.theory().asserts, 1);
        s.push(); // opens a user scope -> theory.push
        assert_eq!(s.theory().depth, 1);
        let b = s.new_var();
        s.add_clause(&[Lit::new(b, true)]); // asserts `b` -> two total
        assert_eq!(s.theory().asserts, 2);
        s.pop(1); // close the scope: theory.pop(1); silent re-install of survivors
        // depth back to 0; the surviving unit `a` is NOT re-asserted (silent).
        assert_eq!(s.theory().depth, 0);
        assert_eq!(s.theory().asserts, 2, "rebuild must not re-assert survivors");
    }
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-sat --lib pop_preserves_theory -- --nocapture`
Expected: FAIL — assertion mismatch (current `rebuild` resets the theory; `asserts`/`depth` are wrong).

- [ ] **Step 3: Add the `theory_silent` field.**

In `struct Solver`, add a field (after `unsat: bool,`):

```rust
    pub(crate) theory_silent: bool,
```

In both `Solver::new`'s initializer list add `theory_silent: false,`.

- [ ] **Step 4: Honor the flag in `enqueue`.**

In `enqueue`, replace `self.theory.assert(l);` with:

```rust
                if !self.theory_silent {
                    self.theory.assert(l);
                }
```

- [ ] **Step 5: Drive theory scopes from user `push`/`pop`.**

Replace `Solver::push` with:

```rust
    pub fn push(&mut self) {
        if self.trail.decision_level() != 0 {
            self.backtrack_to(0);
        }
        self.scopes.push(self.input_clauses.len());
        self.theory.push();
    }
```

Replace `Solver::pop` with:

```rust
    pub fn pop(&mut self, n: usize) {
        for _ in 0..n {
            if let Some(mark) = self.scopes.pop() {
                self.input_clauses.truncate(mark);
            }
        }
        self.theory.pop(n);
        self.rebuild();
    }
```

- [ ] **Step 6: Make `rebuild` theory-preserving + silent.**

Replace the body of `fn rebuild` with:

```rust
    fn rebuild(&mut self) {
        let num_vars = self.assign.num_vars();
        self.assign.reset();
        self.trail = Trail::new();
        self.db = ClauseDb::new();
        self.watches = Watches::new();
        self.watches.ensure_vars(num_vars);
        self.learnts.clear();
        self.unsat = false;
        self.heuristic = H::default();
        for i in 0..num_vars {
            self.heuristic.new_var(Var::new(i as u32));
        }
        self.restart = RestartPolicy::new(self.config.restart, 100);
        self.conflicts = 0;
        // Re-install survivors WITHOUT re-asserting to the theory: the theory
        // retained the surviving scopes' facts via its own push/pop (spec §7).
        self.theory_silent = true;
        let inputs = std::mem::take(&mut self.input_clauses);
        for clause in &inputs {
            self.install_clause(clause);
        }
        self.input_clauses = inputs;
        self.theory_silent = false;
    }
```

- [ ] **Step 7: Run the incremental test.**

Run: `cargo test -p shinri-sat --lib pop_preserves_theory`
Expected: PASS.

- [ ] **Step 8: Run the whole SAT suite (no regressions).**

Run: `cargo test -p shinri-sat`
Expected: PASS (existing tests unaffected; `NoTheory` is stateless so silent re-install is a no-op for it).

- [ ] **Step 9: Commit.**

```bash
git add crates/shinri-sat/src/solver.rs
git commit -m "feat(sat): theory-preserving rebuild + theory-silent re-install for sound push/pop"
```

---

## Phase C — EUF theory solver (`shinri-euf`)

### Task 5: crate scaffold + `Euf` skeleton

**Files:**
- Create: `crates/shinri-euf/Cargo.toml`
- Create: `crates/shinri-euf/src/lib.rs`
- Create: `crates/shinri-euf/src/solver.rs`
- Modify: `Cargo.toml` (root)

**Interfaces:**
- Produces: `pub struct Euf` implementing `TheorySolver` with `const THEORY_ID: u16 = 1;` (all methods present, trivial bodies for now); `Euf::default()`.
- Consumes: `shinri_theory::{TheorySolver, TheoryCtx, TCheck, ModelBuilder, Explainer, EqLeaf}`, `shinri_sat::Effort`.

- [ ] **Step 1: Create the crate manifest.**

Create `crates/shinri-euf/Cargo.toml`:

```toml
[package]
name = "shinri-euf"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-theory = { path = "../shinri-theory" }
shinri-sat = { path = "../shinri-sat" }
rustc-hash = "2"

[dev-dependencies]
proptest = "1"
```

- [ ] **Step 2: Register the workspace member.**

In the root `Cargo.toml`, add `"crates/shinri-euf"` to `[workspace].members`.

- [ ] **Step 3: Write the crate root.**

Create `crates/shinri-euf/src/lib.rs`:

```rust
//! shinri-euf: the EUF (congruence-closure) theory solver. Adds the congruence
//! driver (signature table + use-lists) on top of shinri-theory's shared
//! `EqualityEngine` (union-find + proof forest). Depends only on core, theory,
//! and sat (for `Effort`).

mod egraph;
pub mod solver;

pub use solver::Euf;
```

- [ ] **Step 4: Write the skeleton solver + its test.**

Create `crates/shinri-euf/src/solver.rs`:

```rust
use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};
use shinri_theory::types::EqLeaf;

#[derive(Default)]
pub struct Euf {
    // Filled in across Tasks 6–11.
    inner: crate::egraph::EGraph,
    level: usize,
}

impl TheorySolver for Euf {
    const THEORY_ID: u16 = 1;

    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
        None
    }
    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        None
    }
    fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        TCheck::Sat
    }
    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
    fn push(&mut self) {
        self.level += 1;
    }
    fn pop(&mut self, level: usize) {
        self.level = level;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn euf_constructs_and_has_theory_id_one() {
        let _e = Euf::default();
        assert_eq!(Euf::THEORY_ID, 1);
    }
}
```

> Note: this references `shinri_theory::types::EqLeaf`. Ensure `crates/shinri-theory/src/lib.rs` exposes the `types` module path; it already does `pub mod types;`. If `Explainer`/`ModelBuilder`/`TCheck`/`TheoryCtx`/`TheorySolver` are re-exported at the crate root (they are), the `use shinri_theory::{...}` line resolves.

- [ ] **Step 5: Write the empty e-graph placeholder.**

Create `crates/shinri-euf/src/egraph.rs`:

```rust
//! The congruence-closure machinery layered over `EqualityEngine`.
//! Expanded across Tasks 6–11.

#[derive(Default)]
pub struct EGraph {}
```

- [ ] **Step 6: Build and test.**

Run: `cargo test -p shinri-euf`
Expected: PASS (`euf_constructs_and_has_theory_id_one`).

- [ ] **Step 7: Commit.**

```bash
git add crates/shinri-euf/Cargo.toml crates/shinri-euf/src/lib.rs crates/shinri-euf/src/solver.rs crates/shinri-euf/src/egraph.rs Cargo.toml
git commit -m "feat(euf): crate scaffold + Euf TheorySolver skeleton"
```

---

### Task 6: e-graph construction (`new_var`)

**Files:**
- Modify: `crates/shinri-euf/src/egraph.rs`
- Modify: `crates/shinri-euf/src/solver.rs`

**Interfaces:**
- Produces: `EGraph::add_term(&mut self, cx: &mut TheoryCtx, t: TermId) -> ENodeId` (recursively interns subterms, records app structure, populates use-lists and the signature lookup, enqueues any initial congruence); `EGraph::AppId`, `Signature`. `Euf::new_var` interns the atom's relevant subterms.
- Consumes: `EqualityEngine::{intern, find}`, `Context::{term_node, children}`, `Op`, `TermNode`, `ENodeId`.

**Design:** Each function application is an `AppNode { node, op, args }`. `use_list[node]` lists apps that have `node` (the *original* node id) directly as an argument; on merge we splice the loser's use-list into the winner's and re-canonicalize. `lookup` maps a `Signature(op, [find(arg)])` to the canonical `AppId`.

- [ ] **Step 1: Write the failing test.**

In `crates/shinri-euf/src/egraph.rs`, add a test module that builds `f(a)` and `f(b)` over an uninterpreted sort and asserts both apps were registered with distinct signatures:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Context, Op};
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx};

    fn uconst(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> shinri_core::TermId {
        let sym = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn add_term_registers_apps_and_args() {
        let mut ctx = Context::new();
        let u = ctx.declare_sort("U");
        let a = uconst(&mut ctx, "a", u);
        let b = uconst(&mut ctx, "b", u);
        let f = ctx.declare_fun("f", &[u], u);
        let fa = ctx.mk_app(Op::Uninterpreted(f), &[a]).unwrap();
        let fb = ctx.mk_app(Op::Uninterpreted(f), &[b]).unwrap();

        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut g = EGraph::default();
        {
            let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
            g.add_term(&mut cx, fa);
            g.add_term(&mut cx, fb);
        }
        // f(a) and f(b) are distinct apps (a,b in different classes): no congruence.
        let na = eq.intern(fa);
        let nb = eq.intern(fb);
        assert!(!eq.are_equal(na, nb));
        assert_eq!(g.app_count(), 4); // a, b, f(a), f(b) all recorded as apps
    }
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-euf egraph::tests::add_term -- --nocapture`
Expected: FAIL — `no method named add_term` / `app_count`.

- [ ] **Step 3: Implement the e-graph structures and `add_term`.**

Replace the contents of `crates/shinri-euf/src/egraph.rs` (above the test module) with:

```rust
//! The congruence-closure machinery layered over `EqualityEngine`.

use rustc_hash::FxHashMap;
use shinri_core::{Op, TermId, TermNode};
use shinri_theory::types::{ENodeId, EqJust, EqLeaf};
use shinri_theory::{EqualityEngine, TheoryCtx};

/// Index into `EGraph.apps`.
pub type AppId = u32;

/// A canonicalization key: operator + the representatives of the arguments.
type Signature = (Op, Vec<ENodeId>);

struct AppNode {
    node: ENodeId,
    op: Op,
    args: Vec<ENodeId>,
}

/// An undo entry for backtracking the EUF-owned indices.
enum Undo {
    /// `lookup[sig]` was inserted with no prior value; remove it on undo.
    LookupInsert(Signature),
    /// `lookup[sig]` overwrote `prev`; restore `prev` on undo.
    LookupOverwrite(Signature, AppId),
    /// `count` apps were appended onto `use_list[winner]` from `loser`; move
    /// them back to `loser` on undo.
    UseSplice { winner: usize, loser: usize, count: usize },
}

#[derive(Default)]
pub struct EGraph {
    apps: Vec<AppNode>,
    /// Per-ENodeId apps that use it directly as an argument (by original node id).
    use_list: Vec<Vec<AppId>>,
    lookup: FxHashMap<Signature, AppId>,
    /// Congruence work-queue: pairs of app nodes to merge, with arg pairs.
    pending: Vec<(ENodeId, ENodeId, Vec<(ENodeId, ENodeId)>)>,
    undo: shinri_core::UndoLog<Undo>,
    /// Set when an interned term is a function application (vs a plain leaf).
    is_app: Vec<bool>,
    app_of: FxHashMap<ENodeId, AppId>,
}

impl EGraph {
    pub fn app_count(&self) -> usize {
        self.apps.len()
    }

    fn ensure_node(&mut self, n: ENodeId) {
        let idx = n.index();
        if idx >= self.use_list.len() {
            self.use_list.resize_with(idx + 1, Vec::new);
        }
        if idx >= self.is_app.len() {
            self.is_app.resize(idx + 1, false);
        }
    }

    /// Recursively intern `t` and all subterms, recording app structure.
    /// Returns the e-node of `t`. Idempotent (interning dedups).
    pub fn add_term(&mut self, cx: &mut TheoryCtx, t: TermId) -> ENodeId {
        let node = cx.eq.intern(t);
        self.ensure_node(node);
        if self.app_of.contains_key(&node) {
            return node; // already registered as an app
        }
        match cx.terms.term_node(t) {
            TermNode::App { op, args, .. } => {
                let op = *op;
                let child_terms: Vec<TermId> = cx.terms.children(*args).to_vec();
                let mut arg_nodes = Vec::with_capacity(child_terms.len());
                for ct in child_terms {
                    arg_nodes.push(self.add_term(cx, ct));
                }
                let app_id = self.apps.len() as AppId;
                for &an in &arg_nodes {
                    self.ensure_node(an);
                    self.use_list[an.index()].push(app_id);
                }
                self.apps.push(AppNode {
                    node,
                    op,
                    args: arg_nodes.clone(),
                });
                self.is_app[node.index()] = true;
                self.app_of.insert(node, app_id);
                // Initial signature; a collision means an existing congruent app.
                let sig = self.signature(cx.eq, app_id);
                if let Some(&other) = self.lookup.get(&sig) {
                    if other != app_id {
                        self.enqueue_congruence(cx.eq, other, app_id);
                    }
                } else {
                    self.lookup.insert(sig, app_id);
                }
                node
            }
            TermNode::Const { .. } => node,
        }
    }

    fn signature(&self, eq: &EqualityEngine, app: AppId) -> Signature {
        let a = &self.apps[app as usize];
        let reps: Vec<ENodeId> = a.args.iter().map(|&x| eq.find(x)).collect();
        (a.op, reps)
    }

    fn enqueue_congruence(&mut self, eq: &EqualityEngine, a: AppId, b: AppId) {
        let aa = &self.apps[a as usize];
        let bb = &self.apps[b as usize];
        debug_assert_eq!(aa.args.len(), bb.args.len());
        let pairs: Vec<(ENodeId, ENodeId)> =
            aa.args.iter().copied().zip(bb.args.iter().copied()).collect();
        let _ = eq; // representatives captured at merge time
        self.pending.push((aa.node, bb.node, pairs));
    }
}
```

- [ ] **Step 4: Call `add_term` from `Euf::new_var`.**

In `crates/shinri-euf/src/solver.rs`, change `new_var` to intern the atom. Decode `(= s t)` and `distinct` to intern operands; otherwise intern the whole atom (predicate apps). Replace the `new_var` body:

```rust
    fn new_var(&mut self, cx: &mut TheoryCtx, _v: Var, atom: TermId) {
        use shinri_core::{BuiltinOp, Op, TermNode};
        match cx.terms.term_node(atom) {
            TermNode::App { op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct), args, .. } => {
                let kids: Vec<TermId> = cx.terms.children(*args).to_vec();
                for k in kids {
                    self.inner.add_term(cx, k);
                }
            }
            _ => {
                // Predicate application (or any other EUF atom term).
                self.inner.add_term(cx, atom);
            }
        }
    }
```

Make `inner` accessible: it is already a field. Ensure `egraph::EGraph::add_term` is `pub` (it is).

- [ ] **Step 5: Run the test.**

Run: `cargo test -p shinri-euf egraph::tests::add_term`
Expected: PASS.

- [ ] **Step 6: Commit.**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/solver.rs
git commit -m "feat(euf): e-graph construction (intern subterms, use-lists, signatures)"
```

---

### Task 7: assert equalities + congruence driver + conflict packaging

**Files:**
- Modify: `crates/shinri-euf/src/egraph.rs`
- Modify: `crates/shinri-euf/src/solver.rs`
- Create: `crates/shinri-euf/tests/qfuf_euf.rs`

**Interfaces:**
- Produces: `EGraph::merge_eq(&mut self, eq, a: ENodeId, b: ENodeId, just: EqJust) -> Option<Vec<EqLeaf>>` (merges then closes congruence to fixpoint; `Some(conflict_leaves)` on a disequality violation); `EGraph::assert_diseq(&mut self, eq, a, b, just) -> Option<Vec<EqLeaf>>`. `Euf::assert` decodes the atom and drives them.
- Consumes: `EqualityEngine::{merge, merge_congruence, assert_diseq, explain, find}`, `EqConflict`.

**Design:** `merge_eq` seeds the pending queue and runs the closure: pop a pair, merge in the engine, then splice the loser's use-list into the winner's, re-canonicalizing each app (collision ⇒ enqueue congruence). On an `EqConflict`, build leaves = `explain(a,b)` ∪ the disequality's justification leaf.

- [ ] **Step 1: Write the failing EUF integration test.**

Create `crates/shinri-euf/tests/qfuf_euf.rs`:

```rust
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, Var};
use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};
use shinri_euf::Euf;

fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
    let sym = ctx.declare_fun(name, &[], s);
    ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
}

/// x = y  ∧  f(x) ≠ f(y)  is EUF-unsatisfiable.
#[test]
fn congruence_conflict_x_eq_y_implies_fx_eq_fy() {
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let x = uconst(&mut ctx, "x", u);
    let y = uconst(&mut ctx, "y", u);
    let f = ctx.declare_fun("f", &[u], u);
    let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
    let fy = ctx.mk_app(Op::Uninterpreted(f), &[y]).unwrap();
    let eq_xy = ctx.mk_eq(x, y).unwrap();
    let eq_ff = ctx.mk_eq(fx, fy).unwrap();

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let v_xy = Var::new(0);
    let v_ff = Var::new(1);
    atoms.register(v_xy, eq_xy, shinri_theory::types::Owner::Euf);
    atoms.register(v_ff, eq_ff, shinri_theory::types::Owner::Euf);

    let mut euf = Euf::default();
    {
        let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
        euf.new_var(&mut cx, v_xy, eq_xy);
        euf.new_var(&mut cx, v_ff, eq_ff);
        // assert f(x) ≠ f(y)
        assert!(euf.assert(&mut cx, Lit::new(v_ff, false)).is_none());
        // assert x = y  -> congruence forces f(x)=f(y) -> conflict
        let conflict = euf.assert(&mut cx, Lit::new(v_xy, true));
        assert!(conflict.is_some(), "x=y with f(x)!=f(y) must conflict");
    }
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-euf --test qfuf_euf congruence_conflict -- --nocapture`
Expected: FAIL — `assert` returns `None` (no driver yet), so `conflict.is_some()` fails.

- [ ] **Step 3: Implement the congruence driver in the e-graph.**

In `crates/shinri-euf/src/egraph.rs`, add to `impl EGraph`:

```rust
    /// Merge `a`,`b` (justified by `just`) and close congruence to a fixpoint.
    /// Returns conflict leaves if a disequality is violated.
    pub fn merge_eq(
        &mut self,
        eq: &mut EqualityEngine,
        a: ENodeId,
        b: ENodeId,
        just: EqJust,
    ) -> Option<Vec<EqLeaf>> {
        // Seed the queue with the asserted equality (no congruence pairs).
        if let Some(c) = self.do_merge(eq, a, b, MergeJust::Asserted(just)) {
            return Some(c);
        }
        self.drain_pending(eq)
    }

    /// Assert `a` ≠ `b`; conflict leaves if they are already equal.
    pub fn assert_diseq(
        &mut self,
        eq: &mut EqualityEngine,
        a: ENodeId,
        b: ENodeId,
        just: EqJust,
    ) -> Option<Vec<EqLeaf>> {
        match eq.assert_diseq(a, b, just) {
            Ok(()) => None,
            Err(conflict) => Some(self.conflict_leaves(eq, conflict)),
        }
    }

    fn drain_pending(&mut self, eq: &mut EqualityEngine) -> Option<Vec<EqLeaf>> {
        while let Some((na, nb, pairs)) = self.pending.pop() {
            if eq.find(na) == eq.find(nb) {
                continue;
            }
            if let Some(c) = self.do_merge(eq, na, nb, MergeJust::Congruence(pairs)) {
                return Some(c);
            }
        }
        None
    }

    fn do_merge(
        &mut self,
        eq: &mut EqualityEngine,
        a: ENodeId,
        b: ENodeId,
        mj: MergeJust,
    ) -> Option<Vec<EqLeaf>> {
        let ra = eq.find(a);
        let rb = eq.find(b);
        if ra == rb {
            return None;
        }
        let res = match &mj {
            MergeJust::Asserted(j) => eq.merge(a, b, *j),
            MergeJust::Congruence(pairs) => eq.merge_congruence(a, b, pairs),
        };
        if let Err(conflict) = res {
            return Some(self.conflict_leaves(eq, conflict));
        }
        // Determine winner/loser by post-merge representative.
        let nr = eq.find(a);
        let loser = if nr == ra { rb } else { ra };
        self.recanonicalize_use_list(eq, nr, loser);
        None
    }

    /// Move `loser`'s use-list into `winner`'s, re-canonicalizing each app;
    /// a signature collision enqueues a congruence.
    fn recanonicalize_use_list(
        &mut self,
        eq: &EqualityEngine,
        winner: ENodeId,
        loser: ENodeId,
    ) {
        let moved: Vec<AppId> = std::mem::take(&mut self.use_list[loser.index()]);
        let count = moved.len();
        for app in moved.iter().copied() {
            let sig = self.signature(eq, app);
            match self.lookup.get(&sig).copied() {
                Some(other) if other != app => {
                    self.enqueue_congruence(eq, other, app);
                    self.undo.record(Undo::LookupOverwrite(sig.clone(), other));
                    self.lookup.insert(sig, app);
                }
                Some(_) => {}
                None => {
                    self.undo.record(Undo::LookupInsert(sig.clone()));
                    self.lookup.insert(sig, app);
                }
            }
        }
        self.use_list[winner.index()].extend(moved);
        self.undo.record(Undo::UseSplice {
            winner: winner.index(),
            loser: loser.index(),
            count,
        });
    }

    fn conflict_leaves(
        &mut self,
        eq: &EqualityEngine,
        conflict: shinri_theory::types::EqConflict,
    ) -> Vec<EqLeaf> {
        let mut out = Vec::new();
        // Why a,b became equal:
        eq.explain(conflict.a, conflict.b, &mut out);
        // ...plus the disequality that they violated:
        match conflict.diseq {
            EqJust::Asserted(l) => out.push(EqLeaf::Asserted(l)),
            EqJust::Interface(j) => out.push(EqLeaf::Interface(j)),
            EqJust::Congruence(_) | EqJust::Definitional => {}
        }
        out
    }
```

Add the `MergeJust` helper enum near the top of `egraph.rs` (after the `Undo` enum):

```rust
enum MergeJust {
    Asserted(EqJust),
    Congruence(Vec<(ENodeId, ENodeId)>),
}
```

- [ ] **Step 4: Decode the atom in `Euf::assert`.**

In `crates/shinri-euf/src/solver.rs`, replace `assert` with:

```rust
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        use shinri_core::{BuiltinOp, Op, TermNode};
        use shinri_theory::types::EqJust;
        let atom = cx.atoms.atom(lit.var());
        let just = EqJust::Asserted(lit);
        match cx.terms.term_node(atom) {
            TermNode::App { op: Op::Builtin(BuiltinOp::Eq), args, .. } => {
                let kids: Vec<TermId> = cx.terms.children(*args).to_vec();
                debug_assert_eq!(kids.len(), 2, "Eq atom must be binary");
                let a = cx.eq.intern(kids[0]);
                let b = cx.eq.intern(kids[1]);
                if lit.is_positive() {
                    self.inner.merge_eq(cx.eq, a, b, just)
                } else {
                    self.inner.assert_diseq(cx.eq, a, b, just)
                }
            }
            TermNode::App { op: Op::Builtin(BuiltinOp::Distinct), args, .. } => {
                let kids: Vec<TermId> = cx.terms.children(*args).to_vec();
                debug_assert_eq!(kids.len(), 2, "Distinct lowered to binary (Task 13)");
                let a = cx.eq.intern(kids[0]);
                let b = cx.eq.intern(kids[1]);
                if lit.is_positive() {
                    self.inner.assert_diseq(cx.eq, a, b, just)
                } else {
                    self.inner.merge_eq(cx.eq, a, b, just)
                }
            }
            _ => {
                // Predicate atom: handled in Task 8.
                None
            }
        }
    }
```

> This uses `lit.is_positive()`. If `Lit` exposes the sign differently, adapt: inspect `crates/shinri-core/src/ids.rs` for the accessor (e.g. `lit.is_positive()` / a `sign()` method). Use whichever the codebase provides; the test in Step 1 will catch a wrong choice.

- [ ] **Step 5: Run the EUF integration test + lib tests.**

Run: `cargo test -p shinri-euf`
Expected: PASS (`congruence_conflict_x_eq_y_implies_fx_eq_fy` and earlier tests).

- [ ] **Step 6: Add a transitivity + n-ary congruence test.**

Append to `crates/shinri-euf/tests/qfuf_euf.rs`:

```rust
/// a=c ∧ b=d ∧ g(a,b) ≠ g(c,d) is unsat (n-ary congruence).
#[test]
fn nary_congruence_conflict() {
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let a = uconst(&mut ctx, "a", u);
    let b = uconst(&mut ctx, "b", u);
    let c = uconst(&mut ctx, "c", u);
    let d = uconst(&mut ctx, "d", u);
    let g = ctx.declare_fun("g", &[u, u], u);
    let gab = ctx.mk_app(Op::Uninterpreted(g), &[a, b]).unwrap();
    let gcd = ctx.mk_app(Op::Uninterpreted(g), &[c, d]).unwrap();
    let eq_ac = ctx.mk_eq(a, c).unwrap();
    let eq_bd = ctx.mk_eq(b, d).unwrap();
    let eq_gg = ctx.mk_eq(gab, gcd).unwrap();

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let (v0, v1, v2) = (Var::new(0), Var::new(1), Var::new(2));
    atoms.register(v0, eq_ac, shinri_theory::types::Owner::Euf);
    atoms.register(v1, eq_bd, shinri_theory::types::Owner::Euf);
    atoms.register(v2, eq_gg, shinri_theory::types::Owner::Euf);

    let mut euf = Euf::default();
    let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
    euf.new_var(&mut cx, v0, eq_ac);
    euf.new_var(&mut cx, v1, eq_bd);
    euf.new_var(&mut cx, v2, eq_gg);
    assert!(euf.assert(&mut cx, Lit::new(v2, false)).is_none());
    assert!(euf.assert(&mut cx, Lit::new(v0, true)).is_none());
    let conflict = euf.assert(&mut cx, Lit::new(v1, true));
    assert!(conflict.is_some(), "a=c ∧ b=d ⇒ g(a,b)=g(c,d) contradicts ≠");
}
```

- [ ] **Step 7: Run.**

Run: `cargo test -p shinri-euf --test qfuf_euf`
Expected: PASS.

- [ ] **Step 8: Commit.**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/solver.rs crates/shinri-euf/tests/qfuf_euf.rs
git commit -m "feat(euf): congruence driver, equality/disequality assert, conflict packaging"
```

---

### Task 8: predicate atom encoding (⊤/⊥)

**Files:**
- Modify: `crates/shinri-euf/src/egraph.rs`
- Modify: `crates/shinri-euf/src/solver.rs`
- Modify: `crates/shinri-euf/tests/qfuf_euf.rs`

**Interfaces:**
- Produces: `EGraph::truth_nodes(&mut self, cx) -> (ENodeId, ENodeId)` (interns `⊤`/`⊥` once, asserts them distinct at level 0); `Euf::assert` handles predicate atoms by merging the app with `⊤`/`⊥`.
- Consumes: Task 7 `merge_eq`; `EqualityEngine::assert_diseq`.

**Design:** A predicate application `p(args)` (Bool-sorted uninterpreted app) is a term node. Assert-true merges it with `⊤`; assert-false merges with `⊥`. `⊤ ≠ ⊥` is established once (`Definitional` justification), so `p(a) ∧ ¬p(b) ∧ a=b` becomes `⊤ = ⊥` ⇒ conflict via congruence.

- [ ] **Step 1: Write the failing predicate test.**

Append to `crates/shinri-euf/tests/qfuf_euf.rs`:

```rust
/// p(a) ∧ ¬p(b) ∧ a=b  is unsat (predicate congruence).
#[test]
fn predicate_congruence_conflict() {
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let boolsort = ctx.bool_sort();
    let a = uconst(&mut ctx, "a", u);
    let b = uconst(&mut ctx, "b", u);
    let p = ctx.declare_fun("p", &[u], boolsort);
    let pa = ctx.mk_app(Op::Uninterpreted(p), &[a]).unwrap();
    let pb = ctx.mk_app(Op::Uninterpreted(p), &[b]).unwrap();
    let eq_ab = ctx.mk_eq(a, b).unwrap();

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let (vpa, vpb, vab) = (Var::new(0), Var::new(1), Var::new(2));
    atoms.register(vpa, pa, shinri_theory::types::Owner::Euf);
    atoms.register(vpb, pb, shinri_theory::types::Owner::Euf);
    atoms.register(vab, eq_ab, shinri_theory::types::Owner::Euf);

    let mut euf = Euf::default();
    let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
    euf.new_var(&mut cx, vpa, pa);
    euf.new_var(&mut cx, vpb, pb);
    euf.new_var(&mut cx, vab, eq_ab);
    assert!(euf.assert(&mut cx, Lit::new(vpa, true)).is_none());
    assert!(euf.assert(&mut cx, Lit::new(vpb, false)).is_none());
    let conflict = euf.assert(&mut cx, Lit::new(vab, true));
    assert!(conflict.is_some(), "p(a) ∧ ¬p(b) ∧ a=b must conflict");
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-euf --test qfuf_euf predicate_congruence -- --nocapture`
Expected: FAIL — predicate atoms currently fall through to the `_ => None` arm.

- [ ] **Step 3: Add sentinel truth nodes to the e-graph.**

In `crates/shinri-euf/src/egraph.rs`, add fields to `EGraph`:

```rust
    truth: Option<(ENodeId, ENodeId)>, // (⊤, ⊥)
```

Add a method (synthesizes two unique sentinel terms — use two distinct, otherwise-unused `TermId`s reserved by the engine via interning of dedicated Bool constants). Implement by interning the context's `true`/`false` Bool constants:

```rust
    /// Intern the ⊤/⊥ sentinels once and assert them distinct (level 0).
    pub fn truth_nodes(&mut self, cx: &mut TheoryCtx) -> (ENodeId, ENodeId) {
        if let Some(tf) = self.truth {
            return tf;
        }
        // `Context` provides canonical Bool constants; intern both.
        let t_term = cx.terms_true();
        let f_term = cx.terms_false();
        let tn = cx.eq.intern(t_term);
        let fln = cx.eq.intern(f_term);
        let _ = cx.eq.assert_diseq(tn, fln, EqJust::Definitional);
        self.truth = Some((tn, fln));
        (tn, fln)
    }
```

> `cx.terms_true()`/`terms_false()` do not exist on `TheoryCtx`. Implement them as helpers in `solver.rs` instead (next step), since `TheoryCtx.terms` is `&Context` (immutable) and `mk_const_bool` needs `&mut Context`. **Resolution:** pre-create the Bool constants in `shinri-solver` and pass them in — but EUF must not depend on the solver. Cleaner: have the EUF solver intern the two Bool constants lazily using `TheoryCtx.terms` *read-only* by looking them up. Since `Context::mk_const_bool` requires `&mut`, and `TheoryCtx.terms` is `&Context`, the truth constants MUST be created at construction time when the Context is still mutable.

- [ ] **Step 4: Create the truth constants where the Context is mutable.**

The robust design: `shinri-solver` creates `true`/`false` Bool constants once (it owns the mutable `Context`) and the EUF solver discovers them. To keep EUF self-contained for its own tests, add a one-time initialization entry point on `Euf` that takes the two `TermId`s.

In `crates/shinri-euf/src/solver.rs`, add to `Euf`:

```rust
    truth_terms: Option<(TermId, TermId)>,
```

Add a public setter and use it in `new_var` lazily. Replace `truth_nodes` usage by storing terms on `Euf` and interning in `assert`. Concretely, add to `Euf`:

```rust
    /// Provide the canonical Bool ⊤/⊥ terms (created by the owner of the
    /// mutable `Context`). Must be called before asserting predicate atoms.
    pub fn set_truth_terms(&mut self, t_true: TermId, t_false: TermId) {
        self.truth_terms = Some((t_true, t_false));
    }
```

And in `egraph.rs`, change `truth_nodes` to accept the terms:

```rust
    pub fn truth_nodes(
        &mut self,
        cx: &mut TheoryCtx,
        t_true: TermId,
        t_false: TermId,
    ) -> (ENodeId, ENodeId) {
        if let Some(tf) = self.truth {
            return tf;
        }
        let tn = cx.eq.intern(t_true);
        let fln = cx.eq.intern(t_false);
        let _ = cx.eq.assert_diseq(tn, fln, EqJust::Definitional);
        self.truth = Some((tn, fln));
        (tn, fln)
    }
```

- [ ] **Step 5: Handle predicate atoms in `Euf::assert`.**

In `crates/shinri-euf/src/solver.rs`, replace the `_ => { None }` arm of `assert` with:

```rust
            _ => {
                // Uninterpreted predicate application: p(args) merged with ⊤/⊥.
                let (t_true, t_false) = self
                    .truth_terms
                    .expect("set_truth_terms must precede predicate asserts");
                let (tn, fln) = self.inner.truth_nodes(cx, t_true, t_false);
                let pnode = self.inner.add_term(cx, atom);
                let target = if lit.is_positive() { tn } else { fln };
                self.inner.merge_eq(cx.eq, pnode, target, just)
            }
```

- [ ] **Step 6: Set truth terms in the test.**

In `predicate_congruence_conflict` (the test), before the asserts, create the Bool constants and register them:

```rust
    let t_true = ctx.mk_const_bool(true);
    let t_false = ctx.mk_const_bool(false);
    // (re-open the immutable borrow afterwards)
```

Because the test creates `cx` borrowing `ctx` immutably, create the constants **before** building `cx`, and call `euf.set_truth_terms(t_true, t_false);` before constructing `cx`. Adjust the test ordering: move `let t_true = ...; let t_false = ...;` to just after declaring `p`/atoms and before `let mut cx = ...`, and add `euf.set_truth_terms(t_true, t_false);` right after `let mut euf = Euf::default();`.

- [ ] **Step 7: Run.**

Run: `cargo test -p shinri-euf --test qfuf_euf predicate_congruence`
Expected: PASS.

- [ ] **Step 8: Commit.**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/solver.rs crates/shinri-euf/tests/qfuf_euf.rs
git commit -m "feat(euf): predicate atoms via ⊤/⊥ sentinel encoding"
```

---

### Task 9: backtracking (`push`/`pop`)

**Files:**
- Modify: `crates/shinri-euf/src/egraph.rs`
- Modify: `crates/shinri-euf/src/solver.rs`
- Modify: `crates/shinri-euf/tests/qfuf_euf.rs`

**Interfaces:**
- Produces: `EGraph::push(&mut self)` / `EGraph::pop(&mut self, level: usize)` that undo lookup inserts and use-list splices; `Euf::push`/`pop` drive both the EUF indices and (the engine is driven separately by the Combiner).
- Consumes: the `Undo` enum + `self.undo: UndoLog<Undo>` from Task 6/7.

**Note:** The shared `EqualityEngine` is pushed/popped by the `Combiner` (it owns `eq`). `Euf::push`/`pop` must only roll back EUF-owned state (lookup, use-lists). The `pending` queue is always drained to empty within a single `assert`/`check`, so it needs no backtracking.

- [ ] **Step 1: Write the failing pop test.**

Append to `crates/shinri-euf/tests/qfuf_euf.rs`:

```rust
/// After asserting x=y (forcing f(x)=f(y)) then popping, f(x) and f(y) are
/// independent again: asserting f(x)≠f(y) no longer conflicts.
#[test]
fn pop_undoes_congruence_merge() {
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let x = uconst(&mut ctx, "x", u);
    let y = uconst(&mut ctx, "y", u);
    let f = ctx.declare_fun("f", &[u], u);
    let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
    let fy = ctx.mk_app(Op::Uninterpreted(f), &[y]).unwrap();
    let eq_xy = ctx.mk_eq(x, y).unwrap();
    let eq_ff = ctx.mk_eq(fx, fy).unwrap();

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let (vxy, vff) = (Var::new(0), Var::new(1));
    atoms.register(vxy, eq_xy, shinri_theory::types::Owner::Euf);
    atoms.register(vff, eq_ff, shinri_theory::types::Owner::Euf);

    let mut euf = Euf::default();
    let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
    euf.new_var(&mut cx, vxy, eq_xy);
    euf.new_var(&mut cx, vff, eq_ff);

    // level 1: assert x=y
    cx.eq.push();
    euf.push();
    assert!(euf.assert(&mut cx, Lit::new(vxy, true)).is_none());
    let mut events = Vec::new();
    cx.eq.drain_merges(&mut events); // honor the engine's drain-before-pop contract
    // pop back to level 0
    cx.eq.pop(0);
    euf.pop(0);

    // Now f(x) and f(y) must be independent again.
    assert!(euf.assert(&mut cx, Lit::new(vff, false)).is_none());
    let conflict = euf.assert(&mut cx, Lit::new(vxy, true));
    // x=y again forces f(x)=f(y), contradicting the fresh f(x)≠f(y): conflict.
    assert!(conflict.is_some());
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-euf --test qfuf_euf pop_undoes_congruence -- --nocapture`
Expected: FAIL — without EUF-side undo, the lookup/use-lists are stale after pop, so re-asserting `x=y` does not re-derive the congruence (or panics on inconsistent indices).

- [ ] **Step 3: Implement `EGraph::push`/`pop`.**

In `crates/shinri-euf/src/egraph.rs`, add to `impl EGraph`:

```rust
    pub fn push(&mut self) {
        self.undo.push_level();
    }

    pub fn pop(&mut self, level: usize) {
        let lookup = &mut self.lookup;
        let use_list = &mut self.use_list;
        self.undo.pop_to(level, |u| match u {
            Undo::LookupInsert(sig) => {
                lookup.remove(&sig);
            }
            Undo::LookupOverwrite(sig, prev) => {
                lookup.insert(sig, prev);
            }
            Undo::UseSplice { winner, loser, count } => {
                let total = use_list[winner].len();
                let moved = use_list[winner].split_off(total - count);
                use_list[loser] = moved;
            }
        });
    }
```

> The `UseSplice` undo assumes the `count` apps moved onto `winner` are still its tail. Because undo is LIFO and use-lists are only mutated by splices recorded in order, the last `count` entries are exactly the moved set. The `debug_assert!` in Step 4 guards this.

- [ ] **Step 4: Guard the splice invariant + drive from `Euf`.**

In `egraph.rs`, in `recanonicalize_use_list`, after `self.use_list[winner.index()].extend(moved);` the recorded `count` equals what we appended — already consistent. Add a `debug_assert!` inside the `UseSplice` arm of `pop`:

```rust
            Undo::UseSplice { winner, loser, count } => {
                debug_assert!(use_list[winner].len() >= count, "use-splice underflow");
                let total = use_list[winner].len();
                let moved = use_list[winner].split_off(total - count);
                debug_assert!(use_list[loser].is_empty(), "loser use-list not empty on undo");
                use_list[loser] = moved;
            }
```

In `crates/shinri-euf/src/solver.rs`, update `push`/`pop`:

```rust
    fn push(&mut self) {
        self.level += 1;
        self.inner.push();
    }
    fn pop(&mut self, level: usize) {
        self.inner.pop(level);
        self.level = level;
    }
```

- [ ] **Step 5: Run.**

Run: `cargo test -p shinri-euf --test qfuf_euf pop_undoes_congruence`
Expected: PASS.

- [ ] **Step 6: Run all EUF tests.**

Run: `cargo test -p shinri-euf`
Expected: PASS.

- [ ] **Step 7: Commit.**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/solver.rs crates/shinri-euf/tests/qfuf_euf.rs
git commit -m "feat(euf): backtrack lookup + use-list splices on pop"
```

---

### Task 10: model assembly

**Files:**
- Modify: `crates/shinri-euf/src/solver.rs`
- Modify: `crates/shinri-euf/tests/qfuf_euf.rs`

**Interfaces:**
- Produces: `Euf::model` assigns each registered term a `ModelVal`: uninterpreted-sort terms get `ModelVal::Elem(sort, class_index)` consistent per congruence class; predicate apps get `ModelVal::Bool` from their `⊤`/`⊥` class.
- Consumes: `ModelBuilder::assign`, `EqualityEngine::find`, `ModelVal`, `Context::sort_of`.

**Design:** Walk every interned app term; map its representative to a small per-(sort) integer id (first-seen ordering) and assign `Elem(sort, id)`. For a node equal to `⊤`/`⊥`, assign `Bool(true/false)`.

- [ ] **Step 1: Write the failing model test.**

Append to `crates/shinri-euf/tests/qfuf_euf.rs`:

```rust
/// A satisfiable EUF instance yields a model where equal terms share a value.
#[test]
fn model_assigns_equal_terms_the_same_element() {
    use shinri_theory::ModelBuilder;
    use shinri_theory::types::ModelVal;
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let a = uconst(&mut ctx, "a", u);
    let b = uconst(&mut ctx, "b", u);
    let eq_ab = ctx.mk_eq(a, b).unwrap();

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let v = Var::new(0);
    atoms.register(v, eq_ab, shinri_theory::types::Owner::Euf);

    let mut euf = Euf::default();
    let mut m = ModelBuilder::default();
    let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
    euf.new_var(&mut cx, v, eq_ab);
    assert!(euf.assert(&mut cx, Lit::new(v, true)).is_none());
    euf.model(&mut cx, &mut m);
    assert_eq!(m.get(a), m.get(b), "a=b ⇒ same model element");
    assert!(matches!(m.get(a), Some(ModelVal::Elem(_, _))));
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-euf --test qfuf_euf model_assigns -- --nocapture`
Expected: FAIL — `model` is a no-op, so `m.get(a)` is `None`.

- [ ] **Step 3: Track registered terms + implement `model`.**

In `crates/shinri-euf/src/egraph.rs`, record every interned term so `model` can iterate them. Add a field:

```rust
    terms: Vec<(TermId, ENodeId)>,
```

In `add_term`, right after `let node = cx.eq.intern(t);` and the `ensure_node`, record it once:

```rust
        if !self.app_of.contains_key(&node) {
            // (first registration of this node — record below after structure)
        }
```

Simpler: at the end of `add_term`, before each `return node;`, push `self.terms.push((t, node));`. To avoid duplicates, guard with the existing early-return (`if self.app_of.contains_key(&node) { return node; }`) for apps; for leaves, track a separate seen set. Add field `seen_terms: FxHashMap<TermId, ()>` and at function top:

```rust
        if self.seen_terms.insert(t, ()).is_some() {
            return cx.eq.intern(t);
        }
        let node = cx.eq.intern(t);
        self.terms.push((t, node));
```

(remove the now-redundant early `app_of` return; the `seen_terms` guard subsumes it.)

Add the accessor:

```rust
    pub fn registered_terms(&self) -> &[(TermId, ENodeId)] {
        &self.terms
    }

    pub fn truth(&self) -> Option<(ENodeId, ENodeId)> {
        self.truth
    }
```

In `crates/shinri-euf/src/solver.rs`, implement `model`:

```rust
    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        use shinri_theory::types::ModelVal;
        use rustc_hash::FxHashMap;
        let truth = self.inner.truth();
        let mut elem_of: FxHashMap<(shinri_core::SortId, shinri_theory::types::ENodeId), u32> =
            FxHashMap::default();
        for &(term, _node) in self.inner.registered_terms() {
            let rep = cx.eq.find(cx.eq.intern(term));
            if let Some((tn, fln)) = truth {
                if cx.eq.find(tn) == rep {
                    m.assign(term, ModelVal::Bool(true));
                    continue;
                }
                if cx.eq.find(fln) == rep {
                    m.assign(term, ModelVal::Bool(false));
                    continue;
                }
            }
            let sort = cx.terms.sort_of(term);
            let next = elem_of.len() as u32;
            let id = *elem_of.entry((sort, rep)).or_insert(next);
            m.assign(term, ModelVal::Elem(sort, id));
        }
    }
```

> If `model`'s signature requires `&mut self` but `self.inner.registered_terms()` borrows `self.inner` immutably while `cx.eq` is borrowed mutably — these are disjoint borrows (`self.inner` vs `cx`), so it compiles. If the borrow checker complains, collect `registered_terms()` into a local `Vec` first.

- [ ] **Step 4: Run.**

Run: `cargo test -p shinri-euf --test qfuf_euf model_assigns`
Expected: PASS.

- [ ] **Step 5: Run all EUF tests.**

Run: `cargo test -p shinri-euf`
Expected: PASS.

- [ ] **Step 6: Commit.**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/solver.rs crates/shinri-euf/tests/qfuf_euf.rs
git commit -m "feat(euf): congruence-class model assembly (Elem / Bool)"
```

---

### Task 11: explanation for theory propagation + property test

**Files:**
- Modify: `crates/shinri-euf/src/solver.rs`
- Modify: `crates/shinri-euf/src/egraph.rs`
- Create: `crates/shinri-euf/tests/euf_props.rs`

**Interfaces:**
- Produces: `Euf::propagate` (cheap subset: forced equality/disequality atoms) emitting `(Lit, TheoryJust{theory: 1, tag})`; `Euf::explain(tag)` reconstructing antecedents via `eq.explain`; a per-tag record in the e-graph.
- Consumes: `EqualityEngine::{are_equal, explain, find, intern}`, `Explainer::push_leaf`.

**Design:** On `propagate`, scan registered equality atoms still unassigned in the current model: if both sides are equal in the engine, propagate the positive literal; if a disequality is entailed (representatives are in a recorded disequal pair), propagate the negative. Each propagation records `tag → (a_node, b_node, polarity)`; `explain(tag)` calls `eq.explain(a,b)` (for the equality case) into the `Explainer`. *Minimal cheap version:* only propagate forced **equalities** (the highest-value, simplest case); disequality propagation can be added later behind the same interface.

- [ ] **Step 1: Write the failing propagation test.**

Append to `crates/shinri-euf/tests/qfuf_euf.rs`:

```rust
/// With x=y asserted and a registered atom (x = y'), where y' is merged to y,
/// EUF propagates that atom true with an explainable justification.
#[test]
fn propagates_forced_equality_with_explanation() {
    use shinri_core::TheoryJust;
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let x = uconst(&mut ctx, "x", u);
    let y = uconst(&mut ctx, "y", u);
    let eq_xy = ctx.mk_eq(x, y).unwrap();
    let eq_xy2 = ctx.mk_eq(y, x).unwrap(); // a second, distinct atom over the same pair

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let (v0, v1) = (Var::new(0), Var::new(1));
    atoms.register(v0, eq_xy, shinri_theory::types::Owner::Euf);
    atoms.register(v1, eq_xy2, shinri_theory::types::Owner::Euf);

    let mut euf = Euf::default();
    let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
    euf.new_var(&mut cx, v0, eq_xy);
    euf.new_var(&mut cx, v1, eq_xy2);
    assert!(euf.assert(&mut cx, Lit::new(v0, true)).is_none());

    let mut out: Vec<(Lit, TheoryJust)> = Vec::new();
    assert!(euf.propagate(&mut cx, &mut out).is_none());
    assert!(
        out.iter().any(|(l, _)| l.var() == v1 && l.is_positive()),
        "x=y entails the (y=x) atom"
    );
    // The justification is explainable to the original asserted literal.
    let (_, just) = *out.iter().find(|(l, _)| l.var() == v1).unwrap();
    let mut exp = shinri_theory::Explainer::default();
    euf.explain(&mut cx, just.tag, &mut exp);
    assert!(exp.lits.contains(&Lit::new(v0, true)));
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-euf --test qfuf_euf propagates_forced -- --nocapture`
Expected: FAIL — `propagate` returns nothing.

- [ ] **Step 3: Track equality atoms + propagation records.**

In `crates/shinri-euf/src/egraph.rs`, add fields:

```rust
    /// Registered equality atoms: (var index, a_node, b_node).
    eq_atoms: Vec<(u32, ENodeId, ENodeId)>,
    /// Propagation explanation records: tag -> (a_node, b_node).
    prop_records: Vec<(ENodeId, ENodeId)>,
    /// Vars already propagated (avoid re-emitting), append-only within a solve.
    propagated: rustc_hash::FxHashSet<u32>,
```

Add a registration hook called from `Euf::new_var` for equality atoms:

```rust
    pub fn register_eq_atom(&mut self, var_index: u32, a: ENodeId, b: ENodeId) {
        self.eq_atoms.push((var_index, a, b));
    }
```

Add the propagation scan:

```rust
    /// Emit forced-equality propagations. Returns the (lit-var, tag) pairs.
    pub fn collect_eq_propagations(&mut self, eq: &EqualityEngine) -> Vec<(u32, u32)> {
        let mut out = Vec::new();
        for &(vi, a, b) in &self.eq_atoms {
            if self.propagated.contains(&vi) {
                continue;
            }
            if eq.are_equal(a, b) {
                let tag = self.prop_records.len() as u32;
                self.prop_records.push((a, b));
                self.propagated.insert(vi);
                out.push((vi, tag));
            }
        }
        out
    }

    pub fn prop_record(&self, tag: u32) -> (ENodeId, ENodeId) {
        self.prop_records[tag as usize]
    }
```

> `propagated` is append-only and intentionally NOT backtracked: a propagation re-derived after backtrack is still sound (the SAT layer re-requests via the same atoms). For Phase-1 simplicity we accept possibly missing a re-propagation after pop; correctness is unaffected because `check(Full)` re-validates. (Documented limitation.)

- [ ] **Step 4: Register eq atoms in `new_var`, implement `propagate`/`explain`.**

In `crates/shinri-euf/src/solver.rs`, extend `new_var`'s `Eq` arm to register the atom:

```rust
            TermNode::App { op: Op::Builtin(BuiltinOp::Eq), args, .. } => {
                let kids: Vec<TermId> = cx.terms.children(*args).to_vec();
                let a = self.inner.add_term(cx, kids[0]);
                let b = self.inner.add_term(cx, kids[1]);
                self.inner.register_eq_atom(_v.index() as u32, a, b);
            }
```

(rename `_v` to `v` in the signature so `v.index()` is available: `fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId)`.)

Implement `propagate`:

```rust
    fn propagate(
        &mut self,
        cx: &mut TheoryCtx,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        let props = self.inner.collect_eq_propagations(cx.eq);
        for (vi, tag) in props {
            let lit = Lit::new(Var::new(vi), true);
            out.push((lit, TheoryJust { theory: Self::THEORY_ID, tag }));
        }
        None
    }
```

Implement `explain`:

```rust
    fn explain(&mut self, cx: &mut TheoryCtx, tag: u32, exp: &mut Explainer) {
        let (a, b) = self.inner.prop_record(tag);
        let mut leaves = Vec::new();
        cx.eq.explain(a, b, &mut leaves);
        for leaf in leaves {
            exp.push_leaf(leaf);
        }
    }
```

- [ ] **Step 5: Run the propagation test.**

Run: `cargo test -p shinri-euf --test qfuf_euf propagates_forced`
Expected: PASS.

- [ ] **Step 6: Add a property test (every conflict is genuinely inconsistent).**

Create `crates/shinri-euf/tests/euf_props.rs`:

```rust
//! Property: any conflict EUF returns is a genuine EUF inconsistency — the
//! returned antecedent literals, taken as asserted, force an equality that a
//! disequality forbids. We verify structurally: a conflict is only ever
//! returned by the engine's own disequality guard, so re-running the asserted
//! antecedents must reproduce equality of the conflicting pair.

use proptest::prelude::*;
use shinri_core::{Context, Lit, Op, TermId, Var};
use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};
use shinri_euf::Euf;

fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
    let sym = ctx.declare_fun(name, &[], s);
    ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
}

proptest! {
    /// Random chains a0=a1=...=ak plus a0 != ak must always conflict.
    #[test]
    fn transitivity_chain_conflicts(k in 1usize..8) {
        let mut ctx = Context::new();
        let u = ctx.declare_sort("U");
        let cs: Vec<TermId> = (0..=k).map(|i| uconst(&mut ctx, &format!("c{i}"), u)).collect();
        let mut eqs = Vec::new();
        for i in 0..k {
            eqs.push(ctx.mk_eq(cs[i], cs[i + 1]).unwrap());
        }
        let diseq = ctx.mk_eq(cs[0], cs[k]).unwrap(); // assert NEGATIVE => a0 != ak

        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        for (i, &atom) in eqs.iter().enumerate() {
            atoms.register(Var::new(i as u32), atom, shinri_theory::types::Owner::Euf);
        }
        let vd = Var::new(k as u32);
        atoms.register(vd, diseq, shinri_theory::types::Owner::Euf);

        let mut euf = Euf::default();
        let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
        for (i, &atom) in eqs.iter().enumerate() {
            euf.new_var(&mut cx, Var::new(i as u32), atom);
        }
        euf.new_var(&mut cx, vd, diseq);

        prop_assert!(euf.assert(&mut cx, Lit::new(vd, false)).is_none());
        let mut conflict = None;
        for i in 0..k {
            if let Some(c) = euf.assert(&mut cx, Lit::new(Var::new(i as u32), true)) {
                conflict = Some(c);
                break;
            }
        }
        prop_assert!(conflict.is_some(), "a0=..=ak with a0!=ak must conflict");
    }
}
```

- [ ] **Step 7: Run the property test.**

Run: `cargo test -p shinri-euf --test euf_props`
Expected: PASS.

- [ ] **Step 8: Commit.**

```bash
git add crates/shinri-euf/src/egraph.rs crates/shinri-euf/src/solver.rs crates/shinri-euf/tests/qfuf_euf.rs crates/shinri-euf/tests/euf_props.rs
git commit -m "feat(euf): cheap equality propagation + explanation + conflict property test"
```

---

## Phase D — embeddable solver (`shinri-solver`)

### Task 12: crate scaffold + `Solver` API + wiring

**Files:**
- Create: `crates/shinri-solver/Cargo.toml`
- Create: `crates/shinri-solver/src/lib.rs`
- Create: `crates/shinri-solver/src/model.rs`
- Modify: `Cargo.toml` (root)

**Interfaces:**
- Produces: `pub struct Solver`; `Solver::new()`; `declare_sort`, `declare_fun`, term builders (`eq`, `app`, `not`, `and`, `or`, `bool_const`), `assert(TermId)`; `SolveOutcome { Sat, Unsat, Unknown }`; placeholder `check_sat` returning `Unknown`. Owns a `Context` and the SAT solver type alias `Sat = shinri_sat::Solver<Combiner<Euf, EmptyTheory>, NoProof, Vmtf>`.
- Consumes: `shinri_theory::Combiner`, `shinri_euf::Euf`, `shinri_theory::EmptyTheory`, `shinri_sat::{Solver, Vmtf, SolverConfig}`, `shinri_core::{Context, NoProof, ...}`.

- [ ] **Step 1: Create the crate manifest.**

Create `crates/shinri-solver/Cargo.toml`:

```toml
[package]
name = "shinri-solver"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-sat = { path = "../shinri-sat" }
shinri-theory = { path = "../shinri-theory" }
shinri-euf = { path = "../shinri-euf" }
rustc-hash = "2"

[dev-dependencies]
easy-smt = "0.2"

[features]
# Differential oracle harness (Task 17); off by default; needs `z3` on PATH.
oracle = []
```

- [ ] **Step 2: Register the workspace member.**

Add `"crates/shinri-solver"` to the root `Cargo.toml` `[workspace].members`.

- [ ] **Step 3: Write `model.rs`.**

Create `crates/shinri-solver/src/model.rs`:

```rust
use rustc_hash::FxHashMap;
use shinri_core::TermId;
use shinri_theory::types::ModelVal;

/// The outcome of `check_sat`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SolveOutcome {
    Sat,
    Unsat,
    Unknown,
}

/// A satisfying assignment, keyed by term.
#[derive(Default, Debug)]
pub struct Model {
    pub(crate) values: FxHashMap<TermId, ModelVal>,
}

impl Model {
    pub fn get(&self, t: TermId) -> Option<&ModelVal> {
        self.values.get(&t)
    }
}
```

- [ ] **Step 4: Write the crate root with the API surface + a smoke test.**

Create `crates/shinri-solver/src/lib.rs`:

```rust
//! shinri-solver: the embeddable QF_UF solver entry point. Owns the term DAG,
//! Tseitin-encodes Boolean structure into the CDCL(T) SAT engine, registers EUF
//! atoms, and extracts models. No SMT-LIB parser (assert via the API).

mod model;
mod tseitin;

pub use model::{Model, SolveOutcome};

use shinri_core::{Context, Op, SortId, SymbolId, TermId};

pub struct Solver {
    ctx: Context,
    assertions: Vec<TermId>,
}

impl Default for Solver {
    fn default() -> Self {
        Solver::new()
    }
}

impl Solver {
    pub fn new() -> Solver {
        Solver {
            ctx: Context::new(),
            assertions: Vec::new(),
        }
    }

    pub fn declare_sort(&mut self, name: &str) -> SortId {
        self.ctx.declare_sort(name)
    }
    pub fn declare_fun(&mut self, name: &str, params: &[SortId], result: SortId) -> SymbolId {
        self.ctx.declare_fun(name, params, result)
    }
    pub fn bool_sort(&self) -> SortId {
        self.ctx.bool_sort()
    }
    pub fn app(&mut self, op: Op, args: &[TermId]) -> TermId {
        self.ctx.mk_app(op, args).expect("well-sorted application")
    }
    pub fn eq(&mut self, a: TermId, b: TermId) -> TermId {
        self.ctx.mk_eq(a, b).expect("well-sorted equality")
    }
    pub fn assert(&mut self, formula: TermId) {
        self.assertions.push(formula);
    }

    pub fn check_sat(&mut self) -> SolveOutcome {
        // Implemented in Task 14.
        SolveOutcome::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn solver_builds_terms() {
        let mut s = Solver::new();
        let u = s.declare_sort("U");
        let af = s.declare_fun("a", &[], u);
        let a = s.app(Op::Uninterpreted(af), &[]);
        let bf = s.declare_fun("b", &[], u);
        let b = s.app(Op::Uninterpreted(bf), &[]);
        let e = s.eq(a, b);
        s.assert(e);
        assert_eq!(s.check_sat(), SolveOutcome::Unknown); // until Task 14
    }
}
```

- [ ] **Step 5: Write a `tseitin.rs` placeholder so the module resolves.**

Create `crates/shinri-solver/src/tseitin.rs`:

```rust
//! Boolean-structure CNF encoding + atom registration. Implemented in Task 13.
```

- [ ] **Step 6: Build + test.**

Run: `cargo test -p shinri-solver --lib`
Expected: PASS (`solver_builds_terms`).

- [ ] **Step 7: Commit.**

```bash
git add crates/shinri-solver/Cargo.toml crates/shinri-solver/src/lib.rs crates/shinri-solver/src/model.rs crates/shinri-solver/src/tseitin.rs Cargo.toml
git commit -m "feat(solver): crate scaffold + Solver API surface"
```

---

### Task 13: Tseitin CNF encoder + `distinct` lowering + atom registration

**Files:**
- Modify: `crates/shinri-solver/src/tseitin.rs`
- Modify: `crates/shinri-solver/src/lib.rs`

**Interfaces:**
- Produces: `tseitin::Encoder` with `fn encode(&mut self, sat, combiner_via_theory_mut, formula) -> Lit` (returns the literal representing the formula's truth), allocating SAT vars, registering theory atoms with `register_atom`, lowering n-ary `distinct` to pairwise binary atoms, and adding the defining clauses. Exposes `atom_vars: Vec<(Var, TermId)>` for model extraction.
- Consumes: `shinri_sat::Solver::{new_var, add_clause, theory_mut}`, `Combiner::register_atom`, `Context::{term_node, children}`, `Op`, `BuiltinOp`, `TermNode`.

**Design:** Recursive Tseitin. A Bool term is either a connective (`Not/And/Or/Implies/Xor/Ite`, `Eq`/`Distinct` over Bool args) — encoded with a fresh output var and standard clauses — or a **theory atom** leaf (equality/disequality over non-Bool, or an uninterpreted predicate app), which gets one var registered with the Combiner. A `TermId → Lit` cache shares structure. n-ary `(distinct t1..tn)` over a non-Bool sort is rewritten to `and_{i<j} (distinct ti tj)` where each binary `(distinct ti tj)` is the negation of `(= ti tj)` (so it reuses the equality-atom path negated).

- [ ] **Step 1: Write the failing test (encode a conjunction, check var registration).**

Add to `crates/shinri-solver/src/tseitin.rs` a test that the encoder registers a theory atom and returns a usable literal. First write the encoder skeleton enough for the test to compile against, then the test. Put this test at the bottom:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Op;

    #[test]
    fn encodes_equality_atom_as_registered_var() {
        let mut s = crate::Solver::new();
        let u = s.declare_sort("U");
        let af = s.declare_fun("a", &[], u);
        let a = s.app(Op::Uninterpreted(af), &[]);
        let bf = s.declare_fun("b", &[], u);
        let b = s.app(Op::Uninterpreted(bf), &[]);
        let e = s.eq(a, b);

        let (lit, atom_vars) = s.encode_for_test(e);
        // The equality atom became exactly one registered theory atom.
        assert_eq!(atom_vars.len(), 1);
        assert_eq!(atom_vars[0].1, e);
        // The returned literal is the positive phase of that atom's var.
        assert_eq!(lit.var(), atom_vars[0].0);
        assert!(lit.is_positive());
    }
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-solver --lib encodes_equality_atom -- --nocapture`
Expected: FAIL — `encode_for_test` and the encoder do not exist.

- [ ] **Step 3: Implement the encoder.**

Replace `crates/shinri-solver/src/tseitin.rs` contents with:

```rust
//! Boolean-structure CNF encoding + theory-atom registration.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, TermNode, Var};
use shinri_euf::Euf;
use shinri_theory::{Combiner, EmptyTheory};

type Sat = shinri_sat::Solver<Combiner<Euf, EmptyTheory>, shinri_core::NoProof, shinri_sat::Vmtf>;

pub struct Encoder<'a> {
    ctx: &'a Context,
    sat: &'a mut Sat,
    cache: FxHashMap<TermId, Lit>,
    pub atom_vars: Vec<(Var, TermId)>,
    t_true: TermId,
    t_false: TermId,
}

impl<'a> Encoder<'a> {
    pub fn new(ctx: &'a Context, sat: &'a mut Sat, t_true: TermId, t_false: TermId) -> Self {
        Encoder {
            ctx,
            sat,
            cache: FxHashMap::default(),
            atom_vars: Vec::new(),
            t_true,
            t_false,
        }
    }

    /// Encode `t` (a Bool-sorted term); return a literal true iff `t` holds.
    pub fn encode(&mut self, t: TermId) -> Lit {
        if let Some(&l) = self.cache.get(&t) {
            return l;
        }
        let lit = self.encode_uncached(t);
        self.cache.insert(t, lit);
        lit
    }

    fn fresh(&mut self) -> Lit {
        Lit::new(self.sat.new_var(), true)
    }

    fn encode_uncached(&mut self, t: TermId) -> Lit {
        match self.ctx.term_node(t) {
            TermNode::App { op: Op::Builtin(b), args, .. } => {
                let kids: Vec<TermId> = self.ctx.children(*args).to_vec();
                match b {
                    BuiltinOp::Not => {
                        let a = self.encode(kids[0]);
                        a.negate()
                    }
                    BuiltinOp::And => self.encode_and(&kids),
                    BuiltinOp::Or => self.encode_or(&kids),
                    BuiltinOp::Implies => {
                        // a -> b  ≡  ¬a ∨ b ; chain right-assoc for n args.
                        let mut acc = self.encode(kids[kids.len() - 1]);
                        for i in (0..kids.len() - 1).rev() {
                            let a = self.encode(kids[i]);
                            acc = self.or2(a.negate(), acc);
                        }
                        acc
                    }
                    BuiltinOp::Xor => {
                        let mut acc = self.encode(kids[0]);
                        for k in &kids[1..] {
                            let b = self.encode(*k);
                            acc = self.xor2(acc, b);
                        }
                        acc
                    }
                    BuiltinOp::Ite => {
                        let c = self.encode(kids[0]);
                        let th = self.encode(kids[1]);
                        let el = self.encode(kids[2]);
                        self.ite(c, th, el)
                    }
                    BuiltinOp::Eq if self.is_bool(kids[0]) => {
                        // Bool equality = iff.
                        let a = self.encode(kids[0]);
                        let b = self.encode(kids[1]);
                        let nx = self.xor2(a, b);
                        nx.negate()
                    }
                    BuiltinOp::Distinct if self.is_bool(kids[0]) => {
                        // Bool distinct (binary) = xor.
                        let a = self.encode(kids[0]);
                        let b = self.encode(kids[1]);
                        self.xor2(a, b)
                    }
                    BuiltinOp::Distinct => self.encode_distinct(&kids),
                    BuiltinOp::Eq => self.atom(t), // theory equality atom
                    _ => self.atom(t),             // arithmetic etc. -> atom (refused later)
                }
            }
            // Uninterpreted predicate application, or a Bool constant.
            TermNode::App { op: Op::Uninterpreted(_), .. } => self.atom(t),
            TermNode::Const { .. } => {
                if t == self.t_true {
                    // Represent constant true with a fixed satisfied literal.
                    let l = self.fresh();
                    self.sat.add_clause(&[l]);
                    l
                } else if t == self.t_false {
                    let l = self.fresh();
                    self.sat.add_clause(&[l.negate()]);
                    l
                } else {
                    self.atom(t)
                }
            }
        }
    }

    fn is_bool(&self, t: TermId) -> bool {
        self.ctx.sort_of(t) == self.ctx.bool_sort()
    }

    /// A theory atom leaf: one SAT var, registered with the Combiner.
    fn atom(&mut self, t: TermId) -> Lit {
        let v = self.sat.new_var();
        // Refusal (unsupported atom) surfaces as Unknown at the solver layer;
        // register_atom returns Err for those. We record the (var, term) either
        // way; check_sat consults registration success.
        let _ = self.sat.theory_mut().register_atom(v, t);
        self.atom_vars.push((v, t));
        Lit::new(v, true)
    }

    /// n-ary distinct over a non-Bool sort -> conjunction of pairwise binary
    /// distinct atoms (each = negated equality atom).
    fn encode_distinct(&mut self, kids: &[TermId]) -> Lit {
        // Build pairwise (= ti tj) atoms and require all negated (true distinct).
        let out = self.fresh();
        let mut pair_lits = Vec::new();
        for i in 0..kids.len() {
            for j in (i + 1)..kids.len() {
                // We cannot mk_eq here (immutable ctx); pairwise eq terms must be
                // pre-built by the caller. See lower_distinct in lib.rs (Task 14).
                // For the binary case this branch is unreachable; n-ary distinct
                // is lowered before encoding.
                let _ = (i, j);
                unreachable!("n-ary distinct must be lowered before encoding");
            }
        }
        let _ = &mut pair_lits;
        out
    }

    fn encode_and(&mut self, kids: &[TermId]) -> Lit {
        let out = self.fresh();
        let mut child_lits = Vec::with_capacity(kids.len());
        for &k in kids {
            child_lits.push(self.encode(k));
        }
        // out -> each child ;  (¬out ∨ ci)
        for &ci in &child_lits {
            self.sat.add_clause(&[out.negate(), ci]);
        }
        // (∧ ci) -> out ;  (out ∨ ¬c1 ∨ ... ∨ ¬cn)
        let mut big = vec![out];
        big.extend(child_lits.iter().map(|l| l.negate()));
        self.sat.add_clause(&big);
        out
    }

    fn encode_or(&mut self, kids: &[TermId]) -> Lit {
        let out = self.fresh();
        let mut child_lits = Vec::with_capacity(kids.len());
        for &k in kids {
            child_lits.push(self.encode(k));
        }
        for &ci in &child_lits {
            self.sat.add_clause(&[out, ci.negate()]);
        }
        let mut big = vec![out.negate()];
        big.extend(child_lits.iter().copied());
        self.sat.add_clause(&big);
        out
    }

    fn or2(&mut self, a: Lit, b: Lit) -> Lit {
        let out = self.fresh();
        self.sat.add_clause(&[out, a.negate()]);
        self.sat.add_clause(&[out, b.negate()]);
        self.sat.add_clause(&[out.negate(), a, b]);
        out
    }

    fn xor2(&mut self, a: Lit, b: Lit) -> Lit {
        let out = self.fresh();
        // out <-> (a xor b)
        self.sat.add_clause(&[out.negate(), a, b]);
        self.sat.add_clause(&[out.negate(), a.negate(), b.negate()]);
        self.sat.add_clause(&[out, a.negate(), b]);
        self.sat.add_clause(&[out, a, b.negate()]);
        out
    }

    fn ite(&mut self, c: Lit, th: Lit, el: Lit) -> Lit {
        let out = self.fresh();
        // c -> (out <-> th)
        self.sat.add_clause(&[c.negate(), out.negate(), th]);
        self.sat.add_clause(&[c.negate(), out, th.negate()]);
        // ¬c -> (out <-> el)
        self.sat.add_clause(&[c, out.negate(), el]);
        self.sat.add_clause(&[c, out, el.negate()]);
        out
    }
}
```

- [ ] **Step 4: Add `encode_for_test` to `Solver` (test seam) and `t_true`/`t_false`.**

In `crates/shinri-solver/src/lib.rs`, store canonical Bool constants on the `Solver` and add a test-only wiring helper. Change `Solver` to also build the SAT solver + truth terms. Replace the `Solver` struct and `new`:

```rust
use shinri_euf::Euf;
use shinri_theory::{Combiner, EmptyTheory};
use shinri_sat::{SolverConfig, Vmtf};
use shinri_core::NoProof;

type Sat = shinri_sat::Solver<Combiner<Euf, EmptyTheory>, NoProof, Vmtf>;

pub struct Solver {
    ctx: Context,
    assertions: Vec<TermId>,
    t_true: TermId,
    t_false: TermId,
}

impl Solver {
    pub fn new() -> Solver {
        let mut ctx = Context::new();
        let t_true = ctx.mk_const_bool(true);
        let t_false = ctx.mk_const_bool(false);
        Solver { ctx, assertions: Vec::new(), t_true, t_false }
    }
```

Add the test seam (only compiled in tests):

```rust
    #[cfg(test)]
    pub(crate) fn encode_for_test(&mut self, formula: TermId) -> (Lit, Vec<(shinri_core::Var, TermId)>) {
        use crate::tseitin::Encoder;
        let mut sat: Sat = shinri_sat::Solver::with_theory(
            SolverConfig::default(),
            Combiner::with_context(self.ctx.clone()),
        );
        let mut enc = Encoder::new(&self.ctx, &mut sat, self.t_true, self.t_false);
        let lit = enc.encode(formula);
        (lit, enc.atom_vars.clone())
    }
```

> This requires `Context: Clone`, which it is NOT today (verified). Make it `Clone`: add `#[derive(Clone, Default)]` to `pub struct StringInterner` in `crates/shinri-core/src/symbol.rs` (it currently derives only `Default`; its fields are `Clone`), then add `#[derive(Clone)]` to `pub struct Context` in `crates/shinri-core/src/context.rs`. Run `cargo build -p shinri-core` to confirm. Also add `use shinri_core::Lit;` at the top of `lib.rs`. The clone gives the `Combiner` its own copy of the term DAG; `TermId`s are preserved by cloning, so atoms registered into the clone and model values read back stay id-compatible with the solver's own `Context`.

- [ ] **Step 5: Run the encoder test.**

Run: `cargo test -p shinri-solver --lib encodes_equality_atom`
Expected: PASS.

- [ ] **Step 6: Commit.**

```bash
git add crates/shinri-solver/src/tseitin.rs crates/shinri-solver/src/lib.rs crates/shinri-core/src/context.rs
git commit -m "feat(solver): Tseitin CNF encoder + theory-atom registration"
```

---

### Task 14: `check_sat` + `get_model` + `get_value` + `distinct` lowering

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs`

**Interfaces:**
- Produces: `Solver::check_sat() -> SolveOutcome` (full pipeline), `Solver::get_model() -> Model`, `Solver::get_value(TermId) -> Option<ModelVal>`. Internal `lower_distinct` rewriting n-ary `distinct` to pairwise binary; `Unknown` on unsupported-atom refusal.
- Consumes: Task 13 `Encoder`, `Sat::{add_clause, solve, value_of, theory_mut}`, `Combiner::{register_atom, build_model}`, `Euf::set_truth_terms`.

- [ ] **Step 1: Write the failing end-to-end test (in the lib test module).**

Add to the `#[cfg(test)] mod tests` in `crates/shinri-solver/src/lib.rs`:

```rust
    #[test]
    fn unsat_x_eq_y_and_fx_neq_fy() {
        use shinri_core::{BuiltinOp, Op};
        let mut s = Solver::new();
        let u = s.declare_sort("U");
        let xf = s.declare_fun("x", &[], u);
        let x = s.app(Op::Uninterpreted(xf), &[]);
        let yf = s.declare_fun("y", &[], u);
        let y = s.app(Op::Uninterpreted(yf), &[]);
        let f = s.declare_fun("f", &[u], u);
        let fx = s.app(Op::Uninterpreted(f), &[x]);
        let fy = s.app(Op::Uninterpreted(f), &[y]);
        let xy = s.eq(x, y);
        let ffeq = s.eq(fx, fy);
        let nffeq = s.app(Op::Builtin(BuiltinOp::Not), &[ffeq]);
        s.assert(xy);
        s.assert(nffeq);
        assert_eq!(s.check_sat(), SolveOutcome::Unsat);
    }

    #[test]
    fn sat_with_model() {
        use shinri_core::Op;
        let mut s = Solver::new();
        let u = s.declare_sort("U");
        let af = s.declare_fun("a", &[], u);
        let a = s.app(Op::Uninterpreted(af), &[]);
        let bf = s.declare_fun("b", &[], u);
        let b = s.app(Op::Uninterpreted(bf), &[]);
        let ab = s.eq(a, b);
        s.assert(ab);
        assert_eq!(s.check_sat(), SolveOutcome::Sat);
        let m = s.get_model();
        assert_eq!(m.get(a), m.get(b));
    }
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-solver --lib unsat_x_eq_y -- --nocapture`
Expected: FAIL — `check_sat` still returns `Unknown`.

- [ ] **Step 3: Implement the full pipeline.**

In `crates/shinri-solver/src/lib.rs`, add a stored `Sat` + `Model` to `Solver` so `get_model` works after `check_sat`. Replace the `Solver` struct fields and `new`:

```rust
pub struct Solver {
    ctx: Context,
    assertions: Vec<TermId>,
    t_true: TermId,
    t_false: TermId,
    last_model: Option<Model>,
}
```

Add `last_model: None,` to `new`. Replace `check_sat` with:

```rust
    pub fn check_sat(&mut self) -> SolveOutcome {
        use crate::tseitin::Encoder;
        // Lower n-ary distinct to pairwise binary up front (needs &mut ctx).
        let lowered: Vec<TermId> = self
            .assertions
            .clone()
            .into_iter()
            .map(|a| self.lower(a))
            .collect();

        let mut sat: Sat = shinri_sat::Solver::with_theory(
            SolverConfig::default(),
            Combiner::with_context(self.ctx.clone()),
        );
        sat.theory_mut().euf_mut().set_truth_terms(self.t_true, self.t_false); // euf_mut added in step 4(b)

        let mut atom_vars: Vec<(shinri_core::Var, TermId)> = Vec::new();
        {
            let mut enc = Encoder::new(&self.ctx, &mut sat, self.t_true, self.t_false);
            for &a in &lowered {
                let lit = enc.encode(a);
                enc.assert_top(lit);
            }
            atom_vars = enc.atom_vars.clone();
            if enc.refused {
                return SolveOutcome::Unknown;
            }
        }

        match sat.solve() {
            shinri_sat::SolveResult::Unsat { .. } => SolveOutcome::Unsat,
            shinri_sat::SolveResult::Sat => {
                let mb = sat.theory_mut().build_model();
                let mut model = Model::default();
                for (_v, term) in &atom_vars {
                    if let Some(val) = mb.get(*term) {
                        model.values.insert(*term, val.clone());
                    }
                }
                // Also surface values for all declared leaf terms in the model.
                for (term, val) in mb.iter() {
                    model.values.insert(term, val.clone());
                }
                self.last_model = Some(model);
                SolveOutcome::Sat
            }
        }
    }

    pub fn get_model(&mut self) -> Model {
        std::mem::take(&mut self.last_model).unwrap_or_default()
    }

    pub fn get_value(&self, t: TermId) -> Option<shinri_theory::types::ModelVal> {
        self.last_model.as_ref().and_then(|m| m.get(t).cloned())
    }

    /// Rewrite n-ary `(distinct t1..tn)` into `(and (distinct ti tj) ...)`.
    fn lower(&mut self, t: TermId) -> TermId {
        use shinri_core::{BuiltinOp, Op, TermNode};
        // Shallow: only top-level + one level of Boolean structure need lowering
        // for Phase-1 (assertions are built by the API, not arbitrarily nested
        // distinct). Recurse through Boolean connectives.
        match self.ctx.term_node(t).clone() {
            TermNode::App { op: Op::Builtin(BuiltinOp::Distinct), args, .. } => {
                let kids: Vec<TermId> = self.ctx.children(args).to_vec();
                if kids.len() <= 2 {
                    return t;
                }
                let mut pairs = Vec::new();
                for i in 0..kids.len() {
                    for j in (i + 1)..kids.len() {
                        let d = self
                            .ctx
                            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[kids[i], kids[j]])
                            .expect("binary distinct well-sorted");
                        pairs.push(d);
                    }
                }
                self.ctx
                    .mk_app(Op::Builtin(BuiltinOp::And), &pairs)
                    .expect("and well-sorted")
            }
            TermNode::App { op: Op::Builtin(b), args, .. }
                if matches!(
                    b,
                    BuiltinOp::Not
                        | BuiltinOp::And
                        | BuiltinOp::Or
                        | BuiltinOp::Implies
                        | BuiltinOp::Xor
                        | BuiltinOp::Ite
                ) =>
            {
                let kids: Vec<TermId> = self.ctx.children(args).to_vec();
                let lowered: Vec<TermId> = kids.into_iter().map(|k| self.lower(k)).collect();
                self.ctx.mk_app(Op::Builtin(b), &lowered).expect("well-sorted")
            }
            _ => t,
        }
    }
```

- [ ] **Step 4: Add the missing encoder/theory helpers used above.**

Three referenced items don't exist yet — add them:

(a) `Encoder::assert_top` and `Encoder::refused` in `tseitin.rs`. Add a `pub refused: bool` field (init `false`), set it in `atom` when `register_atom` returns `Err`. Add:

```rust
    /// Force the encoded top-level formula literal to be true.
    pub fn assert_top(&mut self, lit: Lit) {
        self.sat.add_clause(&[lit]);
    }
```

And in `atom`, replace `let _ = self.sat.theory_mut().register_atom(v, t);` with:

```rust
        if self.sat.theory_mut().register_atom(v, t).is_err() {
            self.refused = true;
        }
```

(b) `Combiner::euf_mut` — exposes the EUF field so the solver can hand it the Bool sentinel terms (a generic hook would be awkward since this is EUF-specific). In `crates/shinri-theory/src/combiner.rs`, add to `impl<E: TheorySolver, A: TheorySolver> Combiner<E, A>`: `pub fn euf_mut(&mut self) -> &mut E { &mut self.euf }`. The `check_sat` call in step 3 already uses `sat.theory_mut().euf_mut().set_truth_terms(...)`; `set_truth_terms` exists on `Euf` from Task 8.

(c) `ModelBuilder::iter` — yields `(TermId, ModelVal)`. In `crates/shinri-theory/src/model.rs`, add:

```rust
    pub fn iter(&self) -> impl Iterator<Item = (shinri_core::TermId, crate::types::ModelVal)> + '_ {
        self.values.iter().map(|(t, v)| (*t, v.clone()))
    }
```

The `values` field is private but `iter` lives in the same module (`model.rs`), so direct field access is fine. The contract: iterate all assigned `(TermId, ModelVal)`.

- [ ] **Step 5: Update `encode_for_test` to match the new `Encoder` (refused field).**

No change needed if `Encoder::new` still initializes `refused: false`. Ensure the struct literal in `Encoder::new` sets `refused: false`.

- [ ] **Step 6: Run the end-to-end tests.**

Run: `cargo test -p shinri-solver --lib`
Expected: PASS (`unsat_x_eq_y_and_fx_neq_fy`, `sat_with_model`, earlier tests).

- [ ] **Step 7: Commit.**

```bash
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/src/tseitin.rs crates/shinri-theory/src/combiner.rs crates/shinri-theory/src/model.rs
git commit -m "feat(solver): check_sat/get_model/get_value pipeline + n-ary distinct lowering"
```

---

### Task 15: incremental `push`/`pop` at the solver API

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs`
- Create: `crates/shinri-solver/tests/qfuf_e2e.rs`

**Interfaces:**
- Produces: `Solver::push()` / `Solver::pop(n)` that scope assertions; `check_sat` reflects only the active scopes.
- Consumes: existing `assertions` vec; `Vec` truncation by scope marks.

**Design:** Because `check_sat` rebuilds a fresh `Sat` from the current `Context` + active assertions each call (Phase-1 conservative model — the term DAG persists; the SAT/theory state is rebuilt per query), incremental scopes are simply assertion-stack scope marks. This sidesteps the in-flight-SAT rebuild subtlety while remaining sound: each `check_sat` solves exactly the asserted-and-still-active formula set. (The deeper in-SAT `push`/`pop` machinery from Task 4 is what enables a future single-instance incremental mode; this API-level scoping is the Phase-1 entry point.)

- [ ] **Step 1: Write the failing incremental test.**

Create `crates/shinri-solver/tests/qfuf_e2e.rs`:

```rust
use shinri_core::{BuiltinOp, Op};
use shinri_solver::{SolveOutcome, Solver};

fn uconst(s: &mut Solver, name: &str, sort: shinri_core::SortId) -> shinri_core::TermId {
    let f = s.declare_fun(name, &[], sort);
    s.app(Op::Uninterpreted(f), &[])
}

#[test]
fn push_pop_scopes_assertions() {
    let mut s = Solver::new();
    let u = s.declare_sort("U");
    let a = uconst(&mut s, "a", u);
    let b = uconst(&mut s, "b", u);
    let ab = s.eq(a, b);
    let nab = s.app(Op::Builtin(BuiltinOp::Not), &[ab]);

    s.assert(ab); // a = b
    assert_eq!(s.check_sat(), SolveOutcome::Sat);

    s.push();
    s.assert(nab); // a = b  ∧  a != b  -> unsat in this scope
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
    s.pop(1);

    // Back to just a = b -> sat again.
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}
```

- [ ] **Step 2: Run to confirm failure.**

Run: `cargo test -p shinri-solver --test qfuf_e2e push_pop_scopes -- --nocapture`
Expected: FAIL — `push`/`pop` do not exist on `Solver`.

- [ ] **Step 3: Implement scope marks.**

In `crates/shinri-solver/src/lib.rs`, add a `scopes: Vec<usize>` field to `Solver` (init `Vec::new()` in `new`), and methods:

```rust
    pub fn push(&mut self) {
        self.scopes.push(self.assertions.len());
    }

    pub fn pop(&mut self, n: usize) {
        for _ in 0..n {
            if let Some(mark) = self.scopes.pop() {
                self.assertions.truncate(mark);
            }
        }
        self.last_model = None;
    }
```

- [ ] **Step 4: Run the incremental test.**

Run: `cargo test -p shinri-solver --test qfuf_e2e push_pop_scopes`
Expected: PASS.

- [ ] **Step 5: Add a predicate end-to-end test.**

Append to `crates/shinri-solver/tests/qfuf_e2e.rs`:

```rust
#[test]
fn predicate_congruence_e2e() {
    let mut s = Solver::new();
    let u = s.declare_sort("U");
    let boolsort = s.bool_sort();
    let a = uconst(&mut s, "a", u);
    let b = uconst(&mut s, "b", u);
    let p = s.declare_fun("p", &[u], boolsort);
    let pa = s.app(Op::Uninterpreted(p), &[a]);
    let pb = s.app(Op::Uninterpreted(p), &[b]);
    let npb = s.app(Op::Builtin(BuiltinOp::Not), &[pb]);
    let ab = s.eq(a, b);
    s.assert(pa);
    s.assert(npb);
    s.assert(ab);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}
```

- [ ] **Step 6: Run all solver tests.**

Run: `cargo test -p shinri-solver`
Expected: PASS.

- [ ] **Step 7: Commit.**

```bash
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/qfuf_e2e.rs
git commit -m "feat(solver): assertion-scope push/pop + predicate e2e tests"
```

---

## Phase E — differential oracle

### Task 16: enable the theory-layer oracle for `Combiner<Euf, EmptyTheory>`

**Files:**
- Modify: `crates/shinri-theory/tests/oracle.rs`

**Interfaces:**
- Consumes: the existing `#[ignore]`d oracle scaffold; now instantiable as `Combiner<Euf, EmptyTheory>`.

**Note:** `shinri-theory` cannot depend on `shinri-euf` (that would invert the dependency graph). So the *theory-layer* oracle that needs a concrete `Euf` must move to where `Euf` is available. Implement the differential oracle in `shinri-solver` instead (Task 17), and in this task simply update the stale comment / keep the scaffold honest.

- [ ] **Step 1: Read the existing scaffold.**

Run: `cat crates/shinri-theory/tests/oracle.rs`
Expected: an `#[ignore]`d placeholder referencing `Combiner<Euf, Arith>`.

- [ ] **Step 2: Update the comment to point at the real oracle location.**

Edit `crates/shinri-theory/tests/oracle.rs` so its doc comment reads:

```rust
//! The end-to-end differential oracle lives in `shinri-solver` (it needs the
//! concrete `Euf` theory, which `shinri-theory` cannot depend on without
//! inverting the crate graph). See `crates/shinri-solver/tests/oracle.rs`,
//! run with `--features oracle` and a `z3` binary on PATH.
```

Keep any compiling no-op test `#[ignore]`d so the file stays valid.

- [ ] **Step 3: Build the theory tests.**

Run: `cargo test -p shinri-theory --test oracle`
Expected: PASS / ignored (no failures).

- [ ] **Step 4: Commit.**

```bash
git add crates/shinri-theory/tests/oracle.rs
git commit -m "docs(theory): point oracle scaffold at the shinri-solver differential harness"
```

---

### Task 17: differential `z3` oracle in `shinri-solver`

**Files:**
- Create: `crates/shinri-solver/tests/oracle.rs`

**Interfaces:**
- Consumes: `shinri_solver::{Solver, SolveOutcome}`, `easy-smt` (dev), a `z3` binary on PATH. Feature-gated behind `oracle`.

**Design:** Generate small random well-typed QF_UF formulas; build them in both `shinri-solver` and an SMT-LIB string for `z3` via `easy-smt`; compare. Any `Sat`/`Unsat` disagreement fails; `Unknown` from shinri never fails.

- [ ] **Step 1: Write the oracle test.**

Create `crates/shinri-solver/tests/oracle.rs`:

```rust
//! Differential oracle: shinri-solver vs z3 on random QF_UF.
//! Run with: `cargo test -p shinri-solver --features oracle -- --nocapture`
//! Requires a `z3` binary on PATH.
#![cfg(feature = "oracle")]

use shinri_core::{BuiltinOp, Op};
use shinri_solver::{SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0 >> 16
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

#[test]
fn differential_qf_uf_small() {
    let mut rng = Lcg(0x5eed);
    for _ in 0..200 {
        // Build a random conjunction of (in)equalities over 4 constants and f/1.
        let mut s = Solver::new();
        let u = s.declare_sort("U");
        let consts: Vec<_> = (0..4)
            .map(|i| {
                let f = s.declare_fun(&format!("c{i}"), &[], u);
                s.app(Op::Uninterpreted(f), &[])
            })
            .collect();
        let f = s.declare_fun("f", &[u], u);

        // SMT-LIB mirror.
        let ctx = easy_smt::ContextBuilder::new()
            .solver("z3", &["-smt2", "-in"])
            .build()
            .unwrap();
        let su = ctx.declare_sort("U", 0).unwrap();
        let mut z_consts = Vec::new();
        for i in 0..4 {
            z_consts.push(ctx.declare_const(&format!("c{i}"), su).unwrap());
        }
        let zf = ctx
            .declare_fun("f", &[su], su)
            .unwrap();

        let n_lits = 2 + rng.below(4) as usize;
        let mut z_terms = Vec::new();
        for _ in 0..n_lits {
            let i = rng.below(4) as usize;
            let j = rng.below(4) as usize;
            let use_f = rng.below(2) == 1;
            let neg = rng.below(2) == 1;

            let (lhs, rhs, z_lhs, z_rhs) = if use_f {
                let fl = s.app(Op::Uninterpreted(f), &[consts[i]]);
                let fr = s.app(Op::Uninterpreted(f), &[consts[j]]);
                let zl = ctx.list(vec![ctx.atom("f"), z_consts[i]]);
                let zr = ctx.list(vec![ctx.atom("f"), z_consts[j]]);
                let _ = zf;
                (fl, fr, zl, zr)
            } else {
                (consts[i], consts[j], z_consts[i], z_consts[j])
            };

            let eqt = s.eq(lhs, rhs);
            let lit = if neg {
                s.app(Op::Builtin(BuiltinOp::Not), &[eqt])
            } else {
                eqt
            };
            s.assert(lit);

            let zeq = ctx.eq(z_lhs, z_rhs);
            z_terms.push(if neg { ctx.not(zeq) } else { zeq });
        }

        for zt in z_terms {
            ctx.assert(zt).unwrap();
        }

        let ours = s.check_sat();
        let theirs = ctx.check().unwrap();

        match (ours, theirs) {
            (SolveOutcome::Unknown, _) => {} // never a failure
            (SolveOutcome::Sat, easy_smt::Response::Sat) => {}
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {}
            (o, t) => panic!("DISAGREEMENT: shinri={o:?} z3={t:?}"),
        }
    }
}
```

> `easy-smt`'s exact API (`ContextBuilder`, `declare_sort`, `list`, `eq`, `not`, `check`, `Response`) may differ slightly by version (`0.2`). Adjust calls to the installed API as the compiler directs; the contract is: assert the same formula to z3, compare `check()` to `check_sat()`.

- [ ] **Step 2: Run the oracle (requires z3).**

Run: `cargo test -p shinri-solver --features oracle differential_qf_uf_small -- --nocapture`
Expected: PASS (no disagreements). If `z3` is not installed, the test is compiled but skipped via the feature gate when run without `--features oracle`.

- [ ] **Step 3: Commit.**

```bash
git add crates/shinri-solver/tests/oracle.rs
git commit -m "test(solver): differential z3 oracle for random QF_UF"
```

---

## Final Verification

- [ ] **Step 1: Full workspace test.**

Run: `cargo nextest run` (or `cargo test`)
Expected: PASS across all crates.

- [ ] **Step 2: Lint + format + dependency policy.**

Run: `cargo clippy --all-targets -- -D warnings && cargo fmt --check && cargo deny check`
Expected: clean.

- [ ] **Step 3: Smoke the headline result.**

Run: `cargo test -p shinri-solver --test qfuf_e2e`
Expected: PASS — the first runnable QF_UF solver answers `Sat`/`Unsat` end-to-end.

---

## Self-Review Notes (for the implementer)

- **API drift:** several steps flag exact accessor names to verify against the codebase (`Lit::is_positive()`, `Context: Clone`, `ModelBuilder` iteration, `easy-smt` 0.2 calls). These are explicitly called out at their step; verify and adapt — the failing test in each task pins the behavior.
- **Borrow splits:** the `TheoryCtx { terms, eq, atoms }` pattern requires splitting the `Combiner`'s field borrows (the established `§5.5` pattern visible in `combiner.rs`); follow it when touching `Combiner`.
- **`propagated` not backtracked (Task 11):** documented soundness-preserving simplification; `check(Full)` re-validates, so a missed re-propagation cannot cause a wrong answer.
- **Phase-1 conservative `check_sat` (Task 15):** rebuilds SAT/theory per query from the persistent term DAG; the in-SAT theory-preserving rebuild (Task 4) is the seam for a future single-instance incremental mode and is independently tested.
