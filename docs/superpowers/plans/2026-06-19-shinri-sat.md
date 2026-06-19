# shinri-sat Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `shinri-sat`, the CDCL(T)-ready SAT search engine of the shinri SMT solver: clause database, two-watched-literals propagation, 1-UIP conflict-driven learning, branching (VMTF + EVSIDS), restarts, LBD-based reduction, incremental solving with assumptions, and the zero-cost `Theory`/`ProofSink` seams.

**Architecture:** One crate depending only on `shinri-core`. State lives in focused, independently-testable units (`Assignment`, `Trail`, `ClauseDb`, `Watches`); a thin `Solver<T: Theory, P: ProofSink, H: BranchHeuristic>` orchestrator runs the CDCL(T) loop. Everything is `u32`-indexed flat `Vec`s (arena mandate); binary clauses live implicitly in the watch lists; the theory/proof/heuristic seams are generic type parameters so they monomorphize away when off (`NoTheory`/`NoProof`).

**Tech Stack:** Rust 2021, toolchain `1.96.0`. Runtime deps: `shinri-core` (workspace). Dev-only: `proptest`, and `splr` as a differential SAT oracle.

## Global Constraints

- **Rust edition:** `2021`. Toolchain pinned to `1.96.0` (workspace `rust-version`).
- **Crate license:** `MIT OR Apache-2.0` (permissive — design spec §2).
- **Runtime dependencies are `shinri-core` only.** No native-link crate (enforced by workspace `deny.toml`). `proptest` and `splr` are `[dev-dependencies]` only; the DIMACS reader is `#[cfg(any(test, feature = "dimacs"))]` so the shipping library carries no parser weight.
- **No floating point on the decision path except EVSIDS activities.** VMTF is integer-only; a fixed `random_seed` makes runs bit-reproducible (spec §2, §10).
- **Ids are `Copy`, `#[repr(transparent)]`** and come from `shinri-core`: `Var`/`Lit`/`ClauseId` wrap `u32`; `Lit` packs `var << 1 | sign`.
- **Soundness discipline (spec §9):** resource exhaustion → `unknown`; recoverable input errors (malformed DIMACS) return `Result`, never panic; `debug_assert!` guards hot invariants (trail consistency, watched-literal invariants, decision-level monotonicity); panics reserved for genuine invariant violations. Every `Sat` is re-validated against all clauses before return; every `Unsat` carries a checkable certificate.
- **Monomorphization on the hot path:** generic over `T: Theory`, `P: ProofSink`, `H: BranchHeuristic`; no `dyn` dispatch anywhere in the solve loop.
- **`unsafe` is confined to two justified spots.** (1) `ClauseDb::lits` (Task 4) returns a zero-copy `&[Lit]` view over the `&[u32]` literal codes — sound because `Lit` is `#[repr(transparent)]` over `u32`. (2) Optionally, audited `get_unchecked` in the BCP inner loop (Task 7, deferred until profiling justifies it) — spec §5.2. No other `unsafe`; both are small, individually justified, and guarded by `debug_assert!`-checked invariants.
- **Commit after every green step.** Branch is `feat/shinri-sat-design` (already created for the spec); implementation commits land here.

## File Structure

| File | Responsibility |
|------|----------------|
| `crates/shinri-sat/Cargo.toml` | crate manifest; deps `shinri-core`, dev-deps `proptest`/`splr` |
| `src/lib.rs` | crate root, re-exports, top-level docs |
| `src/types.rs` | `LBool`, `Reason`, `Conflict`, `SolveResult`, `Effort`, `TheoryResult` |
| `src/config.rs` | `SolverConfig`, `RestartKind` |
| `src/assignment.rs` | `Assignment`: per-var value/level/reason/phase |
| `src/trail.rs` | `Trail`: assignment stack + decision-level markers |
| `src/clause.rs` | `ClauseDb`: packed `u32` arena, `ClauseRef`, `ClauseId` map |
| `src/watch.rs` | `Watches`: 2WL with inline blocking lit + implicit binaries |
| `src/analyze.rs` | 1-UIP analysis + recursive minimization |
| `src/heuristic/mod.rs` | `BranchHeuristic` trait + phase saving glue |
| `src/heuristic/vmtf.rs` | VMTF impl |
| `src/heuristic/evsids.rs` | EVSIDS impl |
| `src/restart.rs` | `RestartPolicy`: Luby + Glucose-EMA |
| `src/reduce.rs` | LBD computation + clause-DB reduction |
| `src/theory.rs` | `Theory` trait (the T seam) + `NoTheory` ZST |
| `src/solver.rs` | `Solver<T, P, H>`: orchestrator + CDCL(T) loop, assumptions, push/pop |
| `src/dimacs.rs` | `#[cfg]`-gated DIMACS reader |
| `src/certificate.rs` | `#[cfg(test)]` from-scratch resolution/DRAT checker |
| `tests/props.rs` | proptest invariants (model soundness, entailment, core minimality) |
| `tests/oracle.rs` | differential vs `splr` across configs |
| `fuzz/fuzz_targets/*.rs` | DIMACS no-panic, structured-CNF-vs-oracle, incremental sequence |

Also modifies `Cargo.toml` (workspace root, add member) and `crates/shinri-core/src/ids.rs` (add `Lit::code`/`Lit::from_code` raw accessors the SAT layer needs to pack literals into the arena and index watch lists).

---

### Task 1: Crate scaffold, core raw-lit accessors, leaf types

**Files:**
- Modify: `Cargo.toml` (workspace root — add member)
- Modify: `crates/shinri-core/src/ids.rs` (add `Lit::code`/`Lit::from_code`)
- Create: `crates/shinri-sat/Cargo.toml`
- Create: `crates/shinri-sat/src/lib.rs`
- Create: `crates/shinri-sat/src/types.rs`
- Create: `crates/shinri-sat/src/config.rs`
- Test: inline `#[cfg(test)]` modules

**Interfaces:**
- Consumes: `shinri_core::{Var, Lit, ClauseId, TheoryJust}`.
- Produces:
  - `shinri_core::Lit::code(self) -> u32` (raw packed value), `Lit::from_code(u32) -> Lit`.
  - `shinri_sat::types::LBool` (`True | False | Unset`) with `LBool::from_bool(bool) -> LBool` and `negate(self) -> LBool`.
  - `shinri_sat::clause::ClauseRef(u32)` — *defined in Task 4*; here `types.rs` only forward-refers via re-export, so `Reason`/`Conflict` are defined in Task 4 alongside `ClauseRef` to avoid a forward dependency. (This task defines `LBool`, `Effort`, `TheoryResult`, `SolveResult`; `Reason`/`Conflict` move to Task 4.)
  - `shinri_sat::types::{Effort, TheoryResult, SolveResult}`.
  - `shinri_sat::config::{SolverConfig, RestartKind}`.

- [ ] **Step 1: Add the crate to the workspace**

Modify `Cargo.toml` (workspace root) so `members` reads:

```toml
[workspace]
resolver = "2"
members = ["crates/shinri-num", "crates/shinri-core", "crates/shinri-sat"]

[workspace.package]
edition = "2021"
license = "MIT OR Apache-2.0"
rust-version = "1.96.0"
```

- [ ] **Step 2: Add raw-lit accessors to `shinri-core`**

In `crates/shinri-core/src/ids.rs`, inside `impl Lit { ... }` (after `negate`), add:

```rust
    /// The raw packed code (`var << 1 | sign`). Lets the SAT layer pack
    /// literals into the clause arena and index watch lists by `code as usize`.
    #[inline]
    pub fn code(self) -> u32 {
        self.0
    }
    /// Reconstruct a literal from its raw packed code.
    #[inline]
    pub fn from_code(code: u32) -> Lit {
        Lit(code)
    }
```

- [ ] **Step 3: Write the failing test for the new accessors**

In `crates/shinri-core/src/ids.rs`, add to the existing `#[cfg(test)] mod tests`:

```rust
    #[test]
    fn lit_code_roundtrips() {
        let v = Var::new(9);
        let l = Lit::new(v, false);
        assert_eq!(Lit::from_code(l.code()), l);
        assert_eq!(Lit::new(v, true).code() ^ 1, l.code()); // sign bit toggles
    }
```

- [ ] **Step 4: Run it to verify it fails, then passes**

Run: `cargo test -p shinri-core lit_code_roundtrips`
Expected: compiles and PASSES once Step 2 is in (if you wrote the test before the impl, it fails to compile with "no function `code`").

- [ ] **Step 5: Create `crates/shinri-sat/Cargo.toml`**

```toml
[package]
name = "shinri-sat"
version = "0.1.0"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[features]
# Exposes the DIMACS reader in non-test builds (e.g. a future standalone CLI).
dimacs = []

[dependencies]
shinri-core = { path = "../shinri-core" }

[dev-dependencies]
proptest = "1"
splr = "0.17"
```

- [ ] **Step 6: Create `crates/shinri-sat/src/lib.rs`**

```rust
//! shinri-sat: the CDCL(T)-ready SAT search engine of the shinri SMT solver.
//!
//! Clause database, two-watched-literals propagation, 1-UIP learning,
//! branching, restarts, incremental assumptions, and the zero-cost
//! `Theory`/`ProofSink` seams. Depends only on `shinri-core`.

pub mod config;
pub mod types;

pub use config::{RestartKind, SolverConfig};
pub use types::{Effort, LBool, SolveResult, TheoryResult};

// Re-export the core vocabulary so downstream crates and integration tests can
// name these types via `shinri_sat::` without depending on `shinri-core`
// directly (integration tests cannot see a crate's regular dependencies).
pub use shinri_core::{ClauseId, Lit, NoProof, ProofSink, TheoryJust, Var};
```

- [ ] **Step 7: Create `crates/shinri-sat/src/types.rs` with `LBool` and result enums**

```rust
use shinri_core::Lit;

/// A three-valued Boolean: the value of a variable on the current trail.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LBool {
    True,
    False,
    Unset,
}

impl LBool {
    #[inline]
    pub fn from_bool(b: bool) -> LBool {
        if b {
            LBool::True
        } else {
            LBool::False
        }
    }
    /// Flip True<->False; Unset stays Unset.
    #[inline]
    pub fn negate(self) -> LBool {
        match self {
            LBool::True => LBool::False,
            LBool::False => LBool::True,
            LBool::Unset => LBool::Unset,
        }
    }
}

/// The effort a theory `check` is asked for (spec §8.1).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Effort {
    Standard,
    Full,
}

/// The result of a theory consistency `check` (spec §8.1). `Conflict`/`Lemma`
/// carry literal sets the solver folds into conflict analysis.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TheoryResult {
    Sat,
    Conflict(Vec<Lit>),
    Lemma(Vec<Lit>),
}

/// The outcome of a solve. `Unsat.core` is the failed-assumption set
/// (empty for an unconditional UNSAT) — spec §7.2.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SolveResult {
    Sat,
    Unsat { core: Vec<Lit> },
}
```

- [ ] **Step 8: Write the failing test for `LBool`**

In `types.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lbool_negate_and_from_bool() {
        assert_eq!(LBool::from_bool(true), LBool::True);
        assert_eq!(LBool::True.negate(), LBool::False);
        assert_eq!(LBool::Unset.negate(), LBool::Unset);
    }
}
```

- [ ] **Step 9: Create `crates/shinri-sat/src/config.rs`**

```rust
/// Which restart schedule the solver runs (spec §6.2). Selected at runtime
/// (the restart policy is consulted only once per conflict — too cold to
/// warrant a generic, unlike the branching heuristic).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RestartKind {
    /// Luby sequence — deterministic, theory-friendly.
    Luby,
    /// Glucose-style EMA on learnt-clause LBD.
    EmaGlucose,
}

/// Runtime tuning knobs. The branching heuristic is NOT here — it is the
/// generic type parameter `H` of `Solver`, fixed at construction (spec §8.4).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SolverConfig {
    pub restart: RestartKind,
    pub reduce_interval: u32,
    pub lbd_keep_threshold: u32,
    pub random_seed: u64,
}

impl Default for SolverConfig {
    fn default() -> Self {
        SolverConfig {
            restart: RestartKind::Luby,
            reduce_interval: 2000,
            lbd_keep_threshold: 2,
            random_seed: 0,
        }
    }
}
```

- [ ] **Step 10: Run the whole crate's tests**

Run: `cargo test -p shinri-sat`
Expected: compiles; `lbool_negate_and_from_bool` PASSES.

- [ ] **Step 11: Commit**

```bash
git add Cargo.toml crates/shinri-core/src/ids.rs crates/shinri-sat
git commit -m "feat(sat): crate scaffold, Lit raw accessors, LBool + config leaf types"
```

---

### Task 2: `Assignment` — per-var value / level / reason / phase

**Files:**
- Create: `crates/shinri-sat/src/assignment.rs`
- Modify: `crates/shinri-sat/src/lib.rs` (add `pub mod assignment;`)
- Test: inline `#[cfg(test)]` in `assignment.rs`

**Interfaces:**
- Consumes: `shinri_core::{Var, Lit, TheoryJust}`, `crate::types::LBool`. To keep every type defined before use, this task first creates a minimal `clause.rs` containing only `pub struct ClauseRef(pub u32)` (the full `ClauseDb` arrives in Task 4), then defines `Reason` in `types.rs` (referencing `ClauseRef`), then `Assignment` in `assignment.rs`.
- Produces:
  - `crate::clause::ClauseRef(pub u32)` with `ClauseRef::index(self) -> usize`.
  - `crate::types::Reason` (`Decision | Unit | Clause(ClauseRef) | Binary(Lit) | Theory(TheoryJust)`).
  - `crate::assignment::Assignment` with:
    - `new() -> Assignment`, `num_vars(&self) -> usize`, `new_var(&mut self) -> Var`
    - `value(&self, Var) -> LBool`, `lit_value(&self, Lit) -> LBool`
    - `level(&self, Var) -> u32`, `reason(&self, Var) -> Reason`, `phase(&self, Var) -> bool`
    - `assign(&mut self, Lit, level: u32, reason: Reason)`, `unassign(&mut self, Var)`

- [ ] **Step 1: Create `crates/shinri-sat/src/clause.rs` with just `ClauseRef`**

```rust
/// A reference to a clause: an offset into the `ClauseDb` arena (Task 4).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ClauseRef(pub u32);

impl ClauseRef {
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}
```

- [ ] **Step 2: Add `Reason` to `crates/shinri-sat/src/types.rs`**

Add these imports at the top of `types.rs` (alongside `use shinri_core::Lit;`):

```rust
use shinri_core::TheoryJust;
use crate::clause::ClauseRef;
```

Then add:

```rust
/// The antecedent of a trail assignment: why a variable holds its value.
/// The resolution backbone for both conflict analysis and the proof chain.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Reason {
    /// A branching decision or an assumption.
    Decision,
    /// A top-level unit clause (asserted at level 0).
    Unit,
    /// A longer clause became unit under the current trail.
    Clause(ClauseRef),
    /// Implied by an implicit binary clause; the literal is the *other* literal.
    Binary(Lit),
    /// A theory propagation; the explanation is recomputed lazily (spec §8.1).
    Theory(TheoryJust),
}
```

Re-export from `lib.rs`: change the `pub use types::...` line to include `Reason`, and add `pub mod clause;`:

```rust
pub mod clause;
pub mod assignment;
pub mod config;
pub mod types;

pub use config::{RestartKind, SolverConfig};
pub use types::{Effort, LBool, Reason, SolveResult, TheoryResult};
```

- [ ] **Step 3: Write the failing test for `Assignment`**

Create `crates/shinri-sat/src/assignment.rs`:

```rust
use crate::types::{LBool, Reason};
use shinri_core::{Lit, Var};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assign_sets_value_level_phase_then_unassign_clears_value_keeps_phase() {
        let mut a = Assignment::new();
        let v = a.new_var();
        assert_eq!(a.value(v), LBool::Unset);

        let l = Lit::new(v, false); // negative literal
        a.assign(l, 3, Reason::Decision);
        assert_eq!(a.value(v), LBool::False);
        assert_eq!(a.lit_value(l), LBool::True); // the literal itself is satisfied
        assert_eq!(a.level(v), 3);
        assert_eq!(a.reason(v), Reason::Decision);
        assert_eq!(a.phase(v), false);

        a.unassign(v);
        assert_eq!(a.value(v), LBool::Unset);
        assert_eq!(a.phase(v), false); // phase is remembered for phase-saving
    }
}
```

- [ ] **Step 4: Run it to verify it fails**

Run: `cargo test -p shinri-sat assign_sets_value -- --nocapture`
Expected: FAIL to compile — `Assignment` not defined.

- [ ] **Step 5: Implement `Assignment`**

Above the `#[cfg(test)]` module in `assignment.rs`:

```rust
/// Per-variable solver state, struct-of-arrays, indexed by `Var::index()`.
pub struct Assignment {
    value: Vec<LBool>,
    level: Vec<u32>,
    reason: Vec<Reason>,
    phase: Vec<bool>,
}

impl Default for Assignment {
    fn default() -> Self {
        Assignment::new()
    }
}

impl Assignment {
    pub fn new() -> Assignment {
        Assignment {
            value: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            phase: Vec::new(),
        }
    }

    #[inline]
    pub fn num_vars(&self) -> usize {
        self.value.len()
    }

    /// Allocate the next variable, defaulting to Unset / phase false.
    pub fn new_var(&mut self) -> Var {
        let v = Var::new(self.value.len() as u32);
        self.value.push(LBool::Unset);
        self.level.push(0);
        self.reason.push(Reason::Decision);
        self.phase.push(false);
        v
    }

    #[inline]
    pub fn value(&self, v: Var) -> LBool {
        self.value[v.index()]
    }

    /// The value of a literal: the var's value flipped if the literal is negative.
    #[inline]
    pub fn lit_value(&self, l: Lit) -> LBool {
        let v = self.value[l.var().index()];
        if l.is_positive() {
            v
        } else {
            v.negate()
        }
    }

    #[inline]
    pub fn level(&self, v: Var) -> u32 {
        self.level[v.index()]
    }

    #[inline]
    pub fn reason(&self, v: Var) -> Reason {
        self.reason[v.index()]
    }

    #[inline]
    pub fn phase(&self, v: Var) -> bool {
        self.phase[v.index()]
    }

    /// Record an assignment making `l` true at `level` with antecedent `reason`.
    #[inline]
    pub fn assign(&mut self, l: Lit, level: u32, reason: Reason) {
        let v = l.var();
        debug_assert_eq!(self.value[v.index()], LBool::Unset, "double-assign");
        self.value[v.index()] = LBool::from_bool(l.is_positive());
        self.level[v.index()] = level;
        self.reason[v.index()] = reason;
        self.phase[v.index()] = l.is_positive();
    }

    /// Clear a variable's value on backtrack, preserving its saved phase.
    #[inline]
    pub fn unassign(&mut self, v: Var) {
        self.value[v.index()] = LBool::Unset;
    }
}
```

- [ ] **Step 6: Run the test to verify it passes**

Run: `cargo test -p shinri-sat assign_sets_value`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): Assignment (value/level/reason/phase) + Reason/ClauseRef"
```

---

### Task 3: `Trail` — assignment stack + decision-level markers

**Files:**
- Create: `crates/shinri-sat/src/trail.rs`
- Modify: `crates/shinri-sat/src/lib.rs` (add `pub mod trail;`)
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `shinri_core::Lit`.
- Produces: `crate::trail::Trail` with:
  - `new() -> Trail`, `len(&self) -> usize`, `is_empty(&self) -> bool`
  - `decision_level(&self) -> u32`, `new_level(&mut self)`
  - `push(&mut self, Lit)`, `lit_at(&self, usize) -> Lit`
  - `qhead(&self) -> usize`, `set_qhead(&mut self, usize)`, `next_unpropagated(&mut self) -> Option<Lit>`
  - `backtrack_to(&mut self, level: u32, f: impl FnMut(Lit))` — replays popped lits newest-first (for un-assignment), truncates `qhead` to the new end.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-sat/src/trail.rs`:

```rust
use shinri_core::{Lit, Var};

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(n: u32) -> Lit {
        Lit::new(Var::new(n), true)
    }

    #[test]
    fn levels_push_and_backtrack_replays_newest_first() {
        let mut t = Trail::new();
        t.push(lit(0)); // level 0
        assert_eq!(t.decision_level(), 0);

        t.new_level();
        t.push(lit(1));
        t.push(lit(2)); // level 1: [1,2]
        t.new_level();
        t.push(lit(3)); // level 2: [3]
        assert_eq!(t.decision_level(), 2);
        assert_eq!(t.len(), 4);

        let mut undone = Vec::new();
        t.backtrack_to(1, |l| undone.push(l));
        assert_eq!(undone, vec![lit(3)]); // only level 2 unwound
        assert_eq!(t.decision_level(), 1);

        undone.clear();
        t.backtrack_to(0, |l| undone.push(l));
        assert_eq!(undone, vec![lit(2), lit(1)]); // LIFO
        assert_eq!(t.decision_level(), 0);
        assert_eq!(t.len(), 1); // level-0 lit(0) survives
    }

    #[test]
    fn qhead_walks_then_stops() {
        let mut t = Trail::new();
        t.push(lit(5));
        t.push(lit(6));
        assert_eq!(t.next_unpropagated(), Some(lit(5)));
        assert_eq!(t.next_unpropagated(), Some(lit(6)));
        assert_eq!(t.next_unpropagated(), None);
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-sat -- trail`
Expected: FAIL — `Trail` not defined.

- [ ] **Step 3: Implement `Trail`**

Above the test module:

```rust
/// The stack of assigned literals in assignment order, plus decision-level
/// markers and the BCP cursor `qhead`. The SAT-specific undo (theories unwind
/// through their own `pop`, driven in lockstep with these levels).
pub struct Trail {
    lits: Vec<Lit>,
    level_starts: Vec<usize>, // level_starts[i] = index where level i+1 began
    qhead: usize,
}

impl Default for Trail {
    fn default() -> Self {
        Trail::new()
    }
}

impl Trail {
    pub fn new() -> Trail {
        Trail { lits: Vec::new(), level_starts: Vec::new(), qhead: 0 }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    #[inline]
    pub fn decision_level(&self) -> u32 {
        self.level_starts.len() as u32
    }

    /// Open a new decision level at the current trail height.
    #[inline]
    pub fn new_level(&mut self) {
        self.level_starts.push(self.lits.len());
    }

    #[inline]
    pub fn push(&mut self, l: Lit) {
        self.lits.push(l);
    }

    #[inline]
    pub fn lit_at(&self, i: usize) -> Lit {
        self.lits[i]
    }

    #[inline]
    pub fn qhead(&self) -> usize {
        self.qhead
    }

    #[inline]
    pub fn set_qhead(&mut self, q: usize) {
        self.qhead = q;
    }

    /// The next literal awaiting propagation, advancing the cursor.
    #[inline]
    pub fn next_unpropagated(&mut self) -> Option<Lit> {
        if self.qhead < self.lits.len() {
            let l = self.lits[self.qhead];
            self.qhead += 1;
            Some(l)
        } else {
            None
        }
    }

    /// Unwind every literal assigned above decision `level`, newest-first,
    /// passing each to `f` (the caller un-assigns it). `qhead` is clamped so
    /// propagation resumes from the truncated end.
    pub fn backtrack_to(&mut self, level: u32, mut f: impl FnMut(Lit)) {
        debug_assert!(level <= self.decision_level(), "backtrack above current level");
        let target_len = if (level as usize) < self.level_starts.len() {
            self.level_starts[level as usize]
        } else {
            self.lits.len()
        };
        while self.lits.len() > target_len {
            f(self.lits.pop().unwrap());
        }
        self.level_starts.truncate(level as usize);
        if self.qhead > self.lits.len() {
            self.qhead = self.lits.len();
        }
    }
}
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p shinri-sat -- trail`
Expected: both PASS.

- [ ] **Step 5: Wire the module and commit**

Add `pub mod trail;` to `lib.rs`.

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): Trail (assignment stack + decision-level backtracking)"
```

---

### Task 4: `ClauseDb` — packed `u32` arena with stable `ClauseId`

**Files:**
- Modify: `crates/shinri-sat/src/clause.rs` (extend the Task-2 stub with `ClauseDb`)
- Modify: `crates/shinri-sat/src/lib.rs` (`pub use clause::{ClauseDb, ClauseRef};`)
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `shinri_core::{Lit, ClauseId}`, `crate::clause::ClauseRef`.
- Produces: `crate::clause::ClauseDb` with:
  - `new() -> ClauseDb`
  - `add_clause(&mut self, lits: &[Lit], learnt: bool) -> (ClauseId, ClauseRef)`
  - `lits(&self, ClauseRef) -> &[Lit]`
  - `len_of(&self, ClauseRef) -> usize`
  - `is_learnt(&self, ClauseRef) -> bool`, `lbd(&self, ClauseRef) -> u32`, `set_lbd(&mut self, ClauseRef, u32)`
  - `clause_id(&self, ClauseRef) -> ClauseId`
  - `ref_of(&self, ClauseId) -> ClauseRef` (stable-id → live-ref lookup, survives relocation)
  - `num_clauses(&self) -> usize`

Header layout at arena offset `off`: `[id:u32][meta:u32][len:u32][lit0..litN]`, where `meta = (learnt as u32) << 31 | (lbd & 0x7FFF_FFFF)`, and each literal is stored as `Lit::code()`. Literals begin at `off + 3`.

- [ ] **Step 1: Write the failing test**

Append to `crates/shinri-sat/src/clause.rs` a test module:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Lit, Var};

    fn lit(n: u32, pos: bool) -> Lit {
        Lit::new(Var::new(n), pos)
    }

    #[test]
    fn add_then_read_back_lits_flags_and_stable_id() {
        let mut db = ClauseDb::new();
        let ls = [lit(0, true), lit(1, false), lit(2, true)];
        let (id0, r0) = db.add_clause(&ls, false);
        let (id1, r1) = db.add_clause(&[lit(3, true), lit(4, true)], true);

        assert_eq!(db.lits(r0), &ls);
        assert_eq!(db.len_of(r0), 3);
        assert_eq!(db.is_learnt(r0), false);
        assert_eq!(db.is_learnt(r1), true);

        db.set_lbd(r1, 2);
        assert_eq!(db.lbd(r1), 2);

        // Stable ids map to current refs.
        assert_eq!(db.clause_id(r0), id0);
        assert_eq!(db.ref_of(id0), r0);
        assert_eq!(db.ref_of(id1), r1);
        assert_eq!(db.num_clauses(), 2);
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-sat -- clause::tests`
Expected: FAIL — `ClauseDb` not defined.

- [ ] **Step 3: Implement `ClauseDb`**

Add to `clause.rs` (keep the existing `ClauseRef` from Task 2):

```rust
use shinri_core::{ClauseId, Lit};

const HEADER_WORDS: usize = 3;
const LEARNT_BIT: u32 = 1 << 31;
const LBD_MASK: u32 = 0x7FFF_FFFF;

/// The clause database: one flat `u32` arena. Binary clauses are NOT stored
/// here — they live implicitly in the watch lists (Task 6).
pub struct ClauseDb {
    arena: Vec<u32>,
    /// `id_to_ref[id.index()]` = the live `ClauseRef` for stable `ClauseId`.
    /// Updated on relocation (Task 11) so `ClauseId` stays stable for proofs.
    id_to_ref: Vec<ClauseRef>,
}

impl Default for ClauseDb {
    fn default() -> Self {
        ClauseDb::new()
    }
}

impl ClauseDb {
    pub fn new() -> ClauseDb {
        ClauseDb { arena: Vec::new(), id_to_ref: Vec::new() }
    }

    pub fn add_clause(&mut self, lits: &[Lit], learnt: bool) -> (ClauseId, ClauseRef) {
        let off = self.arena.len() as u32;
        let r = ClauseRef(off);
        let id = ClauseId::new(self.id_to_ref.len() as u32);
        self.id_to_ref.push(r);

        self.arena.push(id.index() as u32); // [id]
        self.arena.push(if learnt { LEARNT_BIT } else { 0 }); // [meta]
        self.arena.push(lits.len() as u32); // [len]
        for &l in lits {
            self.arena.push(l.code());
        }
        (id, r)
    }

    #[inline]
    fn off(&self, r: ClauseRef) -> usize {
        r.index()
    }

    #[inline]
    pub fn len_of(&self, r: ClauseRef) -> usize {
        self.arena[self.off(r) + 2] as usize
    }

    #[inline]
    pub fn lits(&self, r: ClauseRef) -> &[Lit] {
        let off = self.off(r);
        let len = self.arena[off + 2] as usize;
        let start = off + HEADER_WORDS;
        let codes = &self.arena[start..start + len];
        // SAFETY: `Lit` is `#[repr(transparent)]` over `u32` (verified in
        // shinri-core), so a slice of literal codes is layout-identical to a
        // slice of `Lit`. This is a zero-copy view, not a transmute of owned
        // data. The single justified `unsafe` block in the clause module.
        unsafe { std::slice::from_raw_parts(codes.as_ptr() as *const Lit, len) }
    }

    #[inline]
    pub fn is_learnt(&self, r: ClauseRef) -> bool {
        self.arena[self.off(r) + 1] & LEARNT_BIT != 0
    }

    #[inline]
    pub fn lbd(&self, r: ClauseRef) -> u32 {
        self.arena[self.off(r) + 1] & LBD_MASK
    }

    #[inline]
    pub fn set_lbd(&mut self, r: ClauseRef, lbd: u32) {
        let off = self.off(r);
        let learnt = self.arena[off + 1] & LEARNT_BIT;
        self.arena[off + 1] = learnt | (lbd & LBD_MASK);
    }

    #[inline]
    pub fn clause_id(&self, r: ClauseRef) -> ClauseId {
        ClauseId::new(self.arena[self.off(r)])
    }

    #[inline]
    pub fn ref_of(&self, id: ClauseId) -> ClauseRef {
        self.id_to_ref[id.index()]
    }

    #[inline]
    pub fn num_clauses(&self) -> usize {
        self.id_to_ref.len()
    }
}
```

**Note:** `lits` is the only `unsafe` in the clause module (see the Global Constraints justification). `lit_at` (added in Task 7) is the safe single-element accessor used inside the BCP loop.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cargo test -p shinri-sat -- clause::tests`
Expected: PASS.

- [ ] **Step 5: Wire re-exports and commit**

In `lib.rs`: `pub use clause::{ClauseDb, ClauseRef};`

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): ClauseDb packed u32 arena with stable ClauseId mapping"
```

---

### Task 5: DIMACS reader (test/feature-gated)

**Files:**
- Create: `crates/shinri-sat/src/dimacs.rs`
- Modify: `crates/shinri-sat/src/lib.rs` (gated `pub mod dimacs;`)
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `shinri_core::{Lit, Var}`.
- Produces (only under `#[cfg(any(test, feature = "dimacs"))]`):
  - `crate::dimacs::Cnf { pub num_vars: usize, pub clauses: Vec<Vec<Lit>> }`
  - `crate::dimacs::parse_dimacs(&str) -> Result<Cnf, String>`

DIMACS: lines starting `c` are comments; one `p cnf <vars> <clauses>` header; each clause is whitespace-separated nonzero ints terminated by `0`. A positive int `n` is `Var::new(n-1)` positive; `-n` is negative.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-sat/src/dimacs.rs`:

```rust
use shinri_core::{Lit, Var};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_comments_header_and_clauses() {
        let src = "c example\np cnf 3 2\n1 -2 0\n2 3 0\n";
        let cnf = parse_dimacs(src).unwrap();
        assert_eq!(cnf.num_vars, 3);
        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.clauses[0], vec![Lit::new(Var::new(0), true), Lit::new(Var::new(1), false)]);
        assert_eq!(cnf.clauses[1], vec![Lit::new(Var::new(1), true), Lit::new(Var::new(2), true)]);
    }

    #[test]
    fn rejects_var_out_of_range() {
        let src = "p cnf 1 1\n2 0\n";
        assert!(parse_dimacs(src).is_err());
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-sat -- dimacs`
Expected: FAIL — `parse_dimacs` not defined.

- [ ] **Step 3: Implement the reader**

Above the test module:

```rust
/// A parsed CNF formula.
pub struct Cnf {
    pub num_vars: usize,
    pub clauses: Vec<Vec<Lit>>,
}

/// Parse DIMACS CNF. Returns `Err(msg)` on malformed input — never panics
/// (spec §9). Variables are 1-based in DIMACS, 0-based as `Var`.
pub fn parse_dimacs(src: &str) -> Result<Cnf, String> {
    let mut num_vars = 0usize;
    let mut clauses = Vec::new();
    let mut cur: Vec<Lit> = Vec::new();
    let mut saw_header = false;

    for line in src.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if let Some(rest) = line.strip_prefix("p cnf") {
            let mut it = rest.split_whitespace();
            num_vars = it
                .next()
                .ok_or("missing var count")?
                .parse()
                .map_err(|_| "bad var count")?;
            saw_header = true;
            continue;
        }
        for tok in line.split_whitespace() {
            let n: i64 = tok.parse().map_err(|_| format!("bad literal {tok}"))?;
            if n == 0 {
                clauses.push(std::mem::take(&mut cur));
            } else {
                let var0 = n.unsigned_abs() - 1;
                if var0 as usize >= num_vars {
                    return Err(format!("variable {} out of range", n.abs()));
                }
                cur.push(Lit::new(Var::new(var0 as u32), n > 0));
            }
        }
    }
    if !saw_header {
        return Err("missing p cnf header".into());
    }
    if !cur.is_empty() {
        clauses.push(cur);
    }
    Ok(Cnf { num_vars, clauses })
}
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-sat -- dimacs`
Expected: both PASS.

- [ ] **Step 5: Wire the gated module and commit**

In `lib.rs`:

```rust
#[cfg(any(test, feature = "dimacs"))]
pub mod dimacs;
```

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): test/feature-gated DIMACS reader"
```

---

### Task 6: `Watches` — 2WL with inline blocking lit + implicit binaries

**Files:**
- Create: `crates/shinri-sat/src/watch.rs`
- Modify: `crates/shinri-sat/src/lib.rs` (`pub mod watch;`)
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `shinri_core::Lit`, `crate::clause::ClauseRef`.
- Produces:
  - `crate::watch::WatchTarget` (`Clause(ClauseRef) | Binary`)
  - `crate::watch::Watch { pub target: WatchTarget, pub blocker: Lit }`
  - `crate::watch::Watches` with:
    - `new() -> Watches`, `ensure_vars(&mut self, num_vars: usize)`
    - `watch_clause(&mut self, r: ClauseRef, w0: Lit, w1: Lit)` — installs a long clause's two watches (blocker is the *other* watched lit)
    - `watch_binary(&mut self, a: Lit, b: Lit)` — installs implicit binary `(a ∨ b)`
    - `list(&self, l: Lit) -> &[Watch]`, `list_mut(&mut self, l: Lit) -> &mut Vec<Watch>`

The watch list for literal `l` is indexed by `l.code() as usize`; there are `2 * num_vars` lists. A clause watched on literals `w0,w1` registers, on the list of `¬w0`, a `Watch{Clause(r), blocker=w1}`, and symmetrically on `¬w1`. (A watch fires when its index literal becomes *false*.) An implicit binary `(a ∨ b)` registers `Watch{Binary, blocker=b}` on `¬a` and `Watch{Binary, blocker=a}` on `¬b`.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-sat/src/watch.rs`:

```rust
use crate::clause::ClauseRef;
use shinri_core::{Lit, Var};

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(n: u32, pos: bool) -> Lit {
        Lit::new(Var::new(n), pos)
    }

    #[test]
    fn binary_registers_on_negations_with_other_as_blocker() {
        let mut w = Watches::new();
        w.ensure_vars(2);
        let a = lit(0, true);
        let b = lit(1, true);
        w.watch_binary(a, b);
        // (a ∨ b): on ¬a we watch with blocker b; on ¬b blocker a.
        let la = w.list(a.negate());
        assert_eq!(la.len(), 1);
        assert_eq!(la[0].target, WatchTarget::Binary);
        assert_eq!(la[0].blocker, b);
        assert_eq!(w.list(b.negate())[0].blocker, a);
    }

    #[test]
    fn clause_watch_blocker_is_the_other_watched_lit() {
        let mut w = Watches::new();
        w.ensure_vars(3);
        let r = ClauseRef(0);
        let w0 = lit(0, true);
        let w1 = lit(1, true);
        w.watch_clause(r, w0, w1);
        let l = w.list(w0.negate());
        assert_eq!(l[0].target, WatchTarget::Clause(r));
        assert_eq!(l[0].blocker, w1);
        assert_eq!(w.list(w1.negate())[0].blocker, w0);
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-sat -- watch`
Expected: FAIL — types not defined.

- [ ] **Step 3: Implement `Watches`**

Above the test module:

```rust
/// What a watch points at. `Binary` means the clause IS `(blocker ∨ index-lit)`
/// and lives entirely in this entry — propagation never touches the arena.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WatchTarget {
    Clause(ClauseRef),
    Binary,
}

/// One watch-list entry: 8 bytes (a tagged `u32` plus the blocking literal).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Watch {
    pub target: WatchTarget,
    pub blocker: Lit,
}

/// Per-literal watch lists, indexed by `Lit::code()`. There are `2*num_vars`
/// lists. A watch on literal `l` fires when `l` becomes false.
pub struct Watches {
    lists: Vec<Vec<Watch>>,
}

impl Default for Watches {
    fn default() -> Self {
        Watches::new()
    }
}

impl Watches {
    pub fn new() -> Watches {
        Watches { lists: Vec::new() }
    }

    /// Grow to hold `2*num_vars` lists.
    pub fn ensure_vars(&mut self, num_vars: usize) {
        let needed = num_vars * 2;
        if self.lists.len() < needed {
            self.lists.resize_with(needed, Vec::new);
        }
    }

    #[inline]
    fn idx(l: Lit) -> usize {
        l.code() as usize
    }

    pub fn watch_clause(&mut self, r: ClauseRef, w0: Lit, w1: Lit) {
        self.lists[Self::idx(w0.negate())].push(Watch { target: WatchTarget::Clause(r), blocker: w1 });
        self.lists[Self::idx(w1.negate())].push(Watch { target: WatchTarget::Clause(r), blocker: w0 });
    }

    pub fn watch_binary(&mut self, a: Lit, b: Lit) {
        self.lists[Self::idx(a.negate())].push(Watch { target: WatchTarget::Binary, blocker: b });
        self.lists[Self::idx(b.negate())].push(Watch { target: WatchTarget::Binary, blocker: a });
    }

    #[inline]
    pub fn list(&self, l: Lit) -> &[Watch] {
        &self.lists[Self::idx(l)]
    }

    #[inline]
    pub fn list_mut(&mut self, l: Lit) -> &mut Vec<Watch> {
        &mut self.lists[Self::idx(l)]
    }
}
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-sat -- watch`
Expected: both PASS.

- [ ] **Step 5: Wire the module and commit**

Add `pub mod watch;` to `lib.rs`.

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): Watches (2WL + inline blocker + implicit binaries)"
```

---

### Task 7: `Solver` scaffold + clause installation + Boolean BCP

This task introduces the concrete `Solver` (no generics yet — they arrive in Tasks 13/17/18) and the hot propagation loop. After it, the crate can take clauses and propagate unit consequences to fixpoint or a conflict.

**Files:**
- Modify: `crates/shinri-sat/src/clause.rs` (add `lit_at`, `swap_lits`)
- Modify: `crates/shinri-sat/src/types.rs` (add `Conflict`)
- Create: `crates/shinri-sat/src/solver.rs`
- Modify: `crates/shinri-sat/src/lib.rs` (`pub mod solver;`, export `Conflict`, `Solver`)
- Test: inline `#[cfg(test)]` in `solver.rs`

**Interfaces:**
- Consumes: `Assignment`, `Trail`, `ClauseDb`, `Watches`, `SolverConfig`, `LBool`, `Reason`.
- Produces:
  - `crate::types::Conflict` (`Clause(ClauseRef) | Lits(Vec<Lit>)`).
  - `crate::clause::ClauseDb::lit_at(&self, ClauseRef, usize) -> Lit`, `swap_lits(&mut self, ClauseRef, usize, usize)`.
  - `crate::solver::Solver` with:
    - `new(config: SolverConfig) -> Solver`, `new_var(&mut self) -> Var`
    - `add_clause(&mut self, lits: &[Lit]) -> bool` (false ⇒ formula trivially UNSAT)
    - `is_unsat(&self) -> bool`
    - `enqueue(&mut self, Lit, Reason) -> bool` (false ⇒ literal already false)
    - `propagate(&mut self) -> Option<Conflict>`

- [ ] **Step 1: Add `Conflict` to `types.rs`**

```rust
use crate::clause::ClauseRef; // already imported in Task 2

/// A detected inconsistency: a stored clause, or a virtual clause (an implicit
/// binary, or — later — a theory conflict) given by its literal set.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Conflict {
    Clause(ClauseRef),
    Lits(Vec<Lit>),
}
```

Export from `lib.rs`: add `Conflict` to the `pub use types::{...}` list.

- [ ] **Step 2: Add `lit_at` / `swap_lits` to `ClauseDb`**

In `clause.rs`, inside `impl ClauseDb`:

```rust
    #[inline]
    pub fn lit_at(&self, r: ClauseRef, i: usize) -> Lit {
        Lit::from_code(self.arena[self.off(r) + HEADER_WORDS + i])
    }

    /// Swap two literals within a clause (used to keep watched lits at 0,1).
    #[inline]
    pub fn swap_lits(&mut self, r: ClauseRef, i: usize, j: usize) {
        let base = self.off(r) + HEADER_WORDS;
        self.arena.swap(base + i, base + j);
    }
```

- [ ] **Step 3: Write the failing BCP test**

Create `crates/shinri-sat/src/solver.rs`:

```rust
use crate::assignment::Assignment;
use crate::clause::ClauseDb;
use crate::config::SolverConfig;
use crate::trail::Trail;
use crate::types::{Conflict, LBool, Reason};
use crate::watch::{Watch, WatchTarget, Watches};
use shinri_core::{Lit, Var};

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(n: u32, pos: bool) -> Lit {
        Lit::new(Var::new(n), pos)
    }

    fn mk(n_vars: u32) -> Solver {
        let mut s = Solver::new(SolverConfig::default());
        for _ in 0..n_vars {
            s.new_var();
        }
        s
    }

    #[test]
    fn unit_then_binary_chain_propagates() {
        // (x0) , (¬x0 ∨ x1) , (¬x1 ∨ x2)  =>  x0,x1,x2 all true.
        let mut s = mk(3);
        assert!(s.add_clause(&[lit(0, true)]));
        assert!(s.add_clause(&[lit(0, false), lit(1, true)]));
        assert!(s.add_clause(&[lit(1, false), lit(2, true)]));
        assert!(s.propagate().is_none());
        assert_eq!(s.assign.value(Var::new(0)), LBool::True);
        assert_eq!(s.assign.value(Var::new(1)), LBool::True);
        assert_eq!(s.assign.value(Var::new(2)), LBool::True);
    }

    #[test]
    fn long_clause_becomes_unit_and_conflicts() {
        // Force all but one literal false in a ternary clause, then falsify it.
        // Clauses: (x0), (x1), (¬x0 ∨ ¬x1 ∨ x2), (¬x2)
        let mut s = mk(3);
        s.add_clause(&[lit(0, true)]);
        s.add_clause(&[lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, false), lit(2, true)]);
        s.add_clause(&[lit(2, false)]);
        // x0,x1 true => ternary forces x2 true; (¬x2) unit forces x2 false => conflict.
        let c = s.propagate();
        assert!(c.is_some(), "expected a conflict");
    }
}
```

- [ ] **Step 4: Run to verify it fails**

Run: `cargo test -p shinri-sat -- solver`
Expected: FAIL — `Solver` not defined.

- [ ] **Step 5: Implement the `Solver` scaffold + BCP**

Above the test module:

```rust
/// The CDCL search engine (concrete for now; generic params for theory, proof,
/// and heuristic are introduced in Tasks 13/17/18).
pub struct Solver {
    pub(crate) assign: Assignment,
    pub(crate) trail: Trail,
    pub(crate) db: ClauseDb,
    pub(crate) watches: Watches,
    pub(crate) config: SolverConfig,
    pub(crate) unsat: bool,
}

impl Solver {
    pub fn new(config: SolverConfig) -> Solver {
        Solver {
            assign: Assignment::new(),
            trail: Trail::new(),
            db: ClauseDb::new(),
            watches: Watches::new(),
            config,
            unsat: false,
        }
    }

    pub fn new_var(&mut self) -> Var {
        let v = self.assign.new_var();
        self.watches.ensure_vars(self.assign.num_vars());
        v
    }

    #[inline]
    pub fn is_unsat(&self) -> bool {
        self.unsat
    }

    /// Add an input clause at decision level 0. Returns false iff the formula
    /// is now trivially UNSAT (empty clause or a conflicting unit).
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        debug_assert_eq!(self.trail.decision_level(), 0, "add_clause only at level 0");
        match lits.len() {
            0 => {
                self.unsat = true;
                false
            }
            1 => {
                if self.enqueue(lits[0], Reason::Unit) {
                    true
                } else {
                    self.unsat = true;
                    false
                }
            }
            2 => {
                self.watches.watch_binary(lits[0], lits[1]);
                true
            }
            _ => {
                let (_id, r) = self.db.add_clause(lits, false);
                self.watches.watch_clause(r, lits[0], lits[1]);
                true
            }
        }
    }

    /// Try to make `l` true. Returns false if `l` is already false (a conflict).
    #[inline]
    pub fn enqueue(&mut self, l: Lit, reason: Reason) -> bool {
        match self.assign.lit_value(l) {
            LBool::True => true,
            LBool::False => false,
            LBool::Unset => {
                let level = self.trail.decision_level();
                self.assign.assign(l, level, reason);
                self.trail.push(l);
                true
            }
        }
    }

    /// Boolean constraint propagation to fixpoint. Returns the first conflict,
    /// or `None` if a fixpoint with no conflict is reached.
    pub fn propagate(&mut self) -> Option<Conflict> {
        while self.trail.qhead() < self.trail.len() {
            let p = self.trail.lit_at(self.trail.qhead());
            self.trail.set_qhead(self.trail.qhead() + 1);
            let false_lit = p.negate();

            // Inspect clauses watching `false_lit` (filed under `p`). Take the
            // list out so we can re-file moved watches into other lists.
            let watchers = std::mem::take(self.watches.list_mut(p));
            let mut keep: Vec<Watch> = Vec::with_capacity(watchers.len());
            let mut conflict: Option<Conflict> = None;
            let mut idx = 0;

            'watch: while idx < watchers.len() {
                let w = watchers[idx];
                idx += 1;

                // Blocker already satisfied => clause is true, keep untouched.
                if self.assign.lit_value(w.blocker) == LBool::True {
                    keep.push(w);
                    continue;
                }

                match w.target {
                    WatchTarget::Binary => {
                        keep.push(w);
                        match self.assign.lit_value(w.blocker) {
                            LBool::Unset => {
                                self.enqueue(w.blocker, Reason::Binary(false_lit));
                            }
                            LBool::False => {
                                conflict = Some(Conflict::Lits(vec![false_lit, w.blocker]));
                                break 'watch;
                            }
                            LBool::True => {}
                        }
                    }
                    WatchTarget::Clause(r) => {
                        // Keep watched lits at slots 0,1; put the false lit at 1.
                        if self.db.lit_at(r, 0) == false_lit {
                            self.db.swap_lits(r, 0, 1);
                        }
                        let other = self.db.lit_at(r, 0);
                        if other != w.blocker && self.assign.lit_value(other) == LBool::True {
                            keep.push(Watch { target: WatchTarget::Clause(r), blocker: other });
                            continue;
                        }
                        // Look for a replacement watch among slots 2..len.
                        let len = self.db.len_of(r);
                        let mut found = false;
                        for k in 2..len {
                            let lk = self.db.lit_at(r, k);
                            if self.assign.lit_value(lk) != LBool::False {
                                self.db.swap_lits(r, 1, k);
                                self.watches.list_mut(lk.negate()).push(Watch {
                                    target: WatchTarget::Clause(r),
                                    blocker: other,
                                });
                                found = true;
                                break;
                            }
                        }
                        if found {
                            continue; // clause leaves p's list
                        }
                        // No replacement: clause is unit (or conflicting) on `other`.
                        keep.push(Watch { target: WatchTarget::Clause(r), blocker: other });
                        match self.assign.lit_value(other) {
                            LBool::Unset => {
                                self.enqueue(other, Reason::Clause(r));
                            }
                            LBool::False => {
                                conflict = Some(Conflict::Clause(r));
                                break 'watch;
                            }
                            LBool::True => {}
                        }
                    }
                }
            }

            // Preserve any watchers not yet visited (after a conflict break).
            while idx < watchers.len() {
                keep.push(watchers[idx]);
                idx += 1;
            }
            *self.watches.list_mut(p) = keep;

            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }
}
```

**Performance note (deferred unsafe):** the spec permits audited `get_unchecked` in this loop. Implement it with safe indexing first (above); a later optimization pass may replace the hottest `self.db.lit_at` / watch-list accesses with `get_unchecked` inside `debug_assert!`-guarded blocks. Do NOT add `unsafe` until benchmarks justify it.

- [ ] **Step 6: Run to verify it passes**

Run: `cargo test -p shinri-sat -- solver`
Expected: both PASS.

- [ ] **Step 7: Wire and commit**

`lib.rs`: `pub mod solver;` and `pub use solver::Solver;`.

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): Solver scaffold + clause installation + Boolean BCP"
```

---

### Task 8: DPLL search — decide, backtrack, first SAT/UNSAT

This wires `decide` + chronological backtracking into a complete (if naive, non-learning) DPLL `solve`. **Task 9 replaces the search routine with CDCL learning** — this task exists to validate decide/backtrack/propagate end-to-end against known instances.

**Files:**
- Modify: `crates/shinri-sat/src/trail.rs` (add `level_start`)
- Modify: `crates/shinri-sat/src/solver.rs` (add `decide`, `backtrack_to`, `solve`)
- Test: inline `#[cfg(test)]` in `solver.rs`

**Interfaces:**
- Consumes: everything from Task 7, `crate::types::SolveResult`.
- Produces:
  - `crate::trail::Trail::level_start(&self, level: u32) -> usize` (1-based; trail index where `level` began).
  - `crate::solver::Solver`: `pick_branch(&self) -> Option<Lit>`, `backtrack_to(&mut self, u32)`, `solve(&mut self) -> SolveResult`.

- [ ] **Step 1: Add `level_start` to `Trail`**

In `trail.rs`, inside `impl Trail`:

```rust
    /// The trail index where decision `level` (1-based) began. Panics if
    /// `level == 0` (level 0 has no marker — it starts at index 0).
    #[inline]
    pub fn level_start(&self, level: u32) -> usize {
        self.level_starts[(level - 1) as usize]
    }
```

- [ ] **Step 2: Write the failing search test**

Add to the `tests` module in `solver.rs`:

```rust
    use crate::types::SolveResult;

    #[test]
    fn solves_satisfiable_2sat() {
        // (x0 ∨ x1) ∧ (¬x0 ∨ x1)  =>  SAT (x1 = true works).
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, true)]);
        assert_eq!(s.solve(), SolveResult::Sat);
    }

    #[test]
    fn detects_unsatisfiable_2sat() {
        // All four clauses over {x0,x1} => UNSAT.
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        s.add_clause(&[lit(0, true), lit(1, false)]);
        s.add_clause(&[lit(0, false), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, false)]);
        assert_eq!(s.solve(), SolveResult::Unsat { core: vec![] });
    }
```

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-sat -- solver`
Expected: FAIL — `solve` not defined.

- [ ] **Step 4: Implement `decide`, `backtrack_to`, `solve`**

Add to `impl Solver` (you'll need `use crate::types::SolveResult;` at the top of `solver.rs`):

```rust
    /// Pick an unassigned variable, branching on its saved phase (phase saving).
    /// Task 13 replaces this body with the `BranchHeuristic`.
    fn pick_branch(&self) -> Option<Lit> {
        for i in 0..self.assign.num_vars() {
            let v = Var::new(i as u32);
            if self.assign.value(v) == LBool::Unset {
                return Some(Lit::new(v, self.assign.phase(v)));
            }
        }
        None
    }

    /// Unwind the trail to `level`, un-assigning every popped literal.
    pub(crate) fn backtrack_to(&mut self, level: u32) {
        let assign = &mut self.assign;
        self.trail.backtrack_to(level, |l| assign.unassign(l.var()));
    }

    /// Naive DPLL search (no learning). Replaced by CDCL in Task 9.
    pub fn solve(&mut self) -> SolveResult {
        if self.unsat {
            return SolveResult::Unsat { core: vec![] };
        }
        loop {
            match self.propagate() {
                Some(_conflict) => {
                    let d = self.trail.decision_level();
                    if d == 0 {
                        self.unsat = true;
                        return SolveResult::Unsat { core: vec![] };
                    }
                    // Flip the current level's decision into the parent level.
                    let dec_lit = self.trail.lit_at(self.trail.level_start(d));
                    self.backtrack_to(d - 1);
                    self.enqueue(dec_lit.negate(), Reason::Unit);
                }
                None => match self.pick_branch() {
                    Some(l) => {
                        self.trail.new_level();
                        self.enqueue(l, Reason::Decision);
                    }
                    None => return SolveResult::Sat,
                },
            }
        }
    }
```

- [ ] **Step 5: Run to verify it passes**

Run: `cargo test -p shinri-sat -- solver`
Expected: all PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): DPLL search (decide + chronological backtrack), first SAT/UNSAT"
```

---

### Task 9: CDCL — 1-UIP conflict analysis, learning, backjump

Replaces the DPLL backtracking in `solve` with conflict-driven learning: analyze the conflict to a first-UIP asserting clause, backjump non-chronologically, install the learnt clause, and enqueue its asserting literal. This is the first true CDCL solver.

**Files:**
- Create: `crates/shinri-sat/src/analyze.rs`
- Modify: `crates/shinri-sat/src/solver.rs` (replace `solve` body; add `add_learnt`, `analyze` glue)
- Modify: `crates/shinri-sat/src/lib.rs` (`pub mod analyze;`)
- Test: inline `#[cfg(test)]` in `solver.rs` (re-run the Task 8 instances + a learning-specific case)

**Interfaces:**
- Consumes: `Solver` internals (`assign`, `trail`, `db`), `Conflict`, `Reason`.
- Produces:
  - `crate::analyze::Analyzer` (reusable scratch: `seen: Vec<bool>`, `learnt: Vec<Lit>`) with `ensure_vars(&mut self, usize)`.
  - `crate::solver::Solver`:
    - `conflict_lits(&self, &Conflict) -> Vec<Lit>` (the literals of a conflict, stored or virtual)
    - `analyze(&mut self, Conflict) -> (Vec<Lit>, u32)` — returns the learnt clause (asserting literal first) and the backjump level
    - `add_learnt(&mut self, &[Lit]) -> Option<ClauseRef>` (None for a unit learnt clause)

- [ ] **Step 1: Create `analyze.rs` with the scratch buffers**

```rust
use shinri_core::Var;

/// Reusable scratch for 1-UIP analysis, sized to the variable count so the
/// hot path allocates nothing per conflict.
pub struct Analyzer {
    /// Per-variable "seen in this analysis" marks.
    pub seen: Vec<bool>,
    /// The learnt clause being built.
    pub learnt: Vec<shinri_core::Lit>,
}

impl Default for Analyzer {
    fn default() -> Self {
        Analyzer { seen: Vec::new(), learnt: Vec::new() }
    }
}

impl Analyzer {
    pub fn ensure_vars(&mut self, n: usize) {
        if self.seen.len() < n {
            self.seen.resize(n, false);
        }
    }

    #[inline]
    pub fn clear_seen(&mut self, v: Var) {
        self.seen[v.index()] = false;
    }
}
```

Add `pub mod analyze;` to `lib.rs`, and add an `analyzer: Analyzer` field to `Solver` (initialize `Analyzer::default()` in `Solver::new`, and call `self.analyzer.ensure_vars(self.assign.num_vars())` in `new_var`). Add `use crate::analyze::Analyzer;` and `use crate::clause::ClauseRef;` to `solver.rs`.

- [ ] **Step 2: Write the failing test (learning still solves; learnt clause is asserting)**

Add to `solver.rs` tests:

```rust
    #[test]
    fn cdcl_solves_unsat_pigeon_like() {
        // Same UNSAT 2-SAT as before, now via CDCL: must still be UNSAT.
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        s.add_clause(&[lit(0, true), lit(1, false)]);
        s.add_clause(&[lit(0, false), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, false)]);
        assert_eq!(s.solve(), SolveResult::Unsat { core: vec![] });
    }

    #[test]
    fn cdcl_solves_sat_and_assignment_satisfies() {
        // (x0 ∨ x1 ∨ x2) ∧ (¬x0 ∨ ¬x1) ∧ (¬x1 ∨ ¬x2) ∧ (x1) -> forces a chain.
        let mut s = mk(3);
        s.add_clause(&[lit(0, true), lit(1, true), lit(2, true)]);
        s.add_clause(&[lit(0, false), lit(1, false)]);
        s.add_clause(&[lit(1, false), lit(2, false)]);
        s.add_clause(&[lit(1, true)]);
        assert_eq!(s.solve(), SolveResult::Sat);
        // x1 true => x0 false, x2 false => clause1 needs x0|x1|x2: x1 true ok.
        assert_eq!(s.assign.value(Var::new(1)), LBool::True);
        assert_eq!(s.assign.value(Var::new(0)), LBool::False);
        assert_eq!(s.assign.value(Var::new(2)), LBool::False);
    }
```

- [ ] **Step 3: Run to verify it fails or regresses**

Run: `cargo test -p shinri-sat -- solver`
Expected: compile error once you start editing `solve` (or the new tests fail) — proceed to implement.

- [ ] **Step 4: Implement `conflict_lits`, `analyze`, `add_learnt`**

Add to `impl Solver`:

```rust
    /// The literal set of a conflict — read from the arena for a stored clause,
    /// or returned directly for a virtual (binary/theory) conflict.
    fn conflict_lits(&self, c: &Conflict) -> Vec<Lit> {
        match c {
            Conflict::Clause(r) => self.db.lits(*r).to_vec(),
            Conflict::Lits(ls) => ls.clone(),
        }
    }

    /// 1-UIP conflict analysis. Returns (learnt clause with the asserting
    /// literal at index 0, backjump level). Assumes the conflict is at the
    /// current decision level > 0.
    pub(crate) fn analyze(&mut self, conflict: Conflict) -> (Vec<Lit>, u32) {
        let level = self.trail.decision_level();
        self.analyzer.learnt.clear();
        self.analyzer.learnt.push(Lit::from_code(0)); // placeholder for asserting lit
        let mut counter = 0u32; // literals at `level` still to resolve
        let mut trail_idx = self.trail.len();
        let mut seen_vars: Vec<Var> = Vec::new();

        // Seed with the conflict clause's literals.
        let mut reason_lits = self.conflict_lits(&conflict);
        loop {
            for &q in &reason_lits {
                let v = q.var();
                if !self.analyzer.seen[v.index()] && self.assign.level(v) > 0 {
                    self.analyzer.seen[v.index()] = true;
                    seen_vars.push(v);
                    if self.assign.level(v) == level {
                        counter += 1;
                    } else {
                        self.analyzer.learnt.push(q);
                    }
                }
            }
            // Find the next trail literal at `level` that we've marked seen.
            loop {
                trail_idx -= 1;
                let p = self.trail.lit_at(trail_idx);
                if self.analyzer.seen[p.var().index()] {
                    break;
                }
            }
            let p = self.trail.lit_at(trail_idx);
            let pv = p.var();
            self.analyzer.seen[pv.index()] = false;
            counter -= 1;
            if counter == 0 {
                // `p` is the first UIP; the asserting literal is its negation.
                self.analyzer.learnt[0] = p.negate();
                break;
            }
            // Resolve on p's reason.
            reason_lits = self.reason_lits_of(p);
        }

        // Clear remaining seen marks.
        for v in seen_vars {
            self.analyzer.seen[v.index()] = false;
        }

        // Backjump level = second-highest decision level in the learnt clause.
        let learnt = std::mem::take(&mut self.analyzer.learnt);
        let bt = learnt
            .iter()
            .skip(1)
            .map(|l| self.assign.level(l.var()))
            .max()
            .unwrap_or(0);
        (learnt, bt)
    }

    /// The literals (other than `p` itself) of `p`'s antecedent clause —
    /// i.e. the literals to resolve against when walking the implication graph.
    fn reason_lits_of(&self, p: Lit) -> Vec<Lit> {
        match self.assign.reason(p.var()) {
            Reason::Decision => Vec::new(), // a decision has no antecedent
            Reason::Unit => Vec::new(),
            Reason::Binary(other) => vec![other],
            Reason::Clause(r) => {
                // All literals except `p` (which is satisfied by this clause).
                self.db.lits(r).iter().copied().filter(|&l| l != p).collect()
            }
            Reason::Theory(_just) => Vec::new(), // expanded lazily in Task 17
        }
    }

    /// Install a learnt clause and return its ref (None if it is a unit, which
    /// is asserted at level 0). The asserting literal is `learnt[0]`.
    pub(crate) fn add_learnt(&mut self, learnt: &[Lit]) -> Option<ClauseRef> {
        match learnt.len() {
            0 => None, // empty learnt clause => top-level UNSAT (handled by caller)
            1 => None,
            2 => {
                self.watches.watch_binary(learnt[0], learnt[1]);
                None
            }
            _ => {
                let (_id, r) = self.db.add_clause(learnt, true);
                self.watches.watch_clause(r, learnt[0], learnt[1]);
                Some(r)
            }
        }
    }
```

- [ ] **Step 5: Replace the `solve` search loop with CDCL**

Replace the body of `solve`:

```rust
    pub fn solve(&mut self) -> SolveResult {
        if self.unsat {
            return SolveResult::Unsat { core: vec![] };
        }
        loop {
            match self.propagate() {
                Some(conflict) => {
                    if self.trail.decision_level() == 0 {
                        self.unsat = true;
                        return SolveResult::Unsat { core: vec![] };
                    }
                    let (learnt, bt) = self.analyze(conflict);
                    self.backtrack_to(bt);
                    let asserting = learnt[0];
                    let reason = match self.add_learnt(&learnt) {
                        Some(r) => Reason::Clause(r),
                        None if learnt.len() == 2 => Reason::Binary(learnt[1]),
                        None => Reason::Unit,
                    };
                    self.enqueue(asserting, reason);
                }
                None => match self.pick_branch() {
                    Some(l) => {
                        self.trail.new_level();
                        self.enqueue(l, Reason::Decision);
                    }
                    None => return SolveResult::Sat,
                },
            }
        }
    }
```

- [ ] **Step 6: Run to verify all solver tests pass**

Run: `cargo test -p shinri-sat -- solver`
Expected: all PASS (Task 8 instances still correct, plus the new CDCL cases).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): CDCL — 1-UIP analysis, clause learning, non-chronological backjump"
```

---

### Task 10: Recursive clause minimization

Shrinks learnt clauses by dropping literals whose reason is subsumed by the rest of the clause (Sörensson–Biere self-subsuming / recursive minimization).

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs` (add `minimize`, `lit_redundant`, `redundant_step`; call `minimize` in `analyze`; add `stats_minimized`)
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `analyze`'s post-UIP state (learnt clause in `analyzer.learnt`, `seen` marks set for the clause's non-asserting literals).
- Produces: `Solver::stats_minimized: u64` (literals removed; test/telemetry hook), `minimize(&mut self)`.

- [ ] **Step 1: Add the `stats_minimized` field**

In `Solver`, add `pub(crate) stats_minimized: u64,` and initialize it to `0` in `Solver::new`.

- [ ] **Step 2: Write the failing test**

Add to `solver.rs` tests:

```rust
    #[test]
    fn minimization_field_tracks_removals_and_result_correct() {
        // 4-variable UNSAT core; correctness must hold with minimization on.
        let mut s = mk(4);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(2, true)]);
        s.add_clause(&[lit(1, false), lit(2, true)]);
        s.add_clause(&[lit(2, false), lit(3, true)]);
        s.add_clause(&[lit(2, false), lit(3, false)]);
        let r = s.solve();
        // Either SAT or UNSAT, but must be deterministic & sound; here it is SAT.
        assert_eq!(r, SolveResult::Sat);
        let _ = s.stats_minimized; // field must exist
    }
```

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-sat -- minimization_field`
Expected: FAIL to compile — `stats_minimized` referenced before existing / `minimize` missing.

- [ ] **Step 4: Implement minimization**

Add to `impl Solver`:

```rust
    /// Drop redundant literals from the learnt clause in place. Runs after the
    /// UIP loop, while `seen` still marks the clause's non-asserting literals.
    fn minimize(&mut self) {
        let mut learnt = std::mem::take(&mut self.analyzer.learnt);
        let mut newly_seen: Vec<Var> = Vec::new();
        let mut j = 1;
        for i in 1..learnt.len() {
            let l = learnt[i];
            if !self.lit_redundant(l, &mut newly_seen) {
                learnt[j] = l;
                j += 1;
            }
        }
        self.stats_minimized += (learnt.len() - j) as u64;
        learnt.truncate(j);
        for v in newly_seen {
            self.analyzer.seen[v.index()] = false;
        }
        self.analyzer.learnt = learnt;
    }

    /// True if `l` can be removed: every literal of its reason is already in the
    /// clause (`seen`), at level 0, or itself recursively redundant.
    fn lit_redundant(&mut self, l: Lit, newly_seen: &mut Vec<Var>) -> bool {
        match self.assign.reason(l.var()) {
            Reason::Decision => false,
            Reason::Unit => true,
            Reason::Binary(other) => self.redundant_step(other, newly_seen),
            Reason::Clause(r) => {
                let lits: Vec<Lit> =
                    self.db.lits(r).iter().copied().filter(|&x| x != l).collect();
                for x in lits {
                    if !self.redundant_step(x, newly_seen) {
                        return false;
                    }
                }
                true
            }
            Reason::Theory(_) => false, // don't minimize across theory reasons (Phase 1)
        }
    }

    fn redundant_step(&mut self, x: Lit, newly_seen: &mut Vec<Var>) -> bool {
        let v = x.var();
        if self.analyzer.seen[v.index()] || self.assign.level(v) == 0 {
            return true;
        }
        if matches!(self.assign.reason(v), Reason::Decision) {
            return false;
        }
        if self.lit_redundant(x, newly_seen) {
            self.analyzer.seen[v.index()] = true;
            newly_seen.push(v);
            true
        } else {
            false
        }
    }
```

- [ ] **Step 5: Call `minimize` in `analyze`**

In `analyze`, immediately after the UIP `loop { ... }` ends (before the "Clear remaining seen marks" loop), insert:

```rust
        self.minimize();
```

- [ ] **Step 6: Run to verify it passes**

Run: `cargo test -p shinri-sat -- solver`
Expected: all PASS. (Soundness of minimization — learnt clause still entailed — is property-tested in Task 19.)

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): recursive self-subsuming clause minimization"
```

---

### Task 11: LBD computation + clause-DB reduction

Assigns each learnt clause its LBD (glue), and periodically deletes the high-LBD half via lazy deletion (a DELETED bit; watch entries are garbage-collected on the next pass over their list).

**Files:**
- Modify: `crates/shinri-sat/src/clause.rs` (DELETED bit: `is_deleted`/`mark_deleted`)
- Modify: `crates/shinri-sat/src/solver.rs` (LBD, `learnts` tracking, `reduce`, propagate skip of dead clauses, conflict-counter trigger)
- Modify: `crates/shinri-sat/src/reduce.rs` (LBD helper) — *or keep LBD inline in solver.rs; this plan keeps it inline and uses `reduce.rs` only if a later task needs it. Create `reduce.rs` with the doc comment now so the module exists.*
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces:
  - `ClauseDb::is_deleted(&self, ClauseRef) -> bool`, `mark_deleted(&mut self, ClauseRef)`.
  - `Solver`: `compute_lbd(&self, &[Lit]) -> u32`, `reduce(&mut self)`, fields `learnts: Vec<ClauseRef>`, `conflicts: u64`, `stats_deleted: u64`, `is_locked(&self, ClauseRef) -> bool`.

- [ ] **Step 1: Add the DELETED bit to `ClauseDb`**

In `clause.rs`, add `const DELETED_BIT: u32 = 1 << 30;` near the other consts, and inside `impl ClauseDb`:

```rust
    #[inline]
    pub fn is_deleted(&self, r: ClauseRef) -> bool {
        self.arena[self.off(r) + 1] & DELETED_BIT != 0
    }
    #[inline]
    pub fn mark_deleted(&mut self, r: ClauseRef) {
        self.arena[self.off(r) + 1] |= DELETED_BIT;
    }
```

Also update the `LBD_MASK` to exclude the new bit: change it to `const LBD_MASK: u32 = 0x3FFF_FFFF;` (bits 0..30), so `meta = learnt(31) | deleted(30) | lbd(0..30)`. The `set_lbd`/`lbd` masks already use `LBD_MASK`; `set_lbd` must also preserve the DELETED bit — change `set_lbd` to:

```rust
    #[inline]
    pub fn set_lbd(&mut self, r: ClauseRef, lbd: u32) {
        let off = self.off(r);
        let keep = self.arena[off + 1] & (LEARNT_BIT | DELETED_BIT);
        self.arena[off + 1] = keep | (lbd & LBD_MASK);
    }
```

- [ ] **Step 2: Create `reduce.rs` (module marker + doc)**

```rust
//! Clause-database reduction (spec §6.3). The LBD computation and the
//! reduction policy currently live in `solver.rs` (they need the trail and
//! watch state); this module is reserved for extraction if that logic grows.
```

Add `pub mod reduce;` to `lib.rs`.

- [ ] **Step 3: Add fields + write the failing reduce test**

Add to `Solver`: `pub(crate) learnts: Vec<ClauseRef>,` `pub(crate) conflicts: u64,` `pub(crate) stats_deleted: u64,` (init `Vec::new()`, `0`, `0`). Add to `solver.rs` tests:

```rust
    #[test]
    fn reduce_deletes_high_lbd_unlocked_learnts() {
        let mut s = mk(6);
        // Install three "learnt" clauses directly with controlled LBD.
        let r_lo = s.add_learnt(&[lit(0, true), lit(1, true), lit(2, true)]).unwrap();
        let r_hi = s.add_learnt(&[lit(3, true), lit(4, true), lit(5, true)]).unwrap();
        s.learnts.push(r_lo);
        s.learnts.push(r_hi);
        s.db.set_lbd(r_lo, 2); // glue, protected (<= threshold 2)
        s.db.set_lbd(r_hi, 9); // high glue, deletable
        s.reduce();
        assert!(!s.db.is_deleted(r_lo), "low-LBD clause kept");
        assert!(s.db.is_deleted(r_hi), "high-LBD clause deleted");
        assert!(s.stats_deleted >= 1);
    }
```

(Note: `add_learnt` must also push to `self.learnts` for clauses created during real solving; do that in Step 5. In this test we push manually to control LBD precisely.)

- [ ] **Step 4: Run to verify it fails**

Run: `cargo test -p shinri-sat -- reduce_deletes`
Expected: FAIL — `reduce`/`is_locked`/fields missing.

- [ ] **Step 5: Implement LBD, locking, reduce; track learnts; skip dead clauses**

Add to `impl Solver`:

```rust
    /// Literal Block Distance: the number of distinct decision levels in `lits`.
    fn compute_lbd(&self, lits: &[Lit]) -> u32 {
        let mut levels: Vec<u32> = lits.iter().map(|l| self.assign.level(l.var())).collect();
        levels.sort_unstable();
        levels.dedup();
        levels.len() as u32
    }

    /// A learnt clause is locked iff it is currently the reason of its asserting
    /// literal (`lits[0]`), so deleting it would orphan a trail assignment.
    fn is_locked(&self, r: ClauseRef) -> bool {
        let l0 = self.db.lit_at(r, 0);
        self.assign.value(l0.var()) != LBool::Unset
            && matches!(self.assign.reason(l0.var()), Reason::Clause(rr) if rr == r)
    }

    /// Delete the high-LBD half of the learnt database (lazy deletion), keeping
    /// every clause with glue <= threshold and every locked clause.
    pub(crate) fn reduce(&mut self) {
        let keep_glue = self.config.lbd_keep_threshold;
        let mut refs: Vec<ClauseRef> =
            self.learnts.iter().copied().filter(|&r| !self.db.is_deleted(r)).collect();
        refs.sort_by_key(|&r| self.db.lbd(r));
        let n = refs.len();
        let half = n / 2;
        let mut survivors = Vec::with_capacity(n);
        for (i, r) in refs.iter().copied().enumerate() {
            let in_worst_half = i >= n - half;
            if in_worst_half && self.db.lbd(r) > keep_glue && !self.is_locked(r) {
                self.db.mark_deleted(r);
                self.stats_deleted += 1;
            } else {
                survivors.push(r);
            }
        }
        self.learnts = survivors;
    }
```

In `add_learnt`, in the `_ =>` (long-clause) arm, after `let (_id, r) = self.db.add_clause(...)`, push the ref: `self.learnts.push(r);` then continue to watch + return `Some(r)`.

In `propagate`, at the very top of the `WatchTarget::Clause(r) =>` arm, drop dead clauses:

```rust
                    WatchTarget::Clause(r) => {
                        if self.db.is_deleted(r) {
                            continue; // garbage-collect this watch entry
                        }
                        // ... existing find-new-watch logic ...
```

- [ ] **Step 6: Wire the conflict counter + reduce trigger into `solve`**

In `solve`'s conflict branch, after computing/installing the learnt clause, add:

```rust
                    self.conflicts += 1;
                    let lbd = self.compute_lbd(&learnt);
                    if let Reason::Clause(r) = reason {
                        self.db.set_lbd(r, lbd);
                    }
                    if self.conflicts % self.config.reduce_interval as u64 == 0 {
                        self.reduce();
                    }
```

(Place this immediately after the `self.enqueue(asserting, reason);` line.)

- [ ] **Step 7: Run to verify it passes**

Run: `cargo test -p shinri-sat -- solver reduce`
Expected: all PASS.

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): LBD glue + lazy clause-DB reduction (keep glue<=2, protect locked)"
```

---

### Task 12: Restarts — Luby + Glucose-EMA

**Files:**
- Modify: `crates/shinri-sat/src/restart.rs` (the `RestartPolicy`)
- Modify: `crates/shinri-sat/src/solver.rs` (hold a `RestartPolicy`, restart in `solve`)
- Test: inline `#[cfg(test)]` in `restart.rs`

**Interfaces:**
- Produces:
  - `crate::restart::luby(i: u64) -> u64` (the Luby sequence, 1-indexed).
  - `crate::restart::RestartPolicy` with `new(RestartKind, base: u64) -> RestartPolicy`, `on_conflict(&mut self, lbd: u32)`, `should_restart(&self) -> bool`, `on_restart(&mut self)`.

- [ ] **Step 1: Write the failing test for `luby` and the Luby policy**

Replace `restart.rs` contents with the test first:

```rust
use crate::config::RestartKind;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn luby_sequence_prefix() {
        // Classic Luby: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
        let got: Vec<u64> = (1..=15).map(luby).collect();
        assert_eq!(got, vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]);
    }

    #[test]
    fn luby_policy_fires_after_base_times_unit() {
        let mut p = RestartPolicy::new(RestartKind::Luby, 4);
        // First limit = base * luby(1) = 4 conflicts.
        for _ in 0..3 {
            p.on_conflict(3);
            assert!(!p.should_restart());
        }
        p.on_conflict(3);
        assert!(p.should_restart());
        p.on_restart();
        assert!(!p.should_restart());
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-sat -- restart`
Expected: FAIL — `luby`/`RestartPolicy` not defined.

- [ ] **Step 3: Implement `luby` and `RestartPolicy`**

Above the test module in `restart.rs`:

```rust
/// The Luby sequence value at 1-based index `i` (Luby–Sinclair–Zuckerman).
pub fn luby(i: u64) -> u64 {
    // Find the subsequence: for the largest k with 2^k - 1 <= i.
    let mut size = 1u64; // 2^k - 1
    let mut seq = 0u64; // k
    while size < i {
        size = 2 * size + 1;
        seq += 1;
    }
    let mut size = size;
    let mut seq = seq;
    while size != i {
        size = (size - 1) / 2;
        seq -= 1;
        if i > size {
            // move into the right half (recurse on i - size offset)
            return luby(i - size);
        }
    }
    1u64 << seq
}

/// Restart scheduler. Luby is a fixed multiplicative schedule; Glucose-EMA
/// restarts when the fast LBD average exceeds the slow average by a margin.
pub struct RestartPolicy {
    kind: RestartKind,
    base: u64,
    conflicts_since: u64,
    luby_index: u64,
    limit: u64,
    ema_fast: f64,
    ema_slow: f64,
    seen: u64,
}

impl RestartPolicy {
    pub fn new(kind: RestartKind, base: u64) -> RestartPolicy {
        RestartPolicy {
            kind,
            base,
            conflicts_since: 0,
            luby_index: 1,
            limit: base * luby(1),
            ema_fast: 0.0,
            ema_slow: 0.0,
            seen: 0,
        }
    }

    pub fn on_conflict(&mut self, lbd: u32) {
        self.conflicts_since += 1;
        self.seen += 1;
        let x = lbd as f64;
        // Glucose EMA coefficients: fast 1/32, slow 1/2^14.
        self.ema_fast += (x - self.ema_fast) / 32.0;
        self.ema_slow += (x - self.ema_slow) / 16384.0;
    }

    pub fn should_restart(&self) -> bool {
        match self.kind {
            RestartKind::Luby => self.conflicts_since >= self.limit,
            RestartKind::EmaGlucose => {
                // Warm up before trusting the averages.
                self.seen >= 50 && self.ema_fast > 1.25 * self.ema_slow
            }
        }
    }

    pub fn on_restart(&mut self) {
        self.conflicts_since = 0;
        self.luby_index += 1;
        self.limit = self.base * luby(self.luby_index);
    }
}
```

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-sat -- restart`
Expected: both PASS.

- [ ] **Step 5: Wire restarts into `solve`**

In `Solver`, add field `pub(crate) restart: RestartPolicy,` and init in `new`: `restart: RestartPolicy::new(config.restart, 100),` (add `use crate::restart::RestartPolicy;`). In `solve`'s conflict branch, after the reduce trigger, add:

```rust
                    self.restart.on_conflict(lbd);
                    if self.restart.should_restart() && self.trail.decision_level() > 0 {
                        self.restart.on_restart();
                        self.backtrack_to(0);
                    }
```

- [ ] **Step 6: Run the whole crate's tests**

Run: `cargo test -p shinri-sat`
Expected: all PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): Luby + Glucose-EMA restart policies"
```

---

### Task 13: `BranchHeuristic` trait + VMTF; make `Solver` generic over `H`

Introduces the first generic seam. `Solver` becomes `Solver<H: BranchHeuristic>`; the branching choice is fixed at construction (spec §8.4). VMTF (integer-only, deterministic) is the first implementation.

**Files:**
- Create: `crates/shinri-sat/src/heuristic/mod.rs`
- Create: `crates/shinri-sat/src/heuristic/vmtf.rs`
- Modify: `crates/shinri-sat/src/solver.rs` (generic refactor + wiring)
- Modify: `crates/shinri-sat/src/lib.rs` (`pub mod heuristic;`, exports)
- Test: inline `#[cfg(test)]` in `vmtf.rs` and `solver.rs`

**Interfaces:**
- Produces:
  - `crate::heuristic::BranchHeuristic` (supertrait `Default`) with `new_var(&mut self, Var)`, `bump(&mut self, Var)`, `decay(&mut self)`, `on_unassign(&mut self, Var)`, `next(&mut self, &Assignment) -> Option<Var>`.
  - `crate::heuristic::vmtf::Vmtf`.
  - `Solver<H: BranchHeuristic>` with `heuristic: H`; `new(SolverConfig) -> Solver<H>`.

- [ ] **Step 1: Define the trait — `heuristic/mod.rs`**

```rust
use crate::assignment::Assignment;
use shinri_core::Var;

pub mod vmtf;
pub use vmtf::Vmtf;

/// The branching heuristic seam. Fixed at construction as the generic `H` of
/// `Solver`, so `next`/`bump` monomorphize with zero dispatch (spec §8.4).
pub trait BranchHeuristic: Default {
    /// A new variable was allocated.
    fn new_var(&mut self, v: Var);
    /// Raise `v`'s priority (called during conflict analysis).
    fn bump(&mut self, v: Var);
    /// Age all priorities one step (called once per conflict).
    fn decay(&mut self);
    /// `v` was un-assigned on backtrack and is a branching candidate again.
    fn on_unassign(&mut self, v: Var);
    /// The highest-priority *unassigned* variable, or `None` if all assigned.
    fn next(&mut self, assign: &Assignment) -> Option<Var>;
}
```

- [ ] **Step 2: Write the failing VMTF test — `heuristic/vmtf.rs`**

```rust
use crate::assignment::Assignment;
use crate::heuristic::BranchHeuristic;
use crate::types::Reason;
use shinri_core::{Lit, Var};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn most_recently_bumped_unassigned_var_is_chosen() {
        let mut a = Assignment::new();
        for _ in 0..3 {
            a.new_var();
        }
        let mut h = Vmtf::default();
        for i in 0..3 {
            h.new_var(Var::new(i));
        }
        h.bump(Var::new(2)); // var 2 now highest priority
        assert_eq!(h.next(&a), Some(Var::new(2)));

        // Assign var 2; next() must skip it and fall to the next candidate.
        a.assign(Lit::new(Var::new(2), true), 1, Reason::Decision);
        let n = h.next(&a).unwrap();
        assert!(n == Var::new(0) || n == Var::new(1));

        // Unassigning var 2 makes it the top candidate again.
        a.unassign(Var::new(2));
        h.on_unassign(Var::new(2));
        assert_eq!(h.next(&a), Some(Var::new(2)));
    }
}
```

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-sat -- vmtf`
Expected: FAIL — `Vmtf` not defined.

- [ ] **Step 4: Implement VMTF**

Above the test module in `vmtf.rs`:

```rust
use crate::types::LBool;

const NIL: u32 = u32::MAX;

/// Variable Move-To-Front: a doubly-linked priority list over variables. The
/// most-recently-bumped variable is at the head; `next` walks from a `search`
/// pointer (kept at-or-before the highest-priority unassigned var). Integer
/// stamps only — fully deterministic.
pub struct Vmtf {
    next: Vec<u32>,
    prev: Vec<u32>,
    stamp: Vec<u64>,
    head: u32,
    tail: u32,
    search: u32,
    counter: u64,
}

impl Default for Vmtf {
    fn default() -> Self {
        Vmtf {
            next: Vec::new(),
            prev: Vec::new(),
            stamp: Vec::new(),
            head: NIL,
            tail: NIL,
            search: NIL,
            counter: 0,
        }
    }
}

impl Vmtf {
    fn unlink(&mut self, i: u32) {
        let p = self.prev[i as usize];
        let n = self.next[i as usize];
        if p != NIL {
            self.next[p as usize] = n;
        } else {
            self.head = n;
        }
        if n != NIL {
            self.prev[n as usize] = p;
        } else {
            self.tail = p;
        }
    }
}

impl BranchHeuristic for Vmtf {
    fn new_var(&mut self, v: Var) {
        let i = v.index() as u32;
        debug_assert_eq!(i as usize, self.next.len(), "vars added in order");
        self.next.push(NIL);
        self.prev.push(NIL);
        self.stamp.push(0);
        if self.head == NIL {
            self.head = i;
            self.tail = i;
            self.search = i;
        } else {
            self.next[self.tail as usize] = i;
            self.prev[i as usize] = self.tail;
            self.tail = i;
        }
    }

    fn bump(&mut self, v: Var) {
        let i = v.index() as u32;
        self.counter += 1;
        self.stamp[i as usize] = self.counter;
        if self.head == i {
            return;
        }
        self.unlink(i);
        self.next[i as usize] = self.head;
        self.prev[i as usize] = NIL;
        if self.head != NIL {
            self.prev[self.head as usize] = i;
        }
        self.head = i;
        if self.tail == NIL {
            self.tail = i;
        }
    }

    fn decay(&mut self) {
        // VMTF has no decay (move-to-front is the aging mechanism).
    }

    fn on_unassign(&mut self, v: Var) {
        let i = v.index();
        if self.search == NIL || self.stamp[i] > self.stamp[self.search as usize] {
            self.search = i as u32;
        }
    }

    fn next(&mut self, assign: &Assignment) -> Option<Var> {
        let mut i = self.search;
        while i != NIL {
            let v = Var::new(i);
            if assign.value(v) == LBool::Unset {
                self.search = i;
                return Some(v);
            }
            i = self.next[i as usize];
        }
        None
    }
}
```

- [ ] **Step 5: Run to verify VMTF passes**

Run: `cargo test -p shinri-sat -- vmtf`
Expected: PASS.

- [ ] **Step 6: Make `Solver` generic over `H` and wire the heuristic**

In `solver.rs` apply these edits (find-replace the headers, then the bodies):

1. Add imports: `use crate::heuristic::{BranchHeuristic, Vmtf};`
2. Change the struct header and add the field:

```rust
pub struct Solver<H: BranchHeuristic> {
    pub(crate) assign: Assignment,
    pub(crate) trail: Trail,
    pub(crate) db: ClauseDb,
    pub(crate) watches: Watches,
    pub(crate) analyzer: Analyzer,
    pub(crate) restart: RestartPolicy,
    pub(crate) config: SolverConfig,
    pub(crate) heuristic: H,
    pub(crate) learnts: Vec<ClauseRef>,
    pub(crate) conflicts: u64,
    pub(crate) unsat: bool,
    pub(crate) stats_minimized: u64,
    pub(crate) stats_deleted: u64,
}
```

3. Change `impl Solver {` to `impl<H: BranchHeuristic> Solver<H> {` (every `impl Solver` block).
4. In `new`, set `heuristic: H::default(),`.
5. In `new_var`, after `let v = self.assign.new_var();`, add `self.heuristic.new_var(v);` and keep the `ensure_vars` / `analyzer.ensure_vars` calls.
6. Replace `pick_branch` with:

```rust
    fn pick_branch(&mut self) -> Option<Lit> {
        self.heuristic
            .next(&self.assign)
            .map(|v| Lit::new(v, self.assign.phase(v)))
    }
```

7. In `analyze`, where a variable is first marked `seen` (both in the seed loop and inside the resolution loop), add `self.heuristic.bump(v);` right after `self.analyzer.seen[v.index()] = true;`.
8. Replace `backtrack_to` with the split-borrow version that notifies the heuristic:

```rust
    pub(crate) fn backtrack_to(&mut self, level: u32) {
        let assign = &mut self.assign;
        let heuristic = &mut self.heuristic;
        self.trail.backtrack_to(level, |l| {
            assign.unassign(l.var());
            heuristic.on_unassign(l.var());
        });
    }
```

9. In `solve`'s conflict branch, add `self.heuristic.decay();` right after `self.conflicts += 1;`.

- [ ] **Step 7: Update the test helper `mk` to pin `H = Vmtf`**

In `solver.rs` tests, change `mk`:

```rust
    fn mk(n_vars: u32) -> Solver<Vmtf> {
        let mut s = Solver::<Vmtf>::new(SolverConfig::default());
        for _ in 0..n_vars {
            s.new_var();
        }
        s
    }
```

- [ ] **Step 8: Wire modules, run all tests, commit**

`lib.rs`: `pub mod heuristic;` and `pub use heuristic::{BranchHeuristic, Vmtf};`

Run: `cargo test -p shinri-sat`
Expected: all PASS.

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): BranchHeuristic trait + VMTF; Solver generic over H"
```

---

### Task 14: EVSIDS branching heuristic

A second `BranchHeuristic`: exponential VSIDS with an indexed binary max-heap. Selectable by constructing `Solver::<Evsids>`.

**Files:**
- Create: `crates/shinri-sat/src/heuristic/evsids.rs`
- Modify: `crates/shinri-sat/src/heuristic/mod.rs` (`pub mod evsids; pub use evsids::Evsids;`)
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces: `crate::heuristic::evsids::Evsids` implementing `BranchHeuristic`.

- [ ] **Step 1: Write the failing test**

```rust
use crate::assignment::Assignment;
use crate::heuristic::BranchHeuristic;
use crate::types::Reason;
use shinri_core::{Lit, Var};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn highest_activity_unassigned_var_chosen_and_reinserted() {
        let mut a = Assignment::new();
        for _ in 0..3 {
            a.new_var();
        }
        let mut h = Evsids::default();
        for i in 0..3 {
            h.new_var(Var::new(i));
        }
        h.bump(Var::new(1));
        h.bump(Var::new(1)); // var 1 most active
        assert_eq!(h.next(&a), Some(Var::new(1)));

        a.assign(Lit::new(Var::new(1), true), 1, Reason::Decision);
        let n = h.next(&a).unwrap();
        assert!(n != Var::new(1));

        a.unassign(Var::new(1));
        h.on_unassign(Var::new(1));
        assert_eq!(h.next(&a), Some(Var::new(1)));
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-sat -- evsids`
Expected: FAIL — `Evsids` not defined.

- [ ] **Step 3: Implement EVSIDS with an indexed max-heap**

```rust
use crate::types::LBool;

/// Exponential VSIDS: float activities with an indexed binary max-heap of
/// unassigned candidates. `var_inc` grows each conflict (the "exponential"
/// trick that avoids decaying every variable); rescale keeps it finite.
pub struct Evsids {
    activity: Vec<f64>,
    heap: Vec<u32>,    // binary max-heap of var indices
    pos: Vec<i32>,     // pos[v] = index in `heap`, or -1 if absent
    var_inc: f64,
    var_decay: f64,
}

impl Default for Evsids {
    fn default() -> Self {
        Evsids {
            activity: Vec::new(),
            heap: Vec::new(),
            pos: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.95,
        }
    }
}

impl Evsids {
    #[inline]
    fn higher(&self, a: u32, b: u32) -> bool {
        self.activity[a as usize] > self.activity[b as usize]
    }

    fn sift_up(&mut self, mut i: usize) {
        let x = self.heap[i];
        while i > 0 {
            let parent = (i - 1) / 2;
            if self.higher(x, self.heap[parent]) {
                self.heap[i] = self.heap[parent];
                self.pos[self.heap[i] as usize] = i as i32;
                i = parent;
            } else {
                break;
            }
        }
        self.heap[i] = x;
        self.pos[x as usize] = i as i32;
    }

    fn sift_down(&mut self, mut i: usize) {
        let x = self.heap[i];
        let n = self.heap.len();
        loop {
            let l = 2 * i + 1;
            if l >= n {
                break;
            }
            let r = l + 1;
            let child = if r < n && self.higher(self.heap[r], self.heap[l]) { r } else { l };
            if self.higher(self.heap[child], x) {
                self.heap[i] = self.heap[child];
                self.pos[self.heap[i] as usize] = i as i32;
                i = child;
            } else {
                break;
            }
        }
        self.heap[i] = x;
        self.pos[x as usize] = i as i32;
    }

    fn heap_insert(&mut self, v: u32) {
        if self.pos[v as usize] >= 0 {
            return;
        }
        self.heap.push(v);
        let i = self.heap.len() - 1;
        self.pos[v as usize] = i as i32;
        self.sift_up(i);
    }

    fn heap_pop(&mut self) -> Option<u32> {
        if self.heap.is_empty() {
            return None;
        }
        let top = self.heap[0];
        let last = *self.heap.last().unwrap();
        self.heap[0] = last;
        self.pos[last as usize] = 0;
        self.heap.pop();
        self.pos[top as usize] = -1;
        if !self.heap.is_empty() {
            self.sift_down(0);
        }
        Some(top)
    }
}

impl BranchHeuristic for Evsids {
    fn new_var(&mut self, v: Var) {
        debug_assert_eq!(v.index(), self.activity.len(), "vars added in order");
        self.activity.push(0.0);
        self.pos.push(-1);
        self.heap_insert(v.index() as u32);
    }

    fn bump(&mut self, v: Var) {
        let i = v.index();
        self.activity[i] += self.var_inc;
        if self.activity[i] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        if self.pos[i] >= 0 {
            self.sift_up(self.pos[i] as usize);
        }
    }

    fn decay(&mut self) {
        self.var_inc /= self.var_decay;
    }

    fn on_unassign(&mut self, v: Var) {
        self.heap_insert(v.index() as u32);
    }

    fn next(&mut self, assign: &Assignment) -> Option<Var> {
        while let Some(top) = self.heap_pop() {
            let v = Var::new(top);
            if assign.value(v) == LBool::Unset {
                // Re-insert so it can be chosen again after backtrack.
                self.heap_insert(top);
                return Some(v);
            }
        }
        None
    }
}
```

**Note:** `next` pops assigned vars off the heap; they re-enter via `on_unassign` on backtrack. The chosen var is re-inserted so it remains a future candidate.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-sat -- evsids`
Expected: PASS.

- [ ] **Step 5: Wire and commit**

`heuristic/mod.rs`: add `pub mod evsids; pub use evsids::Evsids;`. In `lib.rs` add `Evsids` to the heuristic re-exports.

Run: `cargo test -p shinri-sat`
Expected: all PASS.

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): EVSIDS heuristic (indexed max-heap)"
```

---

### Task 15: Incremental assumptions + failed-assumption core

`solve_under(assumptions)` places assumption literals as the first decisions; when one is already falsified, `analyze_final` extracts the minimal failed-assumption set (spec §7.1–7.2). Also makes `add_clause` and `solve` robust to being called after a prior solve (backtrack to level 0 first).

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces: `Solver::solve_under(&mut self, &[Lit]) -> SolveResult`, `analyze_final(&mut self, Lit) -> Vec<Lit>`. `solve` now delegates to `solve_under(&[])`.

- [ ] **Step 1: Write the failing test**

```rust
    #[test]
    fn failed_assumptions_yield_core() {
        use std::collections::HashSet;
        // Clause (x0 ∨ x1). Assume ¬x0 and ¬x1 => UNSAT, core = {¬x0, ¬x1}.
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        let r = s.solve_under(&[lit(0, false), lit(1, false)]);
        match r {
            SolveResult::Unsat { core } => {
                let set: HashSet<Lit> = core.into_iter().collect();
                assert!(set.contains(&lit(0, false)));
                assert!(set.contains(&lit(1, false)));
            }
            _ => panic!("expected UNSAT under assumptions"),
        }
    }

    #[test]
    fn satisfiable_under_assumptions() {
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        assert_eq!(s.solve_under(&[lit(0, true)]), SolveResult::Sat);
    }
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-sat -- assumptions satisfiable_under`
Expected: FAIL — `solve_under` not defined.

- [ ] **Step 3: Make `add_clause` level-0-safe**

At the very top of `add_clause`, replace the `debug_assert_eq!` with:

```rust
        if self.trail.decision_level() != 0 {
            self.backtrack_to(0);
        }
```

- [ ] **Step 4: Implement `solve_under`, `analyze_final`; redefine `solve`**

Replace `solve` with:

```rust
    pub fn solve(&mut self) -> SolveResult {
        self.solve_under(&[])
    }

    /// Solve under the given assumption literals (placed as the first
    /// decisions). On UNSAT, `core` is the failed-assumption subset.
    pub fn solve_under(&mut self, assumptions: &[Lit]) -> SolveResult {
        if self.unsat {
            return SolveResult::Unsat { core: vec![] };
        }
        self.backtrack_to(0);
        loop {
            match self.propagate() {
                Some(conflict) => {
                    if self.trail.decision_level() == 0 {
                        self.unsat = true;
                        return SolveResult::Unsat { core: vec![] };
                    }
                    let (learnt, bt) = self.analyze(conflict);
                    self.backtrack_to(bt);
                    let asserting = learnt[0];
                    let reason = match self.add_learnt(&learnt) {
                        Some(r) => Reason::Clause(r),
                        None if learnt.len() == 2 => Reason::Binary(learnt[1]),
                        None => Reason::Unit,
                    };
                    self.enqueue(asserting, reason);
                    self.conflicts += 1;
                    self.heuristic.decay();
                    let lbd = self.compute_lbd(&learnt);
                    if let Reason::Clause(r) = reason {
                        self.db.set_lbd(r, lbd);
                    }
                    if self.conflicts % self.config.reduce_interval as u64 == 0 {
                        self.reduce();
                    }
                    self.restart.on_conflict(lbd);
                    if self.restart.should_restart()
                        && self.trail.decision_level() as usize > assumptions.len()
                    {
                        self.restart.on_restart();
                        self.backtrack_to(assumptions.len() as u32);
                    }
                }
                None => {
                    let dl = self.trail.decision_level() as usize;
                    if dl < assumptions.len() {
                        let a = assumptions[dl];
                        match self.assign.lit_value(a) {
                            LBool::True => {
                                self.trail.new_level(); // align levels; no new assignment
                            }
                            LBool::False => {
                                let mut core = self.analyze_final(a.negate());
                                core.push(a);
                                return SolveResult::Unsat { core };
                            }
                            LBool::Unset => {
                                self.trail.new_level();
                                self.enqueue(a, Reason::Decision);
                            }
                        }
                    } else {
                        match self.pick_branch() {
                            Some(l) => {
                                self.trail.new_level();
                                self.enqueue(l, Reason::Decision);
                            }
                            None => return SolveResult::Sat,
                        }
                    }
                }
            }
        }
    }

    /// Collect the assumption/decision literals that entail `p` (which is true
    /// on the trail). The basis of `get-unsat-core` under assumptions.
    fn analyze_final(&mut self, p: Lit) -> Vec<Lit> {
        self.analyzer.ensure_vars(self.assign.num_vars());
        let mut core: Vec<Lit> = Vec::new();
        let mut seen_vars: Vec<Var> = Vec::new();
        self.analyzer.seen[p.var().index()] = true;
        seen_vars.push(p.var());

        let mut i = self.trail.len();
        while i > 0 {
            i -= 1;
            let q = self.trail.lit_at(i);
            let v = q.var();
            if !self.analyzer.seen[v.index()] {
                continue;
            }
            match self.assign.reason(v) {
                Reason::Decision => core.push(q),
                Reason::Unit => {}
                Reason::Binary(other) => {
                    let ov = other.var();
                    if !self.analyzer.seen[ov.index()] && self.assign.level(ov) > 0 {
                        self.analyzer.seen[ov.index()] = true;
                        seen_vars.push(ov);
                    }
                }
                Reason::Clause(r) => {
                    let lits: Vec<Lit> = self.db.lits(r).to_vec();
                    for x in lits {
                        let xv = x.var();
                        if xv != v && !self.analyzer.seen[xv.index()] && self.assign.level(xv) > 0 {
                            self.analyzer.seen[xv.index()] = true;
                            seen_vars.push(xv);
                        }
                    }
                }
                Reason::Theory(_) => {}
            }
        }
        for v in seen_vars {
            self.analyzer.seen[v.index()] = false;
        }
        core
    }
```

- [ ] **Step 5: Run to verify all tests pass**

Run: `cargo test -p shinri-sat`
Expected: all PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): incremental assumptions + analyze_final failed-core"
```

---

### Task 16: Scoped push/pop (conservative rebuild)

A scoped overlay: `push`/`pop` bracket assertions. Phase 1 takes the conservative, obviously-sound route (spec §7.3): on `pop`, rebuild the clause/watch/trail state from the surviving input clauses, dropping all learnt clauses. (In-place removal + `weaken`/restore is a Phase 2 optimization; assumptions are the optimized incremental path.)

**Files:**
- Modify: `crates/shinri-sat/src/assignment.rs` (add `reset` for rebuild)
- Modify: `crates/shinri-sat/src/solver.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces:
  - `Assignment::reset(&mut self)` (clear all values to Unset/level 0; keep var count).
  - `Solver`: `push(&mut self)`, `pop(&mut self, n: usize)`, fields `input_clauses: Vec<Vec<Lit>>`, `scopes: Vec<usize>`; internal `install_clause(&mut self, &[Lit]) -> bool` and `rebuild(&mut self)`.

- [ ] **Step 1: Add `Assignment::reset`**

In `assignment.rs`, inside `impl Assignment`:

```rust
    /// Clear every variable to Unset / level 0, preserving the variable count
    /// and saved phases (used by the conservative push/pop rebuild).
    pub fn reset(&mut self) {
        for v in &mut self.value {
            *v = LBool::Unset;
        }
        for l in &mut self.level {
            *l = 0;
        }
    }
```

- [ ] **Step 2: Write the failing test**

```rust
    #[test]
    fn pop_undoes_scoped_unsat() {
        let mut s = mk(1);
        s.push();
        s.add_clause(&[lit(0, true)]);
        s.add_clause(&[lit(0, false)]); // conflicting units => UNSAT in scope
        assert!(matches!(s.solve(), SolveResult::Unsat { .. }));
        s.pop(1);
        assert_eq!(s.solve(), SolveResult::Sat); // scope undone => satisfiable
    }
```

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-sat -- pop_undoes`
Expected: FAIL — `push`/`pop` not defined.

- [ ] **Step 4: Implement scoping + rebuild**

Add fields to `Solver`: `pub(crate) input_clauses: Vec<Vec<Lit>>,` `pub(crate) scopes: Vec<usize>,` (init both empty in `new`). Refactor `add_clause` to record then install, and add `install_clause`, `rebuild`, `push`, `pop`:

```rust
    /// Add an input clause (records it for push/pop, then installs it).
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        if self.trail.decision_level() != 0 {
            self.backtrack_to(0);
        }
        self.input_clauses.push(lits.to_vec());
        self.install_clause(lits)
    }

    /// Install a clause into the db/watches/trail without recording it.
    fn install_clause(&mut self, lits: &[Lit]) -> bool {
        match lits.len() {
            0 => {
                self.unsat = true;
                false
            }
            1 => {
                if self.enqueue(lits[0], Reason::Unit) {
                    true
                } else {
                    self.unsat = true;
                    false
                }
            }
            2 => {
                self.watches.watch_binary(lits[0], lits[1]);
                true
            }
            _ => {
                let (_id, r) = self.db.add_clause(lits, false);
                self.watches.watch_clause(r, lits[0], lits[1]);
                true
            }
        }
    }

    pub fn push(&mut self) {
        if self.trail.decision_level() != 0 {
            self.backtrack_to(0);
        }
        self.scopes.push(self.input_clauses.len());
    }

    pub fn pop(&mut self, n: usize) {
        for _ in 0..n {
            if let Some(mark) = self.scopes.pop() {
                self.input_clauses.truncate(mark);
            }
        }
        self.rebuild();
    }

    /// Conservative rebuild: reset all derived state and re-install the
    /// surviving input clauses. Drops every learnt clause (spec §7.3).
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
        let inputs = std::mem::take(&mut self.input_clauses);
        for clause in &inputs {
            self.install_clause(clause);
        }
        self.input_clauses = inputs;
    }
```

Delete the old `add_clause` body (now replaced) and keep only the new one. (You'll also need `use crate::trail::Trail;` and `use crate::watch::Watches;` already present.)

- [ ] **Step 5: Run to verify it passes**

Run: `cargo test -p shinri-sat`
Expected: all PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): scoped push/pop via conservative rebuild (drops learnt clauses)"
```

---

### Task 17: `Theory` seam + `NoTheory`; make `Solver` generic over `T` and `P`

Introduces the theory-integration seam (the T in CDCL(T)) and, in the same refactor, the proof type parameter `P` (its call sites are wired in Task 18). Final solver type: `Solver<T: Theory, P: ProofSink, H: BranchHeuristic>`. With `NoTheory`/`NoProof` the theory/proof branches dead-code-eliminate.

**Files:**
- Modify: `crates/shinri-core/src/proof.rs` (add `impl Default for NoProof`)
- Create: `crates/shinri-sat/src/theory.rs`
- Modify: `crates/shinri-sat/src/solver.rs` (generic refactor + theory wiring)
- Modify: `crates/shinri-sat/src/lib.rs` (`pub mod theory;`, exports)
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces:
  - `shinri_core::NoProof: Default`.
  - `crate::theory::Theory` (supertrait `Default`): `assert(&mut self, Lit)`, `propagate(&mut self, &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>>` (returns conflicting literals), `explain(&mut self, TheoryJust, &mut Vec<Lit>)` (the true antecedent literals implying the propagated literal), `check(&mut self, Effort) -> TheoryResult`, `push(&mut self)`, `pop(&mut self, usize)`, `new_var(&mut self, Var)`.
  - `crate::theory::NoTheory` (ZST).
  - `Solver<T: Theory, P: ProofSink, H: BranchHeuristic>` with fields `theory: T`, `proof: P`.

- [ ] **Step 1: Make `NoProof` constructible by `Default`**

In `crates/shinri-core/src/proof.rs`, after `pub struct NoProof;`:

```rust
impl Default for NoProof {
    fn default() -> Self {
        NoProof
    }
}
```

- [ ] **Step 2: Define the `Theory` trait — `theory.rs`**

```rust
use crate::types::{Effort, TheoryResult};
use shinri_core::{Lit, TheoryJust, Var};

/// The theory-integration seam (spec §8.1). Implemented by `shinri-theory`.
/// `NoTheory` makes every method inline to nothing, leaving a pure CDCL solver.
pub trait Theory: Default {
    /// A Boolean literal was placed on the trail.
    fn assert(&mut self, lit: Lit);
    /// Theory propagation: push implied `(lit, justification)` pairs into `out`.
    /// Returns `Some(conflict_lits)` if the theory is inconsistent.
    fn propagate(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>>;
    /// Reconstruct the *true* antecedent literals whose conjunction implied the
    /// literal that carried `just` (lazily, only when analysis needs it).
    fn explain(&mut self, just: TheoryJust, out: &mut Vec<Lit>);
    /// Consistency check at the given effort. `Full` runs before declaring SAT.
    fn check(&mut self, effort: Effort) -> TheoryResult;
    /// Open a backtracking scope (one per SAT decision level).
    fn push(&mut self);
    /// Close `n` scopes (on backtrack).
    fn pop(&mut self, n: usize);
    /// A new variable was allocated.
    fn new_var(&mut self, v: Var);
}

/// The zero-cost default theory: a ZST whose methods compile to nothing.
#[derive(Default)]
pub struct NoTheory;

impl Theory for NoTheory {
    #[inline(always)]
    fn assert(&mut self, _lit: Lit) {}
    #[inline(always)]
    fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
        None
    }
    #[inline(always)]
    fn explain(&mut self, _just: TheoryJust, _out: &mut Vec<Lit>) {}
    #[inline(always)]
    fn check(&mut self, _effort: Effort) -> TheoryResult {
        TheoryResult::Sat
    }
    #[inline(always)]
    fn push(&mut self) {}
    #[inline(always)]
    fn pop(&mut self, _n: usize) {}
    #[inline(always)]
    fn new_var(&mut self, _v: Var) {}
}
```

- [ ] **Step 3: Write the failing tests (NoTheory regression + mock propagation)**

Add to `solver.rs` tests (you'll switch `mk` to the full generic type in Step 5):

```rust
    use crate::theory::{NoTheory, Theory};
    use crate::types::{Effort, TheoryResult};
    use shinri_core::{NoProof, TheoryJust};

    // A toy theory that, once it has seen x0 asserted true, propagates x1 true.
    #[derive(Default)]
    struct ForceX1 {
        saw_x0: bool,
        done: bool,
    }
    impl Theory for ForceX1 {
        fn assert(&mut self, lit: Lit) {
            if lit == Lit::new(Var::new(0), true) {
                self.saw_x0 = true;
            }
        }
        fn propagate(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
            if self.saw_x0 && !self.done {
                self.done = true;
                out.push((Lit::new(Var::new(1), true), TheoryJust { theory: 0, tag: 0 }));
            }
            None
        }
        fn explain(&mut self, _j: TheoryJust, _out: &mut Vec<Lit>) {}
        fn check(&mut self, _e: Effort) -> TheoryResult {
            TheoryResult::Sat
        }
        fn push(&mut self) {}
        fn pop(&mut self, _n: usize) {}
        fn new_var(&mut self, _v: Var) {}
    }

    #[test]
    fn theory_propagation_forces_a_literal() {
        let mut s: Solver<ForceX1, NoProof, Vmtf> =
            Solver::new(SolverConfig::default());
        for _ in 0..2 {
            s.new_var();
        }
        s.add_clause(&[lit(0, true)]); // unit forces x0 true
        assert_eq!(s.solve(), SolveResult::Sat);
        assert_eq!(s.assign.value(Var::new(1)), LBool::True); // theory-propagated
    }
```

- [ ] **Step 4: Run to verify it fails**

Run: `cargo test -p shinri-sat -- theory_propagation`
Expected: FAIL — `Solver` not yet generic over `T`/`P`.

- [ ] **Step 5: Refactor `Solver` to `Solver<T, P, H>` and wire the theory**

Apply in `solver.rs`:

1. Imports: `use crate::theory::Theory;` `use crate::types::{Conflict, Effort, LBool, Reason, SolveResult, TheoryResult};` `use shinri_core::ProofSink;`
2. Struct header + new fields:

```rust
pub struct Solver<T: Theory, P: ProofSink, H: BranchHeuristic> {
    pub(crate) assign: Assignment,
    pub(crate) trail: Trail,
    pub(crate) db: ClauseDb,
    pub(crate) watches: Watches,
    pub(crate) analyzer: Analyzer,
    pub(crate) restart: RestartPolicy,
    pub(crate) config: SolverConfig,
    pub(crate) heuristic: H,
    pub(crate) theory: T,
    pub(crate) proof: P,
    pub(crate) learnts: Vec<ClauseRef>,
    pub(crate) input_clauses: Vec<Vec<Lit>>,
    pub(crate) scopes: Vec<usize>,
    pub(crate) conflicts: u64,
    pub(crate) unsat: bool,
    pub(crate) stats_minimized: u64,
    pub(crate) stats_deleted: u64,
}
```

3. Change every `impl<H: BranchHeuristic> Solver<H>` to `impl<T: Theory, P: ProofSink, H: BranchHeuristic> Solver<T, P, H>`.
4. In `new`, add `theory: T::default(), proof: P::default(),` and in `rebuild` add `self.theory = T::default();` plus `self.theory.new_var(Var::new(i as u32));` inside the var loop.
5. In `new_var`, add `self.theory.new_var(v);`.
6. In `enqueue`, after `self.trail.push(l);`, add `self.theory.assert(l);`.
7. Replace `propagate` with the two-phase version (rename the existing body to `propagate_boolean`):

```rust
    /// Boolean BCP followed by theory propagation, to joint fixpoint.
    pub fn propagate(&mut self) -> Option<Conflict> {
        loop {
            if let Some(c) = self.propagate_boolean() {
                return Some(c);
            }
            let mut out: Vec<(Lit, TheoryJust)> = Vec::new();
            match self.theory.propagate(&mut out) {
                Some(conflict_lits) => return Some(Conflict::Lits(conflict_lits)),
                None => {
                    if out.is_empty() {
                        return None;
                    }
                    for (l, just) in out {
                        self.enqueue(l, Reason::Theory(just));
                    }
                    // loop: Boolean-propagate the new theory literals
                }
            }
        }
    }
```

(Rename the original `propagate` method to `propagate_boolean`, keeping its body verbatim — it already returns `Option<Conflict>` after Boolean BCP.)

8. In `reason_lits_of`, make it `&mut self` and replace the `Reason::Theory` arm:

```rust
            Reason::Theory(just) => {
                let mut antecedents = Vec::new();
                self.theory.explain(just, &mut antecedents);
                // The clause is (p ∨ ¬a1 ∨ ...); resolve against the ¬ai (false).
                antecedents.iter().map(|a| a.negate()).collect()
            }
```

9. Drive theory backtracking from `backtrack_to`:

```rust
    pub(crate) fn backtrack_to(&mut self, level: u32) {
        let from = self.trail.decision_level();
        let assign = &mut self.assign;
        let heuristic = &mut self.heuristic;
        self.trail.backtrack_to(level, |l| {
            assign.unassign(l.var());
            heuristic.on_unassign(l.var());
        });
        if from > level {
            self.theory.pop((from - level) as usize);
        }
    }
```

10. Push a theory scope at every decision. In `solve_under`, after **each** `self.trail.new_level();`, add `self.theory.push();`.
11. Run `check(Full)` before declaring SAT. In `solve_under`'s `pick_branch` arm, replace `None => return SolveResult::Sat,` with:

```rust
                            None => match self.theory.check(Effort::Full) {
                                TheoryResult::Sat => return SolveResult::Sat,
                                TheoryResult::Conflict(lits) => {
                                    if self.trail.decision_level() == 0 {
                                        self.unsat = true;
                                        return SolveResult::Unsat { core: vec![] };
                                    }
                                    let (learnt, bt) = self.analyze(Conflict::Lits(lits));
                                    self.backtrack_to(bt);
                                    let asserting = learnt[0];
                                    let reason = match self.add_learnt(&learnt) {
                                        Some(r) => Reason::Clause(r),
                                        None if learnt.len() == 2 => Reason::Binary(learnt[1]),
                                        None => Reason::Unit,
                                    };
                                    self.enqueue(asserting, reason);
                                }
                                TheoryResult::Lemma(lits) => {
                                    self.add_learnt(&lits);
                                    let dl = self.trail.decision_level();
                                    if dl > 0 {
                                        self.backtrack_to(dl - 1);
                                    }
                                }
                            },
```

- [ ] **Step 6: Switch the test helper `mk` to the full type**

```rust
    fn mk(n_vars: u32) -> Solver<NoTheory, NoProof, Vmtf> {
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..n_vars {
            s.new_var();
        }
        s
    }
```

- [ ] **Step 7: Wire modules, run all tests, commit**

`lib.rs`: `pub mod theory; pub use theory::{NoTheory, Theory};`

Run: `cargo test -p shinri-sat`
Expected: all PASS (including `theory_propagation_forces_a_literal`).

```bash
git add crates/shinri-core/src/proof.rs crates/shinri-sat/src
git commit -m "feat(sat): Theory seam + NoTheory; Solver generic over T, P, H (CDCL(T))"
```

---

### Task 18: Thread `ProofSink` through add/learn/delete

Wires the three proof call sites (spec §8.2). With `NoProof` they dead-code-eliminate; a real sink records the input/learnt/deleted clauses with stable `ClauseId`s.

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `shinri_core::ProofSink` (`input`/`learn`/`theory_lemma`/`delete`), `ClauseId`.
- Produces: proof calls in `install_clause` (input), `analyze`/`solve_under` (learn, with the antecedent `ClauseId` chain), `reduce`/`pop` (delete).

- [ ] **Step 1: Collect the antecedent chain in `analyze`**

The LRAT hint is the set of antecedent clause ids touched during the UIP walk. In `analyze`, add a local `let mut chain: Vec<ClauseId> = Vec::new();` and, each time you resolve on a literal `p` whose reason is `Reason::Clause(r)`, push `self.db.clause_id(r)` into `chain`. Return it alongside the learnt clause: change `analyze`'s signature to `-> (Vec<Lit>, u32, Vec<ClauseId>)` and thread `chain` out. (For `Binary`/`Theory` reasons there is no stored `ClauseId`; Phase 1 records only stored-clause antecedents — sufficient for the Alethe/LRAT consumer in Phase 2, which re-derives the rest.)

- [ ] **Step 2: Write the failing test (a recording sink captures input + learn + delete)**

```rust
    use shinri_core::{ClauseId, ProofSink};

    #[derive(Default)]
    struct CountingSink {
        inputs: u32,
        learns: u32,
        deletes: u32,
    }
    impl ProofSink for CountingSink {
        fn input(&mut self, _c: ClauseId, _lits: &[Lit]) {
            self.inputs += 1;
        }
        fn learn(&mut self, _c: ClauseId, _lits: &[Lit], _chain: &[ClauseId]) {
            self.learns += 1;
        }
        fn theory_lemma(&mut self, _c: ClauseId, _lits: &[Lit], _j: shinri_core::TheoryJust) {}
        fn delete(&mut self, _c: ClauseId) {
            self.deletes += 1;
        }
    }

    #[test]
    fn proof_sink_sees_inputs_and_learns() {
        let mut s: Solver<NoTheory, CountingSink, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..2 {
            s.new_var();
        }
        // Long input clause => one `input` call.
        s.add_clause(&[lit(0, true), lit(1, true), lit(0, false)]);
        s.add_clause(&[lit(0, true), lit(1, false)]);
        s.add_clause(&[lit(0, false), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, false)]);
        let _ = s.solve();
        assert!(s.proof.inputs >= 1, "long input clauses recorded");
    }
```

(Binary input clauses are not stored in `ClauseDb`, so `input` is only called for clauses of length ≥ 3 in Phase 1; the test asserts the long clause was recorded.)

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-sat -- proof_sink`
Expected: FAIL — proof not wired (`s.proof.inputs` stays 0 or signature mismatch).

- [ ] **Step 4: Wire the three call sites**

1. In `install_clause`, in the long-clause `_ =>` arm, after `let (id, r) = self.db.add_clause(lits, false);` (capture `id` now), call `self.proof.input(id, lits);`.
2. In `add_learnt`, in the long-clause arm, after `let (id, r) = self.db.add_clause(learnt, true);`, capture the chain via the caller: change `add_learnt` to take the chain and the asserting clause's `ClauseId`. Simpler: have `solve_under` emit the learn after install:

```rust
                    let (learnt, bt, chain) = self.analyze(conflict);
                    self.backtrack_to(bt);
                    let asserting = learnt[0];
                    let r_opt = self.add_learnt(&learnt);
                    if let Some(r) = r_opt {
                        let id = self.db.clause_id(r);
                        self.proof.learn(id, &learnt, &chain);
                    }
                    let reason = match r_opt {
                        Some(r) => Reason::Clause(r),
                        None if learnt.len() == 2 => Reason::Binary(learnt[1]),
                        None => Reason::Unit,
                    };
                    self.enqueue(asserting, reason);
```

(Apply the same `(learnt, bt, chain)` destructuring to the `TheoryResult::Conflict` arm in Step 11 of Task 17; pass `&chain` to `proof.learn` there too.)

3. In `reduce`, when marking a clause deleted, call `self.proof.delete(self.db.clause_id(r));` right before `self.db.mark_deleted(r);`. In `rebuild` (push/pop), before discarding, you may emit deletes for the learnt clauses; Phase 1 may skip this (the proof consumer treats a fresh scope as a reset) — add a `// TODO(phase2): emit deletes on pop` comment instead of a call to keep pop simple.

- [ ] **Step 5: Run to verify it passes**

Run: `cargo test -p shinri-sat`
Expected: all PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-sat/src
git commit -m "feat(sat): thread ProofSink through input/learn/delete with stable ClauseId"
```

---

### Task 19: Model self-check + UNSAT certificate (DRAT/RUP)

Every `Sat` is re-validated against all input clauses before return (spec §9); UNSAT runs are checked by a from-scratch RUP/DRAT checker over the learnt-clause trace.

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs` (`check_model`, `value_of`, self-check assert, emit *all* learnt clauses)
- Create: `crates/shinri-sat/src/certificate.rs` (`#[cfg(test)]` RUP checker)
- Create: `crates/shinri-sat/tests/props.rs` (proptest model soundness)
- Modify: `crates/shinri-sat/src/lib.rs` (`#[cfg(test)] mod certificate;`)
- Test: inline + `tests/props.rs`

**Interfaces:**
- Produces:
  - `Solver::check_model(&self) -> bool`, `Solver::value_of(&self, Var) -> Option<bool>`.
  - `crate::certificate::check_drat(num_vars: usize, original: &[Vec<Lit>], proof: &[Vec<Lit>]) -> bool`.

- [ ] **Step 1: Add `check_model`, `value_of`, and the self-check**

In `impl ... Solver`:

```rust
    /// The Boolean value of a variable in the current assignment, if assigned.
    pub fn value_of(&self, v: Var) -> Option<bool> {
        match self.assign.value(v) {
            LBool::True => Some(true),
            LBool::False => Some(false),
            LBool::Unset => None,
        }
    }

    /// Every recorded input clause is satisfied by the current assignment.
    pub fn check_model(&self) -> bool {
        self.input_clauses
            .iter()
            .all(|cl| cl.iter().any(|&l| self.assign.lit_value(l) == LBool::True))
    }
```

In `solve_under`, immediately before **each** `return SolveResult::Sat`, add `debug_assert!(self.check_model(), "returned SAT but a clause is unsatisfied");`.

- [ ] **Step 2: Emit *all* learnt clauses to the proof (units/binaries included)**

For the DRAT trace to be complete, change the learn emission in `solve_under` (and the `TheoryResult::Conflict` arm) to emit regardless of storage:

```rust
                    let r_opt = self.add_learnt(&learnt);
                    let pid = match r_opt {
                        Some(r) => self.db.clause_id(r),
                        None => ClauseId::new(u32::MAX), // sentinel id for unit/binary
                    };
                    self.proof.learn(pid, &learnt, &chain);
```

(Replace the previous `if let Some(r) = r_opt { ... }` emission.)

- [ ] **Step 3: Write the failing certificate test**

Create `crates/shinri-sat/src/certificate.rs`:

```rust
use shinri_core::Lit;

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Lit, Var};

    fn cl(spec: &[(u32, bool)]) -> Vec<Lit> {
        spec.iter().map(|&(n, p)| Lit::new(Var::new(n), p)).collect()
    }

    #[test]
    fn rup_certifies_simple_unsat() {
        // (x0) ∧ (¬x0) is UNSAT with an empty proof (RUP of the empty clause).
        let original = vec![cl(&[(0, true)]), cl(&[(0, false)])];
        assert!(check_drat(1, &original, &[]));
    }

    #[test]
    fn rup_rejects_unsound_addition() {
        // Adding (x0) to just (x0 ∨ x1) is NOT RUP -> checker must reject.
        let original = vec![cl(&[(0, true), (1, true)])];
        let bad_proof = vec![cl(&[(0, true)])];
        assert!(!check_drat(2, &original, &bad_proof));
    }
}
```

- [ ] **Step 4: Run to verify it fails**

Run: `cargo test -p shinri-sat -- certificate`
Expected: FAIL — `check_drat` not defined.

- [ ] **Step 5: Implement the RUP/DRAT checker**

Above the test module in `certificate.rs`:

```rust
/// Reverse Unit Propagation: `candidate` is RUP w.r.t. `clauses` iff assuming
/// every literal of `candidate` false and unit-propagating yields a conflict.
fn rup(clauses: &[Vec<Lit>], candidate: &[Lit], num_vars: usize) -> bool {
    let mut val: Vec<Option<bool>> = vec![None; num_vars];
    for &l in candidate {
        let v = l.var().index();
        let b = !l.is_positive(); // assign so that `l` is false
        if val[v] == Some(!b) {
            return true; // contradictory assumptions => trivially conflicting
        }
        val[v] = Some(b);
    }
    loop {
        let mut changed = false;
        for cl in clauses {
            let mut sat = false;
            let mut unassigned: Option<Lit> = None;
            let mut count = 0;
            for &l in cl {
                let v = l.var().index();
                match val[v] {
                    Some(b) => {
                        if b == l.is_positive() {
                            sat = true;
                            break;
                        }
                    }
                    None => {
                        count += 1;
                        unassigned = Some(l);
                    }
                }
            }
            if sat {
                continue;
            }
            if count == 0 {
                return true; // conflict
            }
            if count == 1 {
                let l = unassigned.unwrap();
                val[l.var().index()] = Some(l.is_positive());
                changed = true;
            }
        }
        if !changed {
            return false;
        }
    }
}

/// Check a DRAT-style proof: each added clause must be RUP w.r.t. the clauses
/// so far, and the final clause set must propagate to a conflict (empty-clause
/// RUP). Sound for the RUP-only proofs a CDCL solver emits.
pub fn check_drat(num_vars: usize, original: &[Vec<Lit>], proof: &[Vec<Lit>]) -> bool {
    let mut clauses = original.to_vec();
    for c in proof {
        if !rup(&clauses, c, num_vars) {
            return false;
        }
        clauses.push(c.clone());
    }
    rup(&clauses, &[], num_vars)
}
```

Add to `lib.rs`: `#[cfg(test)] mod certificate;`

- [ ] **Step 6: Add the model-soundness property test — `tests/props.rs`**

```rust
use proptest::prelude::*;
use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

fn build(num_vars: usize, clauses: &[Vec<(u32, bool)>]) -> Solver<NoTheory, NoProof, Vmtf> {
    let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
    for _ in 0..num_vars {
        s.new_var();
    }
    for c in clauses {
        let lits: Vec<Lit> = c.iter().map(|&(n, p)| Lit::new(Var::new(n), p)).collect();
        s.add_clause(&lits);
    }
    s
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]
    #[test]
    fn sat_results_satisfy_every_clause(
        clauses in prop::collection::vec(
            prop::collection::vec((0u32..6, any::<bool>()), 1..4),
            0..20,
        )
    ) {
        let mut s = build(6, &clauses);
        if s.solve() == SolveResult::Sat {
            prop_assert!(s.check_model(), "SAT model violates a clause");
        }
    }
}
```

(`Lit`/`Var`/`NoProof` are re-exported from `shinri-sat` — see the Task 1 `lib.rs` re-export line — so integration tests need no direct `shinri-core` dependency.)

- [ ] **Step 7: Run to verify everything passes**

Run: `cargo test -p shinri-sat`
Expected: all PASS (unit + property tests).

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-sat/src crates/shinri-sat/tests
git commit -m "feat(sat): model self-check + from-scratch RUP/DRAT UNSAT certificate + props"
```

---

### Task 20: Differential oracle harness vs `splr`, across all configs

Random + structured CNF, solved by shinri across every (heuristic × restart) config and by `splr`; **any SAT/UNSAT disagreement is a P0 bug** (spec §10.3).

**Files:**
- Create: `crates/shinri-sat/tests/oracle.rs`
- Test: the integration test itself

**Interfaces:**
- Consumes: the public solver API + `splr` (dev-dependency).

- [ ] **Step 1: Write the differential test**

Create `crates/shinri-sat/tests/oracle.rs`:

```rust
use shinri_sat::{
    BranchHeuristic, Evsids, Lit, NoProof, NoTheory, RestartKind, SolveResult, Solver,
    SolverConfig, Var, Vmtf,
};

/// Tiny deterministic LCG so cases are reproducible without a rand dependency.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 16
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A random 3-CNF over `n` vars with `m` clauses.
fn random_3cnf(seed: u64, n: u64, m: u64) -> Vec<Vec<(u32, bool)>> {
    let mut rng = Lcg(seed.wrapping_add(0x9E3779B97F4A7C15));
    (0..m)
        .map(|_| {
            (0..3)
                .map(|_| ((rng.below(n)) as u32, rng.below(2) == 1))
                .collect()
        })
        .collect()
}

fn run_shinri<H: BranchHeuristic>(
    n: usize,
    clauses: &[Vec<(u32, bool)>],
    cfg: SolverConfig,
) -> (bool, Solver<NoTheory, NoProof, H>) {
    let mut s: Solver<NoTheory, NoProof, H> = Solver::new(cfg);
    for _ in 0..n {
        s.new_var();
    }
    for c in clauses {
        let lits: Vec<Lit> = c.iter().map(|&(v, p)| Lit::new(Var::new(v), p)).collect();
        s.add_clause(&lits);
    }
    (s.solve() == SolveResult::Sat, s)
}

fn to_dimacs(clauses: &[Vec<(u32, bool)>]) -> Vec<Vec<i32>> {
    clauses
        .iter()
        .map(|c| {
            c.iter()
                .map(|&(v, p)| {
                    let lit = (v + 1) as i32;
                    if p { lit } else { -lit }
                })
                .collect()
        })
        .collect()
}

// NOTE: verify these imports against the installed splr version (0.17). The
// `Certificate`/`SolveIF`/`Solver::try_from` surface is stable in 0.17.x; if
// your splr differs, adjust this single helper.
fn splr_is_sat(clauses: &[Vec<i32>]) -> Option<bool> {
    use splr::{Certificate, Config, SolveIF, Solver as SplrSolver, SolverError};
    match SplrSolver::try_from((Config::default(), clauses)) {
        Ok(mut s) => match s.solve() {
            Ok(Certificate::SAT(_)) => Some(true),
            Ok(Certificate::UNSAT) => Some(false),
            Err(_) => None,
        },
        Err(SolverError::EmptyClause) => Some(false),
        Err(_) => None,
    }
}

#[test]
fn differential_random_3cnf_across_configs() {
    let configs = [
        (RestartKind::Luby, false),
        (RestartKind::EmaGlucose, false),
        (RestartKind::Luby, true), // true => use Evsids
        (RestartKind::EmaGlucose, true),
    ];
    for seed in 0..200u64 {
        let n = 8;
        let m = 34; // ~4.26 ratio -> phase transition, mixes SAT/UNSAT
        let clauses = random_3cnf(seed, n as u64, m);
        let dimacs = to_dimacs(&clauses);
        let oracle = match splr_is_sat(&dimacs) {
            Some(b) => b,
            None => continue, // skip instances the oracle can't classify
        };
        for &(restart, use_evsids) in &configs {
            let cfg = SolverConfig { restart, ..SolverConfig::default() };
            let (sat, solver) = if use_evsids {
                run_shinri::<Evsids>(n, &clauses, cfg)
            } else {
                run_shinri::<Vmtf>(n, &clauses, cfg)
            };
            assert_eq!(
                sat, oracle,
                "DISAGREEMENT seed={seed} restart={restart:?} evsids={use_evsids}"
            );
            if sat {
                assert!(solver.check_model(), "SAT but model invalid (seed {seed})");
            }
        }
    }
}
```

- [ ] **Step 2: Run the differential harness**

Run: `cargo test -p shinri-sat --test oracle`
Expected: PASS. If it FAILS with a disagreement, that is a **P0 soundness bug** — use `superpowers:systematic-debugging`; the seed reproduces it deterministically.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-sat/tests/oracle.rs
git commit -m "test(sat): differential oracle vs splr across heuristic/restart configs"
```

---

### Task 21: Fuzz targets + mutation testing + CI

Adds cargo-fuzz targets (parser robustness + structured-CNF-vs-oracle + incremental sequence) and wires a scheduled differential/fuzz CI job; documents `cargo-mutants`. (The base CI job already runs `fmt`/`clippy`/`deny`/`nextest` over the whole workspace, so the new crate is covered for free.)

**Files:**
- Create: `crates/shinri-sat/fuzz/Cargo.toml`
- Create: `crates/shinri-sat/fuzz/fuzz_targets/dimacs_parse.rs`
- Create: `crates/shinri-sat/fuzz/fuzz_targets/cnf_vs_oracle.rs`
- Modify: `.github/workflows/ci.yml` (add a scheduled `differential` job)

**Interfaces:** none (binaries + CI).

- [ ] **Step 1: Create the fuzz crate manifest**

`crates/shinri-sat/fuzz/Cargo.toml`:

```toml
[package]
name = "shinri-sat-fuzz"
version = "0.0.0"
edition = "2021"
publish = false

[package.metadata]
cargo-fuzz = true

[dependencies]
libfuzzer-sys = "0.4"
arbitrary = { version = "1", features = ["derive"] }
shinri-core = { path = "../../shinri-core" }
shinri-sat = { path = "..", features = ["dimacs"] }
splr = "0.17"

[[bin]]
name = "dimacs_parse"
path = "fuzz_targets/dimacs_parse.rs"
test = false
doc = false

[[bin]]
name = "cnf_vs_oracle"
path = "fuzz_targets/cnf_vs_oracle.rs"
test = false
doc = false

[workspace]
```

- [ ] **Step 2: Parser-robustness target — `dimacs_parse.rs`**

```rust
#![no_main]
use libfuzzer_sys::fuzz_target;

// The DIMACS reader must never panic on arbitrary input (spec §9).
fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = shinri_sat::dimacs::parse_dimacs(s);
    }
});
```

- [ ] **Step 3: Structured-CNF-vs-oracle target — `cnf_vs_oracle.rs`**

```rust
#![no_main]
use libfuzzer_sys::fuzz_target;
use shinri_core::{Lit, NoProof, Var};
use shinri_sat::{NoTheory, SolveResult, Solver, SolverConfig, Vmtf};

// Interpret raw bytes as a small CNF; cross-check shinri vs splr. Any
// SAT/UNSAT disagreement is a soundness bug (the fuzzer minimizes the input).
fuzz_target!(|data: &[u8]| {
    if data.len() < 4 {
        return;
    }
    let n = (data[0] % 8 + 1) as usize;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let mut dimacs: Vec<Vec<i32>> = Vec::new();
    let mut i = 1;
    while i + 2 < data.len() {
        let mut cl = Vec::new();
        let mut dl = Vec::new();
        for k in 0..3 {
            let b = data[i + k];
            let v = (b as usize % n) as u32;
            let pos = b & 0x80 == 0;
            cl.push(Lit::new(Var::new(v), pos));
            dl.push(if pos { (v + 1) as i32 } else { -((v + 1) as i32) });
        }
        clauses.push(cl);
        dimacs.push(dl);
        i += 3;
    }
    if clauses.is_empty() {
        return;
    }
    let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
    for _ in 0..n {
        s.new_var();
    }
    for c in &clauses {
        s.add_clause(c);
    }
    let ours = s.solve() == SolveResult::Sat;

    use splr::{Certificate, Config, SolveIF, Solver as SplrSolver};
    if let Ok(mut sp) = SplrSolver::try_from((Config::default(), dimacs.as_slice())) {
        match sp.solve() {
            Ok(Certificate::SAT(_)) => assert!(ours, "shinri UNSAT but splr SAT"),
            Ok(Certificate::UNSAT) => assert!(!ours, "shinri SAT but splr UNSAT"),
            Err(_) => {}
        }
    }
});
```

- [ ] **Step 4: Verify the fuzz targets build**

Run: `cargo +nightly fuzz build` from `crates/shinri-sat/fuzz` (requires `cargo install cargo-fuzz` and a nightly toolchain). If nightly is unavailable, at minimum run `cargo build --manifest-path crates/shinri-sat/fuzz/Cargo.toml` to typecheck.
Expected: builds.

- [ ] **Step 5: Add the scheduled differential CI job**

In `.github/workflows/ci.yml`, add `schedule` to the `on:` triggers and a new job:

```yaml
on:
  push:
  pull_request:
  schedule:
    - cron: '0 3 * * *' # nightly differential/fuzz budget
```

```yaml
  differential:
    runs-on: ubuntu-latest
    if: github.event_name == 'schedule'
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - uses: taiki-e/install-action@v2
        with:
          tool: cargo-nextest
      - name: Extended differential (more cases)
        run: cargo nextest run -p shinri-sat --test oracle
        env:
          PROPTEST_CASES: '4000'
```

- [ ] **Step 6: Document mutation testing**

Mutation testing is a manual/scheduled command (not a blocking CI gate). Record the command in the crate's module docs or a `CONTRIBUTING` note:

```bash
# Confirm the suite kills behavioral mutants in the soundness-critical routines.
cargo mutants -p shinri-sat --file crates/shinri-sat/src/solver.rs --file crates/shinri-sat/src/analyze.rs
```

- [ ] **Step 7: Run the base test suite once more and commit**

Run: `cargo test -p shinri-sat && cargo fmt --all --check && cargo clippy -p shinri-sat --all-targets -- -D warnings`
Expected: all green.

```bash
git add crates/shinri-sat/fuzz .github/workflows/ci.yml
git commit -m "test(sat): cargo-fuzz targets (parser + cnf-vs-oracle), scheduled differential CI"
```

---

## Done

At this point `shinri-sat` is a complete, sound, incremental CDCL(T)-ready SAT solver:
- packed clause arena, two-watched-literals with implicit binaries, 1-UIP analysis + recursive minimization, LBD reduction, Luby + EMA restarts, VMTF + EVSIDS (generic `H`), assumptions + failed-core, conservative push/pop;
- the `Theory` seam (`Solver<NoTheory, NoProof, Vmtf>` monomorphizes to a pure CDCL solver with theory/proof branches eliminated) and `ProofSink` threading, both validated;
- model self-check, a from-scratch RUP/DRAT certificate checker, a differential oracle vs `splr` across all configs, fuzz targets, and a documented mutation-testing command.

**Next (separate plan):** `shinri-theory` + `shinri-euf` (north-star §12 step 3) — the first runnable QF_UF solver, dropping in as `T` via the seam built here.
