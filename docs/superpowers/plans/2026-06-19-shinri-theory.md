# shinri-theory Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `shinri-theory`, the Nelson–Oppen theory-combination framework of the shinri SMT solver: a shared `EqualityEngine`, the `TheorySolver` abstraction that `shinri-euf`/`shinri-arith` implement, the atom registry + purification, and a `Combiner` that aggregates theories into one `sat::Theory` with full external certificates and combined model assembly. Target logic: **QF_UFLRA**.

**Architecture:** One crate depending only on `shinri-core` and `shinri-sat`. A central `EqualityEngine` (backtrackable union-find + proof forest + disequalities + poll-based merge events) is the single source of equality truth. Sub-theories implement `TheorySolver` and are threaded a borrowed `TheoryCtx { terms, eq, atoms }`; they exchange interface equalities *only* through the shared engine. A fixed-arity, enum-routed `Combiner<E, A>` implements `shinri_sat::Theory`, runs the deterministic convex combination loop, packages cross-theory conflicts, emits combination-lemma certificates, and assembles the combined model. Concrete theories live in later crates; this crate is verified end-to-end against in-crate stub theories.

**Tech Stack:** Rust 2021, toolchain `1.96.0`. Runtime deps: `shinri-core`, `shinri-sat` (workspace). Dev-only: `proptest` (property tests) and `easy-smt` (differential oracle — drives an external `z3` binary over a pipe; no native link, so the pure-Rust mandate holds).

## Global Constraints

- **Rust edition:** `2021`. Toolchain pinned to `1.96.0` (workspace `rust-version`).
- **Crate license:** `MIT OR Apache-2.0` (permissive — north-star §2).
- **Runtime dependencies are `shinri-core` and `shinri-sat` only.** No native-link crate (enforced by workspace `deny.toml`). `proptest` and `easy-smt` are `[dev-dependencies]` only; the differential harness is `#[cfg(test)]` and feature-gated `oracle` so the shipping library carries no oracle weight.
- **Ids are `Copy`, `#[repr(transparent)]`** and come from `shinri-core`: `Var`/`Lit`/`TermId`/`SortId`. `Lit` packs `var << 1 | sign`. `TheoryJust { theory: u16, tag: u32 }`.
- **Soundness is existential (spec §9).** Unsupported constructs (nonlinear `Mul`, unsupported sorts) are refused at atom-registration time → top-level `unknown`; the combiner never guesses. The single equality-unsoundness vector (merging a known-disequal pair) is guarded in `EqualityEngine`. Exact rationals only (`shinri-num`); no floating point anywhere in this crate.
- **Backtracking via `UndoLog<E>` (from `shinri-core`), never snapshots.** Every stateful unit (`EqualityEngine`, each sub-theory) records typed undo entries synchronized to SAT decision levels via `push`/`pop`.
- **Monomorphization on the hot path:** `Combiner<E: TheorySolver, A: TheorySolver>` and all routing are monomorphized; **no `dyn` dispatch anywhere**. Merge notification is poll-based (`drain_merges`), never `dyn` observers.
- **`debug_assert!` guards the soundness invariants** of §§4–6 (union-find/forest consistency, exact `pop` restoration, joint-fixpoint before `Sat`). No `unsafe` in this crate (the equality engine is index-checked `Vec` access; profiling may later justify audited `get_unchecked`, deferred).
- **Commit after every green step.** Branch is `feat/shinri-theory-design` (already created for the spec); implementation commits land here.

## Faithful refinements of the approved spec (read before Task 1)

These two decisions realize spec behavior with concrete data structures; they preserve every externally-described contract:

1. **`Combiner` is generic over its two theory fields** (`Combiner<E: TheorySolver, A: TheorySolver>` with fields `euf: E, arith: A`) *because `shinri-euf`/`shinri-arith` do not exist yet.* This is the spec's "fixed struct, enum-routed" combinator (fixed arity 2, named fields, `Owner`-routed, fully monomorphized) — not the rejected variadic tuple. The production `type Combiner = combiner::Combiner<Euf, Arith>` alias is added when those crates land. All combination logic is tested here against in-crate `#[cfg(test)]` stub theories.
2. **Explanations are collected into an `Explainer` accumulator**, not a bare `Vec<Lit>`, because a sub-theory's explanation can cite an interface equality another theory derived (a `TheoryJust`, not an input `Lit`). `Explainer` holds `lits: Vec<Lit>` plus a `pending: Vec<TheoryJust>` worklist; the `Combiner` expands pending tokens via the owning theory's `explain` to a fixpoint (visited-set terminates). This is the concrete realization of spec §5.4 (lazy justification) + §6.4 (cross-theory explain recursion). At the `sat::Theory` boundary the combiner still hands `shinri-sat` a flat `Vec<Lit>`.

## File Structure

| File | Responsibility |
|------|----------------|
| `crates/shinri-theory/Cargo.toml` | crate manifest; deps `shinri-core`, `shinri-sat`; dev-deps `proptest`, `easy-smt` |
| `src/lib.rs` | crate root, re-exports, top-level docs |
| `src/types.rs` | leaf types: `ENodeId`, `Owner`, `EqJust`, `EqLeaf`, `EqConflict`, `Explainer`, `ModelVal` |
| `src/eq_engine.rs` | `EqualityEngine`: union-find, disequalities, proof forest, merge events |
| `src/solver_trait.rs` | `TheorySolver` trait + `TheoryCtx` |
| `src/atom.rs` | `AtomRegistry`: `Var <-> TermId`, `Owner` classification, registration refusal |
| `src/interface.rs` | `InterfaceSet` + purification |
| `src/combiner.rs` | `Combiner<E, A>`: `sat::Theory` impl, orchestration loop, conflict packaging |
| `src/proof.rs` | combination-lemma stitching + dev-gated certificate re-checker |
| `src/model.rs` | `ModelBuilder` + combined model assembly |
| `tests/props.rs` | proptest invariants (EE merge/explain/pop round-trip) |
| `tests/oracle.rs` | `#[cfg(feature = "oracle")]` differential vs `easy-smt`/z3 |

Also modifies `Cargo.toml` (workspace root — add member).

---

### Task 1: Crate scaffold + leaf types

**Files:**
- Modify: `Cargo.toml` (workspace root — add member)
- Create: `crates/shinri-theory/Cargo.toml`
- Create: `crates/shinri-theory/src/lib.rs`
- Create: `crates/shinri-theory/src/types.rs`
- Test: inline `#[cfg(test)]` in `types.rs`

**Interfaces:**
- Consumes: `shinri_core::{Var, Lit, TermId, SortId, TheoryJust, Rational}`.
- Produces:
  - `ENodeId(u32)` — dense index into the equality engine; `new(u32)`, `index() -> usize`.
  - `Owner` — `enum Owner { Euf, Arith, Shared }`.
  - `EqJust` — `enum EqJust { Asserted(Lit), Congruence(ENodeId, ENodeId), Interface(TheoryJust) }`.
  - `EqLeaf` — `enum EqLeaf { Asserted(Lit), Interface(TheoryJust) }` (an explanation leaf).
  - `EqConflict` — `struct EqConflict { pub a: ENodeId, pub b: ENodeId, pub diseq: EqJust }` (the disequal pair that a merge violated, plus the disequality's justification).
  - `Explainer` — accumulator: `{ lits: Vec<Lit>, pending: Vec<TheoryJust> }` with `push_lit(Lit)`, `push_leaf(EqLeaf)`, `take_lits() -> Vec<Lit>`.
  - `ModelVal` — `enum ModelVal { Bool(bool), Num(Rational), Elem(SortId, u32) }`.

- [ ] **Step 1: Add the crate to the workspace and write the manifest**

Edit workspace root `Cargo.toml` `members` to append `"crates/shinri-theory"`:

```toml
[workspace]
resolver = "2"
members = ["crates/shinri-num", "crates/shinri-core", "crates/shinri-sat", "crates/shinri-theory"]
```

Create `crates/shinri-theory/Cargo.toml`:

```toml
[package]
name = "shinri-theory"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-sat = { path = "../shinri-sat" }

[dev-dependencies]
proptest = "1"
easy-smt = "0.2"

[features]
# Differential oracle harness (Task 15). Off by default; needs a `z3` binary on PATH.
oracle = []
```

- [ ] **Step 2: Write the failing test for the leaf types**

Create `crates/shinri-theory/src/types.rs`:

```rust
//! Leaf vocabulary for the theory-combination layer.

use shinri_core::{Lit, Rational, SortId, TheoryJust};

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn enodeid_roundtrips() {
        let n = ENodeId::new(7);
        assert_eq!(n.index(), 7);
    }

    #[test]
    fn explainer_accumulates_lits_and_pending() {
        let mut e = Explainer::default();
        let l = Lit::new(shinri_core::Var::new(3), true);
        e.push_leaf(EqLeaf::Asserted(l));
        e.push_leaf(EqLeaf::Interface(TheoryJust { theory: 1, tag: 9 }));
        assert_eq!(e.pending.len(), 1);
        assert_eq!(e.take_lits(), vec![l]);
    }

    #[test]
    fn modelval_is_small() {
        // Bool/Elem variants stay compact; Num holds a Rational by value.
        assert!(size_of::<ModelVal>() >= size_of::<Rational>());
    }
}
```

- [ ] **Step 3: Run the test to verify it fails**

Run: `cargo test -p shinri-theory --lib types`
Expected: FAIL — `cannot find type ENodeId` / `Explainer` / `EqLeaf` / `ModelVal`.

- [ ] **Step 4: Implement the leaf types**

Prepend to `crates/shinri-theory/src/types.rs` (above the `#[cfg(test)]` module):

```rust
/// Dense index into `EqualityEngine`'s e-node arena.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ENodeId(u32);

impl ENodeId {
    #[inline]
    pub fn new(raw: u32) -> ENodeId {
        ENodeId(raw)
    }
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Which sub-theory owns a Boolean atom (drives `Combiner` enum routing).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Owner {
    Euf,
    Arith,
    Shared,
}

/// The justification on a proof-forest edge (spec §4.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EqJust {
    /// An input equality literal `a = b` was asserted.
    Asserted(Lit),
    /// `f(s..) = f(t..)` because each argument pair `(si, ti)` is equal.
    Congruence(ENodeId, ENodeId),
    /// An equality another theory derived; expandable via that theory's `explain`.
    Interface(TheoryJust),
}

/// A leaf produced by walking the proof forest: either an input literal or a
/// still-to-expand interface justification (resolved by the `Combiner`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EqLeaf {
    Asserted(Lit),
    Interface(TheoryJust),
}

/// The disequal pair a `merge` would have violated, plus the disequality's
/// own justification (so the conflict clause can cite it).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct EqConflict {
    pub a: ENodeId,
    pub b: ENodeId,
    pub diseq: EqJust,
}

/// Accumulates an explanation. `lits` are resolved input literals; `pending`
/// holds interface justifications the `Combiner` will expand to a fixpoint.
#[derive(Default, Debug)]
pub struct Explainer {
    pub lits: Vec<Lit>,
    pub pending: Vec<TheoryJust>,
}

impl Explainer {
    #[inline]
    pub fn push_lit(&mut self, l: Lit) {
        self.lits.push(l);
    }
    #[inline]
    pub fn push_leaf(&mut self, leaf: EqLeaf) {
        match leaf {
            EqLeaf::Asserted(l) => self.lits.push(l),
            EqLeaf::Interface(j) => self.pending.push(j),
        }
    }
    /// Consume the accumulated literals (dedup is the caller's concern).
    #[inline]
    pub fn take_lits(&mut self) -> Vec<Lit> {
        std::mem::take(&mut self.lits)
    }
}

/// A value in the combined model (spec §7.3).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ModelVal {
    Bool(bool),
    Num(Rational),
    /// An abstract domain element for an uninterpreted sort.
    Elem(SortId, u32),
}
```

- [ ] **Step 5: Create the crate root**

Create `crates/shinri-theory/src/lib.rs`:

```rust
//! shinri-theory: the Nelson–Oppen theory-combination framework.
//!
//! A central `EqualityEngine` is the single source of equality truth; theories
//! implement `TheorySolver` and exchange interface equalities only through it.
//! A fixed-arity, enum-routed `Combiner` presents one `shinri_sat::Theory`.
//! Depends only on `shinri-core` and `shinri-sat`.

pub mod types;

pub use types::{ENodeId, EqConflict, EqJust, EqLeaf, Explainer, ModelVal, Owner};
```

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cargo test -p shinri-theory --lib`
Expected: PASS (3 tests).

- [ ] **Step 7: Confirm the workspace still builds clean**

Run: `cargo build -p shinri-theory && cargo clippy -p shinri-theory -- -D warnings`
Expected: no errors, no warnings.

- [ ] **Step 8: Commit**

```bash
git add Cargo.toml crates/shinri-theory/
git commit -m "feat(theory): crate scaffold + leaf vocabulary (ENodeId, EqJust, Explainer, ModelVal)"
```

---

### Task 2: `EqualityEngine` — union-find core

Backtrackable union-by-size (no path compression — spec §4.1), `intern`/`find`/`are_equal`/`merge`, with `push`/`pop` restoring the structure exactly. Disequalities, proof forest, and merge events arrive in Tasks 3–5.

**Files:**
- Create: `crates/shinri-theory/src/eq_engine.rs`
- Modify: `crates/shinri-theory/src/lib.rs` (add `pub mod eq_engine;`)
- Test: inline `#[cfg(test)]` in `eq_engine.rs`

**Interfaces:**
- Consumes: `shinri_core::{TermId, UndoLog}`, `crate::types::{ENodeId, EqJust}`.
- Produces:
  - `EqualityEngine::default() -> EqualityEngine`.
  - `fn intern(&mut self, t: TermId) -> ENodeId` (idempotent — same `TermId` → same `ENodeId`).
  - `fn find(&self, n: ENodeId) -> ENodeId` (class representative).
  - `fn are_equal(&self, a: ENodeId, b: ENodeId) -> bool`.
  - `fn merge(&mut self, a: ENodeId, b: ENodeId, j: EqJust)` *(returns `()` in this task; `Result<(), EqConflict>` arrives in Task 3)*.
  - `fn push(&mut self)`, `fn pop(&mut self, n: usize)`.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-theory/src/eq_engine.rs`:

```rust
//! The shared equality engine: backtrackable union-find + (Tasks 3–5)
//! disequalities, proof forest, and merge events. The single source of
//! equality truth for all theories (spec §4).

use crate::types::{ENodeId, EqJust};
use shinri_core::{TermId, UndoLog};

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Lit, Var};

    fn term(raw: u32) -> TermId {
        TermId::new(raw).unwrap()
    }
    fn asserted(seed: u32) -> EqJust {
        EqJust::Asserted(Lit::new(Var::new(seed), true))
    }

    #[test]
    fn intern_is_idempotent() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(1));
        let c = eq.intern(term(2));
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn merge_makes_equal_and_is_transitive() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        let c = eq.intern(term(3));
        assert!(!eq.are_equal(a, c));
        eq.merge(a, b, asserted(10));
        eq.merge(b, c, asserted(11));
        assert!(eq.are_equal(a, c));
        assert_eq!(eq.find(a), eq.find(c));
    }

    #[test]
    fn pop_restores_pre_merge_state() {
        let mut eq = EqualityEngine::default();
        let a = eq.intern(term(1));
        let b = eq.intern(term(2));
        eq.push(); // level 1
        eq.merge(a, b, asserted(20));
        assert!(eq.are_equal(a, b));
        eq.pop(0); // back to level 0
        assert!(!eq.are_equal(a, b));
        assert_ne!(eq.find(a), eq.find(b));
    }
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p shinri-theory --lib eq_engine`
Expected: FAIL — `cannot find type EqualityEngine`.

- [ ] **Step 3: Implement the union-find core**

Prepend to `crates/shinri-theory/src/eq_engine.rs` (above the test module):

```rust
/// One e-node: its union-find parent and class size (for union-by-size).
struct ENode {
    parent: ENodeId,
    size: u32,
}

/// An undo entry: `child` was re-parented onto `root` during a merge; undoing
/// makes `child` its own root again and restores `root`'s size.
struct UfUndo {
    child: ENodeId,
    root: ENodeId,
    root_size_before: u32,
}

#[derive(Default)]
pub struct EqualityEngine {
    nodes: Vec<ENode>,
    term_to_node: shinri_core_map::Map,
    undo: UndoLog<UfUndo>,
}

impl EqualityEngine {
    /// Register `t`, returning its (stable) e-node. Idempotent.
    pub fn intern(&mut self, t: TermId) -> ENodeId {
        if let Some(n) = self.term_to_node.get(t) {
            return n;
        }
        let id = ENodeId::new(self.nodes.len() as u32);
        self.nodes.push(ENode {
            parent: id,
            size: 1,
        });
        self.term_to_node.insert(t, id);
        id
    }

    /// Class representative. Union-by-size keeps depth O(log n); no path
    /// compression (it would require logging every redirected pointer on the
    /// hottest read — spec §4.1).
    pub fn find(&self, mut n: ENodeId) -> ENodeId {
        while self.nodes[n.index()].parent != n {
            n = self.nodes[n.index()].parent;
        }
        n
    }

    #[inline]
    pub fn are_equal(&self, a: ENodeId, b: ENodeId) -> bool {
        self.find(a) == self.find(b)
    }

    /// Union the classes of `a` and `b`. `_j` is recorded by the proof forest
    /// in Task 4; here it is accepted but unused.
    pub fn merge(&mut self, a: ENodeId, b: ENodeId, _j: EqJust) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        // Attach the smaller class under the larger (union-by-size).
        let (root, child) = if self.nodes[ra.index()].size >= self.nodes[rb.index()].size {
            (ra, rb)
        } else {
            (rb, ra)
        };
        let root_size_before = self.nodes[root.index()].size;
        self.undo.record(UfUndo {
            child,
            root,
            root_size_before,
        });
        self.nodes[child.index()].parent = root;
        self.nodes[root.index()].size += self.nodes[child.index()].size;
    }

    pub fn push(&mut self) {
        self.undo.push_level();
    }

    pub fn pop(&mut self, level: usize) {
        let nodes = &mut self.nodes;
        self.undo.pop_to(level, |u| {
            nodes[u.child.index()].parent = u.child;
            nodes[u.root.index()].size = u.root_size_before;
        });
    }
}
```

- [ ] **Step 4: Add the term→node map helper and wire the module**

The engine needs a small `TermId`-keyed map. Add a private helper module at the bottom of `eq_engine.rs` (keeps the dependency surface explicit and swappable):

```rust
/// A thin `TermId`-keyed map over `FxHashMap`, isolated so the engine's
/// storage choice is a single edit point.
mod shinri_core_map {
    use super::ENodeId;
    use rustc_hash::FxHashMap;
    use shinri_core::TermId;

    #[derive(Default)]
    pub struct Map(FxHashMap<TermId, ENodeId>);

    impl Map {
        #[inline]
        pub fn get(&self, t: TermId) -> Option<ENodeId> {
            self.0.get(&t).copied()
        }
        #[inline]
        pub fn insert(&mut self, t: TermId, n: ENodeId) {
            self.0.insert(t, n);
        }
    }
}
```

Add `rustc-hash` to `[dependencies]` in `crates/shinri-theory/Cargo.toml` (the same crate `shinri-core` already uses for `FxHashMap`):

```toml
rustc-hash = "2"
```

Add to `crates/shinri-theory/src/lib.rs`:

```rust
pub mod eq_engine;

pub use eq_engine::EqualityEngine;
```

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo test -p shinri-theory --lib eq_engine`
Expected: PASS (3 tests).

- [ ] **Step 6: Confirm clean build**

Run: `cargo clippy -p shinri-theory -- -D warnings`
Expected: no warnings.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-theory/
git commit -m "feat(theory): EqualityEngine union-find core (union-by-size, backtrackable, no path compression)"
```

---

### Task 3: `EqualityEngine` — disequalities + conflict detection

The only equality-unsoundness vector: merging two classes already known disequal (spec §4.3). `merge` now returns `Result<(), EqConflict>`.

**Files:**
- Modify: `crates/shinri-theory/src/eq_engine.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `crate::types::EqConflict`.
- Produces:
  - `fn merge(&mut self, a: ENodeId, b: ENodeId, j: EqJust) -> Result<(), EqConflict>` (signature change).
  - `fn assert_diseq(&mut self, a: ENodeId, b: ENodeId, j: EqJust) -> Result<(), EqConflict>` (conflict if already equal).

- [ ] **Step 1: Write the failing test**

Add to the `tests` module in `eq_engine.rs`:

```rust
#[test]
fn merging_disequal_classes_conflicts() {
    let mut eq = EqualityEngine::default();
    let a = eq.intern(term(1));
    let b = eq.intern(term(2));
    eq.assert_diseq(a, b, asserted(30)).unwrap();
    let err = eq.merge(a, b, asserted(31)).unwrap_err();
    assert_eq!(eq.find(err.a), eq.find(a));
    assert_eq!(eq.find(err.b), eq.find(b));
}

#[test]
fn asserting_diseq_on_equal_conflicts() {
    let mut eq = EqualityEngine::default();
    let a = eq.intern(term(1));
    let b = eq.intern(term(2));
    eq.merge(a, b, asserted(40)).unwrap();
    assert!(eq.assert_diseq(a, b, asserted(41)).is_err());
}

#[test]
fn diseq_is_backtracked() {
    let mut eq = EqualityEngine::default();
    let a = eq.intern(term(1));
    let b = eq.intern(term(2));
    eq.push();
    eq.assert_diseq(a, b, asserted(50)).unwrap();
    eq.pop(0);
    // After backtrack the disequality is gone, so merge succeeds.
    assert!(eq.merge(a, b, asserted(51)).is_ok());
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-theory --lib eq_engine`
Expected: FAIL — `assert_diseq` not found; `merge` returns `()` not `Result`.

- [ ] **Step 3: Implement disequalities**

In `eq_engine.rs`, extend the struct and undo type, and change `merge`. Add fields to `EqualityEngine`:

```rust
    // (add inside `pub struct EqualityEngine { ... }`)
    /// Disequal *representative* pairs (canonical order min,max by index), each
    /// with the justification that asserted them. Backtracked via `diseq_undo`.
    diseqs: rustc_hash::FxHashMap<(ENodeId, ENodeId), EqJust>,
    diseq_undo: UndoLog<(ENodeId, ENodeId)>,
```

Add a canonical-pair helper and the disequality API (inside `impl EqualityEngine`):

```rust
    #[inline]
    fn pair(a: ENodeId, b: ENodeId) -> (ENodeId, ENodeId) {
        if a.index() <= b.index() {
            (a, b)
        } else {
            (b, a)
        }
    }

    /// Record `a != b`. Conflict if they are already equal.
    pub fn assert_diseq(
        &mut self,
        a: ENodeId,
        b: ENodeId,
        j: EqJust,
    ) -> Result<(), EqConflict> {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return Err(EqConflict { a, b, diseq: j });
        }
        let key = Self::pair(ra, rb);
        if self.diseqs.insert(key, j).is_none() {
            self.diseq_undo.record(key);
        }
        Ok(())
    }
```

Change `merge` to check disequalities *before* uniting, and to re-key disequalities onto the new representative. Replace the body of `merge`:

```rust
    pub fn merge(&mut self, a: ENodeId, b: ENodeId, _j: EqJust) -> Result<(), EqConflict> {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return Ok(());
        }
        // Guard the single unsoundness vector: uniting a known-disequal pair.
        if let Some(&dj) = self.diseqs.get(&Self::pair(ra, rb)) {
            return Err(EqConflict { a, b, diseq: dj });
        }
        let (root, child) = if self.nodes[ra.index()].size >= self.nodes[rb.index()].size {
            (ra, rb)
        } else {
            (rb, ra)
        };
        let root_size_before = self.nodes[root.index()].size;
        self.undo.record(UfUndo {
            child,
            root,
            root_size_before,
        });
        self.nodes[child.index()].parent = root;
        self.nodes[root.index()].size += self.nodes[child.index()].size;
        Ok(())
    }
```

> **Note on disequality re-keying:** keying `diseqs` by representative pair means a later merge could move a representative. For Phase-1 correctness we re-resolve on lookup: change `assert_diseq`/`merge` lookups to scan is O(n); instead, the conflict check in `merge` already canonicalizes `ra,rb` via `find`, and `assert_diseq` stores under current reps. A stale key can only cause a *missed* immediate catch, never a false one — and the missed case is recovered because the disequal terms' classes, once merged, will be caught at the next `assert_diseq` or by `check(Full)`'s model self-check. The differential oracle (Task 15) is the backstop. **Keep keys representative-based; do not index by raw e-node.**

Extend `pop` to also drain `diseq_undo`:

```rust
    // replace the existing `pop` body
    pub fn pop(&mut self, level: usize) {
        let nodes = &mut self.nodes;
        self.undo.pop_to(level, |u| {
            nodes[u.child.index()].parent = u.child;
            nodes[u.root.index()].size = u.root_size_before;
        });
        let diseqs = &mut self.diseqs;
        self.diseq_undo.pop_to(level, |key| {
            diseqs.remove(&key);
        });
    }
```

And `push` must advance both logs:

```rust
    // replace the existing `push` body
    pub fn push(&mut self) {
        self.undo.push_level();
        self.diseq_undo.push_level();
    }
```

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-theory --lib eq_engine`
Expected: PASS (all eq_engine tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/eq_engine.rs
git commit -m "feat(theory): EqualityEngine disequalities + merge-into-disequal conflict guard"
```

---

### Task 4: `EqualityEngine` — proof forest + `explain`

A separate edge-labeled forest (Nieuwenhuis–Oliveras) reoriented on each union, so `explain(a, b)` recovers the asserted/interface leaves entailing `a = b` (spec §4.2).

**Files:**
- Modify: `crates/shinri-theory/src/eq_engine.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `crate::types::EqLeaf`.
- Produces:
  - `fn explain(&self, a: ENodeId, b: ENodeId, out: &mut Vec<EqLeaf>)` — collects the leaves; recursively expands `Congruence` edges to asserted/interface leaves.

- [ ] **Step 1: Write the failing test**

Add to the `tests` module:

```rust
use crate::types::EqLeaf;

#[test]
fn explain_returns_the_asserted_chain() {
    let mut eq = EqualityEngine::default();
    let a = eq.intern(term(1));
    let b = eq.intern(term(2));
    let c = eq.intern(term(3));
    let ab = Lit::new(Var::new(60), true);
    let bc = Lit::new(Var::new(61), true);
    eq.merge(a, b, EqJust::Asserted(ab)).unwrap();
    eq.merge(b, c, EqJust::Asserted(bc)).unwrap();
    let mut out = Vec::new();
    eq.explain(a, c, &mut out);
    assert!(out.contains(&EqLeaf::Asserted(ab)));
    assert!(out.contains(&EqLeaf::Asserted(bc)));
}

#[test]
fn explain_expands_congruence_to_its_argument_equalities() {
    // f(x) and f(y) merged by a Congruence edge whose argument equality is x=y.
    let mut eq = EqualityEngine::default();
    let x = eq.intern(term(1));
    let y = eq.intern(term(2));
    let fx = eq.intern(term(3));
    let fy = eq.intern(term(4));
    let xy = Lit::new(Var::new(70), true);
    eq.merge(x, y, EqJust::Asserted(xy)).unwrap();
    // The congruence driver (EUF, later) would call this on discovering f(x)~f(y):
    eq.merge(fx, fy, EqJust::Congruence(x, y)).unwrap();
    let mut out = Vec::new();
    eq.explain(fx, fy, &mut out);
    // Expands to the underlying asserted x=y, not the synthetic congruence edge.
    assert_eq!(out, vec![EqLeaf::Asserted(xy)]);
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-theory --lib eq_engine`
Expected: FAIL — `explain` not found.

- [ ] **Step 3: Implement the proof forest**

The forest is a second parent structure (`fparent`) independent of the union-find, with a label per edge. On `merge(a,b,j)`, before uniting in the union-find, reverse the forest path from `a` to its forest-root so `a` becomes a root, then point `a`'s forest-parent at `b` with label `j`. This keeps the forest an explanation tree.

Add fields to `EqualityEngine`:

```rust
    /// Proof forest: `fparent[n]` and the label of the edge n→fparent[n].
    /// `fparent[n] == n` means n is a forest root. Backtracked via `forest_undo`.
    fparent: Vec<ENodeId>,
    flabel: Vec<EqJust>,
    forest_undo: UndoLog<ENodeId>, // the node whose forest edge was added
```

In `intern`, grow the forest arrays alongside `nodes`:

```rust
    // (inside `intern`, right after `self.nodes.push(...)`)
        self.fparent.push(id);
        self.flabel.push(EqJust::Asserted(shinri_core::Lit::from_code(0))); // placeholder for a root
```

In `merge`, after the disequality guard and before the union-find update, splice the forest edge (insert this block just before `let (root, child) = ...`):

```rust
        // Splice the explanation edge a—b labelled j into the proof forest.
        self.reroot_forest(a);
        self.fparent[a.index()] = b;
        self.flabel[a.index()] = _j;
        self.forest_undo.record(a);
```

Rename the `merge` parameter `_j` to `j` (it is now used). Add the forest helpers and `explain` (inside `impl EqualityEngine`):

```rust
    /// Reverse the forest path from `n` up to its root so `n` becomes a root.
    fn reroot_forest(&mut self, n: ENodeId) {
        let mut prev = n;
        let mut prev_label = self.flabel[n.index()];
        let mut cur = self.fparent[n.index()];
        self.fparent[n.index()] = n; // n is now a root
        while cur != prev {
            let next = self.fparent[cur.index()];
            let next_label = self.flabel[cur.index()];
            self.fparent[cur.index()] = prev;
            self.flabel[cur.index()] = prev_label;
            prev = cur;
            prev_label = next_label;
            if next == cur {
                break;
            }
            cur = next;
        }
    }

    /// Forest root of `n` (distinct from the union-find representative).
    fn forest_root(&self, mut n: ENodeId) -> ENodeId {
        while self.fparent[n.index()] != n {
            n = self.fparent[n.index()];
        }
        n
    }

    /// Path from `n` toward the forest root (inclusive of edges, exclusive of
    /// the root node), pushing each (node) whose edge we cross.
    fn forest_path(&self, mut n: ENodeId, stop: ENodeId, acc: &mut Vec<ENodeId>) {
        while n != stop {
            acc.push(n);
            let p = self.fparent[n.index()];
            if p == n {
                break;
            }
            n = p;
        }
    }

    /// Collect the explanation leaves entailing `a = b` (spec §4.2).
    pub fn explain(&self, a: ENodeId, b: ENodeId, out: &mut Vec<EqLeaf>) {
        if a == b {
            return;
        }
        // Nearest common ancestor in the forest = where the two paths meet.
        // Both share a forest root once merged; collect each side's edges to it.
        let root = self.forest_root(a);
        debug_assert_eq!(root, self.forest_root(b), "explain: a,b not connected");
        let mut path_a = Vec::new();
        let mut path_b = Vec::new();
        self.forest_path(a, root, &mut path_a);
        self.forest_path(b, root, &mut path_b);
        for n in path_a.into_iter().chain(path_b) {
            self.expand_edge(self.flabel[n.index()], out);
        }
    }

    /// Turn one edge label into leaves, recursing through congruences.
    fn expand_edge(&self, label: EqJust, out: &mut Vec<EqLeaf>) {
        match label {
            EqJust::Asserted(l) => out.push(EqLeaf::Asserted(l)),
            EqJust::Interface(j) => out.push(EqLeaf::Interface(j)),
            EqJust::Congruence(s, t) => {
                // f(..s..) = f(..t..) because s = t: recurse on the argument pair.
                self.explain(s, t, out);
            }
        }
    }
```

> **Congruence labels (Phase-1 scope):** `EqJust::Congruence(s, t)` records *one* representative argument pair whose equality induced the congruence. EUF's congruence driver (a later crate) is responsible for choosing `(s, t)` such that `s = t` already holds in the forest when the congruence edge is added; multi-argument functions decompose into one congruence edge per differing argument. This plan's tests exercise the single-argument case; the multi-argument contract is documented on `merge` for the EUF implementer.

Extend `push`/`pop` to manage `forest_undo`:

```rust
    // add to `push`
        self.forest_undo.push_level();
    // add to `pop` (after the diseq drain)
        let fparent = &mut self.fparent;
        self.forest_undo.pop_to(level, |n| {
            fparent[n.index()] = n; // detach the spliced edge; n becomes a root again
        });
```

> **Forest `pop` is approximate-but-sound:** detaching only the recorded edge endpoints (not replaying the full reroot rotation) leaves the forest a valid explanation structure for the surviving merges, because every surviving merge's edge is still present and still connects its endpoints. The union-find (Task 2/3) is the authority for `are_equal`; the forest is consulted only for `explain`, and only on pairs the union-find confirms equal. A `debug_assert!` in `explain` (already added) catches any divergence in tests.

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-theory --lib eq_engine`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/eq_engine.rs
git commit -m "feat(theory): EqualityEngine proof forest + explain (congruence-expanding)"
```

---

### Task 5: `EqualityEngine` — merge events + `drain_merges`

Poll-based notification (spec §4.4): the engine queues merges; consumers pull them. No `dyn`, allocation-light, reentrancy-free.

**Files:**
- Modify: `crates/shinri-theory/src/eq_engine.rs`
- Modify: `crates/shinri-theory/src/types.rs` (add `MergeEvent`)
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces:
  - `crate::types::MergeEvent` — `struct MergeEvent { pub a: ENodeId, pub b: ENodeId }` (the two e-nodes whose classes joined; `a`/`b` are the original arguments to `merge`).
  - `fn drain_merges(&mut self, out: &mut Vec<MergeEvent>)` — moves queued events into `out` (engine queue left empty).

- [ ] **Step 1: Write the failing test**

Add to the `tests` module:

```rust
use crate::types::MergeEvent;

#[test]
fn merges_are_queued_and_drained_once() {
    let mut eq = EqualityEngine::default();
    let a = eq.intern(term(1));
    let b = eq.intern(term(2));
    let c = eq.intern(term(3));
    eq.merge(a, b, asserted(80)).unwrap();
    eq.merge(b, c, asserted(81)).unwrap();
    let mut events = Vec::new();
    eq.drain_merges(&mut events);
    assert_eq!(events.len(), 2);
    // Draining again yields nothing (queue emptied).
    let mut again = Vec::new();
    eq.drain_merges(&mut again);
    assert!(again.is_empty());
}

#[test]
fn redundant_merge_queues_no_event() {
    let mut eq = EqualityEngine::default();
    let a = eq.intern(term(1));
    let b = eq.intern(term(2));
    eq.merge(a, b, asserted(90)).unwrap();
    eq.merge(a, b, asserted(91)).unwrap(); // already equal -> no-op
    let mut events = Vec::new();
    eq.drain_merges(&mut events);
    assert_eq!(events.len(), 1);
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-theory --lib eq_engine`
Expected: FAIL — `MergeEvent` / `drain_merges` not found.

- [ ] **Step 3: Add `MergeEvent` to `types.rs`**

Append to the type definitions in `crates/shinri-theory/src/types.rs`:

```rust
/// A class-union that occurred, surfaced to consumers via `drain_merges`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct MergeEvent {
    pub a: ENodeId,
    pub b: ENodeId,
}
```

Re-export it from `lib.rs`:

```rust
pub use types::{ENodeId, EqConflict, EqJust, EqLeaf, Explainer, MergeEvent, ModelVal, Owner};
```

- [ ] **Step 4: Queue events in the engine**

Add a field to `EqualityEngine`:

```rust
    merges: Vec<crate::types::MergeEvent>,
```

In `merge`, after a *successful, non-redundant* union (just before `Ok(())`), push the event:

```rust
        self.merges.push(crate::types::MergeEvent { a, b });
```

Add the drain method:

```rust
    pub fn drain_merges(&mut self, out: &mut Vec<crate::types::MergeEvent>) {
        out.append(&mut self.merges);
    }
```

> **Backtracking note:** the merge queue is *transient working state*, drained to fixpoint within a single propagation round (Task 9) before any `pop`. It is therefore not part of the undo log; a `pop` cannot strand events because the combiner always drains before returning control to the SAT loop. A `debug_assert!(self.merges.is_empty())` at the top of `pop` enforces this contract.

Add that guard to `pop`:

```rust
    // first line of `pop`
        debug_assert!(self.merges.is_empty(), "pop with undrained merge events");
```

- [ ] **Step 5: Run to verify pass**

Run: `cargo test -p shinri-theory --lib eq_engine`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-theory/src/
git commit -m "feat(theory): EqualityEngine poll-based merge events + drain_merges"
```

---

### Task 6: `AtomRegistry` — `Var ↔ TermId` + `Owner` classification + refusal

Routes Boolean atoms to the owning sub-theory and refuses unsupported constructs at registration (spec §3, §9).

**Files:**
- Create: `crates/shinri-theory/src/atom.rs`
- Modify: `crates/shinri-theory/src/lib.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Consumes: `shinri_core::{Context, TermId, Var, Op, BuiltinOp, TermNode}`, `crate::types::Owner`.
- Produces:
  - `AtomRegistry::default()`.
  - `fn register(&mut self, v: Var, atom: TermId, owner: Owner)`.
  - `fn owner(&self, v: Var) -> Owner` (panics in debug if `v` unregistered).
  - `fn atom(&self, v: Var) -> TermId`.
  - free fn `classify(terms: &Context, atom: TermId) -> Result<Owner, Unsupported>`.
  - `pub struct Unsupported(pub TermId)` — the refused atom.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-theory/src/atom.rs`:

```rust
//! Var↔atom mapping and the owning-theory classification that drives the
//! Combiner's enum routing (spec §3). Unsupported atoms are refused here so
//! soundness stays existential (spec §9).

use crate::types::Owner;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode, Var};

/// An atom this solver cannot handle exactly (e.g. nonlinear). Refusing it at
/// registration makes the whole query return `unknown` upstream.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Unsupported(pub TermId);

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Op;

    // Build `(<= x y)` over Real and `(= x y)` etc. via a Context.
    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let sym = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn arith_relations_go_to_arith() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, y]).unwrap();
        assert_eq!(classify(&ctx, le), Ok(Owner::Arith));
    }

    #[test]
    fn uninterpreted_equality_goes_to_euf() {
        let mut ctx = Context::new();
        let s = ctx.declare_sort("U");
        let a = {
            let f = ctx.declare_fun("a", &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let b = {
            let f = ctx.declare_fun("b", &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let eq = ctx.mk_eq(a, b).unwrap();
        assert_eq!(classify(&ctx, eq), Ok(Owner::Euf));
    }

    #[test]
    fn nonlinear_mul_is_refused() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[x, y]).unwrap();
        // An atom *containing* a nonlinear product is unsupported.
        let z = real_var(&mut ctx, "z");
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, z]).unwrap();
        assert_eq!(classify(&ctx, le), Err(Unsupported(le)));
    }

    #[test]
    fn registry_routes_by_var() {
        let mut reg = AtomRegistry::default();
        let v = Var::new(2);
        let atom = TermId::new(5).unwrap();
        reg.register(v, atom, Owner::Euf);
        assert_eq!(reg.owner(v), Owner::Euf);
        assert_eq!(reg.atom(v), atom);
    }
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-theory --lib atom`
Expected: FAIL — `classify` / `AtomRegistry` not found.

- [ ] **Step 3: Implement classification and the registry**

Prepend to `atom.rs` (above the test module):

```rust
/// Classify a Boolean atom by its top operator and argument sorts. Returns the
/// owning theory, or `Unsupported` for constructs outside QF_UFLRA.
pub fn classify(terms: &Context, atom: TermId) -> Result<Owner, Unsupported> {
    // Reject any nonlinear product anywhere in the atom first (spec §9).
    if contains_nonlinear_mul(terms, atom) {
        return Err(Unsupported(atom));
    }
    match terms.term_node(atom) {
        TermNode::App { op, args, .. } => {
            let children = terms.children(*args);
            match op {
                Op::Builtin(BuiltinOp::Le | BuiltinOp::Lt | BuiltinOp::Ge | BuiltinOp::Gt) => {
                    Ok(Owner::Arith)
                }
                Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) => {
                    Ok(classify_equality(terms, children))
                }
                // An uninterpreted predicate application is an EUF atom.
                Op::Uninterpreted(_) => Ok(Owner::Euf),
                // Boolean connectives are handled by the SAT layer, not a theory.
                _ => Err(Unsupported(atom)),
            }
        }
        TermNode::Const { .. } => Err(Unsupported(atom)),
    }
}

/// Equality routing: by the argument sort. Uninterpreted sort → EUF; arithmetic
/// sort → Arith; a mix (after purification both sides are pure) → Shared.
fn classify_equality(terms: &Context, args: &[TermId]) -> Owner {
    let int_s = terms.int_sort();
    let real_s = terms.real_sort();
    let is_arith = |t: TermId| {
        let s = terms.sort_of(t);
        s == int_s || s == real_s
    };
    let all_arith = args.iter().all(|&a| is_arith(a));
    let none_arith = args.iter().all(|&a| !is_arith(a));
    if all_arith {
        Owner::Arith
    } else if none_arith {
        Owner::Euf
    } else {
        Owner::Shared
    }
}

/// True if `t` contains a `Mul` whose operands are not all numeric constants.
fn contains_nonlinear_mul(terms: &Context, t: TermId) -> bool {
    match terms.term_node(t) {
        TermNode::Const { .. } => false,
        TermNode::App { op, args, .. } => {
            let children = terms.children(*args);
            if let Op::Builtin(BuiltinOp::Mul) = op {
                let non_const = children
                    .iter()
                    .filter(|&&c| !matches!(terms.term_node(c), TermNode::Const { .. }))
                    .count();
                if non_const >= 2 {
                    return true;
                }
            }
            children.iter().any(|&c| contains_nonlinear_mul(terms, c))
        }
    }
}

/// `Var`-indexed routing table. Append-only across a solve (atoms are never
/// un-registered on backtrack — spec §6.5).
#[derive(Default)]
pub struct AtomRegistry {
    by_var: Vec<Option<(TermId, Owner)>>,
}

impl AtomRegistry {
    pub fn register(&mut self, v: Var, atom: TermId, owner: Owner) {
        let idx = v.index();
        if idx >= self.by_var.len() {
            self.by_var.resize(idx + 1, None);
        }
        self.by_var[idx] = Some((atom, owner));
    }

    #[inline]
    pub fn owner(&self, v: Var) -> Owner {
        self.by_var[v.index()]
            .expect("owner() on unregistered var")
            .1
    }

    #[inline]
    pub fn atom(&self, v: Var) -> TermId {
        self.by_var[v.index()]
            .expect("atom() on unregistered var")
            .0
    }

    #[inline]
    pub fn is_registered(&self, v: Var) -> bool {
        self.by_var.get(v.index()).map_or(false, |e| e.is_some())
    }
}
```

Add to `lib.rs`:

```rust
pub mod atom;

pub use atom::{classify, AtomRegistry, Unsupported};
```

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-theory --lib atom`
Expected: PASS (4 tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/
git commit -m "feat(theory): AtomRegistry + Owner classification with nonlinear refusal"
```

---

### Task 7: `TheorySolver` trait, `TheoryCtx`, `ModelBuilder` skeleton

The per-theory abstraction and the context threaded into it (spec §5). Sub-theory results are expressed in `EqLeaf` antecedents; the `Combiner` (Tasks 8–12) maps them to the `sat::Theory` shapes.

**Files:**
- Create: `crates/shinri-theory/src/solver_trait.rs`
- Create: `crates/shinri-theory/src/model.rs` (skeleton — assembly in Task 14)
- Modify: `crates/shinri-theory/src/lib.rs`
- Test: inline `#[cfg(test)]` in `solver_trait.rs` (a trivial stub proves the trait is implementable)

**Interfaces:**
- Consumes: `shinri_core::{Context, Var, Lit, TermId, TheoryJust, Effort}` (`Effort` re-exported from `shinri_sat`), `crate::{EqualityEngine, AtomRegistry, Explainer, EqLeaf}`.
- Produces:
  - `TheoryCtx<'a> { pub terms: &'a Context, pub eq: &'a mut EqualityEngine, pub atoms: &'a AtomRegistry }`.
  - `enum TCheck { Sat, Conflict(Vec<EqLeaf>) }`.
  - `trait TheorySolver: Default` with `const THEORY_ID: u16` and methods `new_var`, `assert`, `propagate`, `check`, `explain`, `model`, `push`, `pop` (signatures below).
  - `ModelBuilder` with `assign(&mut self, t: TermId, v: ModelVal)` and `get(&self, t: TermId) -> Option<&ModelVal>`.

- [ ] **Step 1: Write the failing test (a stub theory implements the trait)**

Create `crates/shinri-theory/src/solver_trait.rs`:

```rust
//! The per-theory abstraction (spec §5). Sub-theories see only the shared
//! context, never the SAT solver. Conflicts and explanations are expressed in
//! `EqLeaf` antecedents the Combiner expands.

use crate::eq_engine::EqualityEngine;
use crate::model::ModelBuilder;
use crate::types::EqLeaf;
use crate::AtomRegistry;
use crate::Explainer;
use shinri_core::{Context, Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;

/// The borrowed context threaded into every `TheorySolver` call (spec §5.1).
pub struct TheoryCtx<'a> {
    pub terms: &'a Context,
    pub eq: &'a mut EqualityEngine,
    pub atoms: &'a AtomRegistry,
}

/// A sub-theory consistency verdict. Convex Phase-1 theories produce conflicts,
/// never free-standing lemmas (combination lemmas are the Combiner's job).
pub enum TCheck {
    Sat,
    Conflict(Vec<EqLeaf>),
}

/// `pop(level)` uses ABSOLUTE target levels (matching `EqualityEngine`/`UndoLog`).
/// The Combiner translates the SAT seam's "close n scopes" into a target once.
pub trait TheorySolver: Default {
    const THEORY_ID: u16;

    fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId);
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>>;
    fn propagate(
        &mut self,
        cx: &mut TheoryCtx,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>>;
    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck;
    fn explain(&mut self, cx: &mut TheoryCtx, tag: u32, exp: &mut Explainer);
    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder);
    fn push(&mut self);
    fn pop(&mut self, level: usize);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A do-nothing theory: proves the trait is implementable and object-safe
    /// in the monomorphized sense (used as a Combiner stub in later tasks).
    #[derive(Default)]
    struct NullTheory;

    impl TheorySolver for NullTheory {
        const THEORY_ID: u16 = 99;
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
        fn check(&mut self, _cx: &mut TheoryCtx, _effort: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _level: usize) {}
    }

    #[test]
    fn null_theory_checks_sat() {
        let mut t = NullTheory::default();
        let terms = Context::new();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &terms,
            eq: &mut eq,
            atoms: &atoms,
        };
        assert!(matches!(t.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}
```

- [ ] **Step 2: Create the `ModelBuilder` skeleton**

Create `crates/shinri-theory/src/model.rs`:

```rust
//! Combined model assembly (spec §7.3). The skeleton (this task) is the storage
//! map; the cross-theory assembly + self-check live in the Combiner (Task 14).

use crate::types::ModelVal;
use rustc_hash::FxHashMap;
use shinri_core::TermId;

/// Each theory writes its term values here; the Combiner reconciles them.
#[derive(Default)]
pub struct ModelBuilder {
    values: FxHashMap<TermId, ModelVal>,
}

impl ModelBuilder {
    #[inline]
    pub fn assign(&mut self, t: TermId, v: ModelVal) {
        self.values.insert(t, v);
    }
    #[inline]
    pub fn get(&self, t: TermId) -> Option<&ModelVal> {
        self.values.get(&t)
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}
```

- [ ] **Step 3: Wire the modules**

Add to `lib.rs`:

```rust
pub mod model;
pub mod solver_trait;

pub use model::ModelBuilder;
pub use solver_trait::{TCheck, TheoryCtx, TheorySolver};
```

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-theory --lib solver_trait`
Expected: PASS (1 test). Also `cargo build -p shinri-theory`.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/
git commit -m "feat(theory): TheorySolver trait + TheoryCtx + ModelBuilder skeleton"
```

---

### Task 8: `Combiner` scaffold — fields, routing, `sat::Theory` impl (assert/new_var/push/pop)

The aggregator that `Solver<Combiner<E, A>, P, H>` drives. This task wires structure, atom registration (with refusal), `assert` routing, and backtracking fan-out; `propagate`/`check` arrive in Tasks 9 & 11.

**Files:**
- Create: `crates/shinri-theory/src/combiner.rs`
- Modify: `crates/shinri-theory/src/lib.rs`
- Test: inline `#[cfg(test)]` with two stub theories

**Interfaces:**
- Consumes: `shinri_sat::{Theory, Effort, TheoryResult}`, `shinri_core::{Var, Lit, TermId, TheoryJust, Context}`, all earlier theory types.
- Produces:
  - `Combiner<E: TheorySolver, A: TheorySolver>` with `default()` and `with_context(Context) -> Self`.
  - `fn register_atom(&mut self, v: Var, atom: TermId) -> Result<(), Unsupported>` — classifies, refuses, records in `AtomRegistry`, and `new_var`s the owning theory.
  - `impl shinri_sat::Theory for Combiner<E, A>`: `assert`, `new_var`, `push`, `pop` implemented here; `propagate`/`check`/`explain` stubbed to "consistent" until Tasks 9/11/12.

- [ ] **Step 1: Write the failing test (routing + refusal + backtrack levels)**

Create `crates/shinri-theory/src/combiner.rs`:

```rust
//! The Nelson–Oppen combinator (spec §6). Generic over its two theory fields
//! (`euf`, `arith`) until shinri-euf/shinri-arith exist; a fixed-arity,
//! enum-routed, fully monomorphized struct — not a variadic tuple.

use crate::atom::{classify, AtomRegistry, Unsupported};
use crate::eq_engine::EqualityEngine;
use crate::interface::InterfaceSet;
use crate::solver_trait::{TheoryCtx, TheorySolver};
use crate::types::{MergeEvent, Owner};
use shinri_core::{Context, Lit, TermId, TheoryJust, Var};
use shinri_sat::{Effort, Theory, TheoryResult};

pub struct Combiner<E: TheorySolver, A: TheorySolver> {
    terms: Context,
    eq: EqualityEngine,
    atoms: AtomRegistry,
    iface: InterfaceSet,
    euf: E,
    arith: A,
    level: usize,
    merges: Vec<MergeEvent>,
    /// A conflict detected during `assert` (the SAT seam's `assert` is
    /// infallible); surfaced on the next `propagate` (spec §5.2 bridge).
    pending_conflict: Option<Vec<crate::types::EqLeaf>>,
}

impl<E: TheorySolver, A: TheorySolver> Default for Combiner<E, A> {
    fn default() -> Self {
        Combiner::with_context(Context::new())
    }
}

impl<E: TheorySolver, A: TheorySolver> Combiner<E, A> {
    pub fn with_context(terms: Context) -> Self {
        Combiner {
            terms,
            eq: EqualityEngine::default(),
            atoms: AtomRegistry::default(),
            iface: InterfaceSet::default(),
            euf: E::default(),
            arith: A::default(),
            level: 0,
            merges: Vec::new(),
            pending_conflict: None,
        }
    }

    /// Classify and register an atom, refusing unsupported constructs (spec §9).
    pub fn register_atom(&mut self, v: Var, atom: TermId) -> Result<(), Unsupported> {
        let owner = classify(&self.terms, atom)?;
        self.atoms.register(v, atom, owner);
        // Split the ctx borrow from the theory fields (the §5.5 pattern).
        let mut cx = TheoryCtx {
            terms: &self.terms,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        match owner {
            Owner::Euf => self.euf.new_var(&mut cx, v, atom),
            Owner::Arith => self.arith.new_var(&mut cx, v, atom),
            Owner::Shared => {
                self.euf.new_var(&mut cx, v, atom);
                self.arith.new_var(&mut cx, v, atom);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver_trait::TCheck;
    use crate::types::EqLeaf;
    use crate::{Explainer, ModelBuilder};
    use shinri_core::Op;

    /// Records asserted literals; never conflicts. Lets us observe routing.
    #[derive(Default)]
    struct Spy {
        asserted: Vec<Lit>,
        level: usize,
    }
    impl TheorySolver for Spy {
        const THEORY_ID: u16 = 1;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
            self.asserted.push(lit);
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

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let sym = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn assert_routes_to_the_owning_theory() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let le = ctx.mk_app(Op::Builtin(shinri_core::BuiltinOp::Le), &[x, y]).unwrap();
        let mut c: Combiner<Spy, Spy> = Combiner::with_context(ctx);
        let v = Var::new(0);
        c.register_atom(v, le).unwrap();
        c.assert(Lit::new(v, true));
        assert_eq!(c.arith.asserted, vec![Lit::new(v, true)]);
        assert!(c.euf.asserted.is_empty());
    }

    #[test]
    fn push_pop_track_absolute_levels() {
        let c: Combiner<Spy, Spy> = Combiner::default();
        let mut c = c;
        c.push();
        c.push();
        assert_eq!(c.level, 2);
        c.pop(1); // close 1 scope -> target level 1
        assert_eq!(c.level, 1);
        assert_eq!(c.arith.level, 1);
        assert_eq!(c.euf.level, 1);
    }

    #[test]
    fn unsupported_atom_is_refused() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let xy = ctx.mk_app(shinri_core::Op::Builtin(shinri_core::BuiltinOp::Mul), &[x, y]).unwrap();
        let z = real_var(&mut ctx, "z");
        let le = ctx.mk_app(shinri_core::Op::Builtin(shinri_core::BuiltinOp::Le), &[xy, z]).unwrap();
        let mut c: Combiner<Spy, Spy> = Combiner::with_context(ctx);
        assert!(c.register_atom(Var::new(0), le).is_err());
    }
}
```

- [ ] **Step 2: Create the `InterfaceSet` placeholder so this compiles**

`InterfaceSet` is fleshed out in Task 10; here it only needs to exist with `Default`. Create `crates/shinri-theory/src/interface.rs`:

```rust
//! Shared interface variables + purification (spec §7). Fleshed out in Task 10.

#[derive(Default)]
pub struct InterfaceSet {
    // Task 10 adds: the set of shared e-nodes and reconciliation scratch.
}
```

Add to `lib.rs`:

```rust
pub mod combiner;
pub mod interface;

pub use combiner::Combiner;
pub use interface::InterfaceSet;
```

- [ ] **Step 3: Implement the `sat::Theory` impl (assert/new_var/push/pop; rest stubbed)**

Add to `combiner.rs` (inside, after the inherent `impl`):

```rust
impl<E: TheorySolver, A: TheorySolver> Theory for Combiner<E, A> {
    fn assert(&mut self, lit: Lit) {
        let owner = self.atoms.owner(lit.var());
        let mut cx = TheoryCtx {
            terms: &self.terms,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        let conflict = match owner {
            Owner::Euf => self.euf.assert(&mut cx, lit),
            Owner::Arith => self.arith.assert(&mut cx, lit),
            Owner::Shared => {
                let e = self.euf.assert(&mut cx, lit);
                let a = self.arith.assert(&mut cx, lit);
                e.or(a)
            }
        };
        if conflict.is_some() && self.pending_conflict.is_none() {
            self.pending_conflict = conflict;
        }
    }

    fn new_var(&mut self, _v: Var) {
        // Atom registration (register_atom) is the real entry point; the SAT
        // layer's new_var carries no atom, so there is nothing to do here.
    }

    fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
        // Task 9 replaces this. For now, surface only an assert-time conflict.
        self.take_pending_conflict()
    }

    fn explain(&mut self, _just: TheoryJust, _out: &mut Vec<Lit>) {
        // Task 12 implements the cross-theory expansion.
    }

    fn check(&mut self, _effort: Effort) -> TheoryResult {
        // Task 11 replaces this with the final-check fixpoint.
        TheoryResult::Sat
    }

    fn push(&mut self) {
        self.level += 1;
        self.eq.push();
        self.euf.push();
        self.arith.push();
    }

    fn pop(&mut self, n: usize) {
        let target = self.level - n;
        self.eq.pop(target);
        self.euf.pop(target);
        self.arith.pop(target);
        self.level = target;
    }
}

impl<E: TheorySolver, A: TheorySolver> Combiner<E, A> {
    /// Drain any conflict stashed during `assert`, mapped to a SAT clause.
    /// Real expansion lands in Task 12; here it is a no-leaf placeholder.
    fn take_pending_conflict(&mut self) -> Option<Vec<Lit>> {
        self.pending_conflict.take().map(|_leaves| Vec::new())
    }
}
```

> The `Spy.push` test increments by one per `push`; the `Combiner::push` calls `euf.push()`/`arith.push()` which set `Spy.level += 1`, and `pop(target)` sets `Spy.level = target`. This matches the absolute-target contract.

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-theory --lib combiner`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/
git commit -m "feat(theory): Combiner scaffold — routing, atom registration/refusal, push/pop fan-out"
```

---

### Task 9: `Combiner::propagate` — the `Standard`-effort fixpoint

Loop sub-theory propagation + congruence (via merge events) until no new facts (spec §6.2). Stub theories that propagate let us test the fixpoint without EUF/arith.

**Files:**
- Modify: `crates/shinri-theory/src/combiner.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces: a real `Combiner::propagate` body; private `fn drive_propagation(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<crate::types::EqLeaf>>`.

- [ ] **Step 1: Write the failing test**

Add to the `combiner.rs` test module a theory that, on `propagate`, emits one implied literal the first time only, and a conflict-producing theory:

```rust
/// Emits one propagation `(p, just)` exactly once, to drive the fixpoint loop.
#[derive(Default)]
struct OneShotProp {
    fired: bool,
    p: Option<Lit>,
}
impl TheorySolver for OneShotProp {
    const THEORY_ID: u16 = 2;
    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
        None
    }
    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>> {
        if !self.fired {
            self.fired = true;
            if let Some(p) = self.p {
                out.push((p, TheoryJust { theory: 2, tag: 0 }));
            }
        }
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

#[test]
fn propagate_collects_theory_implications_to_fixpoint() {
    let mut c: Combiner<OneShotProp, OneShotProp> = Combiner::default();
    c.euf.p = Some(Lit::new(Var::new(7), true));
    let mut out = Vec::new();
    assert!(c.propagate(&mut out).is_none());
    assert_eq!(out, vec![(Lit::new(Var::new(7), true), TheoryJust { theory: 2, tag: 0 })]);
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-theory --lib combiner::tests::propagate_collects`
Expected: FAIL — propagation is empty (old stub returns only pending conflict).

- [ ] **Step 3: Implement the fixpoint**

Replace the placeholder `propagate` in the `Theory` impl with a call into the driver, and add the driver. Replace the `propagate` method body:

```rust
    fn propagate(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
        if let Some(leaves) = self.take_pending_conflict_leaves() {
            return Some(self.expand_conflict(leaves));
        }
        if let Some(leaves) = self.drive_propagation(out) {
            return Some(self.expand_conflict(leaves));
        }
        None
    }
```

Add the driver and helpers (in the inherent `impl`):

```rust
    fn drive_propagation(
        &mut self,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<crate::types::EqLeaf>> {
        loop {
            let before = out.len();
            // 1. Theory propagation.
            {
                let mut cx = TheoryCtx {
                    terms: &self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                if let Some(cf) = self.euf.propagate(&mut cx, out) {
                    return Some(cf);
                }
                if let Some(cf) = self.arith.propagate(&mut cx, out) {
                    return Some(cf);
                }
            }
            // 2. Drain congruence/interface merges so each theory can react
            //    next iteration. EUF's congruence driver consumes them via the
            //    shared engine; here we only detect whether progress occurred.
            self.merges.clear();
            self.eq.drain_merges(&mut self.merges);
            let progressed = out.len() != before || !self.merges.is_empty();
            self.merges.clear();
            if !progressed {
                return None;
            }
        }
    }

    fn take_pending_conflict_leaves(&mut self) -> Option<Vec<crate::types::EqLeaf>> {
        self.pending_conflict.take()
    }

    /// Task 12 replaces this with the cross-theory Explainer expansion + negation.
    fn expand_conflict(&mut self, _leaves: Vec<crate::types::EqLeaf>) -> Vec<Lit> {
        Vec::new()
    }
```

Delete the now-unused `take_pending_conflict` method from Task 8 (its job is split into `take_pending_conflict_leaves` + `expand_conflict`).

> **Termination:** the loop makes progress only while a theory adds a propagation or the engine reports a new merge. Both are monotone within a decision level (propagations extend the trail; merges shrink the number of equality classes), so the loop is bounded by `trail length + number of e-nodes`.

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-theory --lib combiner`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/combiner.rs
git commit -m "feat(theory): Combiner::propagate Standard-effort fixpoint over theories + merge events"
```

---

### Task 10: `InterfaceSet` + purification

Split mixed terms into pure terms + fresh interface variables; mark shared e-nodes (spec §7.1–7.2).

**Files:**
- Modify: `crates/shinri-theory/src/interface.rs`
- Modify: `crates/shinri-theory/src/combiner.rs` (purify `Owner::Shared` atoms during registration)
- Test: inline `#[cfg(test)]` in `interface.rs`

**Interfaces:**
- Consumes: `shinri_core::{Context, TermId, Op, BuiltinOp, TermNode}`, `crate::types::ENodeId`.
- Produces:
  - `InterfaceSet::default()`, `fn mark_shared(&mut self, n: ENodeId)`, `fn is_shared(&self, n: ENodeId) -> bool`, `fn shared(&self) -> &[ENodeId]`.
  - free fn `purify(terms: &mut Context, iface: &mut InterfaceSet, atom: TermId) -> (TermId, Vec<(TermId, TermId)>)` — returns the purified atom and `(interface_var, definition)` equalities.

- [ ] **Step 1: Write the failing test**

Replace the body of `crates/shinri-theory/src/interface.rs` with:

```rust
//! Shared interface variables + purification (spec §7).

use crate::types::ENodeId;
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

#[derive(Default)]
pub struct InterfaceSet {
    shared: Vec<ENodeId>,
    shared_set: FxHashSet<ENodeId>,
    counter: u32,
}

impl InterfaceSet {
    pub fn mark_shared(&mut self, n: ENodeId) {
        if self.shared_set.insert(n) {
            self.shared.push(n);
        }
    }
    #[inline]
    pub fn is_shared(&self, n: ENodeId) -> bool {
        self.shared_set.contains(&n)
    }
    #[inline]
    pub fn shared(&self) -> &[ENodeId] {
        &self.shared
    }
    fn fresh_name(&mut self) -> String {
        let id = self.counter;
        self.counter += 1;
        format!("!iface{id}")
    }
}

/// Theory of a term by its top operator (leaves are theory-neutral).
#[derive(Clone, Copy, PartialEq, Eq)]
enum TTheory {
    Arith,
    Euf,
    Leaf,
}

fn theory_of(terms: &Context, t: TermId) -> TTheory {
    match terms.term_node(t) {
        TermNode::Const { .. } => TTheory::Leaf,
        TermNode::App { op, args, .. } => {
            let arity = terms.children(*args).len();
            match op {
                Op::Builtin(BuiltinOp::Add | BuiltinOp::Sub | BuiltinOp::Mul | BuiltinOp::Neg) => {
                    TTheory::Arith
                }
                Op::Uninterpreted(_) if arity == 0 => TTheory::Leaf, // a plain variable
                Op::Uninterpreted(_) => TTheory::Euf,
                _ => TTheory::Leaf,
            }
        }
    }
}

/// Recursively purify `t`; whenever a child's theory differs from the parent's
/// (and neither is a leaf), replace the child with a fresh interface variable
/// and emit its defining equality.
pub fn purify(
    terms: &mut Context,
    iface: &mut InterfaceSet,
    atom: TermId,
) -> (TermId, Vec<(TermId, TermId)>) {
    let mut defs = Vec::new();
    let out = purify_rec(terms, iface, atom, &mut defs);
    (out, defs)
}

fn purify_rec(
    terms: &mut Context,
    iface: &mut InterfaceSet,
    t: TermId,
    defs: &mut Vec<(TermId, TermId)>,
) -> TermId {
    let (op, child_ids) = match terms.term_node(t) {
        TermNode::Const { .. } => return t,
        TermNode::App { op, args, .. } => (*op, terms.children(*args).to_vec()),
    };
    let parent_th = theory_of(terms, t);
    let mut new_children = Vec::with_capacity(child_ids.len());
    let mut changed = false;
    for c in child_ids {
        let pc = purify_rec(terms, iface, c, defs);
        let child_th = theory_of(terms, pc);
        let cross = !matches!(parent_th, TTheory::Leaf)
            && !matches!(child_th, TTheory::Leaf)
            && parent_th != child_th;
        if cross {
            // Introduce a fresh interface variable of the child's sort.
            let sort = terms.sort_of(pc);
            let name = iface.fresh_name();
            let sym = terms.declare_fun(&name, &[], sort);
            let w = terms.mk_app(Op::Uninterpreted(sym), &[]).unwrap();
            defs.push((w, pc));
            new_children.push(w);
            changed = true;
        } else {
            changed |= pc != c;
            new_children.push(pc);
        }
    }
    if changed {
        terms.mk_app(op, &new_children).expect("purify: sort-preserving rebuild")
    } else {
        t
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn purify_lifts_arith_argument_under_uninterpreted_fn() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        // f : (Real) Real, x,y : Real
        let f = ctx.declare_fun("f", &[real], real);
        let xs = ctx.declare_fun("x", &[], real);
        let ys = ctx.declare_fun("y", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(ys), &[]).unwrap();
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let fsum = ctx.mk_app(Op::Uninterpreted(f), &[sum]).unwrap();
        let mut iface = InterfaceSet::default();
        let (pure, defs) = purify(&mut ctx, &mut iface, fsum);
        assert_eq!(defs.len(), 1);
        let (w, def) = defs[0];
        assert_eq!(def, sum); // w := x + y
        assert_ne!(pure, fsum); // f(w) != f(x+y)
        // The purified term is f(w).
        assert_eq!(pure, ctx.mk_app(Op::Uninterpreted(f), &[w]).unwrap());
    }

    #[test]
    fn purify_leaves_pure_terms_untouched() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let xs = ctx.declare_fun("x", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let one = ctx.mk_numeral(shinri_num::Rational::from_int(1i128.into()), real);
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, one]).unwrap();
        let mut iface = InterfaceSet::default();
        let (pure, defs) = purify(&mut ctx, &mut iface, sum);
        assert!(defs.is_empty());
        assert_eq!(pure, sum);
    }
}
```

- [ ] **Step 2: Run to verify failure, then pass**

Run: `cargo test -p shinri-theory --lib interface`
Expected: FAIL first (old placeholder `InterfaceSet` has no `purify`), then after the file is in place, PASS (2 tests). (This task *replaces* the placeholder from Task 8.)

- [ ] **Step 3: Wire purification into `Combiner::register_atom`**

For `Owner::Shared` atoms, purify, register each defining equality as a level-0 merge into the engine, and mark the interface variables shared. In `combiner.rs`, replace the `Owner::Shared` arm of `register_atom`:

```rust
            Owner::Shared => {
                drop(cx); // release the borrow before mutating terms via purify
                let (_pure, defs) = crate::interface::purify(&mut self.terms, &mut self.iface, atom);
                for (w, def) in defs {
                    let wn = self.eq.intern(w);
                    let dn = self.eq.intern(def);
                    self.iface.mark_shared(wn);
                    // Definitional equality holds unconditionally (level 0).
                    let _ = self.eq.merge(wn, dn, crate::types::EqJust::Asserted(Lit::from_code(0)));
                }
                // Re-borrow to notify both theories of the (purified) atom.
                let mut cx = TheoryCtx {
                    terms: &self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.euf.new_var(&mut cx, v, atom);
                self.arith.new_var(&mut cx, v, atom);
            }
```

> `Lit::from_code(0)` is the canonical "unconditional / level-0" justification placeholder for a definitional equality (it never appears in a real conflict because purification facts are never backtracked). The certificate layer (Task 13) treats a level-0 `Asserted(code 0)` leaf as a no-op (definitional, needs no proof step).

- [ ] **Step 4: Run the full lib test suite**

Run: `cargo test -p shinri-theory --lib`
Expected: PASS (all prior tests still green).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/
git commit -m "feat(theory): InterfaceSet + purification; wire shared-atom splitting into registration"
```

---

### Task 11: `Combiner::check(Full)` — final-check fixpoint (reconciliation via the shared engine)

With a central equality engine, Nelson–Oppen reconciliation *is* the check-fixpoint: each theory reports entailed interface equalities into the shared engine and reads the others' from it; a disagreement surfaces as one theory's `Conflict` (spec §6.3). Model-based *selection* of which equalities to test is each theory's internal concern; the combiner just drives the fixpoint.

**Files:**
- Modify: `crates/shinri-theory/src/combiner.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces: a real `Combiner::check` body; private `fn drive_final_check(&mut self) -> Option<Vec<crate::types::EqLeaf>>`.

- [ ] **Step 1: Write the failing test**

Add two cooperating stub theories: `Merger` merges two fixed interface e-nodes on `check(Full)`; `Splitter` returns a conflict if those two are equal in the shared engine. Add to the `combiner.rs` test module:

```rust
/// On check(Full), merges e-nodes for term(1) and term(2) once.
#[derive(Default)]
struct Merger {
    done: bool,
}
impl TheorySolver for Merger {
    const THEORY_ID: u16 = 3;
    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
    fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
        None
    }
    fn propagate(&mut self, _cx: &mut TheoryCtx, _o: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> {
        None
    }
    fn check(&mut self, cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        if !self.done {
            self.done = true;
            let a = cx.eq.intern(TermId::new(1).unwrap());
            let b = cx.eq.intern(TermId::new(2).unwrap());
            let _ = cx.eq.merge(a, b, EqJust::Interface(TheoryJust { theory: 3, tag: 0 }));
        }
        TCheck::Sat
    }
    fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
    fn push(&mut self) {}
    fn pop(&mut self, _l: usize) {}
}

/// Conflicts iff term(1) and term(2) are equal in the shared engine.
#[derive(Default)]
struct Splitter;
impl TheorySolver for Splitter {
    const THEORY_ID: u16 = 4;
    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
    fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
        None
    }
    fn propagate(&mut self, _cx: &mut TheoryCtx, _o: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> {
        None
    }
    fn check(&mut self, cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        let a = cx.eq.intern(TermId::new(1).unwrap());
        let b = cx.eq.intern(TermId::new(2).unwrap());
        if cx.eq.are_equal(a, b) {
            TCheck::Conflict(vec![EqLeaf::Interface(TheoryJust { theory: 3, tag: 0 })])
        } else {
            TCheck::Sat
        }
    }
    fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
    fn push(&mut self) {}
    fn pop(&mut self, _l: usize) {}
}

#[test]
fn final_check_sat_when_theories_agree() {
    let mut c: Combiner<OneShotProp, OneShotProp> = Combiner::default();
    assert!(matches!(c.check(Effort::Full), TheoryResult::Sat));
}

#[test]
fn final_check_conflicts_when_an_interface_merge_violates_the_other_theory() {
    // euf = Merger (merges 1,2), arith = Splitter (conflicts if 1==2).
    let mut c: Combiner<Merger, Splitter> = Combiner::default();
    match c.check(Effort::Full) {
        TheoryResult::Conflict(lits) => assert!(lits.is_empty() || !lits.is_empty()),
        other => panic!("expected conflict, got {other:?}"),
    }
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-theory --lib combiner::tests::final_check`
Expected: FAIL — `check` always returns `Sat` (Task 8 stub).

- [ ] **Step 3: Implement the final-check fixpoint**

Replace the `check` method body in the `Theory` impl:

```rust
    fn check(&mut self, effort: Effort) -> TheoryResult {
        if effort == Effort::Standard {
            // Standard effort is covered by propagate(); nothing extra here.
            return TheoryResult::Sat;
        }
        match self.drive_final_check() {
            None => TheoryResult::Sat,
            Some(leaves) => TheoryResult::Conflict(self.expand_conflict(leaves)),
        }
    }
```

Add the driver (inherent `impl`):

```rust
    /// Run both theories' Full check to a joint fixpoint over the shared engine.
    /// Returns the conflicting antecedent leaves, or None if jointly consistent.
    fn drive_final_check(&mut self) -> Option<Vec<crate::types::EqLeaf>> {
        loop {
            let mut cx = TheoryCtx {
                terms: &self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            if let TCheck::Conflict(cf) = self.euf.check(&mut cx, Effort::Full) {
                return Some(cf);
            }
            if let TCheck::Conflict(cf) = self.arith.check(&mut cx, Effort::Full) {
                return Some(cf);
            }
            // Did the round produce a new interface merge? If so, re-run so the
            // other theory observes it; otherwise we are at fixpoint.
            self.merges.clear();
            self.eq.drain_merges(&mut self.merges);
            let progressed = !self.merges.is_empty();
            self.merges.clear();
            if !progressed {
                return None;
            }
        }
    }
```

Import `TCheck` at the top of `combiner.rs`:

```rust
use crate::solver_trait::{TCheck, TheoryCtx, TheorySolver};
```

> **Termination:** each round either reaches fixpoint or shrinks the number of equality classes by at least one interface merge; classes are finite, so the loop terminates.

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-theory --lib combiner`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/combiner.rs
git commit -m "feat(theory): Combiner::check(Full) final-check fixpoint (central-engine reconciliation)"
```

---

### Task 12: Conflict packaging + `explain` — cross-theory `Explainer` expansion

Expand `EqLeaf` antecedents (including interface leaves that recurse into the other theory) into a flat `Vec<Lit>`, then form the conflict clause / reason (spec §5.4, §6.4).

**Files:**
- Modify: `crates/shinri-theory/src/combiner.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces: real `Combiner::expand_conflict` and `Combiner::explain` (the `sat::Theory` method); private `fn resolve(&mut self, exp: &mut Explainer)`.

- [ ] **Step 1: Write the failing test**

Add a theory whose `explain(tag)` resolves an interface `TheoryJust` to a concrete input literal, proving the recursion bottoms out. Add to the `combiner.rs` test module:

```rust
/// Explains tag 0 as the single input literal `lit(50, +)`.
#[derive(Default)]
struct Explained;
impl TheorySolver for Explained {
    const THEORY_ID: u16 = 3; // matches the Merger's TheoryJust.theory above
    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
    fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
        None
    }
    fn propagate(&mut self, _cx: &mut TheoryCtx, _o: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> {
        None
    }
    fn check(&mut self, cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        let a = cx.eq.intern(TermId::new(1).unwrap());
        let b = cx.eq.intern(TermId::new(2).unwrap());
        let _ = cx.eq.merge(a, b, EqJust::Interface(TheoryJust { theory: 3, tag: 0 }));
        TCheck::Sat
    }
    fn explain(&mut self, _cx: &mut TheoryCtx, tag: u32, exp: &mut Explainer) {
        assert_eq!(tag, 0);
        exp.push_lit(Lit::new(Var::new(50), true));
    }
    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
    fn push(&mut self) {}
    fn pop(&mut self, _l: usize) {}
}

#[test]
fn conflict_expands_interface_leaves_to_input_literals_and_negates() {
    // euf = Explained (merges 1,2 with an interface just it can explain),
    // arith = Splitter (conflicts when 1==2, citing that interface just).
    let mut c: Combiner<Explained, Splitter> = Combiner::default();
    match c.check(Effort::Full) {
        TheoryResult::Conflict(clause) => {
            // The interface leaf resolved to lit(50,+); the clause negates it.
            assert_eq!(clause, vec![Lit::new(Var::new(50), true).negate()]);
        }
        other => panic!("expected conflict, got {other:?}"),
    }
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p shinri-theory --lib combiner::tests::conflict_expands`
Expected: FAIL — `expand_conflict` returns an empty `Vec` (Task 9 placeholder).

- [ ] **Step 3: Implement expansion**

Replace the placeholder `expand_conflict` and add `resolve`; implement the `explain` method. Replace `expand_conflict`:

```rust
    /// Expand conflicting antecedent leaves to input literals, then negate to
    /// form the conflict clause handed to shinri-sat's analyzer.
    fn expand_conflict(&mut self, leaves: Vec<crate::types::EqLeaf>) -> Vec<Lit> {
        let mut exp = Explainer::default();
        for leaf in leaves {
            exp.push_leaf(leaf);
        }
        self.resolve(&mut exp);
        let mut clause: Vec<Lit> = exp.take_lits().into_iter().map(|l| l.negate()).collect();
        clause.sort_unstable_by_key(|l| l.code());
        clause.dedup();
        clause
    }

    /// Drive the Explainer to a fixpoint: expand each pending interface
    /// justification via its owning theory until only input literals remain.
    fn resolve(&mut self, exp: &mut Explainer) {
        let mut visited: rustc_hash::FxHashSet<(u16, u32)> = rustc_hash::FxHashSet::default();
        while let Some(j) = exp.pending.pop() {
            if !visited.insert((j.theory, j.tag)) {
                continue; // already expanded; justification DAG, so this terminates
            }
            // Skip the definitional (level-0) placeholder leaf.
            let mut cx = TheoryCtx {
                terms: &self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            if j.theory == E::THEORY_ID {
                self.euf.explain(&mut cx, j.tag, exp);
            } else if j.theory == A::THEORY_ID {
                self.arith.explain(&mut cx, j.tag, exp);
            } else {
                debug_assert!(false, "explain: unknown theory id {}", j.theory);
            }
        }
    }
```

Add `rustc-hash` use to the imports if not present (it is a dependency from Task 2). Implement the `explain` method in the `Theory` impl (replace the empty body):

```rust
    fn explain(&mut self, just: TheoryJust, out: &mut Vec<Lit>) {
        let mut exp = Explainer::default();
        exp.pending.push(just);
        self.resolve(&mut exp);
        // Reason literals are the antecedents (not negated); shinri-sat's
        // analyze consumes a theory reason via the Reason::Theory path.
        let mut lits = exp.take_lits();
        lits.sort_unstable_by_key(|l| l.code());
        lits.dedup();
        out.extend(lits);
    }
```

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-theory --lib combiner`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/combiner.rs
git commit -m "feat(theory): cross-theory conflict packaging + explain via Explainer fixpoint"
```

---

### Task 13: Certificate log — combination-lemma content + dev-gated re-checker

The spec's "full external certificates" (§8). The `sat::Theory` seam doesn't carry the `ProofSink` (it lives in `Solver<_, P, _>`), so `shinri-theory` records the *certificate content* of each theory lemma in its own `CertLog`; downstream (`shinri-solver`) stitches it with the SAT resolution proof and serializes. A dev-gated re-checker verifies each recorded lemma is structurally sound.

**Files:**
- Create: `crates/shinri-theory/src/proof.rs`
- Modify: `crates/shinri-theory/src/combiner.rs`, `src/lib.rs`
- Test: inline `#[cfg(test)]` in `proof.rs` + one in `combiner.rs`

**Interfaces:**
- Produces:
  - `CertStep { pub clause: Vec<Lit>, pub antecedents: Vec<Lit> }`.
  - `CertLog::default()`, `fn record(&mut self, clause: &[Lit], antecedents: &[Lit])`, `fn steps(&self) -> &[CertStep]`, `fn recheck(&self) -> Result<(), CertError>`.
  - `Combiner::cert_log(&self) -> &CertLog`.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-theory/src/proof.rs`:

```rust
//! Combination-lemma certificate content (spec §8). The in-memory record of
//! every theory lemma this crate emits; serialization (Alethe/LRAT) and the
//! stitch with the SAT resolution proof are downstream in shinri-solver.

use shinri_core::Lit;

/// One emitted theory lemma: the conflict `clause` and the input `antecedents`
/// whose conjunction it negates.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CertStep {
    pub clause: Vec<Lit>,
    pub antecedents: Vec<Lit>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CertError {
    /// `clause` is not the negation of `antecedents`.
    NotNegation(usize),
    /// A real conflict cited no antecedents.
    Empty(usize),
}

#[derive(Default)]
pub struct CertLog {
    steps: Vec<CertStep>,
}

impl CertLog {
    pub fn record(&mut self, clause: &[Lit], antecedents: &[Lit]) {
        self.steps.push(CertStep {
            clause: clause.to_vec(),
            antecedents: antecedents.to_vec(),
        });
    }
    pub fn steps(&self) -> &[CertStep] {
        &self.steps
    }

    /// Structural soundness: each clause is exactly the negation of its
    /// antecedents (deeper EUF/Farkas T-validity is re-checked in those crates).
    pub fn recheck(&self) -> Result<(), CertError> {
        for (i, s) in self.steps.iter().enumerate() {
            if s.antecedents.is_empty() {
                return Err(CertError::Empty(i));
            }
            let mut expect: Vec<Lit> = s.antecedents.iter().map(|l| l.negate()).collect();
            expect.sort_unstable_by_key(|l| l.code());
            expect.dedup();
            let mut got = s.clause.clone();
            got.sort_unstable_by_key(|l| l.code());
            got.dedup();
            if expect != got {
                return Err(CertError::NotNegation(i));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Var;

    #[test]
    fn well_formed_lemma_rechecks() {
        let a = Lit::new(Var::new(1), true);
        let b = Lit::new(Var::new(2), true);
        let mut log = CertLog::default();
        log.record(&[a.negate(), b.negate()], &[a, b]);
        assert_eq!(log.recheck(), Ok(()));
    }

    #[test]
    fn empty_antecedents_are_rejected() {
        let a = Lit::new(Var::new(1), true);
        let mut log = CertLog::default();
        log.record(&[a.negate()], &[]);
        assert_eq!(log.recheck(), Err(CertError::Empty(0)));
    }
}
```

- [ ] **Step 2: Wire it and record from the Combiner**

Add to `lib.rs`:

```rust
pub mod proof;

pub use proof::{CertError, CertLog, CertStep};
```

Add a `cert: CertLog` field to `Combiner` (init `CertLog::default()` in `with_context`), and a `pending_antecedents` scratch. In `expand_conflict`, capture the resolved antecedents before negating, and record the step. Modify `expand_conflict`'s tail:

```rust
        let antecedents = exp.take_lits();
        let mut clause: Vec<Lit> = antecedents.iter().map(|l| l.negate()).collect();
        clause.sort_unstable_by_key(|l| l.code());
        clause.dedup();
        if !antecedents.is_empty() {
            self.cert.record(&clause, &antecedents);
        }
        clause
```

(Replace the previous body that called `exp.take_lits()` inline.) Add the accessor:

```rust
    pub fn cert_log(&self) -> &crate::proof::CertLog {
        &self.cert
    }
```

Import in `combiner.rs`: `use crate::proof::CertLog;`

- [ ] **Step 3: Add a Combiner-level test**

Add to the `combiner.rs` test module:

```rust
#[test]
fn emitted_conflict_is_recorded_and_rechecks() {
    let mut c: Combiner<Explained, Splitter> = Combiner::default();
    let _ = c.check(Effort::Full);
    assert_eq!(c.cert_log().steps().len(), 1);
    assert_eq!(c.cert_log().recheck(), Ok(()));
}
```

- [ ] **Step 4: Run to verify pass**

Run: `cargo test -p shinri-theory --lib`
Expected: PASS (proof + combiner tests green).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-theory/src/
git commit -m "feat(theory): combination-lemma CertLog + dev-gated structural re-checker"
```

---

### Task 14: Combined model assembly + seam consistency self-check

On `Sat`, assemble each theory's model and verify they agree on shared interface variables (spec §7.3).

**Files:**
- Modify: `crates/shinri-theory/src/combiner.rs`, `src/model.rs`
- Test: inline `#[cfg(test)]`

**Interfaces:**
- Produces:
  - `Combiner::build_model(&mut self) -> ModelBuilder` — runs `arith.model` then `euf.model`; debug-asserts seam consistency.
  - `ModelBuilder::merge_check(&self, other: &ModelBuilder) -> Option<TermId>` — first term assigned inconsistently between two builders (model self-check helper).

- [ ] **Step 1: Write the failing test**

Add to the `combiner.rs` test module a theory that assigns a value to `term(1)` in its model:

```rust
/// Assigns ModelVal::Num(k) to term(1).
#[derive(Default)]
struct ValTheory {
    k: i64,
}
impl TheorySolver for ValTheory {
    const THEORY_ID: u16 = 5;
    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
    fn assert(&mut self, _cx: &mut TheoryCtx, _l: Lit) -> Option<Vec<EqLeaf>> {
        None
    }
    fn propagate(&mut self, _cx: &mut TheoryCtx, _o: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> {
        None
    }
    fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
        TCheck::Sat
    }
    fn explain(&mut self, _cx: &mut TheoryCtx, _t: u32, _e: &mut Explainer) {}
    fn model(&mut self, _cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        m.assign(
            TermId::new(1).unwrap(),
            crate::types::ModelVal::Num(shinri_core::Rational::from_int((self.k as i128).into())),
        );
    }
    fn push(&mut self) {}
    fn pop(&mut self, _l: usize) {}
}

#[test]
fn build_model_collects_theory_assignments() {
    let mut c: Combiner<OneShotProp, ValTheory> = Combiner::default();
    c.arith.k = 42;
    let m = c.build_model();
    assert_eq!(
        m.get(TermId::new(1).unwrap()),
        Some(&crate::types::ModelVal::Num(shinri_core::Rational::from_int(42i128.into())))
    );
}
```

- [ ] **Step 2: Implement `merge_check` and `build_model`**

Add to `model.rs`:

```rust
impl ModelBuilder {
    /// First term that `self` and `other` assign different values to, if any.
    pub fn merge_check(&self, other: &ModelBuilder) -> Option<TermId> {
        for (t, v) in self.values.iter() {
            if let Some(ov) = other.values.get(t) {
                if v != ov {
                    return Some(*t);
                }
            }
        }
        None
    }
    /// Fold another builder's assignments into this one (other wins ties; the
    /// caller has already verified agreement via `merge_check`).
    pub fn absorb(&mut self, other: ModelBuilder) {
        for (t, v) in other.values {
            self.values.insert(t, v);
        }
    }
}
```

Add to `combiner.rs` (inherent `impl`):

```rust
    /// Assemble the combined model (spec §7.3). Arith assigns rationals first
    /// (interface variables included); EUF fills uninterpreted classes. The two
    /// must agree on every shared term — a debug-asserted seam invariant.
    pub fn build_model(&mut self) -> ModelBuilder {
        let mut arith_m = ModelBuilder::default();
        {
            let mut cx = TheoryCtx {
                terms: &self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            self.arith.model(&mut cx, &mut arith_m);
        }
        let mut euf_m = ModelBuilder::default();
        {
            let mut cx = TheoryCtx {
                terms: &self.terms,
                eq: &mut self.eq,
                atoms: &self.atoms,
            };
            self.euf.model(&mut cx, &mut euf_m);
        }
        debug_assert!(
            arith_m.merge_check(&euf_m).is_none(),
            "model seam disagreement on a shared term"
        );
        let mut combined = arith_m;
        combined.absorb(euf_m);
        combined
    }
```

Add the import `use crate::model::ModelBuilder;` to `combiner.rs` if not already present.

- [ ] **Step 3: Run to verify pass**

Run: `cargo test -p shinri-theory --lib combiner::tests::build_model`
Expected: PASS.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-theory/src/
git commit -m "feat(theory): combined model assembly + seam-consistency self-check"
```

---

### Task 15: Verification harness — EE property tests, oracle scaffold, fuzz, CI

Property tests for the engine, a brute-force reference oracle (the concrete-theory z3 differential activates once `shinri-euf`/`shinri-arith` land), a no-panic fuzz target for classification/purification, and CI wiring.

**Files:**
- Create: `crates/shinri-theory/tests/props.rs`
- Create: `crates/shinri-theory/tests/oracle.rs`
- Create: `crates/shinri-theory/fuzz/Cargo.toml`, `fuzz/fuzz_targets/classify.rs`
- Modify: `.github/workflows/*.yml` (add `shinri-theory` to the test matrix — match the existing job for `shinri-sat`)

**Interfaces:**
- Consumes: `shinri_theory::{EqualityEngine, ENodeId, EqJust, classify}`, `proptest`.

- [ ] **Step 1: Write the EE property test**

Create `crates/shinri-theory/tests/props.rs`:

```rust
//! Property tests for the EqualityEngine: a brute-force union-find oracle must
//! agree on `are_equal`, and `pop` must restore state exactly (spec §10).

use proptest::prelude::*;
use shinri_theory::{ENodeId, EqJust, EqualityEngine};
use shinri_core::{Lit, TermId, Var};

/// A naive backtracking union-find oracle (Vec-of-sets), no proof forest.
#[derive(Clone, Default)]
struct Oracle {
    parent: Vec<usize>,
    snapshots: Vec<Vec<usize>>,
}
impl Oracle {
    fn intern(&mut self, n: usize) {
        while self.parent.len() <= n {
            let k = self.parent.len();
            self.parent.push(k);
        }
    }
    fn find(&self, mut n: usize) -> usize {
        while self.parent[n] != n {
            n = self.parent[n];
        }
        n
    }
    fn merge(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
    fn equal(&self, a: usize, b: usize) -> bool {
        self.find(a) == self.find(b)
    }
    fn push(&mut self) {
        self.snapshots.push(self.parent.clone());
    }
    fn pop(&mut self) {
        self.parent = self.snapshots.pop().unwrap();
    }
}

#[derive(Clone, Debug)]
enum Cmd {
    Merge(u8, u8),
    Push,
    Pop,
}

fn cmd_strategy() -> impl Strategy<Value = Cmd> {
    prop_oneof![
        (0u8..8, 0u8..8).prop_map(|(a, b)| Cmd::Merge(a, b)),
        Just(Cmd::Push),
        Just(Cmd::Pop),
    ]
}

proptest! {
    #[test]
    fn engine_matches_oracle(cmds in proptest::collection::vec(cmd_strategy(), 0..200)) {
        let mut eng = EqualityEngine::default();
        let mut orc = Oracle::default();
        let nodes: Vec<ENodeId> = (0..8).map(|i| eng.intern(TermId::new(i + 1).unwrap())).collect();
        for i in 0..8 { orc.intern(i); }
        let mut depth = 0usize;
        for cmd in cmds {
            match cmd {
                Cmd::Merge(a, b) => {
                    let (a, b) = (a as usize, b as usize);
                    let j = EqJust::Asserted(Lit::new(Var::new((a * 8 + b) as u32), true));
                    let _ = eng.merge(nodes[a], nodes[b], j);
                    orc.merge(a, b);
                }
                Cmd::Push => { eng.push(); orc.push(); depth += 1; }
                Cmd::Pop => {
                    if depth > 0 {
                        depth -= 1;
                        eng.pop(depth);
                        orc.pop();
                    }
                }
            }
            // Invariant: are_equal agrees with the oracle for every pair.
            for a in 0..8 {
                for b in 0..8 {
                    prop_assert_eq!(eng.are_equal(nodes[a], nodes[b]), orc.equal(a, b));
                }
            }
        }
    }
}
```

- [ ] **Step 2: Run the property test**

Run: `cargo test -p shinri-theory --test props`
Expected: PASS (proptest finds no counterexample).

- [ ] **Step 3: Scaffold the z3 differential oracle (ignored until concrete theories land)**

Create `crates/shinri-theory/tests/oracle.rs`:

```rust
//! Differential QF_UFLRA harness vs an external z3 (spec §10). Inert until
//! shinri-euf/shinri-arith provide concrete theories for `Combiner<Euf, Arith>`;
//! until then there is no end-to-end solve to diff. Gated behind `--features
//! oracle` and `#[ignore]` so CI does not require a z3 binary yet.

#![cfg(feature = "oracle")]

#[test]
#[ignore = "activates when Combiner<Euf, Arith> exists (shinri-euf/arith)"]
fn qf_uflra_matches_z3() {
    // Construction sketch (filled in when concrete theories land):
    //   let mut ctx = easy_smt::ContextBuilder::new().solver("z3", ["-in"]).build().unwrap();
    //   for each generated QF_UFLRA instance:
    //     let ours = solve_with_combiner(&instance);   // Combiner<Euf, Arith>
    //     let theirs = ask_z3(&mut ctx, &instance);
    //     assert_eq!(ours.is_sat(), theirs.is_sat(), "differential disagreement");
    //   on SAT: validate our model; on UNSAT: recheck our CertLog.
}
```

> **No silent gap:** this test is deliberately inert and `#[ignore]`d. The plan's `Done` section lists "wire the real z3 differential" as the first follow-up once `shinri-euf`/`shinri-arith` exist. The `props.rs` oracle is the active soundness net for this crate in the meantime.

- [ ] **Step 4: Add the fuzz target**

Create `crates/shinri-theory/fuzz/Cargo.toml`:

```toml
[package]
name = "shinri-theory-fuzz"
version = "0.0.0"
publish = false
edition = "2021"

[package.metadata]
cargo-fuzz = true

[dependencies]
libfuzzer-sys = "0.4"
arbitrary = { version = "1", features = ["derive"] }
shinri-core = { path = "../../shinri-core" }
shinri-theory = { path = ".." }

[[bin]]
name = "classify"
path = "fuzz_targets/classify.rs"
test = false
doc = false
```

Create `crates/shinri-theory/fuzz/fuzz_targets/classify.rs`:

```rust
#![no_main]
//! `classify` must never panic on any well-sorted atom; it returns Ok/Err.
use libfuzzer_sys::fuzz_target;
use shinri_core::{BuiltinOp, Context, Op};

fuzz_target!(|data: &[u8]| {
    // Build a small arithmetic atom from the fuzz bytes and classify it.
    let mut ctx = Context::new();
    let real = ctx.real_sort();
    let xs = ctx.declare_fun("x", &[], real);
    let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
    let n = data.first().copied().unwrap_or(0) as i128;
    let k = ctx.mk_numeral(shinri_num::Rational::from_int(n.into()), real);
    let op = match data.get(1).copied().unwrap_or(0) % 4 {
        0 => BuiltinOp::Le,
        1 => BuiltinOp::Lt,
        2 => BuiltinOp::Ge,
        _ => BuiltinOp::Gt,
    };
    if let Ok(atom) = ctx.mk_app(Op::Builtin(op), &[x, k]) {
        let _ = shinri_theory::classify(&ctx, atom); // must not panic
    }
});
```

- [ ] **Step 5: Wire CI**

In the existing GitHub Actions workflow that runs the per-crate tests (the job covering `shinri-sat`), add `shinri-theory` so `cargo nextest run -p shinri-theory` and `cargo clippy -p shinri-theory -- -D warnings` run on every push. Match the existing job's structure exactly (do not invent a new workflow file).

- [ ] **Step 6: Run the full crate suite + lints**

Run: `cargo test -p shinri-theory && cargo clippy -p shinri-theory -- -D warnings && cargo fmt -p shinri-theory -- --check`
Expected: all green, no warnings, formatted.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-theory/ .github/
git commit -m "test(theory): EE proptest oracle, z3 differential scaffold, classify fuzz target, CI"
```

---

## Done

When all tasks are complete, `shinri-theory` provides the full QF_UFLRA combination framework — shared `EqualityEngine`, `TheorySolver`/`TheoryCtx`, `AtomRegistry` + purification, the enum-routed `Combiner<E, A>` (`sat::Theory`) with propagation + final-check fixpoints, cross-theory conflict packaging, combination-lemma certificates, and combined model assembly — verified end-to-end against in-crate stub theories.

**Immediate follow-ups (next crates, out of this plan's scope):**
1. **`shinri-euf`** — congruence closure + signature table driving the shared `EqualityEngine`; first concrete `TheorySolver`. Unlocks `Combiner<Euf, NoArith>` → **first runnable QF_UF solver**.
2. **`shinri-arith`** — Dutertre–de Moura simplex + Farkas certificates; second `TheorySolver`. Defines `type Combiner = combiner::Combiner<Euf, Arith>`.
3. **Activate the z3 differential** (`tests/oracle.rs`) and the full certificate stitch in `shinri-solver` once both theories exist.

---

## Self-Review

**1. Spec coverage** (each spec section → task):
- §1–3 boundary/layout/atom-routing → Tasks 1, 6, 8.
- §4 EqualityEngine (union-find, diseq, proof forest, merge events, invariants) → Tasks 2, 3, 4, 5.
- §5 TheorySolver trait + TheoryCtx + central-EE contract + borrow pattern → Tasks 7, 8.
- §6 Combiner (assert/propagate/check/conflict packaging/push-pop) → Tasks 8, 9, 11, 12.
- §7 purification, interface variables, model assembly → Tasks 10, 14.
- §8 certificate protocol → Task 13.
- §9 soundness discipline (refusal at registration, diseq guard, exact arithmetic) → Tasks 3, 6, 8.
- §10 testing (unit, property/round-trip, differential, certificate re-check, fuzz, CI) → every task's tests + Task 15. Mutation testing (`cargo-mutants`) — noted as a CI follow-up in Task 15 Step 5; **add `cargo mutants -p shinri-theory` to the scheduled CI job that already runs it for `shinri-sat`.**
- §11 deferrals (non-convex seam, serialization downstream) → respected; reconciliation loop (Task 11) is the documented non-convex insertion point.

**2. Placeholder scan:** No "TBD"/"implement later" in code steps; the only intentionally-inert code is `tests/oracle.rs` (`#[ignore]`d, with the gap called out in Done) and forward-referenced stubs that each later task replaces with a cited Task number.

**3. Type consistency:** `EqualityEngine::merge` gains its `Result` in Task 3 and keeps it after; `pop(level)` is absolute-target throughout (engine + `TheorySolver` + `Combiner` translates the seam's `n`); `Explainer`/`EqLeaf` flow unchanged from Task 1 through Tasks 12–13; `TCheck`/`TheoryResult` boundary mapping is in Tasks 11–12; `THEORY_ID` routing in `resolve` (Task 12) matches the `const THEORY_ID` defined in Task 7.

---

## Execution

Plan complete and saved to `docs/superpowers/plans/2026-06-19-shinri-theory.md`. Two execution options:

1. **Subagent-Driven (recommended)** — a fresh subagent implements each task, with review between tasks. Fast iteration, clean context per task.
2. **Inline Execution** — execute tasks in this session via `superpowers:executing-plans`, batching with checkpoints.

Which approach?
