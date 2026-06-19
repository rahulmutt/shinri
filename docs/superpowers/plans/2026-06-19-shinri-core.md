# shinri-core Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `shinri-core`, the shared-vocabulary crate of the shinri SMT solver: the identity types, the hash-consed term/sort DAG with a well-sortedness-checking builder, the generic `UndoLog<E>` backtracking toolkit, the re-exported `shinri_num::{Rational, DeltaRational}` (with the i128 fast path folded into `shinri_num::Rational` itself — no trait, no wrapper), and the zero-cost `ProofSink` proof seam.

**Architecture:** A single crate, owning one `Context` that holds index-based arenas (`Vec`s) for terms, sorts, child slices, and literal values, with `FxHashMap` interners giving maximal structural sharing and O(1) structural equality. SAT/theory/proof currency types (`Var`/`Lit`/`ClauseId`) are defined here as inert newtypes because core is the lowest common ancestor of every crate that names them. Operators use a central `Op = Builtin(BuiltinOp) | Uninterpreted(SymbolId)` enum. Backtracking is a generic monomorphized typed undo log. Future quantifier/BV/array variants are admitted by architecture (side tables, interned sort algebra, local matches) but not built.

**Tech Stack:** Rust 2021, toolchain `1.96.0`. Runtime deps: `shinri-num` (workspace), `rustc-hash` (`FxHashMap`). Dev-only: `proptest`, `cargo-nextest`, `cargo-deny`.

## Global Constraints

- **Rust edition:** `2021`. Toolchain pinned to `1.96.0` (workspace `rust-version`).
- **Crate license:** `MIT OR Apache-2.0` (permissive — spec §2).
- **Runtime dependencies are curated permissive only.** `shinri-core`'s `[dependencies]` may contain `shinri-num` (path) and `rustc-hash` (MIT/Apache). No native-link crate (already enforced by workspace `deny.toml`). `proptest` is `[dev-dependencies]` only.
- **No floating point anywhere.** Literal values are exact `shinri_num::Rational`. A wrong arithmetic result is a soundness bug (spec §9).
- **Ids are `Copy`, `#[repr(transparent)]`.** `TermId`/`SortId` wrap `NonZeroU32` (so `Option<Id>` is 4 bytes); `SymbolId`/`RatId`/`Var`/`Lit`/`ClauseId` wrap `u32` (spec §3).
- **Soundness discipline (spec §9):** recoverable construction errors return `Result` (`SortError`), never panic; `debug_assert!` guards hot invariants (interner consistency, `UndoLog` level balance; `Rational` canonicalization in `shinri-num`); panics are reserved for genuine invariant violations.
- **Zero-cost proof seam:** `ProofSink` methods take borrowed, already-computed data; `NoProof` is a ZST with `#[inline]` empty bodies (spec §8.1).
- **No `unsafe`** in this plan's scope.
- **`shinri-num` is reworked in Task 8 (not just extended).** This plan folds the i128 fast path into `shinri_num::Rational` (`Small{i128,i128} | Big{Integer,Integer}` behind a private `Repr`), adds `Integer::to_i128`, and changes `Rational::numer()`/`denom()` to return `Integer` **by value**. The change adds no dependency and is re-validated under `shinri-num`'s existing differential + property + fuzz + mutation regime. `shinri-core` then re-exports the one canonical type — no `Rational` trait or `FastRat` wrapper anywhere.

---

### Task 1: Workspace wiring, crate scaffold, identity newtypes

**Files:**
- Modify: `Cargo.toml` (workspace root — add member)
- Create: `crates/shinri-core/Cargo.toml`
- Create: `crates/shinri-core/src/lib.rs`
- Create: `crates/shinri-core/src/ids.rs`
- Test: inline `#[cfg(test)]` module in `ids.rs`

**Interfaces:**
- Consumes: nothing (first task).
- Produces:
  - `shinri_core::ids::{TermId, SortId, SymbolId, RatId, Var, Lit, ClauseId}` — all `Copy + Clone + PartialEq + Eq + Hash + Debug`.
  - `TermId::new(u32) -> Option<TermId>`, `TermId::index(self) -> usize`; same for `SortId`.
  - `SymbolId::new(u32) -> SymbolId`, `SymbolId::index(self) -> usize`; same for `RatId`, `ClauseId`.
  - `Var::new(u32) -> Var`, `Var::index(self) -> usize`.
  - `Lit::new(var: Var, positive: bool) -> Lit`, `Lit::var(self) -> Var`, `Lit::is_positive(self) -> bool`, `Lit::negate(self) -> Lit`.

- [ ] **Step 1: Add the crate to the workspace**

Modify `Cargo.toml` (workspace root) so `members` reads:

```toml
[workspace]
resolver = "2"
members = ["crates/shinri-num", "crates/shinri-core"]

[workspace.package]
edition = "2021"
license = "MIT OR Apache-2.0"
rust-version = "1.96.0"
```

- [ ] **Step 2: Create `crates/shinri-core/Cargo.toml`**

```toml
[package]
name = "shinri-core"
version = "0.1.0"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[dependencies]
shinri-num = { path = "../shinri-num" }
rustc-hash = "2"

[dev-dependencies]
proptest = "1"
```

- [ ] **Step 3: Create `crates/shinri-core/src/lib.rs` module skeleton**

```rust
//! shinri-core: shared vocabulary for the shinri SMT solver.
//!
//! Term/sort DAG, identity types, backtracking toolkit, rational abstraction,
//! and the proof seam. No theory, SAT, or parsing logic lives here.

pub mod ids;

pub use ids::{ClauseId, Lit, RatId, SortId, SymbolId, TermId, Var};
```

- [ ] **Step 4: Write the failing test for the id newtypes**

Create `crates/shinri-core/src/ids.rs` containing only this test module for now:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn option_id_is_four_bytes() {
        assert_eq!(size_of::<Option<TermId>>(), 4);
        assert_eq!(size_of::<Option<SortId>>(), 4);
    }

    #[test]
    fn termid_roundtrips_and_rejects_zero() {
        assert!(TermId::new(0).is_none());
        let id = TermId::new(7).unwrap();
        assert_eq!(id.index(), 6); // 1-based NonZero -> 0-based index
    }

    #[test]
    fn lit_packs_var_and_sign() {
        let v = Var::new(5);
        let pos = Lit::new(v, true);
        let neg = Lit::new(v, false);
        assert_eq!(pos.var(), v);
        assert_eq!(neg.var(), v);
        assert!(pos.is_positive());
        assert!(!neg.is_positive());
        assert_eq!(pos.negate(), neg);
        assert_eq!(neg.negate(), pos);
    }
}
```

- [ ] **Step 5: Run the test to verify it fails**

Run: `cargo test -p shinri-core --lib ids`
Expected: FAIL — compile error (`TermId` etc. not defined).

- [ ] **Step 6: Implement the id newtypes**

Prepend to `crates/shinri-core/src/ids.rs` (above the test module):

```rust
use std::num::NonZeroU32;

/// Index into `Context.nodes`. 1-based (`NonZeroU32`) so `Option<TermId>` is 4 bytes.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TermId(NonZeroU32);

impl TermId {
    #[inline]
    pub fn new(raw: u32) -> Option<TermId> {
        NonZeroU32::new(raw).map(TermId)
    }
    /// 0-based arena index (`raw - 1`).
    #[inline]
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
    /// Construct from a 0-based arena index.
    #[inline]
    pub(crate) fn from_index(idx: usize) -> TermId {
        TermId(NonZeroU32::new(idx as u32 + 1).expect("term index overflow"))
    }
}

/// Index into `Context.sorts`. 1-based like `TermId`.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SortId(NonZeroU32);

impl SortId {
    #[inline]
    pub fn new(raw: u32) -> Option<SortId> {
        NonZeroU32::new(raw).map(SortId)
    }
    #[inline]
    pub fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
    #[inline]
    pub(crate) fn from_index(idx: usize) -> SortId {
        SortId(NonZeroU32::new(idx as u32 + 1).expect("sort index overflow"))
    }
}

macro_rules! u32_id {
    ($name:ident) => {
        #[repr(transparent)]
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
        pub struct $name(u32);
        impl $name {
            #[inline]
            pub fn new(raw: u32) -> $name {
                $name(raw)
            }
            #[inline]
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

u32_id!(SymbolId);
u32_id!(RatId);
u32_id!(ClauseId);
u32_id!(Var);

/// A Boolean literal: a `Var` plus a polarity, packed as `var << 1 | sign`.
/// `sign` bit 0 = positive, 1 = negative.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Lit(u32);

impl Lit {
    #[inline]
    pub fn new(var: Var, positive: bool) -> Lit {
        Lit((var.0 << 1) | (!positive as u32))
    }
    #[inline]
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }
    #[inline]
    pub fn is_positive(self) -> bool {
        (self.0 & 1) == 0
    }
    #[inline]
    pub fn negate(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}
```

- [ ] **Step 7: Run the tests to verify they pass**

Run: `cargo test -p shinri-core --lib ids`
Expected: PASS (3 tests).

- [ ] **Step 8: Commit**

```bash
git add Cargo.toml crates/shinri-core/Cargo.toml crates/shinri-core/src/lib.rs crates/shinri-core/src/ids.rs
git commit -m "feat(core): workspace wiring, crate scaffold, identity newtypes"
```

---

### Task 2: String interner (`SymbolId`)

**Files:**
- Create: `crates/shinri-core/src/symbol.rs`
- Modify: `crates/shinri-core/src/lib.rs` (add `mod symbol;`)
- Test: inline `#[cfg(test)]` module in `symbol.rs`

**Interfaces:**
- Consumes: `SymbolId` (Task 1).
- Produces:
  - `shinri_core::symbol::StringInterner` — `Default`.
  - `StringInterner::intern(&mut self, text: &str) -> SymbolId` (idempotent: equal text → equal id).
  - `StringInterner::resolve(&self, id: SymbolId) -> &str`.

- [ ] **Step 1: Add the module to `lib.rs`**

Add to `crates/shinri-core/src/lib.rs` after `pub mod ids;`:

```rust
pub mod symbol;
```

- [ ] **Step 2: Write the failing test**

Create `crates/shinri-core/src/symbol.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interns_idempotently() {
        let mut si = StringInterner::default();
        let a = si.intern("foo");
        let b = si.intern("bar");
        let a2 = si.intern("foo");
        assert_eq!(a, a2);
        assert_ne!(a, b);
        assert_eq!(si.resolve(a), "foo");
        assert_eq!(si.resolve(b), "bar");
    }
}
```

- [ ] **Step 3: Run the test to verify it fails**

Run: `cargo test -p shinri-core --lib symbol`
Expected: FAIL — `StringInterner` not defined.

- [ ] **Step 4: Implement the interner**

Prepend to `crates/shinri-core/src/symbol.rs`:

```rust
use crate::ids::SymbolId;
use rustc_hash::FxHashMap;

/// Interns symbol text to a `SymbolId` and back. Equal text always yields the
/// same id (maximal sharing); SipHash is never used (uses `FxHashMap`).
#[derive(Default)]
pub struct StringInterner {
    map: FxHashMap<Box<str>, SymbolId>,
    texts: Vec<Box<str>>,
}

impl StringInterner {
    pub fn intern(&mut self, text: &str) -> SymbolId {
        if let Some(&id) = self.map.get(text) {
            return id;
        }
        let id = SymbolId::new(self.texts.len() as u32);
        let boxed: Box<str> = text.into();
        self.texts.push(boxed.clone());
        self.map.insert(boxed, id);
        id
    }

    pub fn resolve(&self, id: SymbolId) -> &str {
        &self.texts[id.index()]
    }
}
```

- [ ] **Step 5: Run the test to verify it passes**

Run: `cargo test -p shinri-core --lib symbol`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-core/src/lib.rs crates/shinri-core/src/symbol.rs
git commit -m "feat(core): string interner for SymbolId"
```

---

### Task 3: Sort representation + sort interner

**Files:**
- Create: `crates/shinri-core/src/sort.rs`
- Create: `crates/shinri-core/src/context.rs`
- Modify: `crates/shinri-core/src/lib.rs`
- Test: inline `#[cfg(test)]` module in `context.rs`

**Interfaces:**
- Consumes: `SortId`, `SymbolId` (Task 1), `StringInterner` (Task 2).
- Produces:
  - `shinri_core::sort::SortNode` — `enum { Bool, Int, Real, Uninterpreted(SymbolId) }` (`Clone + PartialEq + Eq + Hash + Debug`).
  - `shinri_core::context::Context` — `Default`-constructible via `Context::new()`.
  - `Context::bool_sort(&self) -> SortId`, `Context::int_sort(&self) -> SortId`, `Context::real_sort(&self) -> SortId`.
  - `Context::declare_sort(&mut self, name: &str) -> SortId` (interned: same name → same id).
  - `Context::sort_node(&self, id: SortId) -> &SortNode`.

- [ ] **Step 1: Create `sort.rs`**

```rust
use crate::ids::SymbolId;

/// An interned sort. A small algebra; parameterized sorts ((_ BitVec n),
/// (Array I E)) are reserved for Phase 3 and added as variants then (spec §4.3).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SortNode {
    Bool,
    Int,
    Real,
    Uninterpreted(SymbolId),
}
```

- [ ] **Step 2: Add modules to `lib.rs`**

Add to `crates/shinri-core/src/lib.rs`:

```rust
pub mod sort;
pub mod context;

pub use context::Context;
pub use sort::SortNode;
```

- [ ] **Step 3: Write the failing test**

Create `crates/shinri-core/src/context.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::sort::SortNode;

    #[test]
    fn well_known_sorts_distinct_and_stable() {
        let ctx = Context::new();
        assert_ne!(ctx.bool_sort(), ctx.int_sort());
        assert_ne!(ctx.int_sort(), ctx.real_sort());
        assert_eq!(*ctx.sort_node(ctx.bool_sort()), SortNode::Bool);
        assert_eq!(*ctx.sort_node(ctx.int_sort()), SortNode::Int);
        assert_eq!(*ctx.sort_node(ctx.real_sort()), SortNode::Real);
    }

    #[test]
    fn declare_sort_interns() {
        let mut ctx = Context::new();
        let a = ctx.declare_sort("A");
        let b = ctx.declare_sort("B");
        let a2 = ctx.declare_sort("A");
        assert_eq!(a, a2);
        assert_ne!(a, b);
    }
}
```

- [ ] **Step 4: Run the test to verify it fails**

Run: `cargo test -p shinri-core --lib context`
Expected: FAIL — `Context` not defined.

- [ ] **Step 5: Implement `Context` (sort half)**

Prepend to `crates/shinri-core/src/context.rs`:

```rust
use crate::ids::SortId;
use crate::sort::SortNode;
use crate::symbol::StringInterner;
use rustc_hash::FxHashMap;

/// The single owning arena for all interned sorts (and, after Task 4, terms).
pub struct Context {
    sorts: Vec<SortNode>,
    sort_interner: FxHashMap<SortNode, SortId>,
    symbols: StringInterner,
    bool_sort: SortId,
    int_sort: SortId,
    real_sort: SortId,
}

impl Default for Context {
    fn default() -> Self {
        Context::new()
    }
}

impl Context {
    pub fn new() -> Context {
        let mut ctx = Context {
            sorts: Vec::new(),
            sort_interner: FxHashMap::default(),
            symbols: StringInterner::default(),
            // placeholders; overwritten immediately below
            bool_sort: SortId::from_index(0),
            int_sort: SortId::from_index(0),
            real_sort: SortId::from_index(0),
        };
        ctx.bool_sort = ctx.intern_sort(SortNode::Bool);
        ctx.int_sort = ctx.intern_sort(SortNode::Int);
        ctx.real_sort = ctx.intern_sort(SortNode::Real);
        ctx
    }

    fn intern_sort(&mut self, node: SortNode) -> SortId {
        if let Some(&id) = self.sort_interner.get(&node) {
            return id;
        }
        let id = SortId::from_index(self.sorts.len());
        self.sorts.push(node.clone());
        self.sort_interner.insert(node, id);
        id
    }

    #[inline]
    pub fn bool_sort(&self) -> SortId {
        self.bool_sort
    }
    #[inline]
    pub fn int_sort(&self) -> SortId {
        self.int_sort
    }
    #[inline]
    pub fn real_sort(&self) -> SortId {
        self.real_sort
    }

    pub fn declare_sort(&mut self, name: &str) -> SortId {
        let sym = self.symbols.intern(name);
        self.intern_sort(SortNode::Uninterpreted(sym))
    }

    pub fn sort_node(&self, id: SortId) -> &SortNode {
        &self.sorts[id.index()]
    }
}
```

- [ ] **Step 6: Run the test to verify it passes**

Run: `cargo test -p shinri-core --lib context`
Expected: PASS (2 tests).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-core/src/lib.rs crates/shinri-core/src/sort.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): sort representation + interned sort algebra in Context"
```

---

### Task 4: Term representation + structural interning

**Files:**
- Create: `crates/shinri-core/src/term.rs`
- Modify: `crates/shinri-core/src/context.rs` (add term arenas + `mk_const_bool`, `mk_numeral`)
- Modify: `crates/shinri-core/src/lib.rs`
- Test: inline `#[cfg(test)]` module in `context.rs` (extend), plus a proptest in `crates/shinri-core/tests/term_interning.rs`

**Interfaces:**
- Consumes: `Context` (Task 3), `SortId`, `SymbolId`, `RatId`, `TermId` (Task 1).
- Produces:
  - `shinri_core::term::{TermNode, Op, BuiltinOp, ConstVal, ChildSlice}` (all `Clone + Debug`; `Op`/`BuiltinOp`/`ConstVal`/`ChildSlice` are `PartialEq + Eq + Hash`).
  - `Context::mk_const_bool(&mut self, b: bool) -> TermId`.
  - `Context::mk_numeral(&mut self, value: shinri_num::Rational, sort: SortId) -> TermId` (sort assumed `Int`/`Real`; no checking yet — checking arrives in Task 5 via `mk_app`).
  - `Context::term_node(&self, id: TermId) -> &TermNode`.
  - `Context::children(&self, slice: ChildSlice) -> &[TermId]`.
  - Internal: `Context::intern_term(&mut self, node: TermNode) -> TermId`, `Context::push_children(&mut self, args: &[TermId]) -> ChildSlice`.

- [ ] **Step 1: Create `term.rs`**

```rust
use crate::ids::{RatId, SortId, SymbolId, TermId};

/// A (offset, len) view into `Context.children` — out-of-line child storage (SoA).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ChildSlice {
    pub off: u32,
    pub len: u32,
}

/// The operator of an application. Interpreted operators are a compact central
/// enum (fast type-safe dispatch); user functions are `Uninterpreted` (spec §4.2).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Op {
    Builtin(BuiltinOp),
    Uninterpreted(SymbolId),
}

/// Standardized SMT-LIB core + arithmetic operators. Bit-vector / array ops are
/// reserved for Phase 3 and added as variants then (spec §4.3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum BuiltinOp {
    // Boolean / core
    Not,
    And,
    Or,
    Implies,
    Xor,
    Eq,
    Distinct,
    Ite,
    // Arithmetic (Int / Real)
    Neg,
    Add,
    Sub,
    Mul,
    Le,
    Lt,
    Ge,
    Gt,
}

/// A literal constant value. Numerals reference `Context.nums` by `RatId`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ConstVal {
    Bool(bool),
    Num(RatId),
}

/// A node in the hash-consed term DAG. Fixed-size; children stored out-of-line.
/// Var/Quant variants are reserved for Phase 4 and added then (spec §4.3).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TermNode {
    App { op: Op, args: ChildSlice, sort: SortId },
    Const { val: ConstVal, sort: SortId },
}
```

Note: `TermNode` derives `PartialEq + Eq + Hash` over its fields including `ChildSlice` (the (off,len), not the pointed-to children). This is correct for interning *only because* identical child sequences are themselves interned to identical `TermId`s and appended once via a structural key — see Step 4's `intern_term`, which keys on a fully-resolved structural key, not on raw `ChildSlice`.

- [ ] **Step 2: Add the module and exports to `lib.rs`**

Add to `crates/shinri-core/src/lib.rs`:

```rust
pub mod term;

pub use term::{BuiltinOp, ChildSlice, ConstVal, Op, TermNode};
```

- [ ] **Step 3: Write the failing unit tests** (extend the `tests` module in `context.rs`)

Add inside the existing `#[cfg(test)] mod tests` in `context.rs`:

```rust
    use crate::term::{ConstVal, TermNode};
    use shinri_num::Rational;

    #[test]
    fn bool_consts_intern() {
        let mut ctx = Context::new();
        let t = ctx.mk_const_bool(true);
        let t2 = ctx.mk_const_bool(true);
        let f = ctx.mk_const_bool(false);
        assert_eq!(t, t2);
        assert_ne!(t, f);
        match ctx.term_node(t) {
            TermNode::Const { val: ConstVal::Bool(b), sort } => {
                assert!(*b);
                assert_eq!(*sort, ctx.bool_sort());
            }
            _ => panic!("expected bool const"),
        }
    }

    #[test]
    fn numerals_intern_by_value() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let a = ctx.mk_numeral(Rational::from_int(7i128.into()), int);
        let b = ctx.mk_numeral(Rational::from_int(7i128.into()), int);
        let c = ctx.mk_numeral(Rational::from_int(8i128.into()), int);
        assert_eq!(a, b);
        assert_ne!(a, c);
    }
```

- [ ] **Step 4: Run the tests to verify they fail**

Run: `cargo test -p shinri-core --lib context`
Expected: FAIL — `mk_const_bool` / `mk_numeral` not defined.

- [ ] **Step 5: Add term arenas and constructors to `Context`**

In `crates/shinri-core/src/context.rs`, extend the imports and the `Context` struct, and add the term methods.

Update the `use` lines at the top to include:

```rust
use crate::ids::{RatId, SortId, TermId};
use crate::term::{ChildSlice, ConstVal, TermNode};
use shinri_num::Rational;
```

Add these fields to the `Context` struct:

```rust
    nodes: Vec<TermNode>,
    children: Vec<TermId>,
    nums: Vec<Rational>,
    term_interner: FxHashMap<TermKey, TermId>,
```

Initialize them in `Context::new` (add to the struct literal, before the sort placeholders):

```rust
            nodes: Vec::new(),
            children: Vec::new(),
            nums: Vec::new(),
            term_interner: FxHashMap::default(),
```

Add the structural key type and the term methods (after the sort methods, still inside the file but in a fresh `impl Context` block is fine):

```rust
/// A fully-resolved structural key for term interning. Distinct from `TermNode`
/// because `TermNode::App` stores a `ChildSlice` (offset into the arena); two
/// structurally identical apps built at different times would have different
/// slices but must intern to the same id. The key resolves children to their ids.
#[derive(Clone, PartialEq, Eq, Hash)]
enum TermKey {
    App { op: crate::term::Op, args: Vec<TermId>, sort: SortId },
    Const { val: ConstVal, sort: SortId },
}

impl Context {
    fn intern_with_key(&mut self, key: TermKey, node: TermNode) -> TermId {
        if let Some(&id) = self.term_interner.get(&key) {
            return id;
        }
        let id = TermId::from_index(self.nodes.len());
        self.nodes.push(node);
        self.term_interner.insert(key, id);
        id
    }

    pub(crate) fn push_children(&mut self, args: &[TermId]) -> ChildSlice {
        let off = self.children.len() as u32;
        self.children.extend_from_slice(args);
        ChildSlice { off, len: args.len() as u32 }
    }

    pub fn mk_const_bool(&mut self, b: bool) -> TermId {
        let sort = self.bool_sort();
        let val = ConstVal::Bool(b);
        self.intern_with_key(
            TermKey::Const { val, sort },
            TermNode::Const { val, sort },
        )
    }

    pub fn mk_numeral(&mut self, value: Rational, sort: SortId) -> TermId {
        // Intern by numeric value: reuse an existing RatId if the value is present.
        let rat_id = match self.nums.iter().position(|r| *r == value) {
            Some(idx) => RatId::new(idx as u32),
            None => {
                let id = RatId::new(self.nums.len() as u32);
                self.nums.push(value);
                id
            }
        };
        let val = ConstVal::Num(rat_id);
        self.intern_with_key(
            TermKey::Const { val, sort },
            TermNode::Const { val, sort },
        )
    }

    pub fn term_node(&self, id: TermId) -> &TermNode {
        &self.nodes[id.index()]
    }

    pub fn children(&self, slice: ChildSlice) -> &[TermId] {
        let start = slice.off as usize;
        let end = start + slice.len as usize;
        &self.children[start..end]
    }
}
```

Note on `mk_numeral`'s linear scan: Phase-1 numeral counts are small and this keeps the value→id mapping trivially correct. If profiling later shows it matters, replace the `position` scan with an `FxHashMap<Rational, RatId>` side index — a local change behind the same signature.

- [ ] **Step 6: Run the unit tests to verify they pass**

Run: `cargo test -p shinri-core --lib context`
Expected: PASS (4 tests).

- [ ] **Step 7: Write the structural-sharing property test**

Create `crates/shinri-core/tests/term_interning.rs`:

```rust
use shinri_core::Context;

#[test]
fn identical_numerals_share_one_node_and_one_rat() {
    let mut ctx = Context::new();
    let int = ctx.int_sort();
    let v = shinri_num::Rational::from_int(42i128.into());
    let a = ctx.mk_numeral(v.clone(), int);
    let _b = ctx.mk_numeral(v.clone(), int);
    let c = ctx.mk_numeral(v, int);
    // Maximal sharing: rebuilding the same numeral never yields a new id.
    assert_eq!(a, c);
}

#[test]
fn distinct_bools_are_distinct_ids() {
    let mut ctx = Context::new();
    assert_ne!(ctx.mk_const_bool(true), ctx.mk_const_bool(false));
}
```

- [ ] **Step 8: Run the integration test**

Run: `cargo test -p shinri-core --test term_interning`
Expected: PASS (2 tests).

- [ ] **Step 9: Commit**

```bash
git add crates/shinri-core/src/lib.rs crates/shinri-core/src/term.rs crates/shinri-core/src/context.rs crates/shinri-core/tests/term_interning.rs
git commit -m "feat(core): term representation + structural interning (consts/numerals)"
```

---

### Task 5: Term builder + well-sortedness checking

**Files:**
- Create: `crates/shinri-core/src/error.rs`
- Modify: `crates/shinri-core/src/context.rs` (add `declare_fun`, `mk_app`, `mk_eq`, `sort_of`)
- Modify: `crates/shinri-core/src/lib.rs`
- Test: inline `#[cfg(test)]` module in `context.rs` (extend)

**Interfaces:**
- Consumes: `Context` term/sort machinery (Tasks 3-4), `Op`, `BuiltinOp` (Task 4).
- Produces:
  - `shinri_core::error::SortError` (`Clone + PartialEq + Eq + Debug`).
  - `Context::declare_fun(&mut self, name: &str, params: &[SortId], result: SortId) -> SymbolId`.
  - `Context::mk_app(&mut self, op: Op, args: &[TermId]) -> Result<TermId, SortError>`.
  - `Context::mk_eq(&mut self, a: TermId, b: TermId) -> Result<TermId, SortError>`.
  - `Context::sort_of(&self, t: TermId) -> SortId`.

- [ ] **Step 1: Create `error.rs`**

```rust
use crate::ids::SortId;

/// A recoverable well-sortedness error from the term builder. Reported by the
/// parser (spec §9); never panicked.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SortError {
    /// An operator was applied to the wrong number of arguments.
    Arity { expected: usize, found: usize },
    /// An argument had an unexpected sort.
    Mismatch { expected: SortId, found: SortId },
    /// An argument sort was not one this operator accepts (e.g. non-arithmetic
    /// operand to `+`), where no single `expected` sort applies.
    NotApplicable,
    /// An uninterpreted symbol was applied but was never declared.
    UndeclaredSymbol,
}
```

- [ ] **Step 2: Add the module + export to `lib.rs`**

```rust
pub mod error;

pub use error::SortError;
```

- [ ] **Step 3: Write the failing tests** (extend `tests` in `context.rs`)

```rust
    use crate::error::SortError;
    use crate::term::{BuiltinOp, Op};

    #[test]
    fn mk_app_checks_arithmetic_sorts() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let three = ctx.mk_numeral(shinri_num::Rational::from_int(3i128.into()), int);
        // 2 + 3 : Int
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[two, three]).unwrap();
        assert_eq!(ctx.sort_of(sum), int);
        // 2 <= 3 : Bool
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[two, three]).unwrap();
        assert_eq!(ctx.sort_of(le), ctx.bool_sort());
    }

    #[test]
    fn mk_app_rejects_bool_in_arithmetic() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let t = ctx.mk_const_bool(true);
        let err = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[two, t]).unwrap_err();
        assert_eq!(err, SortError::NotApplicable);
    }

    #[test]
    fn mk_eq_requires_matching_sorts() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let t = ctx.mk_const_bool(true);
        assert!(ctx.mk_eq(two, two).is_ok());
        assert!(matches!(ctx.mk_eq(two, t), Err(SortError::Mismatch { .. })));
        assert_eq!(ctx.sort_of(ctx.mk_eq(two, two).unwrap()), ctx.bool_sort());
    }

    #[test]
    fn uninterpreted_application_checks_signature() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let bool_s = ctx.bool_sort();
        // declare-fun p (Int) Bool
        let p = ctx.declare_fun("p", &[int], bool_s);
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let app = ctx.mk_app(Op::Uninterpreted(p), &[two]).unwrap();
        assert_eq!(ctx.sort_of(app), bool_s);
        // wrong arity
        let err = ctx.mk_app(Op::Uninterpreted(p), &[two, two]).unwrap_err();
        assert_eq!(err, SortError::Arity { expected: 1, found: 2 });
    }
```

- [ ] **Step 4: Run the tests to verify they fail**

Run: `cargo test -p shinri-core --lib context`
Expected: FAIL — `declare_fun` / `mk_app` / `mk_eq` / `sort_of` not defined.

- [ ] **Step 5: Add a function-signature table and the builder methods**

In `context.rs`, add to the imports:

```rust
use crate::error::SortError;
use crate::ids::SymbolId;
use crate::term::{BuiltinOp, Op};
```

Add a field to `Context` for declared-function signatures:

```rust
    fun_sigs: FxHashMap<SymbolId, (Vec<SortId>, SortId)>,
```

Initialize it in `Context::new` (add to the struct literal):

```rust
            fun_sigs: FxHashMap::default(),
```

Add the builder methods in an `impl Context` block:

```rust
impl Context {
    pub fn sort_of(&self, t: TermId) -> SortId {
        match self.term_node(t) {
            TermNode::App { sort, .. } => *sort,
            TermNode::Const { sort, .. } => *sort,
        }
    }

    pub fn declare_fun(&mut self, name: &str, params: &[SortId], result: SortId) -> SymbolId {
        let sym = self.symbols.intern(name);
        self.fun_sigs.insert(sym, (params.to_vec(), result));
        sym
    }

    /// Build (and intern) `op` applied to `args`, checking well-sortedness.
    pub fn mk_app(&mut self, op: Op, args: &[TermId]) -> Result<TermId, SortError> {
        let result_sort = self.check_app(op, args)?;
        let slice = self.push_children(args);
        let key = TermKey::App { op, args: args.to_vec(), sort: result_sort };
        Ok(self.intern_with_key(
            key,
            TermNode::App { op, args: slice, sort: result_sort },
        ))
    }

    pub fn mk_eq(&mut self, a: TermId, b: TermId) -> Result<TermId, SortError> {
        self.mk_app(Op::Builtin(BuiltinOp::Eq), &[a, b])
    }

    /// Returns the result sort if the application is well-sorted.
    fn check_app(&self, op: Op, args: &[TermId]) -> Result<SortId, SortError> {
        let bool_s = self.bool_sort();
        match op {
            Op::Uninterpreted(sym) => {
                let (params, result) = self
                    .fun_sigs
                    .get(&sym)
                    .ok_or(SortError::UndeclaredSymbol)?;
                if args.len() != params.len() {
                    return Err(SortError::Arity {
                        expected: params.len(),
                        found: args.len(),
                    });
                }
                for (&arg, &expected) in args.iter().zip(params.iter()) {
                    let found = self.sort_of(arg);
                    if found != expected {
                        return Err(SortError::Mismatch { expected, found });
                    }
                }
                Ok(*result)
            }
            Op::Builtin(b) => self.check_builtin(b, args, bool_s),
        }
    }

    fn check_builtin(
        &self,
        b: BuiltinOp,
        args: &[TermId],
        bool_s: SortId,
    ) -> Result<SortId, SortError> {
        use BuiltinOp::*;
        let int_s = self.int_sort();
        let real_s = self.real_sort();
        let is_arith = |s: SortId| s == int_s || s == real_s;
        match b {
            // Boolean connectives: all args Bool -> Bool.
            Not => {
                expect_arity(args, 1)?;
                expect_all(self, args, bool_s)?;
                Ok(bool_s)
            }
            And | Or | Implies | Xor => {
                if args.len() < 2 {
                    return Err(SortError::Arity { expected: 2, found: args.len() });
                }
                expect_all(self, args, bool_s)?;
                Ok(bool_s)
            }
            Ite => {
                expect_arity(args, 3)?;
                if self.sort_of(args[0]) != bool_s {
                    return Err(SortError::Mismatch {
                        expected: bool_s,
                        found: self.sort_of(args[0]),
                    });
                }
                let then_s = self.sort_of(args[1]);
                let else_s = self.sort_of(args[2]);
                if then_s != else_s {
                    return Err(SortError::Mismatch { expected: then_s, found: else_s });
                }
                Ok(then_s)
            }
            // Equality / distinct: >=2 args of one common sort -> Bool.
            Eq | Distinct => {
                if args.len() < 2 {
                    return Err(SortError::Arity { expected: 2, found: args.len() });
                }
                let first = self.sort_of(args[0]);
                for &a in &args[1..] {
                    let s = self.sort_of(a);
                    if s != first {
                        return Err(SortError::Mismatch { expected: first, found: s });
                    }
                }
                Ok(bool_s)
            }
            // Arithmetic: all args one arithmetic sort.
            Neg => {
                expect_arity(args, 1)?;
                let s = self.sort_of(args[0]);
                if !is_arith(s) {
                    return Err(SortError::NotApplicable);
                }
                Ok(s)
            }
            Add | Sub | Mul => {
                if args.len() < 2 {
                    return Err(SortError::Arity { expected: 2, found: args.len() });
                }
                let s = self.sort_of(args[0]);
                if !is_arith(s) {
                    return Err(SortError::NotApplicable);
                }
                for &a in &args[1..] {
                    if self.sort_of(a) != s {
                        return Err(SortError::NotApplicable);
                    }
                }
                Ok(s)
            }
            Le | Lt | Ge | Gt => {
                expect_arity(args, 2)?;
                let s = self.sort_of(args[0]);
                if !is_arith(s) || self.sort_of(args[1]) != s {
                    return Err(SortError::NotApplicable);
                }
                Ok(bool_s)
            }
        }
    }
}

fn expect_arity(args: &[TermId], n: usize) -> Result<(), SortError> {
    if args.len() == n {
        Ok(())
    } else {
        Err(SortError::Arity { expected: n, found: args.len() })
    }
}

fn expect_all(ctx: &Context, args: &[TermId], expected: SortId) -> Result<(), SortError> {
    for &a in args {
        let found = ctx.sort_of(a);
        if found != expected {
            return Err(SortError::Mismatch { expected, found });
        }
    }
    Ok(())
}
```

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cargo test -p shinri-core --lib context`
Expected: PASS (all context tests).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-core/src/lib.rs crates/shinri-core/src/error.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): well-sortedness-checking term builder (mk_app/mk_eq/declare_fun)"
```

---

### Task 6: `substitute` helper (for `define-fun`)

**Files:**
- Modify: `crates/shinri-core/src/context.rs` (add `substitute`)
- Test: inline `#[cfg(test)]` module in `context.rs` (extend)

**Interfaces:**
- Consumes: the term builder (Task 5).
- Produces:
  - `Context::substitute(&mut self, t: TermId, params: &[TermId], args: &[TermId]) -> TermId` — rebuilds `t`, replacing each occurrence of `params[i]` with `args[i]`, re-interning. `params` and `args` must have equal length and `args[i]` must share `params[i]`'s sort (the caller — the parser — guarantees this from `define-fun`'s checked signature; rebuilt applications are re-checked and a sort-consistent substitution cannot fail, so the result is returned directly).

- [ ] **Step 1: Write the failing test** (extend `tests` in `context.rs`)

```rust
    #[test]
    fn substitute_replaces_leaves_and_reinterns() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        // body: x + 1, with x a placeholder param (an uninterpreted Int constant)
        let xsym = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xsym), &[]).unwrap();
        let one = ctx.mk_numeral(shinri_num::Rational::from_int(1i128.into()), int);
        let body = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, one]).unwrap();
        // substitute x := 5  =>  5 + 1
        let five = ctx.mk_numeral(shinri_num::Rational::from_int(5i128.into()), int);
        let result = ctx.substitute(body, &[x], &[five]);
        let expected = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[five, one]).unwrap();
        assert_eq!(result, expected); // re-interned to the same id
    }

    #[test]
    fn substitute_is_identity_when_no_param_occurs() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let one = ctx.mk_numeral(shinri_num::Rational::from_int(1i128.into()), int);
        let two = ctx.mk_numeral(shinri_num::Rational::from_int(2i128.into()), int);
        let three = ctx.mk_numeral(shinri_num::Rational::from_int(3i128.into()), int);
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[one, two]).unwrap();
        assert_eq!(ctx.substitute(sum, &[three], &[one]), sum);
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p shinri-core --lib context`
Expected: FAIL — `substitute` not defined.

- [ ] **Step 3: Implement `substitute`**

Add to an `impl Context` block in `context.rs`:

```rust
impl Context {
    /// Rebuild `t`, replacing each occurrence of `params[i]` with `args[i]`.
    /// Re-interns the result (maximal sharing preserved).
    pub fn substitute(&mut self, t: TermId, params: &[TermId], args: &[TermId]) -> TermId {
        debug_assert_eq!(params.len(), args.len(), "substitute: param/arg length mismatch");
        // Direct replacement at this node?
        if let Some(pos) = params.iter().position(|&p| p == t) {
            return args[pos];
        }
        match self.term_node(t).clone() {
            TermNode::Const { .. } => t, // constants contain no params
            TermNode::App { op, args: slice, .. } => {
                let child_ids: Vec<TermId> = self.children(slice).to_vec();
                let mut new_children = Vec::with_capacity(child_ids.len());
                let mut changed = false;
                for c in child_ids {
                    let nc = self.substitute(c, params, args);
                    changed |= nc != c;
                    new_children.push(nc);
                }
                if !changed {
                    return t;
                }
                // A sort-consistent substitution cannot make a well-sorted term
                // ill-sorted, so this rebuild always succeeds.
                self.mk_app(op, &new_children)
                    .expect("substitute: sort-consistent rebuild cannot fail")
            }
        }
    }
}
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p shinri-core --lib context`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-core/src/context.rs
git commit -m "feat(core): substitute helper for define-fun beta-reduction"
```

---

### Task 7: `UndoLog<E>` backtracking toolkit

**Files:**
- Create: `crates/shinri-core/src/undo.rs`
- Modify: `crates/shinri-core/src/lib.rs`
- Test: inline `#[cfg(test)]` module in `undo.rs`, plus a proptest in `crates/shinri-core/tests/undo_restore.rs`

**Interfaces:**
- Consumes: nothing (standalone toolkit).
- Produces:
  - `shinri_core::undo::UndoLog<E>` — `Default`.
  - `UndoLog::record(&mut self, e: E)`.
  - `UndoLog::push_level(&mut self)`.
  - `UndoLog::level(&self) -> usize`.
  - `UndoLog::pop_to(&mut self, level: usize, f: impl FnMut(E))` — replays undone entries through `f` in reverse (LIFO) order, leaving exactly `level` levels.

- [ ] **Step 1: Add the module + export to `lib.rs`**

```rust
pub mod undo;

pub use undo::UndoLog;
```

- [ ] **Step 2: Write the failing unit tests**

Create `crates/shinri-core/src/undo.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn levels_and_lifo_replay() {
        let mut log: UndoLog<i32> = UndoLog::default();
        assert_eq!(log.level(), 0);
        log.record(1);
        log.push_level(); // level 1 starts
        assert_eq!(log.level(), 1);
        log.record(2);
        log.record(3);
        log.push_level(); // level 2 starts
        assert_eq!(log.level(), 2);
        log.record(4);

        let mut undone = Vec::new();
        log.pop_to(1, |e| undone.push(e)); // undo level 2's entries only
        assert_eq!(undone, vec![4]);
        assert_eq!(log.level(), 1);

        undone.clear();
        log.pop_to(0, |e| undone.push(e)); // undo level 1's entries, LIFO
        assert_eq!(undone, vec![3, 2]);
        assert_eq!(log.level(), 0);
    }

    #[test]
    fn pop_to_current_level_is_noop() {
        let mut log: UndoLog<i32> = UndoLog::default();
        log.push_level();
        log.record(9);
        let mut count = 0;
        log.pop_to(1, |_| count += 1);
        assert_eq!(count, 0);
        assert_eq!(log.level(), 1);
    }
}
```

- [ ] **Step 3: Run the tests to verify they fail**

Run: `cargo test -p shinri-core --lib undo`
Expected: FAIL — `UndoLog` not defined.

- [ ] **Step 4: Implement `UndoLog<E>`**

Prepend to `crates/shinri-core/src/undo.rs`:

```rust
/// A generic, monomorphized typed undo log. The core backtracking primitive
/// (spec §6): each component instantiates it with its own POD entry type `E`
/// and supplies how to undo one entry via the `pop_to` closure. Flat `Vec`,
/// no dyn dispatch, zero overhead on normal (non-backtrack) component access.
pub struct UndoLog<E> {
    entries: Vec<E>,
    /// `level_starts[i]` = number of entries present when level `i+1` began.
    level_starts: Vec<usize>,
}

impl<E> Default for UndoLog<E> {
    fn default() -> Self {
        UndoLog { entries: Vec::new(), level_starts: Vec::new() }
    }
}

impl<E> UndoLog<E> {
    #[inline]
    pub fn record(&mut self, e: E) {
        self.entries.push(e);
    }

    #[inline]
    pub fn push_level(&mut self) {
        self.level_starts.push(self.entries.len());
    }

    #[inline]
    pub fn level(&self) -> usize {
        self.level_starts.len()
    }

    /// Pop back to `level`, replaying each undone entry through `f` in reverse
    /// (LIFO) order. Panics in debug if `level` exceeds the current level.
    pub fn pop_to(&mut self, level: usize, mut f: impl FnMut(E)) {
        debug_assert!(level <= self.level(), "pop_to: target level above current");
        while self.level_starts.len() > level {
            let start = self.level_starts.pop().unwrap();
            while self.entries.len() > start {
                let e = self.entries.pop().unwrap();
                f(e);
            }
        }
    }
}
```

- [ ] **Step 5: Run the unit tests to verify they pass**

Run: `cargo test -p shinri-core --lib undo`
Expected: PASS (2 tests).

- [ ] **Step 6: Write the restore-identity property test**

Create `crates/shinri-core/tests/undo_restore.rs`:

```rust
use proptest::prelude::*;
use shinri_core::UndoLog;

// Model a backtrackable Vec<u8> whose mutations are recorded as undo entries.
// Property: snapshot -> mutate -> pop_to(snapshot level) -> bit-identical state.
proptest! {
    #[test]
    fn snapshot_mutate_pop_restores_state(
        initial in proptest::collection::vec(any::<u8>(), 0..16),
        ops in proptest::collection::vec(0u8..=2, 0..64),
    ) {
        // Undo entry: restore index `idx` to old value `old`, or pop the last push.
        enum U { Set { idx: usize, old: u8 }, Pop }

        let mut state = initial.clone();
        let mut log: UndoLog<U> = UndoLog::default();

        log.push_level();
        let snapshot = state.clone();

        // counter to vary mutations deterministically without rand
        let mut k: u8 = 0;
        for op in ops {
            k = k.wrapping_add(1);
            match op {
                0 => {
                    // push
                    state.push(k);
                    log.record(U::Pop);
                }
                1 if !state.is_empty() => {
                    // set element 0
                    let idx = 0usize;
                    log.record(U::Set { idx, old: state[idx] });
                    state[idx] = k;
                }
                _ => { /* no-op to keep lengths varied */ }
            }
        }

        log.pop_to(0, |u| match u {
            U::Set { idx, old } => state[idx] = old,
            U::Pop => { state.pop(); }
        });

        prop_assert_eq!(state, snapshot);
    }
}
```

- [ ] **Step 7: Run the property test**

Run: `cargo test -p shinri-core --test undo_restore`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-core/src/lib.rs crates/shinri-core/src/undo.rs crates/shinri-core/tests/undo_restore.rs
git commit -m "feat(core): generic UndoLog<E> backtracking toolkit + restore-identity proptest"
```

---

### Task 8: `shinri-num` — fold the i128 fast path into `Rational`

**Files:**
- Modify: `crates/shinri-num/src/integer.rs` (add `Integer::to_i128`)
- Modify: `crates/shinri-num/src/rational.rs` (rework representation, accessors, and arithmetic)
- Modify: `crates/shinri-num/src/delta.rs` (only if it fails to compile after the accessor change — see Step 9)
- Test: inline `#[cfg(test)]` in `integer.rs` and `rational.rs`; new `crates/shinri-num/tests/rational_differential.rs`

**Interfaces:**
- Consumes: the existing `Integer` representation (`Repr::Small(i128) | Repr::Big { .. }`).
- Produces:
  - `shinri_num::Integer::to_i128(&self) -> Option<i128>` — `Some(v)` iff stored inline, else `None`.
  - Reworked `shinri_num::Rational`: `pub struct Rational(Repr)` wrapping a **private** `enum Repr { Small { n: i128, d: i128 }, Big { numer: Integer, denom: Integer } }`. Canonical invariant: a value is `Small` **iff** both reduced components fit `i128`; denominators are positive; fractions are reduced; zero is `Small { n: 0, d: 1 }`.
  - **API change:** `Rational::numer(&self) -> Integer` and `Rational::denom(&self) -> Integer` now return **by value** (previously `&Integer`).
  - Unchanged public surface: `new(Integer, Integer)`, `from_int(Integer)`, `zero()`, `one()`, `is_zero`, `is_negative`, `signum`, `recip`, `Add`/`Sub`/`Mul`/`Div`/`Neg`, `PartialEq`/`Eq`/`PartialOrd`/`Ord`.

This is a refactor of already-tested code. The discipline: **keep `shinri-num`'s existing tests green while adding new ones**. The `pub struct(Repr)` shape (mirroring `Integer`) keeps the variants private so external code cannot build a non-canonical `Rational`.

- [ ] **Step 1: Write the failing `Integer::to_i128` tests** (add to the `#[cfg(test)] mod tests` in `integer.rs`)

```rust
    #[test]
    fn to_i128_some_for_inline_values() {
        for v in [0i128, 1, -1, 42, -42, i128::MAX, i128::MIN] {
            assert_eq!(Integer::from(v).to_i128(), Some(v));
        }
    }

    #[test]
    fn to_i128_none_for_big_values() {
        let big = Integer::from(i128::MAX) * Integer::from(2i128);
        assert_eq!(big.to_i128(), None);
        let big_neg = Integer::from(i128::MIN) * Integer::from(2i128);
        assert_eq!(big_neg.to_i128(), None);
    }
```

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p shinri-num --lib to_i128`
Expected: FAIL — `to_i128` not found.

- [ ] **Step 3: Implement `Integer::to_i128`** (new `impl Integer` block in `integer.rs`)

```rust
impl Integer {
    /// The value as `i128` if it fits inline, else `None`. By the canonical
    /// invariant (any i128-representable value is `Small`), `None` means the
    /// magnitude genuinely exceeds `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        match &self.0 {
            Repr::Small(v) => Some(*v),
            Repr::Big { .. } => None,
        }
    }
}
```

- [ ] **Step 4: Run to verify they pass**

Run: `cargo test -p shinri-num --lib to_i128`
Expected: PASS (2 tests).

- [ ] **Step 5: Rewrite `rational.rs` — representation, helpers, constructors, accessors**

Replace the non-test code in `crates/shinri-num/src/rational.rs` with the following (keep the existing `#[cfg(test)] mod tests`; it is updated in Step 7). Adjust the `use` line to whatever the file already imports for `Integer` plus the ops below.

```rust
use crate::integer::Integer;
use core::cmp::Ordering;
use core::ops::{Add, Div, Mul, Neg, Sub};

/// Exact rational with an unboxed i128 fast path (spec §7). `pub struct(Repr)`
/// with a private `Repr` keeps the variants encapsulated, mirroring `Integer`,
/// so external code cannot construct a non-canonical value.
#[derive(Clone, Debug)]
pub struct Rational(Repr);

#[derive(Clone, Debug)]
enum Repr {
    /// Canonical: `d > 0`, `gcd(|n|, d) == 1`, zero is `{ n: 0, d: 1 }`.
    Small { n: i128, d: i128 },
    /// Canonical and genuinely exceeds the i128 pair (`denom > 0`, reduced).
    Big { numer: Integer, denom: Integer },
}

fn igcd(a: i128, b: i128) -> i128 {
    let mut a = a.unsigned_abs();
    let mut b = b.unsigned_abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    // Safe: the only case where the gcd magnitude reaches 2^127 is gcd(MIN, MIN),
    // which `small_canon` pre-empts via the `d < 0` checked_neg path.
    a as i128
}

impl Rational {
    /// Canonicalize a raw i128 pair into `Small`, or `None` if it cannot stay in
    /// i128 (only the `i128::MIN` denominator-negation case). `d` must be non-zero.
    fn small_canon(mut n: i128, mut d: i128) -> Option<Rational> {
        debug_assert!(d != 0);
        if n == 0 {
            return Some(Rational(Repr::Small { n: 0, d: 1 }));
        }
        if d < 0 {
            n = n.checked_neg()?;
            d = d.checked_neg()?;
        }
        let g = igcd(n, d);
        Some(Rational(Repr::Small { n: n / g, d: d / g }))
    }

    /// Build from `Integer` components: sign-fix, reduce, then DEMOTE to `Small`
    /// when both components fit i128 (keeping the hot path unboxed after a
    /// temporary excursion to bignum), else keep `Big`. `denom` must be non-zero.
    fn from_components(numer: Integer, denom: Integer) -> Rational {
        debug_assert!(!denom.is_zero(), "Rational with zero denominator");
        let (mut numer, mut denom) = if denom.is_negative() {
            (-numer, -denom)
        } else {
            (numer, denom)
        };
        let g = numer.gcd(&denom);
        if !g.is_zero() && g != Integer::one() {
            let (qn, _) = numer.div_rem(&g);
            let (qd, _) = denom.div_rem(&g);
            numer = qn;
            denom = qd;
        }
        match (numer.to_i128(), denom.to_i128()) {
            (Some(n), Some(d)) => Rational(Repr::Small { n, d }),
            _ => Rational(Repr::Big { numer, denom }),
        }
    }

    pub fn new(numer: Integer, denom: Integer) -> Rational {
        assert!(!denom.is_zero(), "Rational denominator must be non-zero");
        if let (Some(n), Some(d)) = (numer.to_i128(), denom.to_i128()) {
            if let Some(r) = Rational::small_canon(n, d) {
                return r;
            }
        }
        Rational::from_components(numer, denom)
    }

    pub fn from_int(n: Integer) -> Rational {
        Rational::new(n, Integer::one())
    }

    pub fn zero() -> Rational {
        Rational(Repr::Small { n: 0, d: 1 })
    }

    pub fn one() -> Rational {
        Rational(Repr::Small { n: 1, d: 1 })
    }

    /// The numerator, by value (the `Small` variant has no `Integer` to borrow).
    pub fn numer(&self) -> Integer {
        match &self.0 {
            Repr::Small { n, .. } => Integer::from(*n),
            Repr::Big { numer, .. } => numer.clone(),
        }
    }

    /// The denominator, by value.
    pub fn denom(&self) -> Integer {
        match &self.0 {
            Repr::Small { d, .. } => Integer::from(*d),
            Repr::Big { denom, .. } => denom.clone(),
        }
    }

    pub fn is_zero(&self) -> bool {
        match &self.0 {
            Repr::Small { n, .. } => *n == 0,
            Repr::Big { numer, .. } => numer.is_zero(),
        }
    }

    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small { n, .. } => *n < 0,
            Repr::Big { numer, .. } => numer.is_negative(),
        }
    }

    pub fn signum(&self) -> i32 {
        match &self.0 {
            Repr::Small { n, .. } => (*n > 0) as i32 - (*n < 0) as i32,
            Repr::Big { numer, .. } => numer.signum(),
        }
    }

    pub fn recip(&self) -> Rational {
        debug_assert!(!self.is_zero(), "recip of zero");
        match &self.0 {
            Repr::Small { n, d } => Rational::small_canon(*d, *n).unwrap_or_else(|| {
                Rational::from_components(Integer::from(*d), Integer::from(*n))
            }),
            Repr::Big { numer, denom } => {
                Rational::from_components(denom.clone(), numer.clone())
            }
        }
    }

    /// (numerator, denominator) as `Integer`s — used by the bignum fallback paths.
    fn components(&self) -> (Integer, Integer) {
        (self.numer(), self.denom())
    }
}
```

- [ ] **Step 6: Add the arithmetic, equality, and ordering impls** (append to `rational.rs`, after the `impl Rational` block)

```rust
macro_rules! rat_binop {
    ($trait:ident, $method:ident, $small:expr, $big:expr) => {
        impl $trait for Rational {
            type Output = Rational;
            fn $method(self, rhs: Rational) -> Rational {
                if let (Repr::Small { n: an, d: ad }, Repr::Small { n: bn, d: bd }) =
                    (&self.0, &rhs.0)
                {
                    if let Some(res) = ($small)(*an, *ad, *bn, *bd) {
                        return res;
                    }
                }
                let (an, ad) = self.components();
                let (bn, bd) = rhs.components();
                let (num, den) = ($big)(an, ad, bn, bd);
                Rational::from_components(num, den)
            }
        }
    };
}

rat_binop!(
    Add,
    add,
    |an: i128, ad: i128, bn: i128, bd: i128| -> Option<Rational> {
        let ae = an.checked_mul(bd)?;
        let bdp = bn.checked_mul(ad)?;
        let num = ae.checked_add(bdp)?;
        let den = ad.checked_mul(bd)?;
        Rational::small_canon(num, den)
    },
    |an: Integer, ad: Integer, bn: Integer, bd: Integer| {
        (an * bd.clone() + bn * ad.clone(), ad * bd)
    }
);

rat_binop!(
    Sub,
    sub,
    |an: i128, ad: i128, bn: i128, bd: i128| -> Option<Rational> {
        let ae = an.checked_mul(bd)?;
        let bdp = bn.checked_mul(ad)?;
        let num = ae.checked_sub(bdp)?;
        let den = ad.checked_mul(bd)?;
        Rational::small_canon(num, den)
    },
    |an: Integer, ad: Integer, bn: Integer, bd: Integer| {
        (an * bd.clone() - bn * ad.clone(), ad * bd)
    }
);

rat_binop!(
    Mul,
    mul,
    |an: i128, ad: i128, bn: i128, bd: i128| -> Option<Rational> {
        let num = an.checked_mul(bn)?;
        let den = ad.checked_mul(bd)?;
        Rational::small_canon(num, den)
    },
    |an: Integer, ad: Integer, bn: Integer, bd: Integer| { (an * bn, ad * bd) }
);

rat_binop!(
    Div,
    div,
    |an: i128, ad: i128, bn: i128, bd: i128| -> Option<Rational> {
        debug_assert!(bn != 0, "division by zero rational");
        let num = an.checked_mul(bd)?;
        let den = ad.checked_mul(bn)?;
        if den == 0 {
            return None;
        }
        Rational::small_canon(num, den)
    },
    |an: Integer, ad: Integer, bn: Integer, bd: Integer| {
        debug_assert!(!bn.is_zero(), "division by zero rational");
        (an * bd, ad * bn)
    }
);

impl Neg for Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        match self.0 {
            Repr::Small { n, d } => match n.checked_neg() {
                Some(nn) => Rational(Repr::Small { n: nn, d }),
                None => Rational::from_components(-Integer::from(n), Integer::from(d)),
            },
            Repr::Big { numer, denom } => Rational::from_components(-numer, denom),
        }
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Rational) -> bool {
        match (&self.0, &other.0) {
            (Repr::Small { n: an, d: ad }, Repr::Small { n: bn, d: bd }) => an == bn && ad == bd,
            (
                Repr::Big { numer: an, denom: ad },
                Repr::Big { numer: bn, denom: bd },
            ) => an == bn && ad == bd,
            // Canonical: a value is Small iff it fits, so Small and Big are never equal.
            _ => false,
        }
    }
}

impl Eq for Rational {}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        if let (Repr::Small { n: an, d: ad }, Repr::Small { n: bn, d: bd }) =
            (&self.0, &other.0)
        {
            if let (Some(l), Some(r)) = (an.checked_mul(*bd), bn.checked_mul(*ad)) {
                return l.cmp(&r);
            }
        }
        // Cross-multiply over Integer (denominators are positive, so sign is preserved).
        let (an, ad) = self.components();
        let (bn, bd) = other.components();
        (an * bd).cmp(&(bn * ad))
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
```

- [ ] **Step 7: Update the existing inline tests and add new ones** (`#[cfg(test)] mod tests` in `rational.rs`)

Two mechanical fixes to existing tests, then new coverage:

1. Anywhere an existing test dereferenced an accessor (e.g. `*neg.denom()` / `*x.numer()`), drop the `*` — they now return `Integer` by value (e.g. `assert_eq!(neg.denom(), Integer::from(2i128))`).
2. Keep the existing zero-denominator `#[should_panic]` test (still panics via the `assert!` in `new`).

Add these tests:

```rust
    #[test]
    fn small_tag_and_reduction() {
        // 2/4 reduces to 1/2 and stays Small
        let r = Rational::new(Integer::from(2i128), Integer::from(4i128));
        assert!(matches!(r, Rational(Repr::Small { n: 1, d: 2 })));
        // negative denominator normalizes onto the numerator
        let r2 = Rational::new(Integer::from(1i128), Integer::from(-2i128));
        assert!(matches!(r2, Rational(Repr::Small { n: -1, d: 2 })));
    }

    #[test]
    fn overflow_promotes_to_big() {
        let r = Rational::from_int(Integer::from(i128::MAX) * Integer::from(2i128));
        assert!(matches!(r, Rational(Repr::Big { .. })));
    }

    #[test]
    fn demotes_back_to_small_when_it_fits() {
        // Big value 2*i128::MAX, divided by 2 -> i128::MAX, which fits -> Small
        let big = Rational::from_int(Integer::from(i128::MAX) * Integer::from(2i128));
        assert!(matches!(big, Rational(Repr::Big { .. })));
        let halved = big / Rational::from_int(Integer::from(2i128));
        assert!(matches!(halved, Rational(Repr::Small { .. })));
        assert_eq!(halved, Rational::from_int(Integer::from(i128::MAX)));
    }

    #[test]
    fn fast_path_arithmetic_and_ordering() {
        let half = Rational::new(Integer::from(1i128), Integer::from(2i128));
        let third = Rational::new(Integer::from(1i128), Integer::from(3i128));
        assert_eq!(
            half.clone() + third.clone(),
            Rational::new(Integer::from(5i128), Integer::from(6i128))
        );
        assert!((half.clone() - half.clone()).is_zero());
        assert_eq!(
            half.clone() * third.clone(),
            Rational::new(Integer::from(1i128), Integer::from(6i128))
        );
        assert_eq!(
            half.clone() / third.clone(),
            Rational::new(Integer::from(3i128), Integer::from(2i128))
        );
        assert!(third < half);
        assert_eq!(half.recip(), Rational::from_int(Integer::from(2i128)));
    }
```

- [ ] **Step 8: Run the inline tests**

Run: `cargo test -p shinri-num --lib rational`
Expected: PASS (existing + new).

- [ ] **Step 9: Fix any fallout in `delta.rs` and re-build the crate**

Run: `cargo build -p shinri-num`
If it fails, the only possible cause is a call site that used `numer()`/`denom()` as `&Integer` (e.g. in `delta.rs` or its tests). Fix mechanically by removing the `&`/`*` (the value is now owned). Re-run until clean.
Expected: builds clean.

- [ ] **Step 10: Add the differential test vs the `num-rational` oracle**

Create `crates/shinri-num/tests/rational_differential.rs`:

```rust
use num_bigint::BigInt;
use num_rational::BigRational;
use proptest::prelude::*;
use shinri_num::{Integer, Rational};

fn shinri(n: i128, d: i128) -> Rational {
    Rational::new(Integer::from(n), Integer::from(d))
}

fn oracle(n: i128, d: i128) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

// Both types canonicalize (reduced, positive denominator), so equal values have
// equal numerator/denominator decimal strings.
fn agree(s: &Rational, o: &BigRational) -> bool {
    s.numer().to_string() == o.numer().to_string()
        && s.denom().to_string() == o.denom().to_string()
}

proptest! {
    // The folded Rational must match the oracle on every op, including when
    // operands overflow i128 and spill to Big (and demote back). Spec §7 / §10.
    #[test]
    fn rational_matches_oracle(
        an in -1_000_000i128..1_000_000,
        ad in 1i128..1_000_000,
        bn in -1_000_000i128..1_000_000,
        bd in 1i128..1_000_000,
        scale in prop::sample::select(vec![1i128, 1_000_000_000_000_000_000]),
    ) {
        let (an, ad) = (an.saturating_mul(scale), ad);
        let (bn, bd) = (bn, bd.saturating_mul(scale));

        let (sa, sb) = (shinri(an, ad), shinri(bn, bd));
        let (oa, ob) = (oracle(an, ad), oracle(bn, bd));

        prop_assert!(agree(&(sa.clone() + sb.clone()), &(oa.clone() + ob.clone())));
        prop_assert!(agree(&(sa.clone() - sb.clone()), &(oa.clone() - ob.clone())));
        prop_assert!(agree(&(sa.clone() * sb.clone()), &(oa.clone() * ob.clone())));
        if bn != 0 {
            prop_assert!(agree(&(sa.clone() / sb.clone()), &(oa.clone() / ob.clone())));
        }
        prop_assert_eq!(sa.cmp(&sb), oa.cmp(&ob));
    }
}
```

- [ ] **Step 11: Run the full `shinri-num` regime**

Run:
```bash
cargo test -p shinri-num
cargo clippy -p shinri-num --all-targets -- -D warnings
cargo fmt --check
```
Expected: all green (existing differential/property tests plus the new rational differential test).

- [ ] **Step 12: Commit**

```bash
git add crates/shinri-num/
git commit -m "feat(num): fold i128 fast path into Rational (Small|Big), to_i128, by-value numer/denom"
```

---

### Task 9: `shinri-core` — re-export the rational types

**Files:**
- Modify: `crates/shinri-core/src/lib.rs`
- Test: `crates/shinri-core/tests/rational_reexport.rs`

**Interfaces:**
- Consumes: `shinri_num::{Rational, DeltaRational}` (Task 8).
- Produces: `shinri_core::{Rational, DeltaRational}` re-exports — the solver-wide rational vocabulary. No core-defined trait, wrapper, or `rational` module.

- [ ] **Step 1: Add the re-exports to `lib.rs`**

Add to `crates/shinri-core/src/lib.rs` (alongside the other `pub use` lines; core does **not** define its own rational module):

```rust
pub use shinri_num::{DeltaRational, Rational};
```

- [ ] **Step 2: Write the smoke test**

Create `crates/shinri-core/tests/rational_reexport.rs`:

```rust
use shinri_core::Rational;
use shinri_num::Integer;

#[test]
fn core_reexports_rational_with_fast_path() {
    let half = Rational::new(Integer::from(1i128), Integer::from(2i128));
    let third = Rational::new(Integer::from(1i128), Integer::from(3i128));
    assert_eq!(
        half + third,
        Rational::new(Integer::from(5i128), Integer::from(6i128))
    );
}
```

- [ ] **Step 3: Run the test**

Run: `cargo test -p shinri-core --test rational_reexport`
Expected: PASS.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-core/src/lib.rs crates/shinri-core/tests/rational_reexport.rs
git commit -m "feat(core): re-export shinri_num::{Rational, DeltaRational} (folded fast path)"
```

(`DeltaRational`'s delta-ordering is tested in `shinri-num`'s `delta.rs`; core only re-exports it.)

---

### Task 10: `ProofSink` trait + `NoProof` + `TheoryJust`

**Files:**
- Create: `crates/shinri-core/src/proof.rs`
- Modify: `crates/shinri-core/src/lib.rs`
- Test: inline `#[cfg(test)]` module in `proof.rs`

**Interfaces:**
- Consumes: `ClauseId`, `Lit` (Task 1).
- Produces:
  - `shinri_core::proof::TheoryJust` — opaque justification token a theory attaches to a lemma. Phase-1 shape: `struct TheoryJust { theory: u16, tag: u32 }` (captured, not interpreted until Phase 2).
  - `shinri_core::proof::ProofSink` — trait with `input`, `learn`, `theory_lemma`, `delete` (all taking borrowed slices).
  - `shinri_core::proof::NoProof` — ZST `ProofSink` whose every method is an `#[inline]` empty body.

- [ ] **Step 1: Add the module + exports to `lib.rs`**

```rust
pub mod proof;

pub use proof::{NoProof, ProofSink, TheoryJust};
```

- [ ] **Step 2: Write the failing test**

Create `crates/shinri-core/src/proof.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::ids::{ClauseId, Lit, Var};

    // A recording sink proves the trait is object-usable and captures the chain.
    #[derive(Default)]
    struct Recorder {
        learns: Vec<(ClauseId, Vec<Lit>, Vec<ClauseId>)>,
        deletes: Vec<ClauseId>,
    }
    impl ProofSink for Recorder {
        fn input(&mut self, _c: ClauseId, _lits: &[Lit]) {}
        fn learn(&mut self, c: ClauseId, lits: &[Lit], chain: &[ClauseId]) {
            self.learns.push((c, lits.to_vec(), chain.to_vec()));
        }
        fn theory_lemma(&mut self, _c: ClauseId, _lits: &[Lit], _just: TheoryJust) {}
        fn delete(&mut self, c: ClauseId) {
            self.deletes.push(c);
        }
    }

    #[test]
    fn recorder_captures_learn_chain() {
        let mut r = Recorder::default();
        let c = ClauseId::new(3);
        let lits = [Lit::new(Var::new(0), true), Lit::new(Var::new(1), false)];
        let chain = [ClauseId::new(1), ClauseId::new(2)];
        r.learn(c, &lits, &chain);
        r.delete(c);
        assert_eq!(r.learns.len(), 1);
        assert_eq!(r.learns[0].2, vec![ClauseId::new(1), ClauseId::new(2)]);
        assert_eq!(r.deletes, vec![c]);
    }

    #[test]
    fn noproof_is_zero_sized() {
        assert_eq!(std::mem::size_of::<NoProof>(), 0);
        // Exercise the no-op methods (they must compile and do nothing).
        let mut p = NoProof;
        p.input(ClauseId::new(0), &[]);
        p.learn(ClauseId::new(0), &[], &[]);
        p.delete(ClauseId::new(0));
    }
}
```

- [ ] **Step 3: Run the tests to verify they fail**

Run: `cargo test -p shinri-core --lib proof`
Expected: FAIL — `ProofSink` / `NoProof` / `TheoryJust` not defined.

- [ ] **Step 4: Implement the proof seam**

Prepend to `crates/shinri-core/src/proof.rs`:

```rust
use crate::ids::{ClauseId, Lit};

/// An opaque justification a theory attaches to a lemma. Captured in Phase 1,
/// interpreted (EUF proof-forest / LRA Farkas) when proof emission lands in
/// Phase 2 (spec §8.1). `theory` identifies the producing theory; `tag` is a
/// theory-private handle into its own explanation state.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TheoryJust {
    pub theory: u16,
    pub tag: u32,
}

/// The proof-production seam (spec §8). Threaded through clause add/learn/delete
/// from day one. Methods take borrowed, already-computed data so that with the
/// `NoProof` impl every call dead-code-eliminates (zero cost when off).
/// Emission (Alethe / LRAT) is a Phase-2 consumer of what this captures.
pub trait ProofSink {
    /// An input (asserted) clause entered the database.
    fn input(&mut self, c: ClauseId, lits: &[Lit]);
    /// A learned clause, with its resolution/derivation chain (the LRAT hint),
    /// harvested from 1-UIP conflict analysis's existing antecedent walk.
    fn learn(&mut self, c: ClauseId, lits: &[Lit], chain: &[ClauseId]);
    /// A theory lemma, tagged with its theory justification.
    fn theory_lemma(&mut self, c: ClauseId, lits: &[Lit], just: TheoryJust);
    /// A clause was deleted from the database.
    fn delete(&mut self, c: ClauseId);
}

/// The default, zero-cost sink: a ZST whose methods inline to nothing.
pub struct NoProof;

impl ProofSink for NoProof {
    #[inline(always)]
    fn input(&mut self, _c: ClauseId, _lits: &[Lit]) {}
    #[inline(always)]
    fn learn(&mut self, _c: ClauseId, _lits: &[Lit], _chain: &[ClauseId]) {}
    #[inline(always)]
    fn theory_lemma(&mut self, _c: ClauseId, _lits: &[Lit], _just: TheoryJust) {}
    #[inline(always)]
    fn delete(&mut self, _c: ClauseId) {}
}
```

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo test -p shinri-core --lib proof`
Expected: PASS (2 tests).

- [ ] **Step 6: Run the full crate test suite + lints**

Run:
```bash
cargo test -p shinri-core
cargo clippy -p shinri-core --all-targets -- -D warnings
cargo fmt --check
```
Expected: all green. (If `fmt --check` reports diffs, run `cargo fmt` and re-stage.)

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-core/src/lib.rs crates/shinri-core/src/proof.rs
git commit -m "feat(core): ProofSink trait + NoProof zero-cost seam + TheoryJust token"
```

---

## Self-Review

**Spec coverage** (each spec section → task):
- §1 purpose / responsibilities → the crate as a whole; non-responsibilities respected (no theory/SAT/parser code).
- §2 dependency policy → Task 1 `Cargo.toml` (`shinri-num` + `rustc-hash`; `proptest` dev-only).
- §3 identity types → Task 1 (all newtypes, `NonZeroU32` for Term/Sort, `Lit` packing). §3.1 currency-in-core → `Var`/`Lit`/`ClauseId` defined in `ids.rs`.
- §4 term/sort representation → Task 3 (sorts), Task 4 (terms, `Op`/`BuiltinOp`/`ConstVal`, interning). §4.1 properties (O(1) eq, sharing, SoA children) → Task 4. §4.2 operator split → Task 4 `Op`. §4.3 reserved-not-built → comments in `sort.rs`/`term.rs`; no Var/Quant/BV/Array variants present.
- §5 builder + well-sortedness → Task 5. §5.1 `define-fun`/`substitute` → Task 6.
- §6 `UndoLog<E>` → Task 7. §6.1 decision properties (flat POD, monomorphized, no dyn) → implementation + restore-identity proptest.
- §7 arithmetic (folded fast path) → Task 8 (the i128 fast path folded into `shinri_num::Rational` as `Small{i128,i128} | Big{Integer,Integer}` behind a private `Repr`, with `Integer::to_i128`, by-value `numer()`/`denom()`, overflow→Big and demote-on-fit, differential-tested vs `num-rational`). Core re-export → Task 9. The Q1/§4.3 `Rational` trait + `FastRat` wrapper is intentionally **not** built.
- §8 `ProofSink` + `NoProof`, resolution-chain granularity, borrow-don't-build → Task 10. §8.1 `TheoryJust` → Task 10.
- §9 error handling → `SortError` (Task 5), `debug_assert!` in `UndoLog`/`substitute` (core) and `Rational` canonicalization (Task 8, `shinri-num`).
- §10 testing → property tests (interning Task 4, restore-identity Task 7); `Rational` differential vs oracle + overflow/demotion unit tests (Task 8, `shinri-num`); codegen/ZST check (Task 10 `noproof_is_zero_sized`); CI gates (Task 8 Step 11 and Task 10 Step 6).
- §11 deliverable → all tasks; one-way doors designed in (reserved variants, side-table-ready, proof seam) and the rational fast path centralized in `shinri-num`.

**Placeholder scan:** No TBD/TODO/"handle edge cases"/"similar to". Every code step shows complete code.

**Type consistency:** `TermId`/`SortId` use `from_index`/`index`; `Op`/`BuiltinOp`/`ConstVal`/`ChildSlice` names are stable across Tasks 4-6; `mk_app`/`mk_eq`/`sort_of`/`declare_fun`/`substitute` signatures match between their producing task and later use; `Rational`'s reworked surface (`new`/`from_int`/`zero`/`one`/`numer`/`denom`/`recip`/ops/`Ord`) is consistent between Task 8's implementation, its tests, and the Task 9 re-export smoke test; `from_components`/`small_canon` consume `Integer::to_i128` with matching `Option<i128>` types; `ProofSink` method signatures match between trait, `NoProof`, and the Task 10 `Recorder`.

**`Rational` fast path is symmetric and encapsulated (Task 8):** `Rational` promotes `Small → Big` on overflow and demotes `Big → Small` once a value fits `i128` again, via `Integer::to_i128`. Because the tag is canonical (a value fits ⇒ `Small`; otherwise `Big`), `PartialEq`/`Eq`/`Ord` are correct: equal values share one representation, so `Small`/`Big` cross-comparison is `false` and ordering cross-multiplies over `Integer`. The private `Repr` (behind `pub struct Rational(Repr)`, mirroring `Integer`) prevents external construction of a non-canonical value. Promotion, demotion, and oracle-agreement are covered by Task 8's unit + differential tests.
