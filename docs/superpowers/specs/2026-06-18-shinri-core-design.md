# shinri-core — Design Specification

**The shared core: term/sort DAG, identity vocabulary, backtracking toolkit, arithmetic abstraction, proof seam**

- **Date:** 2026-06-18
- **Status:** Approved design — ready for implementation planning
- **Scope:** A build-ready specification for the `shinri-core` crate (Phase 1 component #2, after `shinri-num`). Derived from and consistent with the north-star design (`2026-06-18-shinri-design.md`, §4).

---

## 1. Purpose & Position in the Workspace

`shinri-core` is the shared vocabulary every higher crate speaks. It defines the term/sort representation, the identity types, the backtracking machinery, the rational-arithmetic abstraction over `shinri-num`, and the proof-production seam. It contains **no** theory logic, **no** SAT search, and **no** parsing — those live in `shinri-sat`, `shinri-{euf,arith}`, `shinri-theory`, and `shinri-parser`, all of which depend on core.

**Dependency position** (from north-star §3): `num ← core ← sat ← theory ← {euf, arith} ← solver`; `parser` depends on `core`.

`shinri-core` depends only on `shinri-num` plus a small set of curated permissive (MIT/Apache) crates. It is the lowest layer that defines shared identity vocabulary used across the SAT, theory, and proof layers.

### 1.1 Responsibilities (what core owns)

- The foundational **id newtypes** (§3).
- The hash-consed immutable **term/sort DAG** and its owning `Context`, with a well-sortedness-checking **builder** (§4–§5).
- The generic **backtracking toolkit** `UndoLog<E>` (§6).
- The **`Rational` trait + `FastRat`** fast-path type and `DeltaRational` (§7).
- The **`ProofSink` trait + `NoProof`** zero-cost default (§8).

### 1.2 Non-responsibilities (what core does *not* own)

Congruence closure, simplex, difference logic, CDCL search, clause storage, SMT-LIB parsing, the top-level solver API. Core defines the *types these layers exchange*, not their algorithms.

---

## 2. Dependency Policy

Unlike `shinri-num` (which is zero-dependency by mandate), `shinri-core` may use curated permissive crates, consistent with north-star §3.1 ("the shipping dependency surface is deliberately tiny and fully permissive (MIT/Apache)"). Specifically:

- **`rustc-hash`** (`FxHashMap`) — the interner hash map. SipHash is never used on hot interning paths (north-star §4.1). `ahash` is an acceptable alternative if benchmarking favors it.
- **`smallvec`** (optional) — small-buffer-optimized vectors where profiling shows it pays.
- **`shinri-num`** — the only intra-workspace dependency.

`cargo deny` (already configured at the workspace level) forbids native-link crates; this design adds no crate that would violate it.

---

## 3. Identity Types

All ids are `Copy`, `#[repr(transparent)]`, and chosen so `Option<Id>` stays 4 bytes. `u32` id-space caps a solve at ~4 billion distinct entities — universally sufficient for SMT and deliberately chosen for cache density (north-star §4.1).

```rust
#[repr(transparent)] pub struct TermId(NonZeroU32);   // index into Context.nodes
#[repr(transparent)] pub struct SortId(NonZeroU32);   // index into Context.sorts
#[repr(transparent)] pub struct SymbolId(u32);        // index into the string interner
#[repr(transparent)] pub struct RatId(u32);           // index into Context.nums (literal values)

// Shared SAT/theory/proof currency — semantics-free identity, defined here because
// core is the lowest common ancestor of every crate that must name them (see §3.1).
#[repr(transparent)] pub struct Var(u32);
#[repr(transparent)] pub struct Lit(u32);             // var << 1 | sign
#[repr(transparent)] pub struct ClauseId(u32);
```

### 3.1 Decision: the SAT/theory currency types live in core

`Var`, `Lit`, and `ClauseId` are *conceptually* SAT-layer concepts (`shinri-sat` owns the assignment map and the clause DB). They are defined in **core** because the set of crates that must *name* them — `core` (via `ProofSink`), `sat`, `theory`, `euf`, `arith` — has `core` as its lowest common ancestor.

- `ProofSink` (in core, §8) records clause events keyed by `ClauseId`, over clauses that are slices of `Lit`.
- The `Theory` trait (north-star §6.2, in `shinri-theory`) traffics entirely in `Lit`.
- `shinri-euf` / `shinri-arith` return conflict explanations as `Vec<Lit>`.

These types are **inert identity newtypes** — no methods implying SAT semantics; `shinri-sat` assigns meaning (maintains var→value, the clause DB). This mirrors how core already defines `SymbolId(u32)` for a concept (symbols) it does not otherwise reason about.

**Alternatives rejected:**
- *Generic `ProofSink<L, C>`* — propagates type parameters through everything that touches the sink for purely cosmetic purity; sat and theory must agree on one instantiation anyway.
- *Raw `u32`/`&[i32]` in the sink* — discards type safety precisely in the proof path, where a swapped id is a silent soundness bug.

A single canonical `Lit` across the whole stack also eliminates conversion boilerplate at every crate boundary.

---

## 4. Term & Sort Representation

A hash-consed immutable DAG, index-based, with one owning `Context`. Everything refers to terms and sorts by small copyable ids.

```rust
pub enum TermNode {                         // fixed-size; children stored out-of-line
    App   { op: Op, args: ChildSlice, sort: SortId },  // 0-ary apps permitted
    Const { val: ConstVal, sort: SortId },
    // Var(DeBruijn, SortId)  — RESERVED (Phase 4 quantifiers); not built (see §4.3)
    // Quant(...)             — RESERVED (Phase 4); not built
}

pub enum Op {
    Builtin(BuiltinOp),                     // interpreted core + theory operators
    Uninterpreted(SymbolId),                // user-declared function or 0-ary constant
}

pub enum BuiltinOp {                        // compact (fits in u8/u16); central op-kind enum
    // Boolean / core
    Not, And, Or, Implies, Xor, Eq, Distinct, Ite,
    // Arithmetic (Int/Real)
    Neg, Add, Sub, Mul, Le, Lt, Ge, Gt,
    // RESERVED for later phases (added as variants when their phase arrives):
    //   bit-vector ops (Phase 3), array select/store (Phase 3), ...
}

pub enum ConstVal { Bool(bool), Num(RatId) }   // Num -> Context.nums side arena

pub struct ChildSlice { pub off: u32, pub len: u32 }   // into Context.children
```

```rust
pub enum SortNode {
    Bool, Int, Real,
    Uninterpreted(SymbolId),                // (declare-sort A 0)
    // BitVec(u32)            — RESERVED (Phase 3); not built
    // Array(SortId, SortId)  — RESERVED (Phase 3); not built
}

pub struct Context {
    nodes:    Vec<TermNode>,                     // term arena; TermId indexes here
    children: Vec<TermId>,                       // shared out-of-line child storage (SoA)
    nums:     Vec<Rational>,                     // literal values; RatId indexes here
    interner: FxHashMap<StructuralKey, TermId>,  // structural dedup -> maximal sharing
    sorts:    Vec<SortNode>,
    sort_interner: FxHashMap<SortKey, SortId>,
    symbols:  StringInterner,                    // symbol text <-> SymbolId
}
```

`Rational` in `Context.nums` is the concrete `shinri_num::Rational` (literal values are stored exactly; the `FastRat` abstraction of §7 is for the theory layer's hot arithmetic, not for term storage).

### 4.1 Properties bought (north-star §4.1)

- **O(1) structural equality** — compare `TermId`s.
- **Maximal sharing** — the interner guarantees one node per distinct subterm.
- **Cache density** — fixed-size nodes; children stored out-of-line (struct-of-arrays); `FxHashMap` (never SipHash); `NonZeroU32` newtypes keep `Option<Id>` at 4 bytes.
- **Side tables, keyed by id** — proof metadata, and later E-matching indices / parallel partition metadata, live in side tables keyed by `TermId`, never bloating the hot node struct.

### 4.2 Decision: interpreted-vs-uninterpreted operator split

`Op = Builtin(BuiltinOp) | Uninterpreted(SymbolId)`. `BuiltinOp` is a compact central enum of standardized SMT-LIB core+theory operators; user-declared functions are `Uninterpreted(SymbolId)`.

**Rationale.** Theories and the rewriter classify operators constantly ("arithmetic atom? boolean connective? uninterpreted app?"). A `match` over a small enum (`Builtin(b) => match b { … }`) is a branch-predictable jump table — far faster than comparing `SymbolId`s against cached well-known ids or consulting a runtime attribute table. This is the industry-standard central op-kind enum (Z3 `decl_kind`, cvc5 `Kind`). 0-ary uninterpreted constants from `(declare-fun x () Int)` fall out as `App { op: Uninterpreted(sym), args: empty }`; numerals/booleans are `Const`.

**Alternatives rejected:**
- *Everything is a `SymbolId`* — relocates the operator taxonomy from the type system into a runtime table, slowing every classification on the hot path.
- *Flatten builtins into `TermNode` variants* — fastest single dispatch, but explodes variant count, sizes the node to its largest variant (fighting cache density), and bakes every theory's operators into core's hottest type.

### 4.3 Decision: reserved-but-not-built (quantifiers / BV / arrays)

Phase 1 logics (QF_UF / IDL / RDL / LRA) are quantifier-free with no bit-vectors or arrays. We **do not** add `Var`/`Quant`/`BitVec`/`Array` variants now (no dead code, no stub match arms). Instead we ensure the *foundational architecture admits them additively* (north-star principle #4: "design the one-way doors in… build full machinery only when its phase arrives"; risk #6):

- metadata lives in **side tables keyed by id**, never as node fields → a future node kind adds a side table, touching no existing node;
- sorts are a proper **interned algebra** (not a flat 3-constant enum) → `(_ BitVec n)` and `(Array I E)` slot in as new `SortNode` variants that the structural sort key already accommodates;
- `match` sites on `TermNode`/`SortNode` stay **local and small** → adding a variant later is a Rust exhaustiveness-guided sweep, not a redesign;
- no decision assumes "terms are always ground / sorts never parameterized" in a way that would block binders.

The real one-way-door risk is whether the arena/interner/sort-algebra *admits* binders and parameterized sorts — secured here by architecture, not by stub variants. Adding a variant later is a small compiler-guided change; adding unused variants now would only front-load dead code that gets rewritten once its driving theory exists.

**Alternatives rejected:**
- *Add variants now with `unreachable!()` arms* — illusory design: dead code and likely-wrong handling that gets rewritten anyway when the driving phase arrives.
- *Ignore the future entirely* — risks a foundational assumption (non-parameterized sorts, no binder encoding) that turns a later addition into a core rewrite (exactly risk #6).

---

## 5. Term Builder & Well-Sortedness

Term construction goes through a checked builder on `Context`. The builder interns (guaranteeing maximal sharing) and **checks well-sortedness inline**, consistent with the parser interning directly (north-star §9.1).

```rust
impl Context {
    pub fn mk_const_bool(&mut self, b: bool) -> TermId;
    pub fn mk_numeral(&mut self, value: shinri_num::Rational, sort: SortId) -> Result<TermId, SortError>;
    pub fn mk_app(&mut self, op: Op, args: &[TermId]) -> Result<TermId, SortError>;
    pub fn mk_eq(&mut self, a: TermId, b: TermId) -> Result<TermId, SortError>;
    // declarations:
    pub fn declare_sort(&mut self, name: &str) -> SortId;
    pub fn declare_fun(&mut self, name: &str, params: &[SortId], result: SortId) -> SymbolId;
    // introspection:
    pub fn sort_of(&self, t: TermId) -> SortId;
    pub fn node(&self, t: TermId) -> &TermNode;
}
```

- `mk_app` resolves the result `sort` from the operator + argument sorts and rejects ill-sorted applications with `SortError` (a recoverable error the parser reports; never a panic — north-star §10).
- **Well-known sorts** (`Bool`, `Int`, `Real`) are interned once at `Context::new` and exposed as constants/accessors.

### 5.1 `define-fun` handling

SMT-LIB `define-fun` is macro-like. It is handled by **substitution/rebuild**: core exposes a `substitute` helper, and `shinri-parser` beta-reduces a definition at its use sites during parsing. No definition nodes enter the DAG, keeping the term layer free of binding forms in Phase 1.

```rust
impl Context {
    /// Rebuild `t` with each occurrence of params[i] replaced by args[i]. Re-interns.
    pub fn substitute(&mut self, t: TermId, params: &[TermId], args: &[TermId]) -> TermId;
}
```

---

## 6. Backtracking Toolkit — `UndoLog<E>`

Core provides a **generic, monomorphized** backtracking primitive. It owns the decision-level / scope-marker machinery and the replay loop; each component (the SAT core, each theory) instantiates `UndoLog` with its **own concrete POD entry type** and supplies how to undo a single entry. This is synchronized to SAT decision levels (north-star §4.2): `shinri-sat` drives `push_level`/`pop_to` as it makes and retracts decisions.

```rust
pub struct UndoLog<E> {
    entries: Vec<E>,        // flat, cache-dense, POD
    levels:  Vec<usize>,    // entries.len() at each level boundary
}

impl<E> UndoLog<E> {
    pub fn record(&mut self, e: E);
    pub fn push_level(&mut self);
    /// Pop back to `level`, replaying each undone entry through `f` in reverse order.
    pub fn pop_to(&mut self, level: usize, f: impl FnMut(E));
    pub fn level(&self) -> usize;
}
```

Example consumer (in `shinri-euf`, *not* in core):

```rust
enum EufUndo { SetRepr(Id, Id), PushUse(Id), /* ... */ }
// on backtrack:
log.pop_to(target, |e| match e { EufUndo::SetRepr(n, old) => uf[n] = old, /* ... */ });
```

### 6.1 Decision: generic `UndoLog<E>` over alternatives

- **Performance.** Records are POD pushes to a flat `Vec` (excellent locality); replay dispatches through a `match` that is **monomorphized per component** (`E` is concrete) — a static jump table, no virtual dispatch. Normal (non-backtrack) access to component state has **zero** overhead: hot structures (union-find arrays, simplex tableau) stay plain arrays; only mutations also append an entry.
- **Layering.** Each component's entry enum is private to that component — no cross-layer `UndoAction` enum (which would force core to know about EUF/simplex internals) and no `Box<dyn FnOnce>` per mutation (heap churn / indirect call on the hot path, against north-star principle #2).

**Alternatives rejected:**
- *Trailed container types* (cvc5 context/CDO style) — most ergonomic, but a single shared heterogeneous trail needs type erasure → an indirect (vtable) call per entry on replay, each often touching a different object → a cache miss per undo. Prized for correctness ergonomics, not speed; Yices2/Bitwuzla use typed per-component logs for hot theories.
- *Minimal `Backtrackable { push; pop(n) }` trait only* — same performance ceiling as `UndoLog<E>` but forces every theory to re-implement level/replay bookkeeping, multiplying the bug surface for one of the most correctness-sensitive mechanisms.

**Future ergonomics.** Thin trailed helpers (e.g. a `TrailedScalar<T>`) may later be layered *on top of* `UndoLog<E>` for cold, non-hot state, where convenience outweighs the tiny indirection — without slowing the hot path.

---

## 7. Arithmetic Abstraction — `Rational` trait + `FastRat`

The theory layer's hot arithmetic flows through a `Rational` **trait** (north-star §4.3), with a concrete fast-path type `FastRat` that stays unboxed until coefficients overflow, spilling to `shinri_num::Rational`.

```rust
pub trait Rational:
    Clone + PartialEq + PartialOrd + Add + Sub + Mul + Div + Neg + /* AddAssign, ... */
{
    fn zero() -> Self;
    fn one() -> Self;
    fn from_i64(n: i64) -> Self;
    fn is_zero(&self) -> bool;
    fn signum(&self) -> i32;
    fn recip(&self) -> Self;
    // ... the closed operation set the simplex/IDL layers require ...
}

pub enum FastRat {
    Small { n: i128, d: i128 },          // canonical: d > 0, gcd(|n|, d) = 1
    Big(shinri_num::Rational),           // overflow fallback
}

impl Rational for FastRat { /* overflow-checked ops; spill Small -> Big on overflow */ }
```

- **`Small` invariant:** kept canonical (positive denominator, reduced) so comparison and equality are branch-light. Arithmetic uses `i128::checked_*`; on overflow the operands promote to `Big` and the operation is redone in `shinri_num::Rational`.
- **`DeltaRational`** for simplex strict inequalities is provided over the rational representation (the `(c, k)` pair, north-star §6.5). `shinri_num::DeltaRational` already exists for the concrete type; the core layer exposes the delta pairing for the `FastRat` fast path.
- **Why a trait, not just `shinri_num::Rational`:** the concrete `shinri_num::Rational` is two enum-tagged `Integer`s with per-op match dispatch; `FastRat::Small` is a bare unboxed `i128` pair, materially cheaper on the overwhelmingly-common small-coefficient path (north-star §7.1). The trait is the one-way door that lets the theory layer be written against the abstraction now and benefit from the fast path immediately.

---

## 8. Proof Seam — `ProofSink` trait + `NoProof`

A zero-cost generic `ProofSink` threaded through clause add/learn/delete from day one (north-star §4.4, §8.2). Emission (Alethe, checked by Carcara; native LRAT hints) is Phase 2 — but the seam captures everything those formats need now, so Phase 2 is a *consumer* of already-captured data rather than a retrofit (risk #6).

```rust
pub trait ProofSink {
    fn input(&mut self, c: ClauseId, lits: &[Lit]);
    fn learn(&mut self, c: ClauseId, lits: &[Lit], chain: &[ClauseId]);   // LRAT hint
    fn theory_lemma(&mut self, c: ClauseId, lits: &[Lit], just: TheoryJust);
    fn delete(&mut self, c: ClauseId);
}

pub struct NoProof;                      // ZST; every method is an #[inline] empty body
impl ProofSink for NoProof { /* ... */ }
```

### 8.1 Decision: resolution-chain granularity, borrow-don't-build

The sink records the full proof DAG at clause granularity: input clauses; each learned clause **with its resolution/derivation chain** (the LRAT hint); theory lemmas tagged with a `TheoryJust` token; deletions. This is exactly what LRAT and Alethe consume.

**Zero-cost-when-off is a guaranteed invariant, secured by a hard implementation rule:** sink methods take **borrowed, already-computed** data (`&[Lit]`, `&[ClauseId]`); nothing is materialized for the sink's benefit. The resolution chain is *a byproduct of 1-UIP conflict analysis* (north-star §5) — analysis already walks each antecedent clause; its ids are the chain, passed as a borrow of a buffer analysis already maintains. With `P = NoProof` (a ZST with empty inlined bodies), the calls and any unused argument population dead-code-eliminate. The SAT core is generic over `P: ProofSink`; monomorphization stamps out a proofless solver with no proof overhead.

**`TheoryJust`** is a small token core defines (e.g. an opaque tag + ids) that a theory attaches to a lemma; the theory crates (EUF proof forest, LRA Farkas certificate) populate its meaning when proof emission lands in Phase 2. It is captured but not interpreted in Phase 1.

**Alternatives rejected:**
- *Coarse event sink* (learned/deleted only, no chain) — same zero-cost-when-off runtime, but discards the derivation chain LRAT/Alethe require, forcing Phase 2 to widen the trait and re-thread the chain through the hottest loop (conflict analysis). A loan against Phase 2 with compounding interest.
- *Generic `Proof` trait with associated types* — format flexibility shinri's roadmap doesn't need (formats are fixed: Alethe + LRAT), paid for in generic spread through the clause DB, code bloat / longer compiles, and per-clause `Ref`-storage risk to the zero-cost guarantee.

---

## 9. Error Handling & Soundness Discipline

Consistent with north-star §10:

- **`Result`-based** for recoverable construction errors: `SortError` from the builder (ill-sorted application, sort mismatch) is reported by the parser, never panicked.
- **Panics reserved for genuine invariant violations** — a broken internal invariant should crash in debug/test, not silently corrupt state.
- **`debug_assert!`** on hot invariants (interner consistency: structural key ⇔ id; `UndoLog` level balance: `pop_to` never underflows; canonical `FastRat::Small`), compiled out of release, exhaustively checked in test/fuzz.

---

## 10. Testing & Verification Strategy

Per-crate slice of north-star §11:

1. **Unit tests** — interner dedup edge cases; builder sort-checking (accept well-sorted, reject ill-sorted); `substitute` correctness; `UndoLog` level push/pop boundaries; `FastRat` overflow-spill boundaries (`i128` edges, denominator normalization, division-by-construction guards).
2. **Property tests (`proptest`):**
   - **Structural equality ⇔ id equality** — two structurally identical builds yield the same `TermId`; distinct structures yield distinct ids.
   - **Interner dedup** — building the same subterm twice never grows `nodes`.
   - **Round-trip** — parse → print → parse is identity on the term DAG (shared with the parser crate).
   - **Undo-log restore identity** — snapshot component state → record mutations → `pop_to` → state is bit-identical to the snapshot. The central backtracking-soundness property.
   - **`FastRat` ⇔ `shinri_num::Rational`** — differential test: every `FastRat` operation agrees with the same operation on `shinri_num::Rational` across a random + overflow-targeted corpus (validates the spill path).
3. **Codegen check** — a proofless (`NoProof`) build carries no proof bookkeeping (verified via benchmark parity and/or inspection that proof calls are elided).
4. **CI gates** (workspace-wide, already configured): `cargo nextest`, `cargo deny check`, `cargo clippy -D warnings`, `cargo fmt --check`.

---

## 11. Deliverable

A `shinri-core` crate providing:

- the id vocabulary (`TermId`/`SortId`/`SymbolId`/`RatId`/`Var`/`Lit`/`ClauseId`),
- the hash-consed term/sort DAG with a well-sortedness-checking builder and `substitute`,
- the generic `UndoLog<E>` backtracking toolkit,
- the `Rational` trait + `FastRat` fast-path type (+ delta-rational pairing),
- the `ProofSink` trait + `NoProof` zero-cost default with resolution-chain granularity,
- the full per-crate test suite (unit, property, differential, codegen, CI gates),

with the cross-cutting one-way doors designed in (reserved-but-not-built quantifier/BV/array variants; side-table-keyed metadata; the proof seam; the arithmetic abstraction) so that `shinri-sat` and the theory layer can be built directly on top without retrofitting core.

---

## Appendix A — Key Decisions (this document)

1. **SAT/theory currency in core** — `Var`/`Lit`/`ClauseId` are inert newtypes defined in core, its being the lowest common ancestor of every crate that names them. (§3.1)
2. **Operator split** — `Op = Builtin(BuiltinOp) | Uninterpreted(SymbolId)`; central op-kind enum for fast type-safe dispatch. (§4.2)
3. **Reserved-but-not-built** — quantifier/BV/array variants are admitted by architecture (side tables, interned sort algebra, local matches), not by stub variants. (§4.3)
4. **`UndoLog<E>`** — generic monomorphized typed undo log; flat POD entries, zero normal-access overhead, no cross-layer enum or `dyn`. (§6.1)
5. **`Rational` trait + `FastRat`** — unboxed `i128` fast path spilling to `shinri_num::Rational`. (§7)
6. **`ProofSink` resolution-chain granularity, borrow-don't-build** — captures what Alethe/LRAT need now; guaranteed zero-cost when off. (§8.1)
