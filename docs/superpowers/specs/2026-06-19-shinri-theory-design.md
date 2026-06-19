# shinri-theory — Design Specification

**The theory-combination framework: a shared Equality Engine, the `TheorySolver` abstraction, and the Nelson–Oppen `Combiner` that turns a federation of theory solvers into one `sat::Theory`**

- **Date:** 2026-06-19
- **Status:** Approved design — ready for implementation planning
- **Scope:** A build-ready specification for the `shinri-theory` crate (Phase 1 component #4, after `shinri-num`, `shinri-core`, and `shinri-sat`). Targets **QF_UFLRA** combination. Derived from and consistent with the north-star design (`2026-06-18-shinri-design.md`, §6) and the SAT spec (`2026-06-19-shinri-sat-design.md`, §8).

---

## 1. Purpose & Position in the Workspace

`shinri-theory` is the **theory-combination framework** of shinri. It does not contain any individual decision procedure — congruence closure lives in `shinri-euf`, simplex/difference-logic in `shinri-arith`. Instead it owns the substrate those theories plug into: the shared equality engine they reason over, the `TheorySolver` trait they implement, the atom registry that routes Boolean atoms to the owning theory, and the `Combiner` that runs Nelson–Oppen combination and presents a single object to the SAT search.

**Dependency position** (north-star §3): `num ← core ← sat ← theory ← {euf, arith} ← solver`. `shinri-theory` depends only on `shinri-core` and `shinri-sat`. It is consumed by `shinri-euf`, `shinri-arith`, and ultimately `shinri-solver`. Because `euf`/`arith` depend on `theory`, the shared equality engine is correctly placed *below* them: they build their procedures on top of it.

The SAT core already owns the `Theory` *calling contract* and the CDCL(T) main loop (`Solver<T: Theory, P, H>`); `shinri-theory` provides the `T` — a `Combiner` that aggregates the concrete theories. This crate is therefore not a second main loop; it is the layer that makes "first runnable QF_UF solver" and later "QF_UFLRA" a drop-in `Solver<Combiner, P, H>`.

### 1.1 Responsibilities (what theory owns)

- The shared **`EqualityEngine`**: a backtrackable union-find + disequality store + proof forest + poll-based merge notification (§4).
- The **`TheorySolver`** trait — the per-theory abstraction `shinri-euf`/`shinri-arith` implement — and the **`TheoryCtx`** context threaded into it (§5).
- The **`Combiner`**: a fixed-struct, enum-routed aggregator that implements `sat::Theory`, runs the Nelson–Oppen orchestration loop, and packages cross-theory conflicts (§6).
- The **`AtomRegistry`**: `Var ↔ TermId` mapping plus the owning-theory classification that drives enum routing (§3).
- **Purification** of mixed terms into pure terms + interface variables (§7).
- **Combination-lemma proof steps** and the certificate protocol the `TheorySolver` trait must satisfy (§8).
- **Combined model assembly** over a `ModelBuilder` (§7.3).

### 1.2 Non-responsibilities (what theory does *not* own)

Congruence closure / the signature table (`shinri-euf`); simplex, difference logic, Farkas-certificate *contents* (`shinri-arith`); SMT-LIB parsing and Tseitin/atom *creation* (`shinri-parser` / `shinri-solver`); the top-level `check-sat` API and proof *serialization* to Alethe/LRAT (`shinri-solver` / a downstream proof crate); the CDCL(T) main loop and Boolean reasoning (`shinri-sat`). `shinri-theory` owns the framework and the combination logic; the concrete theories own their algorithms and their proof leaves.

### 1.3 Inherited vocabulary

From `shinri-core`: `Var`, `Lit`, `TermId`, `SortId`, the term DAG `Context`, `Op`/`BuiltinOp` (`Eq`, `Distinct`, `Le`, `Lt`, …), `Rational`/`DeltaRational`, the generic `UndoLog<E>` backtracking discipline, and the `ProofSink` / `TheoryJust { theory: u16, tag: u32 }` proof seam. From `shinri-sat`: the `Theory` trait (the calling contract this crate implements), `Effort`, `TheoryResult`, `Conflict`.

---

## 2. Design Principles (inherited + theory-specific)

These specialize the north-star principles (§2) for the combination layer.

1. **Soundness is existential.** Anything a theory cannot reason about exactly is refused at atom-registration time, before search begins; the top-level solver then returns `unknown`. The combiner never guesses, and every in-search invariant stays total (§9).
2. **One shared source of equality truth.** A single `EqualityEngine` holds the equality state for *all* theories (cvc5-style). Theories never maintain a private notion of which shared terms are equal, and never exchange equalities pairwise — that duplication is the classic Nelson–Oppen soundness-bug source.
3. **Index/arena over smart pointers.** The engine is indexed by dense `ENodeId`; sub-theories receive a borrowed `&mut TheoryCtx`, never shared ownership. No `Rc`/`RefCell`/`Arc`.
4. **Backtracking via `UndoLog`, never snapshots.** The engine and every sub-theory record backtrackable mutations on typed undo logs synchronized to SAT decision levels.
5. **Closed, monomorphized theory set.** The `Combiner` is a concrete struct with named theory fields, enum-routed — no `dyn` on the hot path. Adding a Phase-3 theory is a deliberate edit, not a runtime config.
6. **Convex now, non-convex seam designed in.** Deterministic model-based equality propagation is complete for QF_UFLRA. The reconciliation step is structured so non-convex arrangement enumeration can be slotted in later without a rewrite, but it is not built now.
7. **Exact arithmetic only.** Rationals via `shinri-num`; strict bounds via `DeltaRational`. A float in a theory core is a soundness bug, full stop.

---

## 3. Crate Layout & Module Boundaries

```
shinri-theory/src/
├── lib.rs            # public surface: Combiner, TheorySolver, TheoryCtx, EqualityEngine, ModelBuilder
├── eq_engine.rs      # EqualityEngine: union-find, disequalities, merge-notify, proof forest
├── solver_trait.rs   # TheorySolver trait + TheoryCtx
├── combiner.rs       # Combiner: sat::Theory impl + Nelson–Oppen orchestration loop
├── atom.rs           # AtomRegistry: Var <-> TermId, owning-theory classification (Owner)
├── interface.rs      # InterfaceSet: shared-variable tracking + model-based reconciliation
├── proof.rs          # combination-lemma justification + certificate protocol
└── model.rs          # ModelBuilder + combined model assembly
```

**The atom registry & enum routing.** `shinri-solver` creates a Boolean abstraction of each theory atom and registers `(Var, TermId)` with the `Combiner`. At registration each atom is classified **once** by inspecting its `Op`:

- `Eq`/`Distinct` over uninterpreted terms, and uninterpreted predicate applications → `Owner::Euf`.
- `Le`/`Lt`/`Ge`/`Gt` and arith-shaped `Eq` → `Owner::Arith`.
- An (in)equality spanning both signatures → `Owner::Shared`, resolved by purification (§7) into pure atoms per theory plus interface equalities.

The `Owner` tag is stored per-`Var` in the `AtomRegistry`, so `assert`/`explain` are a single branch to the right theory field — no scanning, no `dyn`.

**Control flow per SAT decision level.** `Solver` calls `Combiner::assert(lit)` → route to the owning sub-theory and mirror equality atoms into the shared `EqualityEngine`. `Combiner::propagate` runs each sub-theory's propagation, lets the engine fire congruence/interface merges, and exchanges shared equalities to fixpoint. `Combiner::check(Full)` runs before `Sat` is declared. `push`/`pop` fan out to the engine and every sub-theory, synchronized to SAT decision levels.

---

## 4. The Shared `EqualityEngine`

The engine answers two distinct questions with two backtrackable structures.

### 4.1 Union-find — "what is equal *now*?"

A dense `ENode` index space with a `TermId → ENodeId` map; terms are interned into the engine on demand (`intern`, idempotent). **Union-by-size, no path compression** — path compression mutates parent pointers during `find` (a read), and in a backtracking setting every mutation must be logged to be undone, which costs more on the hottest operation than the compression saves. Union-by-size bounds class-tree depth to `O(log n)`; `ENodeId` indexes into a contiguous arena, so the hops are cache-friendly array reads. Every `merge` records one `UndoLog<EqUndo>` entry; `pop_to(level)` restores the structure exactly.

### 4.2 Proof forest — "*why* is `a = b`?"

A separate edge-labeled undirected forest (Nieuwenhuis–Oliveras proof-producing congruence closure), reoriented on each union so the new edge connects the two trees. Each edge carries a justification:

```rust
enum EqJust {
    Asserted(Lit),                // an input equality literal a = b hit the trail
    Congruence(ENodeId, ENodeId), // f(s..) = f(t..) because each argument pair is equal
    Interface(TheoryJust),        // an equality another theory derived
}
```

`explain(a, b, &mut out)` walks the forest path between `a` and `b`, collecting `Asserted`/`Interface` leaf literals and recursively expanding `Congruence` edges down to asserted leaves. Its output is the antecedent `Vec<Lit>` consumed by both `sat::Theory::explain` (conflict analysis) and the combination certificate (§8).

### 4.3 Disequalities

A backtrackable set of disequal representative pairs, populated from asserted `Distinct` / negated `Eq`. The engine reports a conflict iff a `merge` would unite two classes already known disequal. **This is the only equality-conflict source**, and it is caught before the merge becomes observable.

### 4.4 Notification without `dyn`

The engine holds no observer callbacks. It appends to an internal queue; consumers poll via `drain_merges(&mut Vec<MergeEvent>)`. EUF's congruence driver consumes merge events to recanonicalize signatures and request further merges; the combiner consumes them to detect newly-equal interface variables. This keeps notification monomorphized and allocation-light, avoids the reentrant `&mut` borrow that synchronous callbacks would force (no `RefCell`), and enables egg-style **deferred-rebuild batching** (dedup redundant signature recomputation across a batch).

### 4.5 API surface

```rust
impl EqualityEngine {
    fn intern(&mut self, t: TermId) -> ENodeId;            // idempotent
    fn find(&self, n: ENodeId) -> ENodeId;
    fn are_equal(&self, a: ENodeId, b: ENodeId) -> bool;
    fn merge(&mut self, a: ENodeId, b: ENodeId, j: EqJust) -> Result<(), EqConflict>;
    fn assert_diseq(&mut self, a: ENodeId, b: ENodeId, j: EqJust) -> Result<(), EqConflict>;
    fn explain(&mut self, a: ENodeId, b: ENodeId, out: &mut Vec<Lit>);
    fn drain_merges(&mut self, out: &mut Vec<MergeEvent>);
    fn push(&mut self);
    fn pop(&mut self, n: usize);
}
```

### 4.6 Soundness invariants (re-checkable)

1. A `merge` uniting a known-disequal pair is the sole equality conflict; caught before observable.
2. `explain(a, b)` returns only asserted leaf literals whose conjunction genuinely entails `a = b` — independently re-checkable.
3. `pop` restores union-find, proof forest, disequality set, *and* the merge-event queue to their pre-`push` state.

### 4.7 Division of labor with EUF

The engine owns the union-find, disequalities, proof forest, and merge events. `shinri-euf` owns the signature table and the congruence worklist loop; it *drives* the engine via `merge`/`drain_merges` but holds no equality state of its own. One source of truth (Principle 2).

---

## 5. The `TheorySolver` Trait & Threaded Context

The per-theory abstraction `shinri-euf`/`shinri-arith` implement. Distinct from `sat::Theory` (which only the `Combiner` implements): sub-theories never see the SAT solver, only the shared context.

### 5.1 `TheoryCtx`

Sub-theories do not own the equality engine — the `Combiner` does, and threads it in by reference along with the read-only term DAG and atom map:

```rust
pub struct TheoryCtx<'a> {
    pub terms: &'a Context,            // hash-consed term DAG (read-only)
    pub eq:    &'a mut EqualityEngine, // the one shared engine
    pub atoms: &'a AtomRegistry,       // Var <-> TermId (read-only)
}
```

### 5.2 The trait

```rust
pub trait TheorySolver: Default {
    const THEORY_ID: u16;                                  // matches TheoryJust.theory

    fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId);
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Conflict>;
    fn propagate(&mut self, cx: &mut TheoryCtx,
                 out: &mut Vec<(Lit, TheoryJust)>) -> Option<Conflict>;
    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TheoryResult;
    fn explain(&mut self, cx: &mut TheoryCtx, tag: u32, out: &mut Vec<Lit>);
    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder);
    fn push(&mut self);
    fn pop(&mut self, n: usize);
}
```

### 5.3 The central-EE contract

A sub-theory *reports* a derived equality by calling `cx.eq.merge(x, y, EqJust::Interface(just))`; it *reads* equalities others derived directly from `cx.eq` (e.g., arith consults `cx.eq.are_equal` over its interface variables during `check`). It never talks to the other theory directly — the shared engine is the only channel. This collapses Nelson–Oppen's O(theories²) plumbing to O(theories) and gives one place where a shared equality lives.

### 5.4 Lazy justification

`TheoryJust { theory, tag }` (from core) is the cheap token a propagation stores. The `Combiner` routes on `.theory` to the owning sub-theory's `explain`, which interprets its private `.tag` (an index into the EUF proof forest, or an arith Farkas-certificate slot) and emits antecedent `Lit`s. The explaining clause is reconstructed only if conflict analysis touches the propagation — the hot path stores only the 6-byte token.

### 5.5 The borrow pattern

The `Combiner` holds `eq`, `atoms`, `euf`, `arith` as *separate fields*. Its orchestration destructures them to build a `TheoryCtx { eq: &mut self.eq, atoms: &self.atoms, terms: &self.terms }` and call `self.euf.propagate(cx)` — disjoint field borrows, so no `RefCell`. Avoiding methods that borrow all of `self` is an explicit invariant of `combiner.rs`.

---

## 6. The `Combiner`: `sat::Theory` impl + Nelson–Oppen Orchestration

The single object `Solver<Combiner, P, H>` drives.

```rust
pub struct Combiner {
    terms:  Context,          // or a shared handle to it
    eq:     EqualityEngine,   // the one shared engine
    atoms:  AtomRegistry,     // Var -> (TermId, Owner)
    euf:    Euf,              // shinri-euf : TheorySolver
    arith:  Arith,            // shinri-arith : TheorySolver
    iface:  InterfaceSet,     // shared (purified) variables + reconciliation scratch
    merges: Vec<MergeEvent>,  // reused drain buffer (allocation-free steady state)
}
enum Owner { Euf, Arith, Shared }
```

### 6.1 `assert(lit)`

Route on `atoms[var(lit)].owner` to the owning sub-theory's `assert`; if the atom is an equality/disequality, also mirror it into `eq` (`merge` or `assert_diseq`). A returned `Conflict` short-circuits.

### 6.2 `propagate` — the `Standard`-effort fixpoint

Loop until no change:

1. `euf.propagate`, then `arith.propagate`, collecting `(Lit, TheoryJust)` implications into the caller-owned buffer.
2. `eq.drain_merges(&mut self.merges)`; EUF's congruence driver consumes them (new signatures → further merges); interface merges are noted.
3. Any `EqConflict` / theory `Conflict` is packaged (§6.4) and returned.

Returns when propagation, congruence, and interface merges jointly stop producing new facts.

### 6.3 `check(Full)` — final-check fixpoint + model-based combination

Invoked when the Boolean assignment is complete, before `Sat` is declared:

1. `euf.check(Full)`, `arith.check(Full)` — each asserts internal consistency, possibly emitting conflicts/lemmas.
2. **Interface reconciliation (convex, deterministic).** Each theory exposes its model's partition over the shared interface variables. Where the partitions disagree — one theory's model equates `x,y`, the other separates them — the combiner tests entailment cheaply and propagates the entailed interface equality via `eq.merge(x, y, Interface(just))`, which the other theory sees on its next `check`. Because both theories are convex, this needs **no case-splitting on arrangements**; the reconciliation is a deterministic loop. *(This is the exact point the non-convex seam plugs in later: the reconciliation step would branch on a disjunction of arrangements instead of deterministically propagating.)*
3. Repeat until both theories report `Sat` and their interface partitions agree with no new merge → return `Sat`. Any inconsistency returns a conflict/lemma, keeping the SAT search alive.

### 6.4 Conflict packaging

A theory or engine conflict is a set of `ENode`/literal references. The combiner calls `eq.explain` and the owning theory's `explain` to expand every justification — *including* `Interface` edges, which recurse into the *other* theory's `explain` — into a flat antecedent `Vec<Lit>`. The negated set is the conflict clause handed to `shinri-sat`'s analyzer. This cross-theory `explain` recursion is what makes combination conflicts sound.

### 6.5 `push` / `pop`

`sat::Theory::push` → `eq.push()` + `euf.push()` + `arith.push()`, once per SAT decision level. `pop(n)` fans out identically. The `AtomRegistry` and `InterfaceSet` are append-only across a solve (atoms are not un-registered on backtrack), so only the stateful engines undo.

### 6.6 Alignment with the `sat::Theory` seam

`Combiner::propagate`/`check` adapt the per-theory results into the exact shapes the live `shinri-sat` seam expects (conflict literal-sets and `TheoryResult`). Sub-theory `Conflict`s are unioned/packaged by the combiner.

### 6.7 Soundness invariant

`Sat` is returned only at the joint fixpoint of Boolean BCP, both theories' `propagate`, both `check(Full)`, and interface reconciliation — no unreconciled interface disagreement may survive a `Sat`.

---

## 7. Purification, Interface Variables & Model Assembly

### 7.1 Purification

Nelson–Oppen requires each theory to see only *pure* terms in its own signature. A mixed term like `f(x + y)` is split by introducing a fresh **interface variable** `w`: EUF sees `f(w)`, arith receives the defining equality `w = x + y`, and `w` is marked **shared**.

Purification is performed by the `Combiner` at atom-registration time — it already owns the term `Context`, the `EqualityEngine`, and the `AtomRegistry`. When an atom is registered, the combiner walks it; wherever a subterm crosses a theory boundary (an arith-sorted argument under an uninterpreted op, or vice versa), it interns a fresh constant `w`, flags its `ENode` as interface in the `InterfaceSet`, and routes the defining equality to the owning theory. Purification facts are level-0 (append-only across the solve), so they are not undone on backtrack.

### 7.2 Interface variables

Exactly these fresh shared constants, plus any original variable appearing in more than one theory's atoms. They are the only terms the model-based reconciliation loop (§6.3) ranges over, keeping reconciliation cost proportional to the shared surface, not the whole problem.

### 7.3 Model assembly

On `Sat`, the combiner builds the combined model:

```rust
pub enum ModelVal {
    Bool(bool),
    Num(Rational),       // arith-sorted terms
    Elem(SortId, u32),   // an abstract domain element for an uninterpreted sort
}
pub struct ModelBuilder { /* TermId -> ModelVal, keyed by representative */ }
```

1. `arith.model(cx, &mut mb)` assigns a `Rational` (via `DeltaRational` → concrete rational) to each arith term / interface variable.
2. `euf.model(cx, &mut mb)` assigns each uninterpreted equality class a distinct `Elem` — except interface classes, which already carry the value arith gave them.
3. The combiner checks consistency at the seam. Because reconciliation guaranteed the interface partitions agree and both theories are stably-infinite (enough fresh domain elements always exist), a consistent total assignment provably exists. The assembled `TermId → ModelVal` map is handed up to `shinri-solver` for `get-model` / `get-value`.

A debug-gated **model self-check** re-evaluates every asserted literal against the assembled model and asserts it holds — the cheap soundness net for the `Sat` path, mirroring the SAT layer's existing model self-check.

---

## 8. Certificate Protocol (full external certificates)

The combined UNSAT certificate is the SAT-layer resolution proof (produced via `ProofSink::learn`) in which **theory lemmas are the leaves**, each entered through `ProofSink::theory_lemma(clause, lits, just)` with a justification expandable to a checkable derivation:

- **EUF leaf:** the proof-forest path → a congruence-closure proof (asserted-equality literals + congruence steps).
- **Arith leaf:** a Farkas certificate (rational coefficients witnessing linear infeasibility).
- **Combination step:** an interface-equality lemma justified by the producing theory's certificate; the `Combiner` records the *stitch* that resolves it against the consuming theory's reasoning.

**Boundary.** `shinri-theory` produces the in-memory justification content sufficient to reconstruct the proof; serialization (Alethe / LRAT) is a downstream consumer in `shinri-solver` / a proof crate, matching how `shinri-core` defined `TheoryJust` as captured-here, emitted-downstream. The protocol contract on the `TheorySolver` trait: every `TheoryJust` a theory emits must be expandable by `explain` into both (a) a set of antecedent literals and (b) a checkable derivation.

**Re-checker.** A dev-gated checker independently re-verifies that every emitted theory lemma is genuinely T-valid (re-runs the congruence / Farkas check) and that the stitched combined proof is well-formed — this is the north-star §10 "certificate independently re-checked" guard.

---

## 9. Error Handling & Soundness Discipline

- **Soundness is existential — no in-solve `unknown` path needed.** Anything a theory cannot handle exactly (nonlinear `Mul`, an unsupported sort/construct) is **refused at atom-registration time**, before search; the top-level `shinri-solver` then reports `unknown` for the query. Every in-search invariant stays total — the combiner never produces a guess, and `TheoryResult` stays `{Sat, Conflict, Lemma}`.
- **The single equality-unsoundness vector** (merging a known-disequal pair) is guarded in the `EqualityEngine` and caught before observable (§4.3).
- **Exact arithmetic only** — `shinri-num` rationals, strict bounds via `DeltaRational`; no float anywhere in a theory core. The i128 fast path (in `shinri-arith`) must detect overflow and promote to bignum — never silent wraparound.
- **Invariant checks** (`debug_assert!`) gate the soundness invariants of §§4–6; the release hot path uses audited `get_unchecked` only where individually justified, consistent with `shinri-sat`'s discipline.

---

## 10. Testing & Verification Strategy

Layered, matching the established project culture.

1. **Unit** — per module: `EqualityEngine` merge / explain / disequality-conflict; combiner routing; purification.
2. **Property / round-trip** — random `merge` / `assert_diseq` / `push` / `pop` sequences against the engine; invariants: `find` consistent, `explain` returns a valid entailing antecedent, and `pop` restores the engine exactly (the reset round-trip the SAT crate already tests).
3. **Differential / oracle (dev-only, feature-gated)** — QF_UF, QF_LRA, QF_UFLRA SMT-LIB benchmarks vs a `z3.rs` / `easy-smt` oracle (dev-dependency only — pure-Rust mandate intact). **Any sat/unsat disagreement is a P0 bug.** On `sat`, model self-check; on `unsat`, certificate re-check. Crafted **interface-variable-heavy** instances get extra weight, since model-based combination is the flagged soundness-bug source.
4. **Certificate re-checker** — independently verifies every theory lemma and the stitched combined proof (§8).
5. **Mutation testing (`cargo-mutants`)** on the combiner and `EqualityEngine` — confirm the suite catches behavioral changes.
6. **Fuzzing (`cargo-fuzz`)** — random QF_UFLRA inputs; later chained with the existing parser fuzz target.

---

## 11. Scope Boundaries (what is deliberately deferred)

- **Non-convex theory combination** (LIA, arrays) — arrangement enumeration / interface-equality splitting. The reconciliation step (§6.3) is structured to accept it later without a rewrite, but it is not built now.
- **General Delayed Theory Combination** — deferred per north-star §6.7; the central-EE model-based scheme is the Phase-1 mechanism.
- **Proof serialization** to Alethe / LRAT — a downstream consumer; this crate produces the in-memory certificate content only.
- **Phase-3 theories** (bit-vectors, arrays) — adding one is a deliberate edit to the `Combiner` struct + `Owner` enum, by design.

---

## References

- Nieuwenhuis, Oliveras, Tinelli. *Solving SAT and SAT Modulo Theories.* JACM 2006. (DPLL(T) calculus.)
- Nelson, Oppen. *Simplification by Cooperating Decision Procedures.* TOPLAS 1979. (Theory combination.)
- de Moura, Bjørner. *Model-based Theory Combination.* SMT 2007.
- Nieuwenhuis, Oliveras. *Proof-Producing Congruence Closure.* RTA 2005. (Proof forest / `explain`.)
- Dutertre, de Moura. *A Fast Linear-Arithmetic Solver for DPLL(T).* CAV 2006. (`DeltaRational`, Farkas.)
