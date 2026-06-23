# shinri QF_ABV — Bitvector Arrays Theory Combination Design

**Date:** 2026-06-23
**Status:** Approved design, pre-implementation
**Scope:** Full SMT-LIB `QF_ABV` logic — extensional arrays restricted to
`(Array (_ BitVec i) (_ BitVec j))`, combined with the existing QF_BV solver,
via lemmas-on-demand abstraction–refinement over the eager bit-blaster.

## 1. Goal & Scope

Add support for the SMT-LIB `QF_ABV` logic to shinri: arrays whose index and
element sorts are both fixed-width bitvectors, mixed freely with the full QF_BV
operator set already implemented in `shinri-bv`.

Per the SMT-LIB standard, `QF_ABV` restricts every array term to the sort
`(Array (_ BitVec i) (_ BitVec j))` for some `i, j > 0`. **Nested arrays
(array-valued elements) are not part of QF_ABV.** Store *chaining* —
`(store (store a i e) j f)` — is in scope (it is not sort nesting). Practical
multi-dimensional arrays are encoded as arrays over wider bitvector indices, not
as nesting, so flat BV→BV arrays cover the logic completely.

**In scope (v1):**
- Array terms of sort `(Array (_ BitVec i) (_ BitVec j))`, arbitrary `i, j > 0`.
- `select` (read), `store` (write), arbitrarily chained stores.
- **Extensional** reasoning: array `(= a b)`, `(distinct a b)`, and
  `(not (= a b))` are decided, not refused.
- The full QF_BV operator set as operands of indices and elements.
- `(get-model)` / `(get-value)` over BV terms and over array terms.

**Deliberate non-goals (v1):**
- **Nested arrays / array-valued elements.** Out of QF_ABV by definition.
- **QF_AUFBV / BV+arith / uninterpreted sorts mixed with arrays.** A query that
  mixes arrays with EUF, arith, or uninterpreted index/element sorts is refused
  as `unknown` via the existing `Unsupported` fence discipline.
- **Inter-`check-sat` incrementality.** Each `check-sat` rebuilds the
  abstraction from scratch. (The refinement loop's incrementality is
  *intra*-`check-sat` only — see §6.)

**Soundness contract:** anything out of scope returns `unknown`, never a wrong
SAT/UNSAT verdict. This matches the discipline established by the QF_BV design.

## 2. Approach

**Lemmas-on-demand abstraction–refinement** (the Boolector/Bitwuzla family),
layered over shinri's existing *eager* bit-blaster and *incremental* SAT core.

QF_ABV does **not** route through the lazy Nelson–Oppen `Combiner`, and the
array reasoning does **not** implement `TheorySolver`. This is a deliberate
divergence forced by an impedance mismatch:

- shinri's BV is an **eager pre-pass**: it collects BV atoms, bit-blasts them,
  replaces each with a Boolean surrogate literal, *then* runs Tseitin/SAT.
- The lazy `Arrays` solver (`shinri-arrays`) decides index/array/value equality
  by querying the shared `EqualityEngine`, and it *generates* index-equality
  atoms during CDCL(T) search via `TCheck::Split`. You cannot eagerly pre-blast
  an atom invented mid-search.

Rather than force BV into the lazy seam it was designed to avoid, QF_ABV is a
**third solving path**, parallel to the `Combiner` and alongside the QF_BV
pre-pass. Equality between BV-sorted indices/elements is decided by the
bit-blaster's **concrete model values**, not by the abstract `EqualityEngine`.
The existing lazy `Arrays` solver is **not** reused (its ROW *lemma shapes* are,
as a reference for the model-based checker).

## 3. Architecture & Pipeline Placement

```
parse → assertions (term DAG; may contain BV and BV-array ops)
          │
          ▼  shinri-solver routing
   detect array ops over BV sorts?
     │ no  → existing QF_BV pre-pass / Combiner (unchanged)
     │ yes → mixed with EUF/arith/uninterpreted sorts?
     │          │ yes → unknown (fence)
     │          ▼ no
   ┌─────────────────────────── shinri-abv ───────────────────────────┐
   │ 1. build abstraction: reads → fresh BV vars; array-eqs → fresh    │
   │    Bool; no array axioms. (reuses shinri-bv rewrite + blaster)    │
   │ 2. blast abstraction into a live shinri-sat::Solver               │
   │ 3. refinement loop:                                                │
   │      SAT.solve()                                                   │
   │        UNSAT → UNSAT (final)                                       │
   │        SAT   → consistency check on value_of() model              │
   │                  consistent → SAT (extract model)                 │
   │                  violations → add lemma clauses incrementally,     │
   │                               blast any new reads, loop            │
   └────────────────────────────────────────────────────────────────┘
```

**Crate:** new crate **`shinri-abv`**, mirroring `shinri-bv`'s standalone
layout. Depends on `shinri-bv` (blaster, rewrite front-end, surrogate maps,
model formatting), `shinri-sat` (incremental solver), and `shinri-core` (term
DAG, sorts). It owns the refinement controller and the model-based consistency
checker. Rationale: parity with `shinri-bv`, clean dependency layering, and it
keeps the eager+refinement world isolated from the lazy `Combiner`.

**Routing & fence (in `shinri-solver`):** detect assertions containing `select`
/ `store` over BV-sorted arrays and dispatch to the `shinri-abv` driver. Refuse,
as `unknown`, any query mixing arrays with EUF, arith, or uninterpreted
index/element sorts — consistent with the QF_BV mixed-theory fence.

**Extension required of `shinri-bv`:** the blaster must support blasting
*additional* subterms into an already-populated SAT solver mid-loop (e.g. a
`select(a, j)` term first introduced by a ROW-2 lemma). This is intra-`check-sat`
on-demand blasting, distinct from the inter-`check-sat` persistence that remains
a non-goal.

## 4. The Abstraction (base formula)

Build a pure-BV **over-approximation** containing **no array axioms**:

- Each syntactically distinct `select(a, i)` term → a **fresh BV variable** `r`
  of the element sort `(_ BitVec j)`. Record the access
  `⟨base-array a, index i, value r⟩`. A `select` over a `store` is abstracted
  like any other read; its relationship to the store is supplied only by ROW
  lemmas (§5).
- `store(a, i, e)` is an array term; it mints no value of its own. Reads on it
  relate to reads on `a` solely through ROW lemmas added on demand.
- Each array equality atom `(= a b)` → a **fresh Boolean** `e_ab`, initially
  unconstrained.
- All non-array BV structure blasts exactly as in QF_BV today (`shinri-bv`).

Because every read value is initially unconstrained, the abstraction has *fewer*
constraints than the original formula. It is therefore a relaxation:
**UNSAT of the abstraction implies UNSAT of the original** (final), while SAT
models may be spurious and are refined away.

## 5. The Refinement Loop & Lemmas

After each SAT model, read concrete values via `Solver::value_of` and check the
array axioms over the **set of accesses present in the current model**. For each
violation, add the corresponding lemma's clauses (lemmas are added **only when
violated** — true lemmas-on-demand).

**5.1 Functional consistency (congruence).**
For two accesses `⟨a, i, r1⟩` and `⟨a, j, r2⟩` on the *same* array term where the
model has `val(i) == val(j)` but `val(r1) != val(r2)`:

> lemma:  `(i = j) → (r1 = r2)`

**5.2 Read-over-write (ROW).**
For a read `select(store(a, i, e), j) = r`:

> `val(i) == val(j)` →  lemma  `(i = j) → (r = e)`            (ROW-1)
> `val(i) != val(j)` →  lemma  `(i ≠ j) → (r = select(a, j))` (ROW-2)

ROW-2 may introduce a previously-unseen read `select(a, j)`; that read is
abstracted (fresh BV var) and blasted into the live solver before the lemma
clause is added.

**5.3 Extensionality.**
For an array equality atom `(= a b)` with Boolean abstraction `e_ab`:

> `e_ab` true, but ∃ accessed index `k` with `val(select(a,k)) != val(select(b,k))`:
>    lemma  `e_ab → (select(a, k) = select(b, k))`
>
> `e_ab` false: introduce a **single** Skolem witness index `w_ab` (once per
>    array-term pair) and the lemma  `¬e_ab → (select(a, w_ab) ≠ select(b, w_ab))`.

`select(a, w_ab)` and `select(b, w_ab)` are abstracted and blasted on demand.

**5.4 Loop control.**
No violation across all checks → the model is real → **SAT** (proceed to model
extraction). Otherwise add the violated lemmas' clauses incrementally, blast any
new reads, and call `SAT.solve()` again. Learned clauses persist across rounds
(the solver stays alive).

## 6. Soundness & Termination

**Soundness.** The abstraction is a relaxation, so UNSAT is preserving (final).
Every emitted lemma is a valid instance of an array axiom (congruence, ROW, or
extensionality), so adding lemmas never removes a real model. A model that
survives the full consistency check satisfies all array axioms over its
accessed-index set and therefore extends to a total array model — so SAT is
sound.

**Termination.** The universe of distinct lemmas is finite: congruence and ROW
range over finitely many syntactic read / index / store triples drawn from the
(fixed) input plus the finitely many reads minted by ROW-2 and extensionality;
extensionality mints exactly **one** witness index per array-term pair, and the
reads it adds are themselves subject to the same finite closure. Each loop
iteration adds at least one previously-absent lemma, so the loop is bounded.

## 7. Model Extraction

- **BV terms:** reuse `shinri-bv`'s `#b`/`#x` value formatter.
- **Array terms:** emit the SMT-LIB array value form — a default element value
  plus the finite set of `(index ↦ value)` points read off the accesses in the
  final consistent model, rendered as nested `store` over an
  `((as const (Array ...)) default)` base. Indices/values are formatted with the
  BV formatter.

## 8. Testing

Mirror the differential-oracle methodology that landed with QF_BV:

- **Differential oracle vs z3:** randomly generate well-sorted QF_ABV formulas
  (store chains, overlapping/aliased indices, array equalities and
  disequalities, mixed BV widths) and compare SAT/UNSAT verdicts against z3.
- **E2E witness checks:** on SAT, validate the extracted model satisfies the
  original assertions.
- **Targeted unit tests** for each lemma kind: functional consistency (§5.1),
  ROW-1 and ROW-2 (§5.2), and both extensionality directions (§5.3); plus
  loop-level tests for UNSAT-finality and termination on adversarial
  alias/anti-alias instances.
- **Fence tests:** queries mixing arrays with EUF/arith/uninterpreted sorts
  return `unknown`.

## 9. Open Sub-Decisions (resolved defaults)

- **Crate vs. module:** new crate `shinri-abv` (parity with `shinri-bv`, clean
  layering). *Chosen.*
- **Lemma minting:** use the live `Solver`'s `new_var` / `add_clause` directly,
  with **no** `push`/`pop` — the loop only ever *adds* constraints within one
  `check-sat`. *Chosen.*
