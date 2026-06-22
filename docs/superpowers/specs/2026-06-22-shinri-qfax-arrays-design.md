# shinri QF_AX — Design (Extensional Arrays, non-extensional baseline via lazy read-over-write)

**shinri's first non-arithmetic theory extension after UF+LIA. Arrays `select`/`store` are added as congruence-eligible builtins so the shared `EqualityEngine` gives congruence for free; a new `shinri-arrays` `TheorySolver` supplies the one thing congruence cannot — the store semantics — by lazily instantiating the two read-over-write (ROW) axioms on demand, as clauses over theory-valid atoms via the existing `Split`/`bind_fresh` machinery. The combiner is generalized from two theory slots (`Combiner<Euf, Arith>`) to three (`Combiner<Euf, Arith, Arrays>`), the long-term shape QF_ALIA will reuse. Extensionality (array-to-array equality) is fenced to a sound `unknown`, exactly like the `lira` gate. Single milestone, sound and complete for QF_AX-without-extensionality.**

- **Date:** 2026-06-22
- **Status:** Approved design — ready for implementation planning
- **Master design spec (north star):** `docs/superpowers/specs/2026-06-18-shinri-design.md`
- **Combination framework spec:** `docs/superpowers/specs/2026-06-19-shinri-theory-design.md` (the `Combiner`, `EqualityEngine`, `TheorySolver`, `AtomRegistry`, `bind_fresh`, `TCheck::Split`)
- **Sibling theory specs:** `docs/superpowers/specs/2026-06-19-shinri-euf-qfuf-design.md` (EUF / congruence closure — arrays builds directly on this); `docs/superpowers/specs/2026-06-22-shinri-uflia-design.md` (the MBTC milestone whose `Split`/`bind_fresh` split-atom routing this reuses).
- **Successor:** QF_ALIA (integer-indexed/-valued arrays) reuses the three-slot combiner and the N-O seam to let arrays cooperate with arith; extensional QF_AX (array equality via the extensionality axiom) is a separate later refinement.

---

## 1. Scope & relationship to the milestone

QF_AX is the SMT-LIB `ArraysEx` theory restricted to an **uninterpreted index sort `I`** and an **uninterpreted element sort `E`**, with `select`/`store` and Boolean combinations of (dis)equalities over `I`, `E`, and `select` terms. Everything is decided over **EUF congruence + read-over-write lemmas**; there is no arithmetic interaction in this milestone.

This is shinri's first theory extension that is **not** another arithmetic flavour. It exercises two new capabilities the codebase has never had:

1. **Builtin function symbols that participate in congruence.** Today congruence fires only on `Op::Uninterpreted` applications. `select`/`store` must be congruence-eligible so the shared `EqualityEngine` delivers `i = j ⟹ select(a,i) = select(a,j)` and `store` congruence for free.
2. **A theory whose entire job is on-demand lemma emission.** Unlike EUF (congruence) or Arith (simplex + entailed equalities), the arrays solver owns no equality or numeric state. It detects `select`-over-`store` configurations and emits ROW axiom instances as clauses, reusing the splitting-on-demand path. This is the second consumer of `TCheck::Split` (after Arith) and the second consumer of fresh-split-atom routing (`bind_fresh`, after MBTC).

### 1.1 Why congruence is necessary but not sufficient (the store-semantics gap)

If `select` and `store` are ordinary function symbols, EUF congruence already gives every *equational* consequence among array reads: equal arrays at equal indices read equal; equal stores stay equal. What congruence does **not** know is the **defining semantics of `store`** — that a write changes exactly one cell:

```
select(store(a, i, e), i) = e                                   (ROW-1, "hit")
i ≠ j ⟹ select(store(a, i, e), j) = select(a, j)               (ROW-2, "miss")
```

These two axioms are the only array-specific inferences QF_AX (without extensionality) requires. Canonical UNSAT witnesses the baseline must reject:

```
select(store(a, i, e), i) ≠ e                                   (ROW-1 violated)
i ≠ j  ∧  select(store(a, i, e), j) ≠ select(a, j)              (ROW-2 violated)
```

and a free-arrangement SAT case (index relationship unconstrained) the baseline must accept by splitting `i = j ∨ i ≠ j` and finding a consistent branch.

### 1.2 Why baseline = non-extensional (the fence)

`ArraysEx` is extensional: `a = b ⟺ ∀k. select(a,k) = select(b,k)`. Deciding array-to-array **equality/disequality** requires the extensionality axiom — on a disequality `a ≠ b`, introducing a fresh witness index `k` with `select(a,k) ≠ select(b,k)` and feeding the selects back through congruence. That is a distinct, subtle, bug-prone mechanism, separable from ROW. Following shinri's existing soundness-first discipline ("anything a theory cannot reason about exactly is refused at atom-registration time"), the baseline **refuses any array-sorted `=`/`distinct` atom** → top-level `unknown`, exactly like the `lira` gate (`crates/shinri-solver/src/tseitin.rs`, `lib.rs`). A query with no array-sorted (dis)equality atom is fully and completely decided.

### 1.3 In scope

- **`shinri-core`:** add `SortNode::Array(SortId /*index*/, SortId /*elem*/)`; add `BuiltinOp::Select` and `BuiltinOp::Store`; sort-check the two ops (`select: (Array I E) × I → E`, `store: (Array I E) × I × E → (Array I E)`).
- **`shinri-parser`:** parse the `(Array I E)` sort and `(select a i)` / `(store a i e)` applications.
- **`shinri-euf`:** make `Select`/`Store` congruence-eligible function symbols in the signature table, so congruence fires on them as on uninterpreted applications.
- **`shinri-arrays`** (new crate): a `TheorySolver` that lazily instantiates ROW-1/ROW-2 on demand via `TCheck::Split`, introducing fresh `select(a,j)` terms through `bind_fresh`.
- **`shinri-theory`:** generalize `Combiner<E, A>` to `Combiner<E, A, R>` (third arrays slot); extend atom-owner classification/routing to `{Euf, Arith, Arrays}`; thread the third solver through every phase.
- **`shinri-solver`:** instantiate `Combiner<Euf, Arith, Arrays>`; add the array-equality extensionality fence; support `get-value` on `select`/index/element terms.
- Full soundness-first test regime: unit, property, EUF-congruence regression, combiner non-regression, e2e witnesses, differential oracle vs z3 (+ cvc5).

### 1.4 Explicitly out of scope (unchanged or new fences)

- **Extensionality** — array-sorted `=`/`distinct` fenced to `unknown` (§1.2). Extensional QF_AX is a later refinement.
- **Arithmetic indices/elements (QF_ALIA / QF_AUFLIA)** — a separate later milestone that reuses the three-slot combiner and the N-O seam. Mixed Int/Real (`lira`) fence is unchanged.
- **Constant arrays (`(as const ...)`)**, arrays-of-arrays beyond what `(Array I E)` with uninterpreted `E` permits, nonlinear, difference-logic specialization, eager array reasoning.
- **`get-value` on array-sorted terms** — deferred; `get-value` on `select`/index/element terms is supported. Sat/unsat verdicts are always sound regardless.
- **Proof/certificate emission for ROW lemmas** — consistent with the QF_LIA B2 and MBTC decisions that on-demand lemmas/splits are not certified.

---

## 2. The foundation layer (core / parser / EUF)

### 2.1 `shinri-core` — sorts and ops

- `SortNode::Array(SortId, SortId)` — interned index and element sorts. Reuses the existing sort-interning machinery (the variant was reserved in `sort.rs`: *"(Array I E)) are reserved for Phase 3 and added as variants then"*).
- `BuiltinOp::Select`, `BuiltinOp::Store` (reserved in `term.rs`).
- Sort-checking: `select(arr, idx)` requires `arr : (Array I E)` and `idx : I`, yields `E`; `store(arr, idx, elt)` requires `arr : (Array I E)`, `idx : I`, `elt : E`, yields `(Array I E)`. Sort errors surface through the existing `SortError` path.

### 2.2 `shinri-parser`

Parse the parameterized sort `(Array I E)` (resolving `I`, `E` to interned `SortId`s) and the `(select a i)` / `(store a i e)` applications to `BuiltinOp::Select`/`Store` nodes. No new command surface — `declare-const`/`declare-fun` of array sort, `assert`, `check-sat`, `get-value` already exist.

### 2.3 `shinri-euf` — congruence-eligible builtins

Extend the EUF signature table / congruence trigger so an application headed by `BuiltinOp::Select` or `BuiltinOp::Store` is treated like an `Op::Uninterpreted` application: it gets an e-node, joins the signature table, and congruence merges two such applications when their (head, args-up-to-congruence) match. This is the single change that delivers all equational array consequences; the arrays solver only adds store semantics on top.

---

## 3. `shinri-arrays` — lazy read-over-write lemma-on-demand

### 3.1 State

The solver owns **no equality or value state** — all congruence lives in the shared `EqualityEngine`. It maintains only bookkeeping needed to avoid re-emitting lemmas: a backtrackable record (via the standard `UndoLog` discipline, `push`/`pop`) of which `(select-term, store-term)` ROW instances have already been emitted at the current level.

### 3.2 The lazy trigger (in `check`)

At `check(effort)`:

1. **Enumerate candidates.** For each `select(t, j)` term registered with the theory, find every `store(a, i, e)` term such that `t` and `store(a,i,e)` are **congruent in the engine** (the read sees that write).
2. **Consult the index arrangement** of `i` vs `j` in the engine and emit the governing lemma if not already satisfied/emitted:
   - `i = j` known → **ROW-1**: force `select(store(a,i,e), j) = e` (a unit-clause split; the read equals the written value).
   - `i ≠ j` known → **ROW-2 conclusion**: force `select(store(a,i,e), j) = select(a, j)`. Generating this introduces a fresh `select(a, j)` term routed through `bind_fresh` (classified to EUF for congruence).
   - **undecided** → emit **ROW-2 as a split**: the two-atom clause `i = j  ∨  select(store(a,i,e), j) = select(a, j)`, letting the SAT search branch the index arrangement. (The `i = j` branch then triggers ROW-1 on the next round; the `i ≠ j` branch is the conclusion above.)
3. **Throttle:** emit **at most one lemma per `check`** (lemma-on-demand discipline — avoids flooding the SAT solver; the search re-invokes `check` after assimilating each lemma).
4. **Fixpoint:** return `TCheck::Sat` only when **every** `select`-over-`store` candidate already has its governing lemma satisfied — i.e. every read sees its write correctly. Otherwise return `TCheck::Split` with the one new lemma clause.

Store **chains** (`select(store(store(a,i,e),k,d), j)`) are handled transitively: each round peels one `store` layer (the outer write resolves to either its element or a `select` of the inner array), so the fixpoint walks the chain one lemma at a time.

### 3.3 Soundness & completeness

- **Soundness.** Every emitted clause is a ground instance of a valid `ArraysEx` axiom (ROW-1 or ROW-2). The combiner never *asserts* an arrangement — it splits and lets DPLL(T) decide — so the search only ever learns valid lemmas. Identical discipline to MBTC's trichotomy split.
- **Completeness (QF_AX without extensionality).** With extensionality fenced, the only array-specific inferences QF_AX needs are ROW-1/ROW-2 over the finitely many `select`/`store` terms present. Instantiating both forms to the §3.2 fixpoint, on top of EUF congruence, is the standard complete decision procedure for the non-extensional fragment.

### 3.4 `TheorySolver` implementation surface

- `new_var` / `assert`: register `select`/`store`/index atoms the theory must watch; no eager work.
- `check`: the §3.2 trigger; the only place lemmas are produced.
- `explain`: resolve the antecedents of any equality the theory derived (the index relation + the store/select congruences cited in a lemma), in the `EqLeaf` vocabulary the combiner expands.
- `propagate`: none in the baseline (lemmas flow through `check`/`Split`, not theory propagation) — YAGNI; the seam stays available for a later optimization pass.
- N-O equality-exchange seam (`shared_arith_terms`, `entailed_equalities`, `consume_interface_equality`): **all default no-ops.** Arrays is a **congruence-only** N-O participant — it shares the one `EqualityEngine` and contributes nothing arithmetic. (This is exactly the seam QF_ALIA will fill later.)
- `model`: contribute `select` values already pinned in the engine to the `ModelBuilder`; array-sorted term values are deferred (§1.4).
- `push`/`pop`: backtrack the emitted-lemma bookkeeping (§3.1).

---

## 4. Combiner generalization — `Combiner<E, A>` → `Combiner<E, A, R>`

The combiner is today a fixed-struct, enum-routed aggregator over two `TheorySolver`s (`crates/shinri-theory/src/combiner.rs`). The generalization adds a third type parameter `R: TheorySolver` (the arrays slot):

- **Routing enum.** Extend the atom-owner classification from `{Euf, Arith}` to `{Euf, Arith, Arrays}`; the `AtomRegistry` classifies array atoms (`select`-rooted equalities, `store` terms) to the third theory.
- **Phase threading.** Thread the third solver through every phase already threaded for two: `new_var`, `assert`, `propagate`, `check`, `explain`, `model`, `push`, `pop`, and the N-O equality-exchange fixpoint. Arrays participates in `check` (lemma emission) and `explain`; its N-O seam methods are no-ops (§3.4), so the equality-exchange loop is unchanged in shape.
- **Split lifting.** `TCheck::Split` from the arrays slot lifts to `TheoryResult::SplitAtoms` through the same path Arith uses; fresh atoms route via `bind_fresh`.
- **Existing callers / instantiation.** `Combiner<Euf, Arith>` becomes `Combiner<Euf, Arith, EmptyTheory>` for any caller not yet array-aware. **The production `shinri-solver` always builds the full three-slot `Combiner<Euf, Arith, Arrays>`** — it already supports QF_UFLIA, so it must keep the Arith slot live; on a pure QF_AX query the Arith slot simply sees no arith atoms. The `EmptyTheory`-in-a-slot variants (`Combiner<Euf, EmptyTheory, Arrays>`, etc.) are what the type system permits and are used in focused unit tests, not the production wiring. **The generalization itself must not regress** QF_UF / QF_LIA / QF_UFLIA / QF_UFLRA — this is the milestone's headline risk and is covered by re-running their oracle tests.

**Why third slot, not fold-into-EUF.** Keeps the arrays lemma logic isolated and independently testable, and is precisely the shape QF_ALIA requires (arrays cooperating with arith through the same N-O seam) — no second migration later.

---

## 5. Solver wiring, fences, and model

- **Theory instantiation.** `shinri-solver` builds `Combiner<Euf, Arith, Arrays>` as its `Theory`.
- **Extensionality fence.** In atom registration (`tseitin.rs` / `lib.rs`), any `Eq`/`Distinct` whose operands are **array-sorted** sets `refused = true` → top-level `unknown`, mirroring the `lira` gate. Select/index/element (dis)equalities are **not** fenced (they are the supported core of QF_AX). A query with no array-sorted (dis)equality atom is fully decided.
- **Model.** `get-value` on `select`-rooted, index, and element terms works via the existing `ModelBuilder`. `get-value` on an **array-sorted term** returns `unsupported`/`unknown` (deferred, §1.4). Sat/unsat verdicts are always sound.

---

## 6. Test & DoD regime (soundness-first, matching established pattern)

- **Unit (`shinri-arrays`):** ROW-1 hit; ROW-2 miss; undecided-index split; store-chain peeling; no-spurious-lemma fixpoint (terminates at `Sat` with no extra lemmas).
- **Property:** random QF_AX formulas — the solver verdict is never `sat` on a ground-checkable UNSAT; emitted-lemma count stays bounded (no flooding).
- **EUF-congruence regression:** `select`/`store` congruence (`i=j ⟹ select(a,i)=select(a,j)`; `store` congruence) fires through the shared engine.
- **Combiner non-regression:** the three-slot generalization keeps the QF_UF / QF_LIA / QF_UFLIA / QF_UFLRA oracle tests green (headline risk).
- **E2E witnesses (`shinri-solver`):** the canonical triples — `select(store(a,i,e),i) ≠ e` (UNSAT); `i≠j ∧ select(store(a,i,e),j) ≠ select(a,j)` (UNSAT); a free-arrangement SAT case — mirroring the MBTC e2e commit.
- **Differential oracle:** a QF_AX corpus vs **z3** (+ **cvc5**), the same harness as the UFLIA milestone. **Fence check:** array-equality instances return `unknown` (never a wrong `sat`/`unsat`).
- **Definition of Done:** all above green; extensionality instances fenced to `unknown`; no regression across existing theories; `cargo test` workspace-clean.

### Implementation / commit shape (rough granularity, matching git history)

1. `core` — `SortNode::Array`, `BuiltinOp::Select/Store`, sort-checking.
2. `parser` — `(Array I E)` sort + `select`/`store` parsing.
3. `euf` — `Select`/`Store` congruence-eligible.
4. `shinri-arrays` — the ROW lemma-on-demand `TheorySolver` (+ unit/property tests).
5. `theory` — three-slot combiner generalization (+ non-regression run).
6. `solver` — `Combiner<Euf, Arith, Arrays>` wiring + extensionality fence + `get-value`.
7. `tests/oracle` — e2e witnesses + QF_AX differential vs z3/cvc5.
