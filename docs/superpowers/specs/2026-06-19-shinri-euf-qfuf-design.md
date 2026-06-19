# shinri — EUF Congruence Closure → First Runnable QF_UF Solver

**Design Specification**

- **Date:** 2026-06-19
- **Status:** Approved design — ready for implementation planning
- **Parent spec:** `2026-06-18-shinri-design.md` (this realises Phase-1 build-order step 3, "DPLL(T) glue + Theory trait → EUF: first runnable solver, QF_UF")
- **Scope of this document:** The EUF theory solver, the substrate and SAT-incrementality changes it requires, and a minimal embeddable `shinri-solver` that makes QF_UF queries solvable end-to-end.

---

## 1. Motivation & Context

The workspace today has a complete, tested `shinri-num`, `shinri-core`, and `shinri-sat` (a CDCL engine with a working `Theory` seam), plus a complete Nelson–Oppen **combination framework** in `shinri-theory` (`Combiner`, `EqualityEngine`, `AtomRegistry`, purification, `CertLog`, model assembly, propagate/check fixpoint loops).

What is missing is any **concrete theory solver**. The only `TheorySolver` implementation in the tree is a test stub (`NullTheory`). Consequently:

- Nothing runs end-to-end — the SAT engine's theory seam has nothing real plugged into it.
- The combination framework has never been exercised by a real theory; its `#[ignore]`d oracle test (`crates/shinri-theory/tests/oracle.rs`) is annotated *"activates when `Combiner<Euf, Arith>` exists."*

The parent spec's build order makes EUF the immediate next step: it is the gating piece that turns tested components into a solver that answers `sat`/`unsat`, it is the first real consumer that validates the combination plumbing, and it is the shared equality hub every later theory builds on. This cycle delivers **EUF + a runnable QF_UF solver**.

## 2. Goals & Non-Goals

### Goals
- A correct, backtrackable **EUF (congruence closure) theory solver** as a new `shinri-euf` crate implementing `shinri_theory::TheorySolver`, built on the existing shared `EqualityEngine`.
- Wire it through the existing `Combiner` as `Combiner<Euf, EmptyTheory>` and into `shinri_sat::Solver`.
- A **minimal embeddable `shinri-solver` crate**: build a term DAG, assert Boolean combinations of EUF atoms, `check-sat`, `get-model`, `get-value`.
- **Sound incremental `push`/`pop`** at the solver API (see §7).
- The full soundness-first test regime for the new code (unit, property, end-to-end, differential oracle).

### Non-Goals (deferred)
- Any arithmetic theory (difference logic, simplex) — the `Arith` slot is filled by `EmptyTheory`.
- An SMT-LIB 2 parser / CLI binary (`shinri-parser`, `shinri-cli`). Formulas are asserted via the library API.
- Proof *emission* (Alethe/LRAT). The `CertLog` / `ProofSink` *seams* remain wired; emission stays Phase-2.
- Theory-propagation completeness beyond the cheap, high-value cases (see §5.6); the architecture allows incremental addition.
- The Lookup-table timestamp optimisation (spec §6.3) — correctness-first via an `UndoLog`; the optimisation is a later performance pass.

## 3. Architecture Overview

```
shinri-num    (existing)
shinri-core   (existing)            UndoLog, Context, Lit/Var, TheoryJust, ProofSink
shinri-sat    (existing + change)   +Solver::with_theory, +theory_mut, theory-preserving rebuild (§7)
shinri-theory (existing + change)   +EmptyTheory; EqJust::Congruence extended to n-ary (§4)
shinri-euf    (NEW)                 Euf: TheorySolver — e-graph build + congruence driver
shinri-solver (NEW)                 embeddable Solver API: declare/assert/check-sat/get-model

dep graph:  num ← core ← sat ← theory ← euf ← solver
```

QF_UF runs as `shinri_sat::Solver<Combiner<Euf, EmptyTheory>, NoProof, Vmtf>`.

The four units and their boundaries:

| Unit | Responsibility | Depends on |
|---|---|---|
| `EqJust` n-ary extension (in `shinri-theory`) | Represent & explain n-ary congruence edges minimally | core |
| `EmptyTheory` (in `shinri-theory`) | No-op `TheorySolver` to fill the `Arith` Combiner slot | theory |
| `shinri-euf` | Congruence closure: e-graph construction, signature/UseList driver, conflict packaging, backtracking, model | core, theory |
| `shinri-sat` change | Inject/access the theory; preserve theory state across `pop` | core |
| `shinri-solver` | Term DAG ownership, Tseitin CNF, wiring, model/value extraction, incremental scopes | core, sat, theory, euf |

## 4. Substrate change: n-ary congruence justification (`shinri-theory`)

`EqJust::Congruence(ENodeId, ENodeId)` currently carries exactly **one** argument pair — correct for unary `f(x) = f(y)`, but an n-ary congruence `f(a₁..aₙ) = f(b₁..bₙ)` is justified by *all* pairs `(aᵢ, bᵢ)`. `expand_edge` must recurse over each.

**Design:** keep `EqJust` `Copy` by storing the pairs in an arena owned by `EqualityEngine`; the edge label references a range.

```rust
// types.rs
pub enum EqJust {
    Asserted(Lit),
    Congruence(CongRef),          // was Congruence(ENodeId, ENodeId)
    Interface(TheoryJust),
    Definitional,
}
#[derive(Clone, Copy, …)]
pub struct CongRef { start: u32, len: u32 }   // range into EqualityEngine.cong_pairs
```

```rust
// eq_engine.rs additions
cong_pairs: Vec<(ENodeId, ENodeId)>,     // arena of argument pairs
cong_undo:  UndoLog<usize>,              // truncate length on pop

/// Merge a≡b justified by congruence over the given argument pairs.
pub fn merge_congruence(&mut self, a: ENodeId, b: ENodeId,
                        pairs: &[(ENodeId, ENodeId)]) -> Result<(), EqConflict>;
```

`expand_edge` for `Congruence(r)` iterates `self.cong_pairs[r]` and calls `self.explain(aᵢ, bᵢ, out)` per pair (the existing recursion, generalised from one pair to a slice). The arena is backtracked: `merge_congruence` records the pre-insert length on `cong_undo`; `pop` truncates `cong_pairs` to that length (the merge's forest edge is already detached by the existing `forest_undo`, so the range becomes unreferenced).

This is additive and contained: the existing unary test generalises to the slice form; `Definitional`/`Asserted`/`Interface` are unchanged; the proof-forest, NCA, and minimality logic are untouched.

## 5. `shinri-euf` — the EUF theory solver

EUF adds the congruence machinery the shared engine deliberately lacks. The `EqualityEngine` already provides `intern`, `find`, `are_equal`, `merge`, `merge_congruence`, `assert_diseq`, `explain` (minimal, NCA-based), `drain_merges`, `push`/`pop`, and disequality-conflict detection. EUF owns term structure, the congruence driver, predicate encoding, and its own backtrackable indices.

```rust
pub struct Euf {
    apps: Vec<AppNode>,                 // app e-node id → (op, [arg ENodeId])
    use_list: Vec<Vec<AppId>>,          // per representative ENodeId
    lookup: FxHashMap<Signature, AppId>,// (op, [rep(arg)]) → canonical app
    pending: Vec<(ENodeId, ENodeId, EqJust)>, // congruence work-queue
    true_node: Option<ENodeId>, false_node: Option<ENodeId>, // predicate sentinels
    eqs_by_var: Vec<EqAtom>,            // var → asserted-atom semantics
    undo: UndoLog<EufUndo>,             // lookup inserts / use_list growth
    level: usize,
}
impl TheorySolver for Euf { const THEORY_ID: u16 = 1; … }   // EmptyTheory::THEORY_ID = 0 (must differ)
```

### 5.1 E-graph construction (`new_var`, level 0)
For each registered atom, recursively `intern` every subterm. Each function application is recorded as `(op, [arg e-nodes])`, added to the `use_list` of each argument's representative and to `lookup` under its current signature; an initial signature collision fires an immediate congruence merge. All atoms are registered up front at level 0 (the `shinri-solver` wiring; `AtomRegistry` is append-only per spec §6.5), so e-node and structure creation are permanent and never backtracked — only *merges* are.

### 5.2 Atom semantics (`assert(lit)`)
Decode the atom term behind `lit.var()`:
- `(= s t)`: positive → `merge(s, t, Asserted(lit))`; negative → `assert_diseq(s, t, Asserted(lit))`.
- `(distinct s t)` (binary): positive → `assert_diseq(s, t, Asserted(lit))`; negative → `merge(s, t, Asserted(lit))` (it is exactly `¬(s = t)`'s dual). EUF only ever sees **binary** `distinct`: n-ary `(distinct t₁..tₙ)` is expanded into the conjunction of pairwise binary `(distinct tᵢ tⱼ)` atoms at the encoding stage (§6), so both polarities are handled uniformly and there is no awkward "at least two equal" disjunction to assert.
- uninterpreted **predicate** application `p(args)` (Bool-sorted): positive → `merge(node(p(args)), ⊤)`; negative → `merge(node(p(args)), ⊥)`. `⊤`/`⊥` are interned once and `assert_diseq(⊤, ⊥, Definitional)` is established at level 0.

After any merge, run the congruence driver (§5.3) to a fixpoint. `assert` is infallible at the SAT seam, so a detected conflict is returned as `Some(Vec<EqLeaf>)` (the `Combiner` stashes it in `pending_conflict` and surfaces it on the next `propagate`, matching the existing bridge).

### 5.3 Congruence driver
Classic Nieuwenhuis–Oliveras closure over the shared engine:
1. Seed `pending` with the just-asserted equality.
2. While `pending` non-empty: pop `(a, b, just)`; if `find(a) ≠ find(b)`, capture the smaller class's `use_list`, then `merge(a, b, just)` (or `merge_congruence` when `just` is a congruence). On `Err(EqConflict)`, package and return (§5.4).
3. For each app in the captured use-list, recompute its signature under the new representatives; on a `lookup` collision with a different app, enqueue the congruent pair with `Congruence` justification carrying their argument pairs. Update `lookup`/`use_list` (recording undo entries).
4. Repeat to fixpoint.

Closure runs synchronously inside `assert`/`check`, so the class is fully closed before returning. The `Combiner`'s own loop additionally drains `MergeEvent`s for combination progress; for QF_UF (`EmptyTheory` in the other slot) those merges are harmless no-ops to the other theory.

### 5.4 Conflict packaging
When `merge` rejects uniting a known-disequal pair, `EqConflict { a, b, diseq }` gives the offending pair and the disequality's justification. EUF returns the antecedent leaves: `explain(a, b)` (why they became equal) **plus** the `diseq` leaf. The `Combiner` resolves any `Interface` leaves to a fixpoint and negates the result into the SAT conflict clause; `CertLog` records it for the dev-gated structural re-check.

### 5.5 Explanation (`explain(tag, exp)`)
EUF produces explanations through two paths, both already accommodated by `EqualityEngine`/`Combiner`:
- Congruence edges are labelled `EqJust::Congruence(range)`; `EqualityEngine::explain` recurses through them automatically (§4) — EUF need not be re-entered for pure-EUF congruence chains.
- If EUF emits theory propagations (§5.6) it tags them `TheoryJust{theory: Euf::THEORY_ID, tag}`; `Euf::explain(tag)` reconstructs the antecedent equality/disequality via `eq.explain` into the `Explainer`.

### 5.6 Theory propagation (cheap subset)
Exhaustive EUF propagation is valuable but optional for correctness. Phase-1 implements the cheap, high-value cases: when two terms become equal (or disequal) and a registered atom `(= a b)` is still unassigned, propagate its forced polarity with a `TheoryJust` token. The fixpoint loop and lazy `explain` are already provided by the `Combiner`. Broader propagation can be added behind the same interface without structural change.

### 5.7 Backtracking & model
- `push`/`pop` (absolute target levels, per the `TheorySolver` contract) drive EUF's `UndoLog` for `lookup` inserts and `use_list` growth, alongside the engine's own `push`/`pop` the `Combiner` calls. Permanent level-0 structure (e-nodes, initial use-lists) is never rolled back.
- `model(ModelBuilder)`: assign each uninterpreted-sort congruence class a distinct abstract domain element (`ModelVal::Elem(sort, k)`), consistent across the class; predicate apps take `Bool` per their `⊤`/`⊥` class. The `Combiner::build_model` seam check then holds trivially (the `Arith` side is empty).

## 6. `shinri-solver` — embeddable entry point

A thin library crate; the embeddable `Solver` API the parent spec calls the top-level crate, kept minimal here (no parser).

```rust
pub struct Solver { /* owns Context construction inputs + the SAT solver */ }
impl Solver {
    pub fn declare_sort(&mut self, name: &str) -> SortId;
    pub fn declare_fun(&mut self, name: &str, params: &[SortId], result: SortId) -> SymbolId;
    // term builders are reused from Context (mk_app/mk_eq/…)
    pub fn assert(&mut self, formula: TermId);
    pub fn check_sat(&mut self) -> SolveOutcome;       // Sat | Unsat | Unknown
    pub fn get_model(&mut self) -> Model;              // TermId → ModelVal
    pub fn get_value(&mut self, t: TermId) -> Option<ModelVal>;
    pub fn push(&mut self); pub fn pop(&mut self, n: usize);   // §7
}
```

**Internal flow for one `check_sat`:**
1. Build the `Context` (declarations + assertion term trees), hand it to `Combiner::with_context`, wrap in `Solver::with_theory` (§7).
2. **Tseitin CNF pass**: walk each Bool-sorted assertion. Boolean connectives (`Not/And/Or/Implies/Xor/Ite`, and `Eq`/`Distinct` over `Bool`) are encoded into fresh SAT vars + clauses; n-ary `(distinct …)` over an uninterpreted sort is first expanded into the conjunction of pairwise binary `(distinct tᵢ tⱼ)` atoms (§5.2). **Theory atoms** (the leaves `classify` routes to EUF) get one SAT `Var` each via `new_var`, registered into the `Combiner` with `theory_mut().register_atom(v, atom)`. A `TermId → Var` cache ensures shared subterms share a var.
3. `solve()` runs CDCL(T): SAT assigns atoms → `Combiner.assert` → `Euf.assert` (merge/diseq + congruence) → propagate/`check(Full)` fixpoint → conflicts become clauses and drive backjumping.
4. On `Sat`, `Combiner::build_model()` → public `Model` keyed by `TermId`. On a refused/unsupported atom (from `classify`), return `Unknown` — never a guess (parent spec §10).

## 7. SAT incrementality: sound `push`/`pop` (`shinri-sat` change)

**Problem.** `Solver::new` builds `theory: T::default()`, and `rebuild()` (on `pop`) does `self.theory = T::default()` then replays only `new_var(v)` — which carries no atom. A stateful `Combiner` cannot be injected, accessed, or reconstructed this way, so `push`/`pop` is currently unsound for any real theory.

**Changes (additive + one rebuild fix):**

1. **Injection/access:**
   - `Solver::with_theory(config, theory: T) -> Solver<T,P,H>` — construct around a pre-built `Combiner::with_context(ctx)`.
   - `Solver::theory_mut(&mut self) -> &mut T` and `theory(&self) -> &T` — so `shinri-solver` can call `register_atom`/`build_model`.

2. **Theory-preserving rebuild.** The theory is no longer reset to `default()` on `pop`. Instead:
   - `Solver::push()` calls `self.theory.push()` (one theory scope per user scope) in addition to recording the clause-scope mark.
   - `Solver::pop(n)` calls `self.theory.pop(n)` (the `Combiner` supports absolute-level pop and already wires `eq`/`euf`/`arith` underneath), then rebuilds **only the Boolean derived state** (assign/trail/db/watches/learnts) from the surviving input clauses.
   - Rebuild re-installs surviving clauses in a **theory-silent** mode: re-propagated units do **not** re-invoke `theory.assert`, because the theory retained exactly the surviving scopes' facts via its own `push`/`pop`. This avoids double-application while keeping the SAT Boolean state and the theory state consistent.

**Invariant that makes this sound.** Between `solve()` calls the decision level is 0 and the theory level equals the user-scope count; the theory holds exactly the surviving scopes' level-0 facts. Search-time `theory.push`/`pop` (per decision level) are balanced 1:1 with decision levels and return to the user-scope base on exit, so user-scope `pop(n)` removes precisely the popped scopes' facts. New clauses added after a pop assert to the theory normally (no rebuild on `add_clause`). This is the same conservative philosophy as the existing SAT rebuild (learnts are still dropped on `pop`).

## 8. Data Flow (end-to-end, one query)

```
declare_* ; assert(φ)*                      (build Context term DAG)
  └─ Combiner::with_context(ctx) ─ Solver::with_theory ─────────────┐
check_sat:                                                          │
  Tseitin(φ) ─ per atom: v=new_var(); theory_mut().register_atom    │
            └─ add_clause*(CNF)                                     │
  solve():  pick/propagate ─ Combiner.assert ─ Euf.assert           │
             ├ merge/diseq + congruence driver (fixpoint)           │
             ├ conflict? → EqLeaf set → Combiner negates → clause → backjump
             └ all assigned → check(Full) → Sat                     │
  Sat → Combiner.build_model() → Model[TermId]  ◀─────────────────────┘
  unsupported atom → Unknown
```

## 9. Testing & Verification (soundness-first, parent spec §11)

1. **`shinri-theory` (substrate):** extend the existing `EqJust::Congruence` tests to the n-ary slice form; assert minimality (no edges above the NCA), arena backtracking on `pop`.
2. **`shinri-euf` unit:** `a=b ⊢ f(a)=f(b)`; n-ary congruence `a=c ∧ b=d ⊢ g(a,b)=g(c,d)`; transitive chains; diseq conflict (`a=b ∧ f(a)≠f(b)`); predicate `⊤/⊥` (`p(a) ∧ ¬p(b) ∧ a=b` → conflict); `push`/`pop` restore; `explain` correctness + minimality.
3. **Property tests (`proptest`):** every EUF conflict clause is genuinely EUF-inconsistent (independently re-checked via `CertLog::recheck`); every returned model satisfies every asserted literal.
4. **`shinri-solver` end-to-end (`tests/`):** classic unsat (`x=y ∧ f(x)≠f(y)`), sat-with-model, predicate congruence, deep transitivity, and an **incremental** sequence (`assert; push; assert; check; pop; check`) exercising §7.
5. **Differential oracle:** enable the `#[ignore]`d `Combiner<Euf, _>` harness and `shinri-solver` vs `z3`/`easy-smt` on random well-typed QF_UF. Any `sat`/`unsat` disagreement is a P0 bug; `unknown` is never a failure.
6. **CI:** unchanged gates (`nextest`, `deny check`, `clippy -D warnings`, `fmt --check`) extended to the two new crates; mutation testing (`cargo-mutants`) on the congruence driver and conflict packaging.

## 10. Risks & Mitigations

1. **Disequality-edge / congruence soundness** — the classic EUF failure mode. Mitigation: `CertLog` re-check on every conflict, property tests that re-validate conflicts, differential oracle from day one.
2. **Incremental `push`/`pop` (§7) is genuinely the riskiest surface** — it touches the SAT incrementality path and relies on the theory-state invariant. Mitigation: explicit invariant (§7), dedicated incremental end-to-end tests, and the conservative "drop learnts, theory-silent re-install" design that minimises moving parts. If the invariant proves fragile under search-time push/pop accounting, fall back to full theory reconstruction from a registration log (a recorded `(v, atom)` list replayed into a fresh `Combiner`).
3. **Explanation minimality** drives clause quality; non-minimal cores hurt performance, not soundness. The engine's NCA-based `explain` already yields minimal sets; the n-ary extension preserves it.
4. **Predicate / `distinct` encoding corner cases** — handled structurally: n-ary `distinct` is lowered to pairwise binary atoms at encoding time (§5.2/§6), so EUF sees only binary `=`/`≠` in both polarities; any genuinely unsupported construct is refused at classify time (→ `unknown`), keeping soundness existential.
5. **Scope creep into substrate + SAT** — both were explicitly chosen over the minimal alternatives; bounded by the non-goals (§2) and the deferred optimisations.

## 11. Deliverable

A sound QF_UF solver, runnable end-to-end via the `shinri-solver` library API with `assert`, incremental `push`/`pop`, `check-sat`, `get-model`/`get-value`; a new `shinri-euf` congruence-closure theory solver; the n-ary congruence extension and `EmptyTheory` in `shinri-theory`; the theory-injection + theory-preserving-rebuild changes in `shinri-sat`; and the full unit/property/end-to-end/differential test regime — the first time the combination framework and SAT theory seam are exercised by a real theory.
