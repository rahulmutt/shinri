# shinri-arith QF_LIA — Plan B1 Design (baseline: bounds + branch-and-bound, cuts OFF)

**A sound, complete, terminating decision procedure for pure QF_LIA using only the a-priori finite bound and splitting-on-demand branch-and-bound — the known-correct Stage-A reference that Plan B2's Gomory cuts will be differentially validated against.**

- **Date:** 2026-06-21
- **Status:** Approved design — ready for implementation planning
- **Master design spec:** `docs/superpowers/specs/2026-06-20-shinri-arith-lia-design.md` (the approved QF_LIA milestone design; this document scopes the **baseline** subset of it)
- **Predecessor plan:** `docs/superpowers/plans/2026-06-20-shinri-lia-splitting-infra.md` (Plan A — splitting-on-demand *infrastructure*, merged: `TheoryResult::SplitAtoms`, `Theory::bind_fresh`, the solver two-phase mint-and-learn arm, `TCheck::Split`, and the `Combiner` lift, all validated by stub theories)
- **Successor:** Plan B2 (Gomory/GMI cuts) — its own brainstorm + spec + plan, out of scope here

---

## 1. Scope & relationship to the milestone

The QF_LIA milestone (master spec §1.1) rests on one central soundness decision: **completeness and termination depend only on the a-priori bound; cuts are pure optimization.** That decision dictates a two-stage build, and the milestone is therefore split into two implementation plans:

- **Plan B1 (this document):** the complete, terminating baseline with **cuts disabled** — a-priori bounds + branch-and-bound + integer-disequality splits + integer models, validated against z3 + cvc5. This is the spec's "Stage A — baseline: known-correct reference procedure."
- **Plan B2 (later):** GMI cut generation as an optimization layer, producing *identical* sat/unsat verdicts to B1 and the external oracles ("Stage B"). A buggy cut cannot hide because it is checked against a procedure that does not use cuts.

Plan A delivered the cross-crate *mechanism* (the splitting seam) validated by stubs. Plan B1 makes **`shinri-arith` actually produce** real branch/diseq splits and decide pure QF_LIA.

### 1.1 In scope (B1)

1. Mutable term-construction seam so `Arith` can build branch/diseq atom `TermId`s mid-search (master spec §2 — Plan A's flagged first B-task).
2. Narrowing the Int-sort fence to admit **pure-Int** atoms while still fencing **mixed** Int/Real (master spec §3.1).
3. A-priori finite bound `M` seeded as ordinary axiomatic bounds (master spec §3.2).
4. Fractional scan + branch `Split` in `check(Full)` (master spec §4).
5. Integer disequalities via eager `lower()` rewrite to `(or Lt Gt)`; integer strictness handled by reusing the existing δ encoding (master spec §5, corrected to the actual codebase — see §3.5; tightening deferred to B2).
6. Integer model emission (master spec §7).
7. Two-stage-ready differential oracle against **z3 + cvc5** + the unit/property soundness spine (master spec §9).

### 1.2 Explicitly out of scope (deferred to B2)

GMI cut generation (`cuts.rs`), per-node and global cut budgets, the cuts-on differential re-run, and the debug cut re-derivation check. B1 must be complete and terminating **with no cuts at all**, so these are purely additive in B2.

Also unchanged from the milestone fences (master spec §1 decision 5): QF_UFLIA combination and mixed QF_LIRA remain fenced to `unknown`; QF_LRA / QF_UFLRA paths are untouched.

---

## 2. Architecture overview

The QF_LRA Dutertre–de Moura simplex (`shinri-arith`) already solves the **real relaxation**. B1 adds integer search *on top of* it: after the simplex reaches a feasible real assignment, an integer layer either accepts it (all Int vars integral), or emits a theory-valid split clause that the SAT solver case-splits on — driving the search via the Plan A splitting seam. Nothing in the relaxation engine changes; the integer layer is additive.

```
SAT solver (DPLL(T))
   │  assigns atom literals
   ▼
Combiner (Theory impl)  ──TheoryResult::SplitAtoms──▶ solver mints Vars, calls bind_fresh
   │  TCheck::Split lift                                    │
   ▼                                                        ▼
Arith::check(Full)                                   Combiner::bind_fresh → Arith::new_var
   1. simplex → feasible real assignment                (registers atom→Owner::Arith, encodes bound)
   2. scan Int vars for fractional value
   3. all Int vars integral?  → Sat   |  non-integral? → build (x≤⌊v⌋),(x≥⌈v⌉) → TCheck::Split

(integer a≠b is handled earlier/eagerly: lower() → (or (Lt a b) (Gt a b)),
 a Boolean clause the SAT solver case-splits — not via TCheck::Split; see §3.5)
```

Each unit keeps one responsibility: `bounds.rs` owns bound storage + the a-priori `M`; `branch.rs` (new) owns branch-var selection and `Split`-clause construction; `simplex.rs`/`lib.rs` own the relaxation loop and the fractional-scan hand-off; `model.rs` owns integral emission; `atom.rs`/`normalize.rs` own admission/fencing.

---

## 3. Components

### 3.1 Mutable term-construction seam

**Change:** `TheoryCtx.terms: &'a Context` → `&'a mut Context` (`crates/shinri-theory/src/solver_trait.rs`). Update every `TheoryCtx { terms: &self.terms, .. }` construction site in `crates/shinri-theory/src/combiner.rs` to `&mut self.terms`.

**Why full `&mut` (not a narrower side-channel):** `Arith::check` must construct branch atoms `(x ≤ ⌊v⌋)`, `(x ≥ ⌈v⌉)` and diseq-split atoms `(a ≤ b−1)`, `(a ≥ b+1)` on the fly via `Context::mk_app` / `mk_numeral` (each needs `&mut Context`). The borrow-split (§5.5) pattern already isolates `terms` from `eq`/`atoms`, the `Combiner` owns `terms: Context` by value, and a narrower builder seam would awkwardly split term-reads across two fields. The rejected alternative was a scoped builder passed only into `check`.

**Atom interning note:** built atom `TermId`s are returned in `TCheck::Split`; the two-phase Plan A protocol then mints a `Var` per atom and calls `bind_fresh` → `Arith::new_var`, which decodes the atom term into a bound. Atoms are interned in the `Combiner`'s owned `Context`; the append-only `AtomRegistry` (master spec §8) never un-registers them on backtrack.

### 3.2 Narrowing the Int fence

- **`crates/shinri-theory/src/atom.rs`:** `contains_int_arith` currently fences *any* Int-touching arith atom. Replace with a **mixed-sort** test: fence only atoms that mix Int- and Real-sorted operands; admit pure-Int atoms (all arith operands Int-sorted) to `Owner::Arith`. Pure-Real is unaffected.
- **`crates/shinri-arith/src/normalize.rs`:** accept Int-sorted atoms. The `LinAtom` / slack / tableau machinery is reused **verbatim** — an integer enters as a `Rational` with denominator 1.
- **`crates/shinri-arith/src/vars.rs`:** record Int-sortedness per `ArithVar` (e.g. an `is_int: bool` alongside the var→term map) so the a-priori bound (§3.3) and the fractional scan (§3.4) know which vars must be integral.
- **Query-level pure-Int gate (`crates/shinri-solver/src/lib.rs`):** keep the existing `saw_shared` mixed-sort-equality fence; add a gate so a query that mixes Int- and Real-sorted **arith vars** sharing the solver fences the whole query to `unknown` (master spec §3.1). Pure-Int and pure-Real queries are both supported; only mixed is deferred.

### 3.3 A-priori finite bound (`crates/shinri-arith/src/bounds.rs`)

Compute a finite bound `M` (Papadimitriou 1981 / Borosh–Treybig small-model bound) from the magnitudes of the registered constraints' coefficients and constants, in **`shinri-num` big integers** (overflow-safe). Assert `−M ≤ x ≤ M` on every Int **problem** var as **ordinary axiomatic bounds** in the existing bound storage — so the undo log, backtracking, and Farkas conflict extraction all work unchanged.

**Seeding trigger (decided):** lazily, on the **first `check(Full)` at decision level 0**, guarded by a one-shot `apriori_seeded` flag. By the time any check runs, the Encoder has already registered **all** problem atoms (it registers every atom before asserting any unit clause), so all coefficients needed for `M` are known. `M` is a **termination backstop, never branched toward** — with branching active, B&B terminates far inside the box on realistic instances.

### 3.4 Fractional scan + branch split (`crates/shinri-arith/src/lib.rs` `check_full`, new `crates/shinri-arith/src/branch.rs`)

`assert` is unchanged (decode literal → tighten bound → trivial conflict on bound crossing). After the existing simplex reaches a feasible real assignment (or emits a Farkas conflict — unchanged):

1. Scan Int vars for a **non-integral** value. A `DeltaRational` value `c + k·δ` counts as integral for an Int var iff `k = 0` **and** `c` has denominator 1; a nonzero δ-coefficient (introduced by a strict bound — see §3.5) is non-integral and forces a branch. If every Int var is integral, return `Sat`.
2. Otherwise select a branch var — **most-fractional**, ties broken by **Bland index** for determinism (`branch.rs`).
3. Build `(x ≤ ⌊v⌋)` and `(x ≥ ⌈v⌉)` via the mutable seam and return **`TCheck::Split(vec![le, ge])`**.

The Combiner lifts to `SplitAtoms`; the solver mints a `Var` per atom, `bind_fresh` registers + encodes each as a bound, learns the clause, and backtracks one level to force the case-split. The SAT solver assumes one disjunct, `assert` tightens the bound, and `check` re-enters; the simplex re-solves under the tightened bound.

**Termination.** Int vars live in the finite box (§3.3); within it there are finitely many distinct branch atoms, and the SAT solver never repeats a full assignment (it learns). The branch tree is finite ⇒ the procedure terminates. No cut generation exists in B1, so termination rests solely on the box + SAT no-repeat.

### 3.5 Integer disequalities and strict inequalities

> **Correction vs master spec §5.** The master spec describes integer `a ≠ b` as emitted through `TCheck::Split` and references a QF_LRA `diseq.rs` feasibility-shift path. **Neither matches the codebase.** There is no `diseq.rs`; instead the `lower()` pass in `crates/shinri-solver/src/lib.rs` *eagerly* rewrites Real `(distinct a b)` → `(or (Lt a b) (Gt a b))` (and Real `(= a b)` → `Eq` for EUF + `Le`/`Ge` for arith), but both rewrites are **gated to `real_sort()`**. So disequalities are resolved by an **eager Boolean split at encoding time** — the SAT solver case-splits the `(or Lt Gt)` clause — *not* by splitting-on-demand. `TCheck::Split` is reserved for branch-and-bound on fractional vars (§3.4), which genuinely arise mid-search and cannot be eagerly enumerated.

B1 handles integer disequalities by **extending `lower()`** rather than adding a `TCheck::Split` diseq path:

- **Drop the `real_sort()`-only gate** on the Eq and Distinct rewrites so Int-sorted operands lower the same way: Int `(distinct a b)` → `(or (Lt a b) (Gt a b))`; Int `(= a b)` keeps `Eq` (for EUF) and emits `Le`/`Ge` companions for arith. The pairwise `(distinct a … n)` expansion is already sort-agnostic.

> **Reversal vs the original §3.5 (decided 2026-06-21, after API-fact extraction).** The original §3.5 chose to **tighten** Int strict inequalities to non-strict integer bounds (`x < c` ⟹ `x ≤ c − 1`) at encoding time, listing "reuse δ" as the rejected alternative. The extracted facts inverted that tradeoff, so **B1 now reuses δ and defers tightening to B2.** The decisive findings:
>
> - **Branch-and-bound needs floor/ceil and branching regardless** — the simplex relaxation can return `x = 5/2` for an Int var no matter how strictness is encoded, and that fractional value *must* be branched on (`branch.rs`, §3.4). Tightening is therefore **not an alternative to branching**; it is an *add-on* that only pre-empts the one extra branch a strict bound's δ would cause. So "tighten" = "reuse δ" **plus** extra code, not instead of it.
> - `Rational` exposes **no `floor`/`ceil`** (must be hand-rolled via `Integer::div_rem`); δ-reuse needs that helper in exactly one place (`branch.rs`), tightening needs it in two and additionally must thread an `is_int_query` flag and tighten in `build_encoding`/`normalize`.
> - `normalize.rs` and `build_encoding` are **already sort-blind and correct on Int atoms as rationals** — under δ-reuse they need **zero** changes; the existing `Rel::Lt` → `(rhs, −δ)` encoding already produces the strict bound.
> - **The two are byte-identical in sat/unsat verdicts** — the differential oracle cannot distinguish them. Tightening is a pure *performance* optimization (saves ~1 branch round per strict bound / disequality), which is exactly B2's remit, where it gets the same free differential validation against this A baseline.
>
> **Mechanism (δ-reuse):** keep the existing LRA δ-infinitesimal strict bound (`x < c` ⟺ `x ≤ c − δ`); the fractional scan (§3.4) treats a nonzero δ-component as non-integral and branches; the conflicting half of the branch dies, leaving the correct integer bound. Real-sorted disequalities/strict inequalities are unchanged (they keep δ). **Deferred to B2:** integer strict-bound tightening as a preprocessing optimization, differentially validated against B1.

### 3.6 Integer model emission (`crates/shinri-arith/src/model.rs`)

When `check` reports integer-feasible, the assignment is already **integral**, so no δ-infinitesimal elimination is needed for Int vars: emit each Int problem var's value directly as `ModelVal::Num` with denominator 1. Real-sorted models continue to use the QF_LRA δ-elimination path. The existing `shinri-solver` self-check (re-evaluate every `sat` model against all assertions before output) gates the result unchanged.

### 3.7 Backtracking

`push`/`pop` mechanism is unchanged (QF_LRA §9). Branch bounds and a-priori bounds are trail-stamped like any other bound; `pop(target)` restores them in O(changes). The fresh branch **atoms** are append-only (never un-registered on backtrack); only their *bound assertions* are level-scoped.

---

## 4. Test plan (soundness spine)

1. **Differential oracle (headline)** — `crates/shinri-solver/tests/oracle.rs`, `--features oracle`:
   - Add a random **QF_LIA** generator (Int sort; `set-logic QF_LIA`) alongside the existing QF_UF / QF_LRA generators.
   - Wire **cvc5** as a second `easy-smt` backend next to z3; compare our sat/unsat against **both**. Any disagreement panics with the full instance dumped; our `Unknown` is never a disagreement, but assert pure-QF_LIA instances do not go `Unknown` past the fence.
   - Cuts are off throughout B1, so this corpus *is* the Stage-A baseline that B2 must reproduce identically.
2. **Unit:** a-priori `M` computation; branch-atom freshness + mid-search registration (atom → `Owner::Arith`); Int `(distinct a b)` lowering to `(or Lt Gt)`; a strict integer bound (`x < 5`) resolves to the correct integer bound via the δ-branch path; the classic *non-terminating-without-a-bound* instance must **terminate**; most-fractional + Bland-tiebreak branch-selection determinism; pure-Int admitted / mixed Int-Real fenced to `unknown`.
3. **Self-check:** every `sat` integral model re-evaluated against all assertions (already wired in `shinri-solver`); every `unsat` carries a Farkas conflict over the (possibly branch) bound literals.
4. **Property:** assert-then-`pop` observationally equivalent to never-asserted, **including branch bounds**; random feasible/infeasible QF_LIA systems checked against self-evaluation.

**Phase-gate alignment:** only `shinri-num` on the arithmetic shipping path; `num-bigint` / `num-rational` survive solely as the dev-only differential oracle deps.

---

## 5. Crate / file plan

**`shinri-arith`:**

| Module | Change |
|---|---|
| `normalize.rs` / `build_encoding` | **No change** — already sort-blind; Int atoms normalize as rationals and the existing `Rel::Lt` → `(rhs, −δ)` encoding handles strictness (see §3.5 reversal) |
| `vars.rs` | Record Int-sortedness per `ArithVar` |
| `bounds.rs` | Compute + seed a-priori `−M ≤ x ≤ M` (bigint `M`, lazy one-shot at first level-0 `check(Full)`) |
| `lib.rs` (`check_full`) | Non-integral-scan + branch-decision step after the simplex feasibility loop |
| `branch.rs` *(new)* | Branch-var selection (most-fractional, Bland tiebreak) + branch `Split`-clause construction |
| `model.rs` | Integral-model emission path |

**Cross-crate:**

| Crate | Change |
|---|---|
| `shinri-theory` | `TheoryCtx.terms: &mut Context`; update `combiner.rs` construction sites |
| `shinri-theory` (`atom.rs`) | Narrow the Int fence: mixed-only, admit pure-Int |
| `shinri-solver` (`lib.rs`) | Query-level pure-Int gate (mixed Int/Real → `unknown`); extend `lower()` to also rewrite Int Eq/Distinct (drop the `real_sort()`-only gate); add public `Solver::int_sort()` (currently only `real_sort()` is exposed) |
| `shinri-solver` (`tseitin.rs`) | Encoder tracks `saw_int_arith` / `saw_real_arith` so the query-level LIRA gate can fire |
| `shinri-solver` (`tests/oracle.rs`) | QF_LIA generator + cvc5 second backend |

No GMI cut module in B1.

---

## 6. Risks & mitigations

| Risk | Mitigation |
|---|---|
| Non-termination | A-priori finite box (§3.3) + SAT no-repeat; no cuts to cap in B1 |
| A-priori bound `M` overflow on large coefficients | Compute `M` in `shinri-num` big integers; backstop only, never branched toward |
| `&mut Context` borrow churn across `combiner.rs` | Per-call `TheoryCtx` construction (no aliasing); borrow-split (§5.5) already isolates `terms` |
| Fresh branch-atom registration races in the Combiner fixpoint | Append-only atom space; only bound assertions are level-scoped; push/pop property test |
| Splitting-on-demand contract creep | `TCheck::Split` restricted to theory-valid split clauses; `EmptyTheory`/`Euf` stay on Sat/Conflict |
| Accidental QF_UFLIA / QF_LIRA unsoundness | Explicit fences to `unknown` (§3.2 mixed test + query-level gate) |

---

## 7. Definition of done

- `shinri-arith` decides **pure QF_LIA** soundly, completely, and terminatingly via a-priori bounds + splitting-on-demand B&B + integer-diseq splits — **with cuts entirely absent**.
- QF_UFLIA and mixed QF_LIRA fenced to `unknown`; QF_LRA / QF_UFLRA paths unchanged.
- Differential oracle extended to random QF_LIA and green against **z3 + cvc5**.
- The full soundness spine (§4) green; `cargo test --workspace` green; only `shinri-num` on the arithmetic shipping path.
- B1 stands as the known-correct baseline against which Plan B2's cuts will be differentially validated.

---

## References

- Master QF_LIA design: `docs/superpowers/specs/2026-06-20-shinri-arith-lia-design.md` (§1.1 soundness architecture, §2 the seam, §3 bounds, §4 check loop, §5 diseq, §7 model, §9 tests).
- Plan A (infrastructure): `docs/superpowers/plans/2026-06-20-shinri-lia-splitting-infra.md`.
- QF_LRA design: `docs/superpowers/specs/2026-06-20-shinri-arith-design.md` (§1.1 fence, §3 data structures, §5 check loop, §7 Farkas, §9 backtracking).
- Dutertre, de Moura. *A Fast Linear-Arithmetic Solver for DPLL(T).* CAV 2006.
- Barrett, Nieuwenhuis, Oliveras, Tinelli. *Splitting on Demand in Satisfiability Modulo Theories.* LPAR 2006.
- Papadimitriou. *On the complexity of integer programming.* JACM 1981 (the a-priori bound / small-model property).
