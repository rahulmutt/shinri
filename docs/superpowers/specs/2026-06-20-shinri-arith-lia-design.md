# shinri-arith — Design Specification (QF_LIA)

**Sound and complete linear integer arithmetic via splitting-on-demand branch-and-bound + Gomory cuts, terminating by a-priori finite bounds**

- **Date:** 2026-06-20
- **Status:** Approved design — ready for implementation planning
- **Scope of this document:** Extend the `shinri-arith` crate from QF_LRA to a sound *and complete* decision procedure for **pure QF_LIA** (linear integer arithmetic). Lifts the Int-sort soundness fence of the QF_LRA milestone (`docs/superpowers/specs/2026-06-20-shinri-arith-design.md` §1.1) for the pure-integer case. Introduces the cross-crate **splitting-on-demand** infrastructure that integer branching requires.

---

## 1. Goal & scope decisions

The QF_LRA milestone delivered a Dutertre–de Moura simplex that solves the **real relaxation** of linear arithmetic. That relaxation is exactly the engine branch-and-bound needs: this milestone adds integer search *on top of* it rather than replacing anything. Five scoping decisions fix the boundary:

1. **Pure QF_LIA only.** A query is in scope iff **every** arith var it touches is Int-sorted. Deliver a sound, complete, terminating decision procedure for that fragment.
2. **Splitting-on-demand to SAT.** Integer branching (`x ≤ ⌊v⌋ ∨ x ≥ ⌈v⌉`) is realized as a **theory-valid lemma** handed to the SAT solver, which performs the case-split with full backjumping + clause learning (Barrett, Nieuwenhuis, Oliveras, Tinelli, *Splitting on Demand in SAT Modulo Theories*, 2006). This is a deliberate, *controlled* relaxation of the QF_LRA "no free-standing lemmas" contract: the only permitted lemmas are theory-valid split/cut clauses.
3. **Completeness target: fully complete + terminating.** Branch-and-bound + Gomory cuts alone do not guarantee termination; an **a-priori finite bound** does. Completeness and termination rest on the bound; cuts are pure optimization (Section 6).
4. **A-priori finite bounds as the backstop, Gomory cuts as the performance layer.** Termination *never* depends on cut correctness — cuts can be disabled and the procedure stays complete. This decoupling is the central soundness decision (Section 1.1).
5. **Fences to `unknown` (unchanged philosophy):** QF_UFLIA (UF + integers with shared interface vars) and **mixed QF_LIRA** (an atom or query touching both Int- and Real-sorted vars). No unsound answers; these become later milestones.

**Out of scope (each its own later milestone):** QF_UFLIA combination (interface-equality propagation **and** LIA non-convex arrangement reasoning); QF_UFLRA interface-equality propagation; mixed QF_LIRA; non-linear integer arithmetic; difference logic; proof emission beyond Farkas conflicts; eager theory propagation.

### 1.1 The soundness architecture: bounds carry completeness, cuts carry speed

The single most important decision in this milestone, and the reason for the chosen mechanism:

- **Completeness and termination depend only on the a-priori bound.** Each integer var is confined to a finite box `[−M, M]`; the branch tree is then finite by construction (Section 4). Termination is a one-line argument, not a convergence proof.
- **The procedure is complete with cuts entirely disabled.** Cuts only *tighten* the relaxation with inequalities valid for all integer points. A buggy-but-weak cut costs performance, not soundness. A buggy-*wrong* cut (one that excludes an integer solution) is the only soundness hazard, and it is caught by the two-stage differential oracle (Section 9) and a debug re-derivation check (Section 6).
- This **decouples the soundness guarantee from the hottest, most error-prone code**, which is exactly what a from-scratch, soundness-critical solver wants. It also stages the build into a known-correct baseline (bounds + B&B) followed by an optimization layer (cuts) that is differentially validated against that baseline.

The rejected alternatives, for the record: *Cuts-from-Proofs* makes termination itself depend on the cut machinery being exactly right (couples soundness to performance code); a *Cooper/Omega fallback* is a second complete decision procedure to build and keep sound (largest surface area). Both were set aside in favor of the bound-as-backstop design.

---

## 2. The central infrastructure change: splitting-on-demand

Integer branching is the one piece that reaches outside `shinri-arith`. The QF_LRA `TheorySolver` contract allowed `check` to return only *Sat* or *Conflict*; integer search needs two new capabilities:

1. **Fresh theory-atom introduction.** A branch atom `x ≤ ⌊v⌋` (and a Gomory cut `Σ cᵢ·xᵢ ≤ k`) is in general **not** present in the original formula. The theory must mint a fresh atom mid-search and receive a `Lit` for it from the SAT core, with the atom registered to `Owner::Arith`.
2. **A `check` outcome that returns a lemma.** A new `TCheck::Split(Clause)` variant carries a theory-valid clause (e.g. `(x ≤ ⌊v⌋) ∨ (x ≥ ⌈v⌉)`). The `Combiner` forwards it to the SAT solver, which case-splits and drives the search; the new atoms' subsequent truth assignments route back into `Arith::assert` as ordinary bounds.

### 2.1 Cross-crate touch points

| Crate | Change |
|---|---|
| `shinri-theory` | `TCheck` gains a `Split(Clause)` variant. `TheoryCtx` gains a `fresh_atom` seam: given a theory atom description, allocate a SAT var, register `atom → Owner::Arith`, return its `Lit`. Documented contract: *the only permissible lemmas are theory-valid split/cut clauses.* |
| `shinri-core` / `shinri-sat` | Allow **mid-search** allocation of a fresh propositional var and atom→owner registration (the atom space is append-only, mirroring `AtomRegistry`). |
| `shinri-solver` | The `Combiner`: on `Split`, hand the clause to the SAT solver (as an axiom/learnt clause) and continue the joint fixpoint; route future assignments of the new atoms to `Arith`. |
| `shinri-arith` | Produce `Split` clauses; mint branch/cut atoms via the seam. |

`EmptyTheory` and `Euf` are unaffected — they keep returning Sat/Conflict and never call `fresh_atom`. The relaxation is intentionally narrow: there is no general-purpose theory-lemma channel, only the split/cut path enforced by the shape of the seam.

---

## 3. Variables, normalization, bounds

### 3.1 Normalization (`normalize.rs`)

The `LinAtom` / slack / tableau machinery is reused **verbatim** — an integer is a `Rational` with denominator 1 on the way in. Two changes only:

- **Accept** Int-sorted atoms (the QF_LRA §1.1 fence is removed for the all-integer case).
- **Reject mixed** Int/Real: if any atom mixes Int- and Real-sorted vars, or a query contains both an Int-sorted and a Real-sorted arith var sharing the solver, fence the whole query to `unknown` (the `Unsupported` path). Pure-Int and pure-Real queries are both supported; mixed is deferred.

### 3.2 A-priori finite bound (`bounds.rs`)

At decision level 0, compute a finite bound `M` from the magnitudes of the constraint coefficients and constants (Papadimitriou 1981 / Borosh–Treybig small-model bound for linear integer systems) and assert `−M ≤ x ≤ M` on every integer **problem** var. Key properties:

- These are **ordinary axiomatic bounds** in the existing `bounds.rs`, *not* lemmas — so the undo log, backtracking, and Farkas conflict extraction all work unchanged.
- `M` is computed in `shinri-num` big integers to avoid overflow; it is a **termination backstop, never branched toward** — with cuts and branching active, B&B terminates far inside the box on all realistic instances.

---

## 4. The `check(Full)` loop (extends §5 of the QF_LRA spec)

`assert` is unchanged (decode literal → tighten bound → trivial conflict on bound crossing). Integer reasoning runs in `check(Full)`:

1. Run the existing simplex to a feasible **real** assignment, or emit a Farkas conflict (Section 7 of the QF_LRA spec — unchanged).
2. If feasible, scan integer vars for a **fractional** value. If none are fractional, the assignment is integer-feasible → proceed to disequalities (Section 5).
3. Otherwise: select a branching var (**most-fractional**, ties broken by Bland index for determinism), generate any in-budget **GMI cuts** from its tableau row (Section 6), and return **`TCheck::Split`** on `(x ≤ ⌊v⌋) ∨ (x ≥ ⌈v⌉)`.
4. The SAT solver assumes one disjunct and re-enters `check`; the simplex re-solves under the tightened bound.

**Termination.** Integer vars live in a finite box (Section 3.2); within it there are finitely many distinct branch/cut atoms, and the SAT solver never repeats a full assignment (it learns). Hence the branch tree is finite ⇒ the procedure terminates. Cut rounds are **capped per node** and globally, so termination is independent of cut generation; cuts only prune.

---

## 5. Integer disequalities — a split, not a repair

With splitting available, an integer `a ≠ b` no longer needs the QF_LRA lemma-free feasibility-shift repair (`diseq.rs`). Because both sides are integral, `a ≠ b` is exactly the split

> `(a ≤ b − 1) ∨ (a ≥ b + 1)`

emitted through the same `TCheck::Split` mechanism. This is simpler and strictly more complete than the real-valued shift. The QF_LRA disequality-repair path remains for Real-sorted queries; integer disequalities take the split path.

---

## 6. Gomory (GMI) cut generation (`cuts.rs`, new)

- **Source row:** a tableau row whose basic var is integer-constrained but currently has a **fractional** value. The mixed-integer Gomory (GMI) cut is derived from the fractional parts of the row — an inequality valid for every integer point of the feasible region that excludes the current fractional vertex.
- **Introduction:** each cut is a fresh atom `Σ cᵢ·xᵢ ≤ k`, minted through the **same fresh-atom seam** as branch atoms (Section 2) and asserted as a bound. Cuts and branches therefore share one path into the SAT/tableau layer.
- **Soundness check (debug):** every emitted cut is re-validated by re-derivation — assert it dominates the fractional point while admitting the integer hull (mirrors the QF_LRA Farkas re-evaluation `debug_assert`). Compiled out of release, exhaustively checked under test/fuzz.
- **Budget:** capped cut rounds per branch node + a global cut cap. On exhaustion, branch. Termination rests on Section 4's finite box, never on cuts.

---

## 7. Model construction (`model.rs`, extended)

Simpler than the QF_LRA case: when `check` reports integer-feasible, the assignment is already **integral**, so no δ-infinitesimal elimination is needed for integer vars. Emit each integer problem var's value directly as `ModelVal::Num` with denominator 1. The existing `shinri-solver` self-check (re-evaluate every `sat` model against all assertions before output) gates the result unchanged. (Real-sorted models continue to use the QF_LRA δ-elimination path.)

---

## 8. Backtracking

- `push`/`pop` are unchanged in mechanism (QF_LRA §9). Branch bounds, cut bounds, and a-priori bounds are all trail-stamped like any other bound; `pop(target)` restores them in O(changes).
- The fresh branch/cut **atoms** are append-only (mirroring `AtomRegistry`); only their *bound assertions* are level-scoped. Atoms minted during a solve are never un-registered on backtrack.
- Property test: assert-then-`pop` is observationally equivalent to never-asserted, now including branch/cut bounds.

---

## 9. Test plan (soundness spine, design §11)

1. **Two-stage differential validation** (the core de-risking strategy):
   - **Stage A — baseline:** bounds + B&B with **cuts disabled**. Green against **z3 + cvc5** on random QF_LIA. This is the known-correct reference procedure.
   - **Stage B — cuts on:** must produce **identical** sat/unsat verdicts to Stage A *and* to z3/cvc5. Cuts cannot hide a bug because they are checked against a procedure that does not use them.
2. **Differential oracle (headline):** extend the existing z3/cvc5 differential harness with random **QF_LIA** generators (alongside QF_LRA and QF_UF), comparing sat/unsat.
3. **Unit:** GMI cut validity (re-derivation property); a-priori bound `M` computation; branch-atom freshness + mid-search registration; integer-disequality split; the classic *non-terminating-without-a-bound* instance must terminate; most-fractional branch selection determinism.
4. **Self-check:** every `sat` integral model re-evaluated against all assertions (already wired in `shinri-solver`); every `unsat` carries a Farkas conflict over the (possibly branch/cut) bound literals.
5. **Property:** random feasible/infeasible QF_LIA systems checked against self-evaluation; backtracking equivalence including branch/cut bounds.

**Phase gate alignment:** only `shinri-num` on the arithmetic shipping path; `num-bigint`/`num-rational` survive solely as the dev-only differential oracle.

---

## 10. Crate / file plan

**`shinri-arith`:**

| Module | Change |
|---|---|
| `normalize.rs` | Accept Int; reject mixed Int/Real (narrow the QF_LRA §1.1 fence) |
| `bounds.rs` | Seed a-priori `−M ≤ x ≤ M` bounds (reuses existing bound storage) |
| `simplex.rs` | Add the fractional-scan + branch-decision step to `check(Full)` |
| `cuts.rs` *(new)* | GMI cut generation + debug re-validation |
| `branch.rs` *(new)* | Branch-var selection + `Split` clause construction; integer-diseq → split |
| `model.rs` | Integral-model emission path |

**Cross-crate:** `shinri-theory` (`TCheck::Split`, `fresh_atom` seam), `shinri-core`/`shinri-sat` (mid-search fresh var + atom→owner registration), `shinri-solver` (`Combiner` split plumbing + new-atom routing).

---

## 11. Risks & mitigations

| Risk | Mitigation |
|---|---|
| Wrong GMI cut excludes an integer solution (unsoundness) | Cuts disable-able by construction; two-stage differential vs baseline + z3/cvc5; debug re-derivation check |
| Non-termination | A-priori finite box (Section 3.2) + SAT no-repeat; cuts capped per node and globally |
| Fresh-atom registration races in the `Combiner` fixpoint | Append-only atom space; only bound assertions are level-scoped; push/pop property test |
| Splitting-on-demand contract creep | `TCheck::Split` restricted to theory-valid split/cut clauses; enforced by the narrow `fresh_atom` seam; `EmptyTheory`/`Euf` unaffected |
| A-priori bound `M` overflow on large coefficients | Compute `M` in `shinri-num` big integers; backstop only, never branched toward |
| Accidental QF_UFLIA / QF_LIRA unsoundness | Explicit fences to `unknown` (Section 1 decision 5, Section 3.1) |

---

## 12. Definition of done

- `shinri-arith` decides **pure QF_LIA** soundly, completely, and terminatingly via splitting-on-demand B&B + Gomory cuts + a-priori bounds.
- QF_UFLIA and mixed QF_LIRA fenced to `unknown` — no unsound answers; QF_LRA / QF_UFLRA paths unchanged.
- `shinri-theory`/`shinri-solver` carry the narrow splitting-on-demand seam (`TCheck::Split` + `fresh_atom`), used only by `Arith`.
- Two-stage (baseline → cuts) differential oracle extended to random QF_LIA and green against z3 + cvc5.
- Only `shinri-num` on the arithmetic shipping path.

---

## References

- Dutertre, de Moura. *A Fast Linear-Arithmetic Solver for DPLL(T).* CAV 2006. (the QF_LRA base this extends)
- Barrett, Nieuwenhuis, Oliveras, Tinelli. *Splitting on Demand in Satisfiability Modulo Theories.* LPAR 2006. (the branching architecture)
- Papadimitriou. *On the complexity of integer programming.* JACM 1981. (the a-priori bound / small-model property)
- Gomory. *An algorithm for integer solutions to linear programs.* 1963; and the mixed-integer (GMI) refinement. (cut generation)
- QF_LRA design: `docs/superpowers/specs/2026-06-20-shinri-arith-design.md` (§1.1 fence, §3 data structures, §5 check loop, §7 Farkas, §9 backtracking).
- Top-level design: `docs/superpowers/specs/2026-06-18-shinri-design.md` (§3, §7, §11, §13).
