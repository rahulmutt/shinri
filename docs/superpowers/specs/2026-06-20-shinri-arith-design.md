# shinri-arith — Design Specification (QF_LRA)

**A Dutertre–de Moura simplex theory solver for linear real arithmetic**

- **Date:** 2026-06-20
- **Status:** Approved design — ready for implementation planning
- **Scope of this document:** The `shinri-arith` crate, Phase-1 milestone: a sound and complete QF_LRA theory solver that plugs into the existing Nelson–Oppen `Combiner` as its `Arith` slot. Closes the last missing piece of the top-level design's Phase 1 (`docs/superpowers/specs/2026-06-18-shinri-design.md` §13).

---

## 1. Goal & scope decisions

The single most valuable next component for shinri. The SAT core, theory-combination framework, EUF, and `shinri-num` (`Rational`, `DeltaRational`) are all in place; `shinri-theory` already exposes a working Nelson–Oppen `Combiner<E, A>` whose `A` slot is filled by a placeholder `EmptyTheory`. This milestone replaces that placeholder with a real LRA solver.

Five scoping decisions fix the boundary of this milestone:

1. **QF_LRA only.** Deliver a sound and complete standalone linear-real-arithmetic simplex. The combination logic QF_UFLRA is **deferred** to a follow-up milestone.
2. **QF_UFLRA fenced to `unknown`.** Soundness in Nelson–Oppen requires a convex theory to propagate every entailed interface equality. This milestone does **not** implement interface-equality propagation, so if a query actually mixes UF and arithmetic (shared interface variables are present), the solver returns `unknown` rather than risk an unsound `sat`. Pure QF_LRA queries have no shared interface variables and are unaffected.
3. **`check`-only.** Theory (bound) propagation via the `propagate` seam is **not** in scope; `propagate` is a no-op. All consistency reasoning runs at `check(Full)`. Eager bound propagation is a later performance milestone.
4. **Integer-rows-with-shared-denominator tableau** from the start (top-level design §7.5), not per-cell rationals — the primary defense against rational coefficient blowup during pivoting.
5. **Lemma-free disequality repair** for full QF_LRA completeness (Section 6). The `TheorySolver` contract forbids convex Phase-1 theories from emitting free-standing lemmas, so arithmetic disequalities are repaired inside `check` and only ever produce conflicts.

**Out of scope (each its own later milestone):** QF_UFLRA interface-equality propagation; QF_LIA integer reasoning (branch-and-bound / Gomory cuts); difference logic (IDL/RDL); Sum-of-Infeasibilities + heuristic pivoting; eager theory propagation; proof emission beyond Farkas conflicts.

### 1.1 Soundness fence: Int-sorted arithmetic

Int-sorted atoms route to `Owner::Arith` in `classify`, but an LRA simplex solves only the **real relaxation** — sound for QF_LRA, **unsound for QF_LIA** (a real solution need not be an integer solution). Therefore Int-sorted arithmetic atoms are fenced to `unknown` this milestone, exactly like QF_UFLRA. Integer support arrives with the later QF_LIA branch-and-bound milestone. The fence is applied at atom registration / normalization (Section 4).

---

## 2. Crate layout & dependencies

New crate **`shinri-arith`**, slotting into the dependency graph where the top-level design §3 reserves it:

```
num ← core ← sat ← theory ← {euf, arith} ← solver
```

- Depends on `shinri-core` (terms, `Rational`, `DeltaRational`, `Lit`, `Var`, `Context`) and `shinri-theory` (the `TheorySolver` trait, `TheoryCtx`, `TCheck`, `EqLeaf`, and `Effort` re-exported from `shinri-sat`).
- Does **not** depend on `shinri-sat` directly, and never on `shinri-euf`. The one-directional crate graph (design principle §2.5) is preserved.

### 2.1 Modules

| Module | Responsibility |
|---|---|
| `lib.rs` | `pub struct Arith` + its `TheorySolver` impl — the only public surface |
| `normalize.rs` | `TermId` atom → canonical `LinAtom { row: LinComb, rel, rhs }`; rejects nonlinear, fences Int-sort |
| `tableau.rs` | integer-rows-with-shared-denominator tableau; basic/nonbasic split; pivot-and-update |
| `bounds.rs` | per-variable `(lower, upper)` as `DeltaRational`; trail-stamped for backtrack |
| `simplex.rs` | the Dutertre–de Moura `check` loop, Bland's rule, assignment maintenance |
| `diseq.rs` | asserted disequalities + the lemma-free repair pass |
| `farkas.rs` | infeasible-row → conflict `Vec<EqLeaf::Asserted>` |
| `model.rs` | δ-elimination → concrete `Rational` per variable for `ModelBuilder` |

### 2.2 Integration

The only change in `shinri-solver` is one line: `Combiner<Euf, EmptyTheory>` → `Combiner<Euf, Arith>`. `EmptyTheory` remains in `shinri-theory` (still used by tests). `Arith` implements `TheorySolver` (`new_var`, `assert`, `propagate`, `check`, `explain`, `model`, `push`, `pop`); the `Combiner` already routes `Owner::Arith` atoms to it and drives the joint fixpoint.

---

## 3. Core data structures

### 3.1 Arith variables

Two kinds, both interned to a dense `ArithVar(u32)`:

- **Problem variables** — the uninterpreted Int/Real constants appearing in atoms (e.g. `x`, `y`).
- **Slack variables** — one per distinct linear combination `Σ cᵢ·xᵢ` appearing in an atom. The atom `Σ cᵢ·xᵢ ⋈ k` introduces a slack `s = Σ cᵢ·xᵢ` (a tableau row) and reduces the atom to a simple **bound** `s ⋈ k`. This is the standard DdM move: every atom becomes a variable bound; all structure lives in the tableau.

A map from canonical `LinComb` → slack `ArithVar` deduplicates slacks so repeated combinations share one row. The var/slack space is **append-only** across a solve (atoms are never un-registered on backtrack — mirrors `AtomRegistry`).

### 3.2 Tableau (`tableau.rs`)

Rows encode `A·x = 0` over the basic (slack) variables. Per design §7.5, each row is stored as a vector of **integer coefficients plus one shared denominator** for the row, not per-cell rationals. Storage is **sparse** (var-index → integer coeff), since SMT tableaux are sparse. Pivot-and-update works in integers (cross-multiply, then divide the row through by its gcd to keep magnitudes small — `shinri-num`'s fast GCD is the hot path). The tableau **persists across backtracking** (a pivot is only a basis change); backtracking restores bounds and assignment, not the basis.

### 3.3 Bounds (`bounds.rs`)

Each `ArithVar` carries `lower: Option<DeltaRational>` and `upper: Option<DeltaRational>`. `DeltaRational (c, k)` encodes strictness: `x < c` is `upper = (c, -1)`, `x ≤ c` is `(c, 0)`, `x > c` is `lower = (c, +1)`, `x ≥ c` is `(c, 0)`. Every bound tightening pushes (previous value, asserting `Lit`) onto an **undo log** keyed by decision level; `pop(target)` restores bounds in O(changes).

### 3.4 Assignment

`value: Vec<DeltaRational>` per variable, maintained so every tableau equation holds after each nonbasic update (the DdM invariant). On `pop`, the assignment is restored consistently with the restored bounds.

---

## 4. Normalization (`normalize.rs`)

`new_var(cx, v, atom)` decodes the registered `TermId` atom into a `LinAtom`:

- Walk the term: `Add`/`Sub`/`Neg` accumulate into a `LinComb` (map `ArithVar → Rational` coeff); `Mul` is constant-folded (one side must be a numeral — nonlinear is already rejected by `classify`, re-checked here defensively); numerals (`ConstVal::Num`) accumulate into the constant term; uninterpreted Int/Real constants become problem `ArithVar`s.
- Move the constant to the right-hand side; the relation (`Le/Lt/Ge/Gt`) gives `rel` and `rhs`. `Ge/Gt` are normalized to `Le/Lt` by negating the row.
- **Equality** `a = b` over arith terms: the *positive* atom yields two bounds (`a−b ≤ 0 ∧ a−b ≥ 0`); the *negative* literal is a disequality (Section 6).
- **`distinct`** over arith terms: already lowered to pairwise `≠` by `shinri-solver`; each pair is a disequality.
- **Fences (→ `unknown`):** Int-sorted atoms (§1.1) and any residual nonlinear product are refused. The refusal propagates upward as `unknown` for the whole query (the `Unsupported` path).

Each distinct `LinComb` is interned to its slack `ArithVar` and its defining row is added to the tableau (once).

---

## 5. The `check` algorithm (`simplex.rs`)

`assert(lit)` does **no solving**: decode the literal to a bound on its slack/problem var, tighten the bound (record undo entry + asserting `Lit`), and if the new bound crosses the var's opposite bound, record a trivial 2-literal conflict (returned on the `assert`→`propagate` bridge the Combiner already implements). Real solving runs in `check(Full)` (`check(Standard)` returns `Sat` — covered by the no-op `propagate`):

1. **Find a violated basic variable** `xᵢ` (value outside `[lower, upper]`). If none, bounds are feasible → disequality repair (Section 6).
2. **Select an entering nonbasic** `xⱼ` that moves `xᵢ` toward its violated bound (correct sign of the tableau coefficient, and `xⱼ` has slack in its own bound). **Bland's rule** (smallest variable index among eligible candidates) guarantees no cycling.
3. **Pivot** `xⱼ` into the basis, `xᵢ` out; update the assignment so all rows still hold. Integer-row arithmetic with row-gcd normalization keeps coefficients small.
4. **No entering candidate** for a violated `xᵢ` ⇒ that row is a Farkas witness of infeasibility → build the conflict (Section 7).
5. Loop. Bland's rule + finite bounds ⇒ termination.

A `debug_assert!` checks tableau well-formedness (`A·x = 0` holds; basic vars have unit columns) after each pivot — compiled out of release, exhaustively checked under test/fuzz (design §11).

---

## 6. Disequality repair (`diseq.rs`) — lemma-free, the QF_LRA-completeness path

Disequalities `a ≠ b` accumulate (from a negated `=` atom or a lowered `distinct` pair). The `TheorySolver` contract forbids free-standing lemmas, so they are repaired inside `check` after Section 5 step 1 reports the bounds **feasible**:

1. For each asserted `a ≠ b`, compare the model: if `δ(a) ≠ δ(b)` (as `DeltaRational`), it is already satisfied.
2. If `δ(a) = δ(b)`, attempt a **feasibility shift**: the disequality's slack `d = a − b` is a tableau row; try to pivot/update it to a nonzero value still within all bounds. On success, take the shift and re-scan (a shift may re-touch another diseq) to a fixpoint.
3. If **no shift exists**, the bounds *entail* `a = b`, so `a ≠ b` is genuinely violated: emit a **conflict** whose antecedents are the bound literals forcing `a = b` plus the disequality literal itself. A conflict, never a lemma — honoring the trait contract.

Termination: each successful shift removes a disequality from the violated set; re-scans are bounded by a cap. On hitting the cap, the solver conservatively returns `unknown` rather than spin (soundness over completeness at the edge).

---

## 7. Farkas conflict extraction (`farkas.rs`)

When a basic `xᵢ` is infeasible with no entering candidate, its tableau row is the Farkas combination: each nonbasic in the row is pinned at the bound that blocks improvement. The conflict is exactly:

> {the bound literal setting `xᵢ`'s violated bound} ∪ {the bound literal pinning each nonbasic in the row}

returned as `Vec<EqLeaf::Asserted(lit)>`. The `Combiner` negates these into the clause it hands the SAT analyzer. Because every leaf is a real asserted input literal (no interface justifications in pure QF_LRA), the `explain` method is unreachable and is implemented as `unreachable!()` with an explanatory comment. In debug builds the emitted conflict is validated by re-evaluating the Farkas linear combination to a contradiction (`Σ λᵢ·constraintᵢ` sums to `0 < 0` / `0 ≤ −ε`).

---

## 8. Model construction (`model.rs`)

On overall `Sat`, `model(ModelBuilder)` emits each problem variable's value with the δ-infinitesimal eliminated: compute a single small positive rational `δ*` that makes every `(c, k)` assignment respect all active strict bounds simultaneously (the standard minimum-gap computation over active strict bounds), then emit `Rational = c + k·δ*` per problem variable as `ModelVal::Num`. This feeds `shinri-solver`'s existing self-check, which re-evaluates every `sat` model against all assertions before output (design §10.5 / §11).

---

## 9. Backtracking

`push` increments the level. `pop(target)` (absolute target level, matching `EqualityEngine`/`UndoLog`) restores bounds and assignment from the undo log down to `target` in O(changes). The tableau basis is **not** rolled back — pivots are basis changes that remain valid; only the feasibility state (bounds, assignment) is level-dependent. Asserted disequalities are likewise trail-stamped and restored. Property test: assert-then-pop is observationally equivalent to never-asserted.

---

## 10. Test plan (soundness spine, design §11)

- **Unit:** normalizer (each relation; `Neg/Add/Sub/Mul`; constant folding; Int-sort & nonlinear fencing); single-pivot correctness; bound undo/restore across `push`/`pop`; **δ-rational strict-inequality edge cases** (the named off-by-one bug site) as dedicated property tests; Farkas-sum-is-contradiction property; disequality-repair termination.
- **Property:** random feasible/infeasible LRA systems checked against a self-evaluation; backtracking equivalence (assert+pop = never-asserted).
- **Differential oracle (headline):** extend the existing z3 differential harness (the QF_UF random oracle) to **random QF_LRA** — generate random linear systems, compare `sat`/`unsat` against z3 *and* cvc5. This validates the simplex and `shinri-num` together; it is the primary mitigation for the from-scratch soundness failure modes.
- **Self-check:** every `sat` model re-evaluated against all assertions (already wired in `shinri-solver`); every `unsat` carries a Farkas conflict.
- **Integration:** a curated QF_LRA SMT-LIB regression set through the full `shinri-solver` pipeline (sat/unsat/model).

**Phase-1 gate alignment:** `shinri-arith` uses only `shinri-num` for arithmetic — no `num-bigint`/`num-rational` on the shipping path; they survive solely as the dev-only differential oracle.

---

## 11. Risks & mitigations

| Risk | Mitigation |
|---|---|
| δ-rational strict/non-strict off-by-one (named soundness bug site) | Dedicated property tests; `DeltaRational` already proven by EUF/Combiner tests; differential oracle |
| Coefficient blowup during pivoting | Integer-rows-with-shared-denominator (§3.2) + row-gcd normalization + `shinri-num` i128 fast-path |
| Disequality repair non-termination | Bounded re-scan cap → conservative `unknown` (§6) |
| Silent unsoundness from a `shinri-num` bug | Differential oracle vs z3 + cvc5; `unsat` Farkas self-check; `sat` model self-check |
| Accidental QF_LIA / QF_UFLRA unsoundness | Explicit fences to `unknown` (§1.1, §1 decision 2) |

---

## 12. Definition of done

- `shinri-arith` crate implements `TheorySolver`; `shinri-solver` uses `Combiner<Euf, Arith>`.
- Sound and complete for QF_LRA (including arithmetic disequalities via §6).
- QF_UFLRA and QF_LIA fenced to `unknown` (no unsound answers).
- Differential oracle extended to random QF_LRA and green against z3 + cvc5.
- Only `shinri-num` on the arithmetic shipping path.

---

## References

- Dutertre, de Moura. *A Fast Linear-Arithmetic Solver for DPLL(T).* CAV 2006.
- King, Barrett, Dutertre. *Simplex with Sum of Infeasibilities for SMT.* FMCAD 2013. (later milestone)
- Top-level design: `docs/superpowers/specs/2026-06-18-shinri-design.md` (§3, §6.5, §7, §11, §13).
