# shinri-arith QF_LIA — Plan B2 Design (Stage B: GMI cuts + level-0 bound tightening + integer bound rounding)

**The QF_LIA optimization layer that makes UNSAT practically decidable — GMI cuts collapse the LP relaxation, level-0 bound tightening shrinks the box, and integer bound rounding drops the δ-infinitesimal for the integer fragment. All three are pure optimizations behind a single Stage-B gate; B1's a-priori bound still carries completeness and termination, so every B2 verdict is differentially validated against the cuts-off B1 baseline and z3 + cvc5.**

- **Date:** 2026-06-22
- **Status:** Approved design — ready for implementation planning
- **Master design spec:** `docs/superpowers/specs/2026-06-20-shinri-arith-lia-design.md` (the approved QF_LIA milestone design; this document scopes the **Stage B** optimization subset of it — §6 cuts, §9 two-stage differential)
- **Predecessor plan:** `docs/superpowers/specs/2026-06-21-shinri-lia-planB1-design.md` (Plan B1 — the complete, terminating baseline with cuts OFF: a-priori finite box + splitting-on-demand branch-and-bound + integer-diseq splits + integral models, SAT-direction differential green vs z3 + cvc5)
- **Successor:** none planned in the QF_LIA milestone; QF_UFLIA combination and mixed QF_LIRA remain separate later milestones.

---

## 1. Scope & relationship to the milestone

B2 is **Stage B** of the QF_LIA milestone (master spec §1.1, §9): the optimization layer added on top of the B1 baseline. The single most important inherited decision is unchanged — **completeness and termination depend only on the a-priori bound `M`; cuts and tightening are pure optimization.** B2 adds three reinforcing optimizations, all of which can be disabled with B1's completeness/termination intact:

- **GMI cuts** — tighten the LP relaxation in place with inequalities valid for every integer point, until the relaxation goes infeasible, at which point the **existing Farkas conflict path** (`farkas_conflict`, lib.rs) yields UNSAT with **no box enumeration**.
- **Level-0 bound tightening (FBBT)** — shrink each integer var's interval far inside the `[−M, M]` box before search, so any residual branching ranges over a small interval rather than `M ≈ 3×10¹²`.
- **Integer bound rounding** — eliminate the δ-infinitesimal for the integer fragment by rounding every bound on an integer-valued var to an integer at encode time (folds in B1 §3.5's deferred task).

### 1.1 Why B2 exists: UNSAT is intractable at Stage A

B1 is complete and terminating, but the a-priori box `M = (n+1)·((n+m)·a+1)^(n+m)` is astronomically large (empirically `M ≈ 3×10¹²` on the random corpus). For **SAT** instances branch-and-bound finds a model far inside the box, so the B1 SAT-direction differential is green. For **UNSAT** instances B&B must *exhaust* the box, which is `O(M)` nodes — intractable. The B1 oracle therefore **skips the UNSAT direction** (`crates/shinri-solver/tests/oracle.rs`, the `#[ignore]`'d companion test, annotated *"re-enable after Plan B2 adds Gomory cuts"*).

B2's headline **definition of done is outcome-anchored**: the currently-skipped UNSAT differential direction is re-enabled and goes green within a wall-clock budget on curated tiers (§4). Cuts and tightening must *genuinely* make UNSAT decidable — not merely run "optionally faster." This is achieved by cuts driving the relaxation to LP-infeasibility (Farkas UNSAT without enumeration) reinforced by FBBT shrinking the box.

### 1.2 In scope (B2)

1. `cuts.rs` (new): mixed-integer Gomory (GMI) cut derivation from a fractional tableau row, in exact `shinri-num` rationals, plus a debug re-derivation soundness check (master spec §6).
2. `propagate.rs` (new): feasibility-based bound tightening (FBBT) seeded as level-0 axiomatic bounds, with integer rounding.
3. Branch-and-cut control in `integer_check` (lib.rs) + `branch.rs`: cut-before-branch policy with per-node and global cut budgets.
4. Integer bound rounding in `build_encoding` (lib.rs): drop the δ-infinitesimal for integer-valued vars at encode time (folds in B1 §3.5's deferred optimization).
5. A single **Stage-B on/off gate** wrapping all three optimizations, so the differential harness can run B1-baseline vs Stage-B and assert identical verdicts.
6. Resolution of the `TODO(planB)` proof-certificate question at `crates/shinri-sat/src/solver.rs` (§3.7).
7. Two-stage differential oracle: cuts-OFF (B1) vs cuts-ON (B2) vs z3 + cvc5, with the UNSAT direction re-enabled on curated tiers (master spec §9).

### 1.3 Explicitly out of scope

QF_UFLIA combination and mixed QF_LIRA remain fenced to `unknown` (master spec §1 decision 5) — unchanged. QF_LRA / QF_UFLRA paths are untouched. Proof/certificate emission for cuts and branch lemmas beyond the debug re-derivation check is **out of scope** (master spec §1: "proof emission beyond Farkas conflicts"); §3.7 records this decision explicitly.

---

## 2. Architecture overview — branch-and-cut

The B1 check loop already reaches a feasible real assignment via the QF_LRA simplex and, on a fractional integer var, returns a branch `Split`. B2 changes exactly one decision point — `integer_check` (lib.rs) — to **try cuts before branching**, and adds **one level-0 preprocessing step** (FBBT). The relaxation engine, the Farkas path, the splitting seam, and backtracking are all unchanged.

```
SAT solver (DPLL(T))  ── unit-propagates forced cut/branch literals ──┐
   │  assigns atom literals                                           │
   ▼                                                                  │
Combiner (Theory) ──TheoryResult::SplitAtoms──▶ solver mints Vars,    │
   │  TCheck::Split lift                          bind_fresh-encodes ──┘
   ▼                                              (1-elem clause = forced cut bound;
Arith::check(Full)                                 2-elem clause = branch case-split)
   1. seed a-priori box M  +  FBBT tighten (level 0, once)   [§3.4]
   2. simplex → feasible real assignment   (or Farkas conflict → UNSAT, unchanged)
   3. integer_check:
        all Int problem vars integral?  → Sat
        fractional Int var x_B exists:
           node+global cut budget left?
              yes → GMI cut from x_B's tableau row  → TCheck::Split(vec![cut])   [§3.1–3.3]
                    → re-enter; simplex re-solves under tightened relaxation
                    → LP infeasible → Farkas conflict → UNSAT (no enumeration)
              no  → branch: TCheck::Split(vec![le, ge])   (B1 behavior)
```

Each unit keeps one responsibility: `cuts.rs` derives + validates GMI cuts; `propagate.rs` runs FBBT; `branch.rs` owns budget-aware cut-vs-branch selection and clause construction; `build_encoding` owns integer bound rounding; `integer_check` orchestrates; everything downstream is unchanged from B1.

### 2.1 The key reuse: a cut is a unit Split clause

A GMI cut `Σ cⱼ·xⱼ ≤ k` is **unconditionally true** for all integer points, so it is introduced as a **1-element** `TCheck::Split(vec![cut])`. The existing Plan A two-phase seam (`crates/shinri-sat/src/solver.rs`, the `SplitAtoms` arm) handles this verbatim: phase 1 mints a fresh `Var`, calls `bind_fresh` → `Arith::new_var` which decodes the cut atom into a bound; phase 2 `add_learnt(&[cut_lit])` learns a **unit** clause, which enqueues `cut_lit` as a `Reason::Unit` propagation — forcing the cut bound with **no case-split**, then backtracks one level so `check` re-enters under the tightened relaxation. The seam's own `ArithSplitter` test already returns a single-atom Split, so this path is mechanically exercised today. **No cross-crate seam change is required** — cuts and branches share one path into the SAT/tableau layer (master spec §2, §6).

---

## 3. Components

### 3.1 GMI cut derivation (`crates/shinri-arith/src/cuts.rs`, new)

**Source row.** The most-fractional basic integer var `x_B` (the same var B1 would branch on — reuse `branch.rs` selection: most-fractional, ties by Bland/smallest `ArithVar` index). Its tableau `Row` is `x_B = Σ_{j∈N} a_j·x_j` over nonbasic vars `j`, with rational coefficients recoverable via `Row::coeff` (shared-denominator integer storage; see `tableau.rs`).

**Orientation to active bounds.** In the Dutertre–de Moura tableau every nonbasic var sits at one of its bounds. Shift each nonbasic to a nonnegative slack from its *active* bound: `y_j = x_j − lo_j ≥ 0` (at lower) or `y_j = hi_j − x_j ≥ 0` (at upper), reading the active bound from `bounds`. Rewrite the row over the `y_j`.

**GMI inequality.** Let `f₀ = β(x_B) − ⌊β(x_B)⌋ ∈ (0,1)` (the row is fractional, so `f₀ ≠ 0`). For each oriented nonbasic coefficient `ā_j`, with `f_j = ā_j − ⌊ā_j⌋`, emit the standard mixed-integer Gomory cut on the `y_j`:

> `Σ_j ψ(ā_j)·y_j ≥ f₀`,  where for an **integer** nonbasic `ψ(ā_j) = f_j` if `f_j ≤ f₀`, else `f₀·(1−f_j)/(1−f₀)`; for a **continuous** nonbasic `ψ(ā_j) = ā_j` if `ā_j > 0`, else `−f₀·ā_j/(1−f₀)`.

In pure QF_LIA every var (problem **and** slack) is integer-valued — atoms have integer coefficients, so each slack `s = Σ aᵢ·xᵢ` is an integer combination of integers — so only the integer branch of `ψ` is exercised, and the GMI cut coincides with (or strengthens) the Chvátal–Gomory cut. The code implements the general GMI form regardless, for robustness.

**Back-substitution.** Substitute `y_j` back to `x_j` and the active bounds to obtain a cut in the original problem/slack vars, `Σ cⱼ·xⱼ ≤ k` (or `≥`, normalized to the codebase's `Le`/`Ge`).

**Exact arithmetic.** All of the above is computed in `shinri-num` `Rational`/`Integer` — **no floating point**. This is the central soundness property of cut generation: an exactly-derived GMI cut is valid for the integer hull by construction.

### 3.2 Cut introduction — reuse the unit-Split seam

Build the cut atom via `cx.terms.mk_app(Op::Builtin(BuiltinOp::Le), &[lhs, rhs_num])` / `mk_numeral`, exactly as `integer_check` builds its `le`/`ge` branch atoms today (lib.rs). The `lhs` is the linear term `Σ cⱼ·xⱼ` reconstructed from problem-var `TermId`s (slacks expand to their defining comb so the atom is over original terms). Return `TCheck::Split(vec![cut])`. The seam (§2.1) mints + encodes + unit-propagates it. Atoms are interned in the Combiner's owned `Context` and are append-only (master spec §8); only their bound assertions are level-scoped.

### 3.3 Branch-and-cut control + budgets (`integer_check` lib.rs, `branch.rs`)

- **Per-node cut budget:** cap the number of cut rounds at a single search node. Tracked on `Arith`, reset when the node changes (on `pop` / new decision level).
- **Global cut budget:** cap total cuts generated this solve.
- **Policy:** if a fractional integer var exists and both budgets have room, derive an in-budget GMI cut and return it; otherwise fall back to the B1 branch `Split`. On a node where the cut failed to separate (degenerate row, `f₀` collapses) the policy also falls back to branch, so progress is guaranteed.
- **Termination is independent of cuts** (master spec §4): the finite box + SAT no-repeat carry termination regardless of budget values; budgets exist only to bound cut effort. Any finite budget is sound.

### 3.4 Level-0 bound tightening / FBBT (`crates/shinri-arith/src/propagate.rs`, new)

Feasibility-based bound tightening, run **once at level 0** at the same one-shot trigger as the a-priori box (`seed_apriori_if_needed` in lib.rs, called from `propagate`/`check`), **after** `M` is seeded so every var starts with a finite two-sided interval:

- For each registered constraint `Σ aᵢ·xᵢ ≤ rhs` (and its row form) and the current bounds on the other vars, derive an implied bound on each `xₖ`: e.g. for `aₖ > 0`, `xₖ ≤ (rhs − Σ_{i≠k} minᵢ) / aₖ` where `minᵢ` is `aᵢ·loᵢ` or `aᵢ·hiᵢ` per sign.
- **Integer rounding:** round each derived bound to an integer (`⌊·⌋` for upper, `⌈·⌉` for lower) — this is where FBBT bites on integer problems, e.g. `xₖ ≤ 17/3` ⟹ `xₖ ≤ 5`.
- **Iterate** to a fixpoint or a capped round count (a tightened bound can trigger further tightening).
- Install the tightened bounds as **level-0 axiomatic bounds** under fresh sentinel lits, stripped from conflicts (reuse the `apriori_lits` / `strip_apriori` mechanism in lib.rs).

FBBT is **monotone** — it only tightens within the `[−M, M]` box and only from valid constraint implications — so it is always sound; a too-weak round costs nothing. `M` remains the outer backstop.

### 3.5 Debug re-derivation soundness check (`cuts.rs`)

Per master spec §6, every emitted cut carries a `debug_assert` (compiled out of release):

1. **Separation:** the cut excludes the current fractional vertex — `β(Σ cⱼ·xⱼ) > k` for a `≤` cut. A cut that fails to separate is a bug (or a degenerate row that should have fallen back to branch).
2. **Re-derivation agreement:** recompute the GMI coefficients via an independent code path from the same row + active bounds and assert byte-equality with the emitted cut. This guards the derivation arithmetic.

The release-grade soundness net is the two-stage differential (§4): cuts-on verdicts must match the cuts-off B1 baseline and z3 + cvc5, so a wrong cut that excluded an integer solution would surface as a `shinri=Unsat` on a `z3/cvc5=Sat` instance — an instant panic.

### 3.6 Integer bound rounding (`build_encoding` lib.rs) — folds in B1 §3.5's deferred task

B1 reuses the LRA δ-infinitesimal for integer strictness (`x < c` ⟺ `x ≤ c − δ`) and lets the fractional scan branch the δ away (B1 §3.5). B2 eliminates the δ for the integer fragment at encode time:

**In an admitted pure-Int query, every bound on an integer-valued `ArithVar` is rounded to an integer when `build_encoding` constructs the `AtomEncoding::Ineq`:**

- Upper bound: `⌊rhs⌋`; strict `x < rhs` ⟹ `x ≤ ⌈rhs⌉ − 1`.
- Lower bound (the negation polarity): `⌈rhs⌉`; strict `x > rhs` ⟹ `x ≥ ⌊rhs⌋ + 1`.
- The δ-coefficient is set to `0` in both `pos` and `neg` encodings.

This is a **strict superset** of B1's framing: besides strict integer bounds it also rounds the **coefficient-division** fractional case (`2x ≤ 5` reduces to `x ≤ 5/2` today and forces a branch — rounding makes it `x ≤ 2` immediately), pre-empting branches on non-strict atoms too. The `floor_ceil` / `floor_rational` helpers it needs already exist in `branch.rs` (built in B1).

**Gating.** Keyed on integer-valuedness of the bounded var: `self.vars.is_int(var)` for a single problem var, or "all comb vars int" for a slack (true throughout a pure-Int query, since `new_var` marks `is_int` on each atom's vars just before `build_encoding`). Pure-Real atoms keep δ untouched; a mixed query is fenced to `unknown` before solving, so rounding it is harmless. Real-sorted disequalities/strict bounds are unchanged.

### 3.7 Proof certificate — resolving `solver.rs` `TODO(planB)`

The `SplitAtoms` arm in `crates/shinri-sat/src/solver.rs` carries a `TODO(planB)`: when arith emits real branch/cut Split clauses, decide whether they need proof-certificate emission. **Decision: cuts and branch lemmas are NOT recorded to the proof.** This is consistent with the milestone's explicit out-of-scope ("proof emission beyond Farkas conflicts", master spec §1). The soundness backstops are the debug re-derivation check (§3.5) and the two-stage differential (§4). The `TODO(planB)` comment is replaced with this recorded decision. (A branch clause `(x≤⌊v⌋ ∨ x≥⌈v⌉)` is valid over the integers; a unit cut clause is theory-valid by exact derivation — neither is a propositional tautology, so certifying them would require a theory-lemma proof channel that the milestone defers.)

### 3.8 The Stage-B gate

All three optimizations — GMI cuts (§3.1–3.3), FBBT (§3.4), and integer bound rounding (§3.6) — sit behind a single boolean **Stage-B gate** on `Arith` (default ON in production; the differential harness constructs both an OFF and an ON solver). With the gate OFF, `Arith` behaves byte-identically to B1: δ-reuse for integer strictness, no rounding, no FBBT, no cuts — i.e. the known-correct baseline. This makes the two-stage identity test (§4.1) a direct A/B over the same code.

### 3.9 Backtracking

Unchanged mechanism (B1 §3.7 / QF_LRA §9). Cut and branch **atoms** are append-only (never un-registered on backtrack); only their bound assertions are level-scoped and trail-stamped. FBBT and a-priori `M` bounds are level-0 and survive every backtrack. The per-node cut budget counter is reset on `pop`.

---

## 4. Test plan (the headline: re-enabled UNSAT differential)

### 4.1 Two-stage differential identity (`crates/shinri-solver/tests/oracle.rs`)

For every generated QF_LIA instance, run it through **two solvers** — Stage-B gate OFF (pure B1 baseline) and gate ON (cuts + FBBT + rounding) — and assert **identical** sat/unsat verdicts, and both identical to z3 + cvc5 where the oracles decide. A cut/FBBT/rounding bug cannot hide: it is checked against a procedure that uses none of them. This is master spec §9's Stage-A/Stage-B core de-risking strategy made into a single A/B harness.

### 4.2 Re-enabled UNSAT direction — curated tiers

Replace the `#[ignore]`'d UNSAT companion test with two tiers:

- **Tier 1 (hard guarantee):** a fixed, seeded small/medium corpus that must decide **every** UNSAT instance within the per-instance timeout — **zero** `oracle_unsat_skipped`, **zero** `shinri_timeout_skipped`. This is the test that proves cuts + FBBT collapse UNSAT (LP-infeasibility via Farkas, not box enumeration). The corpus is curated so it contains no instance no exact solver could close in budget.
- **Tier 2 (stress):** a larger/random corpus — the bulk (threshold, e.g. ≥95%) decided within budget; any residual timeout is **logged with the full instance dumped and counted**, never silently skipped. A `shinri=Unsat` on a `z3/cvc5=Sat` instance remains an **instant panic** (soundness), regardless of tier.

Both tiers keep the existing rule: our `Unknown` is never a disagreement, but assert pure-QF_LIA instances never go `Unknown` past the fence.

### 4.3 Unit

- **GMI validity:** over random fractional rows, the derived cut separates the current vertex and the independent re-derivation agrees (§3.5).
- **Cut → UNSAT via LP-infeasibility:** a known instance is decided UNSAT by cut-induced relaxation infeasibility (Farkas), not by enumeration (assert the node count stays small).
- **FBBT:** fixpoint termination + integer rounding correctness (`x ≤ 17/3 ⟹ x ≤ 5`); a constraint system whose box collapses to a point.
- **Budget exhaustion** falls back to a branch `Split` and still terminates.
- **Integer bound rounding:** `x < 5` (int) encodes directly to `x ≤ 4` with δ-coeff 0 and produces **no branch**; `2x ≤ 5` encodes to `x ≤ 2`; the negation polarity `¬(x < 5) ⟹ x ≥ 5`; a pure-**Real** `x < 5` still carries δ (rounding does not leak across the fence).

### 4.4 Self-check & property

- Self-check (already wired in `shinri-solver`): every `sat` integral model re-evaluated against all assertions; every `unsat` carries a Farkas conflict over the (possibly cut/branch) bound literals.
- Property: assert-then-`pop` observationally equivalent to never-asserted, **including cut and FBBT bounds**; cuts-on vs cuts-off agree on random feasible/infeasible systems (a property-test form of §4.1).

**Phase-gate alignment:** only `shinri-num` on the arithmetic shipping path; `num-bigint` / `num-rational` survive solely as the dev-only differential oracle deps.

---

## 5. Crate / file plan

**`shinri-arith`:**

| Module | Change |
|---|---|
| `cuts.rs` *(new)* | GMI cut derivation from a fractional tableau row (exact rational) + debug re-derivation check |
| `propagate.rs` *(new)* | FBBT level-0 bound tightening with integer rounding |
| `branch.rs` | Budget-aware cut-vs-branch selection helper (reuses most-fractional + Bland selection) |
| `lib.rs` (`integer_check`) | Cut-before-branch orchestration with per-node + global budgets |
| `lib.rs` (`seed_*` / `propagate`) | Call FBBT once at the level-0 seed, after `M` |
| `lib.rs` (`build_encoding`) | Integer bound rounding (§3.6); δ-coeff 0 for integer-valued vars, behind the Stage-B gate |
| `lib.rs` (`Arith` struct, `pop`) | Stage-B gate flag; cut budgets; per-node budget reset on `pop` |

**Cross-crate:**

| Crate | Change |
|---|---|
| `shinri-sat` (`solver.rs`) | Replace the `TODO(planB)` at the `SplitAtoms` arm with the §3.7 recorded decision (no behavior change) |
| `shinri-solver` (`tests/oracle.rs`) | Two-stage identity (gate OFF vs ON) + re-enabled tiered UNSAT differential |

**No splitting-seam change** — cuts ride the existing unit-`SplitAtoms` path (§2.1).

---

## 6. Risks & mitigations

| Risk | Mitigation |
|---|---|
| Wrong GMI cut excludes an integer solution (unsoundness) | Exact-rational derivation; cuts disable-able via the Stage-B gate; two-stage differential vs B1 baseline + z3/cvc5; debug re-derivation + separation check (§3.5) |
| Cut rounds stall / livelock | Per-node + global budgets; degenerate-row fallback to branch; box backstop carries termination independent of cuts |
| FBBT installs an unsound (too-tight) bound | Monotone tighten-only within the box; derived only from valid constraint implications; level-0 stripped sentinels; assert-then-pop property test |
| Integer bound rounding leaks into Real atoms | Per-var `is_int` gate; Real-still-carries-δ unit test; mixed queries fenced to `unknown` before solving |
| Tier-2 random instance genuinely intractable | Threshold + honest reporting (full instance dumped, counted) — never a silent skip; soundness panic still fires on any wrong verdict |
| Cut/branch lemmas not in the proof certificate | Explicit out-of-scope decision (§3.7) consistent with the milestone; debug re-derivation + differential are the soundness net |

---

## 7. Definition of done

- `cuts.rs` + `propagate.rs` land; **cuts, FBBT, and integer bound rounding** sit behind a single Stage-B gate. With the gate OFF, `Arith` behavior is byte-identical to B1 (δ-reuse, no rounding/FBBT/cuts) — B1's completeness and termination are unchanged.
- Cuts-ON produces **identical** sat/unsat verdicts to the B1 baseline and to z3 + cvc5 on the random QF_LIA corpus (§4.1).
- The re-enabled UNSAT differential is green on curated tiers: **Tier 1 zero skips**, **Tier 2 threshold-green with reported residuals** (§4.2).
- `solver.rs` `TODO(planB)` proof-certificate question resolved (§3.7).
- QF_UFLIA and mixed QF_LIRA still fenced to `unknown`; QF_LRA / QF_UFLRA paths unchanged.
- `cargo test --workspace` green; only `shinri-num` on the arithmetic shipping path.

---

## References

- Master QF_LIA design: `docs/superpowers/specs/2026-06-20-shinri-arith-lia-design.md` (§1.1 soundness architecture, §2 the seam, §4 check loop, §6 GMI cuts, §9 two-stage differential).
- Plan B1 (baseline): `docs/superpowers/specs/2026-06-21-shinri-lia-planB1-design.md` (§3.3 a-priori box, §3.4 fractional scan/branch, §3.5 δ-reuse + the deferred tightening task folded in here).
- QF_LRA design: `docs/superpowers/specs/2026-06-20-shinri-arith-design.md` (§5 check loop, §7 Farkas, §9 backtracking).
- Dutertre, de Moura. *A Fast Linear-Arithmetic Solver for DPLL(T).* CAV 2006.
- Barrett, Nieuwenhuis, Oliveras, Tinelli. *Splitting on Demand in Satisfiability Modulo Theories.* LPAR 2006.
- Gomory. *An algorithm for integer solutions to linear programs.* 1963; and the mixed-integer (GMI) refinement.
- Papadimitriou. *On the complexity of integer programming.* JACM 1981 (the a-priori bound / small-model property).
</content>
</invoke>
