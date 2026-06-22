# shinri QF_UFLIA — Master Design (EUF + Linear Integer Arithmetic combination)

**The first time shinri's Nelson–Oppen combination framework is exercised by two real cooperating theories. The convex combination plumbing already exists (built for QF_UFLRA, never activated as a pair); QF_UFLIA adds Int-sorted term sharing and the one piece integers genuinely need that rationals do not — non-convex arrangement reasoning. Delivered in two stages: a sound, shippable convex baseline that answers `unknown` exactly when the shared-variable arrangement is undecided, then a model-based theory combination (MBTC) layer that removes those `unknown`s without changing any verdict the baseline already produced.**

- **Date:** 2026-06-22
- **Status:** Approved design — Stage 1 ready for implementation planning; Stage 2 specified, planned later
- **Master design spec (north star):** `docs/superpowers/specs/2026-06-18-shinri-design.md`
- **Combination framework spec:** `docs/superpowers/specs/2026-06-19-shinri-theory-design.md` (the `Combiner`, `EqualityEngine`, `TheorySolver`, purification, `InterfaceSet` — built targeting QF_UFLRA)
- **Sibling theory specs:** `docs/superpowers/specs/2026-06-19-shinri-euf-qfuf-design.md` (EUF), `docs/superpowers/specs/2026-06-20-shinri-arith-lia-design.md` (QF_LIA) and its `planB1`/`planB2` successors.
- **Predecessor:** the QF_LIA milestone (B1 complete baseline + B2 Stage-B cuts/FBBT) — the Arith theory this combines is the post-B2 solver.
- **Successor:** QF_UFLRA (incidentally validated here; never the headline target) and mixed QF_LIRA remain separate later milestones.

---

## 1. Scope & relationship to the milestone

QF_UFLIA combines **EUF** (uninterpreted functions and predicates, congruence closure) with **linear integer arithmetic** over a single shared equality engine. The combination *framework* — `Combiner<E, A>`, the shared `EqualityEngine`, `AtomRegistry`, purification, `InterfaceSet`, the bidirectional Nelson–Oppen fixpoint, model assembly, and the certificate protocol — is **already implemented** in `shinri-theory`. It was designed for QF_UFLRA and has been exercised by EUF (`Combiner<Euf, EmptyTheory>`) and by Arith separately, but `Combiner<Euf, Arith>` has **never been activated as a pair**: its oracle test (`crates/shinri-theory/tests/oracle.rs:9`) is `#[ignore]`'d, annotated *"activates when `Combiner<Euf, Arith>` exists."*

This milestone activates that pairing for integers. There are exactly two pieces of real work beyond turning it on:

1. **Route Int-sorted shared terms.** Today only Real-sorted terms join the shared set; Int-sorted UF applications (`f: Int→Int`) are not routed through congruence at all.
2. **Non-convex arrangement reasoning.** Integers are non-convex: LIA can entail a *disjunction* of equalities without entailing any single one, so the convex model-based / probe-based equality propagation the framework was built around is **incomplete** for ℤ. This is the only intellectually substantial part of the milestone.

### 1.1 The non-convexity problem (why QF_UFLRA's plumbing is not enough)

The framework's `Arith::entailed_equalities` is *deduction-complete for individually-entailed equalities* even over ℤ (it probes `u>v` and `u<v`; if both are infeasible, `u=v` holds in every model). That is necessary but **not sufficient** for combination, because integers are non-convex.

Canonical witness:

```
Arith (Int):  1 ≤ x ≤ 2,  y = 1,  z = 2
EUF:          f(x) ≠ f(y),  f(x) ≠ f(z)
```

This is **UNSAT**: x must equal y or z, so congruence forces `f(x)=f(y)` or `f(x)=f(z)`, contradicting a disequality either way. But *no single equality is individually entailed* — neither `x=y` nor `x=z` holds in all models — so an individual-equality fixpoint discovers nothing and a convex-only combiner would wrongly answer **SAT**. The arithmetic theory entails the *disjunction* `x=y ∨ x=z`; resolving such disjunctions is "arrangement reasoning."

### 1.2 In scope

- Extend EUF↔Arith term sharing from Real-only to **{Real, Int}** (Int-sorted UF applications, problem-var interning, numeral pinning, model seam).
- Narrow the current `saw_shared → unknown` fence so EUF↔Int-arith shared terms are **supported**, not fenced.
- A combiner-level **arrangement-completeness check** with one new arith seam (`model_equal_shared_pairs`).
- **Stage 1:** the check maps an undecided arrangement to a sound top-level **`unknown`** (new `FinalCheck::Incomplete` surfaced through the CDCL(T) loop).
- **Stage 2:** the check instead emits interface-equality **splits** via the existing `TCheck::Split` seam (MBTC), completing every verdict.
- A **Stage gate** (Stage-B style) so the differential harness can run guard→unknown (Stage 1) vs guard→split (Stage 2) and assert verdict preservation.
- Activate the `#[ignore]`'d combination oracle and add a `shinri-solver` end-to-end QF_UFLIA differential vs z3 + cvc5.

### 1.3 Explicitly out of scope (unchanged fences)

- **Mixed Int/Real in a single query** — the `lira` gate (`crates/shinri-solver/src/lib.rs`) stays; pure-Int and pure-Real queries are each supported, mixed is `unknown`.
- Nonlinear arithmetic, difference-logic specialization, eager theory propagation.
- Proof/certificate emission beyond the existing Farkas conflicts and the dev-gated `CertLog` structural re-check.
- **QF_UFLRA** is incidentally validated by the shared plumbing but is never the headline target; its own curated milestone (if desired) is separate.

---

## 2. Design principles (inherited)

Specializes the combination-framework principles (`shinri-theory` spec §2):

1. **Soundness is total at every stage; completeness is staged.** Stage 1 returns SAT/UNSAT *only* when the shared-variable arrangement is fully decided; otherwise `unknown`. It never guesses.
2. **One shared source of equality truth.** A single `EqualityEngine` holds equality state for both theories. Theories never exchange equalities pairwise behind the engine's back — the classic combination soundness bug.
3. **Closed, monomorphized theory set.** `Combiner<Euf, Arith>` is a concrete struct, enum-routed, no `dyn` on the hot path.
4. **Backtracking via `UndoLog`, never snapshots**, synchronized to SAT decision levels.
5. **Exact arithmetic only** (`shinri-num` rationals, `DeltaRational`).

---

## 3. The two stages

### 3.1 Stage 1 — Convex baseline (sound, may answer `unknown`)

Activates the pairing for integers and is independently shippable. Reuses the existing probe-based `entailed_equalities` and bidirectional fixpoint unchanged; adds Int sharing and the arrangement guard.

**Soundness mechanism — the arrangement-completeness guard.** After the bidirectional fixpoint reaches a Sat fixpoint, before SAT is declared: if any two shared Int variables share the current arithmetic model value `β(u)=β(v)` but are neither merged nor separated in the `EqualityEngine`, the arrangement is **undecided** → return `unknown`. Pure QF_UFLRA (convex) never trips the guard. The §1.1 non-convex witness trips it and answers `unknown` — sound, not unsound.

### 3.2 Stage 2 — Non-convex completion (MBTC)

Replaces the guard's `unknown` with **model-based theory combination**: each undecided pair `(u,v)` becomes an interface-equality split `(u=v) ∨ (u≠v)` surfaced by the combiner through the existing split machinery (the same clause-forwarding path `TCheck::Split` uses for integer branching; the combiner is the emitter here rather than Arith). The SAT solver case-splits; each branch routes back as an asserted equality or disequality through `Combiner::assert`, driving the arrangement to completeness lazily. The probe-based deduction remains underneath as a cheap pre-filter (it decides individually-entailed pairs without a split). This is the cvc5/Z3 approach.

### 3.3 The soundness contract (the through-line)

> Completeness is staged; **soundness is total at every stage.** Stage 1 produces SAT/UNSAT only when the shared-variable arrangement is fully decided by asserted + congruence + individually-entailed equalities; otherwise `unknown`. Stage 2 decides the remaining arrangements, changing **no** SAT/UNSAT verdict Stage 1 already produced — it only converts `unknown` into a definite verdict.

This gives Stage 2 a differential oracle for free: every Stage-1 SAT/UNSAT must be preserved, and Stage-2 turns Stage-1 `unknown`s into z3/cvc5-agreeing verdicts.

---

## 4. Components (Stage 1)

### 4.1 Sharing extension: Real → {Real, Int}  *(shinri-euf, shinri-arith)*

- `Euf::shared_real_terms` — also return **Int**-sorted registered terms (its role generalizes to "shared arith-sorted terms").
- `Euf::walk_real_uf_apps` / `register_arith_uf_terms` — intern **Int**-sorted UF applications into the e-graph so congruence applies to `f: Int→Int`.
- `Arith::ensure_shared_var` — intern a problem var for each Int-sorted shared term; pin Int numerals with fixed integer bounds (the existing Real numeral-pin path, generalized).
- `entailed_equalities` / `consume_interface_equality` (both directions) — already operate on problem vars and the `iface_lit`/tag sentinel discipline. Work item is verification, not new logic: confirm the Int path round-trips interface sentinels through `explain` as `EqLeaf::Interface(just)` and that push/pop drops tags above the target level (existing R5 backtrack discipline).

### 4.2 Fence narrowing  *(shinri-solver: tseitin.rs, lib.rs:264)*

`saw_shared` no longer forces `unknown` when the shared terms are EUF↔**Int-arith**. The `lira` (Int/Real mixed) gate and `classify → Unsupported` (nonlinear, mixed-sort) fences are untouched.

### 4.3 Arrangement-completeness check  *(shinri-theory: combiner.rs — the one new piece)*

A single helper, run after the fixpoint reaches Sat:

- `undecided_shared_pairs()` — a shared Int pair `(u,v)` is **undecided** iff arith's current β makes `β(u)=β(v)` but they are neither merged nor separated in the `EqualityEngine`.
- New arith seam: `Arith::model_equal_shared_pairs(&shared) -> Vec<(TermId, TermId)>` returns the shared pairs equal under the current β. The combiner intersects this with "not pinned in `EqualityEngine`" (which it computes itself via `find`/diseq lookup).
- **Stage 1** maps a non-empty undecided set → `FinalCheck::Incomplete`.
- **Stage 2** maps the same set → one or more `(u=v) ∨ (u≠v)` splits surfaced by the combiner through the existing split machinery.

Identical detection, different action — the staging seam lives entirely in this one decision.

### 4.4 `unknown` surfacing seam  *(shinri-sat / shinri-theory — the one new SAT-seam touch)*

Stage 1's `FinalCheck::Incomplete` must propagate up as a top-level `Unknown`. The CDCL(T) final-check path gains a distinguished give-up outcome that the loop translates to `Unknown` — **never** SAT. This is the single new interface touch in the SAT seam and the riskiest surface (§7).

### 4.5 Model seam for Int shared terms  *(shinri-theory: combiner.rs build_model)*

`build_model`'s `merge_check` must agree on Int-sorted shared terms: `f(x)` takes its `Num` value from arith and EUF must agree. Confirm EUF's `model()` skips Int (defers the value to arith), as it already does for Real, so `Elem` is assigned only to genuinely uninterpreted sorts.

---

## 5. Data flow per `check(Full)`

```
SAT assigns atoms
  → Combiner::assert  (route Euf/Arith by Owner; mirror equalities into EqualityEngine)
  → propagate fixpoint
  → drive_final_check:
        shared set S  (NOW Real + Int)
        ensure_shared_var for every t ∈ S  (intern problem vars; pin numerals)
        bidirectional fixpoint:
            Arith → EUF:  entailed_equalities(S)  → euf.consume_interface_equality
            EUF → Arith:  congruence classes of S → arith.consume_interface_equality
        at Sat fixpoint:
            undecided = undecided_shared_pairs()
            Stage 1:  undecided ≠ ∅  → FinalCheck::Incomplete  → top-level `unknown`
            Stage 2:  undecided ≠ ∅  → TCheck::Split (u=v ∨ u≠v) → SAT case-splits
            else:     Sat  → build_model (Int-aware seam)
  Conflict at any point → EqLeaf set → Combiner negates → clause → backjump  (unchanged)
```

---

## 6. Why this is sound and terminating

- **Stable infiniteness.** EUF and LIA-over-ℤ are both stably infinite on their sorts, so Nelson–Oppen combination applies. The *only* completeness obstacle is integer non-convexity, isolated entirely into §4.3 and resolved by MBTC in Stage 2.
- **Soundness (both stages).** A SAT verdict is declared only when the shared-variable arrangement is fully decided and both theory models agree on the seam (`build_model::merge_check`). An UNSAT verdict comes from a theory conflict packaged from `EqLeaf` antecedents — the existing, validated path. Stage 1 additionally refuses to declare SAT on an undecided arrangement (`unknown`).
- **Termination.** The shared set is finite; the bidirectional fixpoint's merges are monotone (classes only shrink, asserted pairs are skipped). Stage 2's MBTC splits range over a finite pair set and each split permanently decides one pair, so the arrangement search cannot loop.

---

## 7. Risks & mitigations

| Risk | Mitigation |
| --- | --- |
| **`FinalCheck::Incomplete` → `Unknown` plumbing** is a new SAT-seam outcome (§4.4) — riskiest surface | Minimal, additive variant; dedicated unit test that a known non-convex instance reaches the give-up path and the solver reports `unknown` (not SAT, not a panic) |
| **Unsound SAT on a non-convex instance** (the cardinal sin) | The arrangement guard is the gatekeeper: SAT requires an empty undecided set. The §1.1 witness is a permanent regression test asserting `unknown` (Stage 1) / correct verdict (Stage 2) |
| **Random QF_UFLIA skews convex** → the guard rarely fires → weak non-convex coverage | A **curated non-convex tier** (the `1≤x≤2 ∧ y=1 ∧ z=2` + `f(x)≠f(y) ∧ f(x)≠f(z)` family and relatives), consistent with the project's existing tier-curation practice |
| **Int interface sentinels** leak into conflicts or survive backtracking | Reuse the existing `iface_lit`/tag + R5 push/pop discipline already validated for Real; verification tests on the Int path |
| **Model seam disagreement** on Int shared terms | `build_model::merge_check` debug-assert already guards this for Real; extend coverage to Int-sorted `f`-apps |
| **MBTC split explosion** (Stage 2) | Splits only on model-equal-but-unpinned pairs (lazy); probe deduction pre-filters individually-entailed pairs so they never split |

---

## 8. Testing & Definition of Done

**Harness.** Activate the `#[ignore]`'d `crates/shinri-theory/tests/oracle.rs` (`Combiner<Euf, Arith>`) and add a `shinri-solver` end-to-end QF_UFLIA differential vs **z3 + cvc5** on random well-typed instances. `unknown` is **never** a failure; any SAT/UNSAT disagreement is a **P0** bug.

**Stage 1 DoD (outcome-anchored):**
1. Convex / individually-decided QF_UFLIA corpus — **SAT and UNSAT** both green vs z3 + cvc5.
2. A curated **non-convex tier** (§1.1 family) — Stage 1 returns **`unknown`**, asserted by a dedicated test. This proves the guard *fires* rather than guessing — the soundness headline of the stage.
3. QF_UFLRA convex cases incidentally green (free validation of the shared plumbing).

**Stage 2 DoD (outcome-anchored):**
1. The curated non-convex tier flips `unknown` → z3/cvc5-agreeing verdict (SAT and UNSAT both represented).
2. A **Stage-1-gate-off vs Stage-2-gate-on two-stage differential** (B1/B2 style) asserts **every Stage-1 SAT/UNSAT verdict is preserved** and only `unknown`s change.

**Gate.** A Stage-B-style on/off gate selects guard→unknown (Stage 1) vs guard→split (Stage 2), so the two-stage differential above is mechanically expressible.

---

## 9. Build order (Stage 1)

1. Int-sorted term sharing (§4.1) — EUF interning + Arith `ensure_shared_var`/numeral pin; unit tests on `f: Int→Int` congruence and Int numeral pinning.
2. Fence narrowing (§4.2) — EUF↔Int-arith no longer `saw_shared`-fenced; `lira` and `Unsupported` fences preserved (regression test).
3. Arrangement-completeness check (§4.3) + `model_equal_shared_pairs` seam.
4. `FinalCheck::Incomplete` → `Unknown` surfacing (§4.4) — the SAT-seam touch, with its dedicated test.
5. Int-aware model seam (§4.5).
6. Activate the combination oracle + end-to-end differential (§8); curate the convex and non-convex tiers.

Stage 2 (MBTC) is planned separately once Stage 1 is green.

---

## 10. Summary

QF_UFLIA is the first activation of shinri's Nelson–Oppen framework as a real cooperating pair. The convex combination plumbing already exists; the milestone adds Int-sorted sharing and isolates integer non-convexity into a single combiner-level arrangement check. Stage 1 ships a sound solver that answers `unknown` exactly when the arrangement is undecided; Stage 2 (MBTC, via the existing `TCheck::Split` seam) removes those `unknown`s while provably preserving every Stage-1 verdict. Soundness is total throughout; mixed QF_LIRA and proof emission beyond Farkas remain fenced as separate later milestones.
