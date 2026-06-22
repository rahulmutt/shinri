# shinri QF_UFLIA — Design (EUF + Linear Integer Arithmetic via Model-Based Theory Combination)

**The first time shinri's Nelson–Oppen framework is exercised by two real cooperating theories. The convex combination plumbing already exists (built for QF_UFLRA, never activated as a pair); QF_UFLIA adds Int-sorted term sharing plus the one thing integers genuinely need that rationals do not — non-convex arrangement reasoning. We do this with model-based theory combination (MBTC): at the Nelson–Oppen Sat fixpoint, any two shared Int variables that are equal in the arithmetic model but not yet decided in the shared equality engine are resolved by an integer trichotomy split `(= u v) ∨ (< u v) ∨ (> u v)`, reusing the existing splitting-on-demand machinery. Single milestone, sound and complete; mixed QF_LIRA stays fenced.**

- **Date:** 2026-06-22
- **Status:** Approved design — ready for implementation planning
- **Master design spec (north star):** `docs/superpowers/specs/2026-06-18-shinri-design.md`
- **Combination framework spec:** `docs/superpowers/specs/2026-06-19-shinri-theory-design.md` (the `Combiner`, `EqualityEngine`, `TheorySolver`, purification, `InterfaceSet` — built targeting QF_UFLRA)
- **Sibling theory specs:** `docs/superpowers/specs/2026-06-19-shinri-euf-qfuf-design.md` (EUF); `docs/superpowers/specs/2026-06-20-shinri-arith-lia-design.md` (QF_LIA) and its `planB1`/`planB2` successors (the post-B2 Arith this combines).
- **Successor:** QF_UFLRA is incidentally validated here but is never the headline target; mixed QF_LIRA remains a separate later milestone.

> **Design-history note.** An earlier draft of this spec staged the work as a "sound convex baseline that answers `unknown` on undecided arrangements" (Stage 1), then MBTC (Stage 2). Implementation planning showed the baseline does not work: the simplex parks every unconstrained variable at 0, so *incidental* model collisions (e.g. `x` and `f(x)` both 0 with no constraint between them) are pervasive. A guard that returns `unknown` on every model-equal-unmerged pair is sound but returns `unknown` on nearly all SAT instances; a narrower guard is unsound (it misses functional congruence); a precise guard must speculatively run the congruence closure — which is exactly the MBTC split. The staging was therefore a false economy. MBTC makes the *same* simple "model-equal ∧ unmerged" predicate correct, because a harmless collision costs one split that resolves immediately rather than a spurious `unknown`. We go straight to MBTC.

---

## 1. Scope & relationship to the milestone

QF_UFLIA combines **EUF** (uninterpreted functions and predicates, congruence closure) with **linear integer arithmetic** over a single shared equality engine. The combination *framework* — `Combiner<E, A>`, the shared `EqualityEngine`, `AtomRegistry`, purification, the bidirectional Nelson–Oppen fixpoint, model assembly, and the certificate protocol — is **already implemented** in `shinri-theory`. It was designed for QF_UFLRA and exercised by EUF (`Combiner<Euf, EmptyTheory>`) and Arith separately, but `Combiner<Euf, Arith>` has **never been activated as a pair**: its oracle test (`crates/shinri-theory/tests/oracle.rs:9`) is `#[ignore]`'d, annotated *"activates when `Combiner<Euf, Arith>` exists."*

This milestone activates that pairing for integers. Three pieces of real work:

1. **Route Int-sorted shared terms.** Today only Real-sorted terms join the shared set; Int-sorted UF applications (`f: Int→Int`) are not routed through congruence at all. This is a latent unsoundness: a pure-Int QF_UFLIA query is not fenced today, yet its Int `f`-apps are never shared, so the theories never exchange the equalities that make it sound.
2. **Make shared Int terms integral** in the arithmetic core (so the integer layer and the simplex treat `f`-app interface variables as integers).
3. **Non-convex arrangement reasoning via MBTC.** The interface-equality split that decides each undecided shared Int pair.

### 1.1 The non-convexity problem (why QF_UFLRA's plumbing is not enough)

The framework's `Arith::entailed_equalities` is *deduction-complete for individually-entailed equalities* even over ℤ (it probes `u>v` and `u<v`; if both are infeasible, `u=v` holds in every model). That is necessary but **not sufficient** for combination over integers, which are **non-convex**: LIA can entail a *disjunction* of equalities without entailing any single one.

Canonical witness:

```
Arith (Int):  1 ≤ x ≤ 2,  y = 1,  z = 2
EUF:          f(x) ≠ f(y),  f(x) ≠ f(z)
```

This is **UNSAT** (x must equal y or z, so congruence forces `f(x)=f(y)` or `f(x)=f(z)`, contradicting a disequality either way), but *no single equality is individually entailed*. An individual-equality fixpoint discovers nothing, so a convex-only combiner would wrongly answer **SAT**. The arithmetic theory entails the *disjunction* `x=y ∨ x=z`; resolving such disjunctions is arrangement reasoning, which MBTC supplies by splitting.

### 1.2 Why integers need splits but reals do not (verdict-soundness)

For convex, stably-infinite theories with disjoint signatures (EUF + LRA), the Nelson–Oppen theorem guarantees that propagating *entailed* equalities to a fixpoint and checking each theory consistent yields a **correct satisfiability verdict** — no arrangement guessing required. (Our internally-built model may not exhibit a witness, but the verdict is sound; this is why the existing QF_UFLRA tests pass without splits.) Integers break convexity, so the theorem fails and a correct verdict requires deciding the arrangement. **Therefore MBTC splits Int pairs only; Real pairs are never split** — QF_UFLRA stays split-free and verdict-sound, and pure-Int QF_UFLIA additionally gets a *valid model* because every Int arrangement is decided.

### 1.3 In scope

- Extend EUF↔Arith term sharing from Real-only to **{Real, Int}** (Int-sorted UF applications, problem-var interning, numeral pinning).
- Make shared Int terms integral in Arith (`ensure_shared_var` stamps Int-sortedness).
- An arith seam `model_equal_shared_pairs(shared) -> Vec<(TermId,TermId)>` reporting shared **Int** vars equal under the current model `β`.
- A combiner **MBTC step**: at the N-O Sat fixpoint, take the first model-equal pair not merged in the `EqualityEngine` and emit the trichotomy split `(= u v) ∨ (< u v) ∨ (> u v)` via the existing `TCheck::Split` → `TheoryResult::SplitAtoms` path.
- Generalize `Combiner::bind_fresh` to **classify** each fresh split atom and route it to the owning theory (so `(= u v)` reaches EUF and `(< u v)`/`(> u v)` reach Arith).
- Activate the `#[ignore]`'d combination oracle and add a `shinri-solver` end-to-end QF_UFLIA differential vs z3 (+ cvc5).

### 1.4 Explicitly out of scope (unchanged fences)

- **Mixed Int/Real in a single query** — the `lira` gate (`crates/shinri-solver/src/lib.rs`) stays; pure-Int and pure-Real queries are each supported, mixed is `unknown`.
- Nonlinear arithmetic, difference-logic specialization, eager theory propagation.
- Proof/certificate emission beyond the existing Farkas conflicts and the dev-gated `CertLog` structural re-check. Interface-equality split clauses are not proof-certified (consistent with the QF_LIA B2 decision that branch/cut lemmas are not certified).
- **QF_UFLRA** is incidentally validated by the shared plumbing but is never the headline target.

---

## 2. Design principles (inherited)

1. **Soundness is total.** A SAT/UNSAT verdict is returned only when justified; `unknown` only for genuinely unsupported constructs (nonlinear, mixed-sort, QF_LIRA). The combiner never guesses.
2. **One shared source of equality truth** — a single `EqualityEngine`; theories never exchange equalities behind it.
3. **Closed, monomorphized theory set** — `Combiner<Euf, Arith>`, enum-routed, no `dyn` on the hot path.
4. **Backtracking via `UndoLog`, never snapshots**, synchronized to SAT decision levels.
5. **Exact arithmetic only** (`shinri-num` rationals, `DeltaRational`).

---

## 3. The MBTC mechanism

### 3.1 Detecting undecided pairs

After the bidirectional N-O fixpoint reaches a Sat fixpoint (`drive_final_check`), the combiner asks Arith for `model_equal_shared_pairs(shared)`: the shared **Int** pairs `(u,v)` with `β(u)=β(v)` under the current model. A pair is **undecided** iff it is not already merged in the `EqualityEngine` (`!are_equal`). The naive predicate is correct here precisely because the action is a *split*, not an `unknown` (§ design-history note).

### 3.2 The integer trichotomy split

For the first undecided pair `(u,v)`, the combiner builds three atoms over `self.terms` and returns them as a split:

```
(= u v)   — EUF atom: routes to Owner::Euf
(< u v)   — Lt atom:  routes to Owner::Arith
(> u v)   — Gt atom:  routes to Owner::Arith
```

`drive_final_check` returns `FinalCheck::Split([eq, lt, gt])`; `Theory::check` lifts it to `TheoryResult::SplitAtoms`. The SAT loop (`crates/shinri-sat/src/solver.rs:580`) allocates a fresh Boolean var per atom, calls `bind_fresh` (which now classifies and routes each atom), learns the clause `(eq ∨ lt ∨ gt)`, and backtracks one level to force a case-split — exactly the QF_LIA splitting-on-demand protocol.

- The **`(= u v)`** branch → EUF merge → congruence closure → exchanged back to Arith by the existing N-O loop (so Arith installs `u=v`). EUF/Arith agree.
- The **`(< u v)`** / **`(> u v)`** branch → Arith bound → genuinely separates `u,v`; EUF leaves them unmerged (correct, since they are unequal).

The disjunction is the integer trichotomy, hence theory-valid: SAT must pick a branch.

### 3.3 Routing fresh atoms (`bind_fresh` generalization)

`Combiner::bind_fresh` (`combiner.rs:196`) currently hardcodes `Owner::Arith` (QF_LIA splits are always arith atoms). MBTC's `(= u v)` is an EUF atom, so `bind_fresh` must `classify(atom)` and register/encode it under the correct owner — `arith.new_var` for `Owner::Arith` (plus `euf.register_arith_uf_terms` to match `register_atom`), `euf.new_var` for `Owner::Euf`. This is behavior-preserving for existing QF_LIA splits (`(x≤k)`/`(x≥k)` classify to `Owner::Arith`).

---

## 4. Components

### 4.1 Sharing extension: Real → {Real, Int}  *(shinri-euf)*
- `Euf::shared_arith_terms` (renamed from `shared_real_terms`) — return registered terms of sort **Real or Int**.
- `Euf::walk_arith_uf_apps` (renamed from `walk_real_uf_apps`) — intern **Int**-sorted UF applications so congruence applies to `f: Int→Int`.

### 4.2 Arith seam  *(shinri-arith)*
- `ensure_shared_var` — stamp Int-sortedness (`problem_var_sorted`) so shared Int terms (incl. `f`-apps and numerals) are integral.
- `model_equal_shared_pairs(&mut self, shared) -> Vec<(TermId,TermId)>` (inherent) + a defaulted `TheorySolver` trait method (default returns none) + Arith override — Int-only, read-only over `β`, state-safe.

### 4.3 Combiner MBTC  *(shinri-theory)*
- `FinalCheck::Split` already exists; `drive_final_check` gains the §3.1–3.2 step at the terminal Sat point.
- `bind_fresh` generalized per §3.3.

### 4.4 Fences  *(shinri-solver — unchanged)*
Pure-Int QF_UFLIA is **not** fenced today (`saw_shared` flags only mixed-*sort* equalities, which pure-Int QF_UFLIA never produces); it already reaches `sat.solve()`. No fence change is required. The `saw_shared`, `lira`, and `classify→Unsupported` fences stay exactly as-is.

### 4.5 Model seam  *(shinri-theory — unchanged)*
`build_model::merge_check` already agrees on shared terms; EUF's `model` skips Real/Int (defers values to Arith). After MBTC decides every Int arrangement, the built model is valid for pure-Int QF_UFLIA.

---

## 5. Data flow per `check(Full)`

```
SAT assigns atoms
  → Combiner::assert (route by Owner; mirror equalities into EqualityEngine)
  → propagate fixpoint
  → drive_final_check:
        shared set S  (NOW Real + Int)
        ensure_shared_var ∀ t ∈ S  (intern problem vars / pin numerals / stamp Int)
        bidirectional fixpoint:
            Arith → EUF:  entailed_equalities(S)  → euf.consume_interface_equality
            EUF → Arith:  congruence classes of S → arith.consume_interface_equality
        at Sat fixpoint:
            undecided = first (u,v) ∈ model_equal_shared_pairs(S) with !are_equal(u,v)
            if undecided: FinalCheck::Split([ (=u v), (<u v), (>u v) ])  → SAT case-splits
            else:         Sat → build_model
  Conflict at any point → EqLeaf set → clause → backjump  (unchanged)
```

---

## 6. Soundness, termination, completeness

- **Stable infiniteness.** EUF and LIA-over-ℤ are stably infinite on their sorts, so N-O applies; the only obstacle is integer non-convexity, isolated into the MBTC split.
- **Soundness.** A SAT verdict is declared only when no undecided Int pair remains — i.e. every model-equal Int pair is merged (so congruence is respected) and no EUF-disequal pair is arith-equal (an equal-but-disequal pair is undecided → split → the `=` branch conflicts, forcing `<`/`>`). UNSAT comes from a theory conflict over `EqLeaf` antecedents (the existing path). Hence the verdict is sound and, for pure-Int queries, the built model is valid.
- **Termination.** The shared set is finite. Each split permanently decides one pair's relation (`=`/`<`/`>`); once decided, that pair is no longer model-equal-unmerged, so it is never re-split. The undecided set strictly shrinks → finitely many splits. (This mirrors the integer-branching split, which also emits one split per check.)
- **Completeness.** Every undecided arrangement is eventually decided by a split, so the combination explores all relevant arrangements; with EUF and LIA each complete, the verdict is decided. `unknown` is reserved for genuinely unsupported constructs only.

---

## 7. Risks & mitigations

| Risk | Mitigation |
| --- | --- |
| **Unsound SAT on a non-convex instance** (cardinal sin) | The MBTC split is the gatekeeper: SAT requires zero undecided Int pairs. The §1.1 witness is a permanent regression test asserting UNSAT |
| **`bind_fresh` mis-routes the EUF `=` atom** | Generalize to `classify`-based routing (§3.3); unit test that a fresh `(= u v)` registers under `Owner::Euf` and a fresh `(< u v)` under `Owner::Arith`; existing QF_LIA split tests guard the arith path |
| **Split non-termination / livelock** | One split per check; each decides a pair permanently; undecided set strictly shrinks (§6). A property/e2e test on a multi-pair instance confirms convergence |
| **Int interface sentinels leak into conflicts or survive backtracking** | Reuse the existing `iface_lit`/tag + R5 push/pop discipline already validated for Real; verification tests on the Int path |
| **Spurious extra splits from incidental 0-collisions** | Accepted: each costs one immediately-resolved split (not a wrong answer). If profiling shows blow-up, restrict candidate pairs to congruence-relevant ones later — an optimization, not a correctness need |
| **Commit-ordering unsoundness** | Land the arith seam, `bind_fresh`, and the MBTC split (all inert while the shared set has no Int terms) *before* flipping on Int sharing; every intermediate commit is sound |

---

## 8. Testing & Definition of Done

**Harness.** Activate the `#[ignore]`'d `crates/shinri-theory/tests/oracle.rs` (`Combiner<Euf, Arith>`) and add a `shinri-solver` end-to-end QF_UFLIA differential vs **z3 (+ cvc5)** on random well-typed instances. Any SAT/UNSAT disagreement is **P0**; `unknown` (only for unsupported constructs) is never a failure.

**Definition of done (outcome-anchored):**
1. The non-convexity witness (§1.1) returns **UNSAT** (the soundness headline — it was wrongly SAT before).
2. Curated convex/entailed witnesses return their definite verdicts (SAT and UNSAT): pinned-bounds congruence, non-fixed entailed equality, genuinely-SAT congruence, free-arrangement SAT.
3. The differential vs z3 (+ cvc5) on random QF_UFLIA agrees on every definite verdict across the corpus.
4. QF_UFLRA / QF_UF / QF_LIA suites are unchanged (Real pairs are never split; pure-Int QF_LIA has no shared EUF terms).

---

## 9. Build order

1. Arith seam: Int integrality in `ensure_shared_var` + `model_equal_shared_pairs` (Int-only) + trait method. *(inert)*
2. Combiner `bind_fresh` generalization (classify-based routing). *(inert / behavior-preserving)*
3. Combiner MBTC split in `drive_final_check`. *(inert until Int terms are shared)*
4. EUF Int-sorted sharing (rename + Real∨Int filter) — **activates** MBTC, soundly, because steps 1–3 are in place.
5. QF_UFLIA e2e witnesses (definite verdicts).
6. Differential oracle vs z3 (+ cvc5).

---

## 10. Summary

QF_UFLIA is the first activation of shinri's Nelson–Oppen framework as a real cooperating pair. The convex plumbing already exists; the milestone adds Int-sorted sharing, Int integrality, and isolates integer non-convexity into a single combiner-level MBTC step that decides each undecided shared-Int arrangement with an integer trichotomy split over the existing splitting-on-demand machinery. The result is sound and complete for pure-Int QF_UFLIA, leaves QF_UFLRA split-free and unchanged, and keeps mixed QF_LIRA and proof emission beyond Farkas fenced as separate later milestones.
