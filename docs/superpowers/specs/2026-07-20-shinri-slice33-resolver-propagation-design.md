# Slice 33 — resolver propagation outcome

**Status:** design
**Date:** 2026-07-20
**Predecessor:** slice 32 (HALTED, wall-3 diagnosis retracted in `55257542`)

## 1. Problem

`StepResult` (`crates/shinri-str/src/wordeq.rs:6-24`) has four variants —
`Done`, `Saturated`, `Conflict`, `Split`. **There is no propagation outcome.**

The resolver therefore cannot express "this equation entails `y ≈ "ab"`". A
residual pure assignment `[y] = ["ab"]` falls through the strip, occurs-check,
and all-constant cases to the variable-headed F-split path
(`wordeq.rs:~717`), and on a dedup hit returns `Saturated` → a sound
`Unknown`.

This is the gap slice 32's retraction identified by measurement. Probes C, E,
and G supply the emptiness fact by three increasingly generous routes — an
explicit `len(x) = 0` literal, a source-level `""`, and a hand-asserted
`x = ""` — and the pin remains `unknown` in all three. Access to the fact was
never the binding constraint. Probe F confirms the contradiction machinery is
intact once the equality exists. The gap is downstream of the seam and it is
structural.

Emptiness, length, arithmetic, and the Nelson–Oppen seam are all uninvolved.
This slice does not resume wall 3.

## 2. Scope

**In scope.** A propagation outcome for the narrowest sound shape: the
residual is a single variable `v` on one side and an **all-constant** word `W`
on the other.

**Out of scope.** The wider rule `v ≈ W` where `W` contains other variables
but not `v`. That is the shape the deleted E1 probe got wrong, and it needs
the occurs-check and the flattened-CONCAT-vs-free-variable distinction to be
airtight. Deferred until the citation discipline here is proven.

Also out of scope: grounding `len(x) = 0` to `x ≈ ""` (the retracted seam),
slice-31 §11 walls 1/2/4, and the order preprocessing fence, which stays
**down**.

## 3. Mechanism

`StepResult` gains a fifth variant:

```rust
/// The equation entails the pure assignment `var ≈ word`, where `word` is an
/// all-constant flattened residual. Unlike `Done`, this does not claim the
/// equation is resolved — it reports an entailed fact that the caller merges
/// into EUF with `just` as its antecedent set.
Propagate { var: TermId, word: TermId, just: Vec<EqLeaf> },
```

`resolve_equation` returns it after prefix/suffix stripping and the occurs and
all-constant checks, when one residual is a single term with no
`string_const_value` and the other is entirely constant.

`word` is a **single string constant**, not a residual slice: when the
constant side has several atoms (`["a", "b"]`), the resolver concatenates
their values and interns one constant term (`"ab"`). Merging `var` against a
multi-atom CONCAT term would make the merge depend on that term's own
normal form, reintroducing the substitution dependency §4 exists to bound.
The empty constant side (`v ≈ ""`) is included and interns the empty string
constant.

**Placement is the fix.** The check sits *before* the variable-headed F-split
path at `wordeq.rs:~717`. Today that shape reaches F-split → dedup →
`Saturated`; the whole defect is that ordering.

**This is not the deleted E1 probe.** The probe (`wordeq.rs:497`) returned
`Done` — it claimed resolution and cited nothing. This variant claims a *fact*
and carries its antecedents. It also fixes the probe's other defect: the
all-constant test runs on the **flattened** atoms, so an unflattened CONCAT
representative can never be mistaken for a free variable. The wrapper already
flattens; the spec makes it a stated precondition rather than an incidental
mitigation.

## 4. Citation discipline

This is the load-bearing soundness argument. An under-cited merge is exactly
the ce2 wrong-UNSAT shape, which this codebase has hit twice.

The driver (`lib.rs:~693`) currently calls the resolver with
`just = vec![EqLeaf::Asserted(lit)]` and discards normal-form antecedents,
justified by the comment at `lib.rs:692`: *"`resolve_equation` never derives a
ground conflict from a variable it substituted by a concat class
representative … so no extra merge-antecedent citation is needed here."*

**A propagation outcome falsifies that premise.** It derives a ground fact
precisely from substituted material. The comment must be revised, not worked
around.

The driver therefore:

1. Calls `normal_form_cited` (`normalize.rs:97-103`) with a **live** `ante`
   vector rather than discarding it. This mirrors the established in-repo
   precedent at `lib.rs:805-810`, where the disequality path derives a fact
   from merge-substituted normal forms and cites the substitution antecedents
   via `eq.explain`.
2. Allocates a fresh tag and stores `Asserted(lit) ++ ante` in a tag-indexed
   side table on `StrSolver`.
3. Calls `cx.eq.merge(v, W, EqJust::Interface(TheoryJust { theory:
   StrSolver::THEORY_ID, tag }))`.

`EqJust::Interface` is documented (`types.rs:46-47`) as exactly this hook: "an
equality another theory derived; expandable via that theory's `explain`". It
is required because `merge` takes a **single** `EqJust`, so a multi-antecedent
justification cannot be expressed as a bare `Asserted`.

### 4.1 `StrSolver::explain`

`StrSolver::explain` (`lib.rs:1214-1219`) is today a `debug_assert!(false)`
stub — string theory has never minted a self-tagged interface leaf. Slice 33
is the first, so `explain` gains a real implementation: look the tag up in the
side table and push its leaves into the `Explainer`.

The Combiner side is already built and dormant: `combiner.rs:900-901` routes
`j.theory == S::THEORY_ID` to `self.string.explain`, inside a `visited`-guarded
loop that terminates on the justification DAG. No Combiner change is needed
for dispatch.

### 4.2 Tag lifecycle

The side table truncates on `pop` through the existing trail mechanism
(`lib.rs:1225-1232`, which already scopes `eq_true` / `diseq_true` /
`memb_true` / `order_true` by recording lengths on `push`). Tags never outlive
the branch that minted them.

An under-truncated table is a stale-antecedent wrong-UNSAT. This gets a
dedicated backtracking test; the trail is not trusted by inspection alone.

## 5. Why E1 does not apply

Slice 32 halted because its emitted 2-literal clauses poisoned E1's
`input_cond_roots` — a gate, not a budget.

This mechanism **mints no atom and learns no clause**, so there is nothing for
`input_cond_roots` or `all_cond_roots` to gate. Branch-locality is handled
structurally by `EqualityEngine::push`/`pop` (`eq_engine.rs:456,463`) rather
than by a gate, and any conflict derived downstream expands through `explain`
to real input literals. That combination — backtrack-scoped merge plus
complete antecedent expansion — is what makes this safe where a globally
learnt, singly-cited fact was not.

This is the "direct read" posture the comment at `lib.rs:546-548` already
describes, applied to the resolver rather than the length seam.

## 6. Conflict path

`EqualityEngine::merge` (`eq_engine.rs:182-196`) returns `Err(EqConflict)`
when it unites a known-disequal pair. That is exactly the target shape:
merging `y ≈ "ab"` against an asserted `distinct y "ab"` conflicts inside the
engine.

The driver maps `Err(EqConflict)` to `TCheck::Conflict` with the expanded
explanation. No new conflict machinery is introduced — probe F already proved
that path intact.

## 7. Acceptance — measured, not inherited

The retraction is explicit that the pin must be chosen by measurement rather
than inherited from slice-31 §11. **Task 1 is a measurement task** that runs
the probes against the branch before any pin is written.

Predictions, to be confirmed or falsified:

| Probe | Query | Today | Predicted | Rationale |
|---|---|---|---|---|
| E | `(= (str.++ "" y) "ab") ∧ (distinct y "ab")` | `unknown` | `unsat` | normalizes to `[y] = ["ab"]` → propagate → EUF diseq conflict |
| G | `(= x "") ∧ (= (str.++ x y) "ab") ∧ (distinct y "ab")` | `unknown` | `unsat` | the `x = ""` merge rewrites the normal form to `[y]`; same path |
| C | `(= (str.len x) 0) ∧ (= (str.++ x y) "ab") ∧ (distinct y "ab")` | `unknown` | **`unknown`** | needs `len = 0 → x ≈ ""` grounding — the retracted seam, out of scope |

Probe C remaining `unknown` is a **stated non-goal**, not a failure.

If T1 falsifies E or G, the slice re-scopes at that point rather than after
five tasks of implementation.

`Unknown → decided` is an allowed completeness gain. Every newly-decided probe
must be oracle-confirmed before it is pinned.

## 8. Testing

- **Oracle differential** on every newly-decided probe, run as
  `cargo nextest run -p shinri-solver --features oracle`. Without that flag
  the suite silently runs **zero** tests; a zero-test run is never reported as
  coverage.
- **Test selection** uses `-E 'test(name)'`, and discovery count is confirmed
  before any run is called green.
- **Backtracking test** for the tag side table: mint a propagation tag at
  `dl > 0`, pop, and assert the tag is gone and no stale antecedent survives.
- **Regression:** the pins the deleted E1 probe once broke —
  `variable_equals_constant_splits_then_sat` and the
  `str_input_var_concat_length_*` family — must stay green, as must the
  t8iter175 SAT result.
- **`script_e2e`** runs locally pre-push, since this slice shifts
  completeness.
- All fast-tier; nothing here approaches the 5-minute exhaustive threshold.
- `cargo fmt --all` and `cargo clippy --workspace --all-targets -- -D warnings`
  before pushing.

## 9. Risks

1. **First self-tagged string interface leaf.** The tag lifecycle is new code
   on a hot path. Mitigated by the dedicated backtracking test (§8) and by
   scoping the table through the existing, already-exercised trail.
2. **The retraction-leak net does not cover this.** `combiner.rs:442`
   documents that `EqJust::Interface` justifications are **not swept** by the
   `cited_lits` debug hook — "an arith-side retraction leak would pass
   silently". The safety net that would catch a stale tag does not currently
   see interface justifications. Extending `cited_lits` to sweep the new table
   is in scope for this slice.
3. **Widening pressure.** The constant-word restriction (§2) will look
   arbitrary once it works. It is not: the wider rule reintroduces the E1
   probe's failure mode. Widening is a separate slice with its own
   measurement.

## 10. Non-goals

- Grounding `len(x) = 0` to `x ≈ ""` (retracted wall 3).
- Lifting the order preprocessing fence.
- Slice-31 §11 walls 1, 2, and 4.
- The standing bank (slice-28 §8, slice-27 typed-antecedent refactor,
  slice-29 approach-C) carries forward unchanged.
