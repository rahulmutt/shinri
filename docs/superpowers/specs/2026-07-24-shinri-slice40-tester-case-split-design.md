# Slice 40 — Datatype tester case-splitting (lifting the completeness fence)

**Status:** design
**Date:** 2026-07-24
**Area:** `shinri-dt` (`DtSolver::check`, `model`); no new crates, no new
`Combiner` slot, no new `shinri-core`/`shinri-parser` surface.
**Predecessors:** slice 39 (datatypes foundation) — spine, parser,
Combiner 5th slot, selector-collapse, injectivity, disjointness, tester
consistency, and the §5.2 completeness fence this slice replaces.

## 1. Summary

Slice 39 landed a sound datatype theory that decides `unsat` fully but refuses
to claim `sat` whenever a watched datatype e-class is *constructor-undetermined*
— it returns `TCheck::Unknown` behind the §5.2 completeness fence. The missing
ingredient is **exhaustiveness**: the fact that every datatype term *is some
constructor*, which is precisely the direction that requires a case split.

Slice 40 supplies that case split. It adds two rules to `DtSolver::check`:

1. **Exhaustiveness split** — for a demanded, undetermined class of term
   `t : D`, emit the tester disjunction `is-C₁(t) ∨ … ∨ is-Cₙ(t)`.
2. **Constructor instantiation** — once SAT decides `is-C(t)`, emit the guarded
   lemma `is-C(t) ⇒ t = C(sel₁(t), …, selₙ(t))`.

Both use the pre-existing `TCheck::Split` machinery; the `assert`-side tester
disjointness from slice 39 already supplies at-most-one, so SAT sees a genuine
exactly-one branch.

**The fence is replaced, not deleted.** Acyclicity is slice 41 and finiteness is
slice 42, so slice 40 cannot yet claim `sat` on every determined state without
risking a wrong answer on cyclic constraints (§4). Slice 40 therefore trades the
coarse slice-39 fence ("any undetermined class → `Unknown`") for a **finer,
model-tied fence**: it reports `sat` only when a finite acyclic ground model
actually exists, and returns `Unknown` on the residual (cyclic / unbounded)
cases that slices 41–42 later resolve. Within that fence slice 40 decides the
full non-cyclic QF_DT fragment end to end.

## 2. Representation — nothing new

Slice 40 introduces no new sorts, ops, registry fields, or parser surface. It
reuses everything slice 39 built:

- `DatatypeRegistry` accessors `dt_constructors(sort) → &[SymbolId]`,
  `dt_selectors(ctor) → &[SymbolId]`, `dt_tester(ctor) → SymbolId`, and the
  reverse-dependency map (datatype sort → constructors taking it as an argument,
  `context.rs:1275`) for the occurs-check (§4).
- `Context::mk_app(Op::Uninterpreted(sym), &args)` to mint tester, selector, and
  constructor applications — the same minting `instantiate_injectivity_selectors`
  already performs.
- `TCheck::Split { atoms, guard, phases }`, unchanged; `guard: None` for the
  exhaustiveness tautology, `guard: Some(¬is-C(t))` for the guarded instantiation
  lemma (the same shape the string theory uses).

`DtSolver` still owns no equality state, never merges, and implements no N-O
exchange hooks — it remains a pure lemma-on-demand theory, structurally like
`shinri-arrays`.

## 3. The two rules

Both fire in `DtSolver::check` at `Effort::Full`, **after** the slice-39 rules
(constructor clash, injectivity instantiation, selector-collapse, tester
tautology) have saturated. Ordering matters: the definitional rules must run
first, so the case split only fires on a class those rules cannot resolve.

### 3.1 Exhaustiveness split (demand-driven)

When no slice-39 rule fires, scan watched datatype terms for a class that is
**undetermined** (`ctor_of_class` returns `None`) and **demanded** — at least one
of:

- a selector is applied to a member of the class, or
- a tester (positive **or** negative) mentions the class, or
- the class is otherwise blocking the final `sat` verdict — a watched datatype
  term still undetermined when every other rule has saturated.

The third condition is what actually lifts the fence: a bare `x : List` under
`¬is-nil(x) ∧ ¬is-cons(x)` has only negative testers (which `assert` treats as
no-ops in slice 39), yet must be split to expose the exhaustiveness conflict.
"Demanded" is therefore, in practice, "reachable from the problem and needed to
determine a model" — introduced selector children are split only once they in
turn become demanded, which is what bounds descent (§4).

For the first such class, of term `t : D`, emit **one** split:

```text
Split {
  atoms:  [ is-C₁(t), …, is-Cₙ(t) ],   // Cᵢ ∈ dt_constructors(sort_of(t))
  guard:  None,                          // exhaustiveness is a T-tautology
  phases: [ …nullary-first bias… ],      // §5.D, heuristic only
}
```

built as `is-Cᵢ(t) = mk_app(Uninterpreted(dt_tester(Cᵢ)), &[t])`. One split per
`check`; the Combiner's existing drain loop re-invokes `check`, exactly as
slice-39 collapse lemmas already rely on. At-most-one is already enforced by the
slice-39 tester-disjointness rule in `assert`, so the learnt clause plus that
rule together present SAT with an exactly-one-constructor decision.

### 3.2 Constructor instantiation (guarded)

When a class has an **asserted** `is-C(t)` but still holds no constructor
application, mint the constructor's fields and emit the conditional definition:

```text
Split {
  atoms: [ t = C(sel₁(t), …, selₙ(t)) ],  // selᵢ = dt_selectors(C)
  guard: Some(¬is-C(t)),                    // clause: (¬is-C(t) ∨ t = C(sel(t)…))
  phases: [],
}
```

The minted `selᵢ(t)` children register as watched datatype terms (mirroring
`instantiate_injectivity_selectors`), so each becomes eligible for its own
exhaustiveness split on a later `check` — **but only if itself demanded**.
Nullary constructors have no fields and bottom out immediately: that is the
finite descent that terminates every acyclic problem.

Once the constructor application `C(sel(t)…)` lands in `t`'s class, the slice-39
selector-collapse rule fires on it (`selᵢ(C(sel(t)…)) = selᵢ(t)`) and the class
is now constructor-determined for `ctor_of_class`, model construction, and the
fence.

## 4. Termination and the model-tied residual fence

Acyclicity is slice 41. Without it, a determined class is **not** sufficient for
`sat`: consider `x = cons(h, x)`. Instantiation gives
`x = cons(head(x), tail(x))`; congruence and injectivity force `tail(x) ≡ x`, so
`x`'s class stays constructor-determined and every slice-39/40 rule is
satisfied — yet the constraint is **unsat by acyclicity**, and its only ground
"model" is the infinite term `(cons h (cons h …))`. Reporting `sat` here would be
a wrong-`sat`.

The slice-39 fence ("any undetermined class → `Unknown`") is therefore replaced
by a finer, **model-tied** fence in `check`:

1. If a demanded undetermined class remains → emit its exhaustiveness split
   (progress — *not* `Unknown`).
2. When no rule fires and every demanded class is determined, run a read-only
   **occurs-check over the runtime constructor graph** of the determined
   classes: from a class holding `C(a₁…aₙ)`, follow each datatype-sorted field
   `aᵢ` to *its* class's constructor, and so on. A class reachable from itself is
   a cycle → no finite ground model exists on this branch → return **`Unknown`**.
   The static reverse-dependency map (`context.rs:1275`, sort → constructors that
   can recursively contain the sort) is available to *prune* — a sort that cannot
   recursively contain itself needs no walk — but the cycle detection itself is
   over the e-class argument graph, not the static map.
3. Otherwise → `Sat`.

Termination: the exhaustiveness split only ever fires on *demanded* classes, and
each firing either (a) determines a class via a nullary constructor (descent
stops) or (b) introduces selector children that are split only when themselves
demanded. An acyclic finite problem thus produces finitely many splits. A cyclic
problem is caught by step 2 and answered `Unknown` in finitely many steps rather
than diverging.

**Shared cycle detector.** The `depth > 64` defensive bail in
`render_value` (slice 39) is replaced by a real visited-set, so the fence
(step 2) and model construction (§5.C) share one honest occurs-check instead of
an arbitrary depth cap.

**Slice boundary.** This is the crisp seam with later work:

| Slice | Same cycle traversal, different verdict |
|---|---|
| 40 (this) | Cycle found → `Unknown` (sound, incomplete: "no finite model I can build") |
| 41 | Cycle found → `unsat` with a cycle-explanation conflict clause |
| 42 | Undetermined infinite-sort term may be left *free* → removes residual `Unknown` |

So `x = cons(h, x)` returns `unknown` in slice 40 and flips to `unsat` in slice
41 — a documented, adjudicated flip, not a regression (per the project's
completeness-shifting discipline).

## 5. Model, phase preference, wiring

### 5.C Model construction

`DtSolver::model` already renders a class's ground constructor term recursively.
Two changes:

1. The `depth > 64` bail becomes the shared visited-set occurs-check (§4). A
   cycle cannot reach `model` in a sound run — the fence returned `Unknown`
   first — but the guard remains as defense-in-depth and now fails *safe with a
   reason* (a detected cycle) rather than at an arbitrary depth.
2. The slice-39 branch that filled a class determined *only* by an asserted
   tester (no constructor application) is now unreachable at `sat` time:
   instantiation (§3.2) mints the constructor application before the fence
   clears. That branch is asserted unreachable. Net: every class rendered at
   `sat` is a fully-determined finite ground term.

### 5.D Phase preference (heuristic, recommended)

Populate the exhaustiveness split's `phases` vector to bias SAT toward **nullary
constructors first** (`nil` before `cons`). This steers search toward finite
models and cuts needless recursive descent. It is a heuristic only — soundness
and completeness do not depend on it — and reuses the existing `phases` channel
and the slice-31b phase-preference precedent. Included in slice 40; trivially
droppable.

### 5.E Wiring

Minimal. The Combiner already routes datatype atoms to `Owner::Datatypes` and
drains splits (slice 39). Testers minted by §3.1 flow through `new_var`/`collect`
and become watched when their split clause is learnt, so no explicit
registration is added. No new `Combiner` slot, no N-O hooks. `DtSolver::explain`
still handles only its own conflict tags (unchanged; slice 41 adds the
cycle-explanation tag).

## 6. Testing

Follows slice-39 §7 and the project's standing gates.

- **Unit tests (`shinri-dt`, hand-built `EqualityEngine`/`TheoryCtx`):**
  - exhaustiveness split emits the full tester disjunction for a demanded,
    undetermined class, and does *not* fire on a determined one;
  - constructor instantiation emits the guarded `t = C(sel(t)…)` and registers
    the selector children as watched;
  - nullary bottom-out (a class split to `nil` needs no further split);
  - the occurs-check fence returns `Unknown` on `x = cons(_, x)` and `Sat` on a
    finite determined model.
- **End-to-end `.smt2` (`shinri-solver`):**
  - `¬is-nil(x) ∧ ¬is-cons(x)` now decides **`unsat`** (was `unknown` — the
    fence-lift);
  - a `sat` problem that requires instantiation to build the model;
  - a mutually-recursive datatype group;
  - **one pinned `unknown`** for `x = cons(h, x)`, commented to document the
    residual acyclicity fence and that slice 41 flips it to `unsat`.
- **Oracle differential vs z3 + cvc5** (both support QF_DT), feature-gated:
  `cargo nextest run -p shinri-solver --features oracle`. Baked into the plan —
  **without `--features oracle` the suite silently runs zero tests** and reads as
  green.
- **Fuzz:** seed the `parse_script` / solve corpus with datatype scripts that
  exercise the new split and instantiation paths.
- **Gates:** `script_e2e` runs locally pre-push (this slice shifts
  completeness); `cargo fmt --all` before pushing (CI `fmt --check` fails fast);
  `mise run lint` clean (clippy `-D warnings`).

All additions are small and fast — no exhaustive suites — so the blocking PR
tier budget (10–15 min) is unaffected.

## 7. Scope — explicitly out of slice 40

Kept as residual `Unknown` or untouched trait defaults, for the slices that own
them:

| Deferred | Owner |
|---|---|
| Cycle → `unsat` with occurs-check conflict explanation | 41 |
| Finiteness / cardinality; leaving infinite-sort terms free (removes residual `Unknown`) | 42 |
| Nelson–Oppen exchange for Int/Real datatype fields (QF_UFDTLIA) | 43 |

## 8. Success criteria

- `¬is-nil(x) ∧ ¬is-cons(x)` and analogous exhaustiveness-only queries decide
  `unsat`; the slice-39 pinned-`unknown` end-to-end cases that were blocked
  *only* by exhaustiveness now decide.
- No wrong-`sat`: `x = cons(h, x)` and other cyclic constraints return `unknown`
  (not `sat`), verified by unit test and by the oracle differential (z3/cvc5
  return `unsat`; `unknown` is a sound under-approximation, never a `sat`
  mismatch).
- Oracle differential over a QF_DT corpus shows no `sat`/`unsat` disagreement
  with z3 or cvc5 (only slice-40 `unknown` where the residual fence applies).
- Termination on the acyclic fragment (finite splits); the fuzz corpus finds no
  panic or non-termination on hostile datatype input.
- `mise run ci` green; `script_e2e` and `fmt --check` clean pre-push.
