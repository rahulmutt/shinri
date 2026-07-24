# Slice 42 — Pruning Nelson–Oppen probes over unconstrained shared vars

**Status:** design
**Date:** 2026-07-24
**Area:** `shinri-arith` (`entailed_equalities`, `model_equal_shared_pairs`, and
the entry points that constrain a problem var). No `Combiner` change, no
`shinri-dt` change, no new crates, no `shinri-core`/`shinri-parser` surface, no
new theory slot.
**Predecessors:** slice 40 (tester case-splitting) minted the selector
applications that expose this; slice 41 (acyclicity) left `DtSolver` in its
current shape. Neither is modified here.

## 1. Summary

A datatype whose constructor has an `Int` field makes every QF_DT query
quadratically expensive in the number of datatype terms, **even when the formula
contains no arithmetic atom at all**.

`DtSolver::instantiate_constructor` mints one selector application `head(t)` per
constructor instantiation. Those are `Int`-sorted uninterpreted applications, so
`Euf::shared_arith_terms` (`shinri-euf/src/solver.rs:235`) — which filters
registered terms by **sort alone** — sweeps every one of them into the
Nelson–Oppen shared set `S`. Arith is then asked, once per exchange round, which
equalities over `S` it entails. Every one of those terms is an unconstrained
fresh problem var sitting at β = 0, so `entailed_equalities`' same-β pre-filter
(`shinri-arith/src/lib.rs:591`) admits **every pair**, and each pair costs a
slack definition plus two simplex probes. None can ever succeed.

Measured on a chain of `n` nested `((_ is nil) (tail …))` constraints:

| n | 12 | 16 | 20 | 24 |
|---|---|---|---|---|
| `(cons (head Int) (tail List))` | 0.76 s | 3.1 s | 9.4 s | 24.1 s |
| `(cons (head U) (tail List))`, `U` uninterpreted | — | — | 6 ms | — |
| `(cons (tail List))`, no field | — | — | 5 ms | — |

**A ≈1600× slowdown at n = 20 attributable solely to the field's sort** (9.4 s
vs 6 ms against the uninterpreted-field baseline — same term count, same
structure, same number of DT lemmas).
Instrumentation confirms the location: 100 % of wall-clock is inside
`Combiner::check` at `Effort::Full` across only 123 calls (≈76 ms each), with
`|S| = 40`, 143 exchange rounds total and **0** round-cap hits. The round cap
(`combiner.rs:605`) is not implicated; the per-round pairwise probing is.

Slice 42 adds one guard, applied at two sites (§3.B, §3.C): **arith never probes
or splits on a pair whose var it has received no constraint about.** No `sat` or
`unsat` verdict changes — the slice removes no deduction. It is not, however,
strictly verdict-neutral in one direction: see §4.A.

## 2. Why not fix the shared set instead

The conceptually correct fix is to stop over-approximating `S`. Nelson–Oppen
defines the shared set as terms occurring in *both* theories' constraints;
`shared_arith_terms`' sort-only filter admits terms that occur in no arith
constraint whatsoever. Narrowing `S` to `Int`/`Real` terms appearing in
`Arith`- or `Shared`-owned atoms would eliminate the probing *and* the
downstream per-round bookkeeping.

It is deferred (§6) for two reasons:

1. **Blast radius.** `S` is consumed by the exchange in both directions and by
   MBTC; changing it changes the `Combiner`, the highest-risk surface in the
   codebase. Under-approximating `S` costs completeness — a missed arith→EUF
   equality lets EUF miss a contradiction, i.e. wrong `sat`.
2. **The soundness argument is global.** It must show that no chain of
   EUF-derived equalities can carry information between two arith-constrained
   terms via an excluded one. That argument is available — selector-collapse
   produces `head(x) = 1` as an `Int`-sorted equality *atom*, which classifies
   as `Shared` and so stays in `S` — but it depends on the classification of
   every equality shape the DT and string layers can emit.

This slice's guard rests instead on a **local** invariant internal to
`shinri-arith` (§4), and leaves `S` and both exchange directions byte-for-byte
as they are.

## 3. The rule

### 3.A Constrainedness tracking

`Arith` gains a set of problem vars it has actually received a constraint about,
marked at exactly four entry points:

| Entry point | Site | Why it constrains |
|---|---|---|
| Atom registration | `new_var`, `lib.rs:1104` | the var occurs in a registered arith atom (including B&B branch/cut atoms routed via `Combiner::bind_fresh`) |
| Assertion | `assert`, `lib.rs:1142` | the atom's bound is on the trail |
| Interface equality | `assert_interface_equality`, `lib.rs:750` (via `consume_interface_equality`, `lib.rs:1244`) | EUF→arith equality constrains both sides |
| Numeral pin | `ensure_shared_var`, `lib.rs:543` | a numeral pinned to its value *is* a constraint |

The asymmetry in the last row is the entire point: `ensure_shared_var` marks
constrained **only** on the numeral-pin branch. A shared term arith was merely
told exists — no numeral value, no atom — stays unconstrained. That is exactly
the `head(t)` population.

**The set is monotone: a var is never un-marked, including on `pop`.** After
backtracking, a var constrained only by a since-retracted assertion stays
marked, so it is still probed. This over-approximates constrainedness, which
errs toward *more* probing — the sound direction. Making the set backtrack-exact
would prune more and is not worth the pop-ordering hazard.

### 3.B The guard

In `entailed_equalities`, at candidate construction (`lib.rs:591`), skip a pair
when **either** var is unconstrained.

The guard MUST sit at candidate construction, before the `define_slack` loop at
`lib.rs:604`. Slacks minted for a candidate pair **persist across calls**: the
snapshot at `lib.rs:613` is taken *after* `define_slack`, the final `restore`
(`lib.rs:661`) restores to that post-definition snapshot, and
`Vars::slack_var` memoizes the combination. A guard placed later would leave the
`u − v` rows behind on the first call and pay for them forever.

That persistence is also why the predicate cannot be inferred from the tableau.
The natural reading — "no bounds and appears in no row" — is correct on the
first call and wrong on every subsequent one, because the probe slacks put every
previously-probed var into a row. Constrainedness must be tracked explicitly.

### 3.C MBTC

The same guard applies in `model_equal_shared_pairs` (`lib.rs:671`), which feeds
the MBTC trichotomy split at `combiner.rs:813`. It runs the identical same-β
pairwise sweep over `S` and hands the `Combiner` the first model-equal pair,
which becomes a 3-way `(= u v) ∨ (< u v) ∨ (> u v)` split. With 40 unconstrained
vars at β = 0 those splits are pure waste — arith constrains neither side, so
any arrangement EUF chooses is arith-satisfiable.

This is a **distinct soundness sub-claim** from §3.B (arrangement agreement
rather than equality entailment) and gets its own test (§5). It is included
because it is the same invariant over the same var set in the same file, and
omitting it leaves a second, smaller source of the same waste in place.

## 4. Soundness

**Invariant.** *A problem var that arith has received no constraint about is
free: for any assignment satisfying arith's constraints there is another,
differing only in that var, that also satisfies them.*

Two consequences:

- **§3.B.** `u = v` is not entailed by arith for any `v` when `u` is free —
  shift `u`. Skipping the probe therefore cannot drop an entailed equality,
  which is the only way this change could cost completeness.
- **§3.C.** Any arrangement of a free var is arith-satisfiable, so arith has
  nothing to contribute to deciding it and MBTC's split is not needed for
  agreement.

Vars are deduped to distinct problem vars before pairing (`lib.rs:582`), so the
degenerate `u = u` case does not arise.

**The invariant is only as strong as the exhaustiveness of §3.A's four entry
points.** Establishing that no other path can constrain a var — and that the
monotone set is genuinely conservative under `push`/`pop` — is the substantive
work of this slice; the guards themselves are a handful of lines. The
implementation plan
must carry that audit as an explicit task with its findings recorded, not fold
it into the coding task.

### 4.A One permitted verdict change: `unknown` → decided

The slice removes no deduction, so no `sat` can become `unsat` or vice versa,
and nothing decided can become `unknown` on that account. There is one
asymmetric exception, and it is an improvement rather than a regression.

`Arith::STRING_PATH_PIVOT_BUDGET` and `STRING_PATH_BRANCH_BUDGET`
(`lib.rs:171`, `lib.rs:180`) exist precisely because the String↔Arith length
seam feeds `entailed_equalities` / `model_equal_shared_pairs` a degenerate
system whose probing re-solves simplex unboundedly; on exhaustion `check_full`
returns a **sound `Unknown`**. Those budgets are cumulative over a solve. Pruning
hopeless probes consumes fewer pivots, so a query that previously exhausted its
budget and bailed to `Unknown` may now finish and decide.

That is `unknown` → `sat`/`unsat`: sound, an improvement, and an **adjudicated
flip** in the sense slices 40 and 41 used the term. It must still be
z3/cvc5-confirmed before any pin is updated. Every other flip direction remains
a regression (§5).

This also means the string path — not just QF_DT — is in this slice's blast
radius, which is a further reason the oracle run must be unfiltered (§5).

## 5. Testing

### Unit — `shinri-arith`

- `entailed_equalities` over two unconstrained shared vars returns empty **and
  mints no slack**. Assert on the tableau/`Vars` state, not only on the return
  value: slack persistence is what defeated the tableau-based predicate, so it
  needs a direct fence.
- Each marking path individually restores probing — a var constrained only by a
  numeral pin, only by a registered atom, only by an assertion, and only by a
  consumed interface equality each still yields the entailed equality it yielded
  before.
- An entailed pair between two constrained vars is still reported: the
  anti-regression anchor for the rule itself.
- `model_equal_shared_pairs` omits pairs with an unconstrained var and still
  returns model-equal pairs of constrained vars (§3.C).
- Monotonicity: a var constrained at level *n* is still probed after `pop` below
  *n*.

### End-to-end — `shinri-solver`

The existing DT⋈arith set is the regression anchor and must stay green with
verdicts unchanged: `mixed_datatype_and_arith_unsat`,
`arith_{lt,le,gt,ge}_over_selector_*`, `arith_wrapped_selector_unsat`
(`qfdt_e2e.rs:146–231`).

### Performance gate

Check the `deep` family in as a test: assert a **decided** verdict at n = 24
under a generous wall-clock bound (5 s against a pre-fix 24.1 s). Wall-clock
assertions are normally a flakiness smell; a ≈1600× fault carries enough margin
to justify one, and without it a silent regression quietly consumes the
10–15 min blocking-tier budget.

### Oracle

The **full unfiltered** run: `cargo nextest run -p shinri-solver --features
oracle`, no `-E` filter, and **confirm a non-zero discovered test count** (a
flagless run compiles to zero tests and proves nothing). Non-negotiable here —
this change sits in the shared arith/N-O path, and a filtered run on slice 40
skipped `qfs_differential` and nearly shipped a Sat→Unknown regression. QF_UFLIA
coverage matters as much as QF_DT; the exchange is shared.

### `script_e2e`

Run locally pre-push. The change removes no deduction, so the expected outcome
is **no flips at all**. Adjudicate any that appear by direction:

| Flip | Reading |
|---|---|
| `unknown` → `sat`/`unsat` | **Permitted** (§4.A): a budget-limited query now finishes. Confirm against z3/cvc5 before updating the pin. |
| `sat` ↔ `unsat` | Regression. Stop. |
| decided → `unknown` | Regression. Stop. |

The permitted direction is expected on the **string** path, not QF_DT, since
that is where the cumulative pivot/branch budgets actually bind.

### Standing gates

`cargo fmt --all` before pushing (CI `fmt --check` fails fast); `mise run lint`
clean (clippy `-D warnings`).

## 6. Scope — explicitly out of slice 42

| Deferred | Owner |
|---|---|
| Correcting `Euf::shared_arith_terms`' sort-only filter so `S` is not over-approximated (§2) | 43 |
| Finiteness predicate + demand-driven splitting + leaving infinite-sort terms free (the original slice-42 roadmap entry) | 43 |
| Nelson–Oppen exchange for `Int`/`Real` datatype fields, completing QF_UFDTLIA | 43 |
| `?` placeholders for non-datatype fields in rendered models (`DtSolver::render_value_inner`) | 43 |

The roadmap entry this slice displaces — finiteness/cardinality — was
re-examined and reduced before deferral. Its cardinality half is **not** needed
for completeness: because every finite-sorted term is split exhaustively, every
finite-sort class becomes constructor-determined and the arrangement over those
classes is settled by congruence plus constructor clash. `(distinct a b c d)`
over a three-constructor enum already returns `unsat` with no counting rule.
Slice 43 should build the finiteness **predicate** only; an explicit pigeonhole
rule stays speculative until a query demands it.

## 7. Success criteria

- The n = 24 `deep` query decides `sat` in well under a second, against a
  measured 24.1 s baseline; the n = 20 Int-field query matches the
  uninterpreted-field query's order of magnitude (6 ms), closing the
  sort-attributable gap.
- **No regressive verdict changes**: `qfdt_e2e`, `script_e2e`, and the full
  unfiltered oracle run agree with pre-slice results, except that an
  `unknown` → decided flip on the string path is permitted once
  z3/cvc5-confirmed (§4.A). Any `sat` ↔ `unsat` or decided → `unknown` flip is a
  regression.
- The §3.A entry-point audit is recorded, establishing that no path can
  constrain a problem var without marking it.
- Unit tests pin both the skip (no slack minted) and each marking path's
  restoration of probing.
