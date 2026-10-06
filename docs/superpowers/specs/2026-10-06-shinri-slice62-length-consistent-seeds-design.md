# Slice 62 — Length-consistent seeds and the compound-arithmetic gate

Status: design approved in chat 2026-10-06. Picks up the slice-61 report's
queue items 5 and 3
(`docs/superpowers/research/2026-10-06-smtlib-2024-slice61-joint-concat-seeds-report.md`,
§ Queued for the next slice). Scope rulings (owner, in chat): items 5 and 3
ship together; approach 2 below (gate fix plus intersection length bounds),
with the strict-on-length-mismatch flag kept as a backstop. CEGAR length
refinement stays queued.

**Area:** `shinri-solver` (gate `eval_num_val`), `shinri-str` (`regex.rs`
gains `len_bounds`; `memb.rs` gains a per-leaf bound pass; `model.rs`
`memb_seeds` returns a mismatch flag; `lib.rs` `model_with` ORs it into the
strict flag), and a mechanical theory-interface change: `TCheck::Split`,
the Combiner's `FinalCheck::Split` and the SAT `TheoryResult::SplitAtoms`
carry `guards: Vec<Lit>` instead of `guard: Option<Lit>` (sites in
`shinri-sat`, `shinri-theory`, `shinri-arith`, `shinri-arrays`, `shinri-dt`,
`shinri-str`). No parser, word-equation, Rule-E, emptiness, joint-seed or
bench-tool change.

## 1. Summary

### 1.1 Item 5: a live wrong `sat` on `main`

Re-checked on a fresh `main` (`cdb5630`) release build:

```smt2
(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (and (<= (+ (str.len x) (str.len y)) 3)
             (>= (+ (str.len x) (str.len y)) 3)))
(check-sat)
```

z3: `unsat`. shinri: `sat ((x "") (y ""))`.

Cause. `eval_num_val` (`crates/shinri-solver/src/lib.rs`, the R11a arm for
`+ - * neg`) evaluates a compound term structurally only when the arith
model holds a value for that compound term. Here it holds none, so the term
is unevaluable (`None`) and the non-strict gate skips the assertion, while
`memb_seeds` has re-seeded both leaves with words whose lengths disagree
with the arith model. The precondition does not protect soundness: when
every operand evaluates, the folded value is the term's true value under
the final model.

### 1.2 Item 3: the shortest-word fallback cannot be length-consistent

`QF_SLIA/2015-Norn/ab/norn-benchmark-135.smt2` (z3 `sat`, `v = 2`)
constrains `var_0` to `a*b ∩ a*b+ ∩ ab* ∩ [a-u]*` = `{ab}` and asserts
`(= (* v 2) (+ (str.len var_0) 2))`. The arith model picks
`str.len var_0 = 4`, `v = 3`. No word of length 4 exists, so `memb_seeds`
falls back to the shortest word `"ab"`; R11a's gate then rejects the model
(4 ≠ 6). Slice 61 turned this base `sat` (right by luck, invalid model)
into `unknown`; `-138` is the same shape over `var_4`.

Searching at the model length first cannot help: arith must pick 2. The
slice-26 carve-out (`crates/shinri-str/src/memb.rs`, "Slice 26: general
const-Rex LEAF carve-out") bounds `len` per atom using the structural
`min_len`/`max_len`. Every arm of 135's goal has a `*`, so no atom has a
finite max, and the intersection's bounds (`2..2`) are never told to arith.

## 2. Scope

In: the gate's compound-arithmetic evaluation; a strict-gate backstop for
seeds whose length differs from the model length; exact length bounds of a
bare leaf's membership intersection, emitted as guarded lemmas; the
multi-literal guard needed to state them.

Out (queued, see §9): semilinear length sets such as parity
(`(ab)*` with `len x + len y = 3` stays `unknown`, now soundly); leaves
pinned by an equation; concat subjects; the R9 strict gate's item-4 rows.

## 3. Approaches considered

1. **Gate only.** §4.1 and §4.2. Closes item 5; recovers 0 of item 3's
   rows. Cheap.
2. **Gate plus intersection length bounds (chosen).** Approach 1 plus §4.3–
   §4.5. Recovers Norn `ab` 135/138 with valid models; reuses the slice-26
   emission posture.
3. **Approach 2 plus CEGAR length refinement.** At final check, block a free
   leaf's model length `n` when its intersection has no word of length `n`.
   Would make the item-5 reproducer `unsat`, but costs a witness search per
   leaf per round and can enumerate without bound when no length bound
   stops it. Queued.

For the multi-guard lemma, the alternative to widening the guard was a
split on the bound atom followed by a k-literal conflict. Rejected: two
rounds per bound, and the string theory would have to track the decision
levels of arith atoms.

## 4. Design

### 4.1 Gate: structural evaluation of length arithmetic

In `eval_num_val`, a `+ - * neg` term's value is `fold_arith` over its
operands whenever **every operand evaluates**, whether or not the arith
model valued the compound term. When some operand does not evaluate, the
arm returns the arith model's value of the term as today, and `None` when
there is none.

Soundness: the folded value is computed from the final model's values
(string lengths read from string values, numerals, model numbers), so it
equals the term's value under the model shinri would print. A `Some(false)`
it produces is a real violation.

`model_reject::tests::unevaluable_compound_len_arith` loses its premise
(`len x + 1 = 2` under `x = "a"` now evaluates to true). It is rewritten:
the evaluated case asserts `Some(true)`, and the `unevaluable:len-arith`
tag is pinned with an operand that has no value (an Int variable absent
from the model).

### 4.2 Backstop: strict gate on a seed/model length mismatch

A new `memb_seeds_flagged` returns `(FxHashMap<TermId, String>, bool)`;
`memb_seeds` becomes its `.0` wrapper, so existing callers and tests are
untouched (the slice-61 `joint_seeds` pattern). The flag is set
when it inserts a seed whose char count differs from the
`class_len_in_model` value it searched at (the `search_shortest` fallback
path). `model_with` calls `m.require_strict_check()` when the flag is set,
next to the existing R9 call.

Purpose: a re-lengthed leaf whose length reaches an assertion the gate
cannot evaluate (a UF argument, `str.to_int` of a length-dependent term)
could otherwise be violated unseen. With the flag, such a model yields
`sat` only when every assertion is positively confirmed.

This is live on `main` (found during planning, `cdb5630`): `x ∈ (ab)*`,
`f(len x) = 1`, `f(0) = 0`, `f(2) = 0`, `len x ≤ 3` (logic `ALL`) answers
`sat ((x ""))`; z3 answers `unsat`.

Known costs, measured not tuned: the item-4 pattern (the strict gate
rejecting on an unrelated unevaluable assertion); and a model length that
reads 0 because arith holds no `str.len` entry makes any non-empty
fallback word a mismatch (conservative, sound). §8 criterion 7 counts both.

### 4.3 Exact length bounds: `regex::len_bounds`

```rust
pub(crate) fn len_bounds(r: &Rex) -> Option<(u32, Option<u32>)>
```

Layered breadth-first walk of the derivative automaton. Layer `d` is the
set of distinct states reached by words of length exactly `d`; states are
deduplicated **within a layer only**. (A state can be reached at two depths
without a cycle — `(a|bb)c` reaches `c` at depths 1 and 2 — so global
deduplication would under-state the max.) Like `language_empty`, it
explores every `next_classes` interval, pure-surrogate ones included, using
the class's `lo` as representative; `search_shortest` skips those, so its
length is not a sound lower bound.

- `min` = the first layer holding a nullable state.
- `max` = `Some(last layer holding a nullable state)` once a layer holds
  only `Empty` states; `None` if `LEN_BOUND_DEPTH_CAP` (64) layers pass
  first.
- Returns `None` when the language is empty (slice 28 owns that case: no
  nullable state found before the frontier dies), and on any taint: a
  `next_classes` cap overflow, a derivative over `FUEL_NODE_CAP`, or more
  than `MEMB_SEARCH_STEP_CAP` expanded states in total. `None` means "no
  lemma", never a verdict.

A non-`Empty` state with an empty language keeps a layer alive; that can
only push the walk to the depth cap (max `None`), never produce a wrong
bound.

### 4.4 Emission: per-leaf intersection bounds (`memb.rs`)

A new pass beside the slice-26 carve-out, run in the same `memb_check`
round and under the same fuel:

1. Group the asserted membership atoms (`memb_true`) by subject, keeping
   subjects that are bare leaves (nullary uninterpreted) and not
   `model::is_repair_pinned`, and whose atoms are `side_clean` against
   `input_cond_roots` (the carve-out's gate).
2. `goal = regex::inter` of each atom's polarity-adjusted Rex (`comp` for a
   negative atom) — the goal `memb_seeds` searches. Skip the group if any
   atom's regex does not extract.
3. `len_bounds(goal)`; on `None`, skip.
4. Per-atom bounds already available to arith: `lo₀ = max min_len` over the
   positive atoms' Rex, `hi₀ = min max_len` over those with a finite one.
   Emit `(>= (str.len x) min)` iff `min > lo₀`, and `(<= (str.len x) max)`
   iff `max` is `Some` and tighter than `hi₀` (or `hi₀` is absent).
5. Each bound is emitted through `emit_split` with
   `guards = [¬m₁, …, ¬mₖ]` over every atom in the group (lits in a fixed
   order: sorted by var), i.e. the clause `¬m₁ ∨ … ∨ ¬mₖ ∨ bound`. One
   clause per round, like the carve-out.
6. Dedup on `(bound atom, sorted guard lits)` in a new
   `emitted_group_len_axioms` set (the slice-26 `emitted_len_axioms` is
   keyed by the bound atom alone, which would suppress a lemma needed under
   a different membership set on another branch).
7. Cache `len_bounds` results per sorted guard set, so the walk does not
   re-run every round.

Soundness: the clause is a tautology of the string theory — any `x` in
every `mᵢ`'s language lies in `L(goal)`, whose lengths are within
`[min, max]` by §4.3.

For Norn 135 the group is the four memberships on `var_0`;
`len_bounds = (2, Some(2))`, `lo₀ = 1`, `hi₀` absent, so both bounds are
emitted. Arith must then choose `str.len var_0 = 2`, `v = 2`; `memb_seeds`
finds `"ab"` at the model length; the gate passes.

### 4.5 Multi-literal guards in the theory interface

`TCheck::Split { atoms, guard: Option<Lit>, phases }` becomes
`TCheck::Split { atoms, guards: Vec<Lit>, phases }`, and the same for the
Combiner's `FinalCheck::Split` and `shinri_sat::TheoryResult::SplitAtoms`.
The SAT split arm (`crates/shinri-sat/src/solver.rs`, the `SplitAtoms`
case) pushes every guard as-is before the atom literals, exactly as it
pushes the single guard today. The unit-split path (`lits.len() == 1`) is
reached only with no guards, as now. Every guard is the negation of an
asserted literal and so false at emission, and the
learn-and-backtrack-one-level protocol is unchanged.

Watch order (added during planning): `add_learnt` watches `lits[0]` and
`lits[1]` as given. With two or more already-false guards in front, both
watches would be false guards and the atoms would never be watched, so a
violated lemma would go unnoticed. A clause with two or more guards is
therefore ordered atoms first, then guards by descending decision level.
With 0 or 1 guard the original guard-first order is kept byte-for-byte.

Migration is mechanical and compiler-driven: `guard: None` becomes
`guards: vec![]`, `guard: Some(g)` becomes `guards: vec![g]`, readers move
from `if let Some(g)` to iteration. `memb::emit_split` takes
`guards: Vec<Lit>`. No behaviour change outside §4.4.

## 5. What this does not change

Rule G/S/E unfolding, the slice-26 per-atom carve-out and its dedup, the
slice-28 emptiness conflict, joint seeds (slice 61) and R9, the
reconciliation rebuild, `search_word`/`search_shortest`, the bench tool.

## 6. Tasks

1. `regex::len_bounds` with unit tests (§7.1).
2. Multi-literal guards: interface migration across crates, plus the SAT
   two-guard clause test; `mise run ci` green with no behaviour change.
3. Per-leaf bound pass in `memb.rs` with unit tests.
4. Gate: structural `eval_num_val`, rewritten `model_reject` test.
5. Backstop: `memb_seeds` flag and `model_with` wiring, unit tests.
6. Probes (§7.2).
7. Oracle (§7.3).
8. Gates and bench measurement (§8), report, spec §11.

Tasks 1 and 2 are independent; 3 depends on both; 4 and 5 are independent
of 1–3.

## 7. Testing

### 7.1 Unit (blocking tier)

- `regex.rs` `len_bounds`: `a*b ∩ a*b+ ∩ ab* ∩ [a-u]*` → `(2, Some(2))`;
  `(a|bb)c` → `(2, Some(3))` (cross-depth state, max not under-stated);
  `(ab)*` → `(0, None)`; a language whose only shortest word runs through a
  pure-surrogate class counts that length in `min`; `∅` (e.g. `a ∩ b`) →
  `None`; a finite language longer than `LEN_BOUND_DEPTH_CAP` → max `None`.
- `memb.rs`: a two-atom leaf group emits both bounds with two guards; no
  lemma when `len_bounds` is no tighter than per-atom bounds; a
  repair-pinned leaf emits nothing; the dedup key separates two guard sets
  with the same bound atom.
- `model.rs`: `memb_seeds`' flag is false when the seed is found at the
  model length and true on the shortest-word fallback with a different
  length.
- `lib.rs` (`shinri-str`): `model_with` sets `strict_check_required` when
  the flag is set.
- `shinri-solver` gate: `len x + len y = 3` under `x = ""`, `y = ""` with no
  arith value for the sum evaluates to `Some(false)`; the rewritten
  `unevaluable_compound_len_arith`.
- `shinri-sat` / `shinri-theory`: a `SplitAtoms` with two guards learns the
  clause `g₁ ∨ g₂ ∨ atom`; existing split tests pass after migration.

### 7.2 Probes (`shinri-solver/tests/slice62_probes.rs`, blocking tier)

- §1.1's reproducer and the R10 script (`(= (+ (str.len x) (str.len y)) 3)`
  form): not `sat`.
- Norn 135 and 138 shapes inlined: `sat`, and each `get-value` model
  satisfies the script when substituted back (checked by evaluating the
  assertions on the printed values).
- A UF-argument variant — a leaf whose fallback seed changes its length,
  with that length used only under an uninterpreted function — is not
  `sat` (the backstop's case).

### 7.3 Oracle (`shinri-solver/tests/len_bounds_oracle.rs`, `--features oracle`)

z3 differential over generated scripts: one to three bare String leaves,
each with 2–4 memberships (positive and negative) drawn from a small regex
grammar, plus a compound length constraint (`+`, scalar `*`) and optionally
an Int variable. For every shinri `sat` the witness is substituted and
checked by z3; the test fails on any shinri verdict z3 contradicts, on any
witness z3 rejects, and on a shinri `unsat` z3 does not confirm. Tallies
(`sat`/`unsat`/`unknown`/z3 timeouts) are printed.

### 7.4 Unchanged suites

Everything else in `mise run ci` and the oracle suite, unchanged. The
interface migration must leave them green with identical behaviour.

## 8. Measurement

The slice-60/61 harness. Base: slice 61's after runs at `f9fa4f9`, whose
crates equal `main`'s (`cdb5630`). Because §4.5 touches every theory, the
neutrality sample includes non-string logics.

The report contains:

1. Verdict changes base → after, by logic and family, and the
   `fence_detail` deltas.
2. Triage of every row whose verdict changed (3 re-runs each).
3. Attribution of losses: gate (§4.1), backstop (§4.2), or bound lemma
   (§4.4).
4. Timing per the criteria, plus per-row timings for newly-`correct` rows.
5. The rewritten queue (§9).

### Success criteria

| # | criterion | kind |
| --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | hard; any hit stops the slice for a ruling |
| 2 | Norn `ab` `norn-benchmark-135` and `-138` are `correct`, and their `get-value` models satisfy the script | hard |
| 3 | every `correct → non-correct` row that reproduces in 3/3 re-runs is shown to have had an invalid base model (the gate rightly rejecting it); any other reproducible loss fails | hard |
| 4 | serial, interleaved timing on 150 sampled both-`correct` rows per string logic: summed wall time within ±5% of base | hard |
| 5 | `mise run ci` green; oracle suite passes with a discovered count ≥ 841 plus this slice's oracle tests | hard |
| 6 | neutrality sample (string and non-string logics): no verdict change other than non-reproducible timing flips | hard |
| 7 | counts of rows whose verdict moved because of the backstop flag, and of rows on which a bound lemma was emitted | report-only |

## 9. Queued for the next slice

Written by the measurement report. Carries slice-61 queue items 1, 2, 4
and 6–9 and its deferred minors, re-ranked on the new counts, and adds
**CEGAR length refinement** (approach 3) as the parity follow-up, with
§1.1's reproducer as its target (z3 `unsat`).

## 10. References

- Slice-61 report: § R10 check; § The two `correct → unknown` rows;
  § Queued for the next slice, items 3 and 5.
- Slice-26 spec `docs/superpowers/specs/2026-07-16-shinri-slice26-leaf-membership-length-seam-design.md`
  (leaf carve-out, `min_len`/`max_len` contracts).
- Slice-61 spec `docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md`
  (measurement harness, criteria format, R9).
- Code:
  - `crates/shinri-solver/src/lib.rs` `eval_num_val`, `fold_arith`,
    `string_model_satisfies`
  - `crates/shinri-solver/src/model_reject.rs`
    `unevaluable_compound_len_arith`
  - `crates/shinri-str/src/model.rs` `class_len_in_model`,
    `is_repair_pinned`, `memb_seeds`
  - `crates/shinri-str/src/lib.rs` `model_with`
  - `crates/shinri-str/src/memb.rs` `emit_split`, slice-26 carve-out
  - `crates/shinri-str/src/regex.rs` `min_len`, `max_len`, `deriv`,
    `next_classes`, `language_empty`, `search_shortest`
  - `crates/shinri-theory/src/solver_trait.rs` `TCheck`;
    `crates/shinri-theory/src/combiner.rs` `FinalCheck`;
    `crates/shinri-sat/src/types.rs` `TheoryResult`;
    `crates/shinri-sat/src/solver.rs` `SplitAtoms` arm
