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

## 11. Measured outcomes

Report: `docs/superpowers/research/2026-10-07-smtlib-2024-slice62-length-consistent-seeds-report.md`
(verdict runs at `1261bc9`, 2026-10-07; base: slice 61's runs at `f9fa4f9`;
PR head `fd445aa`, a behaviour-neutral perf fix that was timed and
oracle-tested but not re-benched, see R13 below).

167 rows moved to `correct`, all QF_SLIA and all z3-confirmed: 165 `unsat`
and 2 `sat` (Norn `ab` 135, 138). Every one of them is attributed to the
§4.4 bound lemma. The §1.1 item-5 reproducer and the §4.2 UF case go from
a wrong `sat` to `unknown`.

| # | criterion | result |
| --- | --- | --- |
| 1 | 0 `* → wrong`; 0 wrong in triage | **PASS**: 0 `wrong` rows in both after runs; 0 wrong answers in 546 triage runs; the one new `unverified` `unsat` (denghang `instance46328`) is confirmed by z3 `-T:120` and cvc5 |
| 2 | Norn `ab` 135/138 `correct` with valid models | **PASS**: both `sat` with `v = 2`, `var_0`/`var_4 = "ab"`; z3 accepts the pinned models |
| 3 | reproducible `correct → non-correct` only with invalid base models | **PASS**: none reproduce (39 oracle-churn `correct → unverified`, 10 sample timeouts; all noise 3/3) |
| 4 | timing within ±5% | **PASS per R12.** At `1261bc9` it was a FAIL (pooled QF_S 1.060, QF_SLIA 1.094). After `fd445aa`: 6 passes pooled QF_S 1.037 / QF_SLIA 1.036; set 1 (R10 three-pass, load 21–26) 1.076 / 1.033; set 2 (load 13–15) 0.996 / 1.040; CPU min-of-5 per row QF_S 1.014 / 1.028, QF_SLIA 0.996 / 0.990; A/A base-vs-base swing 0.92–1.08. Set 1 alone fails QF_S by the letter and is accepted under R12 (noise floor, controlled measurements) |
| 5 | ci green; oracle ≥ 841 + this slice's | **PASS**: ci 1838/1838 (6 skipped) at `fd445aa` (1836 at `1261bc9`, 1834 at `01e3fa8`); oracle 854/854 (2 skipped) at `fd445aa` |
| 6 | neutrality sample: timing flips only | **PASS**: 15 changes, all at the 20 s / 3 GB edge, noise 3/3 |
| 7 | backstop and bound-lemma counts (report-only) | bound lemma on 167/167 gains and 1/400 random string rows. The seed backstop moved 0 verdicts (4/400 rows fire it, none changed). Unvalued fold and `uf-stale` fired on 0 changed rows and 0/400 |

Key timing numbers (after `fd445aa`, `target/slice62-after/timing-perf2.txt`):
pooled over 6 passes (150 rows per string logic, core 12, interleaved)
QF_S 1.037 and QF_SLIA 1.036; per-row min-of-5 by CPU time 1.014 / 1.028
(QF_S) and 0.996 / 0.990 (QF_SLIA), against 1.097 / 1.112 at `1261bc9`.
Set 1 alone (the R10 three-pass set) is QF_S 1.076; the A/A control swings
0.92–1.08 on identical binaries.

### Deviations from this spec

- **R2 (§4.5):** `emit_split` keeps its signature and wraps a new
  `memb::emit_split_guards(s, terms, atoms, guards)`. Behaviour is
  identical.
- **R3 (§4.4 step 4, plan conflict):** `lo₀`/`hi₀` are computed over
  positive atoms only, as this spec states; the plan's code used all
  members.
- **R4 (§7.4 "unchanged suites"):**
  `script_e2e::in_re_unfold_unsat_disjoint_stars` (slice-21 KNOWN GAP,
  pinned `unknown`) now answers `unsat`. Its pin was updated. The
  multi-guard lemma closes exactly this gap.
- **R5 (§4.1, §7.4):** two slice-57 probes
  (`strict_gate_keeps_unevaluable_unknown`,
  `rf2_strict_flag_does_not_leak_across_checks`) lost their "unevaluable"
  premise to §4.1. The old script is kept as a renamed `sat` pin. Both
  tests get a new assertion that the gate cannot evaluate.
- **Task 5 fix round (§4.2):** the strict flag alone did not reject the
  §4.2 UF case, because the gate read `f(len x)` at the stale arith
  argument. `eval_num_val` now treats a UF application as unevaluable when
  an argument's numeric model value differs from its evaluated value
  (`uf_args_stale`). That is a solver-gate rule beyond §4.1–4.2.
- **R7 (§7.3):** on (shinri `unsat`, z3 unknown) the oracle re-asks z3 with
  every string leaf bounded `len ≤ 12` (and `v ≤ 12`). Bounded `unsat`
  counts as confirmed; bounded `sat` or unknown fails. Neither z3 nor cvc5
  decides `z ∈ (ab)* ∧ z ∉ [a-u]*`.
- **R9 (§4.3):** `len_bounds` has a new budget, `LEN_BOUND_WORK_CAP` =
  10,000 derivative node-units, beside the unchanged caps. When it runs
  out, the walk returns `(min, None)` if a nullable layer was reached, and
  `None` otherwise. It was added after the first after run (`01e3fa8`)
  hit 238 timeouts. That run was abandoned at 89,050 rows and redone at
  `1261bc9`.
- **R10 (§8 criterion 4 procedure):** the timing load gate (≤ 24) waits at
  most 30 min, with a three-pass pooled fallback. In the event, load was
  21.67, so pass 1 ran gated. Passes 2 and 3 follow the out-of-band
  pooling rule.
- **R11 / second perf fix (§4.3, implementation only):** after criterion 4
  failed at `1261bc9`, one behaviour-neutral perf round produced `fd445aa`
  (`regex.rs` only). Root cause: a lone `Vec<Rex>::retain` in the
  `len_bounds` walk perturbed `Rex` drop-glue codegen crate-wide (about
  +11% even with `bound_split` returning early), plus a QF_S re-derivation
  of the same walk states at every depth. The walk now **interns its
  states** (each state's `nullable`, `next_classes` and per-class
  `(node_count, child)` are computed once and replayed with the same cap
  checks in the same order) and drops the `retain` (`Empty` never enters a
  layer). No cap, constant or lemma changed; §4.3's `len_bounds` results
  are identical, including where a cap trips (unit test
  `len_bounds_memo_matches_plain_walk`: 405 regexes × 7 work caps against
  the old walk; final-check traces identical on 946 bench rows). The fix
  partly rests on a codegen artifact, so the report queues a build-profile
  change (`codegen-units = 1` or LTO) as item 1.
- **R12 (§8 criterion 4 verdict):** criterion 4 is accepted as PASS on the
  6-pass pool (QF_S 1.037, QF_SLIA 1.036) backed by CPU min-of-5 (≤ 1.028).
  By the R10 three-pass letter, set 1 alone fails QF_S at 1.076; this is
  disclosed beside the A/A base-vs-base swing (0.92–1.08), which shows it is
  noise. Cost if wrong: a real ~+4–7% QF_S slowdown ships.
- **R13 (§8 measurement basis):** the after runs were at `1261bc9`, and no
  third full bench was run at the PR head `fd445aa`. `fd445aa` is verified
  behaviour-neutral (above), and the full oracle suite was re-run at
  `fd445aa` instead. Cost if wrong: a verdict change at `fd445aa` outside
  the traced rows goes unmeasured (about 3 h of bench to close).
- **`memb_seeds` is `#[cfg(test)]` (§4.2):** its only production caller,
  `model_with`, uses `memb_seeds_flagged`. The wrapper is kept for tests
  only.
- The §4.5 watch-order rule (atoms first, then guards by descending level,
  for ≥ 2 guards) was already in this spec (added during planning). It is
  pinned by `two_guard_split_detects_violation`.
