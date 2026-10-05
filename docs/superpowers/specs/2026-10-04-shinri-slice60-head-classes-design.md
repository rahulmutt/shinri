# Slice 60 — Head-only next-character classes

Status: design approved in chat 2026-10-04. Picks up the slice-59 report's
queue item 1 (`docs/superpowers/research/2026-10-04-smtlib-2024-slice59-model-rejected-classes-report.md`,
§ Queued for the next slice): "Membership witness search past
`CLASS_SPLIT_CAP`" (class 1, `violated:memb@not-needed`, 2,253 rows).
Scope rulings (owner, in chat): change `next_classes` itself, so every caller
(Rule-E unfolding included) gets the coarser partition; the
unseeded-concat-operand sub-bucket (`regex-035-*`) stays queued.

**Area:** `shinri-str` (`regex.rs`: `next_classes` and a new `head_bounds`;
`range_bounds` deleted). Tests in `shinri-str` and `shinri-solver`. No
parser, SAT, Combiner, word-equation, lowering, model-gate or bench-tool
change.

## 1. Summary

### 1.1 The population

Slice-59 run: class 1, `violated:memb@not-needed`, is 2,253 of the 4,085
`unknown:str-model-rejected` rows (55.2%). Top families: automatark-lu 649,
stringfuzz `generated/regexbig` 493, stringfuzz `generated/regexpair` 394.
In the 40-row sample, 35 rows are a bare-variable subject whose seed search
failed. In all 35, `regex::next_classes` returned `None` (more than
`CLASS_SPLIT_CAP` = 64 cut points) on the **first** derivative step, so
`search_word`, `search_shortest` and `language_empty` all gave up. z3 on the
36 bare-variable rows: 14 `sat`, 7 `unsat`, 15 `timeout`.

### 1.2 Cause

`next_classes` (`crates/shinri-str/src/regex.rs:442`) cuts Σ at the bounds of
**every** `Range` node in the regex (`range_bounds`). Its doc comment notes
that the partition is "finer-than-needed — still correct". A long literal
contributes two cuts per distinct character even though only its first
character can be consumed next. The representative reproducer
(`QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-010-reverse-multiply-fuzz.smt2`,
976 B, z3 `unsat`) intersects three `re.+` literals, one over 40 characters
long. Its full partition overflows 64; its head partition has about 7 classes,
and one derivative step on any of them empties the intersection.

## 2. Scope

In:

- `next_classes` builds its partition from head-reachable `Range` bounds
  only (§4.1).
- Unit tests, a probe file, an oracle file (§7).
- A full-corpus base/after bench run and a research report (§8).

Out (stay queued):

- The unseeded free concat operand sub-bucket (`regex-035-*`, about 10% of
  class 1).
- The class-2 tag fix, class 3, and every item carried from earlier queues.
- Raising or retuning `CLASS_SPLIT_CAP`, `MEMB_SEARCH_STEP_CAP` or
  `FUEL_NODE_CAP`.

## 3. Approaches considered

1. **Head-only bounds inside `next_classes` (chosen).** One function changes;
   all four callers (`search_word`, `search_shortest`, `language_empty`,
   Rule-E in `memb.rs:587`) get the exact, coarser partition. Cost: Rule-E
   behaviour also moves, so the bench must attribute changes per caller.
2. **A separate head partition for the witness search and emptiness only.**
   Rule-E is untouched, so the bench signal is cleaner, but two partition
   functions coexist and Rule-E keeps fencing on the same shapes.
3. **A larger cap for the witness search.** Hides the cost instead of
   removing it: a 40-character literal still produces about 80 classes, each
   explored. Rejected.

## 4. Design

### 4.1 `head_bounds`

`deriv(c, r)` (`regex.rs:331`) tests `c` only against `Range` nodes in
head-reachable positions. `head_bounds(r, out)` collects exactly those nodes'
cut points, mirroring `deriv` case by case:

| node | cut points collected from |
| --- | --- |
| `Empty`, `Eps` | none |
| `Range(lo, hi)` | `lo`, and `hi + 1` when `hi < MAX_CODE` (as `range_bounds` today) |
| `Concat(ps)` | `ps[0]`; also `concat(ps[1..])` when `nullable(ps[0])` (`deriv`'s second branch) |
| `Union(ps)`, `Inter(ps)` | every member |
| `Star(i)`, `Comp(i)`, `Loop(i, ..)` | `i` |

For `Concat` the walk iterates over `ps` while each element is nullable,
rather than allocating `concat(ps[1..])`; the set of visited elements is the
same.

`next_classes` inserts `0`, calls `head_bounds` instead of `range_bounds`,
and is otherwise unchanged: same `CLASS_SPLIT_CAP` check, same return type,
same class construction. `range_bounds` has no other caller and is deleted.
The doc comment drops "finer-than-needed" and states the head-reachability
argument.

### 4.2 Why the partition is exact

Every test `deriv` performs on `c` is `lo <= c <= hi` for a head-reachable
`Range(lo, hi)`. By construction no such range has a boundary strictly inside
a class, so every test answers the same for every `c` in the class, and
`deriv(c, r)` is the same `Rex` for every `c` in the class. Surrogate
handling is unchanged: cut points are still user characters ±1.

### 4.3 Effect on callers

| caller | effect |
| --- | --- |
| `search_word`, `search_shortest` (`memb_seeds`, `model.rs:515`) | find a seed where the full partition overflowed; fewer classes per step |
| `language_empty` (`memb.rs:662`) | can decide `Empty` (emptiness conflict → `unsat`) where the full partition tainted to `Unknown` |
| Rule-E (`memb.rs:587`) | fewer, coarser disjuncts per split; fences only on genuinely wide heads |

A wide head (for example a 70-way character union) still overflows the cap
and fences exactly as today.

### 4.4 Risk

The only unsound failure is a `head_bounds` that misses a range `deriv`
tests. A class would then be non-uniform, its representative's derivative
would stand for characters it does not describe, and `language_empty` could
return a false `Empty` (wrong `unsat`) or Rule-E could drop a disjunct.
§7.1's uniformity sweep and §7.3's oracle file guard this.

### 4.5 Cost

Head-only bounds visit a subset of the nodes `range_bounds` visited, plus a
`nullable` call per nullable concat prefix. Fewer classes mean fewer
derivatives per step in every caller. No slowdown is expected; §8 measures.

## 5. What this does not change

`deriv`, `nullable`, every cap value, every fence site, `memb_seeds`'
eligibility rules, the model gate, the fence names and the `fence_detail`
tags.

## 6. Tasks

1. `head_bounds` + `next_classes` switch + unit tests (§7.1), TDD.
2. Probe file (§7.2).
3. Oracle file (§7.3).
4. Gates: `mise run ci`, oracle suite.
5. Bench base/after runs, triage, report (§8).

## 7. Testing

### 7.1 Unit (`shinri-str/src/regex.rs`, blocking tier)

- **Head-only shapes.**
  - `re.+ (str.to_re "<40 distinct chars>")` gives 3 classes.
  - `a·b` gives the classes of `a` only; `a*·b` adds `b`'s bounds;
    `a*·b*·c` adds `b`'s and `c`'s.
  - `Comp`, `Inter` and `Loop` pass the inner head through.
- **Uniformity sweep.** A deterministic seeded generator (no new dependency)
  builds a few thousand small `Rex` values over a narrow alphabet, covering
  every constructor and nested nullable concat heads. For every class of
  every value, `deriv` at `lo`, the midpoint and `hi` equals `deriv` at the
  representative. This generalises `next_classes_derivative_uniform`.
- **Search and emptiness.**
  - The inter of three `re.+` literals with distinct first characters and a
    long tail: `language_empty` returns `Empty`.
  - The same with a shared first character and a common member:
    `search_word` and `search_shortest` return a word, and `eval_membership`
    accepts it against each literal.
- **Unchanged.** `next_classes_partition_sigma` (its cap case is a union of
  single-character heads, still > 64) and
  `language_empty_class_split_overflow_taints_to_unknown` pass unmodified.

### 7.2 Probes (`shinri-solver/tests/slice60_probes.rs`, blocking tier)

Slice-53 style: each refuting case has a `sat` sibling so the fix cannot pass
by over-refuting.

- `regex-010-reverse-multiply-fuzz` (inlined) answers `unsat`.
- A `sat` sibling (three `re.+` memberships with a common member) answers
  `sat`; its `get-value` witness satisfies every membership.
- A `re.+` membership over a literal of more than 40 characters with a
  length pin answers `sat` (was `str-model-rejected`).
- `script_e2e::in_re_unfold_unknown_class_cap` stays `unknown` unmodified
  (its head is still wide).

### 7.3 Oracle (`shinri-solver/tests/head_classes_oracle.rs`, `--features oracle`)

Every §7.2 script plus seeded generated variants of the representative shape
(k `re.+` literals, mixed shared/distinct first characters, optional length
pin) run against z3. Any shinri `sat`/`unsat` must agree with z3; shinri
`unknown` is allowed. The run's discovered count must be above zero and the
suite total must be ≥ the slice-59 count (825 run, 2 skipped).

### 7.4 Unchanged suites

All existing `shinri-str` and `shinri-solver` tests pass without edits.

## 8. Measurement

Same harness and flags as slice 59: full QF_S and QF_SLIA, plus the seeded
neutrality sample for QF_BVFP, QF_DT, QF_LIA, QF_LRA, QF_UF, QF_UFLIA,
QF_UFLRA; base binary from the branch point; `--timeout 20 --mem-mb 3072
--jobs 6`.

The report (`docs/superpowers/research/2026-10-05-smtlib-2024-slice60-head-classes-report.md`)
gives:

1. Verdict changes by `fence_detail` tag and by family (automatark,
   stringfuzz `generated/regex*`).
2. For a seeded sample of changed rows, which caller produced the change
   (witness search, emptiness conflict, Rule-E), from a throwaway trace
   build.
3. Triage of every changed row (3/3 re-runs).
4. Timing per §Success criteria.
5. The rewritten queue.

### Success criteria

| # | criterion | kind |
| --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | hard; any hit stops the slice for a ruling |
| 2 | `violated:memb@not-needed` shrinks by ≥ 20% (≥ 450 rows) of its slice-59 count, those rows moving to `correct` | hard |
| 3 | no `correct → non-correct` change that reproduces in 3/3 triage re-runs | hard |
| 4 | serial, interleaved timing on 150 sampled both-`correct` rows per string logic: summed wall time within ±5% of base; any reproducible slowdown on newly-`correct` rows is reported | hard |
| 5 | `mise run ci` green; oracle suite passes with a discovered count ≥ the slice-59 count plus this slice's oracle tests | hard |
| 6 | neutrality sample: no verdict change other than non-reproducible timing flips | hard |

## 9. Queued for the next slice

Written by the measurement report (§8 item 5). Carries slice-59 queue items
2 onward and the `regex-035-*` sub-bucket of item 1, re-ranked on the new
`fence_detail` counts.

## 10. References

- Slice-59 report, § Queued for the next slice (item 1) and § 1
  (`violated:memb@not-needed`).
- Slice-59 spec `docs/superpowers/specs/2026-10-04-shinri-slice59-model-rejected-classes-design.md`
  (`fence_detail`, measurement harness).
- Code:
  - `crates/shinri-str/src/regex.rs:331` (`deriv`), `:408`
    (`CLASS_SPLIT_CAP`), `:442` (`next_classes`), `:593` (`search_word`),
    `:703` (`search_shortest`), `:768` (`language_empty`)
  - `crates/shinri-str/src/memb.rs:587` (Rule-E), `:662` (emptiness conflict)
  - `crates/shinri-str/src/model.rs:467` (`memb_seeds`)
  - `crates/shinri-solver/tests/script_e2e.rs` (`in_re_unfold_unknown_class_cap`)

## 11. Measured outcomes

> **Follow-up:** the Rule-E full-partition variant (`56997aa`) is measured in *Follow-up: Rule-E full-partition variant* at the end of this section. With it, criterion 3 passes.

Full evidence:
`docs/superpowers/research/2026-10-05-smtlib-2024-slice60-head-classes-report.md`.
Benchmarked binary: `4a9e656`. HEAD `0e39c39` differs only in tests and
comments.

| # | criterion | result |
| --- | --- | --- |
| 1 | 0 `* → wrong`; 0 wrong answers in triage | PASS. 0 `wrong` rows in all four runs (103,335 + 2,000 rows per binary). 0 `sat` ↔ `unsat` flips. 0 wrong answers in 1,434 triage runs (239 rows). The 42 new unverified `unsat` rows were cross-checked with z3 `-T:120` and cvc5 `--tlimit=120000`: 0 `sat`; 5 confirmed by z3 and 36 by cvc5 (36 by either); 6 automatark rows unconfirmed |
| 2 | `violated:memb@not-needed` shrinks ≥ 20% (≥ 450 rows) to `correct` | PASS. 917 of 2,252 base-tagged rows (40.7%) are now `correct`. A further 897 are decided but `unverified` (z3 oracle timeout) |
| 3 | no `correct → non-correct` reproducing 3/3 | **FAIL — accepted by controller ruling, pending owner decision.** 4 Norn HammingDistance rows (`norn-benchmark-312`, `322`, `362`, `454`): `sat`/`unsat` → `unknown` (3 `sat-budget`, 1 `str-model-rejected`), 3/3 on each side. Only Rule-E runs the changed partition on these rows (a search-order effect). There is no `sat` ↔ `unsat` flip, and the family nets +6 (+10 / −4). The PR does not merge without the owner's decision |
| 4 | serial timing within ±5% (150 both-`correct` rows per string logic) | **FAIL, outside the band on the faster side.** Pooled over 3 passes: QF_S 0.794 (5.49 → 4.36 s), QF_SLIA 0.740 (5.80 → 4.29 s). Every pass is in 0.709–0.828, and an after-first diagnostic pass gives 0.868 / 0.746. Newly-`correct` rows: 11.10× (8.13 → 90.28 s), reported. Their median is 9 ms; the cost is concentrated in stringfuzz `generated` witness searches (up to 2.7 s) |
| 5 | `mise run ci` green; oracle count ≥ slice 59 + this slice's oracle tests | PASS. ci exit 0, 1768 passed / 6 skipped (HEAD 1769). Oracle 831 passed / 2 skipped. Wide-head pins 3/3 |
| 6 | neutrality sample: only non-reproducible flips | PASS. 4 sample rows changed, all noise in triage |

**`violated:memb@not-needed`: 2,252 → 525.** `unknown:str-model-rejected`
overall: 4,084 → 2,360. String `correct`: QF_S 16,057 → 16,666, QF_SLIA
24,856 → 25,144.

Caller attribution (40 sampled gain rows): witness search 24 (1 of them
also has Rule-E splits), emptiness conflict 16, Rule-E only 0.

What remains of class 1 is a concat-subject shape: Norn operands seeded but
jointly inconsistent, about 465 rows, plus `regex-035-*` (28 rows,
unchanged). The report's queue now starts with the Norn Rule-E regressions,
then the class-1 remainder.

### Deviations from this spec

- Criterion 3 is a FAIL, accepted by controller ruling and pending owner
  decision (4 Norn HammingDistance rows, from Rule-E search order).
- Criterion 4 is a FAIL on the faster side (pooled 0.794 / 0.740). By intent
  this is a speed-up; by the letter it is outside ±5%.
- §7.2: the shared-member `sat` sibling in `slice60_probes` has two `re.+`
  memberships and one `re.*`, not three `re.+`.
- §7.3: the oracle uses z3 `-T:3` for generated scripts and `-T:20` for
  probes and witness re-checks. A shinri `unsat` whose z3 check times out
  fails the test, which is stricter than the spec. Last tally: 65 `sat`,
  77 `unsat`, 58 `unknown`, 37 z3 timeouts (the timeout count includes
  genuine z3 `unknown`).
- Rule-E coverage comes from the unit test
  `memb::tests::rule_e_long_literal_head_splits_not_fenced`, not from the
  oracle. The oracle's `(str.++ x y)` scripts never reached a decided answer
  through Rule-E.
- The bench measured `4a9e656`. HEAD `0e39c39` adds only tests and comments.
- Triage covered 239 rows: every small stratum and every `correct → *` and
  sample row in full; seeded samples of 32 from the two large strata (897
  and 133 rows); and 32 gain rows. Rows ran 6 in parallel.
- Extra gate (controller ruling): the cross-check of the 42 unverified
  `unsat` rows.
- Queue candidate from the final review: concat-subject memberships with a
  provably empty intersection (e.g. `(str.++ x y) ∈ L40+ ∩ (bba)+`) stay
  `unknown` in both base and after. Queued as item 4.

### Follow-up: Rule-E full-partition variant

The owner approved a variant after the criterion-3 FAIL. Rule-E calls
`regex::rule_e_classes`, which uses the full all-ranges partition when it
fits `CLASS_SPLIT_CAP` and falls back to the head-only `next_classes` past
it. The witness search and the emptiness conflict keep `next_classes`.

- Benchmarked commit: `56997aa`, md5 `6109b2a0266510f2084dab2df1e60240`.
- Runs: `slice60b` and `slice60b-sample`.
- Evidence: the report's § *Follow-up: Rule-E full-partition variant
  (56997aa)*, with artifacts under `target/slice60b-after/`.

Criteria, base → variant:

| # | criterion | result |
| --- | --- | --- |
| 1 | 0 `* → wrong`; 0 wrong answers in triage | PASS. 0 `wrong` rows in both runs. 0 `sat` ↔ `unsat` flips against base or approach 1. 0 wrong answers in 984 triage runs (164 rows). Unsat cross-check of the 371 newly checked variant `unverified` `unsat` rows (369 pre-existing in base) at 120 s: 0 `sat`, 212 confirmed (z3 8, cvc5 212), 159 unconfirmed, all pre-existing |
| 2 | `violated:memb@not-needed` shrinks ≥ 20% (≥ 450 rows) to `correct` | PASS. 936 of 2,252 base-tagged rows (41.6%) are now `correct`, against 917 for approach 1. The tag goes 2,252 → 432 |
| 3 | no `correct → non-correct` reproducing 3/3 | PASS. The 4 `correct → unverified` rows are noise: same answer 3/3, only the bench z3 timed out. Norn `312`, `322`, `362` and `454` are `correct` again, 3/3 on both binaries |
| 4 | serial timing within ±5% | **FAIL, on the faster side** (as approach 1). Pooled over 3 passes: QF_S 0.809 (4.76 → 3.85 s), QF_SLIA 0.845 (7.30 → 6.17 s). Newly-`correct` rows: 9.36×, reported. The passes ran once the 1-min load fell to ≤ 24, after about 4 h of waiting; during the passes the 1-min load was 14–18 and the 5-min load 23.5–29.3 |
| 5 | `mise run ci` green; oracle count | PASS. ci 1773 / 1773 (6 skipped); oracle 831 / 831 (2 skipped) |
| 6 | neutrality sample: only non-reproducible flips | PASS. 37 sample rows changed, all noise: both binaries give identical results, mostly killed under external host load. The variant changes only string regex code (`shinri-str` Rule-E), and all 37 changed sample rows are in non-string logics that never reach it |

- **Approach 1 → variant.** The 4 Norn regressions are restored. Approach
  1's 10 Norn HammingDistance gains are given back (`correct → sat-budget`,
  attributable 3/3).
- Norn and Jiang `slog` now match base row for row (3,003 rows). This
  removes approach 1's unknown ↔ unknown churn.
- String `correct` is 41,898, against 41,810 for approach 1 and 40,913 for
  base. The +88 over approach 1 is +4 − 10 Norn, plus 94 rows where only
  the bench's z3 oracle timeout differed.
- The report's queue item 1 is resolved.

Deviations (variant):

- Rule-E no longer takes the head-only partition. That contradicts §3
  approach 1, §4.3, and the header's "`range_bounds` deleted":
  `range_bounds` is back, and Rule-E uses it.
- Triage and the cross-check ran under heavy external host load (1-min
  load average 32.78–132.67 on 24 cores, from the triage and cross-check
  start/end readings and `timing-load.log`).
- Cross-check scope: 371 rows, which is all the variant's unchecked
  `unverified` `unsat` rows. 369 of them predate the slice.
- Criterion 4: out of band on the faster side, as with approach 1, and
  measured on a loaded host (1-min load 14–18, 5-min load 23.5–29.3)
  rather than an idle one.
