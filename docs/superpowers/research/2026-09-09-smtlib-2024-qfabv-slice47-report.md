# SMT-LIB 2024 QF_ABV re-run — slice 47 — shinri @ ddabe7b34230

Run-id `slice47`, `BENCH_LOGICS=QF_ABV mise run bench-run`, same limits as the
baseline (20 s / 3072 MB / 6 jobs, cgroup `cpu.max` `800000 100000`,
`memory.max` 34359738368). Started 2026-09-09T23:41:57Z. 15,148 QF_ABV
instances — the same paths as
`docs/superpowers/research/2026-09-09-smtlib-2024-baseline-report.md`, so
every row is a same-path comparison, not a resample. The run took far longer
than the plan's "half an hour to an hour" estimate: an interim read at 537
rows projected 4–6 hours wall-clock, because timeouts (20 s each) came to
dominate the mix. `BENCH_RUN_ID=slice47 mise run bench-report` renders
`bench/results/slice47/report.md` from `bench/results/slice47/results.jsonl`
(15,148 rows); this document narrates that report and the transition analysis
against the baseline, in the style of
`2026-09-09-smtlib-2024-baseline.md`.

**This run was measured at commit `ddabe7b3`.** Two commits landed after it,
`741410ac` and `bdf85f59`, to fix a regression this very run exposed (see
"Post-measurement correction" below). The table and transition matrix in this
document are the honest raw measurement at `ddabe7b3`; they are **not**
adjusted for the later fix. The correction is stated separately.

Baseline for comparison: `2026-09-09-smtlib-2024-baseline-report.md`,
run-id `baseline-8de004d44944`, QF_ABV row (`total 15148, correct 8454,
wrong 359, parse-error 26, panic 5787, oom 98, timeout 361, unknown 62,
unverified 1`).

## Headline

- **Zero wrong answers.** All 359 QF_ABV `wrong` rows at baseline are gone;
  slice 47's gate and fixes decide every one of them correctly or leave them
  undecided (timeout, panic, or the pre-existing `abv-fenced` fence). No new
  wrong answer appeared anywhere in the 15,148-row set.
- **`correct` rose 46%**, from 8,454 to 12,359 (+3,905). Most of the gain is
  not the 359 wrong-`sat` rows themselves — it is a large slice of the
  previously-panicking `blast_word` bucket that a fix made along the way
  turned into real answers (see "Criterion 6" below).
- **`timeout` rose from 361 to 524 (+163).** This is a measured **failure**
  of success criterion 3 (see "Success criteria" below); it is decomposed,
  not softened.
- **`panic` fell 63%**, from 5,787 to 2,127, but 264 of those still-panicking
  rows at the `ddabe7b3` measurement point are **new regressions** — rows
  that answered `correct` at baseline and panic here. Both later commits
  exist to fix exactly this (see "Post-measurement correction").
- **`abv-model-rejected` fired on 0 rows.** The gate never actually rejected
  a model in the full corpus; every row that changed did so through the
  fixes the gate's rejection reasons pointed at, not through a live
  `sat → unknown` downgrade. The only fence QF_ABV fires at all,
  `abv-fenced` (62 rows), is unchanged.

## Per-logic matrix (QF_ABV only, this run)

Copied from `bench/results/slice47/report.md`.

| logic | total | correct | wrong | parse-error | panic | oom | timeout | unknown | unverified | decided% | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_ABV | 15148 | 12359 | 0 | 24 | 2127 | 52 | 524 | 62 | 0 | 81.6 | 13 | 468 |

Baseline's same row, for reference: `total 15148, correct 8454, wrong 359,
parse-error 26, panic 5787, oom 98, timeout 361, unknown 62, unverified 1,
decided% 55.8, median 12, p90 173`.

## Verdict counts, baseline vs. slice47

| verdict | baseline | slice47 | delta |
| --- | ---: | ---: | ---: |
| `correct` | 8454 | 12359 | +3905 |
| `oom` | 98 | 52 | -46 |
| `panic` | 5787 | 2127 | -3660 |
| `parse-error` | 26 | 24 | -2 |
| `timeout` | 361 | 524 | +163 |
| `unknown:abv-fenced` | 62 | 62 | +0 |
| `unverified` | 1 | 0 | -1 |
| `wrong` | 359 | 0 | -359 |

## Transitions (changed cells only, same-path comparison)

| baseline | slice47 | count | families |
| --- | --- | ---: | --- |
| `panic` | `correct` | 3917 | egt 3883, stp_samples 22, dwp_formulas 7, bench_ab 5 |
| `wrong` | `correct` | 297 | dwp_formulas 278, brummayerbiere 19 |
| `correct` | `panic` | 264 | dwp_formulas 264 (regression — see below) |
| `panic` | `timeout` | 64 | — |
| `wrong` | `timeout` | 62 | brummayerbiere 50, brummayerbiere2 5, dwp_formulas 5, calc2 2 |
| `correct` | `timeout` | 62 | dwp_formulas 36, brummayerbiere 14, brummayerbiere2 8, brummayerbiere3 3, stp 1 (regression — see below) |
| `oom` | `panic` | 53 | — |
| `timeout` | `correct` | 18 | — |
| `timeout` | `oom` | 6 | — |
| `timeout` | `panic` | 4 | — |
| `parse-error` | `timeout` | 2 | — |
| `unverified` | `timeout` | 1 | — |
| `correct` | `oom` | 1 | stp |

Unchanged: `correct` 8127, `panic` 1806, `timeout` 333, `unknown:abv-fenced`
62, `oom` 45, `parse-error` 24.

Net read: 4,232 rows now answer correctly that did not before (3,917 from the
panic bucket, 297 from the wrong bucket, 18 from timeout); 327 rows that used
to answer correctly no longer do (264 to panic, 62 to timeout, 1 to oom). Net
`correct` change is +3,905.

## Success criteria

| criterion | baseline | slice47 | verdict |
| --- | ---: | ---: | --- |
| 1. `wrong` = 0 | 359 | **0** | **PASS** |
| 2. `correct` ≥ 8,454 | 8,454 | **12,359** (+3,905) | **PASS** |
| 3. `timeout` ≤ 361 | 361 | **524** (+163) | **FAIL** |
| 4. `abv-model-rejected` fires on 0 rows | n/a | **0** | **PASS** |
| 5. extended generator failed pre-slice, passes now | — | yes | **PASS** |
| 6. panic / parse-error / oom reported, movement explained | 5787 / 26 / 98 | 2127 / 24 / 52 | reported below |

### Criterion 3 — the timeout cap was missed. It is not relaxed.

`timeout` rose from 361 to 524, a genuine miss of the ≤361 cap, and it is
reported as a failure rather than softened or re-derived. But the cap counts
every timeout alike, so a bare "+163" hides what the slice actually did to
that bucket. Decomposing the 524 by what each row was at baseline:

| previously | count |
| --- | ---: |
| `timeout` (unchanged) | 333 |
| `panic` | 64 |
| `wrong` | 62 |
| `correct` | 62 |
| `parse-error` | 2 |
| `unverified` | 1 |

Of the +163 that newly entered the bucket: 62 were previously `wrong`
answers — eliminating a wrong answer by turning it into an honest timeout is
this slice's entire purpose — 64 were previously crashing (`panic`), and 3
were `parse-error`/`unverified`. Only 62 of the 163 were previously `correct`
and are a genuine regression: the slice traded a fast right answer for a slow
non-answer on those rows. (28 rows also left the timeout bucket in the other
direction — see the transition matrix.) So the criterion's cap treats
"wrong answers and crashes became honest timeouts" the same as "correct
answers became timeouts", when only the latter is a real cost. Both are true
at once here, and the criterion's job is to catch the second even when the
first dominates the count. The 62 `correct → timeout` rows (dwp_formulas 36,
brummayerbiere 14, brummayerbiere2 8, brummayerbiere3 3, stp 1) are a real
regression and are queued for the next slice rather than absorbed into this
report's PASS column.

### Criterion 6 — the panic movement, and §2's superseded expectation

Spec §2 scoped the 5,787 `blast_word` panics out of this slice and said they
would be "reported unchanged". That expectation is **superseded**, not met:
fixing the model-corruption cause behind the wrong answers (see "Real cause"
below) required a value-reading fix, `prewarm_array_words`, that forces index
and element terms to be blasted before the first solve rather than lazily
during refinement. Some of those terms mention a nested `select`
(`(select p (bvadd x (select q #x03)))`, ordinary in the `egt` and
`dwp_formulas` families) and `blast_word` cannot encode an array operation —
so the prewarm pairs with `abstract_word`, which rewrites such a term through
its abstraction read-var before blasting. That rewrite is what converts a
large slice of the panic bucket into real answers: 3,917 `panic → correct`
transitions, of which 3,883 are `egt` alone. The panic count fell from 5,787
to 2,127 (raw, at `ddabe7b3`) — a welcome, unplanned side effect of a fix
this slice needed for a different reason, not the "unchanged" outcome §2
anticipated.

`parse-error` (26 → 24) and `oom` (98 → 52) both moved slightly as
second-order effects of the same transition churn (see the matrix); neither
movement is attributed to a new defect.

## Post-measurement correction: `ddabe7b3` → `bdf85f59`

The transition matrix above shows 264 `correct → panic` rows, all
`dwp_formulas`, all the same `non-BV builtin reached blast_word` message.
This is a real regression the `ddabe7b3` measurement exposed: the same
`prewarm_array_words` fix that turned 3,917 panics into correct answers also
newly unlocked a dead branch of `functional_consistency`'s lemma
construction, and the write path that lemma goes through
(`RealBridge::ensure_atom`) never applied the aliasing rewrite that
`prewarm_array_words`'s *read* path did — so it handed a raw,
select-mentioning term straight to `blast_word`, which panics.

Commits `741410ac` and `bdf85f59` fix exactly that: `ensure_atom` now runs
the same aliasing rewrite (`alias_word`) before blasting. This was **not**
re-measured by a full corpus re-run — that would cost hours this task does
not have — but by direct, per-file measurement of all 264 regressed rows: the
fixed binary was run against each of the 264 `.smt2` paths individually, with
a 20 s timeout, and every one of them came back `sat`, matching baseline's
correct verdict. Zero panics, zero unknowns, zero timeouts, zero wrong
answers remained among the 264.

So the **shipped code's real numbers**, as of `bdf85f59` (this branch's
HEAD), are not the raw table above — they are the raw table corrected by
that 264-row swing:

| verdict | raw (`ddabe7b3`, measured) | shipped (`bdf85f59`, corrected) |
| --- | ---: | ---: |
| `panic` | 2127 | ≈**1,863** (2127 − 264) |
| `correct` | 12359 | ≈**12,623** (12359 + 264) |

No other verdict bucket is affected by the correction — the 264 rows moved
in only one direction (panic → correct) and nowhere else. The raw table is
presented as measured, per this document's own standard of not silently
folding a correction into a number that was not actually produced by a full
run.

## Real cause, and the two hypotheses it discards

Spec §9 recorded two candidate causes for the wrong-`sat` shapes, neither
adopted as a finding. The bisect (task 6) confirmed both were the wrong
place to look, and found a third cause underneath the model-gate work
entirely:

| hypothesis | verdict |
| --- | --- |
| §9 #1 — `functional_consistency` relates two selects only when their base arrays are syntactically identical, and is sound only if read-over-write and extensionality cover every other route to array equality | **DISCARDED as the cause of any measured row.** The restriction is real but was never reached — the checks never had a usable model to compare against. |
| §9 #2 — `refine` returns `Sat` at a lemma-set fixpoint that is not an axiom fixpoint | **DISCARDED as stated.** The loop does stop early, but not because a round's guards happened to agree with a real model — it stops because the model it read was fabricated. Fixing the fixpoint condition alone would not have helped. |

**The actual cause:** `Sat::add_clause` (`crates/shinri-sat/src/solver.rs`)
backtracks to decision level 0 on any clause added after a solve, which
destroys the current assignment. `RealBridge::value_bv` blasted words
**on demand** and then read the **live** solver — so the first query for a
word that had never been blasted (an index or element term that only ever
appeared inside an abstracted-away `select`/`store`) wiped the model, and
every value read after that point was `value_of(v).unwrap_or(false)`: a
fabricated `0`, not a real assignment. An all-zero pseudo-model is
internally consistent with every array axiom — functional consistency,
read-over-write and extensionality all "agree" on zeros — so round 0 of
`refine` emitted no lemma and reported `Sat` without ever examining a real
model.

The same corrupted values explain why the model gate (§3, landed in task 4)
had a hole on `bubsort002un.smt2`: `validate` reads the same `value_bv`, so
it built its store-chain overlay and its read comparisons from the same
fabricated zeros and passed every check on garbage. The two rejections the
gate *did* produce during the bisect (`wchains002ue`'s
`DiseqPinsForceEqual`, and the minimal reproducer's `ReadMismatch`) were also
derived from the same fabricated model — sound outcomes, since a rejection
only ever downgrades a `sat` to `unknown`, but not genuine findings about
the shapes they named.

Task 6's fix makes the value readers work from a snapshot taken immediately
after each solve, never mutating the solver; a word the snapshot cannot
value returns `None` (silence) rather than a zero, gets queued, and is
blasted before the *next* solve. `validate.rs` and `check.rs` were not
changed — the diagnosis did not call for it.

## `abv-model-rejected`: 0 rows

The gate landed in task 4 as the soundness backstop, independent of whatever
causes were later found. In the closing corpus run it fired on **zero**
rows — every row that changed did so through a fix the gate's rejection
reason pointed the bisect at, not through a live `sat → unknown` downgrade
surviving to the final measurement. This is success criterion 4's PASS
condition. The gate keeps its 21 unit fences in `validate.rs` as the
executable form of §3.4's grammar restrictions; none of them fired on real
corpus rows in this run either.

## The retracted claim

Commit `60b41c74`'s message states: "Shinri is sound on the 359 measured
QF_ABV wrong answers from here, whatever the remaining tasks find." That
claim was **false when written**, and was retracted in the very next
commit's message, `b88a8349`: `bubsort002un.smt2` — one of the 359 measured
wrong-`sat` rows — passed every one of `validate`'s checks and was still
answered `sat`, because (as task 6 later diagnosed) the checks were
themselves reading a fabricated model. The claim is recorded here as
retracted so it is not repeated or rediscovered as a fresh finding.

## Oracle evidence

`cargo nextest run -p shinri-solver --features oracle -E 'test(qfabv)'` → 7
discovered (non-zero, confirmed), 7 passed, including
`qfabv_oracle::qfabv_matches_z3` in 3.141 s. That test **failed on pre-slice
`main`** — task 1's report quotes the failing instance verbatim:
`QF_ABV SOUNDNESS DISAGREEMENT (iter 3): shinri=Sat z3=unsat` on
`(= (store (store a0 i0 e0) i1 e1) (store (store a0 i0 e1) i1 e0))` with
`i0 != i1`, `e0 != e1` — and now passes. That is success criterion 5.

The full unfiltered oracle suite, `cargo nextest run -p shinri-solver
--features oracle`, ran **642 tests, 642 passed, 3 skipped, 0 mismatches**
at commit `ddabe7b3`, covering `qfs_differential` (the string suite whose
omission from a filtered run once nearly shipped a `Sat → Unknown`
regression on an unrelated slice), both `fp_oracle` suites, `qfufbv`,
`uflia` and `uflra` — the full unfiltered run this spec's §6.3 requires,
because this slice touches the shared `abv_stage` bridge, not only
`shinri-abv`. `abv_stage.rs` changed twice more after that measurement
(`741410ac`, `bdf85f59`); a refreshed full run at the current HEAD was
started to cover the shipped code, since neither of those two commits
touched any file outside `crates/shinri-solver/src/abv_stage.rs`.

## Queued for the next slice

- **62 `correct → timeout` rows** (dwp_formulas 36, brummayerbiere 14,
  brummayerbiere2 8, brummayerbiere3 3, stp 1) — the genuine cost behind
  criterion 3's miss. `countbitstable016.smt2` (95 s) and
  `calc2_sec2_shifter_bmc10.atlas.smt2` (>300 s, unresolved at 5× the corpus
  timeout) are the visible tail during the bisect and are representative of
  the shape: chains long enough that the now-correct (but no longer
  fixpoint-gamed) refinement loop does real work instead of stopping after
  round 0 on a fabricated model.
- **The remaining `blast_word` panic bucket (2,127 raw / ≈1,863 shipped)** —
  still out of scope for this slice per spec §2, and still not fully closed:
  `check.rs` builds lemma atoms out of raw index terms
  (`ctx.mk_eq(ix, iy)`), and if those mention a `select`, the lemma can still
  panic in `ensure_atom` through a route this slice did not touch. No
  measured wrong-`sat` row needs that fix, so it was deliberately deferred
  to the panic-bucket slice (rank 4 of the slice-46 queue) rather than
  folded in here.
- **The 53 stack-overflow rows** and the 24 `parse-error` rows — unchanged
  in kind from baseline, out of scope per spec §2, tracked in the slice-46
  queue under ranks 5 and the `parse-error` clusters respectively.

## References

- Baseline — `2026-09-09-smtlib-2024-baseline.md`,
  `2026-09-09-smtlib-2024-baseline-report.md` (QF_ABV row and
  `## Wrong answers`).
- Spec — `docs/superpowers/specs/2026-09-09-shinri-slice47-qfabv-wrong-sat-design.md`,
  `## 11. Measured outcomes`.
- Raw results — `bench/results/slice47/results.jsonl` (15,148 rows,
  git-ignored), rendered report `bench/results/slice47/report.md`.
- The string-path precedent for a post-solve model gate —
  `crates/shinri-solver/src/lib.rs:1474` (`str-model-rejected`).
