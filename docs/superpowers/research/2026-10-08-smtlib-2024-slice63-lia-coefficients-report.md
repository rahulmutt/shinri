# SMT-LIB 2024 re-run — slice 63 (constant coefficients in linear arithmetic) — shinri @ 58564ef

## Headline

Slice 63 teaches the arith classifier and `linearize` to accept `(- k)` and
other constant coefficients as linear, in lockstep (T1/T2). Before it, an
atom containing the shape was refused with `unknown:theory-refused`. The
benchmarked binary is `58564ef` (md5 `5fac825f…`); the base is `ea60d55`
(md5 `cc09e016…`).

- **`theory-refused` drops to 0.** The refused set (4,874 rows of
  `slice53`) had 4,871 `theory-refused` rows in the base run (3
  `miplib2003` rows were already `timeout` there). After: 0 of 4,874.
  The 2,000-row neutrality sample also had 188 base `theory-refused`
  rows; QF_SLIA had 1. All are gone.
- **Rows moved to `correct`: 983 of the 4,871** (all QF_LIA except 17
  QF_SLIA Norn rows and 1 QF_UFLIA `TwoSquares`; all `wrong = 0`).
- **New `timeout`/`oom` (reported, not gated): 3,100 `timeout`, 770
  `oom`.** All 770 `oom` rows are QF_LIA `nec-smt`; the 3,072 MB cap is
  what stops them. A further 18 QF_SLIA Norn rows land in
  `unknown` (9 `sat-budget`, 9 `str-model-rejected`).
- Unrefused rows in the neutrality sample (188): 33 `correct`, 25 `oom`,
  130 `timeout`. QF_SLIA 1 → `correct`.
- No row went `wrong`, `unverified` or stayed refused.

| logic | refused → correct | → timeout | → oom | → other unknown |
| --- | ---: | ---: | ---: | ---: |
| QF_LIA | 965 | 3,023 | 770 | 0 |
| QF_LRA | 0 | 58 | 0 | 0 |
| QF_SLIA | 17 | 0 | 0 | 18 |
| QF_UFLIA | 1 | 16 | 0 | 0 |
| total | 983 | 3,100 | 770 | 18 |

(The join counts QF_LIA `timeout` as 3,026 because it includes the 3
`miplib2003` rows that were already `timeout`.)

By family (refused set; `correct` / `timeout` / `oom`), QF_LIA:
CAV_2009_benchmarks 420 / 171 / 0; Bromberger 138 / 668 / 0;
dillig 145 / 88 / 0; rings_preprocessed 90 / 204 / 0;
convert 77 / 242 / 0; prime-cone 37 / 0 / 0; cut_lemmas 30 / 63 / 0;
Averest 7 / 12 / 0; slacks 7 / 225 / 0; miplib2003 6 / 7* / 0;
pb2010 5 / 76 / 0; check 2 / 0 / 0; nec-smt 1 / 1,270 / 770.
(* 10 in the join, minus the 3 base timeouts.)
QF_LRA `2017-Heizmann-UltimateInvariantSynthesis` 0 / 58 / 0;
QF_UFLIA `Certora` 0 / 16 / 0; QF_UFLIA `TwoSquares` 1 / 0 / 0;
QF_SLIA `2015-Norn` 17 correct, 18 other unknown.

### Success criteria (spec §8)

| # | Criterion | Result | Evidence |
| --- | --- | --- | --- |
| 1 | `wrong = 0` in every after run | **PASS** | `wrong after: 0` in all four joins |
| 2 | `theory-refused` drops by ≥ 4,700 | **PASS** | 4,871 → 0 on the refused set (join prints 4,874 → 0; see Discrepancies); 0 still refused, so no classification is needed |
| 3 | Each leaving row lands in `correct` / `unverified` (confirmed) / `timeout`/`oom` | **PASS** | 983 / 3,100 / 770 / 18 unknown; 0 `unverified`, so the ≥ 20-row confirmation sample is vacuous (nothing to confirm) |
| 4 | No `correct → non-correct` row reproduces on 3 re-runs of both binaries | **PASS, with one explained timing-edge row** | 84 rows × 6 runs; 1 row reproduces: `QF_UF/QG-classification/qg5/gensys_brn095.smt2`. See Verdict changes |
| 5 | `mise run ci` and the oracle suite green | **PASS** | ci 1857/1857 (6 skipped); oracle 866/866 vs base 859 |
| 6 | Neutrality and QF_SLIA samples change only at the timeout edge, 3/3 as noise | **PASS, with a load caveat** | sample changes are `correct`/`oom`/`parse-error` → `timeout`; host load was very high and unequal (below) |

## Commands

From the plan, without deviation except as noted. `B=/workspace/target/slice63-base`,
`A=/workspace/target/slice63-after`.

```bash
# base (worktree at ea60d55)
taskset -c 0-11 cargo build --release -p shinri-cli -p shinri-bench
cp target/release/shinri target/release/shinri-bench $B/
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle   # base count
# after (58564ef): gates
taskset -c 0-11 mise run ci
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle
# runs, detached, one chain per binary (refused -> arith -> sample -> slia)
setsid nohup sh -c "taskset -c 12-23 $X/shinri-bench run --logics <set> \
  --corpus <set corpus> --results /workspace/bench/results \
  --timeout 20 --mem-mb 3072 --jobs 3 --solver $X/shinri --run-id <id>; ..." &
# re-runs: 3x per binary on each correct->non-correct row
taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin $path
```

Corpora: refused = the 4,874 `slice53` `theory-refused` rows; arith sample =
2,000 rows from `random.Random(63)` over the other
QF_LIA/QF_LRA/QF_UFLIA/QF_UFLRA rows; neutrality = the slice-59 sample;
slia = 2,000 QF_SLIA rows from `random.Random(63)`. Deviations: the §8
row-set narrowing (see below); the re-runs used `xargs -P3` (script
`rerun1.sh`) rather than the plan's serial loop; `--jobs 3` throughout.

## Runs

`--timeout 20 --mem-mb 3072 --jobs 3`, cores 12–23 for every run. Start
times are the fixture's `started`; a run ends when the next starts (the
last at `finished.txt`). The bench fixture `sha` field is the invoking
tree's HEAD, not the binary's (`ea60d55` or `90ecaeb`); the md5 identifies
the binary.

| run id | md5 | commit | started (UTC, 2026-10-07) | finished | rows | load at launch (1/5/15 min) |
| --- | --- | --- | --- | --- | ---: | --- |
| slice63-base-refused | cc09e016 | ea60d55 | 10:15:55 | 10:39:06 | 4,874 | 82.21 / 73.22 / 63.12 |
| slice63-base-arith | cc09e016 | ea60d55 | 10:39:07 | 12:00:47 | 2,000 | not recorded |
| slice63-base-sample | cc09e016 | ea60d55 | 12:00:48 | 12:32:23 | 2,000 | not recorded |
| slice63-base-slia | cc09e016 | ea60d55 | 12:32:24 | 12:39:13 | 2,000 | not recorded |
| slice63-refused | 5fac825f | 58564ef | 12:40:13 | 19:42:58 | 4,874 | 81.48 / 53.50 / 31.40 |
| slice63-arith | 5fac825f | 58564ef | 19:43:00 | 21:15:40 | 2,000 | not recorded |
| slice63-sample | 5fac825f | 58564ef | 21:15:43 | 22:11:52 | 2,000 | not recorded |
| slice63-slia | 5fac825f | 58564ef | 22:11:55 | 22:20:15 | 2,000 | not recorded |

Only the first run of each chain recorded `uptime`. From the controller's
ledger the 1-minute load averaged about 70–80 during the base chain and
about 115–127 during the after chain. The after runs were therefore under
roughly 50% more host load, against a 20 s cap. The base refused run is
short because the base refuses those rows instantly.

## Verdict changes

Source: `target/slice63-after/join.txt`, `changed.tsv`.

| set | changed | notes |
| --- | ---: | --- |
| refused | 4,871 | all `theory-refused` → table above |
| arith sample | 117 | 39 `correct` → `timeout`; 76 `oom` → `timeout`; 2 `parse-error` → `timeout` |
| neutrality sample | 249 | 188 refused rows leave `theory-refused`; 44 `correct` → `timeout` (29 QF_UF, 9 QF_UFLIA, 4 QF_LIA, 2 QF_BVFP); 16 `oom` → `timeout`; 1 `parse-error` → `timeout` |
| slia sample | 4 | 1 `theory-refused` → `correct`; 2 `correct` → `unverified`; 1 `unverified` → `timeout` |

All 85 `correct → non-correct` rows (39 + 44 + 2) were re-run 3× per binary
(510 runs, 84 distinct paths: one path is in two sets).

- 63 rows `timeout` in all 6 runs; 9 `sat` and 3 `unsat` identical in both
  binaries; the other 8 are mixed (run-to-run flips in at least one
  binary, e.g. `timeout`/`unsat` both before and after). None are one-sided
  except the row below.
- **One row reproduces:**
  `QF_UF/QG-classification/qg5/gensys_brn095.smt2` is `unsat` 3/3 in the
  base and `timeout` 3/3 after. The change cannot reach it: QF_UF never
  enters the arithmetic code that changed. Interleaved re-timing on
  2026-10-08 at load 30–65: base 10.05 / 10.10 / 15.39 s, after
  10.22 / 12.13 / 12.74 s, all `unsat`. The overnight 3/3 timeouts ran at
  load ~115 against the 20 s cap, on a row that needs 10–15 s even
  quietly. I rule it a timing-edge row and criterion 4 PASS. The residual
  risk is a ~1 s code-layout perf change on QF_UF (compare slice 62's
  `Rex` drop-glue sensitivity), so a quiet-host timing check is queued.
- The two QF_SLIA rows the script flagged
  (`regex-lengths-00076-17`, `regex-small-00055-12`) are an artifact of
  the script, which has no known expected answer for `unverified` rows:
  both binaries say `sat` 3/3, the `correct → unverified` flip was the
  bench's z3 oracle timing out, and z3 `-T:120` and cvc5 both say `sat`,
  equal to shinri.
- Neither sample shows any `timeout → correct` or other improvement, only
  moves toward `timeout`. That one-sidedness matches the load asymmetry
  above and is why the quiet-host check is queued; it is not evidence of
  slowdown, because the unchanged-logic rows (29 QF_UF) account for a
  third of it.

## Still refused

None. `still-refused.txt` is empty: 0 rows in all four after runs, so no
cause classification or shape file is needed.

## Unverified confirmation

None. `unverified.txt` is empty: no row leaving `theory-refused` landed in
`unverified`, so the ≥ 20-row z3/cvc5 confirmation sample is vacuous.
(The slia sample's own `unverified` rows, 48 → 49, are pre-existing
oracle timeouts, covered above.)

## What changed versus the spec

1. **§8 row-set narrowing** (already amended in the spec): four narrowed
   sets instead of full four-logic base and after runs (about 18 h saved,
   since ~3,700 arith rows already time out).
2. **Oracle-count expectation.** The plan said base + 1. The 6
   non-feature-gated `lia_e2e` tests are also discovered under
   `--features oracle`, so base + 7 is right (859 → 866: 6 + 1 oracle).
   An arithmetic error in the plan; ruled in the ledger.
3. **Timing-edge ruling** on `gensys_brn095` for criterion 4 (above).
4. Base `theory-refused` is 4,871, not 4,874: 3 `miplib2003` rows were
   `timeout` in the base. Criterion 2 is unaffected.

## Gates

`target/slice63-gates.txt`:

- `mise run ci` at 58564ef: 1857 tests run, 1857 passed (8 slow), 6 skipped.
- Oracle (`-p shinri-solver --features oracle`) at 58564ef: 866 tests
  across 46 binaries (2 skipped), 866 passed. Base: 859 (859 passed, 2
  skipped).

## Queued for the next slice

Ordered.

1. **LIA timeout/oom population, for the re-baseline track to rank.**
   Base plus newly exposed, by family (refused set unless noted):
   - `oom` 770, all QF_LIA `nec-smt` (headline: a 3,072 MB cap hit; plus
     25 in the neutrality sample; 76 + 16 base `oom` rows in the samples
     now time out instead).
   - `timeout` 3,100: nec-smt 1,270; Bromberger 668; convert 242;
     slacks 225; rings_preprocessed 204; CAV_2009 171; dillig 88;
     pb2010 76; cut_lemmas 63; QF_LRA Heizmann 58; Certora 16;
     Averest 12; miplib2003 7 (+3 base timeouts).
   - Pre-existing arith timeout/oom population in the base: arith
     sample 630 timeout and 108 oom of 2,000 (about 3,700 across the
     logics, §8).
   - 18 QF_SLIA Norn rows now reach strings and end `unknown`:
     9 `sat-budget`, 9 `str-model-rejected`.
2. **Quiet-host timing check** of `gensys_brn095` and the 29 QF_UF
   `correct → timeout` sample rows, base vs after, interleaved, on an
   otherwise idle host; and re-run the arith/neutrality sample moves
   toward `timeout` under equal load.
3. Deferred minors from the ledger:
   - TDD order deviation in T1 (impl before red; red reconstructed by
     disabling the `Neg` branch);
   - `classify` no longer treats an arbitrary `TermNode::Const` as
     constant, only numerals and `(- c)`;
   - T2 has no counter enforcing that both accept and reject branches are
     hit (generator drift could make one vacuous);
   - mid-file `use` block in `linearity_lockstep_tests.rs`;
   - T3 base red evidence only for sign/compound/guard, not for
     left-sat/mirrored/Real;
   - T4 skips z3 `Unknown` via `continue` (bounded by the 90% floor);
   - T4 double-negation literal exercised only for positive `k`.
4. Rerun script: map `unverified` rows to their known expected answer.

## References

- Spec: `docs/superpowers/specs/2026-10-07-shinri-slice63-lia-const-coefficients-design.md`
- Plan: `docs/superpowers/plans/2026-10-07-shinri-slice63-lia-const-coefficients.md`
- Raw rows: `bench/results/slice63-{base-,}{refused,arith,sample,slia}/`
- Evidence: `target/slice63-after/{join.txt,changed.tsv,losses.txt,loss-reruns.txt}`,
  `target/slice63-gates.txt`, `target/slice63-base/oracle-count.txt`
- Previous report: `docs/superpowers/research/2026-10-07-smtlib-2024-slice62-length-consistent-seeds-report.md`
