# SMT-LIB 2024 re-run — slice 50 (QF_UFLIA compound shared terms, eager ⊤≠⊥) — shinri @ 4f8f0729b4dd

Run-id `slice50` (branch) and `slice50-base` (pre-slice `main`):

```
BENCH_LOGICS=QF_UF,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA,QF_DT BENCH_RUN_ID=slice50 mise run bench-run
target/release/shinri-bench run --solver <worktree@1fe3658>/target/release/shinri \
  --logics QF_UF,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA,QF_DT \
  --timeout 20 --mem-mb 3072 --jobs 6 --run-id slice50-base
BENCH_RUN_ID=slice50 mise run bench-report
BENCH_RUN_ID=slice50-base mise run bench-report
```

Both runs used the baseline limits: 20 s, 3072 MB, 6 jobs, cgroup `cpu.max`
`800000 100000`, `memory.max` 34359738368. Both were pinned with
`taskset -c 12-23`. Each covers 121,481 instances.

| run | solver | `solver_md5` | started | log last written | wall-clock |
| --- | --- | --- | --- | --- | --- |
| `slice50` | `target/release/shinri` @ `4f8f072` (branch HEAD) | `b99562b3db7ca436367a9fd7d96c3bc8` | 2026-09-29T18:44:09Z | 21:56:53Z | ~3 h 13 min |
| `slice50-base` | worktree @ `1fe3658` (merge base) | `8dd709d857767b757c9194189f54c993` | 2026-09-29T12:30:09Z | 15:51:25Z | ~3 h 21 min |

Both `solver_md5` values match the two binaries on disk. The base run's
fixture header records `sha d70d381548c1-dirty`. That is the checkout the
bench harness ran from, not the solver's commit. The harness records the
workspace HEAD, and `--solver` pointed at the `1fe3658` worktree binary.

Final log lines:

```
slice50       121481/121481  correct=56193 wrong=39 status-suspect=0 parse-error=1458 panic=0 oom=15 timeout=1521 unknown=60911 unverified=1344 malformed=0
slice50-base  121481/121481  correct=56185 wrong=50 status-suspect=0 parse-error=1458 panic=0 oom=18 timeout=1502 unknown=60898 unverified=1370 malformed=0
```

**Load difference between the two runs (disclosed; it matters for boundary
rows).** The base run overlapped with cargo builds and test suites (Tasks
2–5 and the final review) pinned to cores 0–11. Those cores are disjoint from
the bench's 12–23, but memory bandwidth and the z3 oracle's time were shared.
The branch run had a mostly idle machine. That difference can favour the
branch on rows near the 20 s boundary and on oracle-timeout rows. So every
`→ correct` row in the logics with ≤ 30 such rows was A/B-timed too, not
only the `correct → *` rows. The results are below: every non-oracle
`→ correct` row except three turned out to be boundary or load noise.

**How the transitions were computed.** The brief's `transitions.py` is scratch
tooling and is not committed. It loads each `results.jsonl` keyed by `path`,
intersects the two key sets, and tallies `(before verdict, after verdict)`
per logic and per family (`path.split("/")[1]`). The same-path check found
**121,481 common paths, 0 missing, 0 extra.** Every per-logic count below
closes under `new = old − outbound + inbound`.

**A/B method.** Each A/B row was run once per binary, one run at a time,
under `taskset -c 12-23 timeout 20 prlimit --as=3 GiB`, with the base binary
first. The machine was otherwise idle. The rows formerly `wrong` were also
re-run on the branch with a 120 s timeout, 6 at a time.

## Headline

- **QF_UFLIA `wrong` fell 11 → 0.** All 11 rows (`mathsat/Wisa` 9,
  `wisas` 2) are now `timeout`. The pre-slice binary answers the same wrong
  `sat` on all 11 in 3.4–14.3 s. The branch does not answer any of them
  within 20 s in the A/B, except `xs-05-08-4-2-5-4` at 19.9 s. With a 120 s
  timeout, the branch answers **`unsat` (correct) on 4** and gives no answer
  on 7. **It answers `sat` on 0.** Only `xs-05-08-4-2-5-4` is tied to §1.3
  (Tasks 1/2). No other row is attributed.
- **0 `correct → wrong` and 0 `* → wrong` in all six logics.** QF_S `wrong`
  (2) and QF_SLIA `wrong` (37) are the same paths with the same answers.
- **Criterion 5 is MISSED for QF_SLIA, QF_UFLIA and QF_UF.** The decomposition
  follows. Two of these misses are real, traced slice costs:
  - **QF_SLIA: 16 rows went `correct → unknown:sat-budget`.** These are
    `2019-Jiang/slent` ×7 and `2019-Leetcode/findAnagrams` ×9, and the loss is
    deterministic. In the A/B, pre-slice gives `sat` in 86–727 ms and the
    branch gives `unknown` in 168–1,232 ms. Instrumentation shows the
    branch **exhausts the string-path cumulative simplex pivot budget**
    (`STRING_PATH_PIVOT_BUDGET` = 2,000), which pre-slice does not. A
    diagnostic toggle that skips `mark_constrained(v_t)` in
    `define_shared_compound` restores `sat` on all 16.
  - **QF_UFLIA: 2 Wisa rows went `correct → timeout`**
    (`xs-06-07-4-5-4-2`, `xs-07-06-4-1-5-3`, both `:status sat`). Pre-slice
    answers `sat` in 10.9 and 13.0 s, and the branch does not answer in 20 s
    (or in 90 s). The same toggle gives `sat` in 19.0 and 15.5 s, with
    about 3,000–4,000 `define_shared_compound` calls instead of more than 1.18 M in 90 s.
  - The rest of the QF_UFLIA and QF_UF shortfall (Hash ×3, QF_UF qg7 ×2,
    `SEQ038_size6`) is boundary rows at 16.5–20 s that both binaries answer,
    or nearly answer, in the A/B. They do not meet the brief's exclusion test
    ("base also fails"), so they stay in the count.
- **Spec §9's un-banking trigger for the unit-difference class join fired,
  and the join was built (Task 8) and not adopted.** Criterion 6's A/B plus
  the instrumented runs attributed 18 `correct → {unknown, timeout}` rows to
  the extra probing caused by marking compound shared terms constrained. The
  join recovered none of them (see "Un-banked §9 class join: tried, not
  adopted").
- **Real improvements (A/B-confirmed):** QF_UFLIA `mathsat/Hash/hash_sat_03_12`
  (pre-slice no answer in 20 s, branch `sat` 9.8 s). QF_SLIA
  `20180523-Reynolds/kaluza/sat/small/{indexof.corecstrs,search}.readable`
  (pre-slice `unknown`, branch `sat` in 61 and 10 ms). No cause is claimed.
  Every other `→ correct` row is noise from the base run's load: 26 oracle
  flips, and 8 rows that both binaries answer or both fail in the A/B.
- **Criterion 5 miss: accepted (decided exception, not a relaxation).** See
  "Un-banked §9 class join: tried, not adopted".
- **Criteria:** 1 PASS, 2 PASS (on the answer; the corpus row is a 20 s
  `timeout`), 3 PASS (0), 4 PASS (11 → 0), **5 MISSED** (QF_SLIA −14,
  QF_UFLIA −3, QF_UF −3 after exclusions), 6 measured (19 rows confirmed
  slower on the branch), 7 measured (0 rows), 8 measured (QF_SLIA 37 → 37,
  QF_S 2 → 2, same paths).

## Comparison run used

Spec §7 names `slice49` (QF_DT, QF_UF, QF_UFLIA, QF_UFLRA, QF_S) and
`baseline-8de004d44944` (QF_SLIA) as comparison runs. Both are git-ignored,
and **neither `results.jsonl` exists on this machine.** Per brief Step 2, the
comparison run for every logic is therefore the **same-machine base run
`slice50-base`**, built from merge base `1fe3658`. It is a stricter
comparison: it removes the hardware and slice-to-slice differences, and every
delta below is a slice-50 delta. The only confound left is the load
difference disclosed above. Spec §7's table is reported alongside as
context.

## Per-logic matrix (this run)

Copied from `bench/results/slice50/report.md`.

| logic | total | correct | wrong | status-suspect | parse-error | panic | oom | timeout | unknown | unverified | malformed | decided% | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_DT | 8700 | 8106 | 0 | 0 | 0 | 0 | 0 | 583 | 11 | 0 | 0 | 93.2 | 4 | 7 |
| QF_S | 18940 | 16025 | 2 | 0 | 0 | 0 | 0 | 8 | 2809 | 96 | 0 | 84.6 | 4 | 17 |
| QF_SLIA | 84395 | 24798 | 37 | 0 | 195 | 0 | 0 | 43 | 58074 | 1248 | 0 | 29.4 | 4 | 14 |
| QF_UF | 7503 | 7118 | 0 | 0 | 34 | 0 | 0 | 351 | 0 | 0 | 0 | 94.9 | 73 | 4232 |
| QF_UFLIA | 659 | 102 | 0 | 0 | 0 | 0 | 5 | 535 | 17 | 0 | 0 | 15.5 | 2198 | 12252 |
| QF_UFLRA | 1284 | 44 | 0 | 0 | 1229 | 0 | 10 | 1 | 0 | 0 | 0 | 3.4 | 7 | 72 |
| all | 121481 | 56193 | 39 | 0 | 1458 | 0 | 15 | 1521 | 60911 | 1344 | 0 | 46.3 | 4 | 52 |

The comparison run, from `bench/results/slice50-base/report.md`:

| logic | total | correct | wrong | parse-error | oom | timeout | unknown | unverified | decided% | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_DT | 8700 | 8103 | 0 | 0 | 0 | 586 | 11 | 0 | 93.1 | 5 | 9 |
| QF_S | 18940 | 16020 | 2 | 0 | 0 | 11 | 2808 | 99 | 84.6 | 10 | 89 |
| QF_SLIA | 84395 | 24789 | 37 | 195 | 0 | 41 | 58062 | 1271 | 29.4 | 7 | 20 |
| QF_UF | 7503 | 7124 | 0 | 34 | 0 | 345 | 0 | 0 | 94.9 | 69 | 4211 |
| QF_UFLIA | 659 | 105 | 11 | 0 | 8 | 518 | 17 | 0 | 15.9 | 2355 | 12170 |
| QF_UFLRA | 1284 | 44 | 0 | 1229 | 10 | 1 | 0 | 0 | 3.4 | 4 | 68 |
| all | 121481 | 56185 | 50 | 1458 | 18 | 1502 | 60898 | 1370 | 46.3 | 8 | 84 |

(status-suspect, panic and malformed are 0 in every row.) The median and p90
columns are shaped by the load difference, so no performance claim is made
from them.

## Verdict counts per logic, against spec §7's comparison table

| logic | verdict | §7 comparison (`slice49` / `baseline-8de004d44944`) | `slice50-base` | `slice50` | delta vs base |
| --- | --- | ---: | ---: | ---: | ---: |
| QF_DT | `correct` | 8,105 | 8,103 | **8,106** | +3 |
| QF_DT | `timeout` | 584 | 586 | 583 | −3 |
| QF_DT | `unknown:sat-budget` | 11 | 11 | 11 | 0 |
| QF_UF | `correct` | 7,111 | 7,124 | **7,118** | **−6** |
| QF_UF | `timeout` | 358 | 345 | 351 | +6 |
| QF_UF | `parse-error` | 34 | 34 | 34 | 0 |
| QF_UFLIA | `correct` | 104 | 105 | **102** | **−3** |
| QF_UFLIA | `wrong` | 11 | 11 | **0** | −11 |
| QF_UFLIA | `timeout` | 522 | 518 | 535 | +17 |
| QF_UFLIA | `oom` | 5 | 8 | 5 | −3 |
| QF_UFLIA | `unknown:theory-refused` | 17 | 17 | 17 | 0 |
| QF_UFLRA | all verdicts | 44 correct, 1,229 pe, 10 oom, 1 timeout | identical | identical | 0 |
| QF_S | `correct` | 16,023 | 16,020 | **16,025** | +5 |
| QF_S | `wrong` | 2 | 2 | 2 | 0 |
| QF_S | `timeout` | 9 | 11 | 8 | −3 |
| QF_S | `unknown` (all reasons) | 2,809 | 2,808 | 2,809 | +1 (str-model-rejected 1,032 → 1,033) |
| QF_S | `unverified` | 97 | 99 | 96 | −3 |
| QF_SLIA | `correct` | 24,799 | 24,789 | **24,798** | +9 |
| QF_SLIA | `wrong` | 37 | 37 | 37 | 0 |
| QF_SLIA | `timeout` | 41 | 41 | 43 | +2 |
| QF_SLIA | `unknown:sat-budget` | — | 4,186 | 4,198 | +12 |
| QF_SLIA | `unknown` (all reasons) | 58,063 | 58,062 | 58,074 | +12 |
| QF_SLIA | `unverified` | 1,260 | 1,271 | 1,248 | −23 |
| QF_SLIA | `parse-error` | 195 | 195 | 195 | 0 |

Against spec §7's comparison table, too, QF_UFLIA `correct` (102 < 104) and
QF_SLIA `correct` (24,798 < 24,799) are below. QF_UF (7,118 ≥ 7,111), QF_DT,
QF_S and QF_UFLRA are not.

QF_UFLIA per family (`slice50-base` → `slice50`):

| family | base | branch |
| --- | --- | --- |
| `mathsat/Wisa` (223) | correct 2, **wrong 9**, timeout 212 | correct 0, **wrong 0**, timeout 223 |
| `wisas` (108) | **wrong 2**, timeout 106 | **wrong 0**, timeout 108 |
| `mathsat/Hash` (198) | correct 83, timeout 115 | correct 82, timeout 116 |
| `mathsat/EufLaArithmetic` (33) | timeout 33 | timeout 33 |
| `TwoSquares` (21) | correct 20, theory-refused 1 | identical |
| `20230314-Jaroslav-Bendik-Certora` (76) | timeout 52, oom 8, theory-refused 16 | timeout 55, oom 5, theory-refused 16 |

## Transition matrices (changed cells only)

| logic | before | after | count | families |
| --- | --- | --- | ---: | --- |
| QF_DT | `timeout` | `correct` | 3 | 20230720-blocksworld 3 |
| QF_S | `timeout` | `correct` | 2 | 20230329-automatark-lu 2 |
| QF_S | `timeout` | `unknown:str-model-rejected` | 1 | 20230329-automatark-lu 1 |
| QF_S | `unverified` | `correct` | 3 | 20230329-automatark-lu 3 |
| QF_SLIA | `correct` | `unknown:sat-budget` | 16 | 2019-Jiang 7, 2019-Leetcode 9 |
| QF_SLIA | `unknown:sat-budget` | `correct` | 2 | 20180523-Reynolds 2 |
| QF_SLIA | `unknown:sat-budget` | `timeout` | 2 | 2019-Leetcode 2 |
| QF_SLIA | `unverified` | `correct` | 23 | 20230327-stringfuzz-lu 19, 20230329-denghang 4 |
| QF_UF | `correct` | `timeout` | 8 | QG-classification 6, SEQ 2 |
| QF_UF | `timeout` | `correct` | 2 | QG-classification 2 |
| QF_UFLIA | `correct` | `timeout` | 5 | mathsat 5 (Hash 3, Wisa 2) |
| QF_UFLIA | `oom` | `timeout` | 3 | 20230314-Jaroslav-Bendik-Certora 3 |
| QF_UFLIA | `timeout` | `correct` | 2 | mathsat 2 (Hash 2) |
| QF_UFLIA | `wrong` | `timeout` | 11 | mathsat 9 (Wisa 9), wisas 2 |

QF_UFLRA has no changed cell.

Closure, `new = old − outbound + inbound`:

- QF_DT `correct` 8,103 − 0 + 3 = 8,106; `timeout` 586 − 3 + 0 = 583.
- QF_S `correct` 16,020 − 0 + 5 = 16,025; `timeout` 11 − 3 + 0 = 8;
  `unverified` 99 − 3 + 0 = 96; `str-model-rejected` 1,032 − 0 + 1 = 1,033.
- QF_SLIA `correct` 24,789 − 16 + 25 = 24,798; `sat-budget` 4,186 − 4 + 16
  = 4,198; `timeout` 41 − 0 + 2 = 43; `unverified` 1,271 − 23 + 0 = 1,248.
- QF_UF `correct` 7,124 − 8 + 2 = 7,118; `timeout` 345 − 2 + 8 = 351.
- QF_UFLIA `correct` 105 − 5 + 2 = 102; `wrong` 11 − 11 + 0 = 0;
  `timeout` 518 − 2 + 19 = 535; `oom` 8 − 3 + 0 = 5.

**Oracle-side flips (29 rows, noise).** All 26 `unverified → correct` rows
(QF_S 3, QF_SLIA 23) have `:status unknown` and **the same shinri answer on
both runs**. In the base run the z3 oracle timed out, and in the branch run
it confirmed. This is the base-run load at work. QF_S `instance10273` (named
in spec §7) is one of the three QF_S rows. The QF_S `timeout →
str-model-rejected` row (`instance04583`) and the two QF_SLIA
`sat-budget → timeout` rows (`findAnagrams/289031e2…`, `a7db18d5…`) move
between non-answers and do not enter any criterion.

## Success criteria

| # | criterion | gate | result |
| --- | --- | --- | --- |
| 1 | Tasks 1–3's tests failed on pre-slice `main` and pass now | hard | **PASS** (see *Oracle and test evidence*) |
| 2 | §1.2 repro and `xs-05-08-4-2-5-4.smt2` answer `unsat` | hard | **PASS**: repro `unsat` (pre-slice `sat`); Wisa row `unsat` standalone in 19.9 s (A/B), 20.3 s (final-fix report), 27.3 s (6-way parallel re-run). **Its corpus row is `timeout` (20,007 ms)**, not `correct` |
| 3 | `correct → wrong`, all six logics | **0**, hard | **PASS: 0** |
| 4 | QF_UFLIA `wrong` ≤ 11 | hard | **PASS: 11 → 0** (every row goes to `timeout`; per-row table below) |
| 5 | per-logic `correct` ≥ comparison run | hard | **MISSED** for QF_SLIA (−14), QF_UFLIA (−3) and QF_UF (−3) after exclusions; PASS for QF_DT, QF_S and QF_UFLRA (decomposed below) |
| 6 | `correct → {timeout, unknown, oom}` | measured | 29 rows: **19 confirmed slower on the branch** (16 QF_SLIA, 2 QF_UFLIA Wisa, 1 QF_UF by 0.4 s), 3 boundary noise, 7 not reproduced on either binary |
| 7 | `* → wrong` from a non-`correct` verdict | measured | **0 rows** (there is no `→ wrong` cell) |
| 8 | QF_SLIA `wrong` delta; QF_S 2 wrong rows | measured | QF_SLIA 37 → 37 (denghang 35, Noetzli 2), same paths and answers; QF_S 2 → 2 (`instance09174`, `instance10773`), unchanged |

### Criterion 4: every formerly `wrong` QF_UFLIA row

All 11 have `:status unsat`. "Pre-slice" and "branch 20 s" are the A/B runs.
"Branch 120 s" is a separate re-run, 6 at a time.

| row | corpus base | corpus branch | pre-slice A/B | branch A/B (20 s) | branch 120 s |
| --- | --- | --- | --- | --- | --- |
| `mathsat/Wisa/xs-05-08-4-2-5-4` | wrong 4,270 ms | timeout | `sat` 4.1 s | **`unsat` 19.9 s** | `unsat` 27.3 s |
| `mathsat/Wisa/xs-05-12-1-4-2-1` | wrong 3,380 ms | timeout | `sat` 4.2 s | none | `unsat` 31.3 s |
| `mathsat/Wisa/xs-05-16-1-5-4-3` | wrong 3,494 ms | timeout | `sat` 4.5 s | none | `unsat` 30.9 s |
| `mathsat/Wisa/xs-05-20-5-1-4-2` | wrong 4,414 ms | timeout | `sat` 4.6 s | none | `unsat` 34.3 s |
| `mathsat/Wisa/xs-06-15-4-1-4-1` | wrong 13,458 ms | timeout | `sat` 12.9 s | none | none |
| `mathsat/Wisa/xs-06-19-3-3-4-4` | wrong 7,091 ms | timeout | `sat` 6.8 s | none | none |
| `mathsat/Wisa/xs-07-10-2-4-5-3` | wrong 14,179 ms | timeout | `sat` 14.0 s | none | none |
| `mathsat/Wisa/xs-07-14-1-1-1-1` | wrong 14,322 ms | timeout | `sat` 13.8 s | none | none |
| `mathsat/Wisa/xs-07-18-1-1-4-1` | wrong 12,379 ms | timeout | `sat` 12.3 s | none | none |
| `wisas/xs_6_11` | wrong 4,935 ms | timeout | `sat` 4.8 s | none | none |
| `wisas/xs_8_13` | wrong 11,135 ms | timeout | `sat` 10.8 s | none | none |

Pre-slice reproduces all 11 wrong answers, so the slice changed these
answers. No branch run answered `sat` on any of them. Only
`xs-05-08-4-2-5-4` has a trace to §1.3 (Task 1's reduction; Task 2 Step 7).
For the other 10, the report claims only what the table shows. **Spec §9's
approach-B trigger ("criterion 4 leaves Wisa rows `wrong` with no named
cause") does not fire: no row is left `wrong`.** Seven rows are now a
non-answer at 120 s.

### Criterion 5: decomposed, not relaxed

Exclusion rule (brief Step 6 and spec §7): a row is excluded only if the
pre-slice binary also fails to answer within 20 s in the A/B, if it is an
oracle-side flip, or if spec §7 pre-declares it (QF_S `instance10273`, QF_UF
`qg5`). Excluded rows are dropped from both sides.

| logic | base | branch | excluded rows (in / out) | adjusted delta | verdict |
| --- | ---: | ---: | --- | ---: | --- |
| QF_DT | 8,103 | 8,106 | in: 3 blocksworld `timeout → correct` (both binaries answer `unsat` in A/B: base 18.8/6.7/7.0 s, branch 19.2/6.9/7.1 s, so the base-run timeout was load) | 0 | PASS |
| QF_S | 16,020 | 16,025 | in: 3 oracle flips (incl. `instance10273`); 2 `timeout → correct` (`instance10357`, `instance12154`: both answer `sat`, base 12.4/2.6 s, branch 12.3/2.6 s) | 0 | PASS |
| QF_SLIA | 24,789 | 24,798 | in: 23 oracle flips | **−14** (−16 real, +2 real) | **MISSED** |
| QF_UF | 7,124 | 7,118 | out: qg5 `icl621`, `icl787`, `icl802`, `icl987` (pre-declared), `SEQ038_size9` (base none in A/B); in: qg5 `icl157`, `icl158` (pre-declared; both none in A/B) | **−3** | **MISSED** |
| QF_UFLIA | 105 | 102 | none qualify | **−3** | **MISSED** |
| QF_UFLRA | 44 | 44 | — | 0 | PASS |

**QF_SLIA −14.** The 16 `correct → unknown:sat-budget` rows are a real,
deterministic slice cost (criterion 6 table). The +2 is
`20180523-Reynolds/kaluza/sat/small/indexof.corecstrs.readable` and
`search.readable`: pre-slice `unknown` in 138/43 ms, branch `sat` in 61/10 ms
in the A/B. That is a real improvement with no traced cause.

**QF_UFLIA −3.** Out:

- Wisa `xs-06-07-4-5-4-2` and `xs-07-06-4-1-5-3` are real (traced, below).
- `Hash/hash_sat_04_11`, `hash_sat_04_14` and `hash_uns_05_18` are boundary
  rows. Both binaries answer correctly in the A/B: base 17.3/17.3/18.7 s,
  branch 18.5/18.0/19.0 s. The branch is 0.3–1.2 s slower in a single A/B
  run. That is not enough to call it a cost, and the rows do not meet the
  exclusion test either.

In:

- `Hash/hash_sat_03_12` is real: pre-slice gives no answer in 20 s, the
  branch gives `sat` in 9.8 s.
- `Hash/hash_sat_06_06` is a boundary row: base 19.3 s, branch 15.3 s.

Net −2 real, −1 boundary.

**QF_UF −3.** QF_UF has no arithmetic, so `define_shared_compound` never runs
there. The slice's only QF_UF-reachable change is the eager ⊤/⊥ install (Task
3). The three rows that stay after exclusion:

- `QG-classification/qg7/gensys_icl_sk005` (base `unsat` 16.5 s, branch
  `unsat` 16.8 s) and `qg7/iso_brn_repgen_sk035` (base `sat` 18.2 s, branch
  `sat` 19.8 s). Neither binary times out in the A/B.
- `SEQ/SEQ038_size6`: base `unsat` 19.6 s, branch no answer at 20.02 s. This
  meets the letter of "base answers, branch does not", by 0.4 s in a single
  run.

No trace ties any of them to Task 3, and none is claimed. They are listed
here, and the miss is left as a miss.

### Criterion 6: every `correct → {timeout, unknown, oom}` row with its A/B result

| logic | row | corpus base → branch | pre-slice A/B | branch A/B | class |
| --- | --- | --- | --- | --- | --- |
| QF_SLIA | `2019-Jiang/slent/slent_kaluza_101_sink` | correct 201 ms → sat-budget 171 ms | `sat` 168 ms | `unknown` 179 ms | **slice cost** |
| QF_SLIA | `2019-Jiang/slent/slent_kaluza_106_sink` | correct → sat-budget | `sat` 159 ms | `unknown` 168 ms | **slice cost** |
| QF_SLIA | `2019-Jiang/slent/slent_kaluza_202_sink` | correct → sat-budget | `sat` 173 ms | `unknown` 202 ms | **slice cost** |
| QF_SLIA | `2019-Jiang/slent/slent_kaluza_203_sink` | correct → sat-budget | `sat` 199 ms | `unknown` 203 ms | **slice cost** |
| QF_SLIA | `2019-Jiang/slent/slent_kaluza_213_sink` | correct → sat-budget | `sat` 204 ms | `unknown` 229 ms | **slice cost** |
| QF_SLIA | `2019-Jiang/slent/slent_kaluza_215_sink` | correct → sat-budget | `sat` 200 ms | `unknown` 209 ms | **slice cost** |
| QF_SLIA | `2019-Jiang/slent/slent_kaluza_73_sink` | correct → sat-budget | `sat` 178 ms | `unknown` 177 ms | **slice cost** |
| QF_SLIA | `2019-Leetcode/findAnagrams/209a7c61…` | correct → sat-budget | `sat` 235 ms | `unknown` 519 ms | **slice cost** |
| QF_SLIA | `2019-Leetcode/findAnagrams/519069b8…` | correct → sat-budget | `sat` 140 ms | `unknown` 335 ms | **slice cost** |
| QF_SLIA | `2019-Leetcode/findAnagrams/8b28a807…` | correct → sat-budget | `sat` 727 ms | `unknown` 991 ms | **slice cost** |
| QF_SLIA | `2019-Leetcode/findAnagrams/a709c5b3…` | correct → sat-budget | `sat` 224 ms | `unknown` 412 ms | **slice cost** |
| QF_SLIA | `2019-Leetcode/findAnagrams/b163e9e2…` | correct → sat-budget | `sat` 301 ms | `unknown` 601 ms | **slice cost** |
| QF_SLIA | `2019-Leetcode/findAnagrams/bee13332…` | correct → sat-budget | `sat` 477 ms | `unknown` 1,048 ms | **slice cost** |
| QF_SLIA | `2019-Leetcode/findAnagrams/d9b08f75…` | correct → sat-budget | `sat` 404 ms | `unknown` 651 ms | **slice cost** |
| QF_SLIA | `2019-Leetcode/findAnagrams/f95f85bd…` | correct → sat-budget | `sat` 86 ms | `unknown` 207 ms | **slice cost** |
| QF_SLIA | `2019-Leetcode/findAnagrams/fb27efc3…` | correct → sat-budget | `sat` 535 ms | `unknown` 1,232 ms | **slice cost** |
| QF_UFLIA | `mathsat/Wisa/xs-06-07-4-5-4-2` | correct 11,718 ms → timeout | `sat` 10.9 s | none | **slice cost** |
| QF_UFLIA | `mathsat/Wisa/xs-07-06-4-1-5-3` | correct 12,884 ms → timeout | `sat` 13.0 s | none | **slice cost** |
| QF_UFLIA | `mathsat/Hash/hash_sat_04_11` | correct 18,168 ms → timeout | `sat` 17.3 s | `sat` 18.5 s | not reproduced (boundary) |
| QF_UFLIA | `mathsat/Hash/hash_sat_04_14` | correct 18,107 ms → timeout | `sat` 17.3 s | `sat` 18.0 s | not reproduced (boundary) |
| QF_UFLIA | `mathsat/Hash/hash_uns_05_18` | correct 19,684 ms → timeout | `unsat` 18.7 s | `unsat` 19.0 s | not reproduced (boundary) |
| QF_UF | `QG-classification/qg5/gensys_icl621` | correct 19,480 ms → timeout | none | `unsat` 18.8 s | boundary noise (qg5; base fails) |
| QF_UF | `QG-classification/qg5/gensys_icl787` | correct 19,042 ms → timeout | none | `unsat` 19.8 s | boundary noise (qg5; base fails) |
| QF_UF | `QG-classification/qg5/gensys_icl802` | correct 19,811 ms → timeout | `unsat` 19.4 s | `unsat` 19.4 s | not reproduced (qg5, pre-declared) |
| QF_UF | `QG-classification/qg5/gensys_icl987` | correct 18,895 ms → timeout | `unsat` 18.4 s | `unsat` 18.6 s | not reproduced (qg5, pre-declared) |
| QF_UF | `QG-classification/qg7/gensys_icl_sk005` | correct 18,343 ms → timeout | `unsat` 16.5 s | `unsat` 16.8 s | not reproduced (boundary) |
| QF_UF | `QG-classification/qg7/iso_brn_repgen_sk035` | correct 18,642 ms → timeout | `sat` 18.2 s | `sat` 19.8 s | not reproduced (boundary) |
| QF_UF | `SEQ/SEQ038_size6` | correct 19,807 ms → timeout | `unsat` 19.6 s | none (20.02 s) | branch slower, by 0.4 s |
| QF_UF | `SEQ/SEQ038_size9` | correct 17,262 ms → timeout | none | `unsat` 18.3 s | boundary noise (base fails) |

**Trace for the 18 traced rows (16 QF_SLIA, 2 QF_UFLIA).** This was a
throwaway instrumented build of `4f8f072` in a scratch worktree, not
committed. It adds an `eprintln!` per `define_shared_compound` call and at
each budget exit (arith pivot and branch budgets, combiner round cap, string
`Unknown`, SAT step budget and guard bail-outs). The same pivot probes were
added to a `1fe3658` build.

- **QF_SLIA, all 16:** the only budget exit that fires is
  `STRING_PATH_PIVOT_BUDGET` (2,000 cumulative pivots per solve). It fires
  25–816 times per run. `define_shared_compound` runs 63–185 times per run.
  The `findAnagrams` inputs contain compound Int terms such as
  `(- (str.len p) 1)` and `(- (- (str.len p) 1) 1)`. The instrumentation
  counted calls, not which terms. On the
  seven `slent` rows, pre-slice's highest pivot count at a feasible check is
  1,938, and it never trips the budget. The branch trips it. On four of the
  `findAnagrams` rows, pre-slice also trips the budget inside probes (152–528
  times) and still reaches `sat`. On the branch the solve ends `Unknown`, and
  no other budget exit fires. Which of the branch's trips propagated was not
  traced. The trips are cumulative per solve, so any check after the
  2,000th pivot can trip.
- **Which part of the change?** A runtime toggle in the diagnostic build
  first skips marking the linearization leaves constrained (the final-fix
  change, `4f8f072`). All 16 SLIA rows still give `unknown`. It then also
  skips `mark_constrained(v_t)`, keeping the definitional row and pin. All 16
  give `sat`. The two Wisa rows behave the same way under the 90 s diagnostic
  run:
  - Default and leaves-unmarked give no answer, with more than 1.18 M
    `define_shared_compound` calls. That means more than 1.18 M final checks,
    because each final check re-ensures every shared term.
  - `v_t` unmarked too gives `sat` in 19.0 s and 15.5 s, with 3,000 and
    4,016 calls.

  So the cost is the **extra `entailed_equalities` / MBTC probing over
  compound shared terms that `mark_constrained(v_t)` turns on**. This is
  exactly spec §9's un-banking condition for the unit-difference class join.
  Skipping `mark_constrained(v_t)` is **not** a candidate fix: it reinstates
  the second half of §1.3, where the pair is never probed. The toggle was
  only a diagnostic.

## Oracle and test evidence

**Criterion 1: red on pre-slice code, green now.**

- Task 1 (red on pre-slice `main`, recorded in `task-1-report.md`):
  - `uflia_e2e`: 9 run, 7 failed, each `left: Sat, right: Unsat` (`add`,
    `add_zero`, `mul`, `nested_sub`, `cancelling`, `nested_uf_leaf`,
    `two_compound_args_equal`). The sat-direction and nonlinear-guard tests
    passed, as designed.
  - `uflra_e2e slice50_real_compound_arg_unsat`: FAIL, `left: Sat, right:
    Unsat`.
  - `shinri-arith compound_shared_term_is_defined_by_its_linearization`:
    FAIL, `(+ a 1) must take a + 1 = 1`, left 0, right 1.
- Task 2:
  - `compound_definition_is_reinstalled_after_pop`: RED `level 1: (+ a 1) =
    1`, left `DeltaRational { c: 0 }`, right `{ c: 1 }`.
  - Fix round 1 `existing_diff_slack_is_not_redefined_after_pivot`: RED `re-assert
    must not re-basify s`.
- Task 3:
  - RED 1: `E0599 no method install_truth_terms`.
  - RED 2, with the eager calls commented out: 3 run, 3 failed.
    `lazy_truth_install_above_base_level_is_rejected` reported "test did not
    panic as expected", and the other two panicked in `Euf::assert` (truth
    terms unset).
- Final-review fix (`4f8f072`):
  - `compound_definition_constrains_its_leaves`: RED.
  - `qfdt_e2e slice50_dt_injective_compound_leaf_unsat` and
    `slice50_dt_selector_compound_leaf_unsat`: RED, `["sat"]` vs
    `["unsat"]`.
- Green today (at `4f8f072`, run for this report):
  - `cargo nextest run -p shinri-solver -E 'binary(uflia_e2e) or
    binary(uflra_e2e) or binary(qfdt_e2e)'`: **56 run, 56 passed**.
  - `cargo nextest run -p shinri-arith -p shinri-euf`: **112 run, 112
    passed**.
  - §1.2 repro via the CLI: pre-slice `sat`, branch `unsat`.
- Latest whole-branch gates, recorded in the ledger:
  - `mise run test`: 1548/1548.
  - `script_e2e`: 73/73.
  - fmt and `clippy --workspace --all-targets -D warnings`: clean.

**Task 4 (oracle coverage).** The pre-fix disagreement dump (arith files from
`d70d381`) was:

```
DISAGREEMENT (QF_UFLIA compound args) iter 1: shinri=Sat z3=Unsat
(= (f (* 2 c1)) 0)
(= (f 2) 1)
(= c0 1)
(= c1 1)
```

Post-fix: PASS in 3.7 s, `compound-args oracle: sat 153, unsat 47`.

**Unfiltered oracle suite** (`cargo nextest run -p shinri-solver --features
oracle`), after the final fix: **669 passed, 3 skipped**. The discovered count
is non-zero.

## Un-banked §9 class join: tried, not adopted

Criterion 6 un-banked spec §9's unit-difference class join, and it was built
as Task 8. It recovered 0 of the 29 `correct → non-correct` rows. A narrower
variant (a per-class "definitionally joined" flag) recovered 1 of 29, which is
`SEQ038_size9` in QF_UF and is timing noise. The 11 formerly-wrong QF_UFLIA
rows all still time out, and none answers `sat`. All 16 QF_SLIA `unknown` rows
and both Wisa `sat → timeout` rows are unchanged under every build tried.

- **Why it does not help.** The join fires (instrumentation shows, for
  example, all 63 definitional rows of one `findAnagrams` row are unit
  differences). But a leaf like `a` is almost always already constrained by
  its own atoms, so joining the compound into its class is equivalent to
  marking it. The cost is the probing the fix needs, not the marking
  mechanism. The Task 6 diagnostic (skipping `mark_constrained(v_t)` restores
  the rows) holds only because skipping is unsound: it leaves `v_t` a free
  singleton, which the join by design does not.
- **§9's "only a performance refinement" is incomplete.** A definitional join
  breaks slice 42's C2 argument. With `a` free, `(+ a 0)` and `a`, or
  `(+ a 1)` and `(- (+ a 2) 1)`, share a class and are always equal, and EUF
  does not know it. So the join needs same-class pairs to be probed. That
  patch conflicts with two slice-42 tests,
  `free_class_pair_joined_by_interface_equality_is_not_probed` and
  `mbtc_skips_a_free_class_pair`. The join was not committed.
- **Decision (user, 2026-09-29): accept the criterion-5 miss and merge.** The
  slice removes 11 wrong answers and has 0 `correct → wrong`, at the cost of
  about 20 `correct` rows becoming `unknown` or `timeout` (QF_SLIA −14,
  QF_UFLIA −3, QF_UF −3 after exclusions). This is recorded as a decided
  exception to criterion 5, not a relaxation of it.

## Queued for the next slice

- **The unit-difference class join is closed as not effective. Do not
  re-queue it** (see "Un-banked §9 class join: tried, not adopted").
- **QF_SLIA `STRING_PATH_PIVOT_BUDGET`.** The 16 lost QF_SLIA rows exhaust the
  budget (2,000). Pre-slice already peaked at 1,938 on those rows, so they sit
  near a fixed-budget cliff. An option is to re-examine whether the budget
  should count probe pivots at all.
- **Wisa final-check blow-up.** The 2 Wisa `correct → timeout` rows make more
  than 1.18 M `define_shared_compound` calls in 90 s. The work is to reduce
  entailment/MBTC probing cost over compound shared terms.
- **Wisa rows that moved** (`wrong → timeout`, 11): the four that reach
  `unsat` in 27–35 s (`xs-05-08-4-2-5-4`, `xs-05-12-1-4-2-1`,
  `xs-05-16-1-5-4-3`, `xs-05-20-5-1-4-2`) and the seven with no answer at 120
  s (`xs-06-15-4-1-4-1`, `xs-06-19-3-3-4-4`, `xs-07-10-2-4-5-3`,
  `xs-07-14-1-1-1-1`, `xs-07-18-1-1-4-1`, `wisas/xs_6_11`, `wisas/xs_8_13`).
  Also `xs-06-07-4-5-4-2` and `xs-07-06-4-1-5-3` (`correct → timeout`, traced
  above). **Wisa rows that did not move:** the other 318 Wisa/wisas rows are
  `timeout` on both runs (appendix).
- **Approach B's gate (§9) stays banked:** criterion 4 leaves no row `wrong`.
- **QF_SLIA wrong rows:** none moved (37 → 37, the same `20230329-denghang`
  35 and Noetzli 2 paths and answers). Spec §1.4 named them only as a
  candidate beneficiary. This run shows no effect on them.
- Carried from spec §10, unchanged: `get-value` echoes purification names;
  the `Owner::Shared` definitional merge; `pending` is not backtracked; the
  blocksworld re-index churn measurement; the QF_S wrong rows
  (`instance09174`, `instance10773`, unchanged here); the `blast_word` panic
  bucket.
- Parked from the final review (ledger): the pin-tighten conflict is only
  `debug_assert`ed; the per-new-compound `recompute_basic_values` cost. This
  run gives no separate signal on either.
- Harness nit: the bench fixture header records the checkout's HEAD, not the
  `--solver` binary's commit (`d70d381548c1-dirty` for a `1fe3658` binary).
  `solver_md5` is the reliable identifier.

## References

- Spec: `docs/superpowers/specs/2026-09-29-shinri-slice50-uflia-shared-compound-args-design.md`
  (§7 criteria, §9 banked alternatives, §12 measured outcomes).
- Slice 49 report: `docs/superpowers/research/2026-09-11-smtlib-2024-slice49-euf-report.md`.
- Runs (git-ignored): `bench/results/slice50/`, `bench/results/slice50-base/`.

## Appendix: every Wisa row, base and branch verdicts

331 rows: `mathsat/Wisa` 223, `wisas` 108. 13 changed (also listed under criteria 4 and 6 above). The other 318 are `timeout` on both runs. Wall times are the corpus runs' `wall_ms`.

| path | base | branch |
| --- | --- | --- |
| `mathsat/Wisa/xs-05-06-2-2-5-1.smt2` | timeout (20013 ms) | timeout (20013 ms) |
| `mathsat/Wisa/xs-05-07-4-5-1-2.smt2` | timeout (20008 ms) | timeout (20014 ms) |
| `mathsat/Wisa/xs-05-08-4-2-5-4.smt2` | wrong (4270 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-05-09-5-1-2-5.smt2` | timeout (20010 ms) | timeout (20020 ms) |
| `mathsat/Wisa/xs-05-11-2-5-3-2.smt2` | timeout (20010 ms) | timeout (20016 ms) |
| `mathsat/Wisa/xs-05-12-1-4-2-1.smt2` | wrong (3380 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-05-13-2-4-5-3.smt2` | timeout (20007 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-05-14-4-3-1-1.smt2` | timeout (20009 ms) | timeout (20014 ms) |
| `mathsat/Wisa/xs-05-16-1-5-4-3.smt2` | wrong (3494 ms) | timeout (20003 ms) |
| `mathsat/Wisa/xs-05-17-1-5-1-5.smt2` | timeout (20008 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-05-18-1-3-1-3.smt2` | timeout (20007 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-05-19-1-4-2-1.smt2` | timeout (20013 ms) | timeout (20017 ms) |
| `mathsat/Wisa/xs-05-20-5-1-4-2.smt2` | wrong (4414 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-06-05-5-2-5-5.smt2` | timeout (20007 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-06-07-4-5-4-2.smt2` | correct (11718 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-06-08-5-1-5-3.smt2` | timeout (20011 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-06-09-3-5-5-3.smt2` | timeout (20006 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-06-10-1-4-2-5.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-06-12-5-4-2-5.smt2` | timeout (20008 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-06-13-5-3-5-5.smt2` | timeout (20008 ms) | timeout (20012 ms) |
| `mathsat/Wisa/xs-06-14-3-1-5-2.smt2` | timeout (20006 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-06-15-4-1-4-1.smt2` | wrong (13458 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-06-17-2-2-4-1.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-06-18-1-2-1-5.smt2` | timeout (20007 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-06-19-3-3-4-4.smt2` | wrong (7091 ms) | timeout (20012 ms) |
| `mathsat/Wisa/xs-06-20-5-1-5-1.smt2` | timeout (20014 ms) | timeout (20010 ms) |
| `mathsat/Wisa/xs-07-05-5-2-3-5.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-07-06-4-1-5-3.smt2` | correct (12884 ms) | timeout (20013 ms) |
| `mathsat/Wisa/xs-07-08-4-4-4-2.smt2` | timeout (20007 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-07-09-3-4-4-3.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-07-10-2-4-5-3.smt2` | wrong (14179 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-07-11-1-1-1-1.smt2` | timeout (20011 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-07-13-5-3-2-1.smt2` | timeout (20009 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-07-14-1-1-1-1.smt2` | wrong (14322 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-07-15-4-4-1-5.smt2` | timeout (20009 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-07-16-2-4-3-5.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-07-18-1-1-4-1.smt2` | wrong (12379 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-07-19-5-3-2-5.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-07-20-2-5-1-4.smt2` | timeout (20009 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-08-05-1-5-4-2.smt2` | timeout (20007 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-08-06-4-5-4-1.smt2` | timeout (20010 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-08-07-3-2-3-1.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-08-09-4-5-5-4.smt2` | timeout (20003 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-08-10-5-2-5-3.smt2` | timeout (20006 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-08-11-4-3-2-2.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-08-12-3-1-3-4.smt2` | timeout (20008 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-08-14-2-3-3-5.smt2` | timeout (20007 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-08-15-4-2-1-4.smt2` | timeout (20007 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-08-16-4-4-5-1.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-08-17-4-1-2-2.smt2` | timeout (20003 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-08-19-2-2-3-1.smt2` | timeout (20007 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-08-20-3-2-4-5.smt2` | timeout (20008 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-09-05-2-4-4-5.smt2` | timeout (20007 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-09-06-1-5-3-2.smt2` | timeout (20007 ms) | timeout (20010 ms) |
| `mathsat/Wisa/xs-09-07-1-3-3-2.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-09-08-1-1-5-3.smt2` | timeout (20004 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-09-10-5-1-5-2.smt2` | timeout (20006 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-09-11-2-4-1-5.smt2` | timeout (20009 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-09-12-5-2-1-5.smt2` | timeout (20003 ms) | timeout (20003 ms) |
| `mathsat/Wisa/xs-09-13-2-3-1-3.smt2` | timeout (20007 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-09-15-5-3-2-3.smt2` | timeout (20008 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-09-16-3-4-1-5.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-09-17-2-1-4-1.smt2` | timeout (20006 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-09-18-1-3-4-5.smt2` | timeout (20010 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-09-20-5-5-1-5.smt2` | timeout (20003 ms) | timeout (20003 ms) |
| `mathsat/Wisa/xs-10-05-5-2-1-5.smt2` | timeout (20007 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-10-06-1-1-5-2.smt2` | timeout (20006 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-10-07-4-1-1-5.smt2` | timeout (20006 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-10-08-2-2-4-5.smt2` | timeout (20006 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-10-09-1-4-4-1.smt2` | timeout (20014 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-10-11-1-3-5-5.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-10-12-4-1-1-4.smt2` | timeout (20007 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-10-13-5-5-4-5.smt2` | timeout (20006 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-10-14-2-1-4-4.smt2` | timeout (20006 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-10-16-3-5-2-4.smt2` | timeout (20006 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-10-17-5-2-2-5.smt2` | timeout (20011 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-10-18-2-2-5-3.smt2` | timeout (20007 ms) | timeout (20015 ms) |
| `mathsat/Wisa/xs-10-19-3-4-2-4.smt2` | timeout (20006 ms) | timeout (20012 ms) |
| `mathsat/Wisa/xs-11-05-3-1-5-3.smt2` | timeout (20006 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-11-06-4-4-5-5.smt2` | timeout (20004 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-11-07-3-4-2-3.smt2` | timeout (20006 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-11-08-3-4-3-5.smt2` | timeout (20015 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-11-09-1-2-1-3.smt2` | timeout (20009 ms) | timeout (20012 ms) |
| `mathsat/Wisa/xs-11-10-2-5-3-2.smt2` | timeout (20004 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-11-12-5-4-4-2.smt2` | timeout (20006 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-11-13-4-4-5-2.smt2` | timeout (20008 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-11-14-5-3-1-2.smt2` | timeout (20003 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-11-15-4-4-5-5.smt2` | timeout (20012 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-11-17-5-2-4-4.smt2` | timeout (20009 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-11-18-3-3-4-1.smt2` | timeout (20004 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-11-19-4-5-1-1.smt2` | timeout (20008 ms) | timeout (20010 ms) |
| `mathsat/Wisa/xs-11-20-5-2-5-3.smt2` | timeout (20008 ms) | timeout (20012 ms) |
| `mathsat/Wisa/xs-12-05-3-3-5-4.smt2` | timeout (20003 ms) | timeout (20010 ms) |
| `mathsat/Wisa/xs-12-06-3-4-5-1.smt2` | timeout (20007 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-12-07-3-4-1-2.smt2` | timeout (20006 ms) | timeout (20010 ms) |
| `mathsat/Wisa/xs-12-08-5-2-5-3.smt2` | timeout (20007 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-12-09-5-5-2-4.smt2` | timeout (20004 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-12-10-4-4-3-1.smt2` | timeout (20006 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-12-11-1-4-4-3.smt2` | timeout (20006 ms) | timeout (20014 ms) |
| `mathsat/Wisa/xs-12-13-3-4-2-3.smt2` | timeout (20004 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-12-14-3-5-4-4.smt2` | timeout (20008 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-12-15-3-2-1-5.smt2` | timeout (20008 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-12-16-5-2-2-3.smt2` | timeout (20006 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-12-18-1-3-1-2.smt2` | timeout (20006 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-12-19-1-4-1-2.smt2` | timeout (20009 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-12-20-1-1-5-2.smt2` | timeout (20008 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-13-05-5-4-1-5.smt2` | timeout (20010 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-13-06-1-1-2-4.smt2` | timeout (20006 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-13-07-1-5-2-3.smt2` | timeout (20008 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-13-08-3-2-1-3.smt2` | timeout (20003 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-13-09-3-2-3-2.smt2` | timeout (20005 ms) | timeout (20013 ms) |
| `mathsat/Wisa/xs-13-10-4-3-1-3.smt2` | timeout (20012 ms) | timeout (20010 ms) |
| `mathsat/Wisa/xs-13-11-5-3-5-3.smt2` | timeout (20007 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-13-12-5-3-4-4.smt2` | timeout (20003 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-13-14-4-5-4-2.smt2` | timeout (20006 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-13-15-5-3-4-1.smt2` | timeout (20006 ms) | timeout (20010 ms) |
| `mathsat/Wisa/xs-13-16-3-1-4-1.smt2` | timeout (20003 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-13-17-4-2-1-5.smt2` | timeout (20014 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-13-19-4-5-5-5.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-13-20-2-2-4-4.smt2` | timeout (20003 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-14-05-1-4-4-5.smt2` | timeout (20006 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-14-06-4-4-1-2.smt2` | timeout (20006 ms) | timeout (20013 ms) |
| `mathsat/Wisa/xs-14-07-1-4-1-3.smt2` | timeout (20003 ms) | timeout (20010 ms) |
| `mathsat/Wisa/xs-14-08-5-1-1-4.smt2` | timeout (20011 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-14-09-3-3-4-4.smt2` | timeout (20007 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-14-10-3-4-2-2.smt2` | timeout (20005 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-14-11-4-2-2-1.smt2` | timeout (20003 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-14-12-4-4-1-3.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-14-13-4-2-1-3.smt2` | timeout (20006 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-14-15-1-1-3-3.smt2` | timeout (20006 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-14-16-4-1-1-5.smt2` | timeout (20006 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-14-17-5-4-3-1.smt2` | timeout (20005 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-14-18-5-5-3-2.smt2` | timeout (20005 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-14-20-3-5-3-5.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-15-05-2-1-2-3.smt2` | timeout (20005 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-15-06-3-5-4-4.smt2` | timeout (20007 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-15-07-3-1-5-5.smt2` | timeout (20009 ms) | timeout (20013 ms) |
| `mathsat/Wisa/xs-15-08-4-5-4-1.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-15-09-3-5-5-3.smt2` | timeout (20005 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-15-10-1-3-5-1.smt2` | timeout (20004 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-15-11-5-2-2-2.smt2` | timeout (20005 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-15-12-2-2-3-4.smt2` | timeout (20009 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-15-13-4-5-2-4.smt2` | timeout (20009 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-15-14-5-5-5-1.smt2` | timeout (20007 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-15-16-2-4-2-5.smt2` | timeout (20005 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-15-17-2-1-1-4.smt2` | timeout (20005 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-15-18-4-1-3-5.smt2` | timeout (20003 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-15-19-3-1-4-1.smt2` | timeout (20012 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-16-05-5-3-1-1.smt2` | timeout (20005 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-16-06-4-1-3-5.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-16-07-1-1-4-2.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-16-08-1-4-4-5.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-16-09-4-2-1-5.smt2` | timeout (20006 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-16-10-4-3-1-3.smt2` | timeout (20010 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-16-11-2-1-5-2.smt2` | timeout (20007 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-16-12-2-5-3-4.smt2` | timeout (20005 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-16-13-4-1-4-5.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-16-14-2-4-1-4.smt2` | timeout (20005 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-16-15-2-3-4-4.smt2` | timeout (20005 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-16-17-5-5-3-5.smt2` | timeout (20008 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-16-18-1-4-4-3.smt2` | timeout (20010 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-16-19-3-4-4-1.smt2` | timeout (20005 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-16-20-5-1-4-4.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-17-05-2-1-1-2.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-17-06-5-5-4-1.smt2` | timeout (20005 ms) | timeout (20019 ms) |
| `mathsat/Wisa/xs-17-07-3-4-4-3.smt2` | timeout (20008 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-17-08-5-3-2-5.smt2` | timeout (20007 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-17-09-4-3-5-5.smt2` | timeout (20005 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-17-10-5-3-2-1.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-17-11-3-3-4-5.smt2` | timeout (20004 ms) | timeout (20004 ms) |
| `mathsat/Wisa/xs-17-12-3-4-4-1.smt2` | timeout (20006 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-17-13-4-4-2-1.smt2` | timeout (20008 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-17-14-2-4-3-1.smt2` | timeout (20009 ms) | timeout (20014 ms) |
| `mathsat/Wisa/xs-17-15-2-2-2-4.smt2` | timeout (20004 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-17-16-4-4-1-4.smt2` | timeout (20004 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-17-18-4-2-3-1.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-17-19-3-3-3-4.smt2` | timeout (20005 ms) | timeout (20010 ms) |
| `mathsat/Wisa/xs-17-20-5-1-5-4.smt2` | timeout (20007 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-18-05-5-4-4-2.smt2` | timeout (20010 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-18-06-4-2-1-1.smt2` | timeout (20005 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-18-07-1-2-1-1.smt2` | timeout (20003 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-18-08-4-5-2-5.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-18-09-1-5-4-4.smt2` | timeout (20005 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-18-10-4-5-2-3.smt2` | timeout (20006 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-18-11-5-3-1-1.smt2` | timeout (20004 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-18-12-3-4-4-3.smt2` | timeout (20007 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-18-13-5-4-1-2.smt2` | timeout (20005 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-18-14-3-5-2-3.smt2` | timeout (20004 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-18-15-4-1-3-1.smt2` | timeout (20004 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-18-16-2-2-1-4.smt2` | timeout (20009 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-18-17-4-5-2-4.smt2` | timeout (20011 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-18-19-4-1-1-5.smt2` | timeout (20003 ms) | timeout (20015 ms) |
| `mathsat/Wisa/xs-18-20-1-4-2-1.smt2` | timeout (20005 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-19-05-2-5-4-2.smt2` | timeout (20004 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-19-06-4-3-2-1.smt2` | timeout (20003 ms) | timeout (20016 ms) |
| `mathsat/Wisa/xs-19-07-4-2-4-4.smt2` | timeout (20006 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-19-08-4-1-1-1.smt2` | timeout (20008 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-19-09-4-2-3-5.smt2` | timeout (20005 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-19-10-3-5-2-5.smt2` | timeout (20003 ms) | timeout (20007 ms) |
| `mathsat/Wisa/xs-19-11-4-4-1-3.smt2` | timeout (20005 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-19-12-4-2-4-5.smt2` | timeout (20005 ms) | timeout (20015 ms) |
| `mathsat/Wisa/xs-19-13-2-1-3-1.smt2` | timeout (20009 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-19-14-3-3-5-3.smt2` | timeout (20004 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-19-15-3-1-3-4.smt2` | timeout (20004 ms) | timeout (20028 ms) |
| `mathsat/Wisa/xs-19-16-4-4-1-4.smt2` | timeout (20004 ms) | timeout (20018 ms) |
| `mathsat/Wisa/xs-19-17-2-2-5-1.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-19-18-2-2-2-5.smt2` | timeout (20005 ms) | timeout (20014 ms) |
| `mathsat/Wisa/xs-19-20-1-1-2-2.smt2` | timeout (20005 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-20-05-5-5-1-3.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-20-06-2-3-1-3.smt2` | timeout (20004 ms) | timeout (20014 ms) |
| `mathsat/Wisa/xs-20-07-5-1-2-1.smt2` | timeout (20004 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-20-08-5-3-1-5.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-20-09-1-5-4-2.smt2` | timeout (20004 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-20-10-5-5-5-4.smt2` | timeout (20006 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-20-11-5-1-3-4.smt2` | timeout (20006 ms) | timeout (20011 ms) |
| `mathsat/Wisa/xs-20-12-3-1-5-2.smt2` | timeout (20004 ms) | timeout (20005 ms) |
| `mathsat/Wisa/xs-20-13-2-5-2-3.smt2` | timeout (20003 ms) | timeout (20012 ms) |
| `mathsat/Wisa/xs-20-14-2-3-3-3.smt2` | timeout (20004 ms) | timeout (20009 ms) |
| `mathsat/Wisa/xs-20-15-2-2-4-2.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-20-16-4-4-4-1.smt2` | timeout (20004 ms) | timeout (20006 ms) |
| `mathsat/Wisa/xs-20-17-5-4-5-4.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `mathsat/Wisa/xs-20-18-3-4-5-4.smt2` | timeout (20005 ms) | timeout (20012 ms) |
| `mathsat/Wisa/xs-20-19-2-2-2-5.smt2` | timeout (20004 ms) | timeout (20007 ms) |
| `wisas/xs_10_10.smt2` | timeout (20007 ms) | timeout (20013 ms) |
| `wisas/xs_10_15.smt2` | timeout (20003 ms) | timeout (20012 ms) |
| `wisas/xs_10_20.smt2` | timeout (20009 ms) | timeout (20006 ms) |
| `wisas/xs_11_11.smt2` | timeout (20009 ms) | timeout (20008 ms) |
| `wisas/xs_11_16.smt2` | timeout (20007 ms) | timeout (20006 ms) |
| `wisas/xs_11_21.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `wisas/xs_12_12.smt2` | timeout (20007 ms) | timeout (20007 ms) |
| `wisas/xs_12_17.smt2` | timeout (20006 ms) | timeout (20008 ms) |
| `wisas/xs_12_22.smt2` | timeout (20009 ms) | timeout (20007 ms) |
| `wisas/xs_13_13.smt2` | timeout (20009 ms) | timeout (20007 ms) |
| `wisas/xs_13_18.smt2` | timeout (20008 ms) | timeout (20007 ms) |
| `wisas/xs_13_23.smt2` | timeout (20006 ms) | timeout (20006 ms) |
| `wisas/xs_14_14.smt2` | timeout (20006 ms) | timeout (20006 ms) |
| `wisas/xs_14_19.smt2` | timeout (20014 ms) | timeout (20004 ms) |
| `wisas/xs_14_24.smt2` | timeout (20011 ms) | timeout (20006 ms) |
| `wisas/xs_15_15.smt2` | timeout (20010 ms) | timeout (20011 ms) |
| `wisas/xs_15_20.smt2` | timeout (20008 ms) | timeout (20006 ms) |
| `wisas/xs_15_25.smt2` | timeout (20006 ms) | timeout (20005 ms) |
| `wisas/xs_16_16.smt2` | timeout (20006 ms) | timeout (20006 ms) |
| `wisas/xs_16_26.smt2` | timeout (20007 ms) | timeout (20010 ms) |
| `wisas/xs_16_36.smt2` | timeout (20017 ms) | timeout (20005 ms) |
| `wisas/xs_17_17.smt2` | timeout (20008 ms) | timeout (20005 ms) |
| `wisas/xs_17_27.smt2` | timeout (20007 ms) | timeout (20013 ms) |
| `wisas/xs_17_37.smt2` | timeout (20006 ms) | timeout (20005 ms) |
| `wisas/xs_18_18.smt2` | timeout (20008 ms) | timeout (20006 ms) |
| `wisas/xs_18_28.smt2` | timeout (20008 ms) | timeout (20008 ms) |
| `wisas/xs_18_38.smt2` | timeout (20008 ms) | timeout (20005 ms) |
| `wisas/xs_19_19.smt2` | timeout (20009 ms) | timeout (20005 ms) |
| `wisas/xs_19_29.smt2` | timeout (20006 ms) | timeout (20008 ms) |
| `wisas/xs_19_39.smt2` | timeout (20005 ms) | timeout (20006 ms) |
| `wisas/xs_20_20.smt2` | timeout (20006 ms) | timeout (20005 ms) |
| `wisas/xs_20_30.smt2` | timeout (20008 ms) | timeout (20006 ms) |
| `wisas/xs_20_40.smt2` | timeout (20008 ms) | timeout (20005 ms) |
| `wisas/xs_21_21.smt2` | timeout (20007 ms) | timeout (20005 ms) |
| `wisas/xs_21_31.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `wisas/xs_21_41.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `wisas/xs_22_22.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `wisas/xs_22_32.smt2` | timeout (20010 ms) | timeout (20016 ms) |
| `wisas/xs_22_42.smt2` | timeout (20006 ms) | timeout (20004 ms) |
| `wisas/xs_23_23.smt2` | timeout (20006 ms) | timeout (20004 ms) |
| `wisas/xs_23_33.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `wisas/xs_23_43.smt2` | timeout (20005 ms) | timeout (20004 ms) |
| `wisas/xs_24_24.smt2` | timeout (20005 ms) | timeout (20004 ms) |
| `wisas/xs_24_34.smt2` | timeout (20008 ms) | timeout (20008 ms) |
| `wisas/xs_24_44.smt2` | timeout (20006 ms) | timeout (20005 ms) |
| `wisas/xs_25_25.smt2` | timeout (20006 ms) | timeout (20004 ms) |
| `wisas/xs_25_35.smt2` | timeout (20004 ms) | timeout (20007 ms) |
| `wisas/xs_25_45.smt2` | timeout (20005 ms) | timeout (20004 ms) |
| `wisas/xs_26_26.smt2` | timeout (20004 ms) | timeout (20004 ms) |
| `wisas/xs_26_36.smt2` | timeout (20005 ms) | timeout (20012 ms) |
| `wisas/xs_26_46.smt2` | timeout (20007 ms) | timeout (20006 ms) |
| `wisas/xs_27_27.smt2` | timeout (20007 ms) | timeout (20005 ms) |
| `wisas/xs_27_37.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `wisas/xs_27_47.smt2` | timeout (20004 ms) | timeout (20005 ms) |
| `wisas/xs_28_28.smt2` | timeout (20004 ms) | timeout (20005 ms) |
| `wisas/xs_28_38.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `wisas/xs_28_48.smt2` | timeout (20005 ms) | timeout (20004 ms) |
| `wisas/xs_29_29.smt2` | timeout (20006 ms) | timeout (20010 ms) |
| `wisas/xs_29_39.smt2` | timeout (20004 ms) | timeout (20006 ms) |
| `wisas/xs_29_49.smt2` | timeout (20007 ms) | timeout (20008 ms) |
| `wisas/xs_30_30.smt2` | timeout (20004 ms) | timeout (20008 ms) |
| `wisas/xs_30_40.smt2` | timeout (20006 ms) | timeout (20014 ms) |
| `wisas/xs_30_50.smt2` | timeout (20009 ms) | timeout (20010 ms) |
| `wisas/xs_31_31.smt2` | timeout (20014 ms) | timeout (20007 ms) |
| `wisas/xs_31_41.smt2` | timeout (20004 ms) | timeout (20006 ms) |
| `wisas/xs_31_51.smt2` | timeout (20004 ms) | timeout (20004 ms) |
| `wisas/xs_32_32.smt2` | timeout (20004 ms) | timeout (20007 ms) |
| `wisas/xs_32_42.smt2` | timeout (20009 ms) | timeout (20008 ms) |
| `wisas/xs_32_52.smt2` | timeout (20005 ms) | timeout (20004 ms) |
| `wisas/xs_33_33.smt2` | timeout (20006 ms) | timeout (20021 ms) |
| `wisas/xs_33_43.smt2` | timeout (20004 ms) | timeout (20005 ms) |
| `wisas/xs_33_53.smt2` | timeout (20004 ms) | timeout (20004 ms) |
| `wisas/xs_34_34.smt2` | timeout (20004 ms) | timeout (20006 ms) |
| `wisas/xs_34_44.smt2` | timeout (20010 ms) | timeout (20010 ms) |
| `wisas/xs_34_54.smt2` | timeout (20004 ms) | timeout (20003 ms) |
| `wisas/xs_35_35.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `wisas/xs_35_45.smt2` | timeout (20004 ms) | timeout (20009 ms) |
| `wisas/xs_35_55.smt2` | timeout (20004 ms) | timeout (20004 ms) |
| `wisas/xs_36_36.smt2` | timeout (20004 ms) | timeout (20004 ms) |
| `wisas/xs_36_46.smt2` | timeout (20017 ms) | timeout (20007 ms) |
| `wisas/xs_36_56.smt2` | timeout (20011 ms) | timeout (20004 ms) |
| `wisas/xs_37_37.smt2` | timeout (20004 ms) | timeout (20006 ms) |
| `wisas/xs_37_47.smt2` | timeout (20006 ms) | timeout (20004 ms) |
| `wisas/xs_37_57.smt2` | timeout (20005 ms) | timeout (20004 ms) |
| `wisas/xs_38_38.smt2` | timeout (20004 ms) | timeout (20004 ms) |
| `wisas/xs_38_48.smt2` | timeout (20006 ms) | timeout (20012 ms) |
| `wisas/xs_38_58.smt2` | timeout (20007 ms) | timeout (20004 ms) |
| `wisas/xs_39_39.smt2` | timeout (20005 ms) | timeout (20005 ms) |
| `wisas/xs_39_49.smt2` | timeout (20007 ms) | timeout (20005 ms) |
| `wisas/xs_39_59.smt2` | timeout (20004 ms) | timeout (20005 ms) |
| `wisas/xs_40_40.smt2` | timeout (20004 ms) | timeout (20006 ms) |
| `wisas/xs_40_50.smt2` | timeout (20004 ms) | timeout (20012 ms) |
| `wisas/xs_40_60.smt2` | timeout (20007 ms) | timeout (20005 ms) |
| `wisas/xs_5_10.smt2` | timeout (20010 ms) | timeout (20010 ms) |
| `wisas/xs_5_15.smt2` | timeout (20008 ms) | timeout (20023 ms) |
| `wisas/xs_5_5.smt2` | timeout (20008 ms) | timeout (20011 ms) |
| `wisas/xs_6_11.smt2` | wrong (4935 ms) | timeout (20007 ms) |
| `wisas/xs_6_16.smt2` | timeout (20019 ms) | timeout (20021 ms) |
| `wisas/xs_6_6.smt2` | timeout (20013 ms) | timeout (20011 ms) |
| `wisas/xs_7_12.smt2` | timeout (20008 ms) | timeout (20009 ms) |
| `wisas/xs_7_17.smt2` | timeout (20010 ms) | timeout (20008 ms) |
| `wisas/xs_7_7.smt2` | timeout (20008 ms) | timeout (20011 ms) |
| `wisas/xs_8_13.smt2` | wrong (11135 ms) | timeout (20006 ms) |
| `wisas/xs_8_18.smt2` | timeout (20008 ms) | timeout (20016 ms) |
| `wisas/xs_8_8.smt2` | timeout (20011 ms) | timeout (20011 ms) |
| `wisas/xs_9_14.smt2` | timeout (20015 ms) | timeout (20014 ms) |
| `wisas/xs_9_19.smt2` | timeout (20007 ms) | timeout (20006 ms) |
| `wisas/xs_9_9.smt2` | timeout (20008 ms) | timeout (20009 ms) |
