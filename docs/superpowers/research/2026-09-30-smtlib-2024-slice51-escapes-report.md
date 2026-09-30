# SMT-LIB 2024 re-run — slice 51 (decode SMT-LIB 2.6 `\u` escapes in string literals) — shinri @ 924ecc98cd06

Run-id `slice51` (branch), compared against `slice50` (fixture sha
`4f8f0729b4dd`), restricted to QF_S and QF_SLIA:

```
BENCH_LOGICS=QF_S,QF_SLIA BENCH_RUN_ID=slice51 taskset -c 12-23 mise run bench-run
BENCH_RUN_ID=slice51 mise run bench-report
md5sum target/release/shinri   # 4347bd57aa6542e0b8567be63c5c0a9b = fixture solver_md5
```

Both runs used the baseline limits: 20 s, 3072 MB, 6 jobs, cgroup `cpu.max`
`800000 100000`, `memory.max` 34359738368, pinned with `taskset -c 12-23`.
Each covers the same 103,335 QF_S + QF_SLIA instances.

| run | solver | `solver_md5` | started | log last written | wall-clock |
| --- | --- | --- | --- | --- | --- |
| `slice51` | `target/release/shinri` @ `924ecc9` (Task 4 head) | `4347bd57aa6542e0b8567be63c5c0a9b` | 2026-09-30T10:31:04Z | 12:05:11Z | ~1 h 34 min |
| `slice50` (comparison) | `target/release/shinri` @ `4f8f072` | `b99562b3db7ca436367a9fd7d96c3bc8` | 2026-09-29T18:44:09Z | 21:56:53Z | (six logics, ~3 h 13 min) |

**Baseline validity.** `git diff --stat 4f8f072 4c7ade5 -- crates/` prints
nothing: `main` at `4c7ade5` has the same solver source as `4f8f072`, so
`slice50` is the pre-slice baseline and no separate base run was made.

**Fixture sha.** The run was built at `924ecc9` (Task 4). The only later
branch commit, `3e08039` (Task 5), touches
`crates/shinri-solver/tests/qfs_differential.rs` (test) and a doc comment in
`crates/shinri-str/src/code_conv.rs`. The solver binary is the same.
`solver_md5` matches `target/release/shinri` on disk.

**Load disclosure.** The Task 5/6 cargo builds, test suites and oracle
suite ran concurrently on the same machine (bench pinned to CPUs 12–23).
Rows near the 20 s boundary and the z3 oracle's own time budget may carry
load noise. It shows up in exactly one place: 62 `correct → unverified` rows
with an unchanged shinri answer and a z3 oracle `timeout` (below). No
`correct → *` row in this run is near 20 s: the slowest branch wall time in
the criterion 5 table is 186 ms.

**How the transitions were computed.** A scratch `transitions.py` (not
committed) loads each `results.jsonl` keyed by `path`, restricted to QF_S
and QF_SLIA, asserts identical key sets (**103,335 common paths, 0 missing,
0 extra**), and tallies `(logic, before, after)` with per-family counts. It
prints an `ESCALATE` line for any row that moves into `wrong`. **It printed
none.** Every per-logic count below closes under
`new = old − outbound + inbound`.

Final log lines:

```
slice51  103335/103335  correct=40873 wrong=2 status-suspect=0 parse-error=195 panic=0 oom=0 timeout=49 unknown=60807 unverified=1409 malformed=0
```

## Headline

- **`wrong` fell 39 → 2** across QF_S + QF_SLIA. The two left are the
  Noetzli pair (`str-pred-small-rw_370`, `_458`), which have no escapes and
  are unchanged.
- **Both QF_S wrong rows are fixed:** `instance10773` → `sat`,
  `instance09174` → `unsat`.
- **denghang: 31 of 35 wrong rows → `unsat` (correct), 4 → `unknown:str-model-rejected`,
  0 wrong.** This matches spec §1.3's pre-decoder prediction (31 `unsat`, 4
  `unknown`) in count.
- **0 rows moved into `wrong`** from any verdict. There is no `ESCALATE`.
- **`correct` rose:** QF_S 16,025 → 16,058 (+33), QF_SLIA 24,798 → 24,815
  (+17).
- **76 rows went `correct → unknown`** (74 QF_S automatark-lu, 2 QF_SLIA
  denghang), 0 went to `timeout`. Every one contains `\u` escapes, so the
  file's formula changed under it. These are not gated (spec §7 criterion
  5); they are listed and triaged below. 68 of them are the
  `str-model-rejected` soundness fence: on the decoded formula the string
  theory proposes a model that the post-solve self-check rejects.
- **parse-error 195 → 195, the same paths and the same message.** None is
  the new surrogate diagnostic.
- Every verdict-changed row contains a `\u` escape, except the 55
  stringfuzz `correct → unverified` oracle-timeout rows.

## Success criteria (spec §7)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | `instance10773` → `sat`, `instance09174` → `unsat` | **PASS** | `instance10773`: wrong `unsat` 155 ms → correct `sat` 23 ms. `instance09174`: wrong `sat` 8 ms → correct `unsat` 20 ms |
| 2 | no denghang row `wrong`; the 31 of §1.3 answer `unsat` | **PASS** | 35 rows: `wrong → correct (unsat)` 31, `wrong → unknown:str-model-rejected` 4 (listed below), `wrong` 0 |
| 3 | QF_S + QF_SLIA `wrong` ≤ 2, only the Noetzli pair | **PASS** | 39 → 2: `20190311-str-small-rw-Noetzli/str-pred-small-rw/str-pred-small-rw_370.smt2` and `_458.smt2`, both `sat` against `:status unsat`, unchanged |
| 4 | 0 `* → wrong`, or each escalated | **PASS: 0** | no changed cell ends in `wrong`; `transitions.py` printed no `ESCALATE` line |
| 5 | every `correct → unknown/timeout` row listed and triaged | **DONE (not gated)** | 76 rows, all `unknown`, 0 `timeout`; table and triage below |
| 6 | standard gates green | **PASS** | Task 6 counts, *Gates* below |

### Criterion 2: the 4 denghang rows that do not answer `unsat`

All 4 were `wrong` (`sat`) on `slice50` and are
`unknown:str-model-rejected` now: the decoded formula makes the string
theory propose a model the self-check rejects, so the solver says `unknown`
instead of a wrong `sat`.

| row | base | branch |
| --- | --- | --- |
| `QF_SLIA/20230329-denghang/instance46836.smt2` | wrong `sat` 50 ms | `unknown:str-model-rejected` 14 ms |
| `QF_SLIA/20230329-denghang/instance51681.smt2` | wrong `sat` 15 ms | `unknown:str-model-rejected` 5 ms |
| `QF_SLIA/20230329-denghang/instance52132.smt2` | wrong `sat` 30 ms | `unknown:str-model-rejected` 27 ms |
| `QF_SLIA/20230329-denghang/instance55189.smt2` | wrong `sat` 16 ms | `unknown:str-model-rejected` 5 ms |

Spec §1.3 gave the pre-decoder outcome as a count (31 `unsat`, 4 `unknown`)
without naming the rows. The counts match. The row identities were not
independently cross-checked against the throwaway pre-decoder run.
The spec's named reproducer `instance55060` is among the 31 (`unsat`, 11 ms).

## Per-logic matrix

From `bench/results/slice51/report.md`, with the `slice50` row below it:

| logic | run | total | correct | wrong | parse-error | timeout | unknown | unverified | decided% |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_S | slice50 | 18940 | 16025 | 2 | 0 | 8 | 2809 | 96 | 84.6 |
| QF_S | **slice51** | 18940 | **16058** | **0** | 0 | 6 | 2775 | 101 | 84.8 |
| QF_SLIA | slice50 | 84395 | 24798 | 37 | 195 | 43 | 58074 | 1248 | 29.4 |
| QF_SLIA | **slice51** | 84395 | **24815** | **2** | 195 | 43 | 58032 | 1308 | 29.4 |

status-suspect, panic, oom and malformed are 0 in every row. No performance
claim is made from the median/p90 columns (load disclosure above).

## Transition matrices (changed cells only)

| logic | before | after | count | families |
| --- | --- | --- | ---: | --- |
| QF_S | `wrong` | `correct` | 2 | 20230329-automatark-lu 2 |
| QF_S | `correct` | `unknown:str-model-rejected` | 67 | 20230329-automatark-lu 67 |
| QF_S | `correct` | `unknown:sat-budget` | 7 | 20230329-automatark-lu 7 |
| QF_S | `correct` | `unverified` | 3 | 20230329-automatark-lu 3 |
| QF_S | `unknown:str-model-rejected` | `correct` | 107 | 20230329-automatark-lu 107 |
| QF_S | `unknown:str-model-rejected` | `unknown:sat-budget` | 21 | 2019-Jiang 21 |
| QF_S | `unknown:str-model-rejected` | `unverified` | 3 | 20230329-automatark-lu 3 |
| QF_S | `unknown:sat-budget` | `unknown:str-model-rejected` | 2 | 2019-Jiang 2 |
| QF_S | `timeout` | `correct` | 1 | 20230329-automatark-lu 1 |
| QF_S | `timeout` | `unknown:str-model-rejected` | 1 | 20230329-automatark-lu 1 |
| QF_S | `unverified` | `unknown:str-model-rejected` | 1 | 20230329-automatark-lu 1 |
| QF_SLIA | `wrong` | `correct` | 31 | 20230329-denghang 31 |
| QF_SLIA | `wrong` | `unknown:str-model-rejected` | 4 | 20230329-denghang 4 |
| QF_SLIA | `correct` | `unverified` | 59 | 20230327-stringfuzz-lu 55, 20230329-denghang 4 |
| QF_SLIA | `correct` | `unknown:sat-budget` | 1 | 20230329-denghang 1 |
| QF_SLIA | `correct` | `unknown:str-model-rejected` | 1 | 20230329-denghang 1 |
| QF_SLIA | `unknown:str-model-rejected` | `correct` | 46 | 20230329-denghang 46 |
| QF_SLIA | `unknown:str-model-rejected` | `unverified` | 4 | 20230329-denghang 4 |
| QF_SLIA | `unknown:str-model-rejected` | `timeout` | 2 | 20230329-denghang 2 |
| QF_SLIA | `unverified` | `unknown:str-model-rejected` | 4 | 20230329-denghang 4 |
| QF_SLIA | `timeout` | `correct` | 1 | 20230329-denghang 1 |
| QF_SLIA | `timeout` | `unverified` | 1 | 20230329-denghang 1 |

Closure, `new = old − outbound + inbound`:

- QF_S `correct` 16,025 − 77 + 110 = 16,058; `wrong` 2 − 2 = 0;
  `str-model-rejected` 1,033 − 131 + 71 = 973; `sat-budget` 1,353 − 2 + 28 =
  1,379; `timeout` 8 − 2 = 6; `unverified` 96 − 1 + 6 = 101.
- QF_SLIA `correct` 24,798 − 61 + 78 = 24,815; `wrong` 37 − 35 = 2;
  `str-model-rejected` 3,254 − 52 + 9 = 3,211; `sat-budget` 4,198 + 1 =
  4,199; `timeout` 43 − 2 + 2 = 43; `unverified` 1,248 − 4 + 64 = 1,308.

**Escapes in moved rows.** Every row in every changed cell contains at least
one `\u` escape (regex `\\u(\{[0-9a-fA-F]{1,5}\}|[0-9a-fA-F]{4})` over the
corpus file), except 55 of the 59 QF_SLIA `correct → unverified` rows (the
stringfuzz ones, which have none).

**Oracle-side flips (62 rows, noise).** All 62 `correct → unverified` rows
(QF_S 3, QF_SLIA 59) have `:status unknown`, **the same shinri answer on both
runs**, and a branch-run oracle record of `{"z3": "timeout"}`. On `slice50`
z3 confirmed them. This is the concurrent Task 5/6 load, not a solver change.
QF_S `instance10273`, named in slice 50, is one of the three QF_S rows again.

## parse-error triage (195 rows)

`slice50` had the same 195 QF_SLIA parse-error rows: **identical path set**,
all in `20230403-webapp`, with identical `first_error`:

| `first_error` | rows |
| --- | ---: |
| `(error "unknown operator str.replace_re")` | 98 |
| `(error "unknown operator str.replace_re_all")` | 97 |

No row anywhere in `slice51/results.jsonl` contains the string `surrogate`,
so the new "unsupported: surrogate code point in string literal" diagnostic
fired on 0 corpus files. That matches spec §1.4 (no corpus file has a
surrogate escape). Across all 103,335 rows, `first_error` changed on 0 rows.
**No parser regression.**

## Criterion 5: every `correct → unknown/timeout` row

76 rows, all to `unknown`, none to `timeout`. Wall times are the corpus
runs' `wall_ms`. The last column counts `\u` escapes in the file. QF_S
`:status`: 33 `sat`, 39 `unsat`, 2 `unknown`; the 2 QF_SLIA rows are `:status unknown`
that z3 confirmed as `unsat` on `slice50`.

| logic | row | `:status` | base answer (ms) | branch verdict (ms) | `\u` escapes |
| --- | --- | --- | --- | --- | ---: |
| QF_S | `20230329-automatark-lu/instance06201.smt2` | unsat | `unsat` 8 | `unknown:sat-budget` 9 | 21 |
| QF_S | `20230329-automatark-lu/instance08202.smt2` | unsat | `unsat` 3 | `unknown:sat-budget` 67 | 8 |
| QF_S | `20230329-automatark-lu/instance12454.smt2` | unsat | `unsat` 4 | `unknown:sat-budget` 183 | 6 |
| QF_S | `20230329-automatark-lu/instance12840.smt2` | unsat | `unsat` 4 | `unknown:sat-budget` 29 | 6 |
| QF_S | `20230329-automatark-lu/instance14377.smt2` | unsat | `unsat` 3 | `unknown:sat-budget` 186 | 4 |
| QF_S | `20230329-automatark-lu/instance15364.smt2` | unsat | `unsat` 4 | `unknown:sat-budget` 12 | 18 |
| QF_S | `20230329-automatark-lu/instance15772.smt2` | unsat | `unsat` 5 | `unknown:sat-budget` 11 | 25 |
| QF_S | `20230329-automatark-lu/instance06182.smt2` | sat | `sat` 80 | `unknown:str-model-rejected` 12 | 34 |
| QF_S | `20230329-automatark-lu/instance06257.smt2` | sat | `sat` 17 | `unknown:str-model-rejected` 5 | 48 |
| QF_S | `20230329-automatark-lu/instance06533.smt2` | sat | `sat` 6 | `unknown:str-model-rejected` 80 | 14 |
| QF_S | `20230329-automatark-lu/instance06737.smt2` | sat | `sat` 7 | `unknown:str-model-rejected` 3 | 15 |
| QF_S | `20230329-automatark-lu/instance06789.smt2` | sat | `sat` 12 | `unknown:str-model-rejected` 7 | 21 |
| QF_S | `20230329-automatark-lu/instance06924.smt2` | unsat | `unsat` 5 | `unknown:str-model-rejected` 4 | 18 |
| QF_S | `20230329-automatark-lu/instance06943.smt2` | sat | `sat` 43 | `unknown:str-model-rejected` 5 | 90 |
| QF_S | `20230329-automatark-lu/instance07022.smt2` | sat | `sat` 17 | `unknown:str-model-rejected` 4 | 6 |
| QF_S | `20230329-automatark-lu/instance07152.smt2` | sat | `sat` 21 | `unknown:str-model-rejected` 5 | 15 |
| QF_S | `20230329-automatark-lu/instance07820.smt2` | unsat | `unsat` 6 | `unknown:str-model-rejected` 5 | 54 |
| QF_S | `20230329-automatark-lu/instance08094.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 4 | 16 |
| QF_S | `20230329-automatark-lu/instance08340.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 5 | 15 |
| QF_S | `20230329-automatark-lu/instance08384.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 4 | 27 |
| QF_S | `20230329-automatark-lu/instance08424.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 8 | 27 |
| QF_S | `20230329-automatark-lu/instance08616.smt2` | sat | `sat` 7 | `unknown:str-model-rejected` 5 | 6 |
| QF_S | `20230329-automatark-lu/instance08692.smt2` | unsat | `unsat` 8 | `unknown:str-model-rejected` 6 | 20 |
| QF_S | `20230329-automatark-lu/instance08715.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 3 | 18 |
| QF_S | `20230329-automatark-lu/instance08959.smt2` | sat | `sat` 79 | `unknown:str-model-rejected` 15 | 33 |
| QF_S | `20230329-automatark-lu/instance09107.smt2` | sat | `sat` 79 | `unknown:str-model-rejected` 7 | 14 |
| QF_S | `20230329-automatark-lu/instance09355.smt2` | unsat | `unsat` 5 | `unknown:str-model-rejected` 12 | 10 |
| QF_S | `20230329-automatark-lu/instance09408.smt2` | unsat | `unsat` 5 | `unknown:str-model-rejected` 10 | 20 |
| QF_S | `20230329-automatark-lu/instance09679.smt2` | sat | `sat` 4 | `unknown:str-model-rejected` 60 | 10 |
| QF_S | `20230329-automatark-lu/instance09871.smt2` | unsat | `unsat` 5 | `unknown:str-model-rejected` 59 | 13 |
| QF_S | `20230329-automatark-lu/instance09954.smt2` | sat | `sat` 7 | `unknown:str-model-rejected` 6 | 7 |
| QF_S | `20230329-automatark-lu/instance09978.smt2` | unsat | `unsat` 5 | `unknown:str-model-rejected` 5 | 18 |
| QF_S | `20230329-automatark-lu/instance10144.smt2` | sat | `sat` 18 | `unknown:str-model-rejected` 11 | 9 |
| QF_S | `20230329-automatark-lu/instance10320.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 11 | 17 |
| QF_S | `20230329-automatark-lu/instance10323.smt2` | sat | `sat` 27 | `unknown:str-model-rejected` 8 | 8 |
| QF_S | `20230329-automatark-lu/instance10365.smt2` | sat | `sat` 236 | `unknown:str-model-rejected` 10 | 10 |
| QF_S | `20230329-automatark-lu/instance10391.smt2` | sat | `sat` 8 | `unknown:str-model-rejected` 10 | 18 |
| QF_S | `20230329-automatark-lu/instance10554.smt2` | unsat | `unsat` 6 | `unknown:str-model-rejected` 7 | 17 |
| QF_S | `20230329-automatark-lu/instance10627.smt2` | sat | `sat` 59 | `unknown:str-model-rejected` 15 | 50 |
| QF_S | `20230329-automatark-lu/instance11174.smt2` | unsat | `unsat` 5 | `unknown:str-model-rejected` 9 | 19 |
| QF_S | `20230329-automatark-lu/instance11369.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 7 | 15 |
| QF_S | `20230329-automatark-lu/instance11688.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 5 | 22 |
| QF_S | `20230329-automatark-lu/instance12116.smt2` | unsat | `unsat` 5 | `unknown:str-model-rejected` 6 | 14 |
| QF_S | `20230329-automatark-lu/instance12303.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 59 | 23 |
| QF_S | `20230329-automatark-lu/instance12338.smt2` | sat | `sat` 7 | `unknown:str-model-rejected` 6 | 12 |
| QF_S | `20230329-automatark-lu/instance12512.smt2` | sat | `sat` 15 | `unknown:str-model-rejected` 6 | 11 |
| QF_S | `20230329-automatark-lu/instance12592.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 8 | 12 |
| QF_S | `20230329-automatark-lu/instance12707.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 57 | 22 |
| QF_S | `20230329-automatark-lu/instance12748.smt2` | sat | `sat` 5 | `unknown:str-model-rejected` 19 | 7 |
| QF_S | `20230329-automatark-lu/instance12827.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 9 | 12 |
| QF_S | `20230329-automatark-lu/instance12955.smt2` | unknown | `unsat` 15 | `unknown:str-model-rejected` 11 | 36 |
| QF_S | `20230329-automatark-lu/instance13120.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 49 | 16 |
| QF_S | `20230329-automatark-lu/instance13288.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 19 | 8 |
| QF_S | `20230329-automatark-lu/instance13575.smt2` | unsat | `unsat` 5 | `unknown:str-model-rejected` 8 | 10 |
| QF_S | `20230329-automatark-lu/instance13721.smt2` | sat | `sat` 34 | `unknown:str-model-rejected` 16 | 25 |
| QF_S | `20230329-automatark-lu/instance13727.smt2` | sat | `sat` 76 | `unknown:str-model-rejected` 58 | 11 |
| QF_S | `20230329-automatark-lu/instance13859.smt2` | unsat | `unsat` 6 | `unknown:str-model-rejected` 7 | 48 |
| QF_S | `20230329-automatark-lu/instance13962.smt2` | sat | `sat` 5 | `unknown:str-model-rejected` 9 | 10 |
| QF_S | `20230329-automatark-lu/instance13981.smt2` | sat | `sat` 16 | `unknown:str-model-rejected` 49 | 13 |
| QF_S | `20230329-automatark-lu/instance14157.smt2` | sat | `sat` 19 | `unknown:str-model-rejected` 8 | 16 |
| QF_S | `20230329-automatark-lu/instance14253.smt2` | sat | `sat` 15 | `unknown:str-model-rejected` 6 | 23 |
| QF_S | `20230329-automatark-lu/instance14393.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 50 | 19 |
| QF_S | `20230329-automatark-lu/instance14567.smt2` | unknown | `unsat` 72 | `unknown:str-model-rejected` 11 | 14 |
| QF_S | `20230329-automatark-lu/instance14569.smt2` | sat | `sat` 894 | `unknown:str-model-rejected` 25 | 7 |
| QF_S | `20230329-automatark-lu/instance14827.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 13 | 11 |
| QF_S | `20230329-automatark-lu/instance14931.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 6 | 21 |
| QF_S | `20230329-automatark-lu/instance14962.smt2` | sat | `sat` 5 | `unknown:str-model-rejected` 5 | 16 |
| QF_S | `20230329-automatark-lu/instance15088.smt2` | sat | `sat` 100 | `unknown:str-model-rejected` 7 | 25 |
| QF_S | `20230329-automatark-lu/instance15155.smt2` | sat | `sat` 162 | `unknown:str-model-rejected` 5 | 18 |
| QF_S | `20230329-automatark-lu/instance15251.smt2` | sat | `sat` 53 | `unknown:str-model-rejected` 19 | 15 |
| QF_S | `20230329-automatark-lu/instance15670.smt2` | unsat | `unsat` 4 | `unknown:str-model-rejected` 5 | 33 |
| QF_S | `20230329-automatark-lu/instance15865.smt2` | unsat | `unsat` 5 | `unknown:str-model-rejected` 6 | 35 |
| QF_S | `20230329-automatark-lu/instance15866.smt2` | sat | `sat` 24 | `unknown:str-model-rejected` 4 | 28 |
| QF_S | `20230329-automatark-lu/instance15894.smt2` | unsat | `unsat` 6 | `unknown:str-model-rejected` 13 | 15 |
| QF_SLIA | `20230329-denghang/instance45124.smt2` | unknown | `unsat` 12 | `unknown:sat-budget` 14 | 7 |
| QF_SLIA | `20230329-denghang/instance48741.smt2` | unknown | `unsat` 52 | `unknown:str-model-rejected` 6 | 27 |

### Triage

**Largest family, `correct → unknown` direction: `20230329-automatark-lu`
(74 rows; 67 `str-model-rejected`, 7 `sat-budget`).** Representative:
`QF_S/20230329-automatark-lu/instance06924.smt2` (`:status unsat`; base
`unsat` 5 ms, branch `unknown:str-model-rejected` 4 ms).

- Its escapes are `\u{9}`, `\u{a}`, `\u{c}`, `\u{d}` (the whitespace class
  TAB/LF/FF/CR) and `\u{1b}` (ESC). Pre-slice each was read as a
  multi-character run of printable ASCII (`\`, `u`, `{`, hex digits, `}`);
  now each is one control character.
- Assertion-subset minimisation (5 top-level assertions, numbered in file
  order): assertions {1, 2, 3, 5} alone reproduce `unknown`; z3 4.16.0 (from
  mise) answers `unsat`. Every 3-subset of them gets the same answer from
  shinri and z3 (`{1,2,3}` and `{1,2,5}` `sat`; `{1,3,5}` and `{2,3,5}`
  `unsat`). Assertions 1 and 2 are negated memberships over the whitespace
  class and a `\u{a}`-prefixed digit pattern; 3 and 5 are positive
  memberships that already clash on their first character (`/` vs `s`).
  Hand-simplifying the regex of assertion 3, of 5, or of both (three
  attempts) made shinri answer `unsat`, so the minimisation stopped at the
  subset.
- **Code path:** the string theory reaches a SAT candidate, and the
  post-solve witness self-check `string_model_satisfies`
  (`crates/shinri-solver/src/lib.rs:1480`, `last_fence =
  "str-model-rejected"`) rejects it and returns a sound `Unknown`. So the
  row is an existing string-theory incompleteness (premature SAT on negated
  memberships), now exposed by the decoded control characters. The fence
  keeps it sound, and the row is not `wrong`.
- The 7 `sat-budget` rows (all `:status unsat`, 9–186 ms) hit the SAT step
  budget on the decoded formula. They were not traced further.

**Largest family, `unknown → correct` direction: `20230329-automatark-lu`
(107 rows `str-model-rejected → correct`, 60 `sat` + 47 `unsat`; denghang
has another 46).** Representative:
`QF_S/20230329-automatark-lu/instance03287.smt2` (`:status sat`; base
`unknown:str-model-rejected` 6 ms, branch `sat` 5 ms).

- It is one membership, a date regex followed by `(str.to_re "\u{a}")`.
  Pre-slice the suffix was the five-character `\u{a}`; now it is one LF.
  The pre-slice solve reached a candidate that the same self-check
  rejected. On the decoded formula the candidate passes. No cause is
  claimed beyond "the formula changed".

**Net.** Out of `str-model-rejected`: 131 (QF_S) + 52 (QF_SLIA). Into it:
71 + 9. The decoded formulas are, on balance, easier for the fence path
(QF_S 1,033 → 973, QF_SLIA 3,254 → 3,211). The 68 `correct →
str-model-rejected` rows are queued below as a string-theory item, not a
slice-51 defect.

## Gates (Task 6)

- `mise run lint`: clean (fmt `--check` and `clippy --workspace
  --all-targets -D warnings`).
- `mise run test`: **1,576 passed, 7 skipped**.
- Unfiltered oracle suite, `cargo nextest run -p shinri-solver --features
  oracle`: **677 tests across 29 binaries, 677 passed (7 slow), 3 skipped**.
  The discovered count is non-zero.
- `mise run ci`: green.

## Queued for the next slice

- **The Noetzli pair** (spec §10): `str-pred-small-rw_370.smt2` and
  `_458.smt2`, wrong `sat`, no escapes. Now the only `wrong` rows in QF_S +
  QF_SLIA.
- **The 4 denghang `unknown` rows** (spec §10), named in criterion 2:
  `instance46836`, `instance51681`, `instance52132`, `instance55189`, all
  `unknown:str-model-rejected`.
- **New: premature string SAT on decoded control-character regexes.** 68
  rows went `correct → unknown:str-model-rejected` (67 automatark-lu, 1
  denghang `instance48741`); the self-check keeps them sound. Reproducer:
  assertions {1, 2, 3, 5} of `automatark-lu/instance06924.smt2` (z3
  `unsat`, shinri `unknown`). Also 8 `correct → unknown:sat-budget` (7
  automatark-lu, 1 denghang `instance45124`).
- Surrogate support (spec §9 approach 3). Still 0 corpus rows need it
  (0 surrogate diagnostics in this run).
- QF_SLIA parse-error (195, `20230403-webapp`): `str.replace_re` and
  `str.replace_re_all` are unsupported operators. Unchanged by this slice.
- Carried from slice 50, unchanged: the QF_SLIA `STRING_PATH_PIVOT_BUDGET`
  cliff; the Wisa final-check blow-up; `get-value` echoing purification
  names; the `Owner::Shared` definitional merge; `pending` is not
  backtracked; the blocksworld re-index churn measurement; the `blast_word`
  panic bucket.
- Harness nit (carried): the fixture header records the checkout HEAD, not
  the binary's commit. Here they agree (`924ecc9`).

## References

- Spec: `docs/superpowers/specs/2026-09-30-shinri-slice51-string-literal-escapes-design.md`
  (§7 criteria, §10 queue, §12 measured outcomes).
- Slice 50 report: `docs/superpowers/research/2026-09-29-smtlib-2024-slice50-uflia-report.md`.
- Runs (git-ignored): `bench/results/slice51/`, `bench/results/slice50/`.
