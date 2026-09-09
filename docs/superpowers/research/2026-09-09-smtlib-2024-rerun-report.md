<!-- Verbatim artefact: bench/results/rerun-0fca46476479/report.md (run-id rerun-0fca46476479). -->
# shinri-bench report

## Fixture

| field | value |
| --- | --- |
| sha | 0fca46476479 |
| version | shinri 0.1.0 |
| solver | target/release/shinri |
| solver_md5 | 6e59670cce84ae4aa36a9a87a04a4974 |
| timeout_s | 20 |
| mem_mb | 3072 |
| jobs | 6 |
| cpu_max | 800000 100000 |
| memory_max | 34359738368 |
| corpus | 10.5281/zenodo.11061097 |
| started | 2026-09-09T04:24:23Z |

Rows: 48398 across 11 logic(s).

## Per-logic matrix

| logic | total | correct | wrong | status-suspect | parse-error | panic | oom | timeout | unknown | unverified | malformed | decided% | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_ABV | 124 | 0 | 0 | 0 | 26 | 53 | 45 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_AUFBV | 19 | 0 | 0 | 0 | 13 | 0 | 6 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_BV | 4998 | 0 | 0 | 0 | 1401 | 2180 | 1417 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_FP | 40013 | 0 | 0 | 0 | 39998 | 0 | 15 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_LIA | 576 | 0 | 0 | 0 | 0 | 57 | 519 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_LRA | 1065 | 0 | 0 | 0 | 1063 | 0 | 2 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_SLIA | 195 | 0 | 0 | 0 | 195 | 0 | 0 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_UF | 34 | 0 | 0 | 0 | 34 | 0 | 0 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_UFBV | 130 | 0 | 0 | 0 | 50 | 0 | 80 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_UFLIA | 5 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_UFLRA | 1239 | 0 | 0 | 0 | 1229 | 0 | 10 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| all | 48398 | 0 | 0 | 0 | 44009 | 2290 | 2099 | 0 | 0 | 0 | 0 | 0.0 | n/a | n/a |

## Ranked gaps

### parse-error:unsupported command: define-sort — 39994

QF_FP: 39994

- `QF_FP/wintersteiger/abs/abs-has-solution-8522.smt2` (622 bytes)
- `QF_FP/wintersteiger/abs/abs-has-solution-10274.smt2` (626 bytes)
- `QF_FP/wintersteiger/abs/abs-has-solution-11534.smt2` (626 bytes)

### panic:thread 'main' (N) has overflowed its stack — 2290

QF_ABV: 53, QF_BV: 2180, QF_LIA: 57

- `QF_ABV/bmc-arrays/bf8.smt2` (493591 bytes)
- `QF_ABV/bmc-arrays/bf9.smt2` (559182 bytes)
- `QF_BV/bmc-bv/ex30.smt2` (565248 bytes)

### oom — 2099

QF_ABV: 45, QF_AUFBV: 6, QF_BV: 1417, QF_FP: 15, QF_LIA: 519, QF_LRA: 2, QF_UFBV: 80, QF_UFLIA: 5, QF_UFLRA: 10

- `QF_BV/brummayerbiere4/unconstrained10.smt2` (631 bytes)
- `QF_ABV/brummayerbiere3/unconstrained01.smt2` (645 bytes)
- `QF_BV/brummayerbiere4/unconstrained07.smt2` (656 bytes)

### parse-error:sort error: NotApplicable — 1858

QF_LRA: 762, QF_UFLRA: 1096

- `QF_LRA/meti-tarski/polypaver/bench-exp-3d/polypaver-bench-exp-3d-chunk-0018.smt2` (769 bytes)
- `QF_LRA/meti-tarski/polypaver/bench-exp-3d/polypaver-bench-exp-3d-chunk-0020.smt2` (769 bytes)
- `QF_LRA/meti-tarski/atan/problem/1/weak/atan-problem-1-weak-chunk-0019.smt2` (774 bytes)

### parse-error:invalid BV numeral suffix `N` — 1129

QF_ABV: 22, QF_AUFBV: 12, QF_BV: 1045, QF_UFBV: 50

- `QF_BV/brummayerbiere/bitrev0128.smt2` (3097 bytes)
- `QF_BV/brummayerbiere/bitrev0256.smt2` (4657 bytes)
- `QF_ABV/ecc/com.galois.ecc.P384ECC64.field_add8.short.smt2` (4729 bytes)

### parse-error:sort error: Mismatch { expected: SortId(N), found: SortId(N) } — 434

QF_LRA: 301, QF_UFLRA: 133

- `QF_UFLRA/FFT/smtlib.624916.smt2` (600 bytes)
- `QF_UFLRA/FFT/smtlib.624898.smt2` (604 bytes)
- `QF_UFLRA/FFT/smtlib.624882.smt2` (623 bytes)

### parse-error:unknown operator bvcomp — 237

QF_ABV: 1, QF_BV: 236

- `QF_BV/2020-Weber/extensions.smt2` (4147 bytes)
- `QF_BV/float/square.smt2` (14253 bytes)
- `QF_BV/log-slicing/bvsdiv_16.smt2` (26093 bytes)

### parse-error:sort error: Arity { expected: N, found: N } — 125

QF_ABV: 3, QF_AUFBV: 1, QF_BV: 117, QF_FP: 4

- `QF_FP/schanda/spark/discrete.smt2` (428 bytes)
- `QF_FP/schanda/spark/average_2.smt2` (627 bytes)
- `QF_FP/schanda/spark/range_mult.smt2` (692 bytes)

### parse-error:unknown operator str.replace_re — 98

QF_SLIA: 98

- `QF_SLIA/20230403-webapp/lan-rep/lan_replace44.smt2` (1321 bytes)
- `QF_SLIA/20230403-webapp/lan-rep/lan_replace67.smt2` (1598 bytes)
- `QF_SLIA/20230403-webapp/lan-rep/lan_replace102.smt2` (1650 bytes)

### parse-error:unknown operator str.replace_re_all — 97

QF_SLIA: 97

- `QF_SLIA/20230403-webapp/lan-rep-all/lan_replace_all44.smt2` (1325 bytes)
- `QF_SLIA/20230403-webapp/lan-rep-all/lan_replace_all67.smt2` (1602 bytes)
- `QF_SLIA/20230403-webapp/lan-rep-all/lan_replace_all102.smt2` (1654 bytes)

### parse-error:unknown operator ! — 34

QF_UF: 34

- `QF_UF/20170829-Rodin/smt4027072204816894856.smt2` (459 bytes)
- `QF_UF/20170829-Rodin/smt3809952321495040629.smt2` (555 bytes)
- `QF_UF/20170829-Rodin/smt3508124013603727984.smt2` (583 bytes)

### parse-error:(error S — 3

QF_BV: 3

- `QF_BV/brummayerbiere/bitrev2048.smt2` (29049 bytes)
- `QF_BV/brummayerbiere/bitrev4096.smt2` (60132 bytes)
- `QF_BV/brummayerbiere/bitrev8192.smt2` (126973 bytes)

## Wrong answers

_none_

## Perf tail

### timeout+oom by logic

| logic | timeout | oom | timeout+oom | total |
| --- | ---: | ---: | ---: | ---: |
| QF_ABV | 0 | 45 | 45 | 124 |
| QF_AUFBV | 0 | 6 | 6 | 19 |
| QF_BV | 0 | 1417 | 1417 | 4998 |
| QF_FP | 0 | 15 | 15 | 40013 |
| QF_LIA | 0 | 519 | 519 | 576 |
| QF_LRA | 0 | 2 | 2 | 1065 |
| QF_SLIA | 0 | 0 | 0 | 195 |
| QF_UF | 0 | 0 | 0 | 34 |
| QF_UFBV | 0 | 80 | 80 | 130 |
| QF_UFLIA | 0 | 5 | 5 | 5 |
| QF_UFLRA | 0 | 10 | 10 | 1239 |
| all | 0 | 2099 | 2099 | 48398 |

### timeout+oom by size decile

| decile | bytes | rows | timeout+oom |
| ---: | --- | ---: | ---: |
| 1 | 428–962 | 4839 | 24 |
| 2 | 962–977 | 4840 | 0 |
| 3 | 977–1089 | 4840 | 1 |
| 4 | 1089–1309 | 4840 | 0 |
| 5 | 1309–1363 | 4840 | 0 |
| 6 | 1363–1378 | 4839 | 0 |
| 7 | 1378–1391 | 4840 | 0 |
| 8 | 1391–1665 | 4840 | 0 |
| 9 | 1665–1082293 | 4840 | 744 |
| 10 | 1082392–2044326719 | 4840 | 1330 |

### 20 slowest correct instances per logic

#### QF_ABV

_none_

#### QF_AUFBV

_none_

#### QF_BV

_none_

#### QF_FP

_none_

#### QF_LIA

_none_

#### QF_LRA

_none_

#### QF_SLIA

_none_

#### QF_UF

_none_

#### QF_UFBV

_none_

#### QF_UFLIA

_none_

#### QF_UFLRA

_none_

