# shinri-bench report

## Fixture

| field | value |
| --- | --- |
| sha | 0f1e2d3c4b5a69788796a5b4c3d2e1f00f1e2d3c |
| version | shinri 0.1.0 |
| solver | target/release/shinri |
| solver_md5 | 9e107d9d372bb6826bd81d3542a419d6 |
| timeout_s | 20 |
| mem_mb | 3072 |
| jobs | 6 |
| cpu_max | 800000 100000 |
| memory_max | 34359738368 |
| corpus | zenodo.11061097 |
| started | 2026-09-08T00:00:00Z |

Rows: 30 across 3 logic(s).

## Per-logic matrix

| logic | total | correct | wrong | status-suspect | parse-error | panic | oom | timeout | unknown | unverified | malformed | decided% | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_BV | 12 | 6 | 1 | 0 | 0 | 1 | 1 | 2 | 1 | 0 | 0 | 50.0 | 47 | 210 |
| QF_LRA | 6 | 0 | 0 | 0 | 4 | 0 | 0 | 2 | 0 | 0 | 0 | 0.0 | n/a | n/a |
| QF_S | 12 | 6 | 0 | 1 | 0 | 0 | 0 | 0 | 3 | 1 | 1 | 54.5 | 61 | 275 |
| all | 30 | 12 | 1 | 1 | 4 | 1 | 1 | 4 | 4 | 1 | 1 | 41.4 | 47 | 210 |

## Ranked gaps

### timeout — 4

QF_BV: 2, QF_LRA: 2

- `QF_LRA/sc/lra-to04.smt2` (5000 bytes)
- `QF_LRA/sc/lra-to03.smt2` (6000 bytes)
- `QF_BV/core/bv-to02.smt2` (7000 bytes)

### parse-error:sort error: Arity { expected: N, found: N } — 3

QF_LRA: 3

- `QF_LRA/sc/lra-pe01.smt2` (130 bytes)
- `QF_LRA/sc/lra-pe02.smt2` (230 bytes)
- `QF_LRA/sc/lra-pe03.smt2` (330 bytes)

### unknown:str-order — 3

QF_S: 3

- `QF_S/kaluza/s-unk01.smt2` (120 bytes)
- `QF_S/kaluza/s-unk02.smt2` (220 bytes)
- `QF_S/kaluza/s-unk03.smt2` (320 bytes)

### malformed:answers=2 — 1

QF_S: 1

- `QF_S/kaluza/s-mal01.smt2` (180 bytes)

### oom — 1

QF_BV: 1

- `QF_BV/core/bv-oom01.smt2` (9000 bytes)

### panic:crates/shinri-bv/src/blast/mod.rs: internal error: entered unreachable code: non-BV builtin reached blast_word — 1

QF_BV: 1

- `QF_BV/core/bv-panic01.smt2` (250 bytes)

### parse-error:invalid BV numeral suffix `N` — 1

QF_LRA: 1

- `QF_LRA/sc/lra-pe04.smt2` (430 bytes)

### unknown:bv-uf-budget — 1

QF_BV: 1

- `QF_BV/core/bv-unk01.smt2` (700 bytes)

### unverified — 1

QF_S: 1

- `QF_S/kaluza/s-unv01.smt2` (260 bytes)

## Wrong answers

| path | :status | shinri | z3 | cvc5 |
| --- | --- | --- | --- | --- |
| `QF_BV/core/bv-wrong01.smt2` | unsat | sat | unsat | unsat |
| `QF_S/kaluza/s-susp01.smt2` | unsat | sat | sat | sat |

## Perf tail

### timeout+oom by logic

| logic | timeout | oom | timeout+oom | total |
| --- | ---: | ---: | ---: | ---: |
| QF_BV | 2 | 1 | 3 | 12 |
| QF_LRA | 2 | 0 | 2 | 6 |
| QF_S | 0 | 0 | 0 | 12 |
| all | 4 | 1 | 5 | 30 |

### timeout+oom by size decile

| decile | bytes | rows | timeout+oom |
| ---: | --- | ---: | ---: |
| 1 | 100–120 | 3 | 0 |
| 2 | 130–160 | 3 | 0 |
| 3 | 180–210 | 3 | 0 |
| 4 | 220–250 | 3 | 0 |
| 5 | 260–310 | 3 | 0 |
| 6 | 320–400 | 3 | 0 |
| 7 | 410–500 | 3 | 0 |
| 8 | 510–610 | 3 | 0 |
| 9 | 700–6000 | 3 | 2 |
| 10 | 7000–9000 | 3 | 3 |

### 20 slowest correct instances per logic

#### QF_BV

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_BV/core/bv-c06.smt2` | 210 | 600 |
| `QF_BV/core/bv-c05.smt2` | 96 | 500 |
| `QF_BV/core/bv-c04.smt2` | 47 | 400 |
| `QF_BV/core/bv-c03.smt2` | 23 | 300 |
| `QF_BV/core/bv-c02.smt2` | 11 | 200 |
| `QF_BV/core/bv-c01.smt2` | 5 | 100 |

#### QF_LRA

_none_

#### QF_S

| path | wall_ms | bytes |
| --- | ---: | ---: |
| `QF_S/kaluza/s-c06.smt2` | 275 | 610 |
| `QF_S/kaluza/s-c05.smt2` | 130 | 510 |
| `QF_S/kaluza/s-c04.smt2` | 61 | 410 |
| `QF_S/kaluza/s-c03.smt2` | 29 | 310 |
| `QF_S/kaluza/s-c02.smt2` | 13 | 210 |
| `QF_S/kaluza/s-c01.smt2` | 7 | 110 |

