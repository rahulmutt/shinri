# SMT-LIB 2024 re-run — slice 49 (EUF mid-search index) — shinri @ c6cb4219ef8a

Run-id `slice49`:

```
BENCH_LOGICS=QF_DT,QF_UF,QF_UFLIA,QF_UFLRA,QF_S BENCH_RUN_ID=slice49 mise run bench-run
BENCH_RUN_ID=slice49 mise run bench-report
```

The limits match the baseline: 20 s, 3072 MB, 6 jobs, cgroup `cpu.max`
`800000 100000`, `memory.max` 34359738368. The run started
2026-09-11T18:27:05Z and its log was last written at 20:25:05Z, about
**1 h 58 min** of wall-clock. The fixture header records `sha c6cb4219ef8a`
and `solver_md5 38dd78cdd634a4e3da48dd4b29e0f499`. That hash matches
`target/release/shinri` at the branch HEAD (`c6cb4219`, Task 5). The final
log line is:

```
37086/37086  correct=31387 wrong=13 status-suspect=0 parse-error=1263 panic=0 oom=15 timeout=1474 unknown=2837 unverified=97 malformed=0
```

**Comparison runs** (spec §7): `slice48b` (commit `f27a340ceb77`) for QF_DT,
and `baseline-8de004d44944` for QF_UF, QF_UFLIA, QF_UFLRA and QF_S. The
same-path check found **37,086 common paths, 0 missing, 0 extra**, so every
row below compares one path with itself.

**The pre-slice binary for A/B checks** was built from `9240b873`, the merge
base of the branch, in a scratch worktree. This matters for reading the
QF_UF/QF_UFLIA/QF_UFLRA/QF_S deltas. Their comparison run is
`baseline-8de004d44944`, which predates slices 46–48. A delta against it is
therefore not a slice-49 delta until an A/B against `9240b873` says so. Every
changed row in all five logics was A/B-run on both binaries (below).

**How the transitions were computed.** The brief's `transitions.py` (scratch
tooling, not committed) loads each `results.jsonl` keyed by `path`. It
intersects the key sets and buckets `(before verdict, after verdict)` per
logic and per family (`path.split("/")[1]`). Barrett is split into
`barrett-jsat/tests/` and `barrett-jsat/typed/` by substring. Every count
below is a raw tally from that script, and every per-logic and per-family
count closes under `new = old − outbound + inbound` (shown inline).

## Headline

- **QF_DT `wrong` fell from 200 to 0.** Barrett `typed/` went 31 → 0, with
  all 31 now `correct`. Blocksworld went 169 → 0: 83 rows are now `correct`
  and **86 are now `timeout`**. Those 86 are an honest non-answer in place of
  a wrong one. They are not counted as correct anywhere in this report.
- **All 200 A/B-checked.** Pre-slice `9240b873` answers the same wrong
  `sat` on **200 of 200** within 20 s. The branch answers `unsat` on 115 of
  them (the 114 `→ correct` rows, plus one `→ timeout` row that finished in
  17.9 s in the A/B run) and does not answer on 85. This shows
  **the slice changed these answers.** It does not show which mechanism
  changed any one of them. Only `bmc_2` has a trace: slice 48
  delta-debugged it to the §1 repro, and the instrumented run of that repro
  shows §1.2 (criterion 2b).
  The 87 QF_DT rows that are now `timeout` were re-run on the branch with
  **120 s** (6-way parallel). **0 answered `sat`.** 8 answered `unsat`, all
  z3-confirmed, in 18.0–98.9 s. 79 still had no answer at 120 s.
- **QF_DT `correct` rose 7,978 → 8,105 (+127):** 114 `wrong → correct` plus
  13 Barrett `timeout → correct`. On all 13, pre-slice `9240b873` times out
  in the A/B and the branch answers in ≤ 10 ms. They include 6 of slice 48's
  7 `correct → timeout` rows. The 7th, blocksworld `bmc_14`, is still
  `timeout`.
- **QF_DT `timeout` rose 510 → 584 (+74):** +86 from `wrong`, +1 from
  `unverified`, −13 to `correct`.
- **0 `correct → wrong` and 0 `* → wrong` in all five logics.**
- **In the other logics, no changed row shows a slice effect in the A/B.**
  QF_UF `correct` is +5 (10 rows in, 5 out), QF_UFLIA is +1 and QF_UFLRA is
  unchanged. On every changed row, `9240b873` gives the same answer as the
  branch, and no row answers on base but not on the branch. These are
  13.8–20 s instances crossing the 20 s boundary against a three-slice-old
  baseline. QF_S `correct` is **−2**. Neither row is a change
  in shinri's output (criterion 5).
- **Criteria:** 1 PASS, 2 PASS, 2b `unsat` (correct), 3 PASS (0), 4 PASS (0 ≤ 200).
  **5 is MISSED on the literal count for QF_S (16,023 < 16,025).**
  Decomposed below: neither row is an answer the slice lost, but neither
  meets the brief's exclusion test either. The miss is left as a miss for a
  decision before merge. 6: 0 rows confirmed slower on the branch. 7: 0 rows.
  8: QF_UFLIA 11 and QF_S 2, the same paths as the baseline.

## Per-logic matrix (this run)

Copied from `bench/results/slice49/report.md`.

| logic | total | correct | wrong | status-suspect | parse-error | panic | oom | timeout | unknown | unverified | malformed | decided% | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_DT | 8700 | 8105 | 0 | 0 | 0 | 0 | 0 | 584 | 11 | 0 | 0 | 93.2 | 4 | 6 |
| QF_S | 18940 | 16023 | 2 | 0 | 0 | 0 | 0 | 9 | 2809 | 97 | 0 | 84.6 | 5 | 22 |
| QF_UF | 7503 | 7111 | 0 | 0 | 34 | 0 | 0 | 358 | 0 | 0 | 0 | 94.8 | 71 | 4536 |
| QF_UFLIA | 659 | 104 | 11 | 0 | 0 | 0 | 5 | 522 | 17 | 0 | 0 | 15.8 | 2413 | 12521 |
| QF_UFLRA | 1284 | 44 | 0 | 0 | 1229 | 0 | 10 | 1 | 0 | 0 | 0 | 3.4 | 6 | 84 |
| all | 37086 | 31387 | 13 | 0 | 1263 | 0 | 15 | 1474 | 2837 | 97 | 0 | 84.6 | 5 | 124 |

The comparison runs' rows, for reference. QF_DT from
`bench/results/slice48b/report.md`: `8700 | 7978 | 200 | … | 510 | 11 | 1 |
91.7 | 6 | 12`. The others from `baseline-8de004d44944`: QF_S `16025 | 2 | 8 |
2809 | 96 | 84.6 | 5 | 19`; QF_UF `7106 | 0 | 34 pe | 363 | 94.7 | 71 | 4349`;
QF_UFLIA `103 | 11 | 5 oom | 523 | 17 | 15.6 | 2497 | 13196`; QF_UFLRA
`44 | 0 | 1229 pe | 10 oom | 1 | 3.4 | 4 | 76`. The median and p90 columns
come from different days and different surrounding load, and no performance
claim is made from them.

## Verdict counts per logic, against spec §7's comparison table

| logic | verdict | §7 comparison | slice49 | delta |
| --- | --- | ---: | ---: | ---: |
| QF_DT | `correct` | 7,978 | **8,105** | +127 |
| QF_DT | `wrong` | 200 (blocksworld 169, Barrett 31) | **0** | −200 |
| QF_DT | `timeout` | 510 | **584** | +74 |
| QF_DT | `unknown:sat-budget` | 11 | 11 | 0 |
| QF_DT | `unverified` | 1 | 0 | −1 |
| QF_UF | `correct` | 7,106 | **7,111** | +5 |
| QF_UF | `timeout` | 363 | 358 | −5 |
| QF_UF | `parse-error` | 34 | 34 | 0 |
| QF_UFLIA | `correct` | 103 | **104** | +1 |
| QF_UFLIA | `wrong` | 11 | 11 | 0 |
| QF_UFLIA | `timeout` | 523 | 522 | −1 |
| QF_UFLIA | `oom` / `unknown:theory-refused` | 5 / 17 | 5 / 17 | 0 |
| QF_UFLRA | all verdicts | 44 correct, 1,229 pe, 10 oom, 1 timeout | identical | 0 |
| QF_S | `correct` | 16,025 | **16,023** | **−2** |
| QF_S | `wrong` | 2 | 2 | 0 |
| QF_S | `timeout` | 8 | 9 | +1 |
| QF_S | `unknown` (sat-budget 1,353, str-model-rejected 1,033, str-regex 343, str-indexof-replace 80) | 2,809 | 2,809 | 0 |
| QF_S | `unverified` | 96 | 97 | +1 |

QF_DT per family (slice48b → slice49):

| family | slice48b | slice49 |
| --- | --- | --- |
| `20172804-Barrett/barrett-jsat/tests/` (4,000) | correct 3,991, timeout 2, unknown 7 | correct **3,993**, timeout 0, unknown 7 |
| `20172804-Barrett/barrett-jsat/typed/` (4,000) | correct 3,954, **wrong 31**, timeout 11, unknown 4 | correct **3,996**, **wrong 0**, timeout 0, unknown 4 |
| `20210312-Bouvier` (200) | timeout 200 | timeout 200 |
| `20230720-blocksworld` (500) | correct 33, **wrong 169**, timeout 297, unverified 1 | correct **116**, **wrong 0**, timeout **384**, unverified 0 |

## Transition matrices (changed cells only)

| logic | before | after | count | families |
| --- | --- | --- | ---: | --- |
| QF_DT | `wrong` | `correct` | 114 | 20230720-blocksworld 83, 20172804-Barrett 31 (all `typed/`) |
| QF_DT | `wrong` | `timeout` | 86 | 20230720-blocksworld 86 |
| QF_DT | `timeout` | `correct` | 13 | 20172804-Barrett 13 (`typed/` 11, `tests/` 2) |
| QF_DT | `unverified` | `timeout` | 1 | 20230720-blocksworld 1 |
| QF_UF | `timeout` | `correct` | 10 | QG-classification 9, 2018-Goel-hwbench 1 |
| QF_UF | `correct` | `timeout` | 5 | QG-classification 3, NEQ 1, PEQ 1 |
| QF_UFLIA | `timeout` | `correct` | 1 | mathsat 1 |
| QF_S | `correct` | `timeout` | 1 | 20230329-automatark-lu 1 |
| QF_S | `correct` | `unverified` | 1 | 20230329-automatark-lu 1 |

232 rows changed and 36,854 are unchanged. No cell ends in `wrong`, and no
cell leaves `correct` for `wrong`.

**Closure (`new = old − outbound + inbound`):**

- **QF_DT.** `correct` 7,978 + 114 + 13 = 8,105 ✓. `wrong` 200 − 114 − 86 = 0 ✓.
  `timeout` 510 − 13 + 86 + 1 = 584 ✓. `unverified` 1 − 1 = 0 ✓.
  `unknown:sat-budget` 11 ✓.
  - Barrett `typed/`: `correct` 3,954 + 31 + 11 = 3,996 ✓; `wrong` 31 − 31 = 0 ✓;
    `timeout` 11 − 11 = 0 ✓.
  - Barrett `tests/`: `correct` 3,991 + 2 = 3,993 ✓; `timeout` 2 − 2 = 0 ✓.
  - Blocksworld: `correct` 33 + 83 = 116 ✓; `wrong` 169 − 83 − 86 = 0 ✓;
    `timeout` 297 + 86 + 1 = 384 ✓; `unverified` 1 − 1 = 0 ✓.
  - Bouvier: 200 `timeout`, no transitions ✓.
- **QF_UF.** `correct` 7,106 − 5 + 10 = 7,111 ✓. `timeout` 363 + 5 − 10 = 358 ✓.
- **QF_UFLIA.** `correct` 103 + 1 = 104 ✓. `timeout` 523 − 1 = 522 ✓.
- **QF_UFLRA.** No transitions ✓.
- **QF_S.** `correct` 16,025 − 1 − 1 = 16,023 ✓. `timeout` 8 + 1 = 9 ✓.
  `unverified` 96 + 1 = 97 ✓.

### A/B method

Every changed row was re-run on both binaries: pre-slice `9240b873`
("base") and the branch `c6cb4219`. Each run used
`timeout 20 prlimit --as=3221225472`, and the last `sat|unsat|unknown` line
on stdout was taken as the answer. The seven `correct → *` rows (criteria 5
and 6) were timed three ways:

1. **Sequential**, exactly as the brief's Step 5 loop is written
   (`ab-results.txt`).
2. **Loaded**: for each row, 3 base and 3 branch runs launched at once,
   6-way concurrent to match the bench's 6 jobs (`ab-results-loaded6.txt`).
3. The other 225 changed rows were run once per binary, with `xargs -P 6`
   (`ab2-results.txt`).

A 120 s branch re-run of the 87 QF_DT rows that are now `timeout` is
reported under criterion 4.

## Success criteria

| # | criterion | gate | result | verdict |
| --- | --- | --- | --- | --- |
| 1 | Tasks 1–3's tests and Task 5's case 9 failed on pre-slice `main` and pass now | hard | all four failed first (quoted in §"Oracle and test evidence"); all pass in Task 6's gates at `c6cb4219` | **PASS** |
| 2 | §1 repro answers `unsat` | hard | the e2e pin `injectivity_over_selector_minted_under_a_case_split_is_unsat` passed at Task 5 Step 5 and in the Task 6 gates. Run directly on the inline query: base `sat`, branch `unsat`, z3 `unsat`. Unit-equality variant: base `unsat`, branch `unsat` | **PASS** |
| 2b | `blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2` answers `unsat` | measured | `slice49` row: `unsat`, 16 ms, `correct` (slice48b: `sat`, 30 ms, `wrong`). A/B: base `sat`, branch `unsat` | **`unsat`** |
| 3 | `correct → wrong`, all five logics | **0**, hard | **0** | **PASS** |
| 4 | QF_DT `wrong` ≤ 200 | hard | **0**. Barrett −31 (all → `correct`); blocksworld −169 (83 → `correct`, 86 → `timeout`) | **PASS** |
| 5 | per-logic `correct` ≥ comparison run | hard | QF_DT 8,105 ≥ 7,978; QF_UF 7,111 ≥ 7,106; QF_UFLIA 104 ≥ 103; QF_UFLRA 44 = 44; **QF_S 16,023 < 16,025** | **MISS (QF_S, −2), decomposed below** |
| 6 | `correct → {timeout, unknown, oom}` | measured | 6 rows (QF_UF 5, QF_S 1), plus QF_S's 1 `correct → unverified`. **0** show base answering where the branch does not, in either A/B | measured: **0 rows of slice cost** |
| 7 | `* → wrong` from a non-`correct` verdict | measured | **0 rows**, so Step 6 had nothing to run | measured: 0 |
| 8 | QF_UFLIA 11 and QF_S 2 wrong rows | measured | QF_UFLIA **11**, QF_S **2**. The same paths as the baseline, each with the same wrong answer | measured |

### Criterion 5: QF_S 16,023 against 16,025, decomposed rather than relaxed

The brief's exclusion test (Step 5) is "`base` also fails to answer within
20 s on this re-run". Neither QF_S row meets it, because base and branch
both answer on both rows. So neither is excluded, and QF_S misses the floor
by 2. The miss is decomposed below and left standing for a decision before
merge.

| path | comparison run | slice49 run | sequential A/B (base / branch) | loaded A/B, 3 + 3 concurrent (base / branch) | what changed |
| --- | --- | --- | --- | --- | --- |
| `QF_S/20230329-automatark-lu/instance10357.smt2` (`:status sat`) | `sat`, 13,913 ms, `correct` | no answer, 20,017 ms, `timeout` | `sat` 12,181 ms / `sat` 12,117 ms | `sat` 13,168–13,220 ms / `sat` 13,121–13,191 ms | Neither binary reproduces the timeout. The row ran ~13 s at baseline and ~12–13 s in every A/B run, on both binaries. The corpus run's 20,017 ms is not reproduced |
| `QF_S/20230329-automatark-lu/instance10273.smt2` (`:status unknown`) | shinri `unsat` 11 ms; oracle z3 `unsat`: `correct` | shinri `unsat` 22 ms; oracle z3 **`timeout`**: `unverified` | `unsat` 13 ms / `unsat` 12 ms | `unsat` 12–14 ms / `unsat` 11–13 ms | **shinri's answer is identical.** `:status` is `unknown`, so the verdict rests on the z3 oracle, which runs under the same 20 s limit. z3 4.16.0 alone takes **14,815 / 14,574 / 14,516 ms** here (3 sequential runs), and in this run it timed out |

**What the decomposition shows:** 0 of the 2 rows is an answer the slice
lost. One is an oracle-side verdict flip with byte-identical solver output.
The other is a timeout that neither binary reproduces. **What it does not
show:** neither row passes the brief's operational exclusion test, so the
hard gate is missed as written. Whether a same-answer oracle flip and an
unreproducible timeout count as "boundary noise" for this gate is a decision
to make before merge. This report does not make it.

### Criterion 6: every `correct → *` row with its A/B result

| path | comparison ms | slice49 | sequential A/B base / branch | loaded A/B base (3 runs) / branch (3 runs) | classification |
| --- | ---: | --- | --- | --- | --- |
| `QF_UF/NEQ/NEQ048_size6.smt2` | 19,800 | timeout 20,020 | `unsat` 18,082 / `unsat` 18,076 | `unsat` 20,002, none, none / `unsat` 19,680, 19,818, 19,845 | 20 s boundary; base is no faster (base timed out 2 of 3 under load, branch 0 of 3) |
| `QF_UF/PEQ/PEQ003_size7.smt2` | 16,853 | timeout 20,014 | `unsat` 15,667 / `unsat` 17,390 | `unsat` 17,341–17,527 / `unsat` 17,286–17,439 | neither times out in the A/B. Sequential branch +1.7 s is not repeated under load (Δ < 0.1 s) |
| `QF_UF/QG-classification/qg5/gensys_brn875.smt2` | 19,870 | timeout 20,005 | `unsat` 19,768 / `unsat` 18,604 | none ×3 / none ×3 | boundary: **flips identically on base under load** |
| `QF_UF/QG-classification/qg5/gensys_icl088.smt2` | 19,744 | timeout 20,004 | `unsat` 18,252 / `unsat` 18,108 | none ×3 / none ×3 | boundary: **flips identically on base under load** |
| `QF_UF/QG-classification/qg5/gensys_icl987.smt2` | 19,439 | timeout 20,005 | `unsat` 18,637 / `unsat` 18,600 | none ×3 / none ×3 | boundary: **flips identically on base under load** |
| `QF_S/20230329-automatark-lu/instance10357.smt2` | 13,913 | timeout 20,017 | `sat` 12,181 / `sat` 12,117 | `sat` 13,168–13,220 / `sat` 13,121–13,191 | not reproduced on either binary (criterion 5) |
| `QF_S/20230329-automatark-lu/instance10273.smt2` (`→ unverified`) | 11 | `unsat` 22, z3 timeout | `unsat` 13 / `unsat` 12 | `unsat` 12–14 / `unsat` 11–13 | oracle-side; shinri output identical (criterion 5) |

**None of the 7 rows is confirmed slower on the branch.** The slice's
measured cost on these rows is 0. QF_UF passes criterion 5 without any
exclusion, so the three rows that flip identically under load change no
verdict. The QF_UF movement is symmetric: 10 `timeout → correct` rows
(9 QG-classification `qg5`, 1 Goel `frogs.3`) are answered by base too, in
13.8–19.0 s, within 0.4 s of the branch (`ab2-results.txt`). Treat it as
±5–10 rows of 20 s-boundary churn against a three-slice-old baseline. It is
neither a gain nor a loss from this slice. The same holds for QF_UFLIA's
`mathsat/Hash/hash_uns_05_13.smt2` (`timeout → correct`): base answers in
15,622 ms and the branch in 15,285 ms.

### Criterion 4: which slice-48 wrong rows moved, and to what

All 200 `slice48b` wrong rows left `wrong`. The full per-row list, with
both runs' answers and the 20 s A/B, is in the appendix.

| family | slice48b wrong | → `correct` | → `timeout` | still `wrong` |
| --- | ---: | ---: | ---: | ---: |
| Barrett `typed/` | 31 | 31 | 0 | 0 |
| blocksworld | 169 | 83 | 86 | 0 |
| **total** | **200** | **114** | **86** | **0** |

**A/B (20 s), all 200 rows.** Base answered `sat` on 200 of 200. That
reproduces `slice48b`'s wrong answer on every row, so the comparison run
and the merge base agree. Base times: Barrett median 8 ms (max 34 ms);
blocksworld `→ correct` median 173 ms (max 2,044 ms); blocksworld
`→ timeout` median 3,600 ms (range 222–18,974 ms). The branch answered:

- **Barrett `typed/` `→ correct` (31):** `unsat` on 31 of 31, median 6 ms.
- **Blocksworld `→ correct` (83):** `unsat` on 83 of 83, median 108 ms, max 15,105 ms.
- **Blocksworld `→ timeout` (86):** no answer on 85. One row,
  `blocksworld_from_6_9_0_to_14_0_1_negated_goal_bmc_7.smt2`, answered
  `unsat` in 17,911 ms, against 20,011 ms (timeout) in the corpus run.

What this establishes: on every one of the 200 rows, **the slice changed
shinri's answer** from the wrong `sat`. What it does not establish: **which
mechanism** changed any row other than `bmc_2`. The slice changes EUF
indexing on backtrack and adds `close` at `propagate`/`check`. Either
change alters search trajectories across every EUF-routed logic. No row
other than `bmc_2` was traced, so no row other than `bmc_2` is attributed to
§1.2. They are **unattributed** answer changes.

**The 86 `wrong → timeout` rows are not correctness wins.** They trade a
fast wrong answer (base median 3.6 s) for no answer at 20 s. At `slice48b`,
58 of them were z3-confirmed `unsat`, and on the other 28 z3 itself timed
out, so those are wrong only against `:status unsat`.

**The 120 s branch re-run** covers all 87 QF_DT rows now in `timeout`: these 86 plus
the `unverified → timeout` row. It ran 6-way parallel, `timeout 120`, same
`prlimit` (`dt-timeout-branch120.txt`, 1,680 s wall). **No row answered
`sat`**, so within 120 s the branch never gives the wrong answer these rows
had at `slice48b`. **8 answered `unsat`**, which matches `:status`, and all
8 were z3-confirmed `unsat` at `slice48b`:

| path (under `QF_DT/20230720-blocksworld/`) | branch 120 s |
| --- | ---: |
| `blocksworld_from_6_9_0_to_14_0_1_negated_goal_bmc_7.smt2` | `unsat` 17,985 ms |
| `blocksworld_from_7_3_12_to_12_0_10_negated_goal_bmc_7.smt2` | `unsat` 21,826 ms |
| `blocksworld_from_12_0_7_to_18_0_1_negated_goal_bmc_7.smt2` | `unsat` 40,270 ms |
| `blocksworld_from_5_0_0_to_5_0_0_negated_goal_bmc_8.smt2` | `unsat` 48,675 ms |
| `blocksworld_from_18_1_7_to_7_17_2_negated_goal_bmc_7.smt2` | `unsat` 51,868 ms |
| `blocksworld_from_2_4_0_to_0_3_3_negated_goal_bmc_7.smt2` | `unsat` 59,804 ms |
| `blocksworld_from_2_6_2_to_3_4_3_negated_goal_bmc_7.smt2` | `unsat` 75,613 ms |
| `blocksworld_from_12_7_0_to_14_5_0_negated_goal_bmc_7.smt2` | `unsat` 98,858 ms |

79 rows still had no answer at 120 s. That includes the `unverified` row,
`bmc_17`. At 120 s, these rows are not sitting just past the 20 s boundary.
The 8 `unsat` rows show that at least some of the 86 are correct answers
the 20 s limit cuts off. No claim is made about the 79 beyond 120 s.

The one other blocksworld row that moved is `unverified → timeout`:
`blocksworld_from_5_0_5_to_5_3_2_negated_goal_bmc_17.smt2`. At `slice48b`
it answered `sat` with `:status unknown`, and z3 timed out, so its correct
answer is not known. In the A/B, base still answers `sat` (11,667 ms) and
the branch does not answer within 20 s.

**Slice 48's other named rows.**

- The cheapest standalone blocksworld reproducer slice 48 named,
  `blocksworld_from_0_18_1_to_17_2_0_negated_goal_bmc_5.smt2`, is now
  `correct` (`unsat`, 430 ms; slice48b `sat` 591 ms). This is unattributed.
- 6 of slice 48's 7 `correct → timeout` rows are `correct` again:
  `typed_v10l50025`, `typed_v3l60096`, `typed_v5l40035`, `typed_v5l60030`,
  `typed_v5l70010` and `tests/v1/v1l60099`. Each answers `sat` in 4–7 ms,
  where base times out at 20 s in the A/B. This is unattributed.
- The 7th, `blocksworld_from_3_5_0_to_8_0_0_negated_goal_bmc_14.smt2`, is
  still `timeout` (20,020 ms).

**Against spec §1.4's blast radius.** Spec §7 traced one wrong row to
§1.2 and claimed no number. All 200 moved, but only 114 became correct.
The 86 blocksworld timeouts are the family's new residual. The family now
reads 116 correct / 384 timeout / 0 wrong.

## The slice-48 root-cause correction (spec §1.1)

The slice-48 report's `#### Root cause of
blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2` attributes the
defect to `EGraph::add_term` recording `Undo::LookupInsert`. **That text is
wrong.** The slice-48 report is historical and is not rewritten. This report
carries the correction. From spec §1.1:

> **`add_term` records no undo entry at all.** `Undo::LookupInsert` is recorded
> only by `recanonicalize_use_list` (`crates/shinri-euf/src/egraph.rs:345`).
> `add_term`'s registration is permanent, so the described mechanism cannot occur.

The confirmed mechanism, from spec §1.2:

> **(I-use)** At every decision level, every app is on the use-list of the
> **current representative** of each of its arguments.
>
> `recanonicalize_use_list` keeps (I-use) across merges by draining the loser's
> use-list into the winner's and re-signing each moved app. `add_term` keeps it at
> registration time by pushing the new app onto `use_list[find(arg)]`
> (`egraph.rs:172`). It installs the signature with `lookup.insert`
> (`egraph.rs:187`). **Neither write is logged.** When `find(arg)` is a
> representative only because of a merge at the current level:
>
> 1. **Level L ≥ 1.** Classes W and X merge, with W the winner. `add_term(f(x))`
>    runs for an `x` in X's class. The app goes onto `use_list[W]`, and signature
>    `(f, [W])` goes into `lookup`, both unlogged.
> 2. **Pop below L.** The equality engine undoes the W/X merge. `UseSplice`
>    moves X's original apps back. `f(x)` stays on `use_list[W]`, although `x`'s
>    representative is X again. (I-use) is now false.
> 3. **Re-merge.** Union-by-size breaks ties deterministically
>    (`crates/shinri-theory/src/eq_engine.rs:209`), so W wins again.
>    `recanonicalize_use_list` walks only the **loser's** list. X's list holds
>    nothing for `f(x)`, so `f(x)` is never re-signed, no collision is found, and
>    no congruence is enqueued.

The evidence, from spec §1.3. First, the unit probe, which Task 1 made
permanent as `midsearch_registration_keeps_congruence_across_backtrack`:

```
PROBE level1 f(a)==f(b): true
PROBE after pop f(a)==f(b): false use_list[a]=[2, 3] use_list[b]=[]
PROBE remerge rep(a)=ENodeId(0) rep(b)=ENodeId(0) f(a)==f(b): false
panicked: congruence lost after mid-search add_term + backtrack
```

Second, the instrumented §1 repro:

```
PROBE49 merge level=0 winner=ENodeId(8) loser=ENodeId(11) moved=[] winner_list=[]
PROBE49 merge level=1 winner=ENodeId(0) loser=ENodeId(8) moved=[] winner_list=[13]
PROBE49 add_term level=1 app_term=TermId(23) op=Uninterpreted(SymbolId(9)) arg=ENodeId(11) keyed_on_rep=ENodeId(0)
PROBE49 pop 1 -> 0
…
PROBE49 merge level=2 winner=ENodeId(0) loser=ENodeId(8) moved=[] winner_list=[13, 14, 15, 16]
```

The slice-48 report's other findings stand as written: the delta-debugged
9-line repro, the `sat-ctor`/`sat-sel` dump showing two same-class `stack`
applications whose `top` selectors never merged, and the observation that
`qfdt_oracle`'s level-0-only generator could not reach the defect. Only the
named mechanism is corrected.

## Oracle and test evidence

**Task 1 (§4.2 case 8).** Failed on pre-slice code (`task-1-report.md`,
Step 4):

```
thread 'egraph::index_tests::midsearch_registration_keeps_congruence_across_backtrack' (706505) panicked at crates/shinri-euf/src/egraph/test_rig.rs:165:13:
index invariant violated: (I-use) app 3 (op Uninterpreted(SymbolId(3))): argument representatives [1] but on use-lists [0]
```

Its e2e pin failed too (Step 6):

```
thread 'injectivity_over_selector_minted_under_a_case_split_is_unsat' (710045) panicked at crates/shinri-solver/tests/qfdt_e2e.rs:607:5:
assertion `left == right` failed: a selector application minted while a same-constructor merge holds only inside a case split must keep its congruence across backtracking
  left: ["sat"]
 right: ["unsat"]
```

The unit-equality guard, `injectivity_over_selector_with_the_equality_as_a_unit_is_unsat`,
passed on pre-slice code, as designed.

**Task 2 (differential property test).** Failed on pre-slice code
(`task-2-report.md`). The committed-state minimal trace is exactly the §1.2
shape:

```
Test failed: (I-use) app 5 (op Uninterpreted(SymbolId(5))): argument representatives [5] but on use-lists [3].
minimal failing input: steps = [
    Push,
    MergeThenRegister(0, 0, 24),
    MergeThenRegister(3, 155, 71),
    Pop(0),
]
```

**Task 3 (`qfdt_oracle` guarded-record generator).** Failed on pre-slice
code, run with `--features oracle` and 1 test discovered
(`task-3-report.md`):

```
assertion `left == right` failed: QF_DT SOUNDNESS DISAGREEMENT (guarded records, iter 8): shinri=sat z3=unsat
```

**Task 4.** RED was a compile error, `error[E0609]: no field 'reindex' on
type 'egraph::EGraph'`, in the edge-case tests for §4.2 cases 1–7. After
Task 4 the guarded-record oracle read `300 iters, 200 sat / 93 unsat /
7 skipped, 0 mismatches`.

**Task 5 (§4.2 case 9).** Failed before `close` existed (`task-5-report.md`):

```
thread 'solver::tests::registration_time_collision_is_closed_by_check' (1063438) panicked at crates/shinri-euf/src/solver.rs:514:18:
a = b forces f(a) = f(b); with f(a) != f(b) asserted, check must report the conflict
thread 'solver::tests::registration_time_collision_is_closed_by_propagate' (1063437) panicked at crates/shinri-euf/src/solver.rs:498:55:
a = b forces f(a) = f(b); with f(a) != f(b) asserted, propagate must report the conflict
```

**Today's passes: the Task 6 gates at `c6cb4219`.**

- `mise run test`: **1,532 passed, 7 skipped** (65 binaries). It includes
  `midsearch_registration_keeps_congruence_across_backtrack` (PASS),
  `egraph_matches_reference_closure` (PASS, 1.795 s), and both
  `registration_time_collision_is_closed_by_{propagate,check}` (PASS). It
  also includes both `qfdt_e2e` injectivity pins (PASS).
- `cargo nextest run -p shinri-solver --features oracle`, **unfiltered**:
  **656 passed, 3 skipped**, 29 binaries.
  `qfdt_random_guarded_records_match_z3` PASS (34.8 s).
- `cargo nextest run -p shinri-solver -E 'binary(script_e2e)'`: **73 passed,
  1 skipped**.
- `cargo fmt --all -- --check` and
  `cargo clippy --workspace --all-targets -- -D warnings`: clean.
- CI on PR #60: green.

## Queued for the next slice

Spec §10's list, updated with what this run showed.

- **`Owner::Shared` definitional merge bypasses EUF** (`combiner.rs:185`).
  Unchanged and **unverified**: it needs a named repro that reaches the arm
  above level 0 before it counts as a diagnosis. Nothing in this run bears
  on it.
- **`pending` is not backtracked** (§3.4). Unchanged. Only the
  drain-before-push contract keeps it safe. The raw user-scope SAT `push` is
  still the one caller that could break it.
- **Blocksworld's 86 new `timeout` rows** (formerly `wrong`). The family
  has 384 timeouts in total, of which 297 were already timeouts at
  `slice48b`. A 120 s re-run answered 8 of the 86 `unsat` (18.0–98.9 s,
  all `bmc_7`/`bmc_8`), none `sat`, and left 78 unanswered. Nothing here
  attributes them to re-index churn. Spec §9's Approach B un-banking trigger
  is "criterion 6 attributes QF_DT `correct → timeout` rows to re-index
  churn". It did **not** fire: QF_DT has 0 `correct → timeout` rows.
- **Slice 48's QF_DT residuals, which moved.** All 31 Barrett `typed/`
  wrong rows are now `correct`, and 6 of the 7 slice-48 `correct → timeout`
  rows are `correct`. These leave the queue as wrong or timeout rows. The
  mechanism is unattributed: the A/B shows the slice changed them, and no
  trace says why. Slice 48's two `typed/` hypotheses (word_norm's
  ite-elimination; the negative-tester no-op) were never confirmed. Neither
  is needed for a queue item now.
- **Slice 48's QF_DT residuals, which did not move.**
  `blocksworld_from_3_5_0_to_8_0_0_negated_goal_bmc_14.smt2` is still
  `timeout`. Blocksworld's other 297 slice48b timeouts and Bouvier's 200
  are all unchanged.
- **QF_S `instance10273` is an oracle-boundary row.** z3 needs about 14.5 s
  (3 sequential runs, unloaded) against a 20 s oracle limit, so its verdict can flip between `correct`
  and `unverified` from run to run with no change in shinri. Any future
  QF_S `correct` floor should exclude it, or give the oracle a longer
  limit.
- **QF_UF's `qg5` boundary set.** At least 12 `QG-classification/qg5` rows
  sit at 13.8–20 s and cross the boundary in both directions. Here 9 moved
  in, and base answers all 9 as well; 3 moved out, and under load all 3
  time out identically on base. A future QF_UF floor should expect ±5–10 rows.
- **Criterion 5's wording.** The brief's operational exclusion test ("base
  also fails within 20 s") does not cover an oracle-side flip, or a timeout
  that neither binary reproduces. Future slices' criteria should say how
  those count.
- **The rest of the slice-46 queue:** rank 3 (the small wrong-answer
  clusters, including QF_S's 2 wrong rows and QF_UFLIA's 11
  Wisa/wisas wrong `sat` rows against z3 `unsat`). The QF_S rows are
  `instance09174`, where shinri answers `sat` against `:status unsat`, and
  `instance10773`, where it answers `unsat` against `:status sat`. The
  `blast_word` panic bucket follows.

## References

- Spec: `docs/superpowers/specs/2026-09-11-shinri-slice49-euf-midsearch-index-design.md`
  (§7 criteria, `## 12. Measured outcomes`).
- Slice 48 report (its root-cause text is corrected above):
  `docs/superpowers/research/2026-09-10-smtlib-2024-qfdt-slice48-report.md`.
- Raw results (git-ignored): `bench/results/slice49/results.jsonl` (37,086
  rows), rendered `bench/results/slice49/report.md`, run log
  `bench/results/slice49-run.log`. Comparison runs:
  `bench/results/slice48b/`, `bench/results/baseline-8de004d44944/`.
- Commits: T1 `5fbc7529`, T2 `685c471b`, T3 `7114e1a0`, T4 `9f47ff76`,
  T5 `c6cb4219` (the measured binary). A/B base: `9240b873`.

## Appendix: every changed QF_DT row

The A/B columns are the single 20 s run per binary from `ab2-results.txt`,
6-way parallel. "none" means no `sat|unsat|unknown` line before the
timeout.

### `wrong` → `correct` (114)

| path (under `QF_DT/`) | `:status` | slice48b (z3) | slice49 | A/B base 20 s | A/B branch 20 s |
| --- | --- | --- | --- | --- | --- |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l30072.cvc.smt2` | unsat | sat 16 ms (unsat) | unsat 4 ms | sat 10 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l40088.cvc.smt2` | unsat | sat 15 ms (unsat) | unsat 11 ms | sat 13 ms | unsat 12 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l50060.cvc.smt2` | unsat | sat 16 ms (unsat) | unsat 5 ms | sat 10 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l60011.cvc.smt2` | unsat | sat 30 ms (unsat) | unsat 12 ms | sat 22 ms | unsat 15 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l60064.cvc.smt2` | unsat | sat 13 ms (unsat) | unsat 4 ms | sat 12 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l60089.cvc.smt2` | unsat | sat 9 ms (unsat) | unsat 4 ms | sat 9 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l70003.cvc.smt2` | unsat | sat 52 ms (unsat) | unsat 6 ms | sat 34 ms | unsat 7 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l80008.cvc.smt2` | unsat | sat 31 ms (unsat) | unsat 6 ms | sat 20 ms | unsat 8 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l80088.cvc.smt2` | unsat | sat 12 ms (unsat) | unsat 5 ms | sat 10 ms | unsat 8 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l90047.cvc.smt2` | unsat | sat 9 ms (unsat) | unsat 3 ms | sat 8 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v10/typed_v10l30054.cvc.smt2` | unsat | sat 8 ms (unsat) | unsat 3 ms | sat 6 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v10/typed_v10l50015.cvc.smt2` | unsat | sat 6 ms (unsat) | unsat 4 ms | sat 6 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v10/typed_v10l70034.cvc.smt2` | unsat | sat 7 ms (unsat) | unsat 4 ms | sat 6 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l30092.cvc.smt2` | unsat | sat 6 ms (unsat) | unsat 5 ms | sat 5 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l40036.cvc.smt2` | unsat | sat 9 ms (unsat) | unsat 3 ms | sat 8 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l40052.cvc.smt2` | unsat | sat 5 ms (unsat) | unsat 3 ms | sat 6 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l40072.cvc.smt2` | unsat | sat 13 ms (unsat) | unsat 4 ms | sat 9 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l50099.cvc.smt2` | unsat | sat 15 ms (unsat) | unsat 5 ms | sat 12 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l60036.cvc.smt2` | unsat | sat 7 ms (unsat) | unsat 5 ms | sat 7 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l60047.cvc.smt2` | unsat | sat 17 ms (unsat) | unsat 7 ms | sat 13 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70043.cvc.smt2` | unsat | sat 12 ms (unsat) | unsat 4 ms | sat 12 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70064.cvc.smt2` | unsat | sat 6 ms (unsat) | unsat 4 ms | sat 7 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l70078.cvc.smt2` | unsat | sat 7 ms (unsat) | unsat 5 ms | sat 7 ms | unsat 7 ms |
| `20172804-Barrett/barrett-jsat/typed/v3/typed_v3l20027.cvc.smt2` | unsat | sat 4 ms (unsat) | unsat 4 ms | sat 6 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v3/typed_v3l20036.cvc.smt2` | unsat | sat 5 ms (unsat) | unsat 5 ms | sat 5 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v3/typed_v3l80051.cvc.smt2` | unsat | sat 11 ms (unsat) | unsat 3 ms | sat 7 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v3/typed_v3l90045.cvc.smt2` | unsat | sat 7 ms (unsat) | unsat 4 ms | sat 7 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v3/typed_v3l90094.cvc.smt2` | unsat | sat 15 ms (unsat) | unsat 4 ms | sat 11 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v5/typed_v5l30006.cvc.smt2` | unsat | sat 6 ms (unsat) | unsat 3 ms | sat 5 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v5/typed_v5l40047.cvc.smt2` | unsat | sat 4 ms (unsat) | unsat 3 ms | sat 6 ms | unsat 8 ms |
| `20172804-Barrett/barrett-jsat/typed/v5/typed_v5l90035.cvc.smt2` | unsat | sat 6 ms (unsat) | unsat 5 ms | sat 9 ms | unsat 7 ms |
| `20230720-blocksworld/blocksworld_from_0_18_1_to_17_2_0_negated_goal_bmc_5.smt2` | unsat | sat 591 ms (unsat) | unsat 430 ms | sat 631 ms | unsat 426 ms |
| `20230720-blocksworld/blocksworld_from_0_1_19_to_6_3_11_negated_goal_bmc_2.smt2` | unsat | sat 94 ms (unsat) | unsat 11 ms | sat 78 ms | unsat 12 ms |
| `20230720-blocksworld/blocksworld_from_0_9_4_to_3_3_7_negated_goal_bmc_5.smt2` | unsat | sat 486 ms (unsat) | unsat 318 ms | sat 533 ms | unsat 300 ms |
| `20230720-blocksworld/blocksworld_from_10_0_0_to_7_3_0_negated_goal_bmc_6.smt2` | unsat | sat 347 ms (unsat) | unsat 1,694 ms | sat 410 ms | unsat 1,831 ms |
| `20230720-blocksworld/blocksworld_from_11_4_8_to_17_1_5_negated_goal_bmc_2.smt2` | unsat | sat 63 ms (unsat) | unsat 13 ms | sat 75 ms | unsat 15 ms |
| `20230720-blocksworld/blocksworld_from_11_6_0_to_8_0_9_negated_goal_bmc_5.smt2` | unsat | sat 640 ms (unsat) | unsat 170 ms | sat 662 ms | unsat 172 ms |
| `20230720-blocksworld/blocksworld_from_12_0_7_to_18_0_1_negated_goal_bmc_5.smt2` | unsat | sat 472 ms (unsat) | unsat 478 ms | sat 451 ms | unsat 458 ms |
| `20230720-blocksworld/blocksworld_from_12_1_1_to_5_7_2_negated_goal_bmc_3.smt2` | unsat | sat 125 ms (unsat) | unsat 25 ms | sat 135 ms | unsat 29 ms |
| `20230720-blocksworld/blocksworld_from_12_1_3_to_11_1_4_negated_goal_bmc_2.smt2` | unsat | sat 69 ms (unsat) | unsat 10 ms | sat 82 ms | unsat 10 ms |
| `20230720-blocksworld/blocksworld_from_12_7_0_to_14_5_0_negated_goal_bmc_4.smt2` | unsat | sat 464 ms (unsat) | unsat 66 ms | sat 525 ms | unsat 63 ms |
| `20230720-blocksworld/blocksworld_from_13_1_5_to_8_4_7_negated_goal_bmc_2.smt2` | unsat | sat 49 ms (unsat) | unsat 48 ms | sat 56 ms | unsat 13 ms |
| `20230720-blocksworld/blocksworld_from_13_2_4_to_13_3_3_negated_goal_bmc_5.smt2` | unsat | sat 952 ms (unsat) | unsat 839 ms | sat 960 ms | unsat 849 ms |
| `20230720-blocksworld/blocksworld_from_13_2_4_to_13_3_3_negated_goal_bmc_6.smt2` | unsat | sat 1,953 ms (unsat) | unsat 8,149 ms | sat 2,044 ms | unsat 5,470 ms |
| `20230720-blocksworld/blocksworld_from_16_2_1_to_12_6_1_negated_goal_bmc_4.smt2` | unsat | sat 264 ms (unsat) | unsat 247 ms | sat 286 ms | unsat 171 ms |
| `20230720-blocksworld/blocksworld_from_16_4_2_to_16_3_3_negated_goal_bmc_1.smt2` | unsat | sat 25 ms (unsat) | unsat 10 ms | sat 29 ms | unsat 12 ms |
| `20230720-blocksworld/blocksworld_from_16_4_2_to_16_3_3_negated_goal_bmc_5.smt2` | unsat | sat 686 ms (unsat) | unsat 594 ms | sat 693 ms | unsat 530 ms |
| `20230720-blocksworld/blocksworld_from_17_0_1_to_1_10_7_negated_goal_bmc_3.smt2` | unsat | sat 260 ms (unsat) | unsat 15 ms | sat 189 ms | unsat 14 ms |
| `20230720-blocksworld/blocksworld_from_17_2_1_to_19_1_0_negated_goal_bmc_1.smt2` | unsat | sat 32 ms (unsat) | unsat 6 ms | sat 21 ms | unsat 7 ms |
| `20230720-blocksworld/blocksworld_from_17_2_3_to_8_7_7_negated_goal_bmc_3.smt2` | unsat | sat 166 ms (unsat) | unsat 40 ms | sat 134 ms | unsat 47 ms |
| `20230720-blocksworld/blocksworld_from_18_0_3_to_4_13_4_negated_goal_bmc_3.smt2` | unsat | sat 169 ms (unsat) | unsat 27 ms | sat 143 ms | unsat 39 ms |
| `20230720-blocksworld/blocksworld_from_18_5_3_to_18_1_7_negated_goal_bmc_2.smt2` | unsat | sat 144 ms (unsat) | unsat 15 ms | sat 116 ms | unsat 16 ms |
| `20230720-blocksworld/blocksworld_from_1_0_2_to_1_0_2_negated_goal_bmc_1.smt2` | unsat | sat 12 ms (unsat) | unsat 5 ms | sat 12 ms | unsat 6 ms |
| `20230720-blocksworld/blocksworld_from_1_0_2_to_1_0_2_negated_goal_bmc_4.smt2` | unsat | sat 121 ms (unsat) | unsat 104 ms | sat 102 ms | unsat 102 ms |
| `20230720-blocksworld/blocksworld_from_1_14_5_to_17_3_0_negated_goal_bmc_4.smt2` | unsat | sat 437 ms (unsat) | unsat 77 ms | sat 501 ms | unsat 108 ms |
| `20230720-blocksworld/blocksworld_from_1_1_7_to_3_0_6_negated_goal_bmc_3.smt2` | unsat | sat 66 ms (unsat) | unsat 25 ms | sat 55 ms | unsat 26 ms |
| `20230720-blocksworld/blocksworld_from_1_1_7_to_3_0_6_negated_goal_bmc_6.smt2` | unsat | sat 536 ms (unsat) | unsat 4,746 ms | sat 489 ms | unsat 4,946 ms |
| `20230720-blocksworld/blocksworld_from_1_24_0_to_9_16_0_negated_goal_bmc_1.smt2` | unsat | sat 33 ms (unsat) | unsat 7 ms | sat 34 ms | unsat 7 ms |
| `20230720-blocksworld/blocksworld_from_1_2_10_to_13_0_0_negated_goal_bmc_3.smt2` | unsat | sat 81 ms (unsat) | unsat 13 ms | sat 84 ms | unsat 20 ms |
| `20230720-blocksworld/blocksworld_from_1_5_0_to_5_1_0_negated_goal_bmc_5.smt2` | unsat | sat 262 ms (unsat) | unsat 915 ms | sat 240 ms | unsat 890 ms |
| `20230720-blocksworld/blocksworld_from_1_5_5_to_1_1_9_negated_goal_bmc_4.smt2` | unsat | sat 175 ms (unsat) | unsat 385 ms | sat 135 ms | unsat 392 ms |
| `20230720-blocksworld/blocksworld_from_1_7_5_to_6_4_3_negated_goal_bmc_3.smt2` | unsat | sat 99 ms (unsat) | unsat 24 ms | sat 84 ms | unsat 31 ms |
| `20230720-blocksworld/blocksworld_from_20_2_0_to_8_7_7_negated_goal_bmc_6.smt2` | unsat | sat 886 ms (unsat) | unsat 1,374 ms | sat 727 ms | unsat 1,341 ms |
| `20230720-blocksworld/blocksworld_from_21_1_2_to_14_3_7_negated_goal_bmc_6.smt2` | unsat | sat 2,882 ms (unsat) | unsat 8,827 ms | sat 1,685 ms | unsat 9,169 ms |
| `20230720-blocksworld/blocksworld_from_23_1_0_to_8_9_7_negated_goal_bmc_5.smt2` | unsat | sat 1,092 ms (unsat) | unsat 431 ms | sat 963 ms | unsat 470 ms |
| `20230720-blocksworld/blocksworld_from_2_0_11_to_11_1_1_negated_goal_bmc_3.smt2` | unsat | sat 179 ms (unsat) | unsat 16 ms | sat 169 ms | unsat 19 ms |
| `20230720-blocksworld/blocksworld_from_2_0_5_to_2_1_4_negated_goal_bmc_2.smt2` | unsat | sat 37 ms (unsat) | unsat 9 ms | sat 25 ms | unsat 9 ms |
| `20230720-blocksworld/blocksworld_from_2_0_5_to_2_1_4_negated_goal_bmc_4.smt2` | unsat | sat 147 ms (unsat) | unsat 188 ms | sat 119 ms | unsat 223 ms |
| `20230720-blocksworld/blocksworld_from_2_12_9_to_0_10_13_negated_goal_bmc_4.smt2` | unsat | sat 250 ms (unsat) | unsat 142 ms | sat 230 ms | unsat 140 ms |
| `20230720-blocksworld/blocksworld_from_2_1_3_to_6_0_0_negated_goal_bmc_6.smt2` | unsat | sat 753 ms (unsat) | unsat 6,471 ms | sat 779 ms | unsat 6,576 ms |
| `20230720-blocksworld/blocksworld_from_2_5_13_to_12_7_1_negated_goal_bmc_1.smt2` | unsat | sat 21 ms (unsat) | unsat 7 ms | sat 19 ms | unsat 6 ms |
| `20230720-blocksworld/blocksworld_from_3_0_3_to_1_2_3_negated_goal_bmc_4.smt2` | unsat | sat 207 ms (unsat) | unsat 145 ms | sat 173 ms | unsat 139 ms |
| `20230720-blocksworld/blocksworld_from_3_1_20_to_23_0_1_negated_goal_bmc_6.smt2` | unsat | sat 554 ms (unsat) | unsat 959 ms | sat 564 ms | unsat 969 ms |
| `20230720-blocksworld/blocksworld_from_3_4_6_to_1_9_3_negated_goal_bmc_1.smt2` | unsat | sat 13 ms (unsat) | unsat 5 ms | sat 21 ms | unsat 8 ms |
| `20230720-blocksworld/blocksworld_from_3_5_0_to_8_0_0_negated_goal_bmc_6.smt2` | unsat | sat 694 ms (unsat) | unsat 737 ms | sat 562 ms | unsat 747 ms |
| `20230720-blocksworld/blocksworld_from_4_0_5_to_8_0_1_negated_goal_bmc_1.smt2` | unsat | sat 12 ms (unsat) | unsat 4 ms | sat 13 ms | unsat 7 ms |
| `20230720-blocksworld/blocksworld_from_4_10_4_to_15_0_3_negated_goal_bmc_6.smt2` | unsat | sat 639 ms (unsat) | unsat 556 ms | sat 569 ms | unsat 542 ms |
| `20230720-blocksworld/blocksworld_from_4_19_1_to_0_8_16_negated_goal_bmc_4.smt2` | unsat | sat 321 ms (unsat) | unsat 117 ms | sat 253 ms | unsat 114 ms |
| `20230720-blocksworld/blocksworld_from_4_19_1_to_0_8_16_negated_goal_bmc_6.smt2` | unsat | sat 1,586 ms (unsat) | unsat 2,612 ms | sat 1,101 ms | unsat 2,685 ms |
| `20230720-blocksworld/blocksworld_from_4_2_4_to_3_2_5_negated_goal_bmc_4.smt2` | unsat | sat 150 ms (unsat) | unsat 162 ms | sat 102 ms | unsat 163 ms |
| `20230720-blocksworld/blocksworld_from_4_3_0_to_5_1_1_negated_goal_bmc_3.smt2` | unsat | sat 66 ms (unsat) | unsat 24 ms | sat 70 ms | unsat 27 ms |
| `20230720-blocksworld/blocksworld_from_4_4_3_to_4_3_4_negated_goal_bmc_6.smt2` | unsat | sat 677 ms (unsat) | unsat 14,844 ms | sat 488 ms | unsat 15,105 ms |
| `20230720-blocksworld/blocksworld_from_5_0_1_to_1_1_4_negated_goal_bmc_5.smt2` | unsat | sat 184 ms (unsat) | unsat 381 ms | sat 190 ms | unsat 392 ms |
| `20230720-blocksworld/blocksworld_from_5_0_1_to_1_1_4_negated_goal_bmc_6.smt2` | unsat | sat 539 ms (unsat) | unsat 9,627 ms | sat 484 ms | unsat 9,764 ms |
| `20230720-blocksworld/blocksworld_from_5_0_8_to_7_5_1_negated_goal_bmc_5.smt2` | unsat | sat 1,565 ms (unsat) | unsat 570 ms | sat 1,427 ms | unsat 592 ms |
| `20230720-blocksworld/blocksworld_from_5_1_10_to_4_9_3_negated_goal_bmc_3.smt2` | unsat | sat 72 ms (unsat) | unsat 31 ms | sat 87 ms | unsat 39 ms |
| `20230720-blocksworld/blocksworld_from_5_21_0_to_20_6_0_negated_goal_bmc_1.smt2` | unsat | sat 25 ms (unsat) | unsat 9 ms | sat 26 ms | unsat 11 ms |
| `20230720-blocksworld/blocksworld_from_5_2_3_to_9_0_1_negated_goal_bmc_2.smt2` | unsat | sat 28 ms (unsat) | unsat 8 ms | sat 29 ms | unsat 9 ms |
| `20230720-blocksworld/blocksworld_from_5_4_17_to_12_6_8_negated_goal_bmc_2.smt2` | unsat | sat 84 ms (unsat) | unsat 15 ms | sat 79 ms | unsat 19 ms |
| `20230720-blocksworld/blocksworld_from_5_5_0_to_7_0_3_negated_goal_bmc_5.smt2` | unsat | sat 353 ms (unsat) | unsat 1,069 ms | sat 374 ms | unsat 824 ms |
| `20230720-blocksworld/blocksworld_from_5_7_12_to_9_3_12_negated_goal_bmc_1.smt2` | unsat | sat 27 ms (unsat) | unsat 11 ms | sat 27 ms | unsat 10 ms |
| `20230720-blocksworld/blocksworld_from_5_7_12_to_9_3_12_negated_goal_bmc_3.smt2` | unsat | sat 141 ms (unsat) | unsat 44 ms | sat 142 ms | unsat 38 ms |
| `20230720-blocksworld/blocksworld_from_5_9_3_to_13_1_3_negated_goal_bmc_1.smt2` | unsat | sat 19 ms (unsat) | unsat 9 ms | sat 20 ms | unsat 7 ms |
| `20230720-blocksworld/blocksworld_from_6_0_0_to_3_2_1_negated_goal_bmc_5.smt2` | unsat | sat 282 ms (unsat) | unsat 1,398 ms | sat 275 ms | unsat 896 ms |
| `20230720-blocksworld/blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2` | unsat | sat 30 ms (unsat) | unsat 16 ms | sat 33 ms | unsat 9 ms |
| `20230720-blocksworld/blocksworld_from_6_1_0_to_7_0_0_negated_goal_bmc_2.smt2` | unsat | sat 33 ms (unsat) | unsat 14 ms | sat 33 ms | unsat 10 ms |
| `20230720-blocksworld/blocksworld_from_6_1_11_to_6_0_12_negated_goal_bmc_1.smt2` | unsat | sat 28 ms (unsat) | unsat 11 ms | sat 26 ms | unsat 10 ms |
| `20230720-blocksworld/blocksworld_from_6_2_14_to_12_6_4_negated_goal_bmc_5.smt2` | unsat | sat 685 ms (unsat) | unsat 1,277 ms | sat 629 ms | unsat 704 ms |
| `20230720-blocksworld/blocksworld_from_6_9_0_to_14_0_1_negated_goal_bmc_4.smt2` | unsat | sat 325 ms (unsat) | unsat 115 ms | sat 326 ms | unsat 81 ms |
| `20230720-blocksworld/blocksworld_from_7_2_0_to_7_0_2_negated_goal_bmc_3.smt2` | unsat | sat 62 ms (unsat) | unsat 77 ms | sat 68 ms | unsat 24 ms |
| `20230720-blocksworld/blocksworld_from_7_3_12_to_12_0_10_negated_goal_bmc_5.smt2` | unsat | sat 570 ms (unsat) | unsat 2,884 ms | sat 550 ms | unsat 1,118 ms |
| `20230720-blocksworld/blocksworld_from_7_4_13_to_4_14_6_negated_goal_bmc_4.smt2` | unsat | sat 236 ms (unsat) | unsat 236 ms | sat 223 ms | unsat 147 ms |
| `20230720-blocksworld/blocksworld_from_8_10_1_to_5_9_5_negated_goal_bmc_2.smt2` | unsat | sat 78 ms (unsat) | unsat 17 ms | sat 78 ms | unsat 13 ms |
| `20230720-blocksworld/blocksworld_from_8_10_1_to_5_9_5_negated_goal_bmc_4.smt2` | unsat | sat 213 ms (unsat) | unsat 197 ms | sat 197 ms | unsat 140 ms |
| `20230720-blocksworld/blocksworld_from_8_1_2_to_6_2_3_negated_goal_bmc_2.smt2` | unsat | sat 40 ms (unsat) | unsat 16 ms | sat 42 ms | unsat 12 ms |
| `20230720-blocksworld/blocksworld_from_8_6_1_to_8_1_6_negated_goal_bmc_5.smt2` | unsat | sat 379 ms (unsat) | unsat 514 ms | sat 376 ms | unsat 347 ms |
| `20230720-blocksworld/blocksworld_from_8_8_1_to_9_4_4_negated_goal_bmc_2.smt2` | unsat | sat 63 ms (unsat) | unsat 26 ms | sat 61 ms | unsat 15 ms |
| `20230720-blocksworld/blocksworld_from_8_8_1_to_9_4_4_negated_goal_bmc_4.smt2` | unsat | sat 330 ms (unsat) | unsat 215 ms | sat 354 ms | unsat 163 ms |
| `20230720-blocksworld/blocksworld_from_8_8_1_to_9_4_4_negated_goal_bmc_6.smt2` | unsat | sat 2,063 ms (unsat) | unsat 8,159 ms | sat 1,981 ms | unsat 6,451 ms |
| `20230720-blocksworld/blocksworld_from_9_0_3_to_11_0_1_negated_goal_bmc_5.smt2` | unsat | sat 446 ms (unsat) | unsat 725 ms | sat 426 ms | unsat 562 ms |
| `20230720-blocksworld/blocksworld_from_9_4_4_to_14_1_2_negated_goal_bmc_3.smt2` | unsat | sat 86 ms (unsat) | unsat 40 ms | sat 86 ms | unsat 32 ms |
| `20230720-blocksworld/blocksworld_from_9_9_2_to_12_5_3_negated_goal_bmc_1.smt2` | unsat | sat 20 ms (unsat) | unsat 14 ms | sat 22 ms | unsat 8 ms |
| `20230720-blocksworld/blocksworld_from_9_9_2_to_12_5_3_negated_goal_bmc_4.smt2` | unsat | sat 186 ms (unsat) | unsat 182 ms | sat 179 ms | unsat 196 ms |
| `20230720-blocksworld/blocksworld_from_9_9_2_to_12_5_3_negated_goal_bmc_6.smt2` | unsat | sat 830 ms (unsat) | unsat 7,546 ms | sat 842 ms | unsat 7,380 ms |

### `wrong` → `timeout` (86)

| path (under `QF_DT/`) | `:status` | slice48b (z3) | slice49 | A/B base 20 s | A/B branch 20 s | branch 120 s |
| --- | --- | --- | --- | --- | --- | --- |
| `20230720-blocksworld/blocksworld_from_0_13_3_to_14_2_0_negated_goal_bmc_12.smt2` | unsat | sat 19,821 ms (timeout) | none 20,016 ms | sat 18,974 ms | none 20,017 ms | none 120,107 ms |
| `20230720-blocksworld/blocksworld_from_0_18_1_to_17_2_0_negated_goal_bmc_12.smt2` | unsat | sat 9,733 ms (timeout) | none 20,014 ms | sat 9,305 ms | none 20,017 ms | none 120,087 ms |
| `20230720-blocksworld/blocksworld_from_0_1_15_to_13_1_2_negated_goal_bmc_13.smt2` | unsat | sat 2,329 ms (timeout) | none 20,018 ms | sat 2,433 ms | none 20,015 ms | none 120,091 ms |
| `20230720-blocksworld/blocksworld_from_0_1_19_to_6_3_11_negated_goal_bmc_11.smt2` | unsat | sat 2,795 ms (timeout) | none 20,014 ms | sat 2,256 ms | none 20,017 ms | none 120,081 ms |
| `20230720-blocksworld/blocksworld_from_0_1_19_to_6_3_11_negated_goal_bmc_9.smt2` | unsat | sat 1,981 ms (unsat) | none 20,013 ms | sat 2,028 ms | none 20,016 ms | none 120,065 ms |
| `20230720-blocksworld/blocksworld_from_0_3_6_to_2_0_7_negated_goal_bmc_14.smt2` | unsat | sat 15,110 ms (timeout) | none 20,018 ms | sat 15,681 ms | none 20,026 ms | none 120,095 ms |
| `20230720-blocksworld/blocksworld_from_0_3_6_to_2_0_7_negated_goal_bmc_9.smt2` | unsat | sat 2,198 ms (unsat) | none 20,016 ms | sat 2,293 ms | none 20,019 ms | none 120,059 ms |
| `20230720-blocksworld/blocksworld_from_0_4_7_to_4_4_3_negated_goal_bmc_13.smt2` | unsat | sat 6,675 ms (timeout) | none 20,015 ms | sat 6,633 ms | none 20,017 ms | none 120,084 ms |
| `20230720-blocksworld/blocksworld_from_0_6_0_to_5_0_1_negated_goal_bmc_9.smt2` | unsat | sat 2,213 ms (unsat) | none 20,016 ms | sat 2,379 ms | none 20,015 ms | none 120,072 ms |
| `20230720-blocksworld/blocksworld_from_0_7_3_to_8_1_1_negated_goal_bmc_11.smt2` | unsat | sat 3,178 ms (unsat) | none 20,016 ms | sat 3,297 ms | none 20,017 ms | none 120,079 ms |
| `20230720-blocksworld/blocksworld_from_0_7_3_to_8_1_1_negated_goal_bmc_8.smt2` | unsat | sat 1,266 ms (unsat) | none 20,016 ms | sat 1,312 ms | none 20,020 ms | none 120,070 ms |
| `20230720-blocksworld/blocksworld_from_0_7_3_to_8_1_1_negated_goal_bmc_9.smt2` | unsat | sat 2,991 ms (unsat) | none 20,017 ms | sat 3,376 ms | none 20,016 ms | none 120,064 ms |
| `20230720-blocksworld/blocksworld_from_0_9_0_to_1_6_2_negated_goal_bmc_8.smt2` | unsat | sat 2,441 ms (unsat) | none 20,010 ms | sat 2,459 ms | none 20,010 ms | none 120,037 ms |
| `20230720-blocksworld/blocksworld_from_10_4_3_to_1_14_2_negated_goal_bmc_10.smt2` | unsat | sat 16,338 ms (unsat) | none 20,016 ms | sat 16,532 ms | none 20,017 ms | none 120,071 ms |
| `20230720-blocksworld/blocksworld_from_10_5_6_to_13_6_2_negated_goal_bmc_11.smt2` | unsat | sat 5,085 ms (timeout) | none 20,016 ms | sat 5,020 ms | none 20,017 ms | none 120,073 ms |
| `20230720-blocksworld/blocksworld_from_10_5_6_to_13_6_2_negated_goal_bmc_9.smt2` | unsat | sat 10,117 ms (unsat) | none 20,012 ms | sat 9,268 ms | none 20,012 ms | none 120,043 ms |
| `20230720-blocksworld/blocksworld_from_11_0_10_to_18_1_2_negated_goal_bmc_9.smt2` | unsat | sat 5,592 ms (unsat) | none 20,014 ms | sat 4,842 ms | none 20,015 ms | none 120,050 ms |
| `20230720-blocksworld/blocksworld_from_12_0_7_to_18_0_1_negated_goal_bmc_7.smt2` | unsat | sat 5,042 ms (unsat) | none 20,009 ms | sat 4,997 ms | none 20,012 ms | unsat 40,270 ms |
| `20230720-blocksworld/blocksworld_from_12_1_0_to_1_12_0_negated_goal_bmc_10.smt2` | unsat | sat 4,367 ms (unsat) | none 20,023 ms | sat 4,369 ms | none 20,016 ms | none 120,051 ms |
| `20230720-blocksworld/blocksworld_from_12_2_0_to_5_0_9_negated_goal_bmc_14.smt2` | unsat | sat 16,598 ms (timeout) | none 20,013 ms | sat 17,121 ms | none 20,017 ms | none 120,068 ms |
| `20230720-blocksworld/blocksworld_from_12_7_0_to_14_5_0_negated_goal_bmc_7.smt2` | unsat | sat 2,328 ms (unsat) | none 20,016 ms | sat 2,450 ms | none 20,011 ms | unsat 98,858 ms |
| `20230720-blocksworld/blocksworld_from_13_1_5_to_8_4_7_negated_goal_bmc_9.smt2` | unsat | sat 8,506 ms (unsat) | none 20,015 ms | sat 8,539 ms | none 20,016 ms | none 120,038 ms |
| `20230720-blocksworld/blocksworld_from_13_3_3_to_3_11_5_negated_goal_bmc_14.smt2` | unsat | sat 12,685 ms (timeout) | none 20,027 ms | sat 13,280 ms | none 20,017 ms | none 120,068 ms |
| `20230720-blocksworld/blocksworld_from_14_0_3_to_12_4_1_negated_goal_bmc_7.smt2` | unsat | sat 1,703 ms (unsat) | none 20,021 ms | sat 1,631 ms | none 20,013 ms | none 120,035 ms |
| `20230720-blocksworld/blocksworld_from_14_0_3_to_12_4_1_negated_goal_bmc_8.smt2` | unsat | sat 1,778 ms (unsat) | none 20,022 ms | sat 1,719 ms | none 20,017 ms | none 120,047 ms |
| `20230720-blocksworld/blocksworld_from_14_1_0_to_5_1_9_negated_goal_bmc_8.smt2` | unsat | sat 1,511 ms (unsat) | none 20,099 ms | sat 1,621 ms | none 20,013 ms | none 120,036 ms |
| `20230720-blocksworld/blocksworld_from_15_6_4_to_10_2_13_negated_goal_bmc_7.smt2` | unsat | sat 5,814 ms (unsat) | none 20,014 ms | sat 5,984 ms | none 20,012 ms | none 120,019 ms |
| `20230720-blocksworld/blocksworld_from_16_4_2_to_16_3_3_negated_goal_bmc_8.smt2` | unsat | sat 1,298 ms (unsat) | none 20,012 ms | sat 1,264 ms | none 20,011 ms | none 120,029 ms |
| `20230720-blocksworld/blocksworld_from_18_1_7_to_7_17_2_negated_goal_bmc_7.smt2` | unsat | sat 3,342 ms (unsat) | none 20,008 ms | sat 2,752 ms | none 20,009 ms | unsat 51,868 ms |
| `20230720-blocksworld/blocksworld_from_18_5_3_to_18_1_7_negated_goal_bmc_15.smt2` | unsat | sat 15,202 ms (timeout) | none 20,014 ms | sat 14,695 ms | none 20,020 ms | none 120,057 ms |
| `20230720-blocksworld/blocksworld_from_1_14_5_to_17_3_0_negated_goal_bmc_10.smt2` | unsat | sat 5,040 ms (timeout) | none 20,014 ms | sat 4,841 ms | none 20,022 ms | none 120,061 ms |
| `20230720-blocksworld/blocksworld_from_1_21_4_to_17_7_2_negated_goal_bmc_10.smt2` | unsat | sat 7,180 ms (unsat) | none 20,015 ms | sat 6,625 ms | none 20,014 ms | none 120,060 ms |
| `20230720-blocksworld/blocksworld_from_1_2_10_to_13_0_0_negated_goal_bmc_12.smt2` | unsat | sat 6,595 ms (timeout) | none 20,017 ms | sat 6,226 ms | none 20,019 ms | none 120,048 ms |
| `20230720-blocksworld/blocksworld_from_1_2_10_to_13_0_0_negated_goal_bmc_9.smt2` | unsat | sat 2,642 ms (unsat) | none 20,018 ms | sat 2,402 ms | none 20,017 ms | none 120,047 ms |
| `20230720-blocksworld/blocksworld_from_1_6_3_to_9_0_1_negated_goal_bmc_12.smt2` | unsat | sat 7,156 ms (unsat) | none 20,020 ms | sat 6,740 ms | none 20,019 ms | none 120,060 ms |
| `20230720-blocksworld/blocksworld_from_1_9_5_to_13_2_0_negated_goal_bmc_11.smt2` | unsat | sat 6,377 ms (timeout) | none 20,014 ms | sat 5,828 ms | none 20,014 ms | none 120,055 ms |
| `20230720-blocksworld/blocksworld_from_20_0_0_to_17_2_1_negated_goal_bmc_10.smt2` | unsat | sat 3,790 ms (unsat) | none 20,014 ms | sat 3,502 ms | none 20,012 ms | none 120,048 ms |
| `20230720-blocksworld/blocksworld_from_20_4_0_to_22_1_1_negated_goal_bmc_14.smt2` | unsat | sat 18,014 ms (timeout) | none 20,022 ms | sat 17,151 ms | none 20,018 ms | none 120,070 ms |
| `20230720-blocksworld/blocksworld_from_21_0_4_to_10_10_5_negated_goal_bmc_9.smt2` | unsat | sat 6,640 ms (unsat) | none 20,012 ms | sat 6,308 ms | none 20,013 ms | none 120,031 ms |
| `20230720-blocksworld/blocksworld_from_21_1_2_to_14_3_7_negated_goal_bmc_7.smt2` | unsat | sat 3,258 ms (unsat) | none 20,011 ms | sat 1,982 ms | none 20,011 ms | none 120,026 ms |
| `20230720-blocksworld/blocksworld_from_21_4_1_to_0_23_3_negated_goal_bmc_7.smt2` | unsat | sat 3,135 ms (unsat) | none 20,011 ms | sat 2,597 ms | none 20,012 ms | none 120,036 ms |
| `20230720-blocksworld/blocksworld_from_22_0_2_to_9_12_3_negated_goal_bmc_7.smt2` | unsat | sat 1,949 ms (unsat) | none 20,010 ms | sat 1,833 ms | none 20,011 ms | none 120,016 ms |
| `20230720-blocksworld/blocksworld_from_2_0_19_to_2_8_11_negated_goal_bmc_11.smt2` | unsat | sat 13,839 ms (timeout) | none 20,014 ms | sat 9,912 ms | none 20,013 ms | none 120,059 ms |
| `20230720-blocksworld/blocksworld_from_2_12_9_to_0_10_13_negated_goal_bmc_15.smt2` | unsat | sat 16,478 ms (timeout) | none 20,018 ms | sat 14,971 ms | none 20,024 ms | none 120,082 ms |
| `20230720-blocksworld/blocksworld_from_2_1_11_to_9_3_2_negated_goal_bmc_7.smt2` | unsat | sat 2,027 ms (unsat) | none 20,013 ms | sat 1,839 ms | none 20,012 ms | none 120,024 ms |
| `20230720-blocksworld/blocksworld_from_2_1_9_to_0_9_3_negated_goal_bmc_9.smt2` | unsat | sat 2,962 ms (unsat) | none 20,014 ms | sat 2,733 ms | none 20,016 ms | none 120,059 ms |
| `20230720-blocksworld/blocksworld_from_2_4_0_to_0_3_3_negated_goal_bmc_7.smt2` | unsat | sat 721 ms (unsat) | none 20,012 ms | sat 670 ms | none 20,017 ms | unsat 59,804 ms |
| `20230720-blocksworld/blocksworld_from_2_6_2_to_3_4_3_negated_goal_bmc_10.smt2` | unsat | sat 4,476 ms (unsat) | none 20,014 ms | sat 3,755 ms | none 20,017 ms | none 120,053 ms |
| `20230720-blocksworld/blocksworld_from_2_6_2_to_3_4_3_negated_goal_bmc_7.smt2` | unsat | sat 793 ms (unsat) | none 20,014 ms | sat 628 ms | none 20,015 ms | unsat 75,613 ms |
| `20230720-blocksworld/blocksworld_from_3_1_18_to_3_16_3_negated_goal_bmc_8.smt2` | unsat | sat 847 ms (unsat) | none 20,013 ms | sat 821 ms | none 20,015 ms | none 120,053 ms |
| `20230720-blocksworld/blocksworld_from_3_5_10_to_17_0_1_negated_goal_bmc_8.smt2` | unsat | sat 2,983 ms (unsat) | none 20,012 ms | sat 2,821 ms | none 20,014 ms | none 120,035 ms |
| `20230720-blocksworld/blocksworld_from_4_0_5_to_8_0_1_negated_goal_bmc_13.smt2` | unsat | sat 2,911 ms (timeout) | none 20,016 ms | sat 2,571 ms | none 20,029 ms | none 120,055 ms |
| `20230720-blocksworld/blocksworld_from_4_0_5_to_8_0_1_negated_goal_bmc_8.smt2` | unsat | sat 1,710 ms (unsat) | none 20,015 ms | sat 1,661 ms | none 20,014 ms | none 120,028 ms |
| `20230720-blocksworld/blocksworld_from_4_1_4_to_1_0_8_negated_goal_bmc_11.smt2` | unsat | sat 7,631 ms (timeout) | none 20,015 ms | sat 6,610 ms | none 20,017 ms | none 120,052 ms |
| `20230720-blocksworld/blocksworld_from_5_0_0_to_5_0_0_negated_goal_bmc_8.smt2` | unsat | sat 245 ms (unsat) | none 20,013 ms | sat 222 ms | none 20,013 ms | unsat 48,675 ms |
| `20230720-blocksworld/blocksworld_from_5_0_8_to_7_5_1_negated_goal_bmc_12.smt2` | unsat | sat 9,858 ms (unsat) | none 20,017 ms | sat 9,052 ms | none 20,017 ms | none 120,072 ms |
| `20230720-blocksworld/blocksworld_from_5_1_10_to_4_9_3_negated_goal_bmc_8.smt2` | unsat | sat 723 ms (unsat) | none 20,011 ms | sat 709 ms | none 20,012 ms | none 120,027 ms |
| `20230720-blocksworld/blocksworld_from_5_1_2_to_3_3_2_negated_goal_bmc_12.smt2` | unsat | sat 7,073 ms (timeout) | none 20,017 ms | sat 6,819 ms | none 20,017 ms | none 120,055 ms |
| `20230720-blocksworld/blocksworld_from_5_21_0_to_20_6_0_negated_goal_bmc_8.smt2` | unsat | sat 2,428 ms (unsat) | none 20,012 ms | sat 2,274 ms | none 20,014 ms | none 120,030 ms |
| `20230720-blocksworld/blocksworld_from_5_21_0_to_20_6_0_negated_goal_bmc_9.smt2` | unsat | sat 4,693 ms (unsat) | none 20,014 ms | sat 4,565 ms | none 20,019 ms | none 120,033 ms |
| `20230720-blocksworld/blocksworld_from_5_2_3_to_9_0_1_negated_goal_bmc_10.smt2` | unsat | sat 2,648 ms (timeout) | none 20,014 ms | sat 2,579 ms | none 20,015 ms | none 120,042 ms |
| `20230720-blocksworld/blocksworld_from_5_3_8_to_14_1_1_negated_goal_bmc_10.smt2` | unsat | sat 4,509 ms (unsat) | none 20,014 ms | sat 4,417 ms | none 20,016 ms | none 120,044 ms |
| `20230720-blocksworld/blocksworld_from_5_4_17_to_12_6_8_negated_goal_bmc_13.smt2` | unsat | sat 18,865 ms (timeout) | none 20,015 ms | sat 18,310 ms | none 20,020 ms | none 120,053 ms |
| `20230720-blocksworld/blocksworld_from_5_4_17_to_12_6_8_negated_goal_bmc_16.smt2` | unsat | sat 7,079 ms (timeout) | none 20,030 ms | sat 6,980 ms | none 20,019 ms | none 120,063 ms |
| `20230720-blocksworld/blocksworld_from_5_5_0_to_10_0_0_negated_goal_bmc_13.smt2` | unsat | sat 4,948 ms (timeout) | none 20,033 ms | sat 4,961 ms | none 20,016 ms | none 120,065 ms |
| `20230720-blocksworld/blocksworld_from_5_8_2_to_8_0_7_negated_goal_bmc_12.smt2` | unsat | sat 3,919 ms (unsat) | none 20,019 ms | sat 3,706 ms | none 20,018 ms | none 120,068 ms |
| `20230720-blocksworld/blocksworld_from_5_9_3_to_13_1_3_negated_goal_bmc_8.smt2` | unsat | sat 8,390 ms (unsat) | none 20,011 ms | sat 7,861 ms | none 20,014 ms | none 120,047 ms |
| `20230720-blocksworld/blocksworld_from_6_1_11_to_6_0_12_negated_goal_bmc_10.smt2` | unsat | sat 2,429 ms (timeout) | none 20,017 ms | sat 2,373 ms | none 20,014 ms | none 120,055 ms |
| `20230720-blocksworld/blocksworld_from_6_1_1_to_1_5_2_negated_goal_bmc_9.smt2` | unsat | sat 4,900 ms (unsat) | none 20,021 ms | sat 4,490 ms | none 20,015 ms | none 120,043 ms |
| `20230720-blocksworld/blocksworld_from_6_1_1_to_4_2_2_negated_goal_bmc_7.smt2` | unsat | sat 899 ms (unsat) | none 20,032 ms | sat 709 ms | none 20,014 ms | none 120,035 ms |
| `20230720-blocksworld/blocksworld_from_6_20_0_to_1_12_13_negated_goal_bmc_11.smt2` | unsat | sat 14,233 ms (unsat) | none 20,019 ms | sat 13,405 ms | none 20,017 ms | none 120,048 ms |
| `20230720-blocksworld/blocksworld_from_6_20_0_to_1_12_13_negated_goal_bmc_12.smt2` | unsat | sat 14,994 ms (unsat) | none 20,029 ms | sat 14,048 ms | none 20,017 ms | none 120,061 ms |
| `20230720-blocksworld/blocksworld_from_6_2_1_to_9_0_0_negated_goal_bmc_8.smt2` | unsat | sat 1,044 ms (unsat) | none 20,015 ms | sat 1,040 ms | none 20,012 ms | none 120,029 ms |
| `20230720-blocksworld/blocksworld_from_6_9_0_to_14_0_1_negated_goal_bmc_7.smt2` | unsat | sat 1,728 ms (unsat) | none 20,011 ms | sat 1,658 ms | unsat 17,911 ms | unsat 17,985 ms |
| `20230720-blocksworld/blocksworld_from_7_1_1_to_8_1_0_negated_goal_bmc_14.smt2` | unsat | sat 1,516 ms (timeout) | none 20,035 ms | sat 1,463 ms | none 20,018 ms | none 120,059 ms |
| `20230720-blocksworld/blocksworld_from_7_3_12_to_12_0_10_negated_goal_bmc_7.smt2` | unsat | sat 3,789 ms (unsat) | none 20,013 ms | sat 3,698 ms | none 20,009 ms | unsat 21,826 ms |
| `20230720-blocksworld/blocksworld_from_7_3_12_to_12_0_10_negated_goal_bmc_8.smt2` | unsat | sat 2,841 ms (unsat) | none 20,011 ms | sat 2,754 ms | none 20,015 ms | none 120,025 ms |
| `20230720-blocksworld/blocksworld_from_7_3_12_to_12_0_10_negated_goal_bmc_9.smt2` | unsat | sat 3,407 ms (unsat) | none 20,031 ms | sat 3,308 ms | none 20,013 ms | none 120,038 ms |
| `20230720-blocksworld/blocksworld_from_7_3_1_to_5_6_0_negated_goal_bmc_11.smt2` | unsat | sat 2,880 ms (timeout) | none 20,016 ms | sat 2,829 ms | none 20,018 ms | none 120,058 ms |
| `20230720-blocksworld/blocksworld_from_7_3_1_to_5_6_0_negated_goal_bmc_13.smt2` | unsat | sat 17,688 ms (timeout) | none 20,032 ms | sat 17,115 ms | none 20,017 ms | none 120,062 ms |
| `20230720-blocksworld/blocksworld_from_7_3_1_to_5_6_0_negated_goal_bmc_9.smt2` | unsat | sat 1,693 ms (unsat) | none 20,021 ms | sat 1,639 ms | none 20,014 ms | none 120,050 ms |
| `20230720-blocksworld/blocksworld_from_7_4_13_to_4_14_6_negated_goal_bmc_8.smt2` | unsat | sat 4,235 ms (unsat) | none 20,012 ms | sat 4,185 ms | none 20,011 ms | none 120,023 ms |
| `20230720-blocksworld/blocksworld_from_8_2_1_to_10_1_0_negated_goal_bmc_11.smt2` | unsat | sat 4,361 ms (timeout) | none 20,027 ms | sat 4,243 ms | none 20,016 ms | none 120,051 ms |
| `20230720-blocksworld/blocksworld_from_8_2_1_to_10_1_0_negated_goal_bmc_8.smt2` | unsat | sat 1,960 ms (unsat) | none 20,029 ms | sat 1,904 ms | none 20,016 ms | none 120,031 ms |
| `20230720-blocksworld/blocksworld_from_9_4_1_to_0_13_1_negated_goal_bmc_11.smt2` | unsat | sat 14,894 ms (unsat) | none 20,014 ms | sat 14,125 ms | none 20,016 ms | none 120,056 ms |
| `20230720-blocksworld/blocksworld_from_9_7_0_to_9_6_1_negated_goal_bmc_9.smt2` | unsat | sat 2,902 ms (unsat) | none 20,012 ms | sat 2,884 ms | none 20,013 ms | none 120,038 ms |

### `timeout` → `correct` (13)

| path (under `QF_DT/`) | `:status` | slice48b (z3) | slice49 | A/B base 20 s | A/B branch 20 s |
| --- | --- | --- | --- | --- | --- |
| `20172804-Barrett/barrett-jsat/tests/v1/v1l60099.cvc.smt2` | sat | none 20,006 ms (-) | sat 7 ms | none 20,005 ms | sat 10 ms |
| `20172804-Barrett/barrett-jsat/tests/v5/v5l80086.cvc.smt2` | sat | none 20,015 ms (-) | sat 5 ms | none 20,005 ms | sat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l20084.cvc.smt2` | unsat | none 20,005 ms (-) | unsat 4 ms | none 20,006 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v1/typed_v1l30088.cvc.smt2` | unsat | none 20,008 ms (-) | unsat 4 ms | none 20,005 ms | unsat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v10/typed_v10l50025.cvc.smt2` | sat | none 20,004 ms (-) | sat 5 ms | none 20,005 ms | sat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v10/typed_v10l70069.cvc.smt2` | sat | none 20,004 ms (-) | sat 5 ms | none 20,004 ms | sat 7 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l30029.cvc.smt2` | sat | none 20,004 ms (-) | sat 4 ms | none 20,005 ms | sat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v2/typed_v2l60068.cvc.smt2` | sat | none 20,005 ms (-) | sat 5 ms | none 20,004 ms | sat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v3/typed_v3l20091.cvc.smt2` | unsat | none 20,004 ms (-) | unsat 4 ms | none 20,005 ms | unsat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v3/typed_v3l60096.cvc.smt2` | sat | none 20,004 ms (-) | sat 5 ms | none 20,005 ms | sat 6 ms |
| `20172804-Barrett/barrett-jsat/typed/v5/typed_v5l40035.cvc.smt2` | sat | none 20,003 ms (-) | sat 4 ms | none 20,007 ms | sat 5 ms |
| `20172804-Barrett/barrett-jsat/typed/v5/typed_v5l60030.cvc.smt2` | sat | none 20,005 ms (-) | sat 5 ms | none 20,008 ms | sat 8 ms |
| `20172804-Barrett/barrett-jsat/typed/v5/typed_v5l70010.cvc.smt2` | sat | none 20,004 ms (-) | sat 5 ms | none 20,005 ms | sat 6 ms |

### `unverified` → `timeout` (1)

| path (under `QF_DT/`) | `:status` | slice48b (z3) | slice49 | A/B base 20 s | A/B branch 20 s | branch 120 s |
| --- | --- | --- | --- | --- | --- | --- |
| `20230720-blocksworld/blocksworld_from_5_0_5_to_5_3_2_negated_goal_bmc_17.smt2` | unknown | sat 13,144 ms (timeout) | none 20,014 ms | sat 11,667 ms | none 20,020 ms | none 120,063 ms |

