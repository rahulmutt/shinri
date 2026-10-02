# SMT-LIB 2024 re-run — slice 54 (compound Bool arguments purified into `bool!` proxies) — shinri @ 6212fa5fcf84

**Measured outcome: no row moved into `wrong`, and every logic's net
`correct` is ≥ 0.** The run `slice54` (slice head `6212fa5`) is compared
with `slice54-base` (the `61be117` sources) over QF_UF, QF_DT, QF_UFLIA and
QF_UFLRA (18,146 instances). The corpus has no `wrong` row in either run, so
the bench cannot show the fix itself: the defect is caught by the probes and
the oracle (below). On the bench, the slice is neutral. Only **5 corpus files
mint a proxy at all** (all QF_UF CLEARSY, all `correct` in both runs). None of
the 189 changed rows can mint one, so every changed row is noise by
construction, and the triage re-runs confirm it.

```
# base, leg 1 (Task 1; frozen binary copy)
taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_UF,QF_DT,QF_UFLIA,QF_UFLRA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice54-base/shinri --run-id slice54-base
# base, leg 2 (the 1,411 files leg 1 did not reach, copied to a corpus dir;
# detached with setsid; the command line is reconstructed from the fixture
# line, which records the solver, limits and corpus)
taskset -c 12-23 target/release/shinri-bench run \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice54-base/shinri --corpus target/slice54-base/rest-corpus \
  --run-id slice54-base-rest

# after (Task 4)
cargo build --release -p shinri-cli -p shinri-bench
md5sum target/release/shinri   # 579f17b300bff4feec82b11bc8371fd3 = fixture solver_md5
BENCH_LOGICS=QF_UF,QF_DT,QF_UFLIA,QF_UFLRA BENCH_RUN_ID=slice54 \
  taskset -c 12-23 mise run bench-run
BENCH_RUN_ID=slice54 mise run bench-report
```

All runs used the default limits: 20 s, 3072 MB, 6 jobs, cgroup `cpu.max`
`800000 100000`, `memory.max` 34359738368, pinned with `taskset -c 12-23`
(fixture lines of the three `results.jsonl` files).

| run | solver | `solver_md5` | started | finished | wall-clock | rows |
| --- | --- | --- | --- | --- | --- | ---: |
| `slice54` (after) | `target/slice54-after/shinri` (= `target/release/shinri` @ `6212fa5`) | `579f17b300bff4feec82b11bc8371fd3` | 2026-10-02T14:10:43Z | 16:09:30Z | ~1 h 59 min | 18,146 |
| `slice54-base` (leg 1) | `target/slice54-base/shinri` (built from the `61be117` sources) | `84a83b41d8718df3cb0905a03b1980d6` | 2026-10-02T11:32:49Z | 13:33:02Z (killed) | ~2 h 00 min | 16,735 |
| `slice54-base-rest` (leg 2) | same binary | `84a83b41d8718df3cb0905a03b1980d6` | 2026-10-02T13:33:24Z | 13:41:30Z | ~8 min | 1,411 |

Sources: `target/slice54-{base,after}/md5.txt`, `started.txt`,
`finished.txt`, `rest.done`, `done`, and the fixture lines.

**Fixture sha.** The harness records the checkout HEAD, not the binary's
commit. `slice54` says `6212fa5fcf84`, which is also the binary's commit.
`slice54-base` says `b59f115979ab` (the toolchain commit checked out when leg 1
started), and `slice54-base-rest` says `6212fa5fcf84` (the checkout when leg 2
started). Both legs ran the same frozen binary, md5 `84a83b41…`, built at
`b59f115` with Rust 1.99.0 (the same toolchain as the after binary).
`git diff --stat 61be117 b59f115 -- crates` is empty (docs and `mise.toml`
only), so the base binary is the `61be117` solver.

**Base run in two legs (deviation).** Leg 1 was started with the Bash tool's
`run_in_background`, as the plan said, and the tool's 2 h limit killed it
after 16,735 of 18,146 rows (all of QF_DT and QF_UF, and 532 of 659
QF_UFLIA). A resume under the same run-id was refused, because the fixture
header records the checkout sha and HEAD had moved from `b59f115` to
`6212fa5` (`run.log`: "results file was produced by a different fixture").
The 1,411 missing files (127 QF_UFLIA, all 1,284 QF_UFLRA) were copied to
`target/slice54-base/rest-corpus` and run as leg 2, detached, with the same
binary and limits. **The base matrix below combines both legs**: the two
`results.jsonl` files (fixture line of leg 1, then every row of both) were
concatenated in a scratch directory and rendered with
`target/release/shinri-bench report`. The two key sets are disjoint and their
union equals the after-run's.

**Load disclosure.** The after-run ran with nothing else on the machine (the
gates finished at 14:10:30, before it started). Leg 1 of the base run did
not: Tasks 2 and 3 (oracle before/after, probes, unit tests, and Task 3's
`mise run test`, which finished at 11:51:34) ran on cores 0–11 from about
11:33 to 11:52. By the harness's own wall times (cumulative `wall_ms` / 6
jobs), that window covers only QF_DT rows; QF_UF starts about 33 min in, the QG-classification family about 39 min in. The
QF_DT bench median, 28 ms in base and 6 ms after, is consistent with that load (see
*Timing*). Leg 2 ran after the Task 3 work and before the gates (lint's log
is stamped 13:42:01, after leg 2's 13:41:30 finish).

**How the transitions were computed.** A scratch script (not committed;
`transitions.py` in the SDD folder) loads both base legs and the after
`results.jsonl`, keyed by `path`, and asserts identical key sets
(**18,146 common paths, 0 missing, 0 extra**). It tallies
`(logic, before, after)` with per-family counts, prints `ESCALATE` for any
row that moves into `wrong` and `LOSS` for any `correct → unknown*/timeout`
row. **It printed no `ESCALATE` and 4 `LOSS` lines.** The per-logic counts
close under `new = old − outbound + inbound` (below).

## Headline

- **0 rows `* → wrong`** in all 4 logics; no `ESCALATE`. Neither run has a
  `wrong` or `status-suspect` row, so there was no base `wrong` row to fix
  (Task 1 Step 6: none).
- **The fix is shown by the tests, not the bench.** `slice54_probes`: 5/23
  pass at HEAD (`bc6d152`), 23/23 after. `bool_arg_oracle`: 29 (QF_DT), 20
  (QF_UFLIA) and 12 (QF_UFLRA) disagreements with z3 at HEAD, 0/0/0 after.
- **Raw `correct` +178** (15,152 → 15,330): QF_DT +1, QF_UF +171,
  QF_UFLIA +6, QF_UFLRA 0.
- **Credited gain: 0.** Only 5 files in the four logics can mint a proxy
  (parse-level scan, *Proxy minting*), all in QF_UF CLEARSY, all `correct`
  in both runs. **No changed row is one of them**, so on every changed row
  the solver's encoding is unchanged (spec §3.3: formulas without the shape
  mint nothing and keep their `TermId`s). The re-runs (216, both binaries
  interleaved) show the +178 is base-run timing noise at the 20 s edge,
  mostly in the QG-classification family.
- **4 `correct → timeout` rows** (QF_UF QG-classification), all triaged as
  noise.
- Timing (criterion 7): neutral. On a paired, interleaved sample the median
  per-row after/base ratio is 0.92 (QF_DT, ~20 ms rows), 0.99 (QF_UF,
  QF_UFLIA) and 1.00 (QF_UFLRA). The bench-level QF_DT median drop
  (28 → 6 ms) is consistent with base-run load.

## What changed versus the spec

1. **The oracle is three tests in `tests/bool_arg_oracle.rs`** (one per
   family: QF_DT, QF_UFLIA, QF_UFLRA), not one `differential_bool_arg`
   (spec §6.3). The generator was used as written; it needed no
   strengthening, since it found 29/20/12 disagreements at HEAD.
2. **`get-value` on a term with a purified argument now prints `?`**
   (contradicts spec §4, "`get-value` output is unchanged"). For
   `(P (= x 1))`, `(not (P true))`, `(= x 2)`, the query
   `(get-value ((P (= x 1)) (= x 1) (P false)))` gave
   `(((P t4) true) (t4 @elem0) ((P t1) ?))` at HEAD and gives
   `(((P t4) ?) (t4 ?) ((P t1) ?))` now. The assertion is rewritten to
   `(P bool!n)`, and `lib.rs` has no remap for it like the one for eliminated
   ites (`ite_map` / `orig_ite_map` → `eliminated_ite_vals`). The fix needs a
   `lib.rs` change, which is outside this slice's file scope, so it is
   queued. No verdict changes; `?` is the existing fallback for a term the
   model cannot evaluate. (The `t4` internal-name echo is the carried
   slice-50 item.)
3. **The base run is two legs** (above).
4. **`string_path_bool_arg_is_not_sat` is `unsat`**, not `unknown` (both
   were allowed). The `(= s "ab")` sibling is `sat`.
5. **QF_DT has no Bool constructor field in the local corpus** (spec §7
   expected QF_DT could carry the shape). The bench therefore exercises the
   DT path only as a control; the DT fix is covered by the probes and the
   QF_DT oracle family.

## Success criteria (spec §7)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | r1–r5, r7, s5 `unsat`; every `sat` sibling stays `sat` | **PASS** | `slice54_probes` 23/23 after (`target/slice54-probes-after.log`); at HEAD `bc6d152` 5 passed / 18 failed, the 18 being wrong `sat`s and the post-mint length check (`target/slice54-probes-before.log`); r6 pinned `unsat` both ways |
| 2 | oracle: disagreements > 0 at HEAD, 0 after; discovered > 0; existing oracle families 0 | **PASS** | `bool_arg_oracle` 3 discovered; before 29 / 20 / 12, after 0 / 0 / 0; `differential_qf_uflia_compound_args` + `qfdt_oracle` 19/19; full oracle suite 749 run, 749 passed, 3 skipped (`target/slice54-oracle.log`) |
| 3 | 0 rows `* → wrong` in the four benched logics | **PASS: 0** | no `ESCALATE`; 0 `wrong` rows in either run; 0 wrong answers in 934 re-runs (triage 216, minting rows 30, timing sample 688) |
| 4 | every `correct → unknown/timeout` row triaged; net `correct` ≥ 0 per logic | **PASS** | 4 rows (QF_UF QG-classification), all noise; raw net QF_DT +1, QF_UF +171, QF_UFLIA +6, QF_UFLRA 0; credited net 0 in every logic |
| 5 | fence pins hold (s3, s4, s6 `unknown`); no `bool!` in `get-model` | **PASS** | `fence_pin_bool_array_select_stays_unknown`, `fence_pin_bool_array_store_stays_unknown`, `fence_pin_ufbv_bool_argument_stays_unknown`, `get_model_has_no_proxy_symbols` pass before and after |
| 6 | `mise run lint`, `mise run test`, `ci` green | **PASS (locally; PR CI pending)** | lint clean; test 1,652 passed / 7 skipped; deny and secrets rc 0 (see *Gates*). `ci` was run as its parts; the PR's CI run is the single-command confirmation |
| 7 | QF_UF/QF_DT rows that mint ≥ 1 proxy; median/p90 ms vs `slice54-base` | **MEASURED** | 5 rows mint (QF_UF CLEARSY), upper bound 105 (QF_UF) and 0 (QF_DT); *Timing* |

## Per-logic matrix

Base = `slice54-base` ∪ `slice54-base-rest`, rendered together (see above);
after = `bench/results/slice54/report.md`.

| logic | run | total | correct | wrong | parse-error | panic | oom | timeout | unknown | unverified | decided% | median ms | p90 ms |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_DT | base | 8700 | 8104 | 0 | 0 | 0 | 0 | 585 | 11 | 0 | 93.1 | 28 | 71 |
| QF_DT | **slice54** | 8700 | **8105** | **0** | 0 | 0 | 0 | 584 | 11 | 0 | 93.2 | 6 | 11 |
| QF_UF | base | 7503 | 6866 | 0 | 34 | 0 | 0 | 603 | 0 | 0 | 91.5 | 153 | 4883 |
| QF_UF | **slice54** | 7503 | **7037** | **0** | 34 | 0 | 0 | 432 | 0 | 0 | 93.8 | 133 | 5464 |
| QF_UFLIA | base | 659 | 138 | 0 | 0 | 0 | 5 | 499 | 17 | 0 | 20.9 | 1998 | 11279 |
| QF_UFLIA | **slice54** | 659 | **144** | **0** | 0 | 0 | 6 | 492 | 17 | 0 | 21.9 | 1853 | 13695 |
| QF_UFLRA | base | 1284 | 44 | 0 | 1229 | 0 | 10 | 1 | 0 | 0 | 3.4 | 5 | 74 |
| QF_UFLRA | **slice54** | 1284 | **44** | **0** | 1229 | 0 | 10 | 1 | 0 | 0 | 3.4 | 7 | 80 |
| all | base | 18146 | 15152 | 0 | 1263 | 0 | 15 | 1688 | 28 | 0 | 83.5 | 51 | 1442 |
| all | **slice54** | 18146 | **15330** | **0** | 1263 | 0 | 16 | 1509 | 28 | 0 | 84.5 | 11 | 1651 |

`status-suspect` and `malformed` are 0 in every row. The unknown buckets are
unchanged: QF_DT `unknown:sat-budget` 11 and QF_UFLIA
`unknown:theory-refused` 17 in both runs. The separate leg reports are
`bench/results/slice54-base/report.md` (16,735 rows; its QF_UFLIA row covers
532 files) and `bench/results/slice54-base-rest/report.md` (1,411 rows:
QF_UFLIA 127, all `timeout`; QF_UFLRA 1,284).

## Transition matrices (changed cells only)

| logic | before | after | count | families |
| --- | --- | --- | ---: | --- |
| QF_DT | `timeout` | `correct` | 1 | 20230720-blocksworld 1 |
| QF_UF | `correct` | `timeout` | 4 | QG-classification 4 |
| QF_UF | `timeout` | `correct` | 175 | QG-classification 173, PEQ 1, SEQ 1 |
| QF_UFLIA | `oom` | `timeout` | 1 | 20230314-Jaroslav-Bendik-Certora 1 |
| QF_UFLIA | `timeout` | `correct` | 6 | mathsat 6 (all `Hash`) |
| QF_UFLIA | `timeout` | `oom` | 2 | 20230314-Jaroslav-Bendik-Certora 2 |

QF_UFLRA has no changed row. Closure, `new = old − outbound + inbound`:

- QF_DT `correct` 8,104 + 1 = 8,105; `timeout` 585 − 1 = 584.
- QF_UF `correct` 6,866 − 4 + 175 = 7,037; `timeout` 603 − 175 + 4 = 432.
- QF_UFLIA `correct` 138 + 6 = 144; `timeout` 499 − 6 − 2 + 1 = 492;
  `oom` 5 − 1 + 2 = 6.

All 9 QF_UFLIA changed rows are in leg 1.

## Proxy minting (criterion 7)

The brief's greps (upper bounds):

```
grep -rlE '\(declare-fun [^ ]+ \([^)]*Bool' bench/corpus/QF_UF | wc -l        # 105
grep -rlE '\(declare-datatypes' bench/corpus/QF_DT \
  | xargs grep -lE '\([a-zA-Z_][^ ()]* Bool\)' | wc -l                       # 0
```

The same grep over QF_UFLIA and QF_UFLRA gives 0 and 0 (spec §7: controls).
A parse-level scan (scratch script: an s-expression reader that handles
multi-line commands, checks every `declare-fun` parameter list and every
`declare-datatype`/`declare-datatypes` selector) over all four logics gives
the same set: **105 files, QF_UF only** (2018-Goel-hwbench 59,
20190906-CLEARSY 46), and **0 Bool selectors in QF_DT**.

Declaring such a function is not enough to mint: the argument must be
compound. A second scan expands `define-fun` macros and looks at every
application of a Bool-parameter function in the assertions (none of the 105
files use `let`):

| family | files with a Bool-parameter function | files with a compound Bool argument (mint ≥ 1 proxy) | distinct compound arguments |
| --- | ---: | ---: | --- |
| 2018-Goel-hwbench | 59 | 0 (arguments are `false`/`true` or Bool symbols, e.g. `(Concat_32_1_2_29 false y$38 y$n0s29)`) | — |
| 20190906-CLEARSY | 46 | **5** | 1–3 per file |

The 5 minting rows (`QF_UF/20190906-CLEARSY/…`): `0001/00304` (2 args,
`sat`), `0001/00314` (1, `sat`), `0015/00324` (3, `sat`), `0016/00428` (2,
`sat`), `0023/00293` (1, `unsat`). All 5 are `correct` in both runs (bench
37/28/16/21/18 ms base, 20/25/7/9/6 ms after). In a 3× interleaved
re-run all 30 runs are `correct` (*Timing*).

**Cross-tabulation with the transitions:** 0 of the 189 changed rows are in
the 105-file upper-bound list, so 0 are minting rows. All 105 are
`correct → correct`.

## Every formerly `wrong` row

None. Neither base leg has a `wrong` (or `status-suspect`) row (Task 1
Step 6), and neither does the after-run. The defect this slice fixes does not
occur in the local corpus in a form that changes an answer: the 5 minting
files were already answered correctly.

## Triage

Every changed row that starts or ends in `correct` was re-run, except
QF_UF QG-classification `timeout → correct`, which was sampled (20 of 173,
`random.seed(54)`). The 3 Certora `oom`/`timeout` swaps were re-run too.
That is 36 rows: the 4 `LOSS` rows, the 20-row QG sample, PEQ 1, SEQ 1, the
blocksworld row, the 6 mathsat `Hash` rows and the 3 Certora rows.

**Method.** Each re-run used the bench's own limit chain,
`prlimit --as=3072MiB timeout -s KILL 21 timeout 20 <bin> --stats <file>`,
with 6 jobs in parallel under `taskset -c 12-23` and nothing else running.
Each row ran **3 times with each binary**, base
(`target/slice54-base/shinri`, md5 `84a83b41…`) and after
(`target/slice54-after/shinri`, md5 `579f17b3…`), interleaved so both
binaries shared the same conditions: 216 runs. The verdict is the answer
compared with `:status`. The disposition rule is the slice-53 one: the row is
solver-attributable only if the base-run status reproduces 3/3 with the base
binary and the after-run status 3/3 with the after binary; if both binaries
give the same result, or the row flips both ways, it is noise.

**Noise by construction.** None of the 36 rows (none of the 189 changed
rows) declares a function with a Bool parameter or a Bool datatype field
(*Proxy minting*), so the purification rule cannot fire on them and the
encoding the after binary builds is the same as the base binary's (spec §3.3;
pinned by `unchanged_assertion_keeps_identical_termid`). The brief's rule: "A
loss on a file with no Bool argument is noise by construction." The re-runs
are the empirical check.

**Result: 0 wrong answers in 216 runs. Every row is noise.** On 33 of 36
rows the two binaries solved the row the same number of times out of 3. On
the other 3 the after binary solved it once more (`gensys_icl148` 2 vs 3,
`gensys_icl538` 1 vs 2, `gensys_brn045` 1 vs 2). In each differing
rep-pair the after binary answered at 18.7–19.8 s and the base binary hit
the 20 s limit: the 20 s edge. Over the 43 rep-pairs where both binaries answered, the median
after/base wall-time ratio is **0.993** (range 0.937–1.119). The variation
is in time, not in binary: the second interleaved repetition solved 44 of 72
row-runs, the first and third 22 and 23, for both binaries alike. A single
pinned run of `gensys_brn378` took 9,381 ms (base) and 9,404 ms (after) on
one core.

### The 4 `correct → timeout` rows (QF_UF QG-classification)

| row | `:status` | bench base / after | re-run base ✓/3 (range) | re-run after ✓/3 (range) | mints a proxy? | disposition |
| --- | --- | --- | --- | --- | --- | --- |
| `qg5/gensys_brn091.smt2` | unsat | `correct` 17,381 ms / timeout | 1 (17.9–20.0 s) | 1 (17.8–20.0 s) | no | **noise** (20 s edge, both binaries) |
| `qg5/gensys_brn1041.smt2` | unsat | `correct` 18,679 ms / timeout | 1 (18.3–20.0 s) | 1 (18.3–20.0 s) | no | **noise** |
| `qg5/gensys_brn378.smt2` | unsat | `correct` 10,934 ms / timeout | 2 (11.0–20.0 s) | 2 (10.8–20.1 s) | no | **noise** (one timeout each, same repetition) |
| `qg7/gensys_brn045.smt2` | sat | `correct` 16,424 ms / timeout | 1 (11.9–20.0 s) | 2 (11.7–20.0 s) | no | **noise** (after solves it more often) |

(prefix `QF_UF/QG-classification/`.) No row is attributable, so no logic's
credited net is negative.

### The QF_UF `timeout → correct` gain (175 rows)

QG-classification 173, PEQ 1, SEQ 1. **Not attributable: it is base-run
timing noise.** None of these files can mint a proxy. In the re-run the two
binaries behave the same: of the 20 sampled QG rows, 4 solve
3/3 with both (`icl167`, `icl180`, `icl644`, `icl703`), 2 time out 3/3 with both (`icl763`, `icl845`), and the rest sit at the edge
with the same count for both, except `icl148` and `icl538` (+1 for after).
PEQ003 times out 3/3 with both binaries; SEQ010 solves 1/3 with both.

Why the base run timed out on these rows: QG-classification is a family of
hundreds of rows that take 10–20 s, so a few percent of wall-time drift
moves rows across the 20 s limit. The drift is visible in the bench itself.
For QG rows that are `correct` in both runs and take > 1 s, the median
after/base wall-time ratio, by position in base leg 1 (estimated from the
cumulative `wall_ms` / 6 jobs), is 1.06, 0.97, 0.75, 0.69 and 0.90 for
successive fifths. The gains cluster where the base run was slow: by the
same estimate, 47 + 67 + 44 of the 173 fall between about 50 and 80 min
into leg 1, and 9 + 6 outside. The 4 losses fall where the base run was
faster (3 at 40–50 min, 1 at 80–90 min). No log of this session's cargo work
is stamped inside the QF_UF section (Task 3's last, `mise run test`, ended at
11:51:34, about 20 min into leg 1, while QF_DT was still running; the next
are the gates at 13:42), so the slowdown looks host-level; its cause
was not identified. Over every QF_UF row `correct` in both runs with base > 200 ms, the median ratio is
0.815. The paired re-run, with interleaved binaries, gives 0.99 (above).

### The other gains and swaps

| logic | rows | re-run base ✓/3, after ✓/3 | disposition |
| --- | --- | --- | --- |
| QF_DT | `blocksworld_from_0_0_8_to_1_3_4_negated_goal_bmc_9` `timeout → correct` | (1, 1); 13.3–20.1 s both | noise |
| QF_UFLIA | mathsat `Hash/hash_{sat_04_17, sat_06_08, sat_10_03, uns_05_15, uns_05_16, uns_05_17}` `timeout → correct` | `sat_04_17` (0, 0); the other 5 (1, 1), 17–20 s | noise (20 s edge) |
| QF_UFLIA | Certora `25959_…_65` `oom → timeout`; `44289_…_14`, `93493_…_49` `timeout → oom` | each 2 timeouts + 1 SIGABRT under the 3 GiB limit (rc −6, the bench's `oom`), for both binaries | noise (undecided either way) |

QF_UFLIA and QF_UFLRA have no file with a Bool-parameter function, so they
are controls (spec §7), and they moved only at the edge.

### Credited gain

| logic | raw net | noise (gain / loss) | attributable | **credited net** |
| --- | ---: | --- | --- | ---: |
| QF_DT | +1 | blocksworld 1 / 0 | 0 | **0** |
| QF_UF | +171 | QG 173, PEQ 1, SEQ 1 / QG 4 | 0 | **0** |
| QF_UFLIA | +6 | mathsat 6 / 0 | 0 | **0** |
| QF_UFLRA | 0 | – | 0 | **0** |
| **all** | **+178** | **+178 net noise** | **0** | **0** |

The QG 173 rows are credited as noise from a 20-row sample (and by
construction, since none can mint); the other changed rows were all
re-run.

## Timing (criterion 7)

The bench-level medians are confounded by load during the base run (QF_DT;
see *Load disclosure*) and by the host drift during its QF_UF section (see
*Triage*). So a controlled paired sample was also taken, as in slice 53: in
each logic, 100 random rows (`random.seed(54)`) that are `correct` in both
runs, or all 44 for QF_UFLRA. Each ran once per binary, interleaved, under
the bench's `prlimit`/`timeout` chain, `taskset -c 12-23`, 6 jobs, on an
otherwise idle machine. Wall time is measured around the process, so it
includes startup.

| logic | bench base med / p90 | bench slice54 med / p90 | paired sample n | sample base med / p90 | sample after med / p90 | median per-row ratio after/base |
| --- | --- | --- | ---: | --- | --- | ---: |
| QF_DT | 28 / 71 | 6 / 11 | 100 | 19 / 37 | 18 / 30 | 0.92 |
| QF_UF | 153 / 4883 | 133 / 5464 | 100 | 171 / 5460 | 198 / 5473 | 0.99 |
| QF_UFLIA | 1998 / 11279 | 1853 / 13695 | 100 | 1666 / 10896 | 1661 / 10760 | 0.99 |
| QF_UFLRA | 5 / 74 | 7 / 80 | 44 | 8 / 90 | 6 / 96 | 1.00 |

The bench columns are over all `correct` rows, from each `report.md` (base:
both legs combined). Over rows `correct` in both runs, the bench medians are
QF_DT 28 → 6, QF_UF 153 → 128, QF_UFLIA 1,998 → 1,579 and QF_UFLRA 5 → 7 ms.
Both binaries gave the same answer on all 344 sampled rows, and all 688 runs
were `correct`.

**The 5 minting rows** (CLEARSY), re-run 3× per binary, interleaved: all 30
runs `correct` (same answers as the bench), base median 21 ms / p90 45 ms,
after 26 ms / 52 ms. They take 10–67 ms with either binary, so this
difference is within run-to-run spread at that scale (for example
`0001/00314`: base 33, 18, 67 ms; after 25, 16, 23 ms).

**Reading.** On the paired sample the slice is timing-neutral: the median
per-row ratio is 0.92–1.00 in every logic. That is expected, since only 5 of
18,146 rows contain the shape. The QF_DT 0.92 is on rows of about 20 ms, so
it is startup-scale; QF_DT has no proxy-minting file, so its encoding is
unchanged.

## Oracle and probe evidence

- **Probes** (`tests/slice54_probes.rs`, blocking tier, 23 tests). At HEAD
  `bc6d152` (Task 3 Step 2), 23 discovered: **5 passed, 18 failed**. The
  passes are the pins (`r6_bare_bool_constant_argument`, the three
  `fence_pin_*`, `get_model_has_no_proxy_symbols`). 17 failed with a wrong
  `sat` (r1, r2, r3, r4, r5, r7, `uflra_eq_argument`, `uflra_le_argument`,
  `s5_datatype_constructor_argument`, `datatype_selector_over_purified_field`,
  `multi_argument_uf`, `bool_argument_uf_under_arithmetic`,
  `nested_purification`, `push_pop_reuses_proxy_soundly` (`sat sat sat`),
  `incremental_pin_after_first_check` (`sat sat`),
  `string_path_bool_arg_is_not_sat`, `proxy_inside_eliminated_term_ite`), and
  `post_mint_declaration_of_bool_proxy_is_rejected` failed its length check
  (`["sat","sat"]`). After the fix (Task 3 Step 6): **23/23**.
- **Unit tests** (`word_norm::tests`): the 6 new tests were 1 passed / 5
  failed before the fix; after, `-E 'test(/word_norm/)'` gives 22/22 (16
  existing + 6 new).
- **Oracle family `bool_arg_oracle`** (3 tests, 200 scripts per family, z3):

  | | QF_DT sat / unsat / unknown / disagreements | QF_UFLIA | QF_UFLRA |
  | --- | --- | --- | --- |
  | before (HEAD `bc6d152`, Task 2 Step 2; 15.3 s) | 124 / 76 / 0 / **29** | 167 / 33 / 0 / **20** | 152 / 48 / 0 / **12** |
  | after (`6212fa5`, Task 3 Step 8; 10.8 s) | 95 / 105 / 0 / **0** | 147 / 53 / 0 / **0** | 140 / 60 / 0 / **0** |

  Both sat and unsat counts are non-zero after; the runtime is under the
  30 s target. Logs: `target/slice54-oracle-before.log`,
  `target/slice54-oracle-after.log`.
- **Existing related families** after the fix:
  `test(differential_qf_uflia_compound_args) + binary(qfdt_oracle)`, 19
  discovered, 19 passed (`target/slice54-oracle-existing-after.log`).
- **Full oracle suite** (Task 4 Step 1,
  `cargo nextest run -p shinri-solver --features oracle`):
  **749 run, 749 passed, 3 skipped** (752 discovered), 1,182.7 s
  (`target/slice54-oracle.log`). The brief expected "720 + 3". Slice 53's
  720 was the discovered count (717 run + 3 skipped); this slice adds 32
  tests to the `shinri-solver` package, and the log shows all of them:
  `slice54_probes` 23, `bool_arg_oracle` 3, and 6 new `word_norm` unit
  tests in the lib binary (22 `word_norm::` tests in the log, 16 before).
  717 + 32 = 749 run; 720 + 32 = 752 discovered.

## Fence audit (Task 3; spec §3.5 risk 2)

No routing predicate treats the new shapes (a nullary `bool!` symbol, a
top-level Bool `(= b t)`) as a trigger:

- `bv_stage::has_non_bv_theory_atom`: a Bool-operand `=`/`distinct` is
  `is_bool_eq` structure and recurses; a nullary Bool uninterpreted symbol
  returns `false` (exempt).
- `abv_stage::fenced` / `walk_fence`: a Bool-operand (dis)equality is
  `is_bool_eq` structure; a Bool-sorted uninterpreted application recurses
  into its children, and a nullary one has none.
- `string_stage::fenced`: fences an uninterpreted application only when it
  is non-nullary and has a String result or argument; `bool!` is nullary
  Bool, and `(= b t)` is a builtin `=` that recurses.

The fence pins (s3, s4, s6) stay `unknown` after the fix (criterion 5).

## Logics not benched (reasoned omission)

QF_LIA, QF_LRA, QF_S, QF_SLIA and QF_BVFP were not run (spec §7). Their
logics admit no uninterpreted function symbols, datatypes or arrays, so no
non-connective parent can take a Bool argument and the rule cannot fire.
Their encoding is byte-identical by spec §3.3 (pinned by the unit test
`unchanged_assertion_keeps_identical_termid` and
`bare_constants_and_connective_children_are_not_purified`). This is a reasoned omission, **not** measured
coverage.

## Gates

Run at `6212fa5` before the after-run, after the base run finished
(logs `target/slice54-gate-{lint,test,deny,secrets}.log`,
`target/slice54-oracle.log`; all rc 0).

- `mise run lint` (fmt `--check` and `clippy --workspace --all-targets -D warnings`): clean.
- `mise run test`: **1,652 tests run, 1,652 passed (5 slow), 7 skipped**
  (261 s).
- `mise run deny`: advisories, bans, licenses and sources ok.
- `mise run secrets` (gitleaks): no leaks found.
- Oracle suite: 749 run, 749 passed, 3 skipped (above).

With lint and test, deny and secrets cover every dependency of
`mise run ci`.

Not a gate: `cargo clippy --features oracle` fails on **pre-existing** oracle
test files under Rust 1.99 (`manual_is_multiple_of`, `too_many_arguments`);
the new `bool_arg_oracle.rs` is clean. CI and `mise run lint` do not lint
with `--features oracle`. Queued.

## Queued for the next slice

New from this slice:

- **`get-value` remap for purified arguments.** After the fix,
  `(get-value ((P (= x 1))))` prints `?` where HEAD printed `true` (see
  *What changed versus the spec*, item 2). Add a `lib.rs` remap from the
  original term to its purified form, the way `orig_ite_map` /
  `eliminated_ite_vals` handle eliminated ites. Do it together with the
  carried "`get-value` echoing internal names" item.
- **`clippy --features oracle` under Rust 1.99.** Pre-existing oracle test
  files fail it (`manual_is_multiple_of`, `too_many_arguments`). Fix them,
  and consider linting with `--features oracle` in `mise run lint`.
- **Harness: a resume is refused when the checkout moved.** The fixture
  check compares the checkout sha, so a base run interrupted after a commit
  cannot be resumed under its run-id (this slice's two-leg base run).
  Either record the binary's md5 as the identity for `--solver` runs, or
  launch long runs detached (as slice 53's ruling R1 did) so the 2 h tool
  limit never applies.
- **No corpus row exercises the fix.** Only 5 local files mint a proxy, and
  they were already `correct`. The slice's evidence is the probes and the
  oracle. A wider corpus (e.g. QF_AUFLIA / UFDT logics) would be needed for
  a bench-level signal.

From spec §9:

- Slice 55: the slice-53 queue's first entry — remove the `Not(Eq)` arm,
  together with the bare-E simplification and the string-engine
  search-order sensitivity, and the axiom memory-growth measurement.
- QF_UFBV / FP-path Bool arguments: blast a proxy as a 1-bit word instead of
  fencing (`bv_stage::uf_args_supported` rejects every Bool argument; pinned
  by `fence_pin_ufbv_bool_argument_stays_unknown`).
- Bool-element arrays (s3, s4; pinned by the two `fence_pin_bool_array_*`
  probes).
- `get-value` echoing internal names (carried; see below).

Carried verbatim from the slice-53 report's queue, minus the "Wrong `sat`: a
theory atom used as an argument of an uninterpreted function" item. That
item is **closed by this slice**, and the shape was broader than described
there: any compound Bool argument of a non-connective parent was unlinked,
including pure-Boolean arguments in QF_UF (`(P (and q q))`) and datatype
constructor arguments in QF_DT (`(mk (and q r))`), not only theory atoms.
Internal references such as "the timing above" and *Attribution* point into
the slice-53 report. (The carried "`bool_proxy` wrong `sat`" item is a
string-engine marker test from slice 52, unrelated to this slice's `bool!`
proxies.)

- **Remove the redundant `Not(Eq) → (or Lt Gt)` arm.** The timing above shows
  the axioms are not slower at the median, which was spec §10's condition.
  Do it together with the next item, because it changes the encoding the
  string engine is sensitive to.
- **The bare-E §3.3 simplification, together with the string-engine order
  sensitivity.** Returning bare `E` from `lower` regressed
  `probe_c_len_zero_var` and `user_pfx_name_declared_before_any_mint_still_works`
  to `str-model-rejected` (R6). In this run the same sensitivity cost
  Reynolds 86 and stringfuzz 3 rows, and gained Reynolds 101 and stringfuzz 9.
  The smallest reproducer is
  `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-translate-rotate-fuzz.smt2`
  (3 assertions; `unsat` at `2ceef06`, `unknown:str-model-rejected` at
  `07ac180`; z3 `unsat`). The string engine accepts a premature SAT that
  depends on the SAT decision order over its split atoms. Fix that first,
  then the bare-E simplification is safe.
- **Losses attributable to the faithful encoding.** The cause is search-order
  sensitivity, not a uniform cost: the same families also gain (rings +4/−5,
  sc +2/−1, Reynolds +101/−86). See *Attribution*. The reproducers are
  `QF_LIA/rings/ring_2exp14_3vars_0ite_unsat.smt2` (46 ms at `2ceef06`;
  timeout now, and timeout on `2ceef06` too once the `(= o_k 1)` atoms are
  encoded faithfully) and
  `QF_SLIA/20180523-Reynolds/kaluza/unsat/big/21760.corecstrs.readable.smt2`
  (`unsat` → `unknown:sat-budget`). Also `calypto/problem-006045`,
  `sc/sc-15.induction.cvc` and `TM/p5-driverlogNumeric_s8`. These are
  search-order/heuristic items in arithmetic (an `ite`/iff-heavy LIA mod-ring
  encoding) and string-budget items, not soundness items.
- **Memory growth on large LIA/UFLIA instances.** On
  `nec-smt/large/handler_sigchld/prp-0-48.smt2` the after binary runs out of
  memory at about 4 s (3/3), while `2ceef06` times out at 20 s. The same
  holds for `arctic-matrix/constraint-2050620` and the two Certora rows.
  Measure the axiom pass's term/clause growth on these instances. Two
  plausible contributors are worth measuring together with the `Not(Eq)` arm
  removal:
  - Pure-arithmetic `(not (= a b))` atoms are still collected and get
    3 axioms, even though the `Not(Eq)` arm rewrites them to `(or Lt Gt)`.
    So E, Le and Ge are minted for nothing.
  - Each axiom is a `TermId` `or` that goes through Tseitin, not a direct
    clause.
- **QF_LRA `ite` with Int-literal branches answers `unknown`** (R7): for
  example `(ite c 1 0)` in a Real context under a QF_LRA header. It is
  pre-existing and independent of this slice. `term_ite_condition` uses
  `1.0`/`0.0` until it is fixed.
- **FP-to-Real bridge hang** (pre-existing). The script is QF_FPLRA:
  `(fp.eq x ((_ to_fp 5 11) RNE 1.0))`, `(= p (= (fp.to_real x) 2.0))`, `p`.
  It was a wrong `sat` on `2ceef06`. It is now a timeout (> 20 s) on
  `07ac180`, because the axioms now give the inner `=` its arithmetic meaning.
  The plain positive form, `(= (fp.to_real x) 2.0)` with `x` pinned to 1.0,
  also hangs (> 20 s) on **both** binaries. z3 answers `unsat` for both.
- **`(get-model)` does not `|…|`-quote symbols that need it** (names with `#`
  or `:`, as in ESBMC's `__ESBMC_rounding_mode&0#10`), so the printed model is
  not re-parseable SMT-LIB. This was found during the ramalho triage.
- Harness nit: the fixture header records the checkout HEAD, not the binary's
  commit. For `slice53-base` they differ (`807ec5b` vs the `2ceef06`
  sources, docs-only diff).

Ramalho is fixed (branch 4a), so it is not queued.

Carried verbatim from the slice-52 report:

- **H3 needs narrowing.** The word-equation gate own-literal/diseq
  exemption took the Noetzli pair to `unsat` but cost 313 correct `sat`
  rows (309 bisected to Task 4, the rest Norn), `sat-budget` +497 (QF_SLIA) in the H3
  run; reproducer `Reynolds/kaluza/sat/small/1708.corecstrs.readable.smt2`
  (`sat` at `c91e221`, `unknown:sat-budget` at `8ee8f00`). Narrow the gate
  or find why the extra resolution exhausts the SAT budget. The reverted
  commits are `4fb0dab`, `18b1e36`, `8ee8f00` (revert commits `a78895e`,
  `c25fbd2`, `c5cd62c`).
- **4 Norn HammingDistance rows lost to Task 3 (H1).** `norn-benchmark-1190`,
  `-147`, `-151`, `-828`: `sat` at `e61e81c`, `unknown:sat-budget` at
  `c91e221`. Cause: H1 also acts on regex-membership-minted equations
  (the split path skips them, D-wordeq-skip); skipping them in H1 restores
  these 4 but loses 6 Norn gains. **Decide deliberately whether H1 should act
  on membership-minted equations.**
- **`bool_proxy` wrong `sat`** (pre-existing; pinned as a passing known-bug
  marker asserting `sat`, R16), with
  `distinct_form` and `xor_form` (sound `unknown`): a minted-branch
  completeness gap. Needs a deep-nf re-resolve that emits only a cited
  `Propagate` (R11).
- **Deep-nf propagate (R11)** and the `eval_bool` audit, which together
  retire the `bool_proxy` wrong `sat` and the `distinct_form`/`xor_form`
  `unknown`s. The Noetzli `unsat` also needs H3 (above).
- **Evidence limit.** Every unsat in the congruence family is decided at
  level 0; the level > 0 `Split` exposure is covered only by the E1 fuzz
  (measured with H3 present).
- **Search-order fragility (R12)**, which applied to the H3 run: the Noetzli
  pair passed by search order. Worth remembering when H3 returns.
- Single-atom `[] = [y]` merge after H1 leaves `len(y)` unlinked (R10; sound,
  the gate backstops).
- Congruence and minted merges are not in the H3 contributor map (Split-only
  exposure).
- The combiner computes shared terms once per final check, so `len`/`0`
  terms minted mid-check reach arithmetic only on a later final check.
- Deferred minors: `empty_merged` is monotone and never restored on pop
  (perf only); the conflict path of the `len(v) ≈ 0` merge (`lib.rs` ~986)
  has no test; no unit test pins `eval` of a Bool constant `p` under Bool
  `=`; Bool `=` against literal `true`/`false` may return `None` if the
  literals are not `TermNode::App` (conservative); the diseq-test assertion
  message is copied from its sibling.

From spec §10 (slice 52):

- H2 (the AB prefix case; z3 says `sat`, so it is a model-soundness check
  rather than an `unsat` target) and the `eval_bool` audit (spec §9).
- Carried from slice 51: the 4 denghang `unknown:str-model-rejected` rows
  (`instance46836`, `51681`, `52132`, `55189`); premature string SAT on
  decoded control-character regexes (68 rows, reproducer
  `automatark-lu/instance06924.smt2` assertions {1, 2, 3, 5}); surrogate
  support; `str.replace_re`/`str.replace_re_all` (195 parse-error rows).
- Carried from slice 50: the QF_SLIA `STRING_PATH_PIVOT_BUDGET` cliff; the
  Wisa final-check blow-up; `get-value` echoing purification names; the
  `Owner::Shared` definitional merge; `pending` is not backtracked; the
  blocksworld re-index churn measurement; the `blast_word` panic bucket.
- ~~Not re-measured since the baseline: `wrong` rows in QF_LIA (calypto, 2),
  QF_LRA (keymaera, 2), QF_BVFP (ramalho, 1).~~ **Closed by this slice**
  (all five `wrong → correct`).
- Harness nit (carried): the fixture header records the checkout HEAD, not
  the binary's commit. Here they differ for the base run (above).

Test-tier note (carried): the unfiltered oracle suite is dominated by
`fp_oracle differential_qf_fp_rem` (~25–33 min), over the 5 min rule; it is an
existing test, not part of this slice.

## References

- Spec: `docs/superpowers/specs/2026-10-02-shinri-slice54-uf-bool-arg-purify-design.md`
  (§7 criteria, §9 queue, §11 measured outcomes).
- Plan: `docs/superpowers/plans/2026-10-02-shinri-slice54-uf-bool-arg-purify.md`.
- Slice-53 report: `docs/superpowers/research/2026-10-02-smtlib-2024-slice53-arith-eq-polarity-report.md`.
- Baseline: `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`.
- Commits: `b59f115` (Rust 1.99.0), `bc6d152` (oracle families, failing at
  HEAD), `6212fa5` (the purification in `word_norm.rs` and `slice54_probes`).
- Runs (git-ignored): `bench/results/slice54/`, `bench/results/slice54-base/`,
  `bench/results/slice54-base-rest/`.
