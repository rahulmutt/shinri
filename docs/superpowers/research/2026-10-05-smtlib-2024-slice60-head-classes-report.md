# SMT-LIB 2024 re-run — slice 60 (head-only next-character classes) — shinri @ 4a9e656

## Headline

> **Follow-up:** the Rule-E full-partition variant (`56997aa`) passes criterion 3 and supersedes approach 1's verdict on it. See *Follow-up: Rule-E full-partition variant (56997aa)* at the end.

Slice 60 changes `regex::next_classes` so that it cuts Σ only at the bounds of
head-reachable `Range` nodes (`head_bounds`). Before, it cut at every `Range`
in the regex. Long literals therefore no longer overflow `CLASS_SPLIT_CAP`
(64) on the first derivative step. Every caller is affected: the membership
witness search (`memb_seeds`), the emptiness conflict and Rule-E.

The benchmarked binary is `4a9e656`. Branch HEAD `0e39c39` differs from it
only in tests and comments: a Rule-E unit test in `memb.rs`, plus oracle and
sweep comments. No production code differs, so the bench measures the code
that ships.

- **Rows moved to `correct`: 917** (QF_S 609, QF_SLIA 308). All 917 were
  `unknown:str-model-rejected` with tag `violated:memb@not-needed` in base.
  - With a corpus status: 310 `unsat`, 289 `sat`.
  - With corpus status unknown and z3 agreeing: 318 (294 `sat`, 24 `unsat`).
  - Adding 10 Norn `sat-budget → correct` rows, string `correct` rises by
    **+897** in net: QF_S 16,057 → 16,666 and QF_SLIA 24,856 → 25,144.
- **Criterion 2:** `violated:memb@not-needed` falls **2,252 → 525**. Of the
  base-tagged rows, **917 (40.7%)** are now `correct` (bar: ≥ 450 and ≥ 20%).
  - Another **897** base-tagged rows are now decided but `unverified`,
    because the z3 oracle timed out at 20 s: 855 `sat` (853 stringfuzz
    `generated`, 2 stringfuzz `transformed/amazon`) and 42 `unsat`
    (automatark 38, denghang 4).
  - `unknown:str-model-rejected` as a whole falls 4,084 → 2,360.
- **Criteria:**

  | # | result |
  | --- | --- |
  | 1 | PASS: 0 `wrong`; 0 wrong answers in triage. Cross-check of the 42 new unverified `unsat` rows: 0 `sat` from z3 or cvc5, 36 confirmed `unsat`, 6 unconfirmed |
  | 2 | PASS |
  | 3 | **FAIL — accepted by controller ruling, pending owner decision**: 4 attributable Norn HammingDistance `correct → unknown` rows, against +10 in the same family |
  | 4 | **FAIL, on the faster side**: the after binary is 17–29% faster on both-`correct` rows, outside ±5%. Newly-`correct` rows run about 11× longer than base's fast fence (reported, not gated) |
  | 5 | PASS |
  | 6 | PASS |

- **Caller attribution** over 40 seeded gain rows: witness search 24 (1 of
  them also with Rule-E splits), emptiness conflict 16, Rule-E only 0.

## Commands

Task 0 (controller): base binary from the branch point `aab0dfd`, then the
base runs, detached.

```bash
# Step 3: build and freeze the base binary
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice60-base && cp target/release/shinri target/slice60-base/shinri
cp target/release/shinri-bench target/slice60-base/shinri-bench
md5sum target/slice60-base/shinri | tee target/slice60-base/md5.txt
git rev-parse --short HEAD | tee target/slice60-base/commit.txt
# Step 4: probes on the base binary (plan Task 0 Step 4) -> target/slice60-base/probes.txt
# Step 5: launch both base runs detached
date -u +%FT%TZ > target/slice60-base/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice60-base/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice60-base/shinri --run-id slice60-base \
  > target/slice60-base/run.log 2>&1; \
  taskset -c 12-23 target/slice60-base/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice60-base/shinri --run-id slice60-base-sample \
  > target/slice60-base/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice60-base/finished.txt' \
  > /dev/null 2>&1 &
```

Task 4 (controller): `mise run ci`, `cargo nextest run -p shinri-solver
--features oracle`, and the wide-head pins, all written to
`target/slice60-gates.txt`.

Task 5:

```bash
# Step 2 (controller), at 4a9e656
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice60-after && cp target/release/shinri target/slice60-after/shinri
md5sum target/slice60-after/shinri | tee target/slice60-after/md5.txt
git rev-parse --short HEAD | tee target/slice60-after/commit.txt
date -u +%FT%TZ > target/slice60-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice60-after/shinri --run-id slice60 \
  > target/slice60-after/run.log 2>&1; \
  taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice60-after/shinri --run-id slice60-sample \
  > target/slice60-after/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice60-after/finished.txt' \
  > /dev/null 2>&1 &
# Step 3: reports and join (brief script) -> target/slice60-after/{join.txt,changed.tsv}
for id in slice60-base slice60 slice60-base-sample slice60-sample; do BENCH_RUN_ID=$id mise run bench-report; done
# Step 4: triage-in.tsv (brief gain selection + stratified non-gain sample), 6 rows in parallel
tr '\t' '\n' < target/slice60-after/triage-in.tsv | xargs -d '\n' -n 6 -P 6 target/slice60-after/triage-row.sh > target/slice60-after/triage.tsv
#   per binary and run: taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats $root/$p
python3 target/slice60-after/triage_disp.py     # -> triage-disp.txt, triage-summary.txt
# Unsat cross-check (controller ruling), 6 rows in parallel on cores 12-23
xargs -d '\n' -n 1 -P 6 target/slice60-after/crosscheck-row.sh < target/slice60-after/unsat-crosscheck-in.txt
#   per row: z3 -T:120 $f ; cvc5 --tlimit=120000 $f      -> unsat-crosscheck.tsv
# Step 5: throwaway trace build (the brief's 3 eprintln!s), then reverted
cargo build --release -p shinri-cli --target-dir target/slice60-trace
git checkout -- crates && git status --short crates     # printed nothing
# Step 6: target/slice60-after/timing.py (brief script, taskset -c 12, random.Random(60)), 3 passes;
#   timing-swapped.py (after before base, diagnostic); per-row newly-correct timing
```

## Runs

| run | solver | md5 | started | finished | rows |
| --- | --- | --- | --- | --- | ---: |
| `bench/results/slice60-base/` | `target/slice60-base/shinri` (`aab0dfd`) | `cf6f6b2f24215ba31e173ebc0d4dfde9` | 2026-10-04T19:54:13Z | (string leg ends when the sample leg starts, 21:42:46Z) | 103,335 |
| `bench/results/slice60-base-sample/` | same | same | 2026-10-04T21:42:46Z | 2026-10-04T22:00:30Z | 2,000 |
| `bench/results/slice60/` | `target/slice60-after/shinri` (`4a9e656`) | `835cc5544cb3df04716e37a7554d64b4` | 2026-10-04T22:01:11Z | (string leg ends when the sample leg starts, 00:56:29Z) | 103,335 |
| `bench/results/slice60-sample/` | same | same | 2026-10-05T00:56:29Z | 2026-10-05T01:13:58Z | 2,000 |

- All four runs used `--timeout 20 --mem-mb 3072 --jobs 6` on cores 12–23.
- Each `results.jsonl` holds its rows plus one fixture line (103,336 and
  2,001 lines).
- The base and after row sets are identical.
- The base md5 matches slice 59's after binary. That is expected: no crate
  changed in between.

Harness nit (carried): the fixture `sha` records the checkout HEAD, not the
commit the binary was built from:

| run | recorded `sha` |
| --- | --- |
| `slice60-base` | `aab0dfd-dirty` |
| `slice60-base-sample` | `4a9e656` |
| `slice60` | `4a9e656` |
| `slice60-sample` | `0e39c39` |

The md5 is the authoritative identity.

## Success criteria (spec §8)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | **PASS** | 0 `wrong` rows in all four runs. 0 rows flip `sat` ↔ `unsat` between base and after. Triage made 1,434 runs (239 rows × 6): no row gets both `sat` and `unsat`, and no decided run contradicts a known corpus status. See *Unsat cross-check* for the 42 new unverified `unsat` rows |
| 2 | `violated:memb@not-needed` shrinks by ≥ 20% (≥ 450 rows), moving to `correct` | **PASS** | 2,252 → 525. 917 base-tagged rows (40.7%) are now `correct` |
| 3 | no `correct → non-correct` change that reproduces 3/3 | **FAIL — accepted by controller ruling, pending owner decision** | 4 Norn HammingDistance rows reproduce 3/3 on each side (table below). None flips `sat` ↔ `unsat`. The same family gains 10 rows. The PR does not merge without the owner's decision |
| 4 | serial interleaved timing on 150 both-`correct` rows per string logic, within ±5% | **FAIL (outside the band on the faster side)** | Pooled over 3 passes: QF_S 0.794, QF_SLIA 0.740. Every pass lies in 0.709–0.828. A diagnostic pass with after run first gives 0.868 / 0.746, so the gap is not an ordering artefact. Newly-`correct` rows: 11.10 pooled (reported, not gated). See *Timing* |
| 5 | `mise run ci` green; oracle suite discovered count ≥ slice 59 + this slice's oracle tests | **PASS** | `target/slice60-gates.txt` at `4a9e656`. ci: exit 0, 1768 run / 1768 passed / 6 skipped, the plan's expected count (HEAD adds 1 `shinri-str` unit test, making 1769). Oracle `--features oracle`: 831 run / 831 passed / 2 skipped, the plan's expected 831 and ≥ 825 + this slice's 2 `head_classes_oracle` tests; discovered count is non-zero. Wide-head pins: 3/3 |
| 6 | neutrality sample: only non-reproducible timing flips | **PASS** | 4 sample rows changed. All 4 are noise in triage: both binaries give identical answers in every run |

Probe outcomes (Task 0 Step 4 vs Task 2): the three probe shapes `pin`,
`regex010` and `shared` all answer `unknown` (`str-model-rejected`,
`violated:memb@not-needed`) on the base binary. On the after binary they
answer `sat`, `unsat` and `sat`.

### Criterion 1: unsat cross-check (controller ruling)

The cross-check covers 42 rows that move from `str-model-rejected` to
`unverified` with a shinri `unsat` answer. These rows have no corpus status,
and the bench's z3 oracle timed out on them at 20 s. Each row was run under
z3 4.16 (`-T:120`) and cvc5 1.4.1 (`--tlimit=120000`), 6 rows in parallel on
cores 12–23. Results are in `target/slice60-after/unsat-crosscheck.tsv`.

| z3 | cvc5 | rows |
| --- | --- | ---: |
| unsat | unsat | 5 |
| timeout | unsat | 31 |
| timeout | timeout | 6 |

- **No `sat` from either solver on any row.**
- Confirmed by z3: 5. Confirmed by cvc5: 36, including all 5 z3
  confirmations. Confirmed by at least one solver: 36.
- **Unconfirmed: 6**, all automatark: `instance06362`, `10317`, `10696`,
  `13032`, `15041`, `15868`.
- All 4 denghang rows are cvc5-confirmed, and 1 of them is z3-confirmed too.

The 855 new `unverified` `sat` rows (853 stringfuzz `generated`, 2
`transformed/amazon`) are model-checked by shinri's own gate,
which is the fence they used to fail. The 32 sampled ones reproduce 3/3.

### Criterion 3: the four regressions

All four rows are QF_SLIA `2015-Norn/HammingDistance` with corpus status
`unknown`. In base they are `correct` because z3 agrees. Each binary
reproduces its own verdict 3/3 in triage, and again in a separate serial
re-run on cores 0–11. The trace column shows Rule-E class counts per split
from the throwaway build, as `count×splits`.

| row | base (3/3) | after (3/3) | after trace |
| --- | --- | --- | --- |
| `norn-benchmark-312.smt2` (1,483 B) | `sat` | `unknown:sat-budget` (1–5 ms) | rule-e 2×1, 3×5, 6×1; no seed, no empty-conflict |
| `norn-benchmark-322.smt2` (1,483 B) | `unsat` | `unknown:sat-budget` | rule-e 2×1, 3×5, 6×1; no seed |
| `norn-benchmark-362.smt2` (1,902 B) | `sat` | `unknown:sat-budget` | rule-e 1×2, 3×1, 5×2, 6×4; no seed |
| `norn-benchmark-454.smt2` (2,093 B) | `sat` | `unknown:str-model-rejected` (`violated:memb@not-needed`) | rule-e on 15 splits; 1 seed |

On these rows only Rule-E runs the changed partition. Three rows get no
witness seed, and no row fires an emptiness conflict. With the coarser
partition, Rule-E produces fewer and different disjuncts per split, which
changes the SAT search over the split atoms. In three rows that search now
exhausts the budget almost immediately. The family has shown this kind of
search-order sensitivity before (slice 52, H1). It is not a soundness issue.

Context:
- The same family moves **+10** rows (`unknown:sat-budget → correct`) and
  **−4** rows, a net gain of +6 `correct`.
- The owner's scope ruling (spec header, §3 approach 1) chose to let Rule-E
  move.
- The controller accepted the FAIL as recorded, with no code change, pending
  the owner's decision.

## Verdict changes

### String runs (QF_S + QF_SLIA)

Verdict counts (base → after):

| verdict | QF_S base | QF_S after | QF_SLIA base | QF_SLIA after |
| --- | ---: | ---: | ---: | ---: |
| correct | 16,057 | 16,666 | 24,856 | 25,144 |
| parse-error | 0 | 0 | 195 | 195 |
| timeout | 8 | 7 | 49 | 54 |
| unknown:reglan-decl | 0 | 0 | 3,287 | 3,287 |
| unknown:sat-budget | 1,381 | 1,393 | 4,244 | 4,131 |
| unknown:str-indexof-replace | 80 | 80 | 26,283 | 26,283 |
| unknown:str-int-conv | 0 | 0 | 1,616 | 1,616 |
| unknown:str-model-rejected | 970 | 311 | 3,114 | 2,049 |
| unknown:str-predicate-polarity | 0 | 0 | 16,016 | 16,016 |
| unknown:str-regex | 343 | 343 | 26 | 26 |
| unknown:str-substr-at | 0 | 0 | 3,359 | 3,359 |
| unknown:theory-refused | 0 | 0 | 35 | 35 |
| unverified | 101 | 140 | 1,315 | 2,200 |
| wrong | 0 | 0 | 0 | 0 |

Changed rows: 2,096 (`target/slice60-after/join.txt`).

| logic | base | after | rows | triage |
| --- | --- | --- | ---: | --- |
| QF_S | unknown:str-model-rejected | correct | 609 | gain (sampled; attributable, as expected) |
| QF_S | unknown:str-model-rejected | unverified | 38 | decided `unsat`, z3 oracle timeout (cross-checked above) |
| QF_S | unknown:str-model-rejected | unknown:sat-budget | 17 | Jiang `slog`; attributable 3/3 |
| QF_S | unknown:sat-budget | unknown:str-model-rejected | 5 | attributable 3/3 (sampled) |
| QF_S | correct | unverified | 2 | noise: identical answer; z3 oracle timeout in after |
| QF_S | timeout | correct | 1 | noise |
| QF_S | timeout | unknown:str-model-rejected | 1 | `automatark-lu/instance02984`: base killed 3/3, after rejected 3/3 (slice 59 had it as noise) |
| QF_S | unknown:str-model-rejected | timeout | 1 | noise |
| QF_S | unverified | correct | 1 | noise: z3 oracle effect |
| QF_SLIA | unknown:str-model-rejected | unverified | 859 | decided (855 `sat`, 4 `unsat`), z3 oracle timeout; 32 sampled, attributable 3/3 |
| QF_SLIA | unknown:str-model-rejected | correct | 308 | gain |
| QF_SLIA | unknown:sat-budget | unknown:str-model-rejected | 128 | Norn; attributable 3/3 (sampled) |
| QF_SLIA | correct | unverified | 55 | noise: identical `sat`; z3 oracle timeout in after |
| QF_SLIA | unverified | correct | 29 | noise: z3 oracle effect |
| QF_SLIA | unknown:str-model-rejected | unknown:sat-budget | 21 | Norn; attributable 3/3 |
| QF_SLIA | unknown:sat-budget | correct | 10 | Norn HammingDistance gain |
| QF_SLIA | unknown:str-model-rejected | timeout | 6 | stringfuzz `generated`: 5 noise, 1 attributable (`regex-big-00183-7`, after killed 3/3) |
| QF_SLIA | correct | unknown:sat-budget | 3 | **attributable** (criterion 3) |
| QF_SLIA | correct | unknown:str-model-rejected | 1 | **attributable** (criterion 3) |
| QF_SLIA | timeout | unknown:sat-budget | 1 | noise |

**The `unverified` movement.** The 87 `correct ↔ unverified` rows give
byte-identical shinri answers in both runs. Only the z3 oracle changed: it
timed out in after on 57 rows and in base on 30. The real increase in
`unverified` comes from the 897 rows that are newly decided but on which z3
times out:
- 855 `sat` rows: 853 stringfuzz `generated` (regexbig 413, regexpair 362,
  regexsmall 78) and 2 stringfuzz `transformed/amazon`;
- 42 `unsat` rows (cross-checked above).

**Unknown ↔ unknown churn.** 133 rows go `sat-budget → str-model-rejected`:
Norn HammingDistance 122, StringReplace 4, `ab` 2, Jiang `slog` 5. Another
38 go the other way: Norn HammingDistance 19, Jiang `slog` 17,
StringReplace 2. Every sampled row in this churn reproduces 3/3. It is a
real effect of the coarser Rule-E partition on these families, not noise,
but neither direction loses a verdict.

### `fence_detail` movement (rows `unknown:str-model-rejected`, string runs)

| tag | base | after |
| --- | ---: | ---: |
| `violated:memb@not-needed` | 2,252 | 525 |
| `violated:bool@not-needed` | 594 | 594 |
| `violated:word-eq@rejected` | 479 | 479 |
| `violated:not-word-eq@not-needed` | 352 | 352 |
| `violated:len-arith@not-needed` | 242 | 242 |
| `unevaluable:other:uf@adopted` | 111 | 111 |
| `violated:not-memb@not-needed` | 19 | 18 |
| `violated:memb@adopted` | 16 | 20 |
| `violated:bool@rejected` | 17 | 17 |
| `violated:not-bool@adopted` | 2 | 2 |

`violated:memb@not-needed` is no longer the largest tag.
`violated:bool@not-needed` (594) now outranks it.

### Base `violated:memb@not-needed` rows, by family and after verdict

| family | rows | correct | unverified | still tagged | other |
| --- | ---: | ---: | ---: | ---: | --- |
| automatark-lu | 648 | 609 | 38 | 0 | 1 timeout |
| stringfuzz `generated/regexbig` | 493 | 75 | 413 | 0 | 5 timeout |
| stringfuzz `generated/regexpair` | 394 | 31 | 362 | 0 | 1 timeout |
| Norn HammingDistance | 326 | 0 | 0 | 307 | 19 sat-budget |
| stringfuzz `generated/regexsmall` | 251 | 173 | 78 | 0 | |
| Jiang `slog` | 44 | 0 | 0 | 27 | 17 sat-budget |
| stringfuzz `transformed/z3str2` | 41 | 11 | 0 | 30 | |
| Norn StringReplace | 22 | 0 | 0 | 20 | 2 sat-budget |
| stringfuzz `transformed/amazon` | 16 | 14 | 2 | 0 | |
| denghang | 9 | 4 | 4 | 1 | |
| Norn `ab` | 6 | 0 | 0 | 6 | |
| Norn ChunkSplit | 2 | 0 | 0 | 2 | |

Rows that moved to `correct`, by base corpus status: `unsat` 310, `sat` 289,
unknown (z3-confirmed) 318.

The 525 rows still tagged after the change:

| family | rows |
| --- | ---: |
| Norn HammingDistance | 431 |
| stringfuzz `transformed/z3str2` (28 of them `regex-035-*`, unchanged) | 30 |
| Jiang `slog` | 28 |
| Norn StringReplace | 24 |
| Norn `ab` | 8 |
| Norn ChunkSplit | 2 |
| automatark | 1 |
| denghang | 1 |

129 of the 525 came in from base `sat-budget`.

### Neutrality sample (seven other logics, 2,000 rows)

| logic | base | after | rows | triage |
| --- | --- | --- | ---: | --- |
| QF_BVFP | timeout | correct | 1 | noise: `unsat` from both binaries 3/3 |
| QF_UF | correct | timeout | 1 | noise: `unsat` from both binaries 3/3 (`qg5/gensys_icl324`) |
| QF_UFLIA | timeout | oom | 1 | noise: allocation failure from both binaries (base 1 OOM + 2 kills, after 3 OOM) |
| QF_UFLRA | timeout | parse-error | 1 | noise: `sat` from both binaries 3/3 |

0 `wrong`.

## Triage

Files: `target/slice60-after/{triage-in.tsv,triage.tsv,triage-disp.txt,triage-summary.txt}`.

Method: 3 runs per binary, interleaved, using the bench's command line on
cores 12–23 with nothing else running. Rows ran 6 at a time in parallel, as
in slice 59.

Selection: 239 rows.
- There are 1,173 non-gain rows, which is more than 200. Every small
  transition stratum was triaged in full, including every `correct → *` row
  and every sample row.
- The two large strata were sampled instead: 32 rows each, seeded
  (`random.Random(60)`) and stratified by family. They are
  `str-model-rejected → unverified` (897 rows) and
  `sat-budget → str-model-rejected` (133 rows).
- That makes 207 non-gain rows. The brief's stratified gain sample adds 32
  (4 from each of 8 families).

| transition | rows | noise | attributable |
| --- | ---: | ---: | ---: |
| gain (`unknown:* → correct`) | 32 | 0 | 32 (expected) |
| `correct → unverified` | 57 | 57 | 0 |
| `unverified → correct` | 30 | 30 | 0 |
| `correct → unknown:sat-budget` | 3 | 0 | **3** |
| `correct → unknown:str-model-rejected` | 1 | 0 | **1** |
| `correct → timeout` (sample) | 1 | 1 | 0 |
| `str-model-rejected → unverified` | 32 (of 897) | 0 | 32 |
| `sat-budget → str-model-rejected` | 32 (of 133) | 0 | 32 |
| `str-model-rejected → sat-budget` | 38 | 0 | 38 |
| `str-model-rejected → timeout` | 7 | 6 | 1 |
| `timeout → str-model-rejected` | 1 | 0 | 1 |
| `timeout → correct` | 2 | 2 | 0 |
| `timeout → sat-budget`, `→ oom`, `→ parse-error` | 3 | 3 | 0 |

Wrong answers: 0. Attributable `correct → non-correct`: 4 (criterion 3).
Attributable sample rows: 0.

## Caller attribution

I used a throwaway trace build of `4a9e656` with the brief's three
`eprintln!`s:
- `seed`, in `memb_seeds`;
- `empty-conflict`, before the slice-28 conflict;
- the Rule-E class count, after `next_classes`.

The build was reverted with `git checkout -- crates`; afterwards
`git status --short crates` printed nothing. It ran on a `random.Random(60)`
sample of 40 gain rows from the string run
(`target/slice60-after/attribution.tsv`).

| caller | rows | verdict |
| --- | ---: | --- |
| witness (`seed`) | 23 | `sat` |
| witness + Rule-E (`seed` plus 4 `rule-e` splits; `norn-benchmark-147`, base `sat-budget`) | 1 | `sat` |
| emptiness conflict (`empty-conflict`) | 16 | `unsat` |
| Rule-E only | 0 | |

By family:

| family | rows | callers |
| --- | ---: | --- |
| automatark | 23 | 9 `sat` via witness, 14 `unsat` via emptiness |
| stringfuzz `generated` | 13 | all witness |
| z3str2 | 2 | both emptiness, including the slice-59 representative `regex-010-reverse-multiply-fuzz` |
| amazon | 1 | witness |
| Norn | 1 | witness + Rule-E |

I skipped the optional base-code Rule-E class counts, because no sampled row
is Rule-E-only.

## Timing

Method: serial and interleaved, pinned to core 12, with nothing else running
on cores 12–23. The script is `target/slice60-after/timing.py`, the brief's
script run three times (`timing.txt`, `timing-rerun2.txt`,
`timing-rerun3.txt`). It samples with `random.Random(60)`, so all three
passes use the same 150 rows per group.

| group | pass 1 | pass 2 | pass 3 | pooled base → after | pooled ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| QF_S both-`correct` | 0.743 (1.90 → 1.41 s) | 0.816 (1.85 → 1.51 s) | 0.828 (1.74 → 1.44 s) | 5.49 → 4.36 s | **0.794** |
| QF_SLIA both-`correct` | 0.772 (1.98 → 1.53 s) | 0.733 (1.92 → 1.41 s) | 0.709 (1.90 → 1.35 s) | 5.80 → 4.29 s | **0.740** |
| newly-`correct` (not gated) | 10.684 (2.79 → 29.77 s) | 11.342 (2.69 → 30.46 s) | 11.323 (2.65 → 30.05 s) | 8.13 → 90.28 s | 11.10 |

**Both gated groups land outside ±5% in every pass, on the faster side.**
By the letter of the criterion this is a FAIL.
- **Not an ordering effect.** The brief's loop runs base before after on
  each row. A diagnostic pass with the order swapped (`timing-swapped.txt`)
  still gives 0.868 (QF_S) and 0.746 (QF_SLIA).
- **Plausible cause:** fewer, coarser classes mean fewer derivatives per step
  in every caller. Spec §4.5 anticipated this ("No slowdown is expected").
- **Bench `wall_ms` is not comparable.** Median / p90 on both-`correct` rows
  is QF_S 23 / 75 → 25 / 60 ms and QF_SLIA 11 / 51 → 15 / 47 ms, but the two
  runs shared the machine differently.

**Newly-`correct` rows** (`timing-newly-correct-rows.txt`): these rows used
to fail fast and now do real work.
- The per-row median is 9 ms.
- The total is dominated by stringfuzz `generated` `sat` rows, whose witness
  search takes up to 2.7 s. The worst is `regex-big-00071-2`, which reached
  the fence in 8 ms in base.
- Of the 31.7 s total: regexsmall 15.1 s, regexbig 10.1 s, regexpair 4.8 s.

The slowdown is reproducible. It is reported, not gated: these rows had no
answer before.

## Class 1: what is left

525 rows remain. I traced 5 of them, chosen with `random.Random(60)`. All 5
are Norn HammingDistance: `norn-benchmark-617`, `531`, `1215`, `488`, `396`.

What the trace shows:
- In every row the witness search **does** seed the bare-variable
  memberships (1–2 `seed` lines).
- Rule-E unfolds with 1–6 classes per split, and no cap is hit.
- The failing memberships have **concat subjects**, such as
  `(str.++ var_6 "z" var_7)`. Each operand is seeded against its own bare
  membership (`var_7 ∈ [a-u]*`). Nothing chooses the operands *jointly*
  against the concat-subject regex.
- z3 (`-T:20`) answers `sat` on 4 rows and `unsat` on `617`.

So the class-1 remainder is no longer a cap problem. It is the
concat-subject shape:
- Norn HammingDistance, StringReplace, `ab` and ChunkSplit (465 rows):
  operands are seeded but jointly inconsistent.
- The `regex-035-*` sub-bucket (28 rows): a free operand is never seeded.
- Jiang `slog` (28 rows): not sampled.

## What changed versus the spec

1. **Criterion 3 FAIL, accepted by controller ruling, pending owner
   decision.** 4 attributable Norn HammingDistance rows go
   `correct → unknown`, caused by the Rule-E partition change. The slice
   continues with no code change. The PR does not merge without the owner's
   decision.
2. **Criterion 4 FAIL on the faster side.** Pooled ratios are 0.794 (QF_S)
   and 0.740 (QF_SLIA). Read by intent (no slowdown), the result is a
   speed-up; read by the letter (±5%), it fails. Flagged for the owner.
3. **The `slice60_probes` shared-member `sat` sibling is two `re.+` plus one
   `re.*` membership**, not three `re.+` as spec §7.2 says.
4. **Oracle z3 timeouts.** `head_classes_oracle` uses z3 `-T:3` for
   generated scripts and `-T:20` for probes and witness re-checks; the spec
   implied a single z3 limit.
   - A shinri `unsat` that z3 does not confirm because it timed out **fails**
     the test. That is stricter than the spec's "any `sat`/`unsat` must
     agree".
   - Last run tally: 65 `sat`, 77 `unsat`, 58 `unknown`, 37 z3 timeouts. The
     "z3 timeouts" tally also counts genuine z3 `unknown` answers.
5. **Rule-E coverage comes from a unit test, not the oracle.** The test is
   `memb::tests::rule_e_long_literal_head_splits_not_fenced`: RED on the
   `aab0dfd` `regex.rs`, GREEN on HEAD. The oracle's `(str.++ x y)` scripts
   never reached a decided answer through Rule-E: 0 `sat`, and 3 `unsat`
   from length conflicts.
6. **Benchmarked commit vs HEAD.** The bench ran `4a9e656`. HEAD `0e39c39`
   adds only the Rule-E unit test and comments, so ci at HEAD counts 1769
   tests (1768 + 1).
7. **Triage sampling.** With 1,173 non-gain rows (more than 200), every
   small stratum was triaged in full, including every `correct → *` row and
   every sample row. The two large strata got 32 seeded, family-stratified
   rows each: 207 non-gain rows plus 32 gain rows. Rows ran 6 in parallel,
   as in slice 59.
8. **Extra gate: unsat cross-check** (controller ruling). The 42 new
   `unverified` `unsat` rows ran under z3 `-T:120` and cvc5
   `--tlimit=120000`: 0 `sat`, 36 confirmed, 6 unconfirmed.
9. **Timing diagnostics beyond the brief:** a pass with after run first, and
   per-row timings for newly-`correct` rows.
10. **Caller attribution** also recorded each row's verdict. It ran on cores
    0–11 while triage occupied 12–23.

## Gates

From `target/slice60-gates.txt`, measured at `4a9e656`:

- `mise run ci`: exit 0. nextest 1768 run / 1768 passed / 6 skipped
  (834.6 s).
- Oracle suite (`cargo nextest run -p shinri-solver --features oracle`):
  831 run / 831 passed / 2 skipped (3,474.8 s). The discovered count is
  non-zero.
- Wide-head pins: 3 run / 3 passed.

## Queued for the next slice

The list is ordered. Items 1–6 are new and come from this run. After them,
slice-59 queue items 2 onward and their carried lists follow verbatim
(slice-59 item 1 is this slice).

**Re-ranks:**
- Item 1 is new and placed first by controller ruling.
- Items 2–3 split class 1's remainder by shape, as spec §9 asks.
- On the after run's counts, `violated:bool@not-needed` (594 rows, slice-59
  items 2–3) now outranks `violated:memb@not-needed` (525 rows). I kept
  class 1's remainder ahead of it for two reasons: the brief orders it that
  way, and 465 of its rows are one Norn shape. The owner may swap them.
- Carried items keep their relative order.

1. **Rule-E search-order regressions on Norn HammingDistance (4 rows).**
   `norn-benchmark-312`, `322`, `362` and `454` go from `correct` to
   `unknown` (3 `sat-budget`, 1 `str-model-rejected`), reproducing 3/3. The
   cause is the coarser Rule-E partition changing the SAT search over the
   split atoms.

   Candidate fixes:
   - (a) Spec §3 approach 2: give Rule-E its own partition that keeps the
     full pre-slice-60 cut set, while the witness search and emptiness keep
     `head_bounds`.
   - (b) A Rule-E variant that keeps the full partition only when it fits the
     cap.
   - (c) A disjunct-ordering fix that makes Rule-E's disjunct order
     independent of the partition's granularity.

   **Hypothesis to test, not a fact.** Caller attribution found no
   Rule-E-only gain among the 40 sampled gain rows (24 witness, 16
   emptiness), so (a) would likely keep most of the 917 gains. But the
   sampled Norn gain (`norn-benchmark-147`, `sat-budget → sat`) shows Rule-E
   splits, and so may the other 9 Norn gains. Approach (a) may lose those,
   so measure the net effect on Norn.

   The same mechanism drives the unknown ↔ unknown churn: 133 rows
   `sat-budget → str-model-rejected` and 38 the other way, in Norn and Jiang
   `slog`, all reproducible. The bench should report that churn too.
2. **Class 1 remainder: concat-subject memberships whose operands are
   seeded but jointly inconsistent (Norn, about 465 of the 525 rows).** Each
   operand of `(str.++ var_6 "z" var_7) ∈ R` is seeded only against its own
   bare membership; nothing chooses them jointly against `R`. The 5 traced
   rows hit no cap. z3: 4 `sat`, 1 `unsat`. Reproducer:
   `QF_SLIA/2015-Norn/HammingDistance/norn-benchmark-531.smt2` (z3 `sat`).
   Needs a joint seed for a concat subject, for example a witness search
   over `R` that respects each operand's own language.
3. **The `regex-035-*` unseeded-concat-operand sub-bucket (28 rows,
   unchanged).** Reproducer:
   `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-035-reverse-fuzz.smt2`
   (869 B, z3 `sat`). It needs the same kind of fix as item 2: seed a free
   operand of a membership subject.
4. **Concat-subject memberships with a provably empty intersection stay
   `unknown`** (final-review queue candidate). Example:
   `(str.++ x y) ∈ L40+ ∩ (bba)+` answers `unknown` on both base and after.
   - The slice-28 emptiness block groups memberships by the raw subject
     `TermId` and fires only when there are ≥ 2 of them.
   - The final review found that concat-subject hand cases stay `unknown` on
     both binaries. The oracle's `(str.++ x y)` scripts reach `unsat` only
     through length conflicts.
   - Needs a check of why the emptiness conflict does not fire on a shared
     concat subject: the key normalisation, or the shape never reaching the
     block.
5. **Oracle coverage for decided-but-unverified rows.** 897 rows are newly
   decided while the z3 oracle times out at 20 s: 855 `sat` (853
   stringfuzz `generated`, 2 `transformed/amazon`) and 42 `unsat`. Of the 42 `unsat`, 6 automatark rows
   stay unconfirmed after z3 `-T:120` and cvc5 `--tlimit=120000`
   (`instance06362`, `10317`, `10696`, `13032`, `15041`, `15868`). Options:
   enable the bench's `cvc5` oracle column (cvc5 confirmed 36 of the 42),
   and/or re-check `sat` witnesses with an independent evaluator.
6. **Witness search cost on newly decided stringfuzz `generated` rows.** Up
   to 2.7 s per row (`regex-big-00071-2`). Newly-`correct` rows take 11×
   longer than base's fast fence, although their median is 9 ms. Measure
   whether `search_word` at the model length dominates. A cheaper first
   try, such as the shortest word when the length is free, may help.

From the slice-59 report's queue, item 2 onward, verbatim (its item 1 is
this slice):

2. **Fix the class-2 tag: `bool` is a mislabelled Int equality (594 rows).**
   Lowering turns every Int `=` into `(and (= a b) (<= a b) (>= a b))`, and
   `violated` mode names the top-level lowered assertion, so a violated
   `len x = k` is tagged `violated:bool`. Either descend, in `violated`
   mode, to the first `Some(false)` conjunct of a top-level `and` (as the
   `unevaluable` leaf search already does), or recognise the lowered
   Int-equality triple as `len-arith`. **This is a deliberate tag rename
   against the slice-59 baseline**: the 594 class-2 rows (and any other
   lowered-`and` rows) will move to another tag, so the next run's per-tag
   comparison has to account for the rename and not count it as movement. No
   code changed in slice 59 (ruling).
3. **Length/membership conflict (class 2, 594 rows).** When the arith model
   fixes `len(x) = k` and `x ∈ R` has no word of length `k` (an exact,
   uncapped search), emit a conflict (or a length lemma) instead of
   reaching SAT. z3 says `unsat` on 39/40 sampled rows. Reproducer:
   `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-017-graft-reverse-graft.smt2`
   (`x ∈ (BA)*`, `len x = 5`). Note: the tag reads `bool` because the
   lowering wraps the Int equality in an `and` (item 2).
4. **Word-equation model rebuild: constant-head/tail strip and minted length
   links (class 3, 479 rows).** Constant head and tail on both sides of an
   input equation that is never split (woorpje `track01`):
   `QF_S/20230329-woorpje-lu/track01/01_track_86.smt2`. Minted members whose
   values disagree with their class (22/40 sampled; a length mismatch is
   confirmed on this row only):
   `QF_S/20230329-woorpje-lu/track01/01_track_154.smt2`. On the membership
   path, the guards `rf2`/`rf3`/`g1` need the tail of a pinned prefix concat
   seeded from the regex's derivative by the head. These absorb the parked
   approach-2 parts that now have reproducers. The cited deep NF on the
   word-equation path stays parked (no reproducer).

Not ranked above, for reference: `violated:not-word-eq@not-needed` (352,
stringfuzz `transformed`), `violated:len-arith@not-needed` (242), and
`unevaluable:other:uf@adopted` (111, Jiang `slent`). In the reproducer
`slent_kaluza_575_sink.smt2`, the undecided leaf is the declared 0-ary Bool
constant `T_SELECT_2`, inside `(= T_SELECT_2 (not (= PCTEMP_LHS_2 (- 1))))`
(the other side evaluates to `true`), and again in `(assert T_SELECT_2)`.
`eval_bool` returns `None` for any non-builtin application, so it never
reads a Bool constant's value. The `other:uf` kind covers declared Bool
constants as well as UF applications. Reading a 0-ary Bool constant from
the model (`ModelVal::Bool`; I did not check that the gate's model holds
it) may be a narrow, cheap evaluator fix behind this class's rows. Only the
reproducer was checked.

From the slice-58 report's queue, item 2 onward, verbatim (its item 1 is
this slice):

2. **Bare-E and `Not(Eq)` arm removal — possibly unblocked.**
   `translate-rotate-fuzz` was the smallest reproducer of the order
   sensitivity that blocked it. Re-run the R6 probes
   (`slice33_probes::probe_c_len_zero_var`,
   `script_e2e::user_pfx_name_declared_before_any_mint_still_works`) with
   bare-E applied, in that slice.
3. **Suffix analogue of G′** (reverse derivative over a member's constant
   tail), only if the classification shows suffix shapes.

Annotations (not part of the copied text):

- Item 2 (slice 58): `translate-rotate-fuzz` now answers `unsat` (G′).
- Item 3 (slice 59): the classification found no suffix shape on the
  membership path (see *Parked items*). Its condition is not met, so it
  stays parked with no reproducer.

3. **Axiom memory measurement** (slice-53 carry).
4. **Solver gate composes concats before reading stored values (slice 57
   follow-up, its own measured slice).** The solver gate's `eval_str_val`
   reads a concat's stored value before composing its operands. Make the
   gate compose first. That leaves a narrow gap for a rebuilt concat with
   an unvalued operand (the strict gate and `concats_consistent` cover the
   rest), and it hides stale-witness defaults today. It changes
   default-path verdicts, which spec §5 forbids in this slice, so it needs
   its own bench measurement.
5. **Slice-57 deferred minors.**
   - After the candidate-trial budget runs out, the walk continues to the
     next top-level check (bounded, result discarded).
   - Spec §7.1's "a rejected candidate leaves no memo entries" is not
     asserted directly.
   - `slice_word` ignores operand class constants (a rebuild is lost, not
     unsound).
   - A composed self-check could in theory newly trigger a rebuild on a
     cyclic, length-inconsistent default model (`sat → unknown` only with
     an unevaluable assertion; not observed on the bench).
   - The `script_e2e` witness check uses byte length (ASCII-only witness
     today).
   - The `slice57_probes.rs` module doc says "every sat case answered
     unknown" at `46d5fd9`, but the len-bounds variants passed.
   - `model.rs:1` has a doc line of about 120 characters.
   - The `diseq_sides` binary assumption is pre-existing and at most a
     spurious rebuild trigger.

Note on the carried slice-52 "`bool_proxy` wrong `sat`" item below: from
slice 57 on, `slice52_probes::bool_proxy` answers a sound `unknown`, not
`sat`. The completeness item (deep-nf propagate to reach `unsat`) remains.

From the slice-56 report's queue, item 3 onwards, verbatim:

3. **V2 evaluator for unregistered query terms.** `get-value` prints `?` for
   built-in applications over unregistered terms (e.g. `(+ a 1)`, e1).
4. **Quoted declarations that shadow theory symbols.** The parser accepts
   declarations that shadow theory symbols or `true`/`false` via quoting
   (`(declare-fun |+| (Int) Int)` echoes `(+ x)`, which re-parses as builtin
   `+`; `|true|` prints `(define-fun true () Int 0)`). Reject such
   declarations (threat-model surface).
5. **AGENTS.md >5 min slow tests.** `shinri-fp` float32 suites take up to
   507 s on the blocking tier (pre-existing); ignore or split them per the
   test-tier rules.
6. **Slice-54 queue, carried** minus the two `get-value` items and the
   `get-model` quoting item, which slice 55 closed. Wording below is
   slice 54's; "this slice" there means slice 54.

- **`clippy --features oracle` under Rust 1.99.** Pre-existing oracle test
  files fail it (18 errors in `qfs_differential` measured on this branch, see
  Gates; slice 54 recorded 32 errors in 5 files). Fix them, then add the
  `--features oracle` clippy to `mise run lint`. Also in the queue:
  `nary_arith_oracle.rs`'s `raw_recv().expect(..)` accepts a z3 `(error ..)`
  ack (the same hole fixed in `bool_arg_oracle.rs` here); it is pre-existing
  and was left untouched.
- **Harness: a resume is refused when the checkout moved.** The fixture
  check compares the checkout sha, so a base run interrupted after a commit
  cannot be resumed under its run-id (this slice's two-leg base run).
  Either record the binary's md5 as the identity for `--solver` runs, or
  launch long runs detached (as slice 53's ruling R1 did) so the 2 h tool
  limit never applies.
- **No corpus row exercises the fix (slice 54).** Only 5 local files mint a proxy, and
  they were already `correct`. The slice's evidence is the probes and the
  oracle. A wider corpus (e.g. QF_AUFLIA / UFDT logics) would be needed for
  a bench-level signal. The same holds for slice 56: no changed row declares a
  Bool-argument function (0 of 89; 105 QF_UF files corpus-wide, 0 in QF_DT,
  QF_UFLIA, QF_UFLRA, single-line-regex heuristic).

From spec §9:

- QF_UFBV / FP-path Bool arguments: blast a proxy as a 1-bit word instead of
  fencing (`bv_stage::uf_args_supported` rejects every Bool argument; pinned
  by `fence_pin_ufbv_bool_argument_stays_unknown`).
- Bool-element arrays (s3, s4; pinned by the two `fence_pin_bool_array_*`
  probes).

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
  Wisa final-check blow-up; the
  `Owner::Shared` definitional merge; `pending` is not backtracked; the
  blocksworld re-index churn measurement; the `blast_word` panic bucket.
- ~~Not re-measured since the baseline: `wrong` rows in QF_LIA (calypto, 2),
  QF_LRA (keymaera, 2), QF_BVFP (ramalho, 1).~~ **Closed by slice 53**
  (all five `wrong → correct`; not this slice's credit).
- Harness nit (carried): the fixture header records the checkout HEAD, not
  the binary's commit. In slice 54 this applies to the base run (above: the recorded sha is
  the moved checkout, the binary was built at `b59f115`); the carried nit is
  about the harness in general, not only that run.

Test-tier note (carried): the unfiltered oracle suite is dominated by
`fp_oracle differential_qf_fp_rem` (~25–33 min), over the 5 min rule; it is an
existing test, not part of this slice.

## References

- Spec: `docs/superpowers/specs/2026-10-04-shinri-slice60-head-classes-design.md`
- Plan: `docs/superpowers/plans/2026-10-04-shinri-slice60-head-classes.md`
- Slice-59 report: `docs/superpowers/research/2026-10-04-smtlib-2024-slice59-model-rejected-classes-report.md`
- Evidence (not committed): `target/slice60-gates.txt`; `target/slice60-{base,after}/{md5.txt,commit.txt,started.txt,finished.txt}`; `target/slice60-base/probes.txt`;
  `target/slice60-after/{join.txt,changed.tsv,triage-in.tsv,triage.tsv,triage-disp.txt,triage-summary.txt,unsat-crosscheck.tsv,attr-in.txt,attribution.tsv,class1-rem-in.txt,timing.txt,timing-rerun2.txt,timing-rerun3.txt,timing-swapped.txt,timing-newly-correct-rows.txt}`;
  `/workspace/bench/results/slice60{,-base,-sample,-base-sample}/`

## Follow-up: Rule-E full-partition variant (56997aa)

### What changed and why

Approach 1 failed criterion 3 on 4 Norn HammingDistance rows (`312`, `322`,
`362`, `454`). In those rows only Rule-E ran the coarser head-only partition,
and that changed the SAT search over the split atoms (see *Criterion 3: the
four regressions*). The owner approved a variant of queue item 1's
candidate (b): Rule-E prefers the full partition when it fits the cap, and
falls back to head-only past it.

- `regex::rule_e_classes` (new): cut Σ at the bounds of **every** `Range`
  node (`range_bounds`, which is back), and use that partition if it is
  within `CLASS_SPLIT_CAP`. Otherwise fall back to the head-only
  `next_classes`. It returns `None` (fence) only when both are over the cap.
- `memb.rs` Rule-E calls `rule_e_classes` instead of `next_classes`.
- The witness search (`search_word`, `search_shortest`) and the emptiness
  conflict (`language_empty`) keep the head-only `next_classes`, unchanged
  from approach 1.
- Both partitions are exact (`deriv` is uniform per class). Where the full
  partition fits, Rule-E reproduces the pre-slice-60 disjunct structure,
  and with it the SAT search order. Where it does not fit, Rule-E no longer
  fences on long literals.

Gates at `56997aa` (`target/slice60b-gates.txt`): ci exit 0, 1773 run /
1773 passed / 6 skipped. That is 1768 + 1 fix-wave `memb` test + 4
`rule_e_classes` tests. Oracle `--features oracle`: 831 run / 831 passed /
2 skipped; the discovered count is non-zero.

### Runs

| run | solver | md5 | started | finished | rows |
| --- | --- | --- | --- | --- | ---: |
| `bench/results/slice60b/` | `target/slice60b-after/shinri` (`56997aa`) | `6109b2a0266510f2084dab2df1e60240` | 2026-10-05T06:34:28Z | (string leg ends when the sample leg starts, 09:14:12Z) | 103,335 |
| `bench/results/slice60b-sample/` | same | same | 2026-10-05T09:14:12Z | 2026-10-05T09:33:23Z | 2,000 |

- Same flags as the other runs: `--timeout 20 --mem-mb 3072 --jobs 6`,
  cores 12–23.
- The row sets match base and approach 1. The fixture `sha` is
  `56997aaacd77` on both runs.
- Base is unchanged: `slice60-base{,-sample}` (`aab0dfd`, md5
  `cf6f6b2f…`).
- **Host load.** Processes outside this container loaded the host heavily
  during the variant run and during this analysis. At 09:34 UTC the load
  average was about 83 on 24 cores. `uptime` readings are in
  `target/slice60b-after/{triage-uptime-before,triage-uptime-after,crosscheck-uptime-before,crosscheck-uptime-after}.txt`
  and `timing-load.log`.

Commands, in addition to *Commands* above:

```bash
# reports
for id in slice60b slice60b-sample; do BENCH_RUN_ID=$id mise run bench-report; done
# join: Task 5 Step 3's script, run for base -> variant and approach 1 -> variant
python3 target/slice60b-after/join.py   # -> join.txt, changed.tsv (base -> variant rows)
# triage: Task 5 Step 4's per-row command, with target/slice60b-after/shinri as the after binary
tr '\t' ' ' < target/slice60b-after/triage-in.tsv | xargs -P6 -L1 target/slice60b-after/triage-row.sh > target/slice60b-after/triage.tsv
python3 target/slice60b-after/triage_disp.py   # -> triage-disp.txt, triage-summary.txt
# unsat cross-check, 5 rows in parallel on cores 13-23 (core 12 kept for timing)
xargs -P5 -L1 target/slice60b-after/crosscheck-row.sh < target/slice60b-after/unsat-crosscheck-in.txt > target/slice60b-after/unsat-crosscheck.tsv
# timing: Task 5 Step 6's script with target/slice60b-after/shinri and runs slice60b,
# gated on the 1-min load being <= 24 (timing-watch.sh)
```

### Success criteria, base → variant

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | **PASS** | 0 `wrong` rows in `slice60b` and `slice60b-sample`. 0 `sat` ↔ `unsat` flips against base or against approach 1. Triage made 984 runs over 164 rows: 0 wrong answers, and no row got both `sat` and `unsat`. The unsat cross-check of 371 variant `unverified` `unsat` rows gave 0 `sat` from z3 or cvc5 (see *Unsat cross-check*) |
| 2 | `violated:memb@not-needed` shrinks by ≥ 20% (≥ 450 rows), moving to `correct` | **PASS** | 2,252 → 432. **936** base-tagged rows (41.6%) are now `correct` (approach 1: 917). Another 885 are decided but `unverified` (843 `sat`, 42 `unsat`), and 431 stay tagged |
| 3 | no `correct → non-correct` change that reproduces 3/3 | **PASS** | base → variant has 4 `correct → *` rows, all `correct → unverified`. In each one the variant gives base's answer 3/3 and only the bench's z3 oracle timed out, so all 4 are noise. The 4 Norn rows are `correct` again in the bench and reproduce 3/3 on both binaries (`sat`, `unsat`, `sat`, `sat`) |
| 4 | serial interleaved timing on 150 both-`correct` rows per string logic, within ±5% | **FAIL on the faster side** (as with approach 1) | Pooled over 3 passes: QF_S **0.809** (4.76 → 3.85 s) and QF_SLIA **0.845** (7.30 → 6.17 s). Each pass is in 0.787–0.864. Newly-`correct` rows: 9.36 (10.79 → 100.99 s), reported. See *Timing (variant)* |
| 5 | `mise run ci` green; oracle count ≥ slice 59 + this slice's oracle tests | **PASS** | `target/slice60b-gates.txt` at `56997aa`: ci 1773 / 1773 / 6 skipped; oracle 831 / 831 / 2 skipped |
| 6 | neutrality sample: only non-reproducible timing flips | **PASS** | 37 sample rows changed. All 37 are noise in triage: both binaries got identical results, mostly `killed` 3/3 on both under the host load (table below) |

### Verdict changes, base → variant

`target/slice60b-after/join.txt`. String runs, 1,880 rows changed:

| logic | base | variant | rows |
| --- | --- | --- | ---: |
| QF_S | `unknown:str-model-rejected` | `correct` | 610 |
| QF_S | `unknown:str-model-rejected` | `unverified` | 38 |
| QF_S | `correct` | `unverified` | 1 |
| QF_S | `timeout` | `correct` | 1 |
| QF_S | `timeout` | `unknown:str-model-rejected` | 1 |
| QF_SLIA | `unknown:str-model-rejected` | `correct` | 326 |
| QF_SLIA | `unknown:str-model-rejected` | `unverified` | 847 |
| QF_SLIA | `unverified` | `correct` | 52 |
| QF_SLIA | `correct` | `unverified` | 3 |
| QF_SLIA | `timeout` | `unknown:sat-budget` | 1 |

- **Rows moved to `correct`: 989** (QF_S 611, QF_SLIA 378).
  - 936 were `str-model-rejected` with tag `violated:memb@not-needed`:
    310 with corpus status `unsat`, 289 `sat`, and 337 corpus-unknown with
    z3 agreeing (312 `sat`, 25 `unsat`).
  - 52 were `unverified` in base, where z3 timed out (28 `sat`, 24 `unsat`).
  - 1 was a base `timeout` (automatark `instance07283`, `sat`).
- String `correct` goes 40,913 → **41,898 (+985)**: QF_S 16,057 → 16,667,
  QF_SLIA 24,856 → 25,231. Approach 1 reached 41,810.
- `unknown:str-model-rejected` overall: 4,084 → 2,264 (approach 1: 2,360).
- **No Norn or Jiang `slog` row changes verdict between base and variant**
  (3,003 rows). The 133 + 38 unknown ↔ unknown churn that approach 1 showed
  is gone.
- Moved base-tagged rows by family: automatark 610, regexsmall 163,
  regexbig 89, regexpair 45, amazon 14, z3str2 11, denghang 4.

`fence_detail` (rows `unknown:str-model-rejected`): only
`violated:memb@not-needed` moves, 2,252 → 432. Every other tag has the same
count in base and variant. What remains of the tag: Norn 356, which is
base's Norn count; Jiang `slog` 44, also base's count; z3str2 30, which
includes the 28 `regex-035-*` rows; automatark 1; denghang 1.

Neutrality sample, 37 rows changed:

| logic | base | variant | rows | triage |
| --- | --- | --- | ---: | --- |
| QF_UF | `correct` | `timeout` | 17 | noise: all `qg5`, both binaries `killed` 3/3 |
| QF_UFLIA | `correct` | `timeout` | 4 | noise: both binaries `killed` 3/3 |
| QF_LIA | `oom` | `timeout` | 14 | noise: both binaries `killed` or OOM on every row, with identical results on most |
| QF_BVFP | `timeout` | `correct` | 1 | noise: base `unsat, unsat, killed`, variant `killed` 3/3 |
| QF_UFLRA | `timeout` | `parse-error` | 1 | noise: both binaries `sat` 3/3 |

The approach-1 sample run against approach 1's binary shows the same shape
(`slice60-sample → slice60b-sample`: 16 QF_UF and 4 QF_UFLIA
`correct → timeout`, 15 QF_LIA/QF_UFLIA `oom → timeout`), and the two
binaries differ only in Rule-E. These are load effects on rows near the
20 s limit. Triage cannot show either binary answering them under the
same load.

### Approach 1 → variant

`slice60 → slice60b`: 310 string rows changed (`join.txt`, by family in
`delta.txt`). The sample runs differ on 35 rows, all timeout/OOM movement
as above.

- **Restored: the 4 Norn regressions.** `312`, `322` and `362` go
  `sat-budget → correct`, and `454` goes `str-model-rejected → correct`.
- **Given back: approach 1's 10 Norn HammingDistance gains.** They go
  `correct → unknown:sat-budget`, base's verdict: `norn-benchmark-147`,
  `151`, `315`, `329`, `434`, `442`, `580`, `592`, `828` and `1190` (7
  `sat`, 3 `unsat` in approach 1). Re-run 3× on each binary
  (`givenback-triage.tsv`): approach 1 answers 3/3 and the variant gives
  `sat-budget` 3/3, so all 10 are attributable. HammingDistance is back to
  base's distribution: 165 `correct`, 281 `sat-budget`, 333
  `str-model-rejected`, 15 `theory-refused` (approach 1: 171 / 171 / 437 /
  15). The family's net effect goes from +6 to 0.
- **Unknown ↔ unknown churn is reverted.** Norn: 122 + 4 + 2
  `str-model-rejected → sat-budget`, and 19 + 2 the other way. `slog`:
  17 `sat-budget → str-model-rejected` and 5 the other way.
- **Oracle churn.** 106 rows go `unverified → correct` and 12 go
  `correct → unverified`. Each has the same shinri answer on both runs;
  only the bench's 20 s z3 call finished or timed out. 7 rows go
  `timeout → unverified`.
- **Net:** string `correct` 41,810 → 41,898 (+88) = +4 Norn restored, −10
  Norn given back, +94 oracle churn. 0 `sat` ↔ `unsat` flips.
- **Class 1:** `violated:memb@not-needed` 525 → 432. Norn's 465 tagged rows
  in approach 1 fall back to base's 356. The difference sat in
  `sat-budget`, not in `correct`.

### Triage

Files: `target/slice60b-after/{triage-in.tsv,triage.tsv,triage-disp.txt,triage-summary.txt}`.
Method: Task 5 Step 4's command and noise rule, base binary vs variant
binary, 3 interleaved runs each, on cores 12–23, 6 rows in parallel. Ran
09:35:59Z–09:51:12Z. Load: `70.81, 77.17, 66.99` before and
`87.30, 96.07, 89.68` after; that load came from outside this container.

Selection: 164 rows.
- 981 non-gain rows (944 string + 37 sample), which is more than 200. Every
  small stratum was triaged in full: all 4 `correct → unverified`, all 37
  sample rows, all `timeout → *` rows, and all 52 `unverified → correct`.
- The one large stratum, `str-model-rejected → unverified` (885 rows), got a
  seeded (`random.Random(60)`) family-stratified sample of 32. That makes
  128 non-gain rows.
- 32 stratified gain rows (`unknown:* → correct`).
- The 4 Norn rows, which are `correct → correct` against base.

| transition | rows | noise | attributable |
| --- | ---: | ---: | ---: |
| gain (`unknown:* → correct`) | 32 | 0 | 32 (expected) |
| Norn 312/322/362/454 (`correct → correct`) | 4 | 4 (same answer on both, 3/3) | 0 |
| `correct → unverified` | 4 | 4 | 0 |
| `unverified → correct` | 52 | 52 | 0 |
| `str-model-rejected → unverified` | 32 (of 885) | 1 | 31 |
| `timeout → correct` | 1 | 1 | 0 |
| `timeout → unknown:sat-budget` | 1 | 1 | 0 |
| `timeout → unknown:str-model-rejected` | 1 | 0 | 1 |
| sample `correct → timeout` | 21 | 21 | 0 |
| sample `oom → timeout` | 14 | 14 | 0 |
| sample `timeout → correct`, `→ parse-error` | 2 | 2 | 0 |

- **Wrong answers: 0.** Attributable `correct → non-correct`: 0. Attributable
  sample rows: 0.
- **The 4 Norn rows:** the variant reproduces `correct` 3/3 on each: `312`
  `sat`, `322` `unsat`, `362` `sat`, `454` `sat`. Base gives the same answers.
- **`correct → unverified` (4):** the variant's answer is base's answer 3/3
  on both binaries. The rows are 3 stringfuzz `regexlengths` `sat`
  (`00076-19`, `00076-7`, `00101-22`) and automatark `instance14507`
  `unsat`. All 4 have corpus status unknown. Base's bench z3 agreed with
  that answer; the variant's bench z3 timed out.
- **`→ unverified` in general:** the variant's answer matches the base
  answer wherever base decided, and never contradicts a corpus status. The
  885 `str-model-rejected → unverified` rows are 843 `sat` (model-checked
  by shinri's gate) and 42 `unsat`. 41 of those 42 are rows approach 1
  produced and cross-checked. The 42nd, `instance13119`, is in this
  run's cross-check.
- `timeout → str-model-rejected` (automatark `instance02984`) is
  attributable: base is killed 3/3 and the variant fences 3/3. It is the
  same row and transition as in approach 1, and it is not a `correct` row.

### Unsat cross-check

Scope (the brief): every variant row that is `unverified` with answer
`unsat` and not already in `target/slice60-after/unsat-crosscheck.tsv`.
The variant has 412 such rows. 41 were already cross-checked for approach 1,
which leaves **371**.
- Only 2 of the 371 are new against base. `instance13119` was `timeout` in
  approach 1. `instance14507` is base `correct` (z3 `unsat`).
- The other 369 were already `unverified` `unsat` in base, meaning the
  bench's 20 s z3 timed out on them in every run. They are pre-existing, not
  caused by this slice.
- Of approach 1's 42 rows, 41 are among the variant's 42
  `str-model-rejected → unverified` `unsat` rows. The 42nd variant row is
  `instance13119`. The 42nd approach-1 row (`instance14567`) is `correct`
  in the variant.

Method: z3 4.16 `-T:120` and cvc5 1.4.1 `--tlimit=120000` per row
(`crosscheck-row.sh`), on cores 13–23.
- The first 135 rows ran 5 in parallel. The rest ran 10 in parallel to
  finish sooner.
- Times: 09:52:17Z–12:19:12Z. Load: `81.43, 92.64, 88.93` before and
  `127.21, 118.80, 110.97` after.
- Results: `target/slice60b-after/{unsat-crosscheck.tsv,crosscheck-summary.txt,crosscheck-unconfirmed.txt}`.

| z3 | cvc5 | rows |
| --- | --- | ---: |
| unsat | unsat | 8 |
| timeout | unsat | 204 |
| timeout | timeout | 159 |

- **No `sat` from either solver on any row.**
- Confirmed by at least one solver: 212 (z3 8, cvc5 212).
- Both new-vs-base rows are confirmed: `instance14507` by z3 and cvc5,
  `instance13119` by cvc5.
- By family:

  | family | z3 + cvc5 | cvc5 only | neither |
  | --- | ---: | ---: | ---: |
  | denghang | 4 | 128 | 0 |
  | automatark | 4 | 67 | 23 |
  | Norn | 0 | 8 | 3 |
  | stringfuzz `generated/manyregexes` | 0 | 0 | 73 |
  | stringfuzz `generated/variants` | 0 | 0 | 59 |
  | stringfuzz `generated/regexpair` | 0 | 1 | 1 |

- **Unconfirmed: 159.** All 159 were already `unverified` `unsat` in base.
- The heavy external load may have turned some solver answers into
  timeouts.

### Timing (variant)

Script: `target/slice60b-after/timing.py`. It is Task 5 Step 6's script with
`target/slice60b-after/shinri` as the after binary and `slice60b` as the
after run: serial, interleaved, pinned to core 12, sampled with
`random.Random(60)`.
- The host load stayed far above 24 (the 1-min load peaked at 142) until
  13:47Z. `timing-watch.sh` checked every 5 min (`timing-load.log`) and
  started the passes once the 1-min load was ≤ 24.
- The passes ran 13:47:33Z–13:49:54Z, with 1-min load 17.72 → 15.09. That
  host was below its core count but not idle.

| group | pass 1 | pass 2 | pass 3 | pooled base → variant | pooled ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| QF_S both-`correct` | 0.787 (1.71 → 1.35 s) | 0.807 (1.54 → 1.24 s) | 0.830 (1.51 → 1.26 s) | 4.76 → 3.85 s | **0.809** |
| QF_SLIA both-`correct` | 0.831 (2.60 → 2.16 s) | 0.842 (2.35 → 1.98 s) | 0.864 (2.35 → 2.03 s) | 7.30 → 6.17 s | **0.845** |
| newly-`correct` (not gated) | 9.126 (3.62 → 33.02 s) | 9.587 (3.66 → 35.14 s) | 9.354 (3.51 → 32.83 s) | 10.79 → 100.99 s | 9.36 |

- **Both gated groups land outside ±5% on the faster side in every pass.**
  This is the same pattern as approach 1 (0.794 / 0.740), and the
  controller treated it as met in intent.
- The variant's QF_SLIA speed-up is smaller than approach 1's (0.845
  against 0.740). That fits Rule-E again building the finer full
  partition wherever it fits.
- The both-`correct` and newly-`correct` row sets are drawn against the
  variant run, so they are not the same rows as approach 1's.
- Bench `wall_ms` median / p90 on both-`correct` rows: QF_S 23 / 75 → 16 /
  55 ms; QF_SLIA 11 / 51 → 14 / 51 ms. The runs shared the machine
  differently, so these are not comparable.

### Queue changes

- **Queue item 1 (Rule-E search-order regressions on Norn HammingDistance)
  is resolved by this variant**, which is candidate (b). All 4 rows are
  `correct` again (3/3), and Norn/`slog` match base row for row. Cost: the
  10 Norn gains that approach 1 got from the coarser Rule-E partition are
  given back.
- **Item 2 (class-1 remainder, Norn concat subjects):** the count is now
  about 356 rows (Norn's share of the 432 still tagged), not about 465.
- **Item 5 (oracle coverage):** with the variant, 885 base-tagged rows are
  decided but `unverified` (843 `sat`, 42 `unsat`). The variant's 371 additional `unverified` `unsat` rows have 0 `sat`, and 212 are confirmed by z3 or cvc5 at 120 s. The 159 unconfirmed rows (manyregexes 73, variants 59, automatark 23, Norn 3, regexpair 1) were already `unverified` `unsat` in base, so the slice did not create them. They belong in this item's oracle-coverage work.
- **New candidate:** recover the 10 HammingDistance gains without the 4
  losses. Candidate (c), a disjunct order independent of partition
  granularity, is still open. Lower priority than items 2–4.
- Items 3, 4 and 6 and the carried list are unchanged.

### What changed versus the spec (variant)

1. **Rule-E no longer uses `next_classes`.** Spec §3 approach 1 and §4.3
   say every caller gets the head-only partition. Rule-E now prefers the
   full all-ranges partition (`range_bounds`, which the spec header says is
   deleted, is back) and falls back to head-only only past the cap. This is
   the owner-approved follow-up to the criterion-3 FAIL.
2. **Benchmarked commit:** `56997aa`, which is branch HEAD before this docs
   commit.
3. **Triage under external load.** Load average was 67–96 on 24 cores
   during triage. Sample rows near the 20 s limit were killed on both
   binaries, so their noise classification rests on the two binaries
   agreeing, not on reproducing the base answer.
4. **Unsat cross-check scope.** The brief asked for every variant `unverified` `unsat` row not already checked. That is 371 rows, of which 369 predate this slice (they were already `unverified` `unsat` in base). All were run. Parallelism went from 5 to 10 partway through, to finish sooner under the load.
5. **Timing.** Timing waited about 4 h for the host load to drop. It ran at a 1-min load of 15–18 rather than on an idle host. Criterion 4 is out of band on the faster side, as with approach 1.
