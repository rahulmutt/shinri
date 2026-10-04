# SMT-LIB 2024 re-run — slice 59 (classify the `str-model-rejected` population) — shinri @ 8dbcda9

## Headline

Slice 59 adds a detail tag `<mode>:<kind>@<rebuild>` to the
`str-model-rejected` fence. The tag is computed by the solver, printed as
`detail=` on the `--stats` line, stored in bench rows as `fence_detail`, and
shown in a "Fence detail" report section. The slice is meant to change no
verdicts, and the bench shows none it caused.

- **Population: 4,085 rows** (QF_S 971, QF_SLIA 3,114). The base run had
  4,084; the one extra row is a `timeout → str-model-rejected` timing flip.
  **Mode:** 3,974 `violated`, 111 `unevaluable`. **Rebuild outcome:** 3,460
  `not-needed`, 496 `rejected`, 129 `adopted`, 0 `budget`.
- **Top classes:** 3 tags cover **3,326 / 4,085 rows (81.4%)**:
  1. `violated:memb@not-needed`: 2,253 rows (55.2%)
  2. `violated:bool@not-needed`: 594 rows (14.5%)
  3. `violated:word-eq@rejected`: 479 rows (11.7%)
- **What the top classes are** (40 sampled rows per class, traced offline
  with a throwaway debug build, plus z3 on the same rows):
  1. In class 1, the membership witness search gives up. In 35 of the 36
     sampled bare-variable subjects, the seed search in `memb_seeds` (and the
     emptiness check behind it) stops at `CLASS_SPLIT_CAP` (64) on its first
     step. The variable then keeps a default fill (`"DDDD…"`). The other
     sampled rows are concat subjects whose free operand is never seeded
     (4/40), and one pinned subject that has the slice-58 guard shape (1/40).
  2. Class 2 is a length/membership conflict the engine misses. Its `bool`
     kind is a lowering artifact: every sampled failing assertion is a
     lowered Int equality `(and (= a b) (<= a b) (>= a b))` over `str.len`
     (40/40). No word of the asserted length exists, so the seed falls back to
     the shortest word. z3 says `unsat` on 39 of the 40.
  3. Class 3 is a failed word-equation model rebuild. Sub-buckets: constant
     head/tail equations that are never split (woorpje `track01`, 10/40),
     which a constant-head strip would solve; and leaf classes whose member
     values disagree (24/40). In the traced example (`01_track_154`) the
     minted concat member and the variable also disagree in length, which is
     the shape of missing minted length links. z3 says `sat` on 33 of the 40.
- **Recommended next slice:** class 1. Make the membership witness search
  (`memb_seeds` → `search_word` / `search_shortest`) work past
  `CLASS_SPLIT_CAP`, for example with a lazy first-character choice instead
  of the full partition. Reproducer:
  `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-010-reverse-multiply-fuzz.smt2`
  (976 B). See *Queued for the next slice*.
- **Criteria:** all six PASS. 0 `wrong`. 97 changed rows, all noise in
  triage (582 runs). Every rejected row has a detail and no other row has
  one. Timing is within ±5%: one QF_S pass came out 6.8% faster, and the
  pooled ratio over three passes is inside the band. CI and oracle gates are
  green.

## Commands

Task 0 (controller): branch point, base binary, sample corpus, base runs.

```bash
# base binary from the branch point (crates identical to de96d28), plan Task 0 Step 3
cargo build --release -p shinri-cli -p shinri-bench
cp target/release/shinri target/slice59-base/shinri; cp target/release/shinri-bench target/slice59-base/shinri-bench
# sample corpus: plan Task 0 Step 4 (seed 59, hard links) -> target/slice59-sample-corpus, target/slice59-sample.txt
# base runs: target/slice59-base/launch.sh (detached, setsid nohup)
taskset -c 12-23 target/slice59-base/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --corpus /workspace/bench/corpus --results /workspace/bench/results \
  --solver target/slice59-base/shinri --run-id slice59-base
taskset -c 12-23 target/slice59-base/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --results /workspace/bench/results --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice59-base/shinri --run-id slice59-base-sample
```

Task 5 (controller, `target/slice59-gates.sh`):

```bash
taskset -c 0-11 mise run ci
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle
```

Task 6:

```bash
# Step 2 (controller): target/slice59-after-build.sh, then target/slice59-after/launch.sh
taskset -c 0-11 cargo build --release -p shinri-cli -p shinri-bench   # copied to target/slice59-after/
taskset -c 12-23 target/slice59-after/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --corpus /workspace/bench/corpus --results /workspace/bench/results \
  --solver target/slice59-after/shinri --run-id slice59
taskset -c 12-23 target/slice59-after/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --results /workspace/bench/results --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice59-after/shinri --run-id slice59-sample
# Step 3: reports (ruling R8) and the join
target/slice59-after/shinri-bench report /workspace/bench/results/<id>   # for the four run ids
python3 target/slice59-after/step3.py      # -> step3.txt, changed.tsv
python3 target/slice59-after/step3b.py     # unverified / oracle breakdown -> step3b.txt
# Step 4: triage, every changed row, 3 runs per binary interleaved, 6 rows in parallel
tr '\t' '\n' < target/slice59-after/changed.tsv | xargs -d '\n' -n 5 -P 6 target/slice59-after/triage-row.sh > target/slice59-after/triage.tsv
#   triage-row.sh runs, per binary and run:
#   taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats $root/$p
python3 target/slice59-after/triage_disp.py   # -> triage-disp.txt
# Step 5: target/slice59-after/timing.py (brief script; taskset -c 12, random.Random(59)), run 3 times
# Step 6: target/slice59-after/step6.py -> classes.txt; classes_table.py -> classes-table.md
# Step 7: target/slice59-after/guards/mk.sh -> guards.txt
# Step 8: throwaway debug build (CARGO_TARGET_DIR=target/slice59-debug), reverted with git checkout -- crates
python3 target/slice59-after/shapes_sample.py 40   # -> shapes_sample.txt
sh target/slice59-after/z3_sample.sh               # -> z3_sample.tsv
python3 target/slice59-after/empt_reasons.py       # -> class1-empt-reasons.txt
```

## Runs

| run | solver | md5 | started | finished | rows |
| --- | --- | --- | --- | --- | ---: |
| `bench/results/slice59-base/` | `target/slice59-base/shinri` (crates `de96d28`, built at `e96ad5d`) | `0c0f16e8fdf3e1c7cb303d8d9c0cf0b0` | 2026-10-04T06:09:43Z | (string leg ends when the sample leg starts, 08:03:12Z) | 103,335 |
| `bench/results/slice59-base-sample/` | same | same | 2026-10-04T08:03:12Z | 2026-10-04T08:20:03Z | 2,000 |
| `bench/results/slice59/` | `target/slice59-after/shinri` (`8dbcda9`) | `cf6f6b2f24215ba31e173ebc0d4dfde9` | 2026-10-04T08:20:58Z | (string leg ends when the sample leg starts, 09:57:43Z) | 103,335 |
| `bench/results/slice59-sample/` | same | same | 2026-10-04T09:57:43Z | 2026-10-04T10:16:28Z | 2,000 |

All four runs used `--timeout 20 --mem-mb 3072 --jobs 6` on cores 12–23.
The string runs cover QF_S (18,940 rows) and QF_SLIA (84,395 rows). The
sample covers QF_BVFP 627, QF_DT 316, QF_LIA 484, QF_LRA 100, QF_UF 273,
QF_UFLIA 100 and QF_UFLRA 100. The base and after row sets are identical.
Each `results.jsonl` has its rows plus one fixture line. The bench's own
md5 matches in each fixture. The base binary's md5 is the same as slice 58's
after binary. That is expected: the slice-58 merge commit `de96d28` has the
same crates.

Harness nit (carried): the fixture `sha` field records the checkout HEAD,
not the commit the binary was built from. `slice59-base-sample` therefore
records `8dbcda9`, because the worktree had moved by then. The md5 is the
authoritative identity.

## Success criteria (spec §8)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | **PASS** | 0 `wrong` rows in all four runs. In triage (97 rows × 6 runs = 582 runs), no row gets both `sat` and `unsat`, and all 418 decided triage runs agree with the row's corpus status, z3 oracle answer and bench answers (`triage_vs_bench.py`: 0 mismatches) |
| 2 | verdict-neutral: every changed row is a non-reproducible timing flip | **PASS** | 74 string rows and 23 sample rows changed. Triage marks all 97 as noise and 0 as attributable: in every row the two binaries agree on at least one run, and in most rows on all three. The 59 `unverified ↔ correct` rows have identical shinri answers in both bench runs; only the z3 oracle result differs (§ Verdict neutrality) |
| 3 | every `unknown:str-model-rejected` row has a non-null `fence_detail`; no other row has one | **PASS** | after: 4,085 rejected rows, 0 missing detail, 0 stray details (string run and sample). Base rows carry no detail (0), as expected for the old binary |
| 4 | serial interleaved timing, 150 rows per string logic and 150 `str-model-rejected` rows, within ±5% | **PASS (pooled; one pass outside on the fast side)** | Pass 1: QF_S 0.932, QF_SLIA 0.971, rejected 0.995. Passes 2 and 3: 0.977 / 0.952 / 1.032 and 0.984 / 0.996 / 1.030. Pooled over the three passes: QF_S 0.964 (5.23 s → 5.04 s), QF_SLIA 0.973 (4.05 s → 3.94 s), rejected 1.018 (6.81 s → 6.93 s). The pass-1 QF_S excursion is *faster* than base, outside the band. See *Timing* |
| 5 | `mise run ci` green; oracle suite passes with the slice-58 count | **PASS (count rises by this slice's tests, ledger ruling)** | `target/slice59-gates.txt`: `mise run ci` exit 0, 1759 tests run / 1759 passed / 6 skipped. Oracle suite `--features oracle`: 825 run / 825 passed / 2 skipped, which is 808 (slice 58) + 17 new `shinri-solver` tests from this slice (15 `model_reject` + 2 `fence_tags`) |
| 6 | named classes cover ≥80% of the population, each with a reproducer | **PASS** | top 3 tags: 3,326 / 4,085 = 81.4%. Each has a smallest reproducer and an offline shape analysis (§ Top classes) |

## Verdict neutrality

### String runs (QF_S + QF_SLIA)

Verdict counts (base → after):

| verdict | QF_S base | QF_S after | QF_SLIA base | QF_SLIA after |
| --- | ---: | ---: | ---: | ---: |
| correct | 16,056 | 16,060 | 24,852 | 24,884 |
| parse-error | 0 | 0 | 195 | 195 |
| timeout | 8 | 6 | 59 | 46 |
| unknown:reglan-decl | 0 | 0 | 3,287 | 3,287 |
| unknown:sat-budget | 1,381 | 1,381 | 4,234 | 4,247 |
| unknown:str-indexof-replace | 80 | 80 | 26,283 | 26,283 |
| unknown:str-int-conv | 0 | 0 | 1,616 | 1,616 |
| unknown:str-model-rejected | 970 | 971 | 3,114 | 3,114 |
| unknown:str-predicate-polarity | 0 | 0 | 16,016 | 16,016 |
| unknown:str-regex | 343 | 343 | 26 | 26 |
| unknown:str-substr-at | 0 | 0 | 3,359 | 3,359 |
| unknown:theory-refused | 0 | 0 | 35 | 35 |
| unverified | 102 | 99 | 1,319 | 1,287 |
| wrong | 0 | 0 | 0 | 0 |

Changed rows (74):

| logic | base | after | rows | triage |
| --- | --- | --- | ---: | --- |
| QF_S | timeout | correct | 1 | noise: `sat` from both binaries 3/3 (`automatark-lu/instance07283`) |
| QF_S | timeout | unknown:str-model-rejected | 1 | noise: each binary gives 2 kills + 1 `str-model-rejected` (`automatark-lu/instance02984`) |
| QF_S | unverified | correct | 3 | noise: same answer on both binaries 3/3; z3 oracle effect |
| QF_SLIA | correct | unverified | 12 | noise: same answer on both binaries 3/3 (11 `unsat`, 1 `sat`); z3 oracle `timeout` in the after run |
| QF_SLIA | timeout | unknown:sat-budget | 13 | noise: `sat-budget` from both binaries 3/3 (Reynolds kaluza `unsat/big/3018`–`3023`, Leetcode `findAnagrams` ×7) |
| QF_SLIA | unverified | correct | 44 | noise: `sat` from both binaries 3/3; z3 oracle effect |

**The `unverified` movement.** A row is `unverified` when shinri decides
it, the corpus status is unknown, and the z3 oracle answers `timeout` or
`unknown`. All 59 `unverified ↔ correct` rows have byte-identical shinri
answers in the two bench runs. Only the oracle's answer changed: 47 rows had
z3 `timeout` in base and an answer in after, and 12 had an answer in base
and `timeout` in after. The final count fell, QF_S 102 → 99 and QF_SLIA
1,319 → 1,287 (1,421 → 1,386 combined).

The controller saw `unverified` looking higher in after mid-run. The
progress lines in `run.log` don't show that. At every common progress mark,
after ≤ base (max after − base = 0; min −49 at row 90,800). A comparison at
equal *wall-clock* times would read differently, because the after run was
faster (it finished the string leg in 1 h 36 min against base's 1 h 53 min).
The base run shared the machine with the Task 5 gates (06:21–07:21Z, cores
0–11).

The oracle's answer *kind* shifted inside `unverified`: z3 `unknown`
(rather than `timeout`) went from 43 to 252 rows. 228 of these rows are
z3 `timeout` in base and z3 `unknown` in after, and 226 of the 228 are
stringfuzz `generated`. Both are oracle-side results. shinri's answers are
identical, and all 228 rows are `unverified` in both runs.

Rows whose shinri answer differs between the bench runs: 15, all
`timeout → unknown` (13 `sat-budget`, 1 `str-model-rejected`) or
`timeout → sat`. In triage, both binaries give the after-run answer on at
least one run.

### Neutrality sample (seven other logics, 2,000 rows)

Changed rows (23), all noise:

| logic | base | after | rows | triage |
| --- | --- | --- | ---: | --- |
| QF_BVFP | correct | timeout | 2 | `unsat` from both binaries 3/3 |
| QF_LIA | correct | timeout | 1 | `sat` from both binaries 3/3 |
| QF_LIA | oom | timeout | 8 | `memory allocation … failed` from both binaries in every run (1 run killed instead) |
| QF_UF | correct | timeout | 6 | both binaries decide in ≥1 run; kills occur on both sides |
| QF_UFLIA | correct | timeout | 2 | `sat` from both binaries 3/3 |
| QF_UFLIA | oom | timeout | 1 | allocation failure from both binaries |
| QF_UFLRA | oom | timeout | 3 | allocation failure from both binaries |

The after-sample run was slower throughout. On both-`correct` rows, the
median `wall_ms` was 12 → 32 on QF_BVFP, 9 → 19 on QF_DT, 65 → 152 on
QF_LIA and 88 → 131.5 on QF_UF. Every flip goes in the slower direction
(`correct → timeout`, or `oom → timeout`, where the time limit is hit before
the memory limit). At 10:21Z, five minutes after the run finished, the host
load average was 52.5 (5 min) / 60.1 (15 min) on 24 cores, so the host was
heavily loaded during that window. Outside the string path, the code change
is an unread `ModelBuilder` field plus `detail=-`. Triage reproduces none
of the flips.

### Triage method

Every changed row was triaged (97 rows, so no sampling): 3 runs per binary,
interleaved, with the bench's command line on cores 12–23. Rows ran 6 in
parallel (the bench's own `--jobs 6`), not serially (see *What changed
versus the spec*). Dispositions are in `target/slice59-after/triage-disp.txt`.
A row is *attributable* if each binary reproduces its own bench verdict 3/3
and the two differ. **Attributable: 0.** Wrong answers: 0.

## Timing

Serial and interleaved, pinned to core 12, nothing else on cores 12–23.
Each group is 150 rows sampled with `random.Random(59)` from rows with the
same verdict in both runs. Script: `target/slice59-after/timing.py`, the
brief's script with absolute corpus/results paths. It was run three times
(`timing.txt`, `timing-rerun2.txt`, `timing-rerun3.txt`).

| group | pass 1 | pass 2 | pass 3 | pooled base → after | pooled ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| QF_S both-`correct` | 0.932 (1.90 → 1.77 s) | 0.977 | 0.984 | 5.23 → 5.04 s | 0.964 |
| QF_SLIA both-`correct` | 0.971 (1.34 → 1.30 s) | 0.952 | 0.996 | 4.05 → 3.94 s | 0.973 |
| both-`str-model-rejected` | 0.995 (2.38 → 2.37 s) | 1.032 | 1.030 | 6.81 → 6.93 s | 1.018 |

Pass 1's QF_S ratio, 0.932, is outside 0.95–1.05 on the *fast* side. The
change cannot speed QF_S up. The classifier runs only on rejected rows, and
the extra stats field appears only with `--stats`, which this timing does
not pass. The two re-runs land at 0.977 and 0.984, so the 150-row sums
(about 11 ms per row, dominated by process start-up) carry about ±5% noise.
The rejected group, which is the path the classifier actually runs on, stays
within 0.995–1.032 in every pass.

Bench `wall_ms` (median / p90):

| rows | base | after |
| --- | ---: | ---: |
| QF_S both-`correct` (16,056) | 16 / 41 ms | 7 / 18 ms |
| QF_SLIA both-`correct` (24,840) | 23 / 69 ms | 15 / 37 ms |
| both `str-model-rejected` (4,084) | 21 / 85 ms | 12 / 40 ms |

The bench medians are lower in after because the base string run shared the
machine with the Task 5 gates. The serial measurement above is the evidence.

## Classes

Population (after run): **4,085** rows. Corpus status: QF_S 447 `sat`,
314 `unsat`, 210 unknown. QF_SLIA: all 3,114 unknown.

- **Mode:** `violated` 3,974; `unevaluable` 111.
- **Rebuild:** `not-needed` 3,460; `rejected` 496; `adopted` 129; `budget` 0.
- **Mode × rebuild:** violated/not-needed 3,460; violated/rejected 496;
  violated/adopted 18; unevaluable/adopted 111. Every `unevaluable` row
  comes from an adopted rebuild, because only an adopted rebuild sets the
  strict gate.

Ranked tags (`target/slice59-after/classes.txt`, `classes-table.md`):

| # | tag | QF_S sat / unsat / unknown | QF_SLIA sat / unsat / unknown | total | cum % | top families |
| ---: | --- | --- | --- | ---: | ---: | --- |
| 1 | `violated:memb@not-needed` | 290 / 310 / 93 | 0 / 0 / 1,560 | 2,253 | 55.2 | automatark-lu 649, stringfuzz `generated/regexbig` 493, stringfuzz `generated/regexpair` 394 |
| 2 | `violated:bool@not-needed` | 0 / 0 / 0 | 0 / 0 / 594 | 594 | 69.7 | stringfuzz `transformed/z3str2` 594 |
| 3 | `violated:word-eq@rejected` | 157 / 4 / 86 | 0 / 0 / 232 | 479 | 81.4 | stringfuzz `transformed/z3str2` 192, woorpje `track01` 157, woorpje `track03` 67 |
| 4 | `violated:not-word-eq@not-needed` | 0 / 0 / 0 | 0 / 0 / 352 | 352 | 90.0 | stringfuzz `transformed/z3str2` 352 |
| 5 | `violated:len-arith@not-needed` | 0 / 0 / 0 | 0 / 0 / 242 | 242 | 96.0 | stringfuzz `transformed/z3str2` 130, stringfuzz `generated/regexdeep` 74, denghang 38 |
| 6 | `unevaluable:other:uf@adopted` | 0 / 0 / 0 | 0 / 0 / 111 | 111 | 98.7 | Jiang `slent` 111 |
| 7 | `violated:not-memb@not-needed` | 0 / 0 / 0 | 0 / 0 / 19 | 19 | 99.1 | Norn `StringReplace` 12, Norn `HammingDistance` 7 |
| 8 | `violated:bool@rejected` | 0 / 0 / 17 | 0 / 0 / 0 | 17 | 99.6 | Jiang `slog` 17 |
| 9 | `violated:memb@adopted` | 0 / 0 / 14 | 0 / 0 / 2 | 16 | 100.0 | Jiang `slog` 14, stringfuzz `transformed/z3str2` 2 |
| 10 | `violated:not-bool@adopted` | 0 / 0 / 0 | 0 / 0 / 2 | 2 | 100.0 | Noetzli `str-pred-small-rw` 2 |

Smallest reproducer per tag (bytes):

- `violated:memb@not-needed`: `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-035-reverse-fuzz.smt2` (869 B)
- `violated:bool@not-needed`: `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-017-graft-reverse-graft.smt2` (836 B)
- `violated:word-eq@rejected`: `QF_S/20240318-omark/parikh.smt2` (435 B)
- `violated:not-word-eq@not-needed`: `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-019-unsat-reverse-reverse-translate.smt2` (864 B)
- `violated:len-arith@not-needed`: `QF_SLIA/20230327-stringfuzz-lu/generated/regexdeep/regex-deep-00001-27.smt2` (835 B)
- `unevaluable:other:uf@adopted`: `QF_SLIA/2019-Jiang/slent/slent_kaluza_575_sink.smt2` (1,407 B)
- `violated:not-memb@not-needed`: `QF_SLIA/2015-Norn/HammingDistance/norn-benchmark-124.smt2` (1,128 B)
- `violated:bool@rejected`: `QF_S/2019-Jiang/slog/slog_stranger_133_sink.smt2` (921 B)
- `violated:memb@adopted`: `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-graft-graft-fuzz.smt2` (885 B)
- `violated:not-bool@adopted`: `QF_SLIA/20190311-str-small-rw-Noetzli/str-pred-small-rw/str-pred-small-rw_370.smt2` (735 B)

Reading the tags: `bool` on a lowered top-level `and` names the lowering's
connective, not the source assertion. Class 2 shows this in full: every
sampled row is a source `(= k (str.len x))` that the lowering turns into
`(and (= …) (<= …) (>= …))`. The kind is computed on the lowered assertion,
as spec §4.1 says, so the tag is stable and correct, but a reader should
treat `bool` as "possibly a lowered Int equality".

## Top classes

Method (spec §8 item 2): a throwaway debug build of `8dbcda9`
(`target/slice59-after/shinri-debug`, never committed; crates reverted with
`git checkout -- crates`). It prints:

- in the solver gate: every lowered assertion's 3-valued result, plus the
  values of the first failing assertion's subterms;
- in `StrSolver::model_with`: `eq_true` atoms with their minted flags,
  membership atoms, and every EUF class over `known` (members, concat or
  not, minted side, constant head/tail, model value, concat-graph cycle);
- in `memb_seeds`: per variable, pinned / extraction failure, the model
  length `n`, whether `search_word(goal, n)` and `search_shortest` found a
  word, and `language_empty`;
- in `language_empty`: which cap returned `Unknown`.

Each class was traced on its smallest reproducer and on a `random.Random(59)`
sample of 40 rows (`shapes_sample.py` → `shapes_sample.txt`), with z3 4.16
(`-T:20`) on the sampled rows (`z3_sample.tsv`). Notes: `target/slice59-after/shapes.md`.

### 1. `violated:memb@not-needed` (2,253 rows, 55.2%)

**Smallest reproducer** (869 B, z3 `sat`):
`QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-035-reverse-fuzz.smt2`

```smt2
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in_re (str.++ y x) (re.* (str.to_re "b"))))
(check-sat)
```

The membership F-split mints `y = !strk0 ++ !strk1` (and
`!strk1 = !strk4 ++ !strk5`), and each minted leaf is seeded with `b`s. `x`
appears only as a concat *operand* (`(str.++ y x)`, `(str.++ !strk1 x)`,
`(str.++ !strk5 x)`), never as a bare membership subject, so `memb_seeds`
never seeds it. It keeps the default fill `"FF"`, and `(str.++ y x)` =
`"bbbbbFF"` violates the assertion. Shape: **concat subject with an unseeded
free operand.** The 12 smallest rows of the class are all this
`regex-035-*` family.

**This reproducer is not typical of the class.** In the 40-row sample:

| shape | rows |
| --- | ---: |
| bare-variable subject, seed search failed, value is a default fill (`"DDDD…"`) | 35 |
| concat subject (`regex-035-*` shape above) | 4 |
| bare-variable subject pinned by a concat in its class (no seed; the slice-58 guard shape) | 1 |

In the 35 failed seeds, `search_word(goal, n)` and `search_shortest` both
fail and `language_empty` returns `Unknown`. The cap is `CLASS_SPLIT_CAP`
(64) in `regex::next_classes`, hit on the **first** derivative step in 35/35
(`class1-empt-reasons.txt`). Memberships on the variable: 1 in 13 rows, 2 in
6, 3+ in 17. z3 on the 36 bare-variable rows: 14 `sat`, 7 `unsat`, 15
`timeout`.

**Representative reproducer** (976 B, z3 `unsat`):
`QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-010-reverse-multiply-fuzz.smt2`

```smt2
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (str.in_re x (re.+ (str.to_re "bba"))))
(assert (str.in_re x (re.+ (str.to_re "aaps]0e4_b{a"))))
(assert (str.in_re x (re.+ (str.to_re "j.3F&AXI'\x0c';7lLbg8[c_P1ou^uNIM-(' '%+}q'\x0c''\r''\t''\n'(CW/"))))
(check-sat)
```

Seed trace: `rexes=3 n=64`, no word at 64, no shortest word, emptiness
`Unknown` via the class-split cap at step 1. The three words start with
different characters, so the intersection is empty after one derivative. The
cap is hit while partitioning the first-character classes, before that
derivative is taken.

**Shape bucket:** model construction, specifically the membership witness
search. The evaluator is not the problem. On `sat` rows the fix is a
witness. On `unsat` rows (corpus: 310 of the class's 600 QF_S rows with a
status are `unsat`), the same cap blocks the emptiness conflict.
**Parked-item match:** the pinned sub-bucket matches the constant-head
strip on the membership path (the guards, below). The main bucket matches
no parked item; it is new.

### 2. `violated:bool@not-needed` (594 rows, 14.5%)

**Smallest reproducer** (836 B, z3 `unsat`):
`QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-017-graft-reverse-graft.smt2`

```smt2
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (str.in_re x (re.* (str.to_re "BA"))))
(assert (= 5 (str.len x)))
(check-sat)
```

Failing assertion (lowered):
`(and (= 5 (str.len x)) (<= 5 (str.len x)) (>= 5 (str.len x)))`. The
membership holds (`x = ""`), and the length equality fails. The seed for `x`
finds no word of length 5 in `(BA)*`, because the language has even lengths
only, so it falls back to the shortest word, `""`.

40-row sample: 40/40 failing assertions are lowered Int equalities (38
`len = const`, 2 `len = len`). Every `str.len` variable carries a membership
(42/42). The seed is "no word at the model length, shortest fallback" in
40/40, and the value is `""` in 33. z3 says `unsat` on 39 and `sat` on 1.

**Shape bucket:** a missing length/membership conflict (the evaluator is
fine). The engine reaches SAT with `len(x) = k` and `x ∈ R` where no word of
length `k` exists. **Parked-item match:** none of the four. This is a
length-abstraction gap: the exact-length emptiness of `R` is not turned into
a conflict.

### 3. `violated:word-eq@rejected` (479 rows, 11.7%)

**Smallest reproducer** (435 B, z3 `unsat`): `QF_S/20240318-omark/parikh.smt2`

```smt2
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x x "b" x)(str.++ x "a" x x)))
(check-sat)
```

The input equation's two concat sides share one class. The split mints
`x = "a" ++ !strk0`. The model gives `x = "DD"` while that minted member
evaluates to `"a"`: the values in `x`'s class disagree. The rebuild was
tried and rejected. The instance is `unsat` (an `a`/`b` count argument), so
no model fix can help this reproducer. It is the smallest row, not a typical
one.

40-row sample (`class3-groups.txt`): in all 40 rows the equation's sides sit
in one class with 2 concats. 26 have a leaf variable whose class holds a
minted concat, 24 have leaf classes whose member values disagree, 19/21 have
a constant head/tail on the sides, and 2 have a leaf concat cycle (rows
counted once per feature). z3: 33
`sat`, 3 `unsat`, 4 `timeout`. Groups:

| group | rows | example |
| --- | ---: | --- |
| woorpje `track01`, constant head and tail, equation **never split** (0 minted equations), z3 `sat` | 10 | `01_track_86` |
| split; a leaf's class holds a minted concat whose value (and length) disagrees with the variable | 22 (stringfuzz `x++y = m++n`, woorpje `track01`–`04`, Kepler `quad`; the 2 cycle rows below also disagree) | `01_track_154` |
| stringfuzz `x++y = m++n`, unsplit | 4 | `regex-032-rotate-translate-rotate` |
| leaf concat cycle | 2 | `noodles-unsat-8` |

`QF_S/20230329-woorpje-lu/track01/01_track_86.smt2` (935 B, corpus `sat`):

```smt2
(set-logic QF_S)
(declare-fun F () String)
(declare-fun E () String)
(assert (= (str.++  "cbab" F "abaacbcacb")  (str.++  "cbabacccc" E "bbbaabaacbcacb") ))
(check-sat)
```

Stripping the common constant head `"cbab"` and tail `"abaacbcacb"` leaves
`F = "acccc" ++ E ++ "bbba"`, which is a solved form. The engine never
splits the equation. `F` and `E` keep default fills (`"EEEEEEEEEEE"`,
`"II"`; the lengths fit) and the rebuild is rejected. **Parked-item match:
constant-head strip** (here head *and* tail), on the word-equation path.

`QF_S/20230329-woorpje-lu/track01/01_track_154.smt2` (946 B, corpus `sat`):
`(= (str.++ "f" C E) (str.++ D G))`. The split mints `D = "f" ++ !strk0` and
`!strk0 = C ++ !strk2`. The model has `D = "HHHHHH"` (length 6) but
`"f" ++ !strk0 = "fLLLLLLL"` (length 8), and `!strk0` (7) differs from
`C ++ !strk2` (8). The minted equations' sides have different model
lengths. **Parked-item match: minted length links.** I did not inspect the
arith model to tell whether the link is missing or merely not respected.

## Slice-58 guards

`target/slice59-after/guards.txt` (after binary):

| guard | stats | class rank |
| --- | --- | --- |
| `g1` | `fence=str-model-rejected detail=violated:memb@adopted` | 9 (16 rows) |
| `g3` | `fence=sat-budget detail=-` | outside the population |
| `rf2` | `fence=str-model-rejected detail=violated:memb@not-needed` | 1 (2,253 rows) |
| `rf3` | `fence=str-model-rejected detail=violated:memb@not-needed` | 1 |
| `rf4` | `fence=sat-budget detail=-` | outside (as the spec expects) |

**`g3` deviates from the brief's expectation.** It answers `sat-budget`,
not `str-model-rejected`, and the base binary gives the same
(`fence=sat-budget`). So this slice did not cause the move. The slice-58
report recorded `str-model-rejected` at `e784454`. The two later slice-58
commits before the merge, `c3f6e48` and `a47de77`, both touch `memb.rs`. I
did not bisect which one moved it.

Traces: in `g1`, `rf2` and `rf3`, the membership subject `y` is *pinned*,
because its class holds the prefix concat (`"a" ++ !pfx0`, `"" ++ !pfx0`,
`"é" ++ !pfx0`). So `memb_seeds` skips it, and the concat's free tail
`!pfx0` keeps a default fill (`"FF"` / `"F"`) that violates the range
regex. In `g1` the rebuild is adopted and the membership still fails on
`"aFF"`. This is the membership side of the constant-head strip: the tail
should be seeded from the regex's derivative by the constant head.

## Parked items

| item | ruling | reproducer |
| --- | --- | --- |
| Constant-head strip | **Has reproducers; leave parked as a fix item in its own right** and fold it into the class-3 fix (queue item 3). It appears on both paths: on word equations (class 3: woorpje `track01`, never split, constant head and tail) and on memberships (pinned subject; the guards `rf2`, `rf3`, `g1`) | `QF_S/20230329-woorpje-lu/track01/01_track_86.smt2` (935 B); guards `rf2`/`rf3` |
| Cited deep NF on the word-equation path | **Stays parked.** No sampled row isolates it. The class-3 value disagreements trace to minted members whose lengths differ, not to a stale normal form | none |
| Minted length links | **Has a reproducer** (class 3, about half of the sample). The minted equation's sides take different model lengths | `QF_S/20230329-woorpje-lu/track01/01_track_154.smt2` (946 B) |
| Suffix G′ (constant tail on a membership member) | **Stays parked.** No sampled class-1 row has a constant-tail member in a membership subject's class (the 4 concat subjects have free operands, and the pinned case has a constant *head*). Constant tails in class 3 are on word equations, which the constant-head strip covers | none |

## What changed versus the spec

1. **Spec §7.3's end-to-end checks are in `shinri-cli` `tests/cli.rs`,
   not `script_e2e`** (ruling R4). `stats_line_shape_on_sat` checks
   `detail=-`, and `stats_detail_clears_on_the_next_check_sat` checks a
   rejected detail followed by a cleared one. Cost if the owner wants them in
   `script_e2e`: one extra test.
2. **Plan correction (Task 2):** `tag_safe("(_ extract 7 0)")` gives
   `(__extract_7_0)`, not the plan's `(_extract_7_0)`, because the space
   maps to `_` and the `_` is kept. The classifier is unchanged and the test
   expectation was corrected.
3. **Criterion 5 count:** the oracle suite discovers 825 tests, not
   808. 825 = 808 + 17 tests this slice added (15 `model_reject` +
   2 `fence_tags`), so this is PASS (ledger ruling, Task 5).
4. **Criterion 4:** pass 1's QF_S ratio of 0.932 is outside the band on the
   *faster* side. Two re-runs (0.977, 0.984) and the pooled ratio over three
   passes (0.964) are inside. I read this as PASS on the pooled
   measurement. If the owner reads the criterion per pass, pass 1 fails on
   QF_S, and only in the direction where the after binary is faster.
5. **Guard `g3` lands at `sat-budget`** at both base and after, not at
   `str-model-rejected` as the brief expected. It moved before this
   slice's base (see *Slice-58 guards*).
6. **Paths (ruling R2):** the corpus and results live in the main checkout
   (`/workspace/bench/{corpus,results}`). The runs passed
   `--corpus`/`--results` explicitly, and the scripts use absolute paths.
   Reports were rendered with `target/slice59-after/shinri-bench report
   /workspace/bench/results/<id>` (ruling R8), not `mise run bench-report`.
7. **The after runs used `target/slice59-after/shinri-bench`**, a copy of
   the same build, rather than `target/release/shinri-bench`. The base runs
   used `target/slice59-base/shinri-bench`.
8. **Triage parallelism:** rows ran 6 at a time on cores 12–23 (the bench's
   `--jobs 6`), each row's 6 runs interleaved and serial. The brief's loop is
   serial. With 0 attributable rows and 0 wrong answers, this changes no
   disposition. A serial pass would take about 80 minutes.
9. **Triage result for kills:** the triage loop's `grep` keeps only
   answers and `stats:` lines, so a killed run shows as empty. I also kept
   `memory allocation … failed` lines to tell OOM aborts apart. Both
   binaries give the same OOM abort on every `oom → timeout` row.
10. **Step 8 traces went beyond the brief's two `eprintln!` sites.** The
    debug build also instrumented `memb_seeds` and `language_empty`
    (throwaway, reverted with `git checkout -- crates`, not `git stash`,
    ruling R3). That is how the class-1 cap (`CLASS_SPLIT_CAP`) was
    identified.
11. **Class-1 reproducer:** the brief's `min=` reproducer
    (`regex-035-reverse-fuzz`) is from a 10% sub-bucket (concat subject).
    The report also names a representative reproducer for the main
    sub-bucket (`regex-010-reverse-multiply-fuzz`, 976 B).
12. **Push and PR not done by the analysing agent** (ruling R7): the
    report and the spec section are committed locally, and the controller
    opens the PR.
13. **Family key replaced (review fix, controller ruling).** The plan's
    Step 6 script grouped families by `"/".join(path.split("/")[1:3])`.
    In a flat directory that key makes every file its own family, which hid
    automatark (649 rows, class 1's largest family) and Kepler (40 rows in
    class 3). The ranked table's "top families" column is now keyed on the
    containing directory, `"/".join(path.split("/")[1:-1])`
    (`target/slice59-after/fix1_recount.py`). No counts changed.

## Gates

From `target/slice59-gates.txt` (Task 5, controller, cores 0–11, during the
base string run):

- `mise run ci`: exit 0. nextest 1759 run / 1759 passed / 6 skipped
  (949.6 s).
- Oracle suite `cargo nextest run -p shinri-solver --features oracle`:
  825 run / 825 passed / 2 skipped (2,592 s). The discovered count is
  non-zero.

## Queued for the next slice

Ordered. Items 1–3 are new, from the classification. They are ranked by
population, and each item says what it needs. After them come slice-58 queue
items 2 onward and its carried lists, verbatim. **Re-rank:** the
classification puts the three new items ahead of everything carried. Suffix
G′ (slice-58 item 3) stays where it was but is marked *no reproducer*,
because the classification found no suffix shapes on the membership path.

1. **Membership witness search past `CLASS_SPLIT_CAP` (recommended next
   fix slice; class 1, 2,253 rows).** `memb_seeds` →
   `regex::search_word` / `search_shortest` (and `language_empty`) fail on
   the first derivative step when `next_classes` produces more than 64 cut
   points (35/35 sampled failures). The variable keeps a default fill, and
   the gate rejects the model. Search lazily, for example by picking
   characters from the components' first-character sets instead of the full
   partition, or give the witness search its own, larger cap. That gives a
   witness on `sat` rows, and the same change lets `language_empty` decide
   `Empty` on the intersection rows z3 calls `unsat` (7/36 sampled).
   Reproducers:
   `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-010-reverse-multiply-fuzz.smt2`
   (976 B, z3 `unsat`, 3 memberships) and the z3-`sat` rows in
   `target/slice59-after/z3_sample.tsv` (class 1). Also in the class, a
   smaller sub-bucket: a free concat operand of a membership subject is never
   seeded (`regex-035-reverse-fuzz.smt2`, 869 B, z3 `sat`).
   Expected bench signal: `str-model-rejected → correct` on stringfuzz
   `generated` and automatark rows, measured per tag with the new
   `fence_detail`.
2. **Length/membership conflict (class 2, 594 rows).** When the arith model
   fixes `len(x) = k` and `x ∈ R` has no word of length `k` (an exact,
   uncapped search), emit a conflict (or a length lemma) instead of
   reaching SAT. z3 says `unsat` on 39/40 sampled rows. Reproducer:
   `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-017-graft-reverse-graft.smt2`
   (`x ∈ (BA)*`, `len x = 5`). Note: the tag reads `bool` because the
   lowering wraps the Int equality in an `and`.
3. **Word-equation model rebuild: constant-head/tail strip and minted length
   links (class 3, 479 rows).** Constant head and tail on both sides of an
   input equation that is never split (woorpje `track01`):
   `QF_S/20230329-woorpje-lu/track01/01_track_86.smt2`. Minted members whose
   model lengths disagree with their class:
   `QF_S/20230329-woorpje-lu/track01/01_track_154.smt2`. On the membership
   path, the guards `rf2`/`rf3`/`g1` need the tail of a pinned prefix concat
   seeded from the regex's derivative by the head. These absorb the parked
   approach-2 parts that now have reproducers. The cited deep NF on the
   word-equation path stays parked (no reproducer).

Not ranked above, for reference: `violated:not-word-eq@not-needed` (352,
stringfuzz `transformed`), `violated:len-arith@not-needed` (242), and
`unevaluable:other:uf@adopted` (111, Jiang `slent`: an uninterpreted
function application the strict gate cannot evaluate after an adopted
rebuild; this is evaluator coverage).

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

- Spec: `docs/superpowers/specs/2026-10-04-shinri-slice59-model-rejected-classes-design.md`
- Plan: `docs/superpowers/plans/2026-10-04-shinri-slice59-model-rejected-classes.md`
- Slice-58 report: `docs/superpowers/research/2026-10-04-smtlib-2024-slice58-member-prefix-report.md`
- Evidence (not committed): `target/slice59-gates.txt`; `target/slice59-{base,after}/{launch.sh,md5.txt,commit.txt,started.txt,finished.txt}`;
  `target/slice59-after/{step3.txt,step3b.txt,changed.tsv,triage.tsv,triage-disp.txt,timing.txt,timing-rerun2.txt,timing-rerun3.txt,matrix.txt,classes.txt,classes-table.md,guards.txt,shapes.md,shapes_sample.txt,z3_sample.tsv,class1-empt-reasons.txt,class3-groups.txt}`;
  `/workspace/bench/results/slice59{,-base,-sample,-base-sample}/`
