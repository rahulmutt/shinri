# SMT-LIB 2024 re-run — slice 62 (length-consistent seeds and the compound-arithmetic gate) — shinri @ 1261bc9 (benchmarked), fd445aa (PR head)

## Headline

Slice 62 makes three changes, plus one interface change that lets the
first of them be stated:

- a per-leaf pass, `leaf_bounds::bound_split`
  (`crates/shinri-str/src/leaf_bounds.rs`), that tells arith the exact
  length bounds of a bare leaf's membership intersection
  (`regex::len_bounds`). It emits them as multi-guard lemmas
  `¬m₁ ∨ … ∨ ¬mₖ ∨ bound`. `TCheck::Split`, `FinalCheck::Split` and
  `TheoryResult::SplitAtoms` now carry `guards: Vec<Lit>`;
- a gate change: `eval_num_val` folds `+ - * neg` whenever every operand
  evaluates;
- a strict-gate backstop when a `memb_seeds` seed changes a leaf's length.
  Fix round 1 added a gate rule: a UF application with a stale numeric
  argument is unevaluable (`uf_args_stale`).

The benchmarked binary is `1261bc9`. This includes the mid-measurement
perf fix (`LEN_BOUND_WORK_CAP`, ruling R9). The PR head is `fd445aa`, a
second, behaviour-neutral perf fix (interned `len_bounds` walk states, no
`Vec<Rex>::retain`; rulings R11-R13) that touches only
`crates/shinri-str/src/regex.rs`. The full verdict runs were **not**
repeated at `fd445aa` (R13): the evidence that it is behaviour-neutral is
a unit test against the old walk and identical final-check traces, and the
full oracle suite was re-run at `fd445aa` instead. Timing (criterion 4) was
re-measured at `fd445aa`. Any commits after it are this report's, and they
are docs-only.

- **Rows moved to `correct`: 167**, all QF_SLIA, all corpus status
  `unknown`, and all confirmed by the bench's z3 oracle. **165 `unsat`, 2
  `sat`.**
  - All 167 were `unknown:str-model-rejected` in base: 106 tagged
    `violated:bool@not-needed` and 61 tagged `violated:len-arith@not-needed`.
  - By family: stringfuzz `transformed/z3str2` 156 (`regex-007-*` 62,
    `regex-028-*` 47, `regex-042-*` 42, `regex-009-*` 5), denghang 9, Norn
    `ab` 2.
  - **Every one of the 167 is attributed to the bound lemma.** The trace
    build prints `group-bound` on 167/167 and no other slice-62 mechanism.
  - String `correct` rises **+130 net** (42,024 → 42,154). That is 167
    gains, plus 2 rows that only flipped from noise (`unverified → correct`,
    `timeout → correct`), minus 39 rows where the z3 oracle timed out this
    time (`correct → unverified`).
- **Criterion 2:** Norn `ab` `norn-benchmark-135` and `-138` are `correct`
  (`sat`). Their models are `v = 2` with `var_0 = "ab"` and `var_4 = "ab"`.
  z3 accepts both models when they are pinned into the script.
- **Losses: none attributable.** The 39 `correct → unverified` rows give
  identical answers from both binaries 3/3. The 15 neutrality-sample
  changes are base-run timing edges: both binaries time out, OOM, or answer
  alike.
- **Unverified:** one new `unverified` `unsat`, denghang `instance46328`
  (the z3 oracle timed out at 20 s). z3 `-T:120` and cvc5
  `--tlimit=120000` both answer `unsat`.
- **The two live wrong `sat`s on `main` are closed.** The item-5
  reproducer and the UF-argument backstop case both go from `sat` to
  `unknown` (z3: `unsat`).
- **Criteria:**

  | # | result |
  | --- | --- |
  | 1 | PASS: 0 `wrong` rows in both after runs; 0 wrong answers in 546 triage runs; the one new `unverified` `unsat` is confirmed by z3 -T:120 and cvc5 |
  | 2 | PASS: 135 and 138 `correct`; z3 accepts both pinned models |
  | 3 | PASS: 0 `correct → non-correct` rows reproduce (39 oracle churn + 10 sample timeouts, all noise) |
  | 4 | **PASS per ruling R12** (was FAIL at `1261bc9`: pooled QF_S 1.060 / QF_SLIA 1.094). After `fd445aa`: 6 passes pooled **1.037 / 1.036**. Set 1 (R10 three-pass, load 21-26) 1.076 / 1.033, set 2 (load 13-15) 0.996 / 1.040. CPU min-of-5 per row: QF_S 1.014 / 1.028, QF_SLIA 0.996 / 0.990. A/A base-vs-base swing 0.92-1.08. Set 1 alone fails QF_S by the letter; accepted under R12 (see *Timing*) |
  | 5 | PASS: ci 1838/1838/6 skipped at `fd445aa` (1836 at `1261bc9`, 1834 at `01e3fa8`); oracle 854/854/2 skipped at `fd445aa` (≥ 841 + 2) |
  | 6 | PASS: 15 sample rows changed, all to/from `timeout` at the 20 s edge; noise 3/3 |
  | 7 | report-only: the bound lemma fired on 167/167 gains and on 1/400 random string rows. The seed backstop moved 0 verdicts and fired on 4/400 random rows, none of which changed verdict. Unvalued fold and `uf-stale`: 0 changed rows, 0/400 |

## Commands

Task 0 (base build and probes; see the slice-62 plan, Task 0 for the
verbatim scripts):

```bash
git diff f9fa4f9 HEAD -- crates Cargo.toml Cargo.lock | grep -E '^[+-]' | grep -vE '^(\+\+\+|---)' \
  | grep -vE '^[+-]\s*(//|$)' ; echo "non-comment lines above (expect none)"
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice62-base && cp target/release/shinri target/release/shinri-bench target/slice62-base/
md5sum target/slice62-base/shinri | tee target/slice62-base/md5.txt
git rev-parse --short HEAD | tee target/slice62-base/commit.txt
# sample corpus re-created by slice 59's seeded hard-link recipe -> target/slice59-sample-corpus (matches slice61-sample: True 2000)
# probes r11a-variant, r10, uf-len, uf-len-sat, norn135, norn138 -> target/slice62-base/probes/, base outcomes in probes.txt
```

Task 8 (gates): `cargo fmt --all --check && taskset -c 0-11 mise run ci`
and `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle`,
recorded in `target/slice62-gates.txt` (at `01e3fa8`). After the perf
fix, `taskset -c 0-11 mise run ci` was re-run at `1261bc9`
(`perf-fix-report.md`).

Task 9:

```bash
# Step 1 (controller): build and freeze at 1261bc9, then the detached two-leg run (brief verbatim)
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice62-after && cp target/release/shinri target/release/shinri-bench target/slice62-after/
md5sum target/slice62-after/shinri | tee target/slice62-after/md5.txt
git rev-parse --short HEAD | tee target/slice62-after/commit.txt
uptime | tee target/slice62-after/uptime-start.txt
date -u +%FT%TZ > target/slice62-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice62-after/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice62-after/shinri --run-id slice62 \
  > target/slice62-after/run.log 2>&1; \
  taskset -c 12-23 target/slice62-after/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice62-after/shinri --run-id slice62-sample \
  > target/slice62-after/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice62-after/finished.txt' \
  > /dev/null 2>&1 &
# Step 2: reports and join (brief script verbatim) -> join.txt, changed.tsv
for id in slice61 slice62 slice61-sample slice62-sample; do BENCH_RUN_ID=$id mise run bench-report; done
# Step 3: triage-in.tsv (brief script verbatim, random.Random(62)); rows 6 at a time, detached
tr "\t" " " < target/slice62-after/triage-in.tsv | xargs -P6 -L1 target/slice62-after/triage-row.sh > target/slice62-after/triage.tsv
#   per binary and run: taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats $root/$p
python3 target/slice62-after/triage_disp.py       # -> triage-disp.txt, triage-summary.txt
mise exec -- z3 -T:120 bench/corpus/QF_SLIA/20230329-denghang/instance46328.smt2      # unsat
mise exec -- cvc5 --tlimit=120000 bench/corpus/QF_SLIA/20230329-denghang/instance46328.smt2   # unsat
# criterion 2: get-value of the mentioned vars appended, values pinned, z3 -T:20 -> crit2/result.txt
# Step 4: throwaway trace build (brief's three eprintln!s + uf-stale), copied to shinri-trace, reverted
cargo build --release -p shinri-cli --target-dir target/slice62-trace
git checkout -- crates && git status --short       # printed nothing
target/slice62-after/attr.sh   # attribution.tsv (91 triage rows), strict-sample.txt + prevalence.tsv (400 rows); cores 0-11
#   plus attribution-allgains.tsv: the same trace over all 167 gain rows
# Step 5: timing-watch.sh (R10 gate: 1-min load <= 24, up to 30 min), timing.py (brief script verbatim), 3 passes
#   diagnostics: timing-rows.py (per-row min-of-5, order alternated), timing-diag.txt (throwaway
#   bound_split/len_bounds timer build, reverted), timing-bisect.txt (per-commit builds in a scratch worktree, removed)
```

## Runs

| run | solver | md5 | started | finished | rows |
| --- | --- | --- | --- | --- | ---: |
| `bench/results/slice61/` (base) | slice 61's `target/slice61-after/shinri` (`f9fa4f9`) | `8fa66e7ec36c0670af8bcda06bcdd379` | 2026-10-05T21:36:28Z | (string leg ends when the sample leg starts, 2026-10-06T00:06:14Z) | 103,335 |
| `bench/results/slice61-sample/` (base) | same | same | 2026-10-06T00:06:14Z | 2026-10-06T00:22:29Z | 2,000 |
| `bench/results/slice62/` | `target/slice62-after/shinri` (`1261bc9`; the PR head `fd445aa` was not run, see below) | `b8bb8d94f1c26556097fcd23030d3a9c` | 2026-10-07T02:13:26Z | (string leg, then the sample leg) | 103,335 |
| `bench/results/slice62-sample/` | same | same | (after the string leg) | 2026-10-07T05:12:11Z | 2,000 |

- All runs used `--timeout 20 --mem-mb 3072 --jobs 6` on cores 12–23.
  Each `results.jsonl` holds its rows plus one fixture line (103,336 and
  2,001 lines). The base and after row sets are identical (the join
  asserts it). The after fixture records `sha` `1261bc94689a` and
  `solver_md5` `b8bb8d94…`, which matches `md5.txt`.
- **Base binary for re-runs** (triage, timing): `target/slice62-base/shinri`,
  md5 `d10b1202cfd1b18395946032462368b3`, built from `main` `9ac5105`.
  The spec names `cdb5630` as `main`. By branch time `main` was `9ac5105`,
  whose crates match `f9fa4f9` (the slice-61 after binary that produced
  the base runs) except for comments: Task 0 Step 2 printed no
  non-comment line. So the `slice61{,-sample}` runs serve as base runs,
  with no new base run, and the rebuilt binary behaves the same as the
  one that produced them.
- **Host load.** At launch the 1-min load average was **29.26** (5-min
  43.06, 15-min 46.24; `uptime-start.txt`). It was host-wide: none of our
  processes were running on this shared host. The slice-61 after runs
  launched at 16.71. Absolute bench `wall_ms` is therefore not comparable
  between base and after (see *Timing*).
- **The after runs' binary is `1261bc9`, not the PR head `fd445aa`
  (R13).** `fd445aa` (second perf fix) came after the runs finished. No
  third full bench was run: `fd445aa` is verified behaviour-neutral
  (`len_bounds` equals the old walk on 405 regexes × 7 work caps, and the
  final-check traces are identical on 946 bench rows), and the full oracle
  suite was re-run at `fd445aa` instead. Cost if wrong: a verdict change at
  `fd445aa` outside the traced rows goes unmeasured (about 3 h of bench to
  close). Timing was re-measured with the `fd445aa` build.
- **Abandoned first after run (diagnostic only).** The first after run was
  at `01e3fa8` (md5 `65afad2568d3e02a6aff5cbec1ab4cb6`, launched
  2026-10-07T00:17:58Z). It was stopped at **89,050 / 103,335** rows when
  a perf regression showed up: 238 rows had gone from `correct`/`unverified`
  to `timeout`. It had `wrong = 0` at that point. Its partial results are
  in `bench/results/slice62-abandoned-01e3fa8/` and its binaries in
  `target/slice62-after-abandoned-01e3fa8/`. See *What changed versus the
  spec*, R8/R9.

## Success criteria (spec §8)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | **PASS** | 0 `wrong` rows in `slice62` and `slice62-sample`, and 0 `sat ↔ unsat` flips. Triage ran 546 runs over 91 rows: no row got both `sat` and `unsat`, and no run contradicts a known corpus status. One row became `unverified` with `unsat` (denghang `instance46328`: base z3 oracle `unsat`, after z3 oracle `timeout`). z3 `-T:120` → `unsat`, cvc5 `--tlimit=120000` → `unsat` (`unsat-xcheck.txt`). All 165 new `unsat` rows are `correct`, i.e. z3-confirmed by the bench oracle |
| 2 | Norn `ab` 135 and 138 `correct`, with `get-value` models that satisfy the script | **PASS** | Both rows go `unknown:str-model-rejected → correct` (`sat`). `get-value`: 135 `((v 2) (var_0 "ab"))`, 138 `((v 2) (var_4 "ab"))`. Pinned into the script, z3 answers `sat` for both (`crit2/result.txt`). Task 6's `norn_135/138_sat_with_valid_model` probes are GREEN on HEAD and RED on `main` |
| 3 | every reproducible `correct → non-correct` row had an invalid base model | **PASS** | No such row reproduces. The 39 string `correct → unverified` rows (38 `sat`, 1 `unsat`) give the same answer 3/3 on both binaries; only the bench's 20 s z3 oracle differed. The 10 sample `correct → timeout` rows time out on both binaries 3/3 in triage. No pinned-model check was needed |
| 4 | serial interleaved timing on 150 both-`correct` rows per string logic, within ±5% of base | **PASS (R12)** | At `1261bc9` it was a FAIL: pooled QF_S **1.060**, QF_SLIA **1.094** (pass 1 1.048 / 1.072; min-of-5 1.116 / 1.109), bisected to Task 3's bound pass (`d8dbf2d`). After the second perf fix (`fd445aa`): 6 passes pooled QF_S **1.037**, QF_SLIA **1.036**; set 1 (R10 three-pass, load 21–26) 1.076 / 1.033; set 2 (load 13–15) 0.996 / 1.040; CPU min-of-5 per row QF_S 1.014 / 1.028, QF_SLIA 0.996 / 0.990; A/A base-vs-base 0.92–1.08. **Set 1 alone fails QF_S by the letter (1.076 > 1.05); it is accepted under R12** because the controlled measurements and the A/A noise floor show it is noise. See *Timing* |
| 5 | `mise run ci` green; oracle discovered count ≥ 841 + this slice's oracle tests | **PASS** | At `fd445aa` (PR head): ci **1838** run / 1838 passed / 6 skipped (1836 plus the 2 new `len_bounds` unit tests of the second perf fix; 1836 at `1261bc9`, 1834 at `01e3fa8`). Oracle with `--features oracle` re-run at `fd445aa`: **854 run** / 854 passed / 2 skipped (≥ 841 + 2 `len_bounds_oracle` tests; discovered count non-zero; log `target/slice62-oracle-fd445aa.log`). The same count was 854/854/2 at `01e3fa8` |
| 6 | neutrality sample: only non-reproducible timing flips | **PASS** | 15 sample rows changed, all into `timeout` from base `correct` (10) or `oom` (5). In triage (load 28–45) both binaries time out or OOM alike. A single re-check at load 24–33 (`sample-recheck.tsv`) gives identical outcomes from the two binaries on 14/15, all at 13–20 s: 5 QF_UF `unsat`/`sat`, 4 OOMs, 5 timeouts. FISCHER7-12 answers `sat` at 19.0 s on after and times out on base. 0 attributable |
| 7 | rows moved by the backstop; rows on which a bound lemma was emitted | report-only | See *Attribution and prevalence* |

Probe outcomes (`target/slice62-after/probes.txt`; z3 in the last column):

| probe | base `9ac5105` | after `1261bc9` | z3 | after trace |
| --- | --- | --- | --- | --- |
| `r11a-variant` (item 5) | **`sat`** (wrong) | `unknown` (`violated:bool@not-needed`) | `unsat` | `strict seed=true`, `unvalued-fold` ×4 |
| `uf-len` (backstop) | **`sat`** (wrong) | `unknown` (`unevaluable:len-arith@not-needed`) | `unsat` | `strict seed=true`, `uf-stale` ×7 |
| `r10` | `unknown` | `unknown` | `unsat` | `strict seed=true` |
| `uf-len-sat` | `sat` | `sat` | `sat` | none |
| `norn135` | `unknown` (`str-model-rejected`) | **`sat`** | `sat` | `group-bound` ×2 |
| `norn138` | `unknown` (`str-model-rejected`) | **`sat`** | `sat` | `group-bound` ×2 |

Task 6's `slice62_probes` is RED on `main` for `r11a_variant_not_sat`,
`norn_135/138_sat_with_valid_model` and `uf_len_backstop_not_sat`, and
GREEN on HEAD (6/6). The Task 7 oracle tally (R7) is: 33 `sat`, 123
`unsat`, 44 `unknown`, 14 z3 unknown/timeouts, 11 bounded-confirmed
`unsat`.

## The two live wrong `sat`s on `main`

**Item 5 (slice-61 queue, the R11a residual).** The script is:

```smt2
(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (and (<= (+ (str.len x) (str.len y)) 3) (>= (+ (str.len x) (str.len y)) 3)))
(check-sat)
```

z3 answers `unsat`. The base binary answers `sat ((x "") (y ""))`. The
arith model never valued the sum, so the old gate could not evaluate it and
skipped it. The after binary answers `unknown`: the gate now folds the sum
from the string values (0 ≠ 3), and the trace shows `unvalued-fold`.
Reaching `unsat` needs CEGAR length refinement (queued, item 3), because
`(ab)*` has only even lengths.

**UF-argument backstop (found while planning).** The script is:

```smt2
(set-logic ALL)(declare-fun x () String)(declare-fun f (Int) Int)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (= (f (str.len x)) 1))
(assert (= (f 0) 0))
(assert (= (f 2) 0))
(assert (<= (str.len x) 3))
(check-sat)
```

z3 answers `unsat`. Base answers `sat ((x ""))`. Task 5 as first written
still answered `sat`: arith had `len x = 3` and `f(3) = 1`, the string
model had `x = ""`, and the gate read `f(len x)` at the stale argument.
Fix round 1 (`2c31cb0`) makes a UF application unevaluable when an
argument's model value differs from its evaluated value (`uf_args_stale`).
Together with the strict flag the seed raises, the model is rejected. The
after binary answers `unknown`, and the trace shows `strict seed=true` and
`uf-stale`. The sibling `uf-len-sat` (no `f(2) = 0`, z3 `sat`) stays `sat`.

## Verdict changes

### String runs (QF_S + QF_SLIA)

Verdict counts (base → after), from `bench/results/{slice61,slice62}/results.jsonl`:

| verdict | QF_S base | QF_S after | QF_SLIA base | QF_SLIA after |
| --- | ---: | ---: | ---: | ---: |
| correct | 16,668 | 16,670 | 25,356 | 25,484 |
| parse-error | 0 | 0 | 195 | 195 |
| timeout | 6 | 5 | 45 | 48 |
| unknown:reglan-decl | 0 | 0 | 3,287 | 3,287 |
| unknown:sat-budget | 1,381 | 1,381 | 4,248 | 4,245 |
| unknown:str-indexof-replace | 80 | 80 | 26,283 | 26,283 |
| unknown:str-int-conv | 0 | 0 | 1,616 | 1,616 |
| unknown:str-model-rejected | 323 | 323 | 1,833 | **1,666** |
| unknown:str-predicate-polarity | 0 | 0 | 16,016 | 16,016 |
| unknown:str-regex | 343 | 343 | 26 | 26 |
| unknown:str-substr-at | 0 | 0 | 3,359 | 3,359 |
| unknown:theory-refused | 0 | 0 | 35 | 35 |
| unverified | 139 | 138 | 2,096 | 2,135 |
| wrong | 0 | 0 | 0 | 0 |

Changed rows: 211 string + 15 sample (`target/slice62-after/join.txt`).

| logic | base | after | rows | triage |
| --- | --- | --- | ---: | --- |
| QF_SLIA | unknown:str-model-rejected | correct (`unsat`) | 165 | gain (30 sampled: base `str-model-rejected` 3/3, after `unsat` 3/3) |
| QF_SLIA | unknown:str-model-rejected | correct (`sat`) | 2 | gain: Norn `ab` 135, 138 (both sampled, attributable as expected) |
| QF_SLIA | correct | unverified | 39 | noise: identical answers 3/3 on both binaries (38 stringfuzz `generated` `sat`, the z3 oracle timed out; denghang `instance46328` `unsat`, cross-checked) |
| QF_SLIA | unknown:sat-budget | timeout | 3 | noise: Leetcode `findAnagrams` near 20 s, both binaries time out (one mixes `sat-budget` and timeout on both) |
| QF_S | timeout | correct | 1 | noise: automatark `instance15770`, `sat` on base 3/3 and on after 2/3 (timeout once) |
| QF_S | unverified | correct | 1 | noise: automatark `instance08669`, `unsat` on both; only the oracle finished this time |

### `fence_detail` movement (rows `unknown:str-model-rejected`, string runs)

| tag | base | after |
| --- | ---: | ---: |
| `violated:bool@not-needed` | 598 | **492** |
| `violated:len-arith@not-needed` | 242 | **181** |

No other tag moved. No row changed tag without also changing verdict.
`violated:bool@not-needed` is slice-59 class 2 (a lowered Int equality,
in practice a length/membership conflict, slice-59 items 2–3). 106 of its
rows are now decided: 104 `unsat` and the 2 Norn `sat`s. The other 61
gains come from `len-arith`. The remaining 492 include the parity shape
(slice-59 item 3's reproducer `regex-017-graft-reverse-graft`, `x ∈ (BA)*`,
`len x = 5`), which exact bounds cannot refute.

### Gains by family and shape

| family | base tag | answer | rows |
| --- | --- | --- | ---: |
| stringfuzz `transformed/z3str2` | `violated:bool@not-needed` | `unsat` | 104 |
| stringfuzz `transformed/z3str2` | `violated:len-arith@not-needed` | `unsat` | 52 |
| denghang | `violated:len-arith@not-needed` | `unsat` | 9 |
| Norn `ab` | `violated:bool@not-needed` | `sat` | 2 |

The typical z3str2 gain (`regex-007-unsat-fuzz-multiply`) is
`len x = 2 ∧ x ∈ (w₁)* ∧ x ∈ (w₂)*` with long, distinct words `wᵢ`. The
intersection is `{ε}`, so `len_bounds = (0, Some(0))` and the bound lemma
conflicts with `len x = 2`. The typical denghang gain (`instance50780`) is
a finite real-world regex, a negated "danger letter" filter, and
`20 < len X`. The intersection's max is below the lower bound.
Two of the slice-51 carried denghang rows (`instance51681`, `55189`) are
among the gains. The other two (`46836`, `52132`) are still
`violated:len-arith@not-needed`.

Losses by family (all noise, above): stringfuzz `generated` 38 (oracle
churn), denghang 1 (oracle churn), plus the sample rows below.

### Neutrality sample (seven other logics, 2,000 rows)

| logic | base | after | rows | triage |
| --- | --- | --- | ---: | --- |
| QF_UF | correct | timeout | 5 | noise: both binaries time out 3/3 in triage; at lower load both answer (13–19 s) |
| QF_LIA | correct | timeout | 3 | noise: both time out; FISCHER7-12 answers on after at 19.0 s in the re-check, base times out |
| QF_UFLIA | correct | timeout | 2 | noise: mathsat Hash, both time out |
| QF_LIA | oom | timeout | 3 | noise: both OOM or time out (mixed on both binaries) |
| QF_UFLIA | oom | timeout | 2 | noise: Certora, both OOM |

Every change is an edge case at 20 s or 3 GB. The after sample leg ran at
the end of a run that launched at load 29 on a host that stayed at load
30–48. The string-model changes cannot reach these logics. The only code
on their path is the `guards: Vec<Lit>` migration, which is
behaviour-identical for 0–1 guards (spec §4.5).

## Triage

Files: `target/slice62-after/{triage-in.tsv,triage.tsv,triage-disp.txt,triage-summary.txt,triage-row.sh,triage_disp.py}`.

Method: the brief's per-run command and noise rule. Base binary
`target/slice62-base/shinri` against after binary
`target/slice62-after/shinri`, 3 interleaved runs each, on cores 12–23,
6 rows in parallel (`xargs -P6`, as in slices 60 and 61). The run took
2026-10-07T05:15:17Z–05:23:19Z. 1-min load was 27.62 before and 44.53
after (host-wide). Attribution ran on cores 0–11 at the same time.

Selection: 91 rows. All 59 non-gain rows (44 string + 15 sample, fewer
than 200) are included, plus the brief's seeded (`random.Random(62)`)
family-stratified gain sample of 32: z3str2 21, denghang 9, Norn `ab` 2.

| transition | rows | noise | attributable |
| --- | ---: | ---: | ---: |
| gain (`unknown:str-model-rejected → correct`) | 32 | 0 | 32 (expected: 30 `unsat` 3/3, 2 `sat` 3/3) |
| `correct → unverified` | 39 | 39 | 0 |
| `unknown:sat-budget → timeout` | 3 | 3 | 0 |
| `timeout → correct` | 1 | 1 | 0 |
| `unverified → correct` | 1 | 1 | 0 |
| sample `correct → timeout` | 10 | 10 | 0 |
| sample `oom → timeout` | 5 | 5 | 0 |

- Wrong answers: 0. Attributable `correct → non-correct`: 0, so criterion
  3 needs no pinned-model check. Attributable sample rows: 0.
- **Unsat cross-check:** one row, denghang `instance46328`, gave `unsat`
  on both binaries in all 3 triage runs. The bench oracle had z3 `unsat` in
  base and `timeout` in after. z3 `-T:120` gives `unsat` and cvc5
  `--tlimit=120000` gives `unsat`. The 165 new `unsat` rows are all
  `correct`, so the oracle confirmed each of them in the bench run.

## Attribution and prevalence

Throwaway trace build of `1261bc9` (`target/slice62-trace`, copied to
`target/slice62-after/shinri-trace`). It carries the brief's three
`eprintln!`s plus one more, at these sites in the current code:

- `group-bound`: before `return Some(memb::emit_split_guards(…))` in
  `leaf_bounds.rs`;
- `strict joint=… seed=…`: inside `model_with`'s
  `if joint_len_changed || seed_len_changed {` block;
- `unvalued-fold`: in `eval_num_val`'s compound arm, when the fold is
  `Some` and the arith model has no value for the term;
- `uf-stale`: where `uf_args_stale` returns true (the Task 5 fix-round
  gate rule).

Reverted with `git checkout -- crates`; `git status --short` printed
nothing.

**Changed rows** (`attribution.tsv`, the 91 triage rows, and
`attribution-allgains.tsv`, all 167 gains):

| rows | mechanism fired |
| --- | --- |
| 167 / 167 gains | `group-bound` only (1 lemma on 29 of the 32 sampled, 2 on 3) |
| 59 non-gain rows | none |

- None of the changed rows fired `strict` (joint or seed), `unvalued-fold`
  or `uf-stale`. **The backstop and the gate changes moved 0 corpus
  verdicts.** Their effect is the two closed wrong-`sat` probes above.
- Every gain comes from the bound lemma reaching arith. 165 of them are
  `unsat`, a result the spec did not expect: it expected the gate to yield
  only `sat` models, but the bound lemma conflicts with asserted lengths
  during search. The spec noted that new `unsat` rows were possible.

**Prevalence** (`prevalence.tsv`, 400 random QF_S/QF_SLIA rows,
`random.Random(62)`, trace binary, 20 s):

| mechanism | rows (of 400) | verdicts of those rows (after; base) |
| --- | ---: | --- |
| `group-bound` | 1 (0.25%) | z3str2 `regex-007-unsat-multiply-rotate-reverse`: `correct` (`unsat`); base `str-model-rejected` (a gain) |
| `strict joint=false seed=true` | 4 (1.0%) | 2 `correct` (both binaries; automatark `instance10500`, `13513`); 2 `unknown:str-model-rejected` on both binaries (z3str2 `regex-018-rotate-graft-translate`, `regex-019-unsat-rotate-fuzz-translate`) |
| `strict joint=true` | 0 | |
| `unvalued-fold` | 0 | |
| `uf-stale` | 0 | |

The seed backstop fires on roughly 1% of string rows. On the sample, it
neither lost a `correct` nor blocked a gain: the 2 rows it flagged that
were rejected were already rejected in base. The spec's two known costs
(§4.2) are the item-4 pattern and length 0 when no `str.len` entry exists.
Neither shows as a verdict change in this run.

## Timing

Two measurements: the first at `1261bc9` (Task 9 Step 5, a FAIL), then a
re-measurement at `fd445aa` after the second perf fix (the verdict-bearing
one, `target/slice62-after/timing-perf2.txt`). The `1261bc9` section is kept
as the record of how the regression was found.

### After the second perf fix (`fd445aa`)

Same Step-5 script, seed 62, 150 rows per logic, core 12, base then after
per row. Base is `target/slice62-base/shinri`; after is the `fd445aa` build.

| | QF_S | QF_SLIA | newly-`correct` (not gated) |
| --- | --- | --- | --- |
| set 1 passes (load 21–26; the R10 three-pass set) | 1.077 / 1.094 / 1.063 | 1.085 / 1.013 / 0.993 | 0.979 / 0.992 / 0.984 |
| set 1 pooled | **1.076** | 1.033 | 0.985 |
| set 2 passes (load 13–15) | 1.054 / 0.998 / 0.946 | 0.943 / 1.085 / 1.102 | 0.997 / 1.004 / 1.014 |
| set 2 pooled | 0.996 | 1.040 | 1.005 |
| **6 passes pooled** | **1.037** (10.27 → 10.65 s) | **1.036** (20.80 → 21.55 s) | 0.994 |
| A/A control (base vs a copy of base, 3 passes, load 16–23) | 1.084 / 0.922 / 1.010, pooled 1.000 | 0.935 / 1.037 / 0.940, pooled 0.968 | pooled 0.979 |

Per-row min-of-5, order alternating, same sample, wall / CPU (user+sys via
`wait4`):

| run | QF_S wall / cpu | QF_SLIA wall / cpu |
| --- | --- | --- |
| `1261bc9` (before the fix) | 1.101 / 1.097 | 1.110 / 1.112 |
| `fd445aa` run A | 1.015 / 1.014 | 0.995 / 0.996 |
| `fd445aa` run B | 1.027 / 1.028 | 0.990 / 0.990 |
| `fd445aa`, wall only (first, load 17) | 1.034 | 1.001 |
| `fd445aa`, wall only (second, load 14) | 1.053 | 1.080 * |

\* In that run `regex-big-00050-5` and `-00071-0` were each exactly +100 ms
of wall time. It did not reproduce in the other three runs, where the
candidate is 10–48 ms *faster* than base on both rows by CPU time. The
container's cgroup has `cpu.max` 800000/100000 and a history of 75k
throttled periods; a 100 ms step matches one throttle period, though
`nr_throttled` did not move during the CPU runs.

- **Verdict on criterion 4: PASS under R12.** Set 1 alone (the R10
  three-pass set) fails QF_S by the letter (1.076 > 1.05). It is accepted
  because: the 6-pass pool is 1.037 / 1.036; the CPU min-of-5 figures, the
  more reliable measurement here, are 1.014–1.028 / 0.990–0.996; and the
  A/A control shows one pass of the script moves ±8% on QF_S with identical
  binaries (base-vs-base 0.92–1.08). A 3-pass pooled wall ratio on QF_S is
  only good to about ±4% on this shared host. The residual is real walk
  work, about +1–3% on QF_S (one walk per affected row, up to the 10k-unit
  cap). Cost if wrong: a real ~+4–7% QF_S slowdown ships (R12).
- **Root cause of the `1261bc9` slowdown**, found by the second perf
  round: the pass's own work was not the main cost. `bound_split` runs
  once per solve on the slow rows, one `len_bounds` miss of 3–6 ms. A build
  whose `bound_split` returned immediately (`black_box(true)`) was still
  ~11% slower (793 vs 717 ms on `regex-big-00050-5`); a build with
  `len_bounds` dead code ran at base speed. A bisect with the pass disabled
  puts it at `d8dbf2d`, where `len_bounds` first becomes live: the cost
  comes from *linking* it. `nm` shows `drop_glue::<Rex>` as nine copies of
  0x1fa bytes in slow builds against eight of 0xf8 plus one of 0x37e in
  fast ones. The walk's `layer.retain(...)` was the crate's only
  `Vec<Rex>::retain` instantiation, and it changed LLVM's shaping of
  `Rex`'s drop glue in every `shinri-str` codegen unit, so every
  derivative-heavy path paid. (This resolves the "mechanism not measured"
  gap in the `1261bc9` section below.)
- **The QF_S residual** was re-derivation: infinite languages bring the
  same states back layer after layer, and 70–85% of the walk was `deriv`.
- **The fix** (`fd445aa`, `regex.rs` only): `Empty` never enters a layer
  (no `retain`), and walk states are interned with their `nullable`,
  `next_classes` and per-class `(node_count, child)` recorded at first
  expansion and replayed, with the work-cap checks done in the same order on
  the same counts. Walk time on the QF_S rows went from 1.5–4.1 ms to
  0.6–2.0 ms. No cap, constant or lemma changed.
- **Behaviour neutrality:** the new unit test
  `len_bounds_memo_matches_plain_walk` checks 405 regexes against the old
  walk (kept in the tests as `len_bounds_plain`) at work caps 0, 7, 50, 300,
  2000, `LEN_BOUND_WORK_CAP` and unbounded, including where a cap trips.
  Final-check traces (every `drive_final_check` result) of `1261bc9` and
  `fd445aa` are identical on 452/452 seed-62 sample rows and on 494/494 rows
  of the regressed list plus every 4th Norn file (946 rows).
- Fragility: see queue item 1.

### At `1261bc9` (before the second perf fix; a FAIL)

Method: the brief's script (`target/slice62-after/timing.py`), serial and
interleaved, pinned to core 12, sampled with `random.Random(62)`. Ruling
R10 gates on the 1-min load ≤ 24, waiting at most 30 min
(`timing-watch.sh`, `timing-load.log`). Load was 21.67 at the first check
(2026-10-07T05:24:57Z), after triage and attribution had ended, so pass 1
started at once and R10's fallback was not needed. Pass 1's QF_SLIA ratio
fell outside the band, so passes 2 and 3 followed and the brief's pooling
applies.

| group | pass 1 (load 21.7) | pass 2 (18.8) | pass 3 (18.8) | pooled base → after | pooled ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| QF_S both-`correct` | 1.048 (1.85 → 1.94 s) | 1.027 (1.83 → 1.88 s) | 1.107 (1.67 → 1.85 s) | 5.35 → 5.67 s | **1.060** |
| QF_SLIA both-`correct` | 1.072 (3.35 → 3.59 s) | 1.104 (3.21 → 3.54 s) | 1.109 (3.20 → 3.55 s) | 9.76 → 10.68 s | **1.094** |
| newly-`correct` (150 of 169, not gated) | 1.146 (12.35 → 14.16 s) | 1.030 (13.48 → 13.88 s) | 1.102 (12.90 → 14.21 s) | 38.73 → 42.25 s | 1.091 |

- **By the letter, a FAIL on the slower side.** Unlike slices 59–61, this
  is a slowdown and it reproduces. All three passes are slower, and a
  per-row min-of-5 with alternating order (`timing-rows.txt`) gives
  QF_S **1.116** (1.677 → 1.871 s) and QF_SLIA **1.109**
  (3.205 → 3.555 s).
- **Where it comes from** (min-of-5, per-row deltas):
  - QF_SLIA: 3 large stringfuzz `generated/regexbig`/`regexsmall` rows
    account for 255 ms of the 350 ms gap. These are `regex-big-00050-5`
    868 → 979 ms, `regex-big-00071-0` 1,225 → 1,319 ms and
    `regex-small-00049-10` 214 → 264 ms. 8 small rows take ~+8 ms each
    (84 ms), and the other 139 rows add 10 ms in total.
  - QF_S: 11 rows take ~+8 ms each (61 ms), one automatark row
    (`instance10357`) takes +58 ms, and the other 138 rows add 74 ms
    (~0.5 ms each).
- **Commit bisect** (`timing-bisect.txt`; per-commit release builds in a
  scratch worktree, since removed; internal `wall_ms`, 3 runs each, core 12):

  | commit | `regex-big-00050-5` | `regex-big-00071-0` | automatark `instance14518` | `regex-small-00049-10` |
  | --- | --- | --- | --- | --- |
  | `9ac5105` (base) | 873 906 960 | 1153 1274 1283 | 3 3 3 | 172 180 197 |
  | `0f22551` (T1 `len_bounds`, uncalled) | 851 959 867 | 1113 1283 1147 | 2 2 2 | 222 209 256 |
  | `6551b70` (T2 multi-guard) | 973 819 948 | 1188 1330 1188 | 2 2 2 | 247 207 212 |
  | `d8dbf2d` (T3 bound pass) | 2688 2681 2784 | 4128 4322 4207 | 11 11 9 | 6556 6311 5975 |
  | `59b5b14`, `df3bf3a`, `2c31cb0` | ~2.7–2.8 s | ~3.7–4.4 s | 7–11 | ~5.8–6.4 s |
  | `1261bc9` (R9 budget) | 1062 925 1054 | 1278 1484 1425 | 10 9 9 | 236 200 208 |

  The slowdown arrives with Task 3's bound pass. The R9 work budget removes
  most of it, but not all; the second perf fix removes the rest (above).
- **Direct cost of the walk** (`timing-diag.txt`, throwaway timer build,
  reverted). On each of the four rows `bound_split` runs once, with one
  `len_bounds` miss of 3.0–6.4 ms. The result is `None` (budget spent)
  three times and `(33, None)` once. That explains the ~+6–8 ms steps on
  small rows. It does **not** explain the +100–200 ms on the large regex
  rows, where the pass itself takes 6.5 ms. That indirect cost was later
  traced to `Rex` drop-glue codegen (see the second-fix section above), not
  to arena or cache effects.
- Bench `wall_ms` median / p90 on both-`correct` rows: QF_S 11 / 23 →
  11 / 22 ms; QF_SLIA 6 / 20 → 10 / 30 ms. The after runs launched at load
  29 and the base runs at 17, so these numbers are not comparable on their
  own. They do point the same way as the serial timing for QF_SLIA.

## What changed versus the spec

Controller rulings (SDD ledger, with each one's cost if wrong):

1. **R1: branch in place, no pull.** Task 0 Step 1 was skipped. The branch
   was created off local `main` `9ac5105` (= `origin/main`). Cost if wrong:
   a stale base. Task 0 Step 2's crate diff check (comment-only against
   `f9fa4f9`) still guards it.
2. **R2: `emit_split_guards` plus an `emit_split` wrapper.** Spec §4.5
   changes `emit_split`'s signature. The plan adds `emit_split_guards`
   instead and keeps `emit_split` as a one-line wrapper. Behaviour is
   identical, and no caller had to change.
3. **R3: `lo₀`/`hi₀` over positive members only.** The plan's code took
   them over all members, including complements of negative atoms. Spec
   §4.4 step 4 is binding, so only positive atoms count. This only affects
   whether a redundant lemma is skipped, never soundness.
4. **R4: one existing pin flipped to `unsat`.**
   `script_e2e::in_re_unfold_unsat_disjoint_stars` was the slice-21 KNOWN
   GAP ("single-guard Split channel cannot cite two membership lits"),
   pinned as `unknown`. It now answers `unsat` (`x ∈ a* ∧ x ∈ b* ∧ len ≥ 1`),
   which is the gap the multi-guard lemma closes. The pin and its comment
   were updated. No other pin flipped.
5. **R5: two slice-57 probes re-premised.**
   `slice57_probes::strict_gate_keeps_unevaluable_unknown` used
   `(- (str.len x) (str.len y))` as its "unevaluable" premise, and §4.1 now
   folds that, so the old script answers the now-correct `sat`. It is kept
   as a renamed pin (witness checked). Both it and
   `rf2_strict_flag_does_not_leak_across_checks` get a new assertion the
   gate genuinely cannot evaluate, found by experiment. When strict is
   forced off it answers `sat`, as the original doc says (not
   machine-pinned; deferred minor).
6. **Task 5 fix round (R6): `uf_args_stale`, a gate rule the spec does not
   name.** Task 6 found that §4.2's backstop alone left the UF-argument
   case a wrong `sat`. `eval_num_val` read `f(len x)` at the stale arith
   argument, so the strict gate saw it as confirmed. Fix `2c31cb0` treats
   a UF application as unevaluable when an argument has a numeric model
   value that differs from its evaluated value. This is spec §4.2's stated
   intent ("`sat` only when every assertion is positively confirmed"), but
   it is a change to the solver gate (`crates/shinri-solver/src/lib.rs`)
   that §4.1–4.2 do not describe. Measured: 0 corpus verdicts moved
   (`uf-stale` 0/400, 0 changed rows). Deferred: under the non-strict gate,
   an argument with a numeric model value whose evaluation is `None` also
   counts as stale. That can widen a definite `Some(false)` to `None`. No
   trigger was found; a tighter rule would be `Some(v) != r` only.
7. **R7: oracle bounded confirmation.** Spec §7.3 fails the oracle on any
   shinri `unsat` z3 does not confirm. Neither z3 (`-T:10`) nor cvc5
   decides `z ∈ (ab)* ∧ z ∉ [a-u]*`, which is trivially `unsat`. So on
   (shinri `unsat`, z3 unknown) the oracle re-asks z3 with every string
   leaf bounded `len ≤ 12` (and `v ≤ 12`). Bounded `unsat` counts as
   "bounded-confirmed" (11 in the tally); bounded `sat` or unknown fails.
   Cost if wrong: a wrong `unsat` whose only witnesses are longer than 12
   chars escapes the oracle.
8. **R8: perf regression found mid-measurement.** The first after run at
   `01e3fa8` showed 238 rows `correct`/`unverified → timeout` (stringfuzz
   `regexbig` 210, automatark). The cause was one `len_bounds` walk per
   affected row costing up to 25 s (~5 ms per expanded state on automatark
   regexes) and ending at the step cap with `None`. The run was stopped at
   89,050 rows (wrong = 0, results kept as diagnostic). The defect was
   fixed, and the after run was redone from scratch at `1261bc9`.
9. **R9: `LEN_BOUND_WORK_CAP` = 10,000 derivative node-units (spec §4.3
   deviation).** This is a new budget beside the spec's unchanged caps
   (`LEN_BOUND_DEPTH_CAP`, `MEMB_SEARCH_STEP_CAP`, `FUEL_NODE_CAP`,
   `CLASS_SPLIT_CAP`). The spec's step cap bounds the number of states,
   not their cost. When the budget runs out, the walk returns
   `(min, None)` if a nullable layer was reached and `None` otherwise. It
   only drops the max lemma or the group, which is base behaviour. The
   budget was calibrated from one sweep: every finite-max result seen cost
   ≤ 5.2k units. The residual slowdown at `1261bc9` is dealt with by R11 and
   the second perf fix below.
10. **R10: timing load gate.** On a shared host at load 38–46, the ruling
    was to wait up to 30 min for load ≤ 24 and otherwise run three
    interleaved passes pooled from the start, recording load per pass. In
    the event the load was 21.67 at the first check, so pass 1 ran gated.
    The three passes come from the brief's own pooling rule. R12 below
    judges criterion 4 on more than this three-pass set.
11. **`memb_seeds` became `#[cfg(test)]`.** Spec §4.2 keeps `memb_seeds` as
    a `.0` wrapper over `memb_seeds_flagged` "so existing callers and tests
    are untouched". Task 5 moved the one production caller, `model_with`,
    to `memb_seeds_flagged`, so the wrapper survives only for tests. The
    brief allowed this fallback.
12. **SAT watch order (plan Review Focus 1).** This is in the spec (§4.5,
    "added during planning"), not a deviation. A clause with ≥ 2 guards is
    ordered atoms first, then guards by descending decision level. It is
    pinned by `two_guard_split_detects_violation`.

After the Task 9 analysis (criterion 4 failed at `1261bc9`):

17. **R11: one targeted perf round before ruling on criterion 4.**
    Criterion 4 is hard, so before deciding whether to accept the slowdown or
    gate the pass, one behaviour-neutral perf round was run on the bound
    pass's per-round overhead, with only the Step 5 timing and ci re-run
    afterwards. Result: the second perf fix `fd445aa`. Root cause: a lone
    `Vec<Rex>::retain` in the `len_bounds` walk perturbed `Rex` drop-glue
    codegen crate-wide (about +11% even with `bound_split` returning
    early), plus a QF_S re-derivation of the same walk states at every
    depth. The fix interns walk states (replaying their recorded successors
    with the same cap checks) and drops the `retain`. Only `regex.rs`
    changed; no cap, constant or lemma moved. The ledger's own guess (per-
    round re-extraction of leaf regexes) was refuted: `bound_split` runs
    once per solve on the slow rows. Reviewed: within-layer dedup preserved,
    caps trip on identical inputs. `ci` 1838/1838/6 skipped.
18. **R12: criterion 4 accepted as PASS on the 6-pass pool.** Pooled QF_S
    1.037 / QF_SLIA 1.036, backed by CPU min-of-5 (≤ 1.028) and read against
    the A/A base-vs-base swing 0.92–1.08. By the R10 letter (three passes)
    set 1 fails QF_S at 1.076; this is disclosed, not hidden (see *Timing*).
    Cost if wrong: a real ~+4–7% QF_S slowdown ships.
19. **R13: no third full bench at `fd445aa`.** The after runs are at
    `1261bc9`; `fd445aa` is verified behaviour-neutral (memo test on 405
    regexes × 7 caps; identical final-check traces on 946 bench rows). The
    full oracle suite was re-run at `fd445aa` instead (*Gates*). Cost if
    wrong: a verdict change at `fd445aa` outside the traced rows goes
    unmeasured.
20. **Abandoned `01e3fa8` after run (R8).** Counted above under item 8; its
    results are diagnostic only and no number in this report comes from it.

Task 9 process deviations:

13. **Triage ran 6 rows in parallel** (`xargs -P6`), not the brief's
    serial loop. The per-run command and the noise rule are the brief's.
    Attribution ran at the same time on cores 0–11.
14. **The trace build carries a fourth `eprintln!`, `uf-stale`** (Task 9
    amendment), and the trace edits went into the current code sites. A
    second throwaway build (`timing-diag.txt`) timed `bound_split` and
    `len_bounds`. Both were reverted with `git checkout -- crates`, and
    `git status --short` was empty.
15. **Timing diagnostics beyond the brief:** a per-row min-of-5 with
    alternating order, a per-commit bisect of four rows (scratch worktree,
    removed), and a single low-load re-check of the 15 sample rows.
16. **Base binary is from `9ac5105`, not `cdb5630`** (*Runs*): both are
    `main` with crates that match `f9fa4f9` except for comments.

## Gates

- `target/slice62-gates.txt` at `01e3fa8`: `mise run ci` green, nextest
  1834 run / 1834 passed / 6 skipped (836 s). Oracle
  (`cargo nextest run -p shinri-solver --features oracle`): 854 run / 854
  passed / 2 skipped (1,721 s), with a non-zero discovered count.
- At `1261bc9` (perf fix, `perf-fix-report.md`): `taskset -c 0-11 mise run
  ci` exit 0, **1836** run / 1836 passed / 6 skipped. `cargo fmt --all
  --check` and `mise run lint` are clean. `len_bounds_oracle` was re-run
  (2 passed).
- At `fd445aa` (second perf fix, `perf2-fix-report.md`): `taskset -c 0-23
  mise run ci` exit 0, **1838** run / 1838 passed (9 slow) / 6 skipped
  (1836 + the 2 new `len_bounds` unit tests); `cargo fmt --all --check` and
  `mise run lint` clean. The **full oracle suite was re-run at `fd445aa`**
  (R13): `taskset -c 0-23 cargo nextest run -p shinri-solver --features
  oracle`: **854 run** / 854 passed / 2 skipped, with a
  non-zero discovered count (`target/slice62-oracle-fd445aa.log`).
- `cargo clippy -p shinri-solver --all-targets --features oracle -- -D
  warnings` fails in `qfs_differential`, `fp_oracle` and `nary_oracle`
  (inconsistent digit grouping, `wrong_self_convention`). This is
  **pre-existing on `main` `9ac5105`** (Task 8 compared both). The new
  `len_bounds_oracle.rs` has 0 findings. It stays queued (slice-54 carry).

## Queued for the next slice

Ordered. **Re-ranks** (each stated):

- **New item 1 (build robustness to the `Rex` drop-glue codegen
  sensitivity)** goes first. The timing story changed: the criterion-4
  slowdown was mostly a codegen artifact, not the bound pass's work, and
  the fix is only as stable as LLVM's drop-glue shape. This is cheap, and a
  regression of it would silently cost ~10% on every derivative-heavy
  path. The bound-pass work itself (+1–3% QF_S) drops to item 2.
- **CEGAR length refinement** (spec approach 3) is item 3. It turns the
  item-5 reproducer and R10 from a sound `unknown` into `unsat`. It is also
  the likely route for the parity shapes left in `violated:bool@not-needed`
  (492 after this slice, still the largest tag).
- Slice-61 item 1 (class 1, `violated:memb@not-needed`, **314**,
  unchanged) and item 2 (concat-subject emptiness) follow. Class 1 now
  ranks below `bool@not-needed` (492), `word-eq@rejected` (479) and
  `not-word-eq@not-needed` (352) on counts. It stays above the carried
  word-equation items because it has a trace.
- Slice-61 item 4 (strict gate on unevaluable assertions) absorbs this
  slice's seed flag and the `uf_args_stale` widening. It drops below
  items 1–5 because the backstop moved 0 verdicts in this run (4/400 rows
  fire it, all with unchanged verdicts).
- Slice-61 items 3 and 5 are **closed by this slice**. Norn 135/138 are
  `correct` with valid models, and the item-5 wrong `sat` is `unknown`.
- Slice-61 items 6–9 keep their order below.

1. **Make the build robust to the `Rex` drop-glue codegen sensitivity**
   (`codegen-units = 1` or LTO for the release profile; check in the
   report). The `fd445aa` fix relies partly on a codegen artifact: the
   walk's `Vec<Rex>::retain` was the crate's only such instantiation and
   changed `Rex`'s drop-glue shape (nine copies of 0x1fa bytes instead of
   eight of 0xf8 plus one of 0x37e) for every codegen unit, costing ~11%.
   Any new generic instantiation over `Rex` in `shinri-str` could bring it
   back. Quick check: `nm -C -S target/release/shinri | grep
   'drop_glue::<shinri_str::regex::Rex>$'` (0xf8/0x37e fast, 0x1fa slow).
   Either set the profile and measure with the Step-5 script, or add this
   `nm` check to a bench task. Workspace profile change, so it needs its own
   timing run.
2. **Bound-pass cost** (criterion 4 now PASS per R12; residual ~+1–3% on
   QF_S). One walk per affected row, up to the 10k-unit cap, mostly `deriv`
   on unique states (3.3 ms on `regex-small-00049-10`). Candidates:
   - skip the walk when no bound could beat `lo₀`/`hi₀` (for example, a
     single positive atom whose structural bounds are already exact);
   - cache negative results across guard sets that share their regexes;
   - make `deriv` cheaper.

   Reproducers:
   `QF_SLIA/20230327-stringfuzz-lu/generated/regexbig/regex-big-00050-5.smt2`
   and `QF_S/20230329-automatark-lu/instance14518.smt2`. This item also
   carries **`LEN_BOUND_WORK_CAP` calibration**: 10k units was set from one
   sweep (largest finite-max walk seen: 5.2k units).
3. **CEGAR length refinement** (spec approach 3; parity follow-up). At
   final check, block a free leaf's model length `n` when its intersection
   has no word of length `n`. Targets:
   - the item-5 reproducer and R10 (`x, y ∈ (ab)*`, `len x + len y = 3`,
     z3 `unsat`; now `unknown`);
   - slice-59 item 3's `regex-017-graft-reverse-graft` (`x ∈ (BA)*`,
     `len x = 5`).

   The risk is unbounded enumeration when no length bound stops it, so it
   needs a budget.
4. **Class 1 remainder: 314 rows `violated:memb@not-needed`** (slice-61
   item 1, verbatim trace there). Rows by family: HammingDistance 252,
   Jiang `slog` 44, StringReplace 11, Norn `ab` 2, z3str2 2, automatark 1,
   ChunkSplit 1, denghang 1. Of 10 sampled rows, the `value_dictated` skip
   explains 7. Next step: trace whether the pinning class member is an
   input concat, and whether the joint search can flatten through it.
5. **Concat-subject memberships with a provably empty intersection stay
   `unknown`** (slice-61 item 2 / slice-60 item 4). R8 of slice 61 found
   jointly unsat derivative atoms in Norn SAT states that were never
   refuted. Note: this slice's per-leaf bound pass groups by **bare leaf**
   only. A concat-subject group gets no length lemma, and extending
   `len_bounds` lemmas to `len(x·y)` is a cheap partial step.
6. **Strict gate on unevaluable assertions, and the flags that raise it**
   (slice-61 item 4, extended):
   - 14 Norn rows are blocked by R9's strict gate on an unevaluable leaf
     assertion;
   - this slice's per-leaf seed flag fires on ~1% of string rows (4/400:
     2 `correct`, 2 already-rejected);
   - the flag also fires at model length 0 (no `str.len` entry);
   - **`uf_args_stale`'s non-strict widening**: an argument with a numeric
     model value but `eval_num_val` `None` counts as stale, which can turn
     a definite `Some(false)` into `None`. Tighten it to `Some(v) != r`.

   Scoping strictness to the assertions that mention a re-lengthed leaf
   would address all of these.
7. **Oracle coverage for decided-but-unverified rows** (slice-61 item 7 /
   slice-60 item 5). After this run 1,862 string rows are `unverified`
   `sat` and 411 `unverified` `unsat`. The 6 automatark `unsat` rows that
   z3 and cvc5 never confirmed remain. This run's 40
   `correct ↔ unverified` flips are again the 20 s z3 oracle (stringfuzz
   `generated` 38, denghang `instance46328`, automatark `instance08669`).
   Enabling the bench's cvc5 column would settle most of them.
8. **Witness search cost on newly decided stringfuzz `generated` rows**
   (slice-61 item 8, verbatim there).
9. **`get-value` prints `?` for a never-constrained String** (slice-61
   item 6). Seen again here: the criterion-2 check had to query only the
   mentioned variables.
10. **Candidate (c)** (slice-61 item 9): make Rule-E's disjunct order
   independent of partition granularity (10 HammingDistance
   `sat-budget` rows).
11. **String-valued UF staleness in `eval_str_val`** (Task 5 deferred).
    The gate reads the stored value of a String-valued UF application
    without the staleness check `uf_args_stale` now does for numeric ones.
    It is latent, because String-valued UFs are not supported end to end
    today. Fix it before they are.

Deferred minors from this slice's reviews (not ranked):
- Walk memo: `len_bounds_plain` is kept in the tests only as the oracle for
  `len_bounds_memo_matches_plain_walk`.
- `len_bounds`: the taint paths (`next_classes` overflow, `FUEL_NODE_CAP`,
  step cap) are untested, and there is no boundary test for a finite
  language whose max is exactly `LEN_BOUND_DEPTH_CAP` (64).
  `len_bounds_empty_language_is_none` may be satisfied by `inter()`
  constructor folding. (The `layer.retain` minor is gone: `fd445aa` removed the `retain`.)
- Stale doc comments still describe an `Option` guard: the `types.rs`
  `TheoryResult` doc, the `solver_trait.rs` `TCheck` doc, and the
  `solver.rs` comment above `guard_was_present`. A Task 2 test comment
  writes the clause guards-first.
- `pinned_leaf_emits_no_group_lemma` lacks a positive control. No test
  separates R3 (positive-only `lo₀`/`hi₀`) from the all-members version.
  `lib.rs:88` doc uses `<->`.
- `slice57_probes.rs` has a doc line over 100 columns. The R5 claim that
  strict-off gives `sat` is not machine-pinned.
- The seed flag is set even when a joint seed later overrides the per-leaf
  seed (safe, stricter). There is no mixed-leaf flag test (one leaf
  matches, one does not).
- `r11a`/`r10` probes assert "not `sat`" (`unknown` passes).
  `word_and_int` would misparse a negative Int.
- Oracle: the vacuity floor is only `sat > 0`, and the `unknown` share
  (44/200) is unbounded. Bounded confirmation is weaker than proof, and its
  `12` / 20 s values are not named constants. The probe test discards its
  counters.

Carried from slice 61, not re-ranked:
- Its deferred minors: `joint_seed.rs` `key()` clones per node; the sweep
  guard counts pass 1 only; no `StrSolver`-level unit test of the R8
  filter; `joint_empty_not_sat` / `length_pin_sound` witness paths are
  unexercised; `verdict_with_witness_check` indexes `out[0]`/`out[1]`;
  the Task 5 generator doc comment.
- The verbatim lists it carried (slice-59 items 2–4, slice-58 items 2–3,
  slice-57 deferred minors, slice-56 items 3–6 with the slice-54 carry,
  slice-53 and slice-52 lists, the test-tier note) are unchanged; see the
  slice-61 report, § Queued for the next slice. Annotations from this run:
  - slice-59 item 3 (length/membership conflict, class 2): **104 of its
    rows are now `unsat`** via the bound lemma. The parity remainder moves
    to item 3 above.
  - The slice-51 carry "4 denghang `unknown:str-model-rejected` rows":
    `instance51681` and `55189` are now `correct` (`unsat`); `46836` and
    `52132` remain (`violated:len-arith@not-needed`).
  - The `clippy --features oracle` item (slice-54 carry) is still open;
    Task 8 confirmed it is pre-existing on `main`.

## References

- Spec: `docs/superpowers/specs/2026-10-06-shinri-slice62-length-consistent-seeds-design.md`
- Plan: `docs/superpowers/plans/2026-10-06-shinri-slice62-length-consistent-seeds.md`
- Slice-61 report: `docs/superpowers/research/2026-10-06-smtlib-2024-slice61-joint-concat-seeds-report.md`
- Evidence (not committed): `target/slice62-gates.txt`;
  `target/slice62-base/{commit.txt,md5.txt,probes.txt,probes/}`;
  `target/slice62-oracle-fd445aa.log`;
  `target/slice62-after/timing-perf2.txt`;
  `target/slice62-after/{md5.txt,commit.txt,started.txt,finished.txt,uptime-start.txt,join.txt,changed.tsv,triage-in.tsv,triage.tsv,triage-disp.txt,triage-summary.txt,triage-row.sh,triage_disp.py,triage-uptime-before.txt,triage-uptime-after.txt,unsat-xcheck.txt,crit2/,probes.txt,probes-trace.txt,shinri-trace,attr.sh,attribution.tsv,attribution-allgains.tsv,strict-sample.txt,prevalence.tsv,timing.py,timing-watch.sh,timing-load.log,timing-pass1.txt,timing-pass2.txt,timing-pass3.txt,timing-pooled.txt,timing-rows.py,timing-rows.txt,timing-diag.txt,timing-bisect.txt,sample-recheck.tsv}`;
  `bench/results/slice62{,-sample}/`, base `bench/results/slice61{,-sample}/`,
  abandoned `bench/results/slice62-abandoned-01e3fa8/`.
