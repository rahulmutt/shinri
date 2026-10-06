# SMT-LIB 2024 re-run — slice 61 (joint seeds for concat-subject memberships) — shinri @ f9fa4f9

## Headline

Slice 61 adds `joint_seed::joint_seeds_flagged` (`crates/shinri-str/src/joint_seed.rs`).
At model-build time it chooses witness words for the free leaves of
concat-subject memberships jointly, and the result is merged over
`memb_seeds`' per-leaf seeds. Before this, every operand was seeded
against its own bare membership only, and the gate then rejected the
composed concat. Three controller rulings widened the slice beyond the
spec: R8 (joint constraints come from input memberships only), R9 (strict
gate when a joint seed changes a leaf's length) and R11a (the solver gate
evaluates `+ - *` length arithmetic structurally when the arith model
valued the term). See *What changed versus the spec*.

The benchmarked binary is branch HEAD `f9fa4f9`. The only commits after it
are this report's, and they are docs-only.

- **Rows moved to `correct`: 110**, all QF_SLIA and all `sat`, all with
  corpus status `unknown` and z3 agreeing. All 110 were
  `unknown:str-model-rejected` in base: 108 tagged `violated:memb@not-needed`
  and 2 tagged `violated:not-memb@not-needed`.
  - By family: Norn HammingDistance 75, stringfuzz `transformed/z3str2`
    `regex-035-*` 28, Norn StringReplace 4, Norn `ab` 3.
  - String `correct` rises **+126** in net: QF_S 16,667 → 16,668 and
    QF_SLIA 25,231 → 25,356. That is 110 gains, plus 34 rows the bench's
    z3 oracle confirmed this time (`unverified → correct`), minus 16 rows
    where it timed out (`correct → unverified`), minus 2 losses (below).
- **Criterion 2:** `violated:memb@not-needed` falls **432 → 314**. Of the
  base-tagged rows, **108 (25.0%)** are now `correct` (bar: ≥ 87 and
  ≥ 20%). None became `unverified`.
  - `unknown:str-model-rejected` as a whole falls 2,264 → 2,156.
- **Two `correct → unknown` rows, both caused by the R11a gate fix, not by
  joint seeds.** Norn `ab` `norn-benchmark-135` and `138` answered `sat` in
  base with an **invalid model**: `var_0 = "ab"` but `(str.len var_0) = 4`
  and `v = 3`, which breaks `(= (* v 2) (+ (str.len var_0) 2))`. The answer
  matched z3 only by luck. The after binary's gate re-evaluates the sum from
  the string value and rejects the model. This is the corpus instance of
  ruling R10's pre-existing wrong-`sat` mechanism.
- **Criteria:**

  | # | result |
  | --- | --- |
  | 1 | PASS: 0 `wrong` rows in both after runs; 0 wrong answers in 828 triage runs; no new `unverified` `unsat` row |
  | 2 | PASS: 432 → 314; 108 base-tagged rows (25.0%) now `correct` |
  | 3 | **FAIL by the letter**: 2 attributable `correct → unknown:str-model-rejected` rows (Norn `ab` 135, 138). Both come from the R11a gate rejecting base's invalid model, so this is a soundness fix, not a regression in the answers shinri can justify. Controller ruling R13: met in substance |
  | 4 | **FAIL on the faster side**: pass 1 QF_S 0.982 (inside ±5%), QF_SLIA 0.901 (outside). Pooled over 3 passes: QF_S 0.969 (inside), QF_SLIA 0.931 (outside). A min-of-3 per-row diagnostic gives QF_SLIA 0.987. No slowdown anywhere; newly-`correct` rows 0.93. Controller ruling R14: met in substance |
  | 5 | PASS: ci 1808 / 1808 / 6 skipped; oracle 841 / 841 / 2 skipped |
  | 6 | PASS: 51 sample rows changed, all noise (base-run timeouts under host load; both binaries identical 3/3) |

- **Pass attribution** (40 seeded gain rows): pass 1 (model lengths) 15,
  pass 2 (free lengths) 25. Every pass-2 gain also raised the R9 strict-gate
  flag and still passed the gate.
- **R10 is closed incidentally.** The bare-variable variant
  (`x, y ∈ (ab)*`, `len x + len y = 3`, z3 `unsat`) is a wrong `sat` on
  the base binary (`x = "ab"`, `y = ""`) and `unknown` on the after binary.

## Commands

Task 0 (base check, no new base run). The base is the slice-60 variant's
runs and binary (see *Runs*).

```bash
git diff --quiet 56997aa HEAD -- crates Cargo.toml Cargo.lock && echo "crates identical"
mkdir -p target/slice61-base
cat target/slice60b-after/commit.txt | tee target/slice61-base/commit.txt
md5sum target/slice60b-after/shinri | tee target/slice61-base/md5.txt
wc -l bench/results/slice60b/results.jsonl bench/results/slice60b-sample/results.jsonl
find target/slice59-sample-corpus -name '*.smt2' | wc -l
python3 - <<'PY' | tee target/slice61-base/tagcount.txt   # violated:memb@not-needed count and families
...
PY
# throwaway trace build of the reproducers, then reverted
cargo build --release -p shinri-cli --target-dir target/slice61-trace
git checkout -- crates && git status --short crates
# probes: norn531, regex035, empty, empty-sat-sibling, lenpin -> target/slice61-base/probes/
for f in $D/*.smt2; do printf '%s\t' $(basename $f); target/slice60b-after/shinri --stats $f 2>&1 | grep '^stats:'; done | tee target/slice61-base/probes.txt
for f in $D/*.smt2; do printf '%s\t' $(basename $f); mise exec -- z3 -T:20 $f; done
```

Task 6 (gates): `mise run ci` and
`cargo nextest run -p shinri-solver --features oracle`, recorded in
`target/slice61-gates.txt`.

Task 7:

```bash
# Step 1: build, freeze, launch detached
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice61-after && cp target/release/shinri target/slice61-after/shinri
cp target/release/shinri-bench target/slice61-after/shinri-bench
md5sum target/slice61-after/shinri | tee target/slice61-after/md5.txt
git rev-parse --short HEAD | tee target/slice61-after/commit.txt
uptime | tee target/slice61-after/uptime-start.txt
date -u +%FT%TZ > target/slice61-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice61-after/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice61-after/shinri --run-id slice61 \
  > target/slice61-after/run.log 2>&1; \
  taskset -c 12-23 target/slice61-after/shinri-bench run \
  --logics QF_BVFP,QF_DT,QF_LIA,QF_LRA,QF_UF,QF_UFLIA,QF_UFLRA \
  --corpus target/slice59-sample-corpus --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice61-after/shinri --run-id slice61-sample \
  > target/slice61-after/run-sample.log 2>&1; \
  date -u +%FT%TZ > target/slice61-after/finished.txt' \
  > /dev/null 2>&1 &
# Step 2: reports and join (brief script verbatim) -> join.txt, changed.tsv
for id in slice60b slice61 slice60b-sample slice61-sample; do BENCH_RUN_ID=$id mise run bench-report; done
# Step 3: triage-in.tsv (brief script verbatim, random.Random(61)); rows 6 at a time, detached
tr "\t" " " < target/slice61-after/triage-in.tsv | xargs -P6 -L1 target/slice61-after/triage-row.sh > target/slice61-after/triage.tsv
#   per binary and run: taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats $root/$p
python3 target/slice61-after/triage_disp.py     # -> triage-disp.txt, triage-summary.txt
# Step 4: throwaway trace build (brief's 4 eprintln!s + 2 diagnostics, see Pass attribution), reverted
cargo build --release -p shinri-cli --target-dir target/slice61-trace
git checkout -- crates && git status --short crates     # printed nothing
#   attr-in.txt / still-in.txt (brief scripts, random.Random(61)) -> attribution.tsv, still.tsv (cores 0-11)
# Step 5: timing.py (brief script verbatim), 3 passes, gated on 1-min load <= 24 (timing-watch.sh)
#   timing-swapped.py (after before base) and a per-row min-of-3 diagnostic (timing-slia-rows.txt)
```

## Runs

| run | solver | md5 | started | finished | rows |
| --- | --- | --- | --- | --- | ---: |
| `bench/results/slice60b/` (base) | `target/slice60b-after/shinri` (`56997aa`) | `6109b2a0266510f2084dab2df1e60240` | 2026-10-05T06:34:28Z | (string leg ends when the sample leg starts, 09:14:12Z) | 103,335 |
| `bench/results/slice60b-sample/` (base) | same | same | 2026-10-05T09:14:12Z | 2026-10-05T09:33:23Z | 2,000 |
| `bench/results/slice61/` | `target/slice61-after/shinri` (`f9fa4f9`) | `8fa66e7ec36c0670af8bcda06bcdd379` | 2026-10-05T21:36:28Z | (string leg ends when the sample leg starts, 2026-10-06T00:06:14Z) | 103,335 |
| `bench/results/slice61-sample/` | same | same | 2026-10-06T00:06:14Z | 2026-10-06T00:22:29Z | 2,000 |

- All runs used `--timeout 20 --mem-mb 3072 --jobs 6` on cores 12–23.
  Each `results.jsonl` holds its rows plus one fixture line (103,336 and
  2,001 lines). The base and after row sets are identical.
- **Why the base is `56997aa`, not the spec's `5aa164a`.** The spec names
  `main` `5aa164a` as the base. `56997aa` is the slice-60 Rule-E variant
  commit, whose `crates/` are identical to `main`'s (Task 0:
  `git diff --quiet 56997aa HEAD -- crates Cargo.toml Cargo.lock` at the
  branch point). Its runs `slice60b{,-sample}` are therefore base runs for
  this slice, and they were reused instead of re-run. Task 0 confirmed the
  md5 and the row counts.
- The after runs' fixture records `sha` `f9fa4f9dff52` and `solver_md5`
  `8fa66e7e…`, which matches `target/slice61-after/md5.txt`.
- **Host load.** At launch the 1-min load average was 16.71 (5-min 19.83,
  15-min 35.98) on 24 cores (`uptime-start.txt`); at the end of the sample
  leg it was 29.74. The 10-minute progress ticks during the string leg read
  13.5–39.6. The base runs `slice60b` ran under heavier external load (70+
  at its triage), which explains the 51 sample-run changes (see
  *Neutrality sample*).

## Success criteria (spec §8)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | **PASS** | 0 `wrong` rows in `slice61` and `slice61-sample`. 0 `sat` ↔ `unsat` flips. Triage made 828 runs over 138 rows: no row got both `sat` and `unsat`, and no decided run contradicts a known corpus status. No row became `unverified` with an `unsat` answer, so the brief's unsat cross-check had no input (the only `unsat` row that moved, automatark `instance14507`, went `unverified → correct`; slice 60b's cross-check already confirmed it with z3 and cvc5) |
| 2 | `violated:memb@not-needed` shrinks by ≥ 20% (≥ 87 rows) of 432, moving to `correct` | **PASS** | 432 → 314. 108 base-tagged rows (25.0%) are now `correct`; 0 `unverified` |
| 3 | no `correct → non-correct` change that reproduces 3/3 | **FAIL (by the letter)** | 2 rows reproduce 3/3: `QF_SLIA/2015-Norn/ab/norn-benchmark-135.smt2` and `-138.smt2`, base `sat` → after `unknown:str-model-rejected` (`violated:bool@not-needed`). The trace build shows `gate-arith-diff` and no joint-seed group, so the R11a gate change is the cause. Base's `sat` came with an invalid model (see *The two `correct → unknown` rows*). Reported, not tuned. Controller ruling R13: met in substance |
| 4 | serial interleaved timing on 150 both-`correct` rows per string logic, within ±5% | **FAIL (outside the band on the faster side)** | Pass 1: QF_S 0.982 (in band), QF_SLIA 0.901 (out). Pooled over 3 passes: QF_S **0.969** (in band), QF_SLIA **0.931** (out). Swapped order: 0.987 / 0.947. Min-of-3 per row on the QF_SLIA sample: 0.987. Newly-`correct` rows: 0.93 pooled, no slowdown. See *Timing*. Controller ruling R14: met in substance |
| 5 | `mise run ci` green; oracle discovered count ≥ 831 + this slice's oracle tests | **PASS** | `target/slice61-gates.txt` at `f9fa4f9`: ci 1808 run / 1808 passed / 6 skipped (1773 + 35 new: 2 `regex`, 12 `joint_seed` core, 13 `joint_seed` front, 5 probes, 3 gate-arith). Oracle `--features oracle`: 841 run / 841 passed / 2 skipped; ≥ 831 + 2 `joint_seed_oracle` tests, non-zero discovered count |
| 6 | neutrality sample: only non-reproducible timing flips | **PASS** | 51 sample rows changed, every one from a base `timeout`. Triage: all 51 are noise, with identical results from both binaries 3/3 (24 `unsat`, 7 `sat`, 20 OOM) |

Probe outcomes. Task 0 (base binary `56997aa`): `norn531`, `regex035` and
`empty-sat-sibling` answer `unknown` (`str-model-rejected`,
`violated:memb@not-needed`); `empty` and `lenpin` answer `unknown`
(`sat-budget`). z3: `sat`, `sat`, `sat`, `unsat`, `sat`. After binary:
`norn531`, `regex035` and `empty-sat-sibling` answer `sat`; `empty` and
`lenpin` stay `unknown`; `lensum` (Task 3's review repro, z3 `unsat`) is
`unknown` (`target/slice61-after/r10/results.tsv`). Task 4's
`slice61_probes` are RED on `main` for the three `sat` probes (they get
`unknown`) and GREEN on HEAD, 5/5.

### R10 check: the pre-existing wrong `sat` on main

The R10 shape is bare memberships plus compound length arithmetic, with no
concat subject:

```smt2
(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (= (+ (str.len x) (str.len y)) 3))
(check-sat)
```

z3: `unsat`. Base binary (`56997aa`, `main`'s crates): **`sat`** with
`x = "ab"`, `y = ""`. That is a wrong answer, and the witness's lengths sum
to 2. After binary: `unknown` (`str-model-rejected`,
`violated:bool@not-needed`); the trace build prints `gate-arith-diff`. The
cause is `memb_seeds`' shortest-word fallback combined with a gate that read
the stale arith value of `(+ (str.len x) (str.len y))`. R11a closes it, so
R10 moves from "queued" to "fixed incidentally". Norn `ab` 135 and 138 are
the same mechanism in the corpus, but there the answer happened to be
right (`target/slice61-after/r10/`).

### The two `correct → unknown` rows

Both rows are `QF_SLIA/2015-Norn/ab`, with corpus status `unknown`. In base
they count as `correct` because z3 also says `sat`.

`norn-benchmark-135` constrains `var_0` to `a*b ∩ a*b+ ∩ ab* ∩ [a-u]*`,
so `var_0 = "ab"`, plus `(= (* v 2) (+ (str.len var_0) 2))`. Base's model,
from `get-value`:

```
((var_0 "ab") (v 3) ((str.len var_0) 4) ((* v 2) 6) ((+ (str.len var_0) 2) 6))
```

The arith model gave `str.len var_0` the value 4, while the string model's
`var_0` has length 2. `memb_seeds`' shortest-word fallback ignored the
model length. The old gate read the arith value of the compound sum, so it
accepted a model in which `2 * 3 ≠ 2 + 2`. z3's model is `var_0 = "ab"`,
`v = 2`. `norn-benchmark-138` is the same shape over `var_4` (base model
`var_4 = "ab"`, `v = 3`).

The after binary's gate (R11a) evaluates `(+ (str.len var_0) 2)` from the
string value, gets 4 ≠ 6, and rejects. The trace build shows two
`gate-arith-diff` lines and no joint-seed group. Each binary reproduces its
own verdict 3/3. By the letter of criterion 3 this is a FAIL. In substance,
base was right only by luck, with a witness that does not satisfy the
script. Getting these two rows back soundly needs a length-consistent seed
for bare memberships, which is the R10 follow-up in the queue.

## Verdict changes

### String runs (QF_S + QF_SLIA)

Verdict counts (base → after), from `bench/results/{slice60b,slice61}/report.md`:

| verdict | QF_S base | QF_S after | QF_SLIA base | QF_SLIA after |
| --- | ---: | ---: | ---: | ---: |
| correct | 16,667 | 16,668 | 25,231 | 25,356 |
| parse-error | 0 | 0 | 195 | 195 |
| timeout | 6 | 6 | 48 | 45 |
| unknown:reglan-decl | 0 | 0 | 3,287 | 3,287 |
| unknown:sat-budget | 1,381 | 1,381 | 4,245 | 4,248 |
| unknown:str-indexof-replace | 80 | 80 | 26,283 | 26,283 |
| unknown:str-int-conv | 0 | 0 | 1,616 | 1,616 |
| unknown:str-model-rejected | 323 | 323 | 1,941 | 1,833 |
| unknown:str-predicate-polarity | 0 | 0 | 16,016 | 16,016 |
| unknown:str-regex | 343 | 343 | 26 | 26 |
| unknown:str-substr-at | 0 | 0 | 3,359 | 3,359 |
| unknown:theory-refused | 0 | 0 | 35 | 35 |
| unverified | 140 | 139 | 2,113 | 2,096 |
| wrong | 0 | 0 | 0 | 0 |

Changed rows: 165 (`target/slice61-after/join.txt`).

| logic | base | after | rows | triage |
| --- | --- | --- | ---: | --- |
| QF_SLIA | unknown:str-model-rejected | correct | 110 | gain (32 sampled, attributable 3/3 as expected); all `sat` |
| QF_SLIA | unverified | correct | 33 | noise: identical `sat` 3/3 on both binaries; only the bench's z3 oracle finished this time (all stringfuzz `generated`) |
| QF_S | unverified | correct | 1 | noise: automatark `instance14507`, `unsat` from both binaries |
| QF_SLIA | correct | unverified | 16 | noise: identical `sat`; the z3 oracle timed out in after (all stringfuzz `generated`) |
| QF_SLIA | timeout | unknown:sat-budget | 3 | noise: Leetcode `findAnagrams`, `sat-budget` from both binaries 3/3 |
| QF_SLIA | correct | unknown:str-model-rejected | 2 | **attributable** (criterion 3): Norn `ab` 135, 138, R11a gate (above) |

No Norn, Jiang `slog` or stringfuzz row moves from `correct` to anything
else apart from these two and the oracle churn.

### `fence_detail` movement (rows `unknown:str-model-rejected`, string runs)

| tag | base | after |
| --- | ---: | ---: |
| `violated:bool@not-needed` | 594 | 598 |
| `violated:word-eq@rejected` | 479 | 479 |
| `violated:not-word-eq@not-needed` | 352 | 352 |
| `violated:memb@not-needed` | 432 | **314** |
| `violated:len-arith@not-needed` | 242 | 242 |
| `unevaluable:other:uf@adopted` | 111 | 111 |
| `violated:not-memb@not-needed` | 19 | 9 |
| `violated:bool@rejected` | 17 | 17 |
| `violated:memb@adopted` | 16 | 16 |
| `unevaluable:other:leaf@not-needed` | 0 | 13 |
| `violated:not-bool@adopted` | 2 | 2 |
| `violated:not-bool@not-needed` | 0 | 2 |
| `unevaluable:not-other:leaf@not-needed` | 0 | 1 |

`violated:bool@not-needed` gains 4: the 2 `ab` losses, plus 2 tag moves.

**Tag moves without a verdict change** (18 rows, `target/slice61-after/tagmove.tsv`,
traced in `nongain-trace.tsv`): Norn StringReplace 14, HammingDistance 2,
`ab` 1, ChunkSplit 1.

| base tag | after tag | rows | trace |
| --- | --- | ---: | --- |
| `violated:memb@not-needed` | `unevaluable:other:leaf@not-needed` | 6 | joint seed pass 2 + strict flag |
| `violated:not-memb@not-needed` | `unevaluable:other:leaf@not-needed` | 7 | joint seed pass 2 + strict flag |
| `violated:memb@not-needed` | `unevaluable:not-other:leaf@not-needed` | 1 | pass 2 + strict |
| `violated:memb@not-needed` | `violated:not-bool@not-needed` | 2 | 1 pass 2 + strict, 1 pass 1 |
| `violated:memb@not-needed` | `violated:bool@not-needed` | 1 | pass 2 + strict + `gate-arith-diff` (`ab/norn-benchmark-140`) |
| `violated:not-memb@not-needed` | `violated:bool@not-needed` | 1 | pass 2 + strict (`HammingDistance/norn-benchmark-22`) |

On these rows the joint seed fixes the membership the gate used to name,
and the gate now stops at a later assertion. On 14 of them that assertion is
**unevaluable**, which only rejects because R9 forced the strict gate.
Without R9 the non-strict gate would skip the unevaluable assertion and
might accept; whether such a model would be right is not known (queue
item 2).

### Base `violated:memb@not-needed` rows, by family and after verdict

| family | rows | correct | unverified | still tagged | other tag |
| --- | ---: | ---: | ---: | ---: | ---: |
| Norn HammingDistance | 326 | 73 | 0 | 252 | 1 |
| Jiang `slog` | 44 | 0 | 0 | 44 | 0 |
| stringfuzz `transformed/z3str2` | 30 | 28 | 0 | 2 | 0 |
| Norn StringReplace | 22 | 4 | 0 | 11 | 7 |
| Norn `ab` | 6 | 3 | 0 | 2 | 1 |
| Norn ChunkSplit | 2 | 0 | 0 | 1 | 1 |
| automatark | 1 | 0 | 0 | 1 | 0 |
| denghang | 1 | 0 | 0 | 1 | 0 |

- All 28 `regex-035-*` rows (slice-60 queue item 3) are now `correct`. The
  2 z3str2 rows still tagged are not `regex-035`
  (`regex-050-rotate-fuzz-fuzz`, `regex-050-translate-fuzz`).
- Rows moved to `correct`, by corpus status: unknown 108 (z3-confirmed `sat`).
  No corpus-`sat` or corpus-`unsat` row was in this population.
- The 2 non-tag gains are Norn HammingDistance `norn-benchmark-124` and
  `246`, base tag `violated:not-memb@not-needed` (a negated concat-subject
  membership, which joint seeds handle as `comp(R)`).

Still tagged after (314): Norn HammingDistance 252, Jiang `slog` 44, Norn
StringReplace 11, Norn `ab` 2, z3str2 2, automatark 1, ChunkSplit 1,
denghang 1.

### Neutrality sample (seven other logics, 2,000 rows)

| logic | base | after | rows | triage |
| --- | --- | --- | ---: | --- |
| QF_UF | timeout | correct | 22 | noise: identical answers from both binaries 3/3 |
| QF_UFLIA | timeout | correct | 6 | noise |
| QF_LIA | timeout | correct | 3 | noise |
| QF_LIA | timeout | oom | 15 | noise: OOM from both binaries 3/3 |
| QF_UFLIA | timeout | oom | 2 | noise |
| QF_UFLRA | timeout | oom | 3 | noise |

Every change is a base `timeout`. The base sample run (`slice60b-sample`)
ran under heavy external load; slice 60b's own report shows the mirror
image, with `correct → timeout` and `oom → timeout` on the same families.
In triage, the 31 `timeout → correct` rows give `unsat` (24) or `sat` (7)
3/3 on **both** binaries, and the 20 `timeout → oom` rows OOM 3/3 on both.
0 `wrong`. The R11a gate change is on the string model path; no sample row
shows any binary difference.

## Triage

Files: `target/slice61-after/{triage-in.tsv,triage.tsv,triage-disp.txt,triage-summary.txt}`.

Method: the brief's command and noise rule. Base binary
`target/slice60b-after/shinri` vs after binary
`target/slice61-after/shinri`, 3 interleaved runs each, on cores 12–23,
6 rows in parallel (`triage-row.sh`, as in slice 60). Ran
2026-10-06T00:23:00Z–00:35:20Z. Load averages (1-, 5-, 15-min):
`26.02, 28.68, 27.33` before and `16.88, 20.84, 24.62` after.

Selection: 138 rows. There are 106 non-gain rows (55 string + 51 sample),
fewer than 200, so all were triaged. The brief's seeded
(`random.Random(61)`), family-stratified gain sample adds 32.

| transition | rows | noise | attributable |
| --- | ---: | ---: | ---: |
| gain (`unknown:* → correct`) | 32 | 0 | 32 (expected) |
| `correct → unknown:str-model-rejected` | 2 | 0 | **2** |
| `correct → unverified` | 16 | 16 | 0 |
| `unverified → correct` | 34 | 34 | 0 |
| `timeout → unknown:sat-budget` | 3 | 3 | 0 |
| sample `timeout → correct` | 31 | 31 | 0 |
| sample `timeout → oom` | 20 | 20 | 0 |

- Wrong answers: 0. Attributable `correct → non-correct`: 2 (criterion 3,
  gate-caused). Attributable sample rows: 0.
- The 32 sampled gains: the after binary answers `sat` 3/3 on every one,
  and base answers `unknown:str-model-rejected` 3/3.
- **Unsat cross-check:** not needed. No after row is `unverified` with
  answer `unsat` that was not so in base. The 16 new `unverified` rows are
  all `sat`, with base's answer reproduced.
- **R9 strict flag at model length 0** (Task 3 deferred minor): no gain was
  lost in triage. Every non-gain string row is either oracle churn, the 3
  Leetcode timeouts, or the 2 gate rows.

## Pass attribution

Throwaway trace build of `f9fa4f9` (`target/slice61-trace`, copied to
`target/slice61-after/shinri-trace`). It carries the brief's four
`eprintln!`s, at the addendum's sites in `joint_seeds_flagged`: `pass1`,
`pass2`, `none`, and `skip-pinned` before the `value_dictated` `continue`.
It also carries two diagnostics the addendum asked for, to separate
gate-caused from joint-seed-caused changes:
- `strict`, printed when `length_changed` is true;
- `gate-arith-diff`, in `eval_num_val`, printed when the structural value
  differs from the arith model's value.

Reverted with `git checkout -- crates`; `git status --short crates` printed
nothing.

**Gains** (`attribution.tsv`, 40 rows sampled with `random.Random(61)` from
the 110):

| family | pass 1 | pass 2 |
| --- | ---: | ---: |
| Norn HammingDistance | 11 | 16 |
| stringfuzz z3str2 `regex-035-*` | 1 | 9 |
| Norn `ab` | 2 | 0 |
| Norn StringReplace | 1 | 0 |
| **total** | **15** | **25** |

- Every pass-2 gain also printed `strict`. So the strict gate accepted all
  25: their models have no unevaluable assertion.
- No gain printed `gate-arith-diff`. The gains come from joint seeds, not
  from the gate change.
- Pass 1 alone would have reached 15 of 40: free lengths (pass 2) carry most
  of the slice. The `regex-035` reproducer itself is solved in pass 1, but
  9 of its 10 siblings need pass 2.

**Still tagged** (`still.tsv`, 10 rows sampled from the 314):

| outcome | rows | rows' families |
| --- | ---: | --- |
| group skipped (`skip-pinned`: a leaf's class holds a string constant or a non-minted concat) | 7 | Norn HammingDistance |
| group formed, both passes found nothing (`none`) | 1 | Norn HammingDistance (`norn-benchmark-743`) |
| no eligible group (`no-group`) | 2 | Jiang `slog` (`slog_stranger_2614_sink`, `4560_sink`) |
| group solved, gate rejected for another reason | 0 | |

**Non-gain rows** (`nongain-trace.tsv`): the 2 losses show only
`gate-arith-diff`. The oracle-churn and Leetcode rows show no trace line at
all. The 18 tag moves are joint-seed rows (above).

## Timing

Method: the brief's script (`target/slice61-after/timing.py`), serial and
interleaved, pinned to core 12, sampled with `random.Random(61)`. The
script ran three times back to back (`timing.txt`, `timing-rerun2.txt`,
`timing-rerun3.txt`), gated on a 1-min load ≤ 24 (`timing-watch.sh`,
`timing-load.log`). It ran 2026-10-06T00:36:13Z–00:39:24Z, at a 1-min
load of 12.15 at the start and 7.01 at the end. Triage had finished and
nothing else of ours was running.

| group | pass 1 | pass 2 | pass 3 | pooled base → after | pooled ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| QF_S both-`correct` | 0.982 (1.20 → 1.18 s) | 0.914 (1.18 → 1.08 s) | 1.001 (1.15 → 1.16 s) | 3.53 → 3.42 s | **0.969** |
| QF_SLIA both-`correct` | 0.901 (2.17 → 1.95 s) | 0.919 (2.14 → 1.97 s) | 0.973 (2.05 → 2.00 s) | 6.36 → 5.92 s | **0.931** |
| newly-`correct` (144 rows, not gated) | 0.931 (28.49 → 26.53 s) | 0.933 (28.45 → 26.55 s) | 0.934 (28.43 → 26.57 s) | 85.37 → 79.65 s | 0.933 |

- Pass order is from `timing-load.log` and the file mtimes: pass 1 =
  `timing.txt` (ended 00:37:16Z), pass 2 = `timing-rerun2.txt`, pass 3 =
  `timing-rerun3.txt`.
- **By the letter, a FAIL on the faster side.** In pass 1, QF_S is inside
  ±5% (0.982) and QF_SLIA is outside (0.901). Per the brief, two more
  passes were pooled: QF_S stays in band (0.969), QF_SLIA does not
  (0.931). Pass 2 has both logics outside (0.914 / 0.919).
- **Diagnostics.** A pass with after run first (`timing-swapped.txt`)
  gives 0.987 / 0.947. A per-row min-of-3 on the same 150 QF_SLIA rows
  (`timing-slia-rows.txt`) gives **0.987** (1.931 → 1.905 s). The
  summed-ratio gap comes from a few rows of about 5–30 ms whose single runs
  jitter by up to 2×. The largest, `regex-small-00021-10`, reports an
  internal `wall_ms` of 14–17 on base and 12–13 on after over 5 runs.
  Total sample time is about 2 s over 300 process launches, so per-launch
  overhead may be a sizeable share of it; I did not measure that
  separately.
- **No slowdown.** The slice adds work only in `model_with`, after SAT, and
  only when an eligible group exists, so no real speed-up is expected
  either. I read the result as "no slowdown, within noise", as slices 60
  and 60b did for their out-of-band speed-ups.
- **Newly-`correct` rows (144 = 110 gains + 34 oracle churn):** 0.933, so
  there is no reproducible slowdown. I did not break that group's time
  down by row, so which rows dominate it is not measured. The 34
  oracle-churn rows give the same answer on both binaries.
- Bench `wall_ms` median / p90 on both-`correct` rows: QF_S 17 / 56 →
  11 / 23 ms; QF_SLIA 14 / 54 → 6 / 19 ms. The runs shared the machine
  differently (base under 70+ load), so these are not comparable.

## What changed versus the spec

Controller rulings, each with its reason and its cost if wrong (from the
SDD ledger):

1. **R1: branch in place, no pull.** Task 0 Step 1 was skipped. The branch
   was created in place off `main` `1736094`, by the user's choice, and
   `main` was clean at the plan commit. Cost if wrong: the base differs from
   `origin/main`. Step 2's crate-identity check still catches that.
2. **R2: count slip.** Task 3 Step 6 expects 12 `joint_seed` core tests +
   2 `regex` tests (+ front tests). The plan's "13" was an arithmetic slip.
   Cost if wrong: none (a count only).
3. **R3: RED worktree path.** Task 4's RED check used
   `target/slice61-red-wt` (git-ignored, inside the repo) instead of
   `../slice61-red`, because the parent of `/workspace` is `/` and may be
   unwritable. Cost if wrong: none; it is throwaway.
4. **R4: no push or PR in Task 7.** Task 7 Step 8 stops after the local
   commit. Push and PR come after the final whole-branch review, because
   they are outward-facing. Cost if wrong: the PR opens a little later. The
   PR body material is under *PR body material* below.
5. **R5: minted Rule-S1 concats don't disqualify a leaf.** Spec §4.3 skips
   a group if any leaf is `model::is_repair_pinned`. Task 0 found both
   reproducers' leaves pinned, but only by solver-minted Rule-S1 concats
   (`!strk*` operands, `memb.rs` ~481–501). The gate ignores minted
   equalities. `joint_seeds` therefore uses a local, narrower test,
   `value_dictated`: a leaf disqualifies its group iff its EUF class holds
   a string constant other than itself, or a concat that is not minted. A
   concat is minted iff every flattened operand leaf is a reserved
   nullary symbol. `memb_seeds` and `is_repair_pinned` are untouched. Cost
   if wrong: a seed overriding a minted split could break some invariant
   other than the gate, so rows would go `unknown`, never wrong, because
   the gate re-checks. Revert = restore the `is_repair_pinned` call.
6. **R6: tests for R5.** Task 3 added a front test pinning R5: a leaf whose
   class holds a minted `!strk` concat is seeded. It kept
   `pinned_leaf_skips_its_group_only`: a constant merge still skips. Cost
   if wrong: one extra test.
7. **R7: Task 0 had no review.** Task 0 has no repo diff, so the controller
   checked its artifacts instead of dispatching a reviewer. Cost if wrong:
   none; the evidence is in `target/slice61-base/`.
8. **R8: joint constraints come from input memberships only
   (`minted_membs`).** Spec §4.2 takes constraints from `memb_true`. Task 3
   found that `norn-benchmark-531`'s `memb_true` (13 group constraints) is
   **jointly unsat** per z3. The cause is Rule-S/E derivative atoms that
   carry SAT decisions the incomplete theory never refuted (concat-subject
   emptiness, queue item 3 below). `StrSolver` now keeps a monotone
   `minted_membs: FxHashSet<TermId>`, filled at the `StrInRe` mint sites in
   `memb.rs` (the S3/S4 heads and the Rule-E residual atom). `model_with`
   passes only non-minted memberships to the joint search. This mirrors the
   `minted_eqs`/`input_eqs` split. It is pure bookkeeping: Rule-S/E logic is
   unchanged, but the spec's "no Rule-E change" is touched by the set
   inserts. Cost if wrong: if a derived atom were needed for a gate-passing
   model, the group is under-constrained and the gate rejects (`unknown`,
   never wrong). Revert = drop the filter. Known minor: hash-consing means a
   Rule-E atom equal to an input atom marks the input as minted
   (completeness only).
9. **R9: strict gate when a joint seed changes a leaf's length.** Task 3's
   review found a new wrong `sat`: `x·y ∈ (ab)*`, `len x + len y = 3`
   (z3 `unsat`). Pass 2 ignores arith lengths, and the non-strict gate
   treated the compound `+` over `str.len` as satisfied. Spec §4.5's
   gate-backstop argument holds only for atomic `str.len` comparisons. When
   any adopted word's length differs from `class_len_in_model`,
   `model_with` now calls `m.require_strict_check()` (the slice-57 flag).
   Cost if wrong: the strict gate rejects some legitimate pass-2 models, so
   fewer gains (criterion 2 risk), never wrong answers. Measured: all 25
   sampled pass-2 gains passed the strict gate. 14 tag-moved rows stop at
   an unevaluable assertion that only rejects under strict (queue item 2).
10. **R10: the pre-existing wrong `sat` on main.** Bare `x, y ∈ (ab)*` with
    `len x + len y = 3` is a wrong `sat` on `main` (`x = "ab"`, `y = ""`),
    via `memb_seeds`' shortest-word fallback plus compound length
    arithmetic. It was first ruled out of scope (`memb_seeds` is frozen),
    then amended: R11a closes it incidentally. **Verified:** base `sat`
    (wrong), after `unknown` (*R10 check* above). The corpus has two
    instances where the wrong model happened to give the right answer (Norn
    `ab` 135, 138); they are criterion 3's two rows.
11. **R11 / R11a: the gate evaluates length arithmetic structurally,
    narrowed to valued terms.** This deviates from spec §2/§5's "no
    model-gate change". R11 had `eval_num_val`
    (`crates/shinri-solver/src/lib.rs` ~1594) evaluate `+`, `-`, unary `-`
    and `*` from their evaluated operands. It broke the existing test
    `model_reject::tests::unevaluable_compound_len_arith`, so R11a narrowed
    it: only when the model **holds** a `Num` value for the compound term,
    and every operand evaluates, is the structural value returned. With no
    model value the behaviour is exactly as before (`None`). The spec's
    soundness rests on the gate re-checking `str.len` (§4.5), and the gate
    broke that promise for compound arithmetic, on `main` too. Cost if
    wrong: unexpected verdict churn in other string rows. Measured: 2 rows
    (`correct → unknown`, both invalid base models) and 1 tag move; 0 in
    the neutrality sample. Residual hole: a compound term with no arith
    value stays unevaluable and passes the non-strict gate (queue item 4).
12. **R12: Task 6 had no review.** Task 6 has no repo diff; the controller
    checked `target/slice61-gates.txt`. Cost if wrong: none.
13. **R13: criterion 3 treated as met in substance.** The criterion is
    still a FAIL by the letter. The two `correct → unknown` rows
    (`norn-benchmark-135`, `138`) had **invalid** base witnesses and were
    correct by luck. The R11a gate now rejects them; this is the corpus form
    of R10, a soundness fix. Cost if wrong: −2 `correct` rows until seeds
    for bare memberships that respect model lengths bring them back soundly
    (queue item 3).
14. **R14: criterion 4 treated as met in substance.** The criterion is
    still a FAIL by the letter. The deviation is a speed-up, the same
    pattern as slices 60 and 60b, and the per-row min-of-3 gives 0.987.
    Cost if wrong: an unexplained timing effect goes unnoticed; no
    correctness risk.
15. **Plan task reordering.** Spec §6 orders the work as trace, extraction
    and grouping, search pass 1, pass 2, wiring with probes, oracle, bench.
    The plan builds the pure search core first: Task 1 is pass 1, Task 2
    is pass 2 plus the sweep, and both are testable without a `Context`.
    The front end (extraction, grouping, `joint_seeds`) and the wiring
    follow in Task 3, then probes (4), oracle (5), gates (6) and bench (7).
16. **Entry point name.** The spec's `joint_seeds(...) -> FxHashMap` ships
    as `joint_seeds_flagged(...) -> (FxHashMap, bool)`. The flag drives R9.
    It is called with the input-membership slice (R8), not `memb_true`.

Task 7 process deviations:

17. **Triage ran 6 rows in parallel** (`xargs -P6`, as in slice 60), not
    the brief's serial loop. The per-run command and the noise rule are the
    brief's. All 106 non-gain rows were triaged (< 200).
18. **The trace build carries two extra diagnostics**, `strict` and
    `gate-arith-diff`, to separate gate-caused from joint-seed-caused
    changes as the addendum asks. The build was made from HEAD before the
    after runs finished, and reverted at once (`git status --short crates`
    printed nothing). Attribution ran on cores 0–11 while triage held
    12–23.
19. **Timing:** the three passes ran back to back without waiting to see
    pass 1. Pass 1's QF_SLIA ratio (0.901) was out of band, so the brief's
    pooling applies in any case. A swapped-order pass and a per-row min-of-3 pass were added as
    diagnostics.
20. **No new base run.** The base is slice 60b's runs (see *Runs*), as the
    plan specifies.

## Gates

From `target/slice61-gates.txt`, measured at `f9fa4f9`:

- `mise run ci`: green. nextest 1808 run / 1808 passed / 6 skipped
  (707.6 s).
- Oracle suite (`cargo nextest run -p shinri-solver --features oracle`):
  841 run / 841 passed / 2 skipped (1,460.8 s). The discovered count is
  non-zero. `joint_seed_oracle`'s last tally (Task 5): 47 `sat`, 40
  `unsat`, 113 `unknown`, 17 z3 timeouts.

## PR body material (R4: the controller opens the PR)

```
Spec: docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md
Plan: docs/superpowers/plans/2026-10-05-shinri-slice61-joint-concat-seeds.md
Report: docs/superpowers/research/2026-10-06-smtlib-2024-slice61-joint-concat-seeds-report.md

The free leaves of concat-subject memberships now get jointly chosen witness words at
model-build time (`joint_seed::joint_seeds_flagged`, merged over `memb_seeds`), so the gate
stops rejecting the composed concat. The gate also evaluates valued compound length
arithmetic structurally (R11a), which closes a pre-existing wrong `sat` on main (R10).

| # | criterion | result |
| 1 | 0 wrong | PASS: 0 wrong rows, 0 wrong answers in 828 triage runs |
| 2 | memb@not-needed -20% (>= 87) to correct | PASS: 432 -> 314; 108 (25.0%) now correct |
| 3 | no reproducible correct -> non-correct | FAIL (letter): 2 Norn ab rows; base sat had an invalid model, R11a gate rejects it; ruling R13: met in substance |
| 4 | timing within +-5% | FAIL (faster side): pass 1 QF_S 0.982, QF_SLIA 0.901; pooled 0.969 / 0.931; min-of-3 0.987; ruling R14: met in substance |
| 5 | ci + oracle | PASS: 1808/1808; oracle 841/841 |
| 6 | neutrality sample | PASS: 51 changes, all noise |

violated:memb@not-needed: 432 -> 314. String correct +126 (110 gains, all sat).
```

## Queued for the next slice

Ordered. Items 1–6 come from this run and its rulings. Items 7–9 are the
slice-60 queue items 5 and 6 and the candidate (c) note. Then the carried
lists follow verbatim.

**Re-ranks:**
- On the after run's counts, `violated:bool@not-needed` (598, slice-59
  items 2–3) and `violated:word-eq@rejected` (479) and
  `violated:not-word-eq@not-needed` (352) all outrank class 1's remainder
  (314). Class 1 stays first because the brief orders it first and because
  252 of its rows are one Norn shape, with a trace below. The owner may
  move the carried `bool` items ahead of it.
- Slice-60 item 4 (concat-subject emptiness) moves up to item 2, as the
  brief directs. R8's finding makes it doubly motivated.
- New items 3–6 (from rulings R9–R11a and Task 5) sit above the remaining
  slice-60 items 5–6 because items 3–5 are about gate and model soundness.
- Slice-60 items 2 and 3 are this slice and are closed. Item 3's 28
  `regex-035-*` rows are all `correct`; item 2's Norn remainder is item 1
  here.

1. **Class 1 remainder: 314 rows `violated:memb@not-needed`.** By family:
   Norn HammingDistance 252, Jiang `slog` 44, Norn StringReplace 11, Norn
   `ab` 2, z3str2 2 (`regex-050-*`), automatark 1, ChunkSplit 1,
   denghang 1. Trace of 10 seeded rows (`still.tsv`):
   - **7 of 10 (all HammingDistance): the group is skipped by
     `value_dictated`.** A leaf's class holds a string constant or a
     **non-minted** concat (R5 exempts only minted Rule-S1 concats). The
     next step is to trace which of the two it is. If it is an input concat
     (`var_8 = var_3 ++ var_4`-style equations), the joint search could
     flatten through it and take the concat's operands as the leaves.
   - **1 of 10 (`norn-benchmark-743`): the group formed but both passes
     found nothing.** It is not yet known whether the cause is a cap or a
     jointly empty input group (z3 not run).
   - **2 of 10 (Jiang `slog`): no eligible group.** All 44 `slog` rows are
     unchanged. Their membership subjects are not concats of leaves and
     constants (spec §4.2), so the shape needs its own trace.
   - **0 of 10**: solved, then rejected by the gate for another reason.
2. **Concat-subject memberships with a provably empty intersection stay
   `unknown`** (slice-60 item 4, verbatim below; now doubly motivated).
   Task 3 found that `norn-benchmark-531`'s SAT state carried a **jointly
   unsat** set of derivative membership atoms (z3), which the theory never
   refuted. That is why R8 restricts the joint search to input memberships.
   The same refutation, turned into a conflict, would make Norn's SAT
   states consistent and could turn some of the 314 into `unsat` (z3
   answered `unsat` on `norn-benchmark-617` in slice 60's class-1 trace).

   Slice-60 text: Example: `(str.++ x y) ∈ L40+ ∩ (bba)+` answers `unknown`
   on both base and after.
   - The slice-28 emptiness block groups memberships by the raw subject
     `TermId` and fires only when there are ≥ 2 of them.
   - The final review found that concat-subject hand cases stay `unknown` on
     both binaries. The oracle's `(str.++ x y)` scripts reach `unsat` only
     through length conflicts.
   - Needs a check of why the emptiness conflict does not fire on a shared
     concat subject: the key normalisation, or the shape never reaching the
     block.
3. **Length-consistent seeds for bare memberships (R10 follow-up; recovers
   criterion 3's 2 rows soundly).** `memb_seeds`' shortest-word fallback
   picks a word whose length disagrees with the arith model's
   `str.len`. Before R11a, the gate accepted the result when the length
   sat inside compound arithmetic: a wrong `sat` on the R10 script, and
   right-by-luck `sat`s on Norn `ab` `norn-benchmark-135` and `138`. Those
   two are now `unknown`. A fallback that searches at the model length
   first, or that re-solves arithmetic with the chosen lengths pinned,
   would get them back with valid models. Reproducers:
   `target/slice61-after/r10/lensum-bare.smt2` (z3 `unsat`) and
   `QF_SLIA/2015-Norn/ab/norn-benchmark-135.smt2` (z3 `sat`, `v = 2`).
4. **R9's strict gate blocks rows on unevaluable assertions (14 rows), and
   fires at model length 0.** On 14 Norn rows (StringReplace 13,
   HammingDistance 1) the joint seed now satisfies the memberships, but the
   strict gate rejects an **unevaluable** leaf assertion
   (`unevaluable:other:leaf@not-needed` 13,
   `unevaluable:not-other:leaf@not-needed` 1). The non-strict gate would
   skip those assertions. Two things to settle: what the unevaluable leaf
   is (likely a value the evaluator cannot read), and whether the strict
   flag can be scoped to the assertions that mention a re-lengthed leaf.
   The flag also fires when `class_len_in_model` is 0 because the model
   has no length for the leaf (Task 3 minor). No triaged gain was lost to
   it, but these 14 rows are where it would show.
5. **R11a residual: a compound arithmetic term the arith model never
   valued stays unevaluable** and passes the non-strict gate, as on main.
   With joint or shortest seeds changing lengths, such a term could hide a
   violated sum. Pinned as unevaluable by
   `model_reject::tests::unevaluable_compound_len_arith`. A fix evaluates
   it structurally whenever every operand evaluates. It changes that
   test's premise, so it needs its own measured slice.
6. **`get-value` prints `?` for a never-constrained String** (Task 5). For
   example, `x` declared and never used. It should print a value (`""`).
   Pre-existing. Task 5's oracle queries only mentioned leaves to work
   around it.
7. **Oracle coverage for decided-but-unverified rows** (slice-60 item 5,
   verbatim; slice 61 adds no new `unverified` row). 897 rows are newly
   decided while the z3 oracle times out at 20 s: 855 `sat` (853
   stringfuzz `generated`, 2 `transformed/amazon`) and 42 `unsat`. Of the
   42 `unsat`, 6 automatark rows stay unconfirmed after z3 `-T:120` and
   cvc5 `--tlimit=120000` (`instance06362`, `10317`, `10696`, `13032`,
   `15041`, `15868`). Options: enable the bench's `cvc5` oracle column
   (cvc5 confirmed 36 of the 42), and/or re-check `sat` witnesses with an
   independent evaluator. (Slice 60b's update: 885 decided-but-unverified,
   and 159 pre-existing unconfirmed `unsat` rows.) This run's 50
   `correct ↔ unverified` flips are all this oracle's 20 s timeout: 49
   stringfuzz `generated` rows and automatark `instance14507`.
8. **Witness search cost on newly decided stringfuzz `generated` rows**
   (slice-60 item 6, verbatim). Up to 2.7 s per row (`regex-big-00071-2`).
   Newly-`correct` rows take 11× longer than base's fast fence, although
   their median is 9 ms. Measure whether `search_word` at the model length
   dominates. A cheaper first try, such as the shortest word when the
   length is free, may help.
9. **Candidate (c) (slice-60 variant note):** recover the 10
   HammingDistance gains of slice 60's approach 1 without its 4 losses, by
   making Rule-E's disjunct order independent of partition granularity.
   Lower priority than items 1–3. This slice moved 75 HammingDistance rows
   to `correct` by a different route (joint seeds). None of the 10
   approach-1 rows is among them: all 10 are still `unknown:sat-budget`.
   Joint seeds act only after SAT, and these rows never reach it.

Deferred minors from this slice's reviews (not ranked):
- `joint_seed.rs` `key()` clones pending words per node: O(len) per step at
  long fixed lengths.
- The sweep's found/exhausted guard counts pass 1 only; pass 2 could
  degenerate unnoticed.
- No `StrSolver`-level unit test of the R8 filter in `model_with` (probes
  only).
- `joint_empty_not_sat` and `length_pin_sound` are `unknown` today, so
  their witness paths are unexercised tripwires.
- `verdict_with_witness_check` indexes `out[0]`/`out[1]` directly, with an
  unclear panic message on a parse error.
- The Task 5 generator doc comment says all three leaves are "queried".

Carried verbatim from the slice-60 report, which carried them in turn. In this text, "this slice" means the slice whose report is being quoted.

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

- Spec: `docs/superpowers/specs/2026-10-05-shinri-slice61-joint-concat-seeds-design.md`
- Plan: `docs/superpowers/plans/2026-10-05-shinri-slice61-joint-concat-seeds.md`
- Slice-60 report: `docs/superpowers/research/2026-10-05-smtlib-2024-slice60-head-classes-report.md`
- Evidence (not committed): `target/slice61-gates.txt`;
  `target/slice61-base/{commit.txt,md5.txt,tagcount.txt,trace.txt,probes.txt,probes/}`;
  `target/slice61-after/{md5.txt,commit.txt,started.txt,finished.txt,uptime-start.txt,uptime-finish.txt,join.txt,changed.tsv,tagmove.tsv,triage-in.tsv,triage.tsv,triage-disp.txt,triage-summary.txt,triage-uptime-before.txt,triage-uptime-after.txt,attr-in.txt,attribution.tsv,still-in.txt,still.tsv,nongain-trace.tsv,timing.py,timing.txt,timing-rerun2.txt,timing-rerun3.txt,timing-swapped.txt,timing-slia-rows.txt,timing-load.log,r10/}`;
  `bench/results/slice61{,-sample}/`, base `bench/results/slice60b{,-sample}/`
