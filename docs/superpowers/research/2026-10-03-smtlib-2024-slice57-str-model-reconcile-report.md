# SMT-LIB 2024 re-run — slice 57 (string model reconciliation for multi-concat classes) — shinri @ 57743db

## Headline

Slice 57 makes the string model builder rebuild a model whose default build
violates an input string equation (a class holding several concats, or a
cycle through a minted concat), and puts every adopted rebuild behind a
strict gate (every assertion must evaluate to `true`). It targets the
slice-53 regression in which `(= (str.len x) 3)` with `(str.prefixof "cd" x)`
and similar trivially satisfiable inputs answered
`unknown fence=str-model-rejected`. On the bench (QF_S, QF_SLIA, QF_LIA,
116,641 rows):

- **0 `wrong`**, 0 `* → wrong`, 0 wrong answers in 1,440 triage re-runs.
  Panic (57, all QF_LIA) and parse-error (195, all QF_SLIA) are identical
  in both runs.
- 445 of 116,641 rows differ in recorded verdict. Triage re-ran 240 of them
  3× per binary (1,440 runs). **One change is attributable to the slice**:
  `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-multiply-reverse-fuzz.smt2`,
  `unknown:str-model-rejected → correct` (base `unknown` 3/3, after `sat`
  3/3). On the other 239 rows both binaries gave the same answer in all six
  runs. Those changes are bench-time noise: shinri resource-limit flips,
  and z3 oracle timeouts that turned rows into `unverified`.
- **`unknown:str-model-rejected`, raw: QF_S 966 → 967, QF_SLIA 3,122 →
  3,122** (combined 4,088 → 4,089, **+1**). Each logic has one
  `timeout → str-model-rejected` row (`automatark-lu/instance02984`,
  `denghang/instance52452`), and the base binary also gives
  `unknown fence=str-model-rejected` on both of them (3/3 in triage, plus a
  `--stats` check). Counting those two rows as `str-model-rejected` in the
  base too, the count falls by 1 (QF_SLIA 3,123 → 3,122, QF_S 967 → 967).
  **Spec criterion 3 ("decreases") fails on raw counts and passes only on
  credited counts.** That needs a ruling (see *Success criteria*).
- Net `correct` per logic, raw: QF_S +5, QF_SLIA +115, QF_LIA +84. Credited
  to the slice: QF_S 0, QF_SLIA +1, QF_LIA 0. No reproducible `correct → *`
  loss: on all 12 `correct → *` rows (all QF_LIA) both binaries gave the
  correct `sat` 3/3.
- The slice's own targets pass: all 16 `slice57_probes` pass at `57743db`
  (5 failed before the fix), including the three §1.1 shapes and
  `multiply-reverse-fuzz`. In the oracle family the count of scripts where
  shinri said `unknown` and z3 said `sat` fell from 48 to 35, with
  0 disagreements and 61 witnesses checked.
- Why so few bench rows move: the 4,088 `str-model-rejected` rows in the
  corpus are almost all other mechanisms. The rebuild fixes the
  multi-concat model-builder failure, and only `multiply-reverse-fuzz` of
  the slice-53 stringfuzz trio has that shape and is `sat`. The other two
  (`translate-rotate-fuzz`, `translate-graft-translate`) are `unsat` and
  need the engine-side work (queue item 1).
- Timing is neutral. In a serial, interleaved run of 300 sampled
  both-`correct` rows the binaries take the same time: summed 23.10 s vs
  23.06 s (QF_LIA), 0.99 s vs 0.98 s (QF_S), 1.12 s vs 1.12 s (QF_SLIA).
  The bench medians differ (base 19/29 ms vs after 5/5 ms on QF_S/QF_SLIA)
  only because the base run was slower throughout. A tiny QF_S row takes
  2 ms on both binaries in isolation.

## Commands

Task 0 (base binary and base run; controller):

```bash
git diff --stat 46d5fd9 HEAD -- crates          # empty
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice57-base && cp target/release/shinri target/slice57-base/shinri
cp target/release/shinri-bench target/slice57-base/shinri-bench
md5sum target/slice57-base/shinri | tee target/slice57-base/md5.txt
echo 46d5fd9 > target/slice57-base/commit.txt
date -u +%FT%TZ > target/slice57-base/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice57-base/shinri-bench run \
  --logics QF_S,QF_SLIA,QF_LIA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice57-base/shinri --run-id slice57-base \
  > target/slice57-base/run.log 2>&1; date -u +%FT%TZ > target/slice57-base/finished.txt' \
  > /dev/null 2>&1 &
```

Tasks 1 and 3 (probes and oracle family, before and after):

```bash
cargo nextest run -p shinri-solver -E 'binary(slice57_probes)'
cargo nextest run -p shinri-solver --features oracle --no-capture \
  -E 'test(differential_qfs_model_reconcile)'
```

Task 4 (gates):

```bash
taskset -c 0-11 mise run ci 2>&1 | tee target/slice57-ci.log | tail -30
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 \
  | tee target/slice57-oracle-suite.log | tail -15
```

Task 5 (after run; the bench driver is the frozen copy
`target/slice57-after/shinri-bench`, the same build as `target/release`):

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice57-after && cp target/release/shinri target/slice57-after/shinri
md5sum target/slice57-after/shinri | tee target/slice57-after/md5.txt
git rev-parse --short HEAD | tee target/slice57-after/commit.txt
date -u +%FT%TZ > target/slice57-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice57-after/shinri-bench run \
  --logics QF_S,QF_SLIA,QF_LIA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice57-after/shinri --run-id slice57 \
  > target/slice57-after/run.log 2>&1; date -u +%FT%TZ > target/slice57-after/finished.txt' \
  > /dev/null 2>&1 &
BENCH_RUN_ID=slice57-base mise run bench-report
BENCH_RUN_ID=slice57 mise run bench-report
```

Verdict join: the plan's Step 3 script (not committed). It joins the two
`results.jsonl` by `path`, skipping the fixture header line. The key sets
are identical (116,641 each). It counts `(logic, base, after)` for rows that
differ and writes `target/slice57-after/changed.tsv`.

Unverified check, on cores 0–11 while triage ran on 12–23:

```bash
awk -F'\t' '$4=="unverified"{print $1}' target/slice57-after/changed.tsv > target/slice57-after/unverified.txt
while read -r p; do
  printf '%s\t%s\n' "$p" "$(taskset -c 0-11 timeout 60 z3 bench/corpus/$p 2>/dev/null | head -1)"
done < target/slice57-after/unverified.txt | tee target/slice57-after/unverified-z3.tsv
```

Triage: per row, 3 rounds, each round runs base then after:
`taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 <bin> bench/corpus/<path>`,
keeping the first `sat|unsat|unknown` line (or `none`) and the elapsed ms.
Six paths ran in parallel (`xargs -P 6`), matching the bench's `--jobs 6`.
Nothing else was running. Raw output: `target/slice57-after/triage.tsv`
(1,440 lines, 2026-10-03T17:41:33Z–18:06:20Z).

Serial timing sample: 100 random rows per logic (seed 57), each
`correct` in both runs with after-run wall < 5 s. Each binary ran once per
row, interleaved, on cores 12–23. Output: `target/slice57-after/timing-serial.tsv`.

## Runs

| run | solver | md5 | started | finished | rows |
| --- | --- | --- | --- | --- | ---: |
| `bench/results/slice57-base/` (base) | `target/slice57-base/shinri` (built from `46d5fd9` sources; checkout `6367774`, docs-only diff) | `7c73abb538a48c90b839ac466cf4a3db` | 2026-10-03T06:56:46Z | 2026-10-03T12:41:24Z | 116,641 |
| `bench/results/slice57/` (after) | `target/slice57-after/shinri` (built at `57743db`) | `0a42b4b0b6fb74651387535c869c51b2` | 2026-10-03T12:41:51Z | 2026-10-03T17:39:36Z | 116,641 |

Both runs used `--timeout 20 --mem-mb 3072 --jobs 6` on cores 12–23 over
QF_S (18,940), QF_SLIA (84,395) and QF_LIA (13,306). Each `results.jsonl`
has 116,642 lines: 116,641 rows plus the fixture line. The base binary's md5
equals the slice-56 after binary's (`7c73abb5…`), so the base is the
slice-56 head. Runs are git-ignored.

## Success criteria (spec §8)

| # | Criterion | Result | Evidence |
| --- | --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage | PASS | 0 `wrong` in either run; 0 `* → wrong`. 1,440 triage runs: every answer from the after binary matches the row's status or z3 answer. The 5 changed `unverified` rows: z3 (60 s) `sat` for the 3 QF_LIA rows (shinri `sat`). On the 2 QF_SLIA denghang rows (shinri `unsat`, z3 no answer in 60 s) cvc5 1.4.1 gives `unsat`. **z3 `unsat` count: 0** |
| 2 | the three §1.1 shapes and `multiply-reverse-fuzz` answer `sat` | PASS | `target/slice57-probes-before.log`: 15 run, 10 pass, 5 fail (`p1_len_eq_prefix_cd`, `p2_len_eq_prefix_backslashes`, `p3_len_eq_suffix_c`, `p4_stringfuzz_multiply_reverse`, `rf2_…`). `target/slice57-probes-after.log` and a re-run at `57743db` (`target/slice57-probes-head.log`): 16 run, 16 pass. Bench: `multiply-reverse-fuzz` is `correct` (`sat`), 3/3 in triage |
| 3 | `unknown:str-model-rejected` decreases in QF_S + QF_SLIA; every `→ correct` group triaged | **FAIL raw / PASS credited — needs a ruling** | Raw: QF_S 966 → 967, QF_SLIA 3,122 → 3,122 (combined +1). The +1 per logic comes from two `timeout → str-model-rejected` rows. On both, the base binary gives the same `unknown fence=str-model-rejected` 3/3: the base run timed out on them under load (base wall 20.1 s and 20.5 s, isolated runs 18.3–18.7 s and 4.6–5.0 s). Credited: QF_S 967 → 967, QF_SLIA 3,123 → 3,122 (−1, `multiply-reverse-fuzz`). Every `→ correct` group was triaged in full (215 rows) |
| 4 | every `correct → *` row triaged; net `correct` ≥ 0 per logic | PASS | 12 `correct → *` rows (QF_LIA: 9 `→ timeout`, 3 `→ unverified`) re-run 3× per binary: both give the correct `sat` 3/3, so none is reproducible. Net correct, raw: QF_S +5, QF_SLIA +115, QF_LIA +84. Credited: 0 / +1 / 0 |
| 5 | §7.4 before/after, 0 disagreements, 0 witness failures; discovered non-zero; `mise run ci` green | PASS | Before (`46d5fd9` engine, Task 1): `300 iters — 48 sat / 179 unsat / 73 shinri-unknown (48 with z3 sat) / 0 z3-unknown; 48 witnesses; 0 disagreements`. After (re-run at `57743db`, 1 test discovered, 1 passed, 8.9 s): `61 sat / 179 unsat / 60 shinri-unknown (35 with z3 sat) / 0 z3-unknown; 61 witnesses; 0 disagreements`. `mise run ci` at `57743db`: 1,719 run, 1,719 passed (11 slow), 7 skipped |
| 6 | median/p90 ms per logic against `slice57-base` | reported (neutral) | See *Timing* |

## Per-logic matrix

After run (`slice57`):

| logic | total | correct | wrong | parse-error | panic | oom | timeout | unknown | unverified | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_LIA | 13306 | 4799 | 0 | 0 | 57 | 577 | 3106 | 4764 | 3 | 66 | 2869 |
| QF_S | 18940 | 16061 | 0 | 0 | 0 | 0 | 6 | 2775 | 98 | 5 | 13 |
| QF_SLIA | 84395 | 24901 | 0 | 195 | 0 | 0 | 44 | 57993 | 1262 | 5 | 15 |
| all | 116641 | 45761 | 0 | 195 | 57 | 577 | 3156 | 65532 | 1363 | 6 | 37 |

Base run (`slice57-base`):

| logic | total | correct | wrong | parse-error | panic | oom | timeout | unknown | unverified | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_LIA | 13306 | 4715 | 0 | 0 | 57 | 387 | 3382 | 4764 | 1 | 88 | 2068 |
| QF_S | 18940 | 16056 | 0 | 0 | 0 | 0 | 8 | 2774 | 102 | 19 | 49 |
| QF_SLIA | 84395 | 24786 | 0 | 195 | 0 | 0 | 56 | 57985 | 1373 | 29 | 79 |
| all | 116641 | 45557 | 0 | 195 | 57 | 387 | 3446 | 65523 | 1476 | 25 | 95 |

(status-suspect and malformed are 0 everywhere. The median/p90 columns
are the bench report's, over all rows.)

`unknown:str-model-rejected`, base → after:

| logic | base | after | raw Δ | credited Δ |
| --- | ---: | ---: | ---: | ---: |
| QF_S | 966 | 967 | +1 | 0 |
| QF_SLIA | 3122 | 3122 | 0 | −1 |
| QF_LIA | 0 | 0 | 0 | 0 |

## Transition matrices

Changed rows (logic, base → after, count). Total 445.

| logic | base → after | rows | triage disposition |
| --- | --- | ---: | --- |
| QF_LIA | correct → timeout | 9 | noise (both `sat` 3/3) |
| QF_LIA | correct → unverified | 3 | noise (both `sat` 3/3; after-run z3 timed out, z3 60 s `sat`) |
| QF_LIA | timeout → correct | 96 | noise (both binaries give the correct answer 3/3) |
| QF_LIA | oom → timeout | 7 | not triaged (no answer either run) |
| QF_LIA | timeout → oom | 197 | not triaged (no answer either run) |
| QF_LIA | unverified → timeout | 1 | not triaged |
| QF_S | timeout → correct | 1 | noise (both `sat` 3/3) |
| QF_S | timeout → unknown:str-model-rejected | 1 | noise (both `unknown`, fence `str-model-rejected`, 3/3) |
| QF_S | unverified → correct | 4 | noise (same answer 3/3 on both; z3 answered in the after run only) |
| QF_SLIA | timeout → correct | 1 | noise (both `unsat` 3/3) |
| QF_SLIA | timeout → unknown:sat-budget | 8 | noise (both `unknown` 3/3) |
| QF_SLIA | timeout → unknown:str-model-rejected | 1 | noise (both `unknown`, fence `str-model-rejected`, 3/3) |
| QF_SLIA | timeout → unverified | 2 | noise (both `unsat` 3/3; cvc5 `unsat`) |
| QF_SLIA | unknown:str-model-rejected → correct | 1 | **attributable** (base `unknown` 3/3, after `sat` 3/3) |
| QF_SLIA | unverified → correct | 113 | noise (same answer 3/3 on both: 52 `sat`, 61 `unsat`; z3 answered in the after run only) |

Closure, per logic (after − base = sum of transitions):

- QF_LIA: correct −9 −3 +96 = **+84** (4,715 → 4,799); timeout +9 +7 −96
  −197 +1 = −276 (3,382 → 3,106); oom −7 +197 = +190 (387 → 577);
  unverified +3 −1 = +2 (1 → 3). 313 rows.
- QF_S: correct +1 +4 = **+5** (16,056 → 16,061); timeout −1 −1 = −2
  (8 → 6); unknown +1 (2,774 → 2,775); unverified −4 (102 → 98). 6 rows.
- QF_SLIA: correct +1 +1 +113 = **+115** (24,786 → 24,901); timeout −1 −8
  −1 −2 = −12 (56 → 44); unknown +8 +1 −1 = +8 (57,985 → 57,993);
  unverified +2 −113 = −111 (1,373 → 1,262). 126 rows.

No `sat ↔ unsat` change in recorded answers. Every row whose verdict
changed between two decided verdicts (`correct ↔ unverified`) kept the same
shinri answer, and only the z3 oracle's answer changed.

## Triage

Method (slice-53/56): each changed row that starts or ends in `correct`
(228 rows) was re-run 3× per binary, interleaved, under the bench's limits.
No row ends in `wrong`. No group exceeds 200 rows (the largest is 113), so
there is no sampling. Twelve more rows were also triaged: the QF_S/QF_SLIA
rows outside that rule (8 `→ sat-budget`, 2 `→ str-model-rejected`,
2 `→ unverified`). That makes 240 rows and 1,440 runs. A row is
*attributable* when base and after each reproduce their bench verdict 3/3,
and *noise* otherwise.

- **Attributable: 1 row.**
  `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-multiply-reverse-fuzz.smt2`:
  base `unknown` 3/3 (7–8 ms), after `sat` 3/3 (7–8 ms). This is the
  spec's §1.1 target row.
- **Noise: 239 rows.** On every one, base and after gave the same answer in
  all six runs:
  - 12 `correct → *` (QF_LIA cmodelsdiff `randomNontight`/`stillLive`,
    ezsmt): `sat` on both, 3.0–19.5 s in isolation, with near-identical
    per-row times on the two binaries. The after run timed out on 9 of them
    under bench load. On the other 3 the after-run z3 oracle timed out,
    which made them `unverified`.
  - 96 QF_LIA `timeout → correct` (`20220307-SMPT`): both binaries give the
    correct answer (48 `unsat`, 48 `sat`) 3/3. The base run timed out on
    them.
  - 117 `unverified → correct` (113 QF_SLIA: stringfuzz-lu `generated`
    41, denghang and others; 4 QF_S automatark): shinri's answer is
    unchanged. The base run's z3 oracle timed out at 20 s, and the after
    run's answered.
  - 2 `timeout → correct`, 8 `→ sat-budget`, 2 `→ str-model-rejected`,
    2 `→ unverified`: same answer on both binaries 3/3.
- **Wrong answers in triage: 0.** Every after-binary answer on a row with a
  status or a z3/cvc5 answer matches it.

Unverified-z3 check (`target/slice57-after/unverified-z3.tsv`): 5 changed
rows end in `unverified`. The 3 QF_LIA `stillLive` rows: shinri `sat`, z3
60 s `sat`. The 2 QF_SLIA denghang rows (`instance51542`, `instance57489`):
shinri **`unsat`**, not `sat`, and z3 gave no answer within 60 s. cvc5
1.4.1 (300 s) gives `unsat` for both, and the base binary also answers
`unsat` 3/3. **z3 `unsat` count: 0.**

Base-run load. The base run was slower throughout its 5 h 45 min. Its
median `wall_ms` on `correct` rows was above the after run's in every
twentieth of the row order: 1.3–1.4× on the QF_LIA twentieths and 2–8× on
the string ones (for example 19 vs 4 ms, 30 vs 5 ms). So the slowdown was
not confined to the hours when Tasks 1–4 used cores 0–11. The base run's z3
oracle also timed out more often, which accounts for the 117
`unverified → correct` rows. In isolation the two binaries run at the same
speed (see *Timing*). This report does not identify the cause of the
slowdown beyond bench-time environment.

## Timing

Over rows `correct` in both runs, from `results.jsonl` (median = index
`n/2`, p90 = index `ceil(0.9n) − 1`, as in the bench report):

| logic | rows | base median ms | base p90 ms | after median ms | after p90 ms | base Σ s | after Σ s |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_S | 16056 | 19 | 49 | 5 | 13 | 512 | 166 |
| QF_SLIA | 24786 | 29 | 79 | 5 | 15 | 1212 | 343 |
| QF_LIA | 4703 | 86 | 1986 | 63 | 1618 | 5532 | 3340 |

The bench-time gap is the base run's environment (*Triage*, base-run load),
not the binaries. In the serial, interleaved sample (100 rows per logic,
cores 12–23, nothing else running):

| logic | base median ms | base p90 ms | after median ms | after p90 ms | base Σ ms | after Σ ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_S | 4 | 8 | 4 | 9 | 988 | 983 |
| QF_SLIA | 4 | 17 | 4 | 16 | 1123 | 1123 |
| QF_LIA | 45 | 622 | 49 | 635 | 23100 | 23063 |

Neutral, as spec §8 expected: the rebuild runs only when the default model
is rejected. The 240 triage rows agree. Per-row times on the two binaries
are within run-to-run variation (for example `n40-sat-b8` 11.7–12.1 s vs
11.7–12.0 s).

## What changed versus the spec

1. **Strict-gate pin swapped (Task 3, ruling).** Spec §7.3 named
   `(str.< x "zzz")` as the unevaluable constraint. Lowering makes `str.<`
   against a constant gate-evaluable, so the rebuilt model is confirmed
   and the script answers `sat` (z3 `sat`, model `"cdH"`). The pin
   `strict_gate_keeps_unevaluable_unknown` now uses
   `(<= (- (str.len x) (str.len y)) 1)` (compound arithmetic the gate cannot
   evaluate). It answers `unknown` with strict on and `sat` with strict
   forced off, z3 `sat`. The original `str.<` script is kept as the positive
   probe `strict_gate_confirms_lowered_str_lt` (`sat`). At `57743db` the pin
   also asserts the fence `str-model-rejected`.
2. **rf2 probe swapped (final review).**
   `rf2_strict_flag_does_not_leak_across_checks` used a `str.<`-against-a-constant second query.
   That query is gate-evaluable, so the probe could not fail. Its second
   query now uses the gate-unevaluable compound-arithmetic constraint, so a
   leaked strict flag would turn it into `unknown` (`57743db`).
3. **Concat/operand consistency fix (Task 3 review, `e0bba20`).** As first
   implemented, `slice_word` returned the anchor word instead of the joined
   pieces, and `eval_word` and the gate trusted a concat's stored value. An
   adopted rebuild could therefore disagree with its operands (reproduced at
   unit level). Fix: `slice_word` joins the pieces, `eval_word` composes
   concats, and a `concats_consistent` guard runs before adoption.
4. **Candidate-trial budget and undo log (final review, `9514852`).** The
   spec says nothing about rebuild cost. A memo clone per candidate made a
   late-failing nested rebuild O(b^d). The rebuild now has a trial budget of
   4 × |known| + 64. When the budget runs out the rebuild is abandoned and
   the default model is kept (flag unset), the same sound fallback as a
   failed rebuild. An undo log replaces the memo clone.
5. **Two existing tests re-pinned (Task 4, rulings, `5137977`).**
   - `script_e2e::str_input_var_concat_length_decides`: the `len(s)=3`
     control now answers `sat` (z3 `sat`). It is re-pinned to `sat` with the
     witness checked, and the not-`unsat` assertion is kept. The old pin
     recorded the incompleteness this slice fixes.
   - `slice52_probes::bool_proxy`: the slice-52 KNOWN WRONG `sat` (z3
     `unsat`) now answers a sound `unknown`. The rebuild is adopted, and the
     strict gate cannot evaluate Bool `p`. It is re-pinned to `unknown`,
     keeping the flip-to-`unsat` note.

   These are the only existing-test changes.
6. **Final whole-branch review ran before Task 5 (ruling).** It covered
   `6367774..5137977` and ran while the base bench ran. Its fixes (items 2
   and 4) were re-reviewed: clean at `57743db`. Task 5 adds only docs.
7. **Oracle generator unchanged.** Spec §7.4 allowed strengthening the
   generator if the before count was 0. It was 48, so the generator was not
   changed (after: 35).
8. **No `known` reordering** was needed in Task 3 Step 3.
9. **Bench mechanics.** Both runs used frozen copies of `shinri-bench`
   (`target/slice57-{base,after}/shinri-bench`). The base fixture header
   records the checkout `6367774` (spec and plan commits on `46d5fd9`,
   docs-only crates diff, verified empty). Triage ran 6 paths in parallel,
   as in slice 56, and recorded elapsed ms. The brief's triage command line
   omits `--stats`, so the two `→ str-model-rejected` rows' fences were
   checked with a separate `--stats` run on both binaries.
10. **Changed `unverified` rows are `unsat`, not `sat`.** Plan Step 4
    assumes new `unverified` rows are shinri `sat`. Two of the five are
    shinri `unsat` (denghang, `timeout → unverified`). z3 gives no answer
    within 60 s, so cvc5 (`unsat`) was used as the cross-check.
11. **Criterion 3 direction.** It is met only on credited counts (see
    *Success criteria*). The raw +1 is two load-driven timeouts in the base
    run that become the same `str-model-rejected` the base binary produces
    in isolation.

## Gates

- `mise run ci` at `57743db`: green. 1,719 tests run, 1,719 passed
  (11 slow), 7 skipped (`target/slice57-ci-final2.log`). It includes lint
  (fmt check, clippy `-D warnings`), deny and secrets.
- Oracle suite (`--features oracle`, Task 4 at `e0bba20`): 797 discovered,
  795 passed, 2 failed, 3 skipped. The two failures were the non-oracle
  pins `script_e2e::str_input_var_concat_length_decides` and
  `slice52_probes::bool_proxy`, re-pinned in `5137977` and green in the
  final ci.
- Oracle family at `57743db`:
  `-E 'test(differential_qfs_model_reconcile)'`: 1 discovered, 1 passed
  (non-zero), `61 sat / 179 unsat / 60 shinri-unknown (35 with z3 sat) / 0 z3-unknown; 61 witnesses; 0 disagreements`.
- `slice57_probes` at `57743db`: 16 discovered, 16 passed.
- Task 4 before totals (`target/slice57-before.txt`): ci fail-fast stopped
  on `script_e2e`. `--no-fail-fast`: 1,717 run, 1,715 passed, 2 failed (the
  two re-pinned tests), 7 skipped. The slice-56 oracle gate (filtered):
  22 of 22 passed.

## Queued for the next slice

Ordered. Items 1–3 are spec §9's. They split the engine part of slice-56
queue item 2: slice 57 did the model-side half, and §9 items 1–2 carry the
engine-side reconciliation and the bare-E/`Not(Eq)` work that waits on it.
The other items keep the slice-56 report's numbering and wording from
item 3 on.

1. **Engine-side reconciliation (approach 2).** Partial constant-head
   strip in `resolve_inner` (`wordeq.rs:1056` returns `Done` for a
   constant-prefix residual), a cited deep normal form on the
   conflict/split path, and sound length links for minted equations.
   Reproducers: `translate-rotate-fuzz`, `translate-graft-translate`
   (`unsat`, pinned `unknown` by `slice57_probes::k1`/`k2`), and the §1.1
   shapes reached without the model-side fix.
2. **Bare-E and `Not(Eq)` arm removal**, after (1). The acceptance test is
   the R6 probes (`slice33_probes::probe_c_len_zero_var`,
   `script_e2e::user_pfx_name_declared_before_any_mint_still_works`).
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
6. **str-model-rejected population.** 4,089 `str-model-rejected` rows
   remain (QF_S 967, QF_SLIA 3,122), and the rebuild moved only one. Their
   causes are not this slice's multi-concat shape. Classify them (for
   example by the first violated assertion) before targeting them.

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

- Spec: `docs/superpowers/specs/2026-10-03-shinri-slice57-str-model-reconcile-design.md`
  (§8 criteria, §11 measured outcomes).
- Plan: `docs/superpowers/plans/2026-10-03-shinri-slice57-str-model-reconcile.md`.
- Slice-56 report: `docs/superpowers/research/2026-10-03-smtlib-2024-slice56-uf-bool-const-report.md`.
- Commits: `f6366b6`, `6367774` (spec, plan), `756c6cb` (probes, oracle
  family), `bfe7a88` (strict flag and gate), `c47d50c`, `501012d`
  (reconciliation), `e0bba20` (concat/operand consistency), `5137977`
  (re-pins), `9514852`, `57743db` (trial budget, probe fixes).
- Runs (git-ignored): `bench/results/slice57-base/` (base),
  `bench/results/slice57/` (after). Triage and timing evidence:
  `target/slice57-after/{changed.tsv,triage.tsv,unverified-z3.tsv,timing-serial.tsv}`.
