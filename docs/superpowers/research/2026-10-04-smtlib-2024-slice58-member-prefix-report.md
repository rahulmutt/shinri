# SMT-LIB 2024 re-run — slice 58 (membership Rule G over class concat members) — shinri @ c3f6e48

## Headline

Slice 58 extends the string engine's membership Rule G (`memb_check`,
`crates/shinri-str/src/memb.rs`) with G′: when a regex-membership atom's
subject class holds a concat member, G′ reads that member's cited deep normal
form and takes Brzozowski derivatives of the regex over the constant prefix.
An empty derivative is a fully cited conflict. It targets the two stringfuzz
`unsat` rows slice 57 left pinned (`translate-rotate-fuzz`,
`translate-graft-translate`). On the bench (QF_S + QF_SLIA, 103,335 rows):

- **0 `wrong`** in either run, 0 `* → wrong`, 0 wrong answers in 306 triage
  runs. Parse-error (195, all QF_SLIA) is identical in both runs.
- 60 of 103,335 rows differ in recorded verdict (QF_S 15, QF_SLIA 45).
  Triage re-ran all 39 rows that end in `correct` (none starts there), plus the
  12 rows that change between `sat-budget` and `str-model-rejected` (3× per
  binary, interleaved). **8 rows are attributable to G′** (`unknown:str-model-rejected
  → correct`, all QF_SLIA stringfuzz `transformed/z3str2/regex-050-*`): the
  base binary answers `unknown fence=str-model-rejected` 3/3 and the after
  binary answers `unsat` 3/3, with z3 `unsat` for each as bench oracle. These
  include both slice-57 reproducers. The other 31 `→ correct` rows are z3
  oracle timeouts in the base run (`unverified`); both binaries give the same
  answer as before 3/3, so they are not the slice's credit.
- **`unknown:str-model-rejected`, raw: QF_S 966 → 970 (+4), QF_SLIA 3,122 →
  3,114 (−8); combined 4,088 → 4,084 (−4).** No row is credited (the slice-57
  rule credits a row the base also fences in triage; here the 8 QF_S rows
  that move `sat-budget → str-model-rejected` are `sat-budget` in the base 3/3
  in isolation). Spec criterion 3 is stated for the combined count: PASS.
  Per logic, QF_S rises by 4 (see *What changed versus the spec*).
- Net `correct`: QF_S +3, QF_SLIA +36 (+39). All 39 rows are enumerated in
  *Triage*. No `correct → *` rows at all.
- The slice's own targets pass: 11/11 `slice58_probes` at `c3f6e48` (4 failed
  before; five guards only forbid `unsat`, see below). In the oracle family
  `differential_qfs_member_prefix` the count of scripts where shinri said
  `unknown` and z3 said `unsat` fell from 69 to 47, with 0 disagreements.
- Timing is neutral: in a serial, interleaved run of 150 sampled both-`correct`
  rows per logic, summed wall 1.07 s vs 1.04 s (QF_S, ratio 0.974) and 1.59 s
  vs 1.62 s (QF_SLIA, ratio 1.017). The bench medians differ (QF_S 14 → 8 ms,
  QF_SLIA 16 → 5 ms) only because the base run was slower throughout.

## Commands

Task 0 (controller; base binary and base run):

```bash
# base binary built from the branch point (engine f515c00) into target/slice58-base/shinri
taskset -c 12-23 target/slice58-base/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice58-base/shinri --run-id slice58-base   # detached with setsid nohup
```

Task 1 (probes and oracle family before):

```bash
taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice58_probes)' --no-fail-fast 2>&1 | tee target/slice58-probes-before.log
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle --no-capture -E 'test(differential_qfs_member_prefix)' 2>&1 | tee target/slice58-oracle-before.log
```

Task 2/3 (after, gates):

```bash
taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice58_probes)' 2>&1 | tee target/slice58-probes-after.log
taskset -c 0-11 cargo nextest run -p shinri-str
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle --no-capture -E 'test(differential_qfs_member_prefix)' 2>&1 | tee target/slice58-oracle-after.log
taskset -c 0-11 mise run ci 2>&1 | tee target/slice58-ci.log
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 | tee target/slice58-oracle-suite.log
```

Task 4 (after run, reports, join, triage, timing):

```bash
cargo build --release -p shinri-cli -p shinri-bench
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_S,QF_SLIA --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice58-after/shinri --run-id slice58 \
  > target/slice58-after/run.log 2>&1; date -u +%FT%TZ > target/slice58-after/finished.txt' > /dev/null 2>&1 &
BENCH_RUN_ID=slice58-base mise run bench-report
BENCH_RUN_ID=slice58 mise run bench-report
# join script: python3 over both results.jsonl (output target/slice58-after/join.txt, changed.tsv)
# triage (3 runs x 2 binaries, interleaved), per changed row:
taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats bench/corpus/$p
# timing: target/slice58-after/timing.py (taskset -c 12, 150 seeded rows per logic, random.Random(58))
```

## Runs

| run | solver | md5 | started | finished | rows |
| --- | --- | --- | --- | --- | ---: |
| `bench/results/slice58-base/` (base) | `target/slice58-base/shinri` (engine `f515c00`) | `0a42b4b0b6fb74651387535c869c51b2` | 2026-10-03T21:20:12Z | 2026-10-03T23:04:37Z | 103,335 |
| `bench/results/slice58/` (after) | `target/slice58-after/shinri` (built at `c3f6e48`) | `0c0f16e8fdf3e1c7cb303d8d9c0cf0b0` | 2026-10-03T23:05:31Z | 2026-10-04T00:33:30Z | 103,335 |

Both runs used `--timeout 20 --mem-mb 3072 --jobs 6` on cores 12–23 over
QF_S (18,940) and QF_SLIA (84,395). Each `results.jsonl` has 103,336 lines:
103,335 rows plus the fixture line. The row sets are identical. Runs are
git-ignored.

## Success criteria (spec §8)

| # | criterion | result | evidence |
| --- | --- | --- | --- |
| 1 | 0 `* → wrong`; 0 wrong answers in triage | **PASS** | 0 `wrong` rows in either run; 0 `* → wrong`; 0 wrong answers in 306 triage runs. No changed row ends `unverified`, so the z3 cross-check (§Triage) has 0 rows and 0 disagreements |
| 2 | `translate-rotate-fuzz`, `translate-graft-translate` answer `unsat` | **PASS** | both `unknown:str-model-rejected → correct`; triage: base `unknown` 3/3, after `unsat` 3/3 |
| 3 | credited `str-model-rejected` (QF_S + QF_SLIA) does not increase | **PASS (combined)** | raw = credited: QF_S 966 → 970 (+4), QF_SLIA 3,122 → 3,114 (−8), combined 4,088 → 4,084 (−4). The 4 `str-model-rejected → sat-budget` rows are fenced by the base 3/3, so nothing needs crediting in the base's favour; no after row gets credit either (the 8 QF_S `sat-budget → str-model-rejected` rows give `sat-budget` in the base 3/3). QF_S alone rises by 4, see *What changed versus the spec* |
| 4 | no reproducible `correct → *` loss | **PASS** | 0 `correct → *` rows (net `correct`: QF_S +3, QF_SLIA +36) |
| 5 | serial timing within ±5% | **PASS** | QF_S 0.974 (1.07 s vs 1.04 s), QF_SLIA 1.017 (1.59 s vs 1.62 s), 150 rows each |
| 6 | `ci` green; oracle suite non-zero and passing; §7.4 count strictly falls | **PASS** | `mise run ci` exit 0, nextest 1735 run / 1735 passed / 6 skipped; oracle suite (`--features oracle`) 808 run / 808 passed / 2 skipped; §7.4 count 69 → 47 with 0 disagreements |

Probes (`target/slice58-probes-before.log` / `-after.log`): before, at HEAD
`e784454` (engine `f515c00`), m1, m2, m3, rf1 FAIL and the other seven pass;
`m4` already passes at HEAD and stays as a regression guard. After
(`c3f6e48`): 11/11 pass.

Oracle family `differential_qfs_member_prefix` (`target/slice58-oracle-before.log`
/ `-after.log`):

- before: `300 iters — 73 sat / 72 unsat / 155 shinri-unknown (69 with z3 unsat) / 0 z3-unknown; 73 witnesses; 0 disagreements`
- after: `300 iters — 71 sat / 94 unsat / 135 shinri-unknown (47 with z3 unsat) / 0 z3-unknown; 71 witnesses; 0 disagreements`

Note: `sat` falls 73 → 71. Two instances went `sat → unknown` (decisiveness
only; shinri-unknown with z3 `sat` rose 86 → 88; 0 disagreements). The
family takes about 669 s; it runs only in the nightly-only `oracle` CI job
(ruling in the ledger, see below).

## Per-logic matrix

Verdict counts (rows):

| verdict | QF_S base | QF_S after | QF_SLIA base | QF_SLIA after |
| --- | ---: | ---: | ---: | ---: |
| correct | 16,057 | 16,060 | 24,873 | 24,909 |
| parse-error | 0 | 0 | 195 | 195 |
| timeout | 7 | 7 | 54 | 45 |
| unknown:reglan-decl | 0 | 0 | 3,287 | 3,287 |
| unknown:sat-budget | 1,385 | 1,381 | 4,239 | 4,248 |
| unknown:str-indexof-replace | 80 | 80 | 26,283 | 26,283 |
| unknown:str-int-conv | 0 | 0 | 1,616 | 1,616 |
| unknown:str-model-rejected | 966 | 970 | 3,122 | 3,114 |
| unknown:str-predicate-polarity | 0 | 0 | 16,016 | 16,016 |
| unknown:str-regex | 343 | 343 | 26 | 26 |
| unknown:str-substr-at | 0 | 0 | 3,359 | 3,359 |
| unknown:theory-refused | 0 | 0 | 35 | 35 |
| unverified | 102 | 99 | 1,290 | 1,262 |
| wrong | 0 | 0 | 0 | 0 |

`unknown:str-model-rejected`, raw and credited:

| logic | base | after | raw Δ | credited Δ |
| --- | ---: | ---: | ---: | ---: |
| QF_S | 966 | 970 | +4 | +4 |
| QF_SLIA | 3,122 | 3,114 | −8 | −8 |
| combined | 4,088 | 4,084 | −4 | −4 |

No row is credited: the only candidate class (`* → str-model-rejected`) is
the 8 QF_S `sat-budget → str-model-rejected` rows, and the base binary gives
`fence=sat-budget` on all 8 (3/3 each).

## Transition matrices

Changed rows only (60), from `target/slice58-after/join.txt`:

| logic | base verdict | after verdict | rows |
| --- | --- | --- | ---: |
| QF_S | unknown:sat-budget | unknown:str-model-rejected | 8 |
| QF_S | unknown:str-model-rejected | unknown:sat-budget | 4 |
| QF_S | unverified | correct | 3 |
| QF_SLIA | timeout | unknown:sat-budget | 9 |
| QF_SLIA | unknown:str-model-rejected | correct | 8 |
| QF_SLIA | unverified | correct | 28 |
| total | | | 60 |

## Triage

Method (slice-53/57): for every changed row that starts or ends in `correct`
(39 rows, all ending there) or ends in `str-model-rejected` (8 rows, for crediting), 3 runs per
binary, interleaved, on the bench's command line (`taskset -c 12-23 prlimit
--as=3221225472 timeout -s KILL 21 timeout 20 $bin --stats …`), with nothing
else on the machine. The 4 `str-model-rejected → sat-budget` rows were run in
a separate pass (`triage-reverse.tsv`). No group exceeds 200 rows, so no
sampling: 51 rows, 306 runs (`triage.tsv` holds 47 rows × 6 runs = 282 lines,
`triage-reverse.tsv` 4 × 6 = 24). A row is *attributable* if base
and after each reproduce their bench verdict 3/3, *noise* otherwise.

| group | rows | disposition |
| --- | ---: | --- |
| QF_SLIA `str-model-rejected → correct` (stringfuzz `transformed/z3str2/regex-050-*`) | 8 | **attributable**: base `unknown fence=str-model-rejected` 3/3, after `unsat` 3/3; z3 `unsat` |
| QF_S `unverified → correct` (automatark-lu) | 3 | noise: answers identical on both binaries 3/3 (`unsat`, `sat`, `unsat`); the base run's z3 oracle timed out, the after run's oracle confirmed |
| QF_SLIA `unverified → correct` (stringfuzz regexbig / regexlengths / regexpair / regexsmall) | 28 | noise: `sat` on both binaries 3/3; same oracle effect |
| QF_S `sat-budget → str-model-rejected` (Jiang slog_stranger) | 8 | reproduces 3/3 (base `sat-budget`, after `str-model-rejected`); no `correct` change, informational |
| QF_S `str-model-rejected → sat-budget` (Jiang slog_stranger 2950, 3686, 4068, 5414) | 4 | reproduces 3/3 (base `str-model-rejected`, after `sat-budget`); informational |
| QF_SLIA `timeout → sat-budget` | 9 | not triaged (neither side is `correct`; timeout flips are bench-time resource noise) |

**Rows G′ decided: 8** (the attributable group above): in each, the base
binary answered `unknown` 3/3 and the after binary answers `unsat` 3/3. All
are the stringfuzz `regex-050-*` transformed family: `fuzz-graft-fuzz`,
`graft-graft-multiply…`, `multiply-multiply-…`, `multiply-reverse-…`,
`multiply-translate…`, `translate-graft-translate`, `translate-rotate-fuzz`,
`translate-translate-…` (full paths in `target/slice58-after/triage.tsv`).

**Unverified-z3 check (Step 4).** No changed row has an `unverified` after
verdict (the three `unverified` entries in the matrix are base-side), so the
list `target/slice58-after/unverified.txt` is empty and there are 0 rows and
0 disagreements.

The 31 `unverified → correct` rows are a harness effect, not a change of
answer: base status `unknown` with z3 oracle `timeout`, after oracle `sat`
(29) or `unsat` (2), with identical shinri answers. They are not counted
for the slice.

## Timing

Serial, interleaved, pinned to core 12, 150 rows per logic sampled with
`random.Random(58)` from rows that are `correct` in both runs
(`target/slice58-after/timing.py`, output `timing.txt`):

| logic | rows | base | after | ratio |
| --- | ---: | ---: | ---: | ---: |
| QF_S | 150 | 1.07 s | 1.04 s | 0.974 |
| QF_SLIA | 150 | 1.59 s | 1.62 s | 1.017 |

Both ratios are inside 0.95–1.05 (no re-run needed). Bench `wall_ms` over
all both-`correct` rows (QF_S 16,057, QF_SLIA 24,873):

| logic | base median / p90 | after median / p90 |
| --- | ---: | ---: |
| QF_S | 14 / 36 ms | 8 / 21 ms |
| QF_SLIA | 16 / 45 ms | 5 / 15 ms |

The bench medians fall for the same reason as in slice 57: the base run was
slower throughout. The serial isolated measurement above is the evidence.

## What changed versus the spec

1. **Guards `g1`, `g3`, `rf2`, `rf3`, `rf4` only forbid `unsat`** (Task 1
   controller ruling). At HEAD `e784454` the first four answer
   `unknown fence=str-model-rejected` and `rf4` answers
   `unknown fence=sat-budget` (z3: `sat` for all; confirmed with the base
   binary `f515c00`). The plan's premise (guards `sat` at HEAD) was false,
   and G′ is conflict-only, so it cannot change those answers. The guards
   assert "never `unsat`; if `sat`, the witness satisfies every assertion",
   which keeps the §7.3 sound-direction role and does not pin `unknown`. Cost:
   they no longer catch a `sat → unknown` regression. The five shapes are
   queued as `str-model-rejected` classification seeds (§9 item 1). After
   the slice they still answer `unknown`/non-`unsat` and the probes pass.
2. **`m3`/`m4` HEAD outcomes (Task 1 Step 4).** `m3` fails at HEAD as
   expected; `m4` (negative polarity) already passes at HEAD and is kept as
   a regression guard, so the before count is 7 PASS / 4 FAIL.
3. **Oracle family runtime ~669 s (> 5-min rule), no `#[ignore]`** (Task 1
   ruling): `differential_qfs_member_prefix` stays at 300 iterations because
   the `oracle` CI job runs only on schedule / `workflow_dispatch`, not on
   the blocking tier the 5-minute rule protects; z3 is the slow side. Cost:
   nightly oracle job about 11 minutes longer; fix by lowering iterations or
   z3 `-T`.
4. **Unit test `g_prime_reads_member_deep_nf`** (Task 2 deviation): `known`
   is reordered (`cb` before `z`), because `build_node_of` picks the first
   non-constant term in `known` as the representative, which differs from
   the brief's assumption. The helper code is verbatim.
5. **Oracle `sat` 73 → 71** (Task 2 review note): two oracle instances went
   `sat → unknown` (shinri-unknown with z3 `sat` 86 → 88). Decisiveness
   only; 0 disagreements.
6. **QF_S `str-model-rejected` rises by 4 (raw and credited).** The 8
   `sat-budget → str-model-rejected` and 4 `str-model-rejected →
   sat-budget` Jiang `slog_stranger` rows reproduce 3/3, so the movement is
   deterministic and slice-attributable (the only engine change is G′), but
   it is a change of fence label, not of verdict (all stay `unknown`, none
   were `correct`); the mechanism was not investigated. The spec states criterion 3 for the
   QF_S + QF_SLIA combined count, which falls by 4; QF_S alone rises. This is
   reported honestly and does not fail the criterion as written.
7. **Step 9 not run by the analysing agent** (controller ruling, ledger):
   push/PR is deferred to the finishing step; the report and spec section
   are committed locally.
8. **Ledger ruling: work on the branch in `/workspace`**, not a separate
   worktree, because the corpus and `target/` artifacts live here; the
   controller ran Tasks 0 and 3 directly (no review surface); plan/spec
   commits `adc85c5`, `108be50` ride the slice PR.
9. **Deferred minors from review** (not fixed): `slice58_probes.rs` module
   doc still says g*/rf* "must stay sat"; ~190-character doc lines on the five
   `not_unsat_*` guards; the five guards are vacuous on `unknown`;
   `before.txt` records PASS/FAIL only; the oracle witness check is skipped if
   the model is unparseable; `MEMBER_CAP` and the helper sit between
   `memb_check`'s doc comment and its `fn`; comments at `memb.rs:151-152`,
   `:307` say a concat is never the representative, but `build_node_of` can
   keep one; `g_prime_skips_unexpandable_member` never reaches the `None`
   skip and the node-cap skip is untested; `g_prime_negative_polarity` checks
   only `is_some()`.

## Gates

- `mise run ci` (lint, deny, secrets, test): exit 0; nextest 1735 run /
  1735 passed / 6 skipped (651 s).
- Oracle suite `cargo nextest run -p shinri-solver --features oracle`:
  808 run / 808 passed / 2 skipped (1,597 s). Non-zero discovered count
  confirmed.
- `shinri-str` unit suite: 263/263 (Task 2), including the six `g_prime_*`
  tests.
- `slice58_probes`: 11/11.

## Queued for the next slice

Ordered. Items 1–3 are spec §9's; item 4 carries the rest. Slice-57's items 1
and 6 merge into §9 item 1 (classify the `str-model-rejected` population and
the remaining approach-2 parts), and its item 2 is §9 item 2. Its items 3–5
and carried lists follow verbatim.

1. **Classify the `str-model-rejected` population** (4,089 rows at slice 57,
   4,084 after this slice), for example by the first violated assertion and
   the class shape. Seeds: the five guards `g1`, `g3`, `rf2`, `rf3` (`unknown
   fence=str-model-rejected`) and `rf4` (`unknown fence=sat-budget`), all z3
   `sat`. This absorbs slice-57 queue items 1 and 6: the remaining
   approach-2 parts (constant-head strip, cited deep NF on the word-equation
   path, minted length links) have no current reproducer and wait for one
   from the classification.
2. **Bare-E and `Not(Eq)` arm removal — possibly unblocked.**
   `translate-rotate-fuzz` was the smallest reproducer of the order
   sensitivity that blocked it, and now answers `unsat`. Re-run the R6 probes
   (`slice33_probes::probe_c_len_zero_var`,
   `script_e2e::user_pfx_name_declared_before_any_mint_still_works`) with
   bare-E applied, in that slice.
3. **Suffix analogue of G′** (reverse derivative over a member's constant
   tail), only if the classification shows suffix shapes.

From the slice-57 report's queue, items 3–5 verbatim:

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

- Spec: `docs/superpowers/specs/2026-10-03-shinri-slice58-member-prefix-design.md`
- Plan: `docs/superpowers/plans/2026-10-03-shinri-slice58-member-prefix.md`
- Slice-57 report: `docs/superpowers/research/2026-10-03-smtlib-2024-slice57-str-model-reconcile-report.md`
- Evidence (git-ignored): `target/slice58-before.txt`, `target/slice58-after/{join.txt,changed.tsv,triage.tsv,triage-reverse.tsv,timing.txt}`, `bench/results/slice58{,-base}/`
