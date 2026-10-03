# SMT-LIB 2024 re-run — slice 56 (excluded-middle definition for a bare Bool constant UF argument) — shinri @ 43c531c

## Headline

Slice 56 closes the slice-55 queue's item 1: an atomic Bool constant used as
a UF argument was not tied to `true`/`false`, so `(P q)`, `(not (P true))`,
`(not (P false))` answered `sat` (z3: `unsat`). The fix adds the definition
`(or q (not q))` for each such constant in `word_norm`, so the constant is
forced into `{true, false}`. On the bench (QF_UF, QF_DT, QF_UFLIA, QF_UFLRA,
18,146 rows):

- **0 `wrong`**, 0 panic; parse-error rows are identical to the base (1,263
  both runs).
- 89 of 18,146 rows differ in recorded verdict against slice 55. All are
  resource-limit flips: 63 `correct → timeout`, 18 `timeout → correct`,
  4 `oom → timeout`, 3 `timeout → oom`, 1 `unknown:theory-refused → timeout`.
  No `sat ↔ unsat` change and no `* → wrong`.
- All 89 rows were re-run 3× on **both** binaries (89 × 2 × 3 = 534 runs).
  **No reproducible `correct → *` loss**: for every one of the 63 rows the
  after binary gave the base's correct answer in all 3 runs (62 rows give the
  same single answer in all six runs; the 63rd,
  `blocksworld_from_6_9_0_to_14_0_1_negated_goal_bmc_7`, gave `unsat` on the
  after binary 3 of 3 and on the base 2 of 3). No run on either binary
  produced a wrong answer.
- The bench has an uneven direction (63 losses to 18 gains, net correct
  -45: 15,308 vs 15,353). It is bench-time load, not the fix: the 63
  `correct` rows took 8.6–19.9 s (median 15.8 s) on the base, i.e. they sit
  on the 20 s limit, and a direct serial timing of 8 of them shows no
  difference between the binaries (191.48 s base vs 191.46 s after, each
  within 0.2 s per row). On the 691 rows that are `correct` on both runs
  and took over 5 s on the base, the after run's summed wall time is 7.2 Ks
  vs 6.7 Ks (+7%), consistent with a slower machine during the second run.
- No changed row can trigger the new code path: a grep of the 89 files listed in
  `target/slice56-after/changed.txt` found 0 `declare-fun` with a Bool argument and
  0 `(<field> Bool)` datatype fields (regexes: `\(declare-fun[^)]*\([^)]*\bBool\b[^)]*\)` (declare-fun with a Bool argument) and `\([A-Za-z0-9_|!$@.-]+ Bool\)` (datatype field)). Across the corpus only 105
  QF_UF files declare a Bool-argument function (single-line-regex heuristic; 0 in
  QF_DT, QF_UFLIA and QF_UFLRA), and none of them is among the changed rows.

## Commands

```bash
mise run ci
cargo nextest run -p shinri-solver --features oracle --no-capture \
  -E 'binary(bool_arg_oracle) | binary(qfdt_oracle) | test(differential_qf_uflia_compound_args)'

cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice56-after && cp target/release/shinri target/slice56-after/shinri
md5sum target/slice56-after/shinri | tee target/slice56-after/md5.txt
git rev-parse --short HEAD | tee target/slice56-after/commit.txt
date -u +%FT%TZ > target/slice56-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_UF,QF_DT,QF_UFLIA,QF_UFLRA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice56-after/shinri --run-id slice56 \
  > target/slice56-after/run.log 2>&1; date -u +%FT%TZ > target/slice56-after/finished.txt' &
BENCH_RUN_ID=slice56 mise run bench-report
```

Verdict comparison: a scratch script (not committed) joined
`bench/results/slice55/results.jsonl` and `bench/results/slice56/results.jsonl`
by `path` (the files have a fixture header line, skipped; key sets identical,
18,146 each) and counted `(logic, base verdict, after verdict)` where the two
differ. Re-runs: each changed path, 3× per binary,
`timeout 25 prlimit --as=3221225472 taskset -c 12-23 <binary> bench/corpus/<path>`,
first `sat|unsat|unknown` line kept, 6 paths in parallel.

## Runs

| run | solver | md5 | started | finished | rows |
| --- | --- | --- | --- | --- | ---: |
| `bench/results/slice55/` (base, reused) | `target/slice55-after/shinri` (built at `1a9db04`) | `6a753b2e1c088e0eefefc0a5ae4b1b38` | 2026-10-02T18:34:35Z | 2026-10-02T20:29:06Z | 18,146 |
| `bench/results/slice56/` (after) | `target/slice56-after/shinri` (built at `43c531c`) | `7c73abb538a48c90b839ac466cf4a3db` | 2026-10-02T22:07:23Z | 2026-10-03T00:07:13Z | 18,146 |

Both runs: `--timeout 20 --mem-mb 3072 --jobs 6`, logics QF_UF, QF_DT,
QF_UFLIA, QF_UFLRA. (Runs are git-ignored.)

## Success criteria (spec §7)

| # | Criterion | Result | Evidence |
| --- | --- | --- | --- |
| 1 | a1–a8 pass; all eight fail on `main` | PASS | Task 1 report: RED run of `binary(slice56_probes)`: 13 discovered, 3 pass (`rf2_ufbv_header_with_bv_term`, `rf3`, `rf4`), 10 fail (a1–a8, `rf1`, `rf2_ufbv_header_without_bv_term`: wrong `sat`); GREEN: probes plus 2 unit tests 15/15; re-run by the controller 15/15 |
| 2 | Bench: 0 `wrong`, 0 panic, no reproducible `correct → *` loss | PASS | 0 wrong, 0 panic; 89 changed rows, 63 `correct → timeout`, none reproducible (re-run 3× on both binaries; *Verdict comparison*) |
| 3 | Oracle: non-zero count, 0 disagreements, no `@` values | PASS | 22 tests discovered, 22 passed; QF_DT 0 disagreements / 0 value disagreements / n_valued 393; QF_UFLIA 0/0/424; QF_UFLRA 0/0/432 (no `n_abstract` any more; an `@` value is now a disagreement) |
| 4 | `mise run ci` green, fmt clean | PASS | 1,691 tests run, 1,691 passed (12 slow), 7 skipped; `cargo fmt --all --check` clean |

## Per-logic matrix (after run)

| logic | total | correct | wrong | parse-error | oom | timeout | unknown |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_DT | 8700 | 8101 | 0 | 0 | 0 | 588 | 11 |
| QF_UF | 7503 | 7028 | 0 | 34 | 0 | 441 | 0 |
| QF_UFLIA | 659 | 135 | 0 | 0 | 3 | 505 | 16 |
| QF_UFLRA | 1284 | 44 | 0 | 1229 | 10 | 1 | 0 |
| all | 18146 | 15308 | 0 | 1263 | 13 | 1535 | 27 |

Base (slice 55), per logic: QF_DT 8106 correct / 583 timeout / 11 unknown;
QF_UF 7060 / 409 timeout / 34 parse-error; QF_UFLIA 143 correct / 492
timeout / 7 oom / 17 unknown; QF_UFLRA 44 correct / 1229 parse-error /
7 oom / 4 timeout. All rows: correct 15,353; timeout 1,488; parse-error
1,263; oom 14; `unknown` 28; wrong 0.

## Verdict comparison

Changed rows (logic, base → after, count):

| logic | base → after | rows |
| --- | --- | ---: |
| QF_DT | correct → timeout | 5 |
| QF_UF | correct → timeout | 50 |
| QF_UF | timeout → correct | 18 |
| QF_UFLIA | correct → timeout | 8 |
| QF_UFLIA | oom → timeout | 4 |
| QF_UFLIA | unknown:theory-refused → timeout | 1 |
| QF_UFLRA | timeout → oom | 3 |
| total | | 89 |

Net: correct -45, timeout +47, oom -1, unknown -1. The parse-error column is
unchanged in every logic (QF_UF 34, QF_UFLRA 1,229), so the late rise of the
run's running parse-error and oom counters (1,220 → 1,263; 10 → 13) was the
QF_UFLRA tail of the corpus being processed, not a change against the base:
the final totals are 1,263 vs 1,263 and 13 vs 14.

### The 63 `correct → timeout` rows (Ruling 3 re-run)

- 62 rows: the same single answer on all six runs (3 per binary). The
  base answer is the correct one, so the after binary reproduces it. No
  reproducible loss.
- 1 row, `QF_DT/20230720-blocksworld/blocksworld_from_6_9_0_to_14_0_1_negated_goal_bmc_7.smt2`:
  base `none, unsat, unsat`; after `unsat, unsat, unsat`. The row sits on the
  limit on the base too. No loss.
- Families: QF_UF `QG-classification/qg5` 29, `qg7` 11, `2018-Goel-hwbench` 5,
  `SEQ` 4, `NEQ` 1; QF_UFLIA `mathsat/Hash` 8; QF_DT `20230720-blocksworld` 5.
  Base wall times 8.6–19.9 s, median 15.8 s.
- No `wrong`, and no answer other than the base's correct one, on any run.

### Rows outside the 3× rule (base verdict not `correct`)

All 26 were also re-run 3× on both binaries.

- 18 `timeout → correct` (QF_UF, mostly `QG-classification/qg5` `gensys_*`,
  plus `qg6/iso_brn_repgen_sk014`): the same single answer on all six runs
  (`unsat`, or `sat` for `sk014`). Both binaries solve them in isolation;
  the base had timed out under load in its bench run. The after-run times were
  9.0–19.5 s. Not credit to this slice.
- 4 `oom → timeout` (QF_UFLIA Certora: `25959_…_65`, `44289_…_14`,
  `44788_…_35`, `93493_4ea6…_49`): no answer within 25 s on all six runs. The
  base's recorded oom wall times were 14.9–18.8 s, so these are memory-growth
  rows near both limits; under the 3 GiB `prlimit` they do not answer on
  either binary. Resource-limit flip, no answer difference.
- 1 `unknown:theory-refused → timeout`
  (`93493_27ab26d5…_51_QF_UFLIA`): `unknown` on all six runs (the base's
  recorded wall time was 10.9 s; the after run hit the 20 s cap). Both
  binaries give the same sound `unknown`; the bench-time timeout is load.
- 3 `timeout → oom` (QF_UFLRA `cpachecker-induction.test_locks_{6,7,15}`):
  no answer on all six runs under the 3 GiB limit; the after run's recorded
  oom came at 17.4–17.7 s, the base timed out at 20.0–20.3 s. Same
  boundary behaviour (about 3 GiB reached near the time limit), no answer
  difference. The slice-55 run already had this family at 7 oom rows.

Raw re-run lines are kept in the session scratchpad, not committed.

## What changed versus the spec

1. **Bench base reused.** The base is the slice-55 run
   (`bench/results/slice55/`, binary `target/slice55-after/shinri`), as the
   spec §7 says. No deviation.
2. **Unit-test expectation updated (Task 1 Step 7).** One existing unit test,
   `bare_constants_and_connective_children_are_not_purified`, was updated
   because a bare Bool constant argument now gets the excluded-middle
   definition; a new test,
   `bare_bool_constant_argument_gets_excluded_middle_definition`, covers it.
   No other test needed changes.
3. **`(or k (not k))` was not folded** (Task 1): probe a7 shows the model
   `q = false` with no `@` value.
4. **Task 2 before-evidence.** With the pre-fix `word_norm.rs` (`1784436`) the
   extended oracle fails in all three families:
   QF_DT value_disagreements 50 (n_valued 189), QF_UFLIA 1 disagreement +
   75 value disagreements, QF_UFLRA 1 + 74; the failures are
   "abstract value @elem0 for s" and one wrong `sat` each in QF_UFLIA and
   QF_UFLRA. After the fix: 0 / 0 in all three. The oracle's random stream
   changed (the extra Bool constant `s`), so the sat/unsat counts differ from
   slice 55.
5. **Bench noise direction.** The spec (§7) expected resource-limit flips and
   the Ruling 3 re-run. The flips here are more one-sided (63 to 18) than
   slice 55's; the serial timing in the *Headline* shows equal speed per
   row on the two binaries.
   The slice-54→55 flips skewed 42/19 the other way (`timeout → correct`
   versus `correct → timeout`), so the slice-55 base was itself a fast run. No
   changed row can trigger the new code path (0 Bool-argument `declare-fun`, 0
   `(<field> Bool)` fields in the 89 changed files; 105 QF_UF files corpus-wide
   declare one, single-line-regex heuristic), which supports load, not the fix.
6. **Probe-only coverage.** Review Focus 1–2 (QF_SLIA, QF_UFBV headers) are
   probe-covered only, not benched.

## Gates

- `mise run ci`: green. 1,691 tests run, 1,691 passed (12 slow), 7 skipped
  (Task 1 report). `cargo fmt --all --check`: clean.
- Oracle gate (`--features oracle`):
  `binary(bool_arg_oracle) | binary(qfdt_oracle) | test(differential_qf_uflia_compound_args)`:
  **22 tests discovered, 22 passed** (non-zero; Task 2 report, re-run by the
  controller).
- Oracle lines (Task 2): QF_DT sat=119 unsat=81 unknown=0 disagreements=0
  value_disagreements=0 n_valued=393; QF_UFLIA sat=147 unsat=53 unknown=0 0 0
  n_valued=424; QF_UFLRA sat=147 unsat=53 unknown=0 0 0 n_valued=432.
- `mise run lint` (clippy `-D warnings`): clean (Task 2 report).

## Queued for the next slice

Ordered. Items 2–3 are from slice 55; the rest are carried.

*(Item 1 of slice 55's queue, the wrong `sat` for a Bool constant as a UF argument, is closed by slice 56 and removed here. Items 2 onwards keep slice 55's numbering and wording; "slice 56" in item 2 is the slice-53 carry's label for the `Not(Eq)` work, not this slice.)*

2. **`Not(Eq)` / bare-E / string-order item (slice 56).** Remove the
   redundant `Not(Eq) → (or Lt Gt)` arm together with the bare-E
   simplification, the string-engine search-order sensitivity and the axiom
   memory-growth measurement (details under the slice-53 carry below).
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

- Spec: `docs/superpowers/specs/2026-10-02-shinri-slice56-uf-bool-const-arg-design.md`
  (§7 criteria, §11 measured outcomes).
- Slice-55 report: `docs/superpowers/research/2026-10-02-smtlib-2024-slice55-get-value-report.md`.
- Commits: `9019a26`, `1784436` (spec, plan), `7e8c706` (fix), `43c531c` (oracle).
- Runs (git-ignored): `bench/results/slice56/` (after), `bench/results/slice55/` (base).
