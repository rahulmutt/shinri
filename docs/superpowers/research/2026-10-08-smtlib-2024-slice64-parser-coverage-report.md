# SMT-LIB 2024 re-run — slice 64 (parser coverage: Reals-logic numerals, named terms, define-sort) — shinri @ 1d3e7fd (+ merge 6884bc2)

## Headline

Slice 64 widens the parser (the only trust boundary) in three places:
integer literals are `Real` under Reals-only logics, `(! t attr*)`
annotations with `:named` aliases are accepted, and nullary `define-sort`
aliases are accepted. Before it, 39,998 of 40,407 QF_FP files, 2,287 of
3,037 QF_LRA/QF_UFLRA files and all 34 Rodin `QF_UF` files failed to parse.
Amendment A added two pre-existing `shinri-fp` soundness fixes after the
newly reachable QF_FP rows exposed 3 wrong answers (§ FP soundness).

Binaries: base `90ecaeb` (md5 `cc09e016…`, identical to `slice63-base`);
pre-fix after `a7dd0cf` (md5 `5d6821de…`); post-fix `1d3e7fd` (md5
`69dd2578…`). The merge `6884bc2` brings slice 63 in (md5 `5124ac11…`);
every bench run in this report used one of these four binaries. The final
review's fix wave (§ Final-review fix wave) changed parser code after them;
its gates are in § Gates.

- **`parse-error` drops.** QF_FP 39,998 → **4** (−39,994); QF_LRA +
  QF_UFLRA 2,287 → **0**; Rodin 34 → **0**; neutrality sample 158 → 0.
- **`wrong = 0` in every after run.** For QF_FP this is the combined set
  (pre-fix run with the 8,570 fp-ops rows replaced by the post-fix re-run).
  The pre-fix QF_FP run had 3 wrong rows; both causes are fixed (§ FP
  soundness).
- **Zero `correct → non-correct` rows** in all four row sets.
- **Rows that left `parse-error` and are now `correct`:**

| logic | family | → correct | → other |
| --- | --- | ---: | --- |
| QF_FP | wintersteiger | 39,865 | 129 timeout |
| QF_LRA | sal | 97 | 10 timeout |
| QF_LRA | meti-tarski | 76 | 174 theory-refused |
| QF_LRA | spider_benchmarks | 42 | |
| QF_LRA | tta_startup | 32 | 40 timeout |
| QF_LRA | uart | 12 | 61 timeout |
| QF_LRA | clock_synchro | 10 | 8 timeout |
| QF_LRA | 2019-ezsmt | 9 | 1 timeout |
| QF_LRA | TM | 5 | 5 timeout |
| QF_LRA | check | 2 | |
| QF_LRA | LassoRanker | 0 | 414 theory-refused, 5 timeout |
| QF_LRA | miplib | 0 | 42 theory-refused |
| QF_LRA | latendresse | 0 | 18 theory-refused |
| QF_UFLRA | cpachecker-induction-svcomp14 | 10 | 180 theory-refused, 108 timeout, 9 panic, 2 oom |
| QF_UFLRA | FFT | 3 | |
| QF_UFLRA | cpachecker-bmc-svcomp14 | 2 | 10 timeout |
| QF_UFLRA | mathsat | 0 | 900 theory-refused |
| QF_UF | 20170829-Rodin | 34 | |

  Totals: QF_FP 39,865; QF_LRA 285; QF_UFLRA 15 (300 for the LRA set; the
  Rodin 34 are separate). Destinations of the 2,287 LRA-set rows: 300
  `correct`, 130 + 118 = 248 `timeout`, 648 + 1,080 = 1,728
  `unknown:theory-refused`, 9 `panic`, 2 `oom`.
- **New `timeout`/`oom`/`panic` are reported, not gated.** Rows that were
  base `timeout` and moved (not parse-error rows): QF_FP 8 → `correct`, 8 →
  `oom`, 1 → `unverified`; LRA set 7 + 1 → `correct`, 1 → `oom`, 4 → `panic`.
  The 13 `panic` rows are the stack-overflow finding below.
- `unknown:theory-lira` rows (36 at base) become `correct` (8) and
  `timeout` (28): Real numerals remove the Int/Real mix that made them
  unlinearizable.

### Findings queued (prominent)

1. **13 QF_UFLRA `cpachecker-induction-svcomp14` rows abort with a solver
   stack overflow at `check-sat`.** Message: `thread 'main' has overflowed
   its stack`. The 13 files span 5.0–161.9 MB; the repro below is the
   22.7 MB one, with ~462k chained `define-fun`s. In the repro all 831
   preceding commands print `success`, so the parser handles it; the crash is
   deep recursion in a solver pass over a very deep term DAG, newly reachable
   because the files now parse. The same 13 rows panic after the merge
   (§ Post-merge LRA addendum). Repro:
   `QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.cs_stack_false-unreach-call.i.smt2`.
   *Ruling (ledger):* queue it, don't fix it in slice 64. It is not a wrong
   answer (criterion 1 is about wrong answers), the parser is not the
   crashing component, and the fix lives in solver passes outside amendment
   A's scope. Cost if wrong: 13 files abort instead of failing to parse
   until the next slice; the user may prefer to fix it here (to be raised
   at PR time). A further 3 rows of the same family go `oom` and 4 base
   `timeout` rows became `panic` (the 13 includes those 4).
2. **4 chained FP comparisons** still fail to parse (see Residual parse
   errors).
3. **1,728 rows newly reach `unknown:theory-refused`** (648 QF_LRA, 1,080
   QF_UFLRA; 133 more in the sample). This is the slice-63 shape,
   `(* (- k) x)`, which slice 64 now unblocks at parse time but slice 63's
   fix is not in the benchmarked binary. The merge brings slice 63 in; the
   post-merge LRA run (§ Post-merge LRA addendum) takes all of them out of
   `theory-refused`: 1,083 → `correct`, 703 → `timeout`, `wrong` 0.
4. **Spec §9 error-continuation item** (a sort error drops the assertion and
   a later `check-sat` still answers) is unchanged. This slice shrinks the
   population that hits it (4 residual rows) but does not change the
   behaviour; see the queue below.
5. **Parametric `define-sort`: 0 rows.** In the QF_FP, QF_LRA/QF_UFLRA,
   Rodin and sample sets, every `unsupported command: define-sort` row
   (39,994 at base) now parses; no after run has a parametric-`define-sort`
   error. The parametric case stays an explicit error and has no known users
   in the benchmarked logics.
6. **Ledger-deferred minors** (§ Queued for the next slice).

## Success criteria (spec §8)

| # | Criterion | Result | Evidence |
| --- | --- | --- | --- |
| 1 | `wrong = 0` in every after run | **PASS** | join prints `wrong after: 0` for QF_FP (combined), LRA, Rodin, sample. The pre-fix QF_FP run had 3 wrong rows; the post-fix fp-ops re-run (8,570 rows) is 8,570 `correct` |
| 2 | QF_FP `parse-error` drops by ≥ 39,900 | **PASS** | 39,998 → 4 (−39,994) |
| 3 | QF_LRA + QF_UFLRA `parse-error` drops by ≥ 2,000; the rest classified | **PASS** | 2,287 → 0; nothing remains to classify |
| 4 | All 34 Rodin rows parse | **PASS** | 34 → 0 `parse-error`; 34 `correct` |
| 5 | No `correct → non-correct` row reproduces on 3 re-runs | **PASS (vacuous)** | the join has 0 `correct → non-correct` rows in any set, so Step 6 had no input rows |
| 6 | Gates green (§7.4) | **PASS** | pre-fix ci 1866/1866, oracle 864; post-fix ci 1873/1873, oracle 869, fuzz clean; post-merge ci 1887/1887, oracle 878/878; final-review fix wave: see § Gates |
| 7 | Neutrality sample changes only at the timeout edge | **PASS by class; 3× noise re-run not done** | 158 `parse-error` rows move as expected. The other 56 changes are 55 base `timeout` → `correct` (40) / `oom` (15) in QF_UF, QF_UFLIA, QF_LIA and QF_BVFP — rows that already parsed at base, in logics without the Real-numeral change — plus 1 QF_LRA `theory-lira` → `timeout`, a logic the slice does touch (Real numerals remove its Int/Real mix, as for the LRA set's 36 `theory-lira` rows); 0 `correct → non-correct`. They were not re-run 3×, because the plan's Step 6 re-runs only `correct → non-correct` rows |

## FP soundness (amendment A)

The first after run (`slice64-fp`, pre-fix binary `a7dd0cf`) found **3 wrong
rows** in the newly reachable QF_FP set, and no other run has any. Running
the *base* binary on the same files with the `define-sort` aliases inlined by
hand gives the same wrong answers, so the parser did not cause them. They
are `shinri-fp` bugs that were unreachable while every QF_FP file failed to
parse. The owner ruled (2026-10-07) to fix them in this slice.

| row | `:status` | pre-fix | cause | post-fix |
| --- | --- | --- | --- | --- |
| `wintersteiger/min/min-has-solution-13472` | sat | unsat | ±0 tie | correct |
| `wintersteiger/fma/fma-has-solution-4663` | sat | unsat | fma zero addend | correct |
| `wintersteiger/fma/fma-has-no-other-solution-4663` | unsat | sat | fma zero addend | correct |

**Root cause 1: `fp.min` / `fp.max` on a ±0 tie** (`6c32ff4`).
`blast/minmax.rs` hard-coded the `(+0, −0)` tie to −0 for `fp.min` and +0 for
`fp.max`. SMT-LIB leaves the result unspecified (either zero), so `fp.min`
is *some fixed function* whose value on the two tie inputs is unknown, and a
solver must admit both choices, consistently. The fix mints a tie bit per key
`(is_max, eb, sb, x_is_pos_zero)`, once per query, cached on the blaster
(`WordSink::fp_tie_bits`); a set bit means the tie returns +0. The bits are
**shared, never per occurrence**. A per-occurrence choice would let
`fp.min(a,b) ≠ fp.min(c,d)` be satisfiable with `a=c, b=d`, which no
interpretation of the function allows, and would turn the fix into a wrong
`sat` source. Non-tie behaviour, including NaN passthrough, is unchanged.

**Root cause 2: `fp.fma` zero-addend election** (`1d3e7fd`). `blast/fma.rs`
normalizes the addend's significand, so a zero addend gets exponent
`emin − pw` (−1,128 for Float64). The code assumed that always loses the
hi/lo election to the product. The reproducer's product underflows further
(exponent about −1,576), so the zero addend won, `res_sign` took its sign,
and an exact result that is tiny and negative rounded to +0 where IEEE 754
requires −0. The fix elects the product whenever the addend is zero and the
product is not. The hypothesis was **RED-confirmed**: with the election hunk
reverted, the unit test got `0x0` where it wants `0x8000000000000000` and
both e2e tests failed. Both-zero and exact-cancellation signs are decided by
`cancel_zero` and the rounding-mode zero-sign rule, unchanged. The reviewer
checked `fp.add` (zero exponent is an `emin` floor) and `fp.mul` (no
election) for the same bug; neither has it. The expected values in the
tests are literal IEEE results, not `ref_fma`.

**fp-ops re-run.** Rows with `fp.min`, `fp.max` or `fp.fma`: 8,570 files
(matches spec §8: 5,706 min/max, 2,864 fma). Re-run with `1d3e7fd` as
`slice64-fp-ops`: 8,570 `correct`. Against the pre-fix run only the 3 wrong
rows changed, all to `correct`; there are 0 other verdict changes.
**Combined QF_FP set** (`slice64-fp-combined`, the pre-fix run with the
fp-ops rows replaced): 40,079 `correct`, 306 `timeout`, 15 `oom`, 3
`unverified`, 4 `parse-error`, **0 wrong**. Rows without these operators
cannot change under §3.5, so the pre-fix run stands for them.

## Commands

`A=/workspace/target/slice64-after` (pre-fix), `F=/workspace/target/slice64-fpfix`
(post-fix), `B=/workspace/target/slice64-base`, `M=/workspace/target/slice64-merged`
(merge). `$X` stands for whichever of `$B`, `$A`, `$F`, `$M` the run uses
(each directory holds that build's `shinri` and `shinri-bench`; see § Runs).

```bash
# base: worktree at 90ecaeb; after: a7dd0cf; post-fix: 1d3e7fd; merged: 6884bc2
taskset -c 0-11 cargo build --release -p shinri-cli -p shinri-bench
taskset -c 12-23 $X/shinri-bench run --logics <set> --corpus <corpus> --results /workspace/bench/results \
  --timeout 20 --mem-mb 3072 --jobs 3 --solver $X/shinri --run-id <id>
# gates
taskset -c 0-11 mise run ci
taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle
(cd crates/shinri-parser && ASAN_OPTIONS=detect_leaks=0 taskset -c 0-11 mise x rust@nightly -- cargo fuzz run parse_script -- -max_total_time=600)
```

Row sets: fp = all QF_FP (40,407); lra = QF_LRA + QF_UFLRA (3,037); rodin =
the 34 `parse-error` QF_UF Rodin rows (hard links); sample = the slice-59
2,000-row seeded sample; fp-ops = the 8,570 operator files. Join:
`bench/results/slice64-*` through the plan's Step 4 script
(`$A/join.txt`, `$A/changed.tsv`). Spot checks: `unverified-confirm.txt`.

## Runs

`--timeout 20 --mem-mb 3072 --jobs 3`, cores 12–23. Start times are the
fixture's `started`; end is the last result write.

| run id | binary | started (UTC) | finished | rows |
| --- | --- | --- | --- | ---: |
| slice64-base-fp | base `cc09e016`, 90ecaeb | 2026-10-07 16:45:09 | 17:18:22 | 40,407 |
| slice64-base-lra | base | 17:18:29 | 17:48:40 | 3,037 |
| slice64-base-rodin | base | 17:48:40 | 17:48:41 | 34 |
| slice64-base-sample | base | 17:48:43 | 18:29:19 | 2,000 |
| slice64-fp | pre-fix `5d6821de`, a7dd0cf | 18:42:10 | 22:51:19 | 40,407 |
| slice64-lra | pre-fix | 22:51:22 | 23:57:45 | 3,037 |
| slice64-rodin | pre-fix | 23:57:45 | 23:57:45 | 34 |
| slice64-sample | pre-fix | 23:57:45 | 2026-10-08 00:32:34 | 2,000 |
| slice64-fp-ops | post-fix `69dd2578`, 1d3e7fd | 2026-10-08 07:14:03 | 07:23:27 | 8,570 |
| slice64-lra-merged | merged `5124ac11`, 6884bc2 | 2026-10-08 08:52:57 | 11:24:33 | 3,037 |

`slice64-fp-combined` is derived (no run). The base QF_FP run has all
40,407 rows; only 206 are `correct` because the base fails to parse 39,998.

**Host load.** Unequal and high; none of these is a quiet-host timing
measurement. `uptime` at launch of each chain (1/5/15 min): base
117.74 / 110.41 / 109.06 (16:44:49); pre-fix after 65.98 / 63.88 / 68.21
(18:42:00); post-fix fp-ops 82.15 / 76.85 / 57.90 (07:13:58); merged LRA
80.38 / 100.94 / 107.27 (08:52:54). Only the first run of a chain recorded
`uptime`. Here the base ran under *more* load than the after, so
timeout-edge rows (the 56 sample changes, the 55 base-timeout rows that
became `correct`/`oom`) are not evidence of a performance change in either
direction. The 8 QF_FP base-timeout → `oom` rows (qurt, sin, sin2) are a
memory effect at the 3,072 MB cap, not a verdict claim.

## Verdict changes

Source: `$A/join.txt` (QF_FP uses the combined run).

| set | changed | parse-error | wrong after | other changes |
| --- | ---: | --- | ---: | --- |
| fp (combined) | 40,011 | 39,998 → 4 | 0 | 39,865 → correct, 129 → timeout; base timeout → 8 correct, 8 oom, 1 unverified |
| lra | 2,336 | 2,287 → 0 | 0 | 300 correct, 248 timeout, 1,728 theory-refused, 9 panic, 2 oom; base timeout → 8 (7 + 1) correct, 1 oom, 4 panic; theory-lira → 8 correct, 28 timeout |
| rodin | 34 | 34 → 0 | 0 | 34 correct |
| sample | 214 | 158 → 0 | 0 | 13 QF_LRA correct, 7 + 5 timeout, 41 + 92 theory-refused; base timeout → 40 correct, 15 oom; theory-lira → 1 timeout |

By-logic detail for the LRA set (join): QF_LRA parse-error → 285 correct,
130 timeout, 648 theory-refused; QF_UFLRA parse-error → 15 correct, 118
timeout, 1,080 theory-refused, 9 panic, 2 oom. LRA-set totals after: 748
`correct` (432 at base), 487 `timeout`, 1,786 `theory-refused`, 13 `panic`,
3 `oom`. The `theory-refused` total 1,786 is 1,728 new plus 58 that were
already refused at base.

## Residual parse errors

| count | set | message | cause |
| ---: | --- | --- | --- |
| 4 | QF_FP | `sort error: Arity { expected: 2, found: 3 }` | `QF_FP/schanda/spark/{average_2,discrete,guarded_div_1,range_mult}`: a chained FP comparison, `(fp.leq a mid b)`. SMT-LIB marks these `:chainable`; the core arity check rejects 3 arguments. Pre-existing, outside this slice, queued. |
| 0 | LRA set | none | all 2,287 parse |
| 0 | Rodin | none | all 34 parse |

The 39,994 `unsupported command: define-sort` rows and the 3 LRA sort-error
classes (`NotApplicable` 1,854, `Mismatch` 433) are all gone.

## Unverified confirmation

3 `unverified` rows, all QF_FP, shinri answers `sat`. `unverified-confirm.txt`:

| row | shinri | z3 | cvc5 |
| --- | --- | --- | --- |
| `griggio/fmcad12/newton.7.2.i` | sat | timeout | sat |
| `griggio/fmcad12/newton.7.3.i` | sat | timeout | undecided |
| `ramalho/esbmc/newton_3_6_false-unreach-call-main` | sat | timeout | undecided |

For the last two (`:status unknown`; z3 and cvc5 undecided at 120 s) the
model was confirmed by pinning: shinri's `get-model` values were asserted
into the script and z3 answered `sat` on the pinned script
(`model-pins/`). The pinned script is a strengthening of the original, so the
original is `sat`. No disagreement with shinri; the plan's 20-row sample
confirmation is replaced by checking all 3 rows.

## What changed versus the spec

1. **Amendment A** (spec §3.5, §7.5, §8): two `shinri-fp` fixes (shared
   ±0 tie bits, fma zero-addend election), a new `fp_soundness_e2e.rs`,
   criterion 1 reworded, and an fp-ops re-run.
2. **fp-ops targeted re-run instead of a full QF_FP re-run.** Only rows
   containing `fp.min`/`fp.max`/`fp.fma` (8,570) were re-run with the
   post-fix binary; the pre-fix run stands for the rest. Cost if wrong:
   an unrelated change in `1d3e7fd` would go unseen in the other 31,837
   rows; the diffs touch only min/max and fma lowering.
3. **Division-by-zero `Diagnostic`.** `(/ x 0)` reached
   `recip of zero` in the parser (`panic` on the base binary, found while
   planning). It is now a `Diagnostic`, in code Task 2 already touched. A
   pre-existing panic fixed, not a behaviour the spec listed.
4. **`reals_only_arith` is a plain suffix test** on the logic name,
   equivalent to the spec's rule over the supported logics.
5. **`first_error` helper ruling.** The plan's new
   `first_error -> Diagnostic` would clash with the existing
   `first_error(src) -> Option<String>` (27 uses); Tasks 3 and 4 use the
   existing helper and assert on the message text.
6. **Fuzz LeakSanitizer ruling.** The pre-fix fuzz run exited 1 from a
   LeakSanitizer fatal error at exit (LSan cannot run under `ptrace` in
   this environment); the recorded "crash" artifact is the 0-byte input
   (sha1 `da39a3ee…`) and re-runs clean with `ASAN_OPTIONS=detect_leaks=0`.
   So **leak detection was off or ineffective in the fuzz gates**. Leaks
   are outside the threat model's scope; crashes and panics were fuzzed for
   601 s per round with none found. Cost if wrong: a real leak would go
   unnoticed.
7. **Base oracle count reused (859)** from `slice63-base`; the base binary
   is byte-identical (md5 `cc09e016…`), so the test set is the same.
8. **Extra post-merge LRA run** (`slice64-lra-merged`). *Ruling:* the spec
   §6 "no new bench run after the merge" rule predates the finding that
   1,728 rows newly unblocked by slice 64 flow into slice 63's newly
   accepted `(* (- k) x)` path. Neither slice's bench exercised that
   interaction. Cost if wrong: about 1 h of bench cores; no soundness
   downside.
9. **Not done (ledger rulings):** the Task 6 Step 6 re-runs had no input
   rows; the stack overflow (Findings 1) and `(reset)` not clearing the
   Reals flag (below) are queued, not fixed.
10. `(reset)` does not clear `numerals_are_real`: the parser `Env` is
    never cleared on reset (declarations persist too), and any later
    `set-logic` overwrites the flag. Not a gap for this slice. (The fix
    wave makes `(reset)` clear the new push/pop scope stack, nothing more.)
11. **Push/pop scoping of definitions (final review, Important).** The
    parser's macro table (`define-fun`, and slice 64's `:named`) ignored
    push/pop, giving wrong answers on valid incremental scripts. Reusing a
    `:named` name after its pop was rejected ("name already in use"), the
    assertion was dropped, and the next `check-sat` answered `sat` where
    `unsat` is right. A `declare-fun h` after the pop of a scope that bound
    `h` was shadowed by the stale alias and answered `unsat` where `sat` is
    right. The `define-fun` variant of the second shape was **pre-existing
    on `main`** (the `define-fun` variant of the first shape happened to be
    right, because `define-fun` silently overwrote). Fixed in `7d56d6e`
    (§ Final-review fix wave).
12. **The zero-divisor `Diagnostic` (item 3) feeds spec §9's
    continue-after-error behaviour.** `(assert (not (= (/ x 0) (/ x 0))))`
    in QF_LRA used to abort the base binary (`recip of zero`). It now
    prints `(error "division by a zero constant unsupported")`, the
    assertion is dropped, and a following `check-sat` answers `sat`
    (checked on `6884bc2` and on the fix-wave build). That is the §9 queue
    item, not a new class: it answers instead of crashing, and the answer
    is for the weaker problem.
13. **Final-review minors fixed in the same wave:** `:named` inside a
    `define-fun` body with parameters is rejected (it bound an open term
    over the parameter placeholders); `:named` and `define-fun` reject
    builtin operator names (`and`, `=`, `/`, …) and solver-reserved symbols
    (`(! a :named and)` broke every later `(and …)`); the LRA oracle
    gained the cross-slice `(* (- k) v)` shapes; FP doc comments
    (`ref_min`/`ref_max` tie, `exp_diff`) corrected.
14. **Queued by the final review (not fixed):** `declare-fun h` after
    `(! t :named h)` in the *same* scope is accepted (the macro keeps
    shadowing it); `get-value` of a compound FP term prints `?`; and the
    `rem_float32_specials_and_random` test-tier item (below).

## Gates

| round | commit | ci | oracle | fuzz `parse_script` (600 s) |
| --- | --- | --- | --- | --- |
| pre-fix | a7dd0cf | 1866/1866 (15 slow, 6 skipped), exit 0 | 864/864 = 859 + 5, 47 binaries | 3,431,314 runs, no finding; exit 1 only from the LSan environment fault (§ above) |
| post-fix | 1d3e7fd | 1873/1873 (11 slow, 6 skipped), exit 0 | 869/869 = 859 + 5 + 5, 48 binaries | 1,317,812 runs, exit 0 with `ASAN_OPTIONS=detect_leaks=0` |
| post-merge | 6884bc2 | 1887/1887 (13 slow, 6 skipped), 772 s total | 878/878 = 868 on `main` (incl. slice 63) + 10 slice 64, 49 binaries | not re-run (no parser change) |
| final-review fix wave | a34ddca | 1898/1898 (12 slow, 6 skipped), 693 s; = 1887 + 11 new (8 parser unit, 1 streaming, 2 e2e); `fmt --check` and `mise run lint` clean | 880/880 = 878 + the 2 new `parser_coverage_e2e` tests, 49 binaries; `lra_numeral_oracle` with the cross-slice shapes passes | 300 s: `Done 1166827 runs in 301 second(s)`, exit 0 (`ASAN_OPTIONS=detect_leaks=0`) |

Without `--features oracle` the oracle tests run 0 tests; the counts above
are with the feature. Note for the blocking tier: in the post-merge ci,
`shinri-fp blast::rem::tests::rem_float32_specials_and_random` took 727.6 s
under load, over the AGENTS.md 5 min `#[ignore]` threshold (queued).

## Post-merge LRA addendum

Run id `slice64-lra-merged`, binary `6884bc2` (md5 `5124ac11…`), the 3,037
QF_LRA + QF_UFLRA rows, `--timeout 20 --mem-mb 3072 --jobs 3`, cores
12–23, 2026-10-08 08:52:57Z → 11:24:33Z (launch load 80.38 / 100.94 /
107.27). Evidence: `target/slice64-merged/join-merged.txt`,
`target/slice64-merged/loss-retiming.txt`,
`bench/results/slice64-lra-merged/`.

| verdict | base (90ecaeb) | pre-merge (a7dd0cf) | merged (6884bc2) |
| --- | ---: | ---: | ---: |
| `correct` | 432 | 748 | **1,838** |
| `timeout` | 224 | 487 | 1,178 |
| `unknown:theory-refused` | 58 | 1,786 | **0** |
| `unknown:theory-lira` | 36 | 0 | 0 |
| `parse-error` | 2,287 | 0 | 0 |
| `panic` | 0 | 13 | 13 |
| `oom` | 0 | 3 | 8 |
| `wrong` | 0 | 0 | **0** |

- **Cross-slice result.** Every pre-merge `theory-refused` row leaves that
  class: 1,083 → `correct`, 703 → `timeout` (1,786 = the 1,728 slice-64
  newly unblocked + 58 refused at base). Largest moves: QF_UFLRA/mathsat
  854 → `correct` (46 `timeout`), QF_LRA/meti-tarski 174 → `correct`,
  QF_LRA/LassoRanker 414 → `timeout`, QF_UFLRA/cpachecker-induction 51 →
  `correct` / 129 → `timeout`.
- **Other moves:** 12 `timeout` → `correct`, 6 `timeout` → `oom`, 1 `oom`
  → `timeout`.
- **The 13 `panic` rows** are the same stack-overflow rows (Findings 1).
- **5 pre-merge-`correct` → `timeout` rows** (`QF_LRA/sc/sc-7.base`,
  `sc-8.induction3`, `sc-9.induction2`,
  `tta_startup/simple_startup_14nodes.abstract.base`,
  `simple_startup_5nodes.missing.induct`). Re-timed interleaved, 3× per
  binary, no timeout, under load 63–97
  (`target/slice64-merged/loss-retiming.txt`): every run of both binaries
  answers the expected verdict. Merged is faster on 3 rows (e.g.
  14nodes: 18.5 / 14.0 / 15.8 s pre-merge vs 12.8 / 12.5 / 13.1 s merged)
  and within ±1 s of pre-merge on `sc-8` and `sc-9`. `sc-7` straddles the
  20 s limit on both (pre-merge 24.0 / 22.2 / 19.3 s, merged 20.3 / 20.3 /
  18.0 s). So these are timing-edge noise under load, not a loss.
- **Post-merge gates:** ci 1887/1887; oracle 878/878 (= 868 on `main`
  incl. slice 63 + 10 slice 64).

**Code changed after these runs.** Every bench number in this report was
measured on `90ecaeb`, `a7dd0cf`, `1d3e7fd` or `6884bc2`. The fix wave
below changes parser code: definitions are scoped by push/pop, and `:named`
/ `define-fun` reject more names. None of the benchmarked rows was re-run
on it. Those changes only affect scripts that use `push`/`pop` with
definitions, `:named` inside a parameterised `define-fun` body, or a
definition named like a builtin or reserved symbol. Its gates are in
§ Gates.

## Final-review fix wave

Commits on top of `71cb41e` (`7d56d6e`..`a34ddca`, then this docs commit):

- `7d56d6e` **fix(parser): scope define-fun and :named bindings by
  push/pop.** `Env` keeps an undo log of the bindings that scoped
  definitions (`define-fun`, `:named`, `define-sort`) replaced, plus a
  run-length-encoded scope stack of undo-log marks. `push n` costs O(1)
  memory whatever `n` is (`(push 4294967295)` is one stack entry); `pop n`
  costs O(definitions undone), never O(n). Definitions at depth 0 are
  never logged. Popping more levels than are open closes them all and is
  otherwise a no-op, which matches the solver. Scoping is applied only
  after the command's closing `)`, and on the persisted `Env`, so the batch
  and streaming paths behave alike. `(reset)` clears the scope stack.
  **Declarations stay global**, matching the solver: its `Command::Pop`
  truncates assertions only, and its declaration registry and hash-consed
  symbols survive a pop. Also in this commit: `:named` inside a
  parameterised `define-fun` body is rejected (`named term: not allowed
  inside define-fun`); `:named` and `define-fun` reject builtin operator
  and reserved names; `reals_only_arith` doc aligned with spec §3.1.
  Tests: 8 parser unit tests, 1 streaming test, 2 e2e tests
  (`parser_coverage_e2e.rs`: the four final-review scripts answer
  `sat`,`unsat` / `sat`).
- `834d118` **test(solver): cross-slice `(- k)` products in the LRA
  oracle.** Products are also emitted as `(* (- k) v)`, `(* v (- k))` and
  `(* v k)`, and `+` takes integer-literal operands. Per-shape vacuity
  floors were added. Result: `sat=151 unsat=49 z3_checked=200
  neg_coeff_scripts=187 literal_summand_scripts=163`, 0 disagreements, 0
  `unknown`.
- `a34ddca` **docs(fp): tie and `exp_diff` comments.** No behaviour change.

## Queued for the next slice

- **Solver stack overflow** on the 13 `cpachecker-induction` rows (Findings 1).
- **Chained FP comparisons** `(fp.leq a b c)` and the other `:chainable`
  predicates: 4 QF_FP rows.
- **Spec §9 error continuation**: a failed assertion is dropped and a later
  `check-sat` still answers. After this slice the bench sees it only on the
  4 chained-comparison rows (in the benchmarked sets), but it is unchanged.
- **Parametric `define-sort`**: 0 rows in the re-baseline; keep as an
  explicit error until a user appears.
- **`rem_float32_specials_and_random` ~300 s unloaded, 727.6 s under load in
  ci** (AGENTS.md: `#[ignore]` anything over 5 min and keep a smoke
  companion).
- **Final-review deferrals:** `declare-fun h` after `(! t :named h)` in the
  same scope is accepted while the macro keeps shadowing it; `get-value` of
  a compound FP term prints `?`.
- **Ledger-deferred minors:**
  - T1: missing blank line before the new test fns.
  - T2: `coerces_negated_int_literal_in_real_context` asserts only the
    result sort, not the re-minted operand.
  - T3: `skip_attribute_value` silently consumes lexer-error tokens inside
    ignored attribute values (`parse_attr` rejects them; lenient, not
    unsafe); the `:named` alias is bound before later attributes are
    validated, so a failed `(! …)` leaves the alias bound; no tests for
    `:named 3`, `:named )` or an unterminated `(! a`.
  - T4: `declare-sort` after `define-sort` of the same name silently
    shadows (pre-existing `add_sort`); long doc-comment lines; the
    parametric error span is not asserted.
  - T5: a redundant `z3_checked == N` assert. (Literal `+` operands were
    added in the fix wave.)
  - T7: blank line before `tie_bit`; a 107-char doc line in `minmax.rs`; no
    e2e test for order/op/format independence of the tie bits. (The
    `ref_min`/`ref_max` docs were fixed in the fix wave.)
  - T8: thin coverage of the newly reachable deep-product-`hi` path (add `+x·+y` with
    `z = −0` and a symbolic `z`); a 120-char comment line.
- **`(push 4294967295)` crashes the solver**: pre-existing, found in final fix-wave re-review. "Memory allocation of 4294967296 bytes failed"; the solver's `Command::Push` loops per level in crates/shinri-solver/src/lib.rs while parser is O(1)—the solver should cap or validate push count.
- **`(reset)` doesn't clear parser bindings**: pre-existing, found in final fix-wave re-review. The parser's `Env` keeps its macros, function and sort bindings; only the scope stack is cleared.
- **`:named` bindings persist after failed `assert`**: pre-existing, found in final fix-wave re-review. A `:named` binding made inside an `assert` that fails to parse stays bound even though the assertion is dropped.
- **Reserved words accepted as `:named` names**: pre-existing, found in final fix-wave re-review. SMT-LIB reserved words (`let`, `_`, `!`, `as`, `forall`, `par`) are still accepted as `:named` names; harmless because those heads resolve before macros, but non-conforming.

## References

- Spec: `docs/superpowers/specs/2026-10-07-shinri-slice64-parser-coverage-design.md`
  (§3.5 amendment A, §8 criteria, §9 queue).
- Plan: `docs/superpowers/plans/2026-10-07-shinri-slice64-parser-coverage.md`
  (Amendment A: Tasks 7–9).
- Baseline: `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`.
- Slice-63 report: `docs/superpowers/research/2026-10-08-smtlib-2024-slice63-lia-coefficients-report.md`.
- Threat model: `docs/threat-model.md`.
- Evidence: `target/slice64-gates.txt`, `target/slice64-after/{join.txt,changed.tsv,*-parse-errors.txt,unverified-*.txt,model-pins/}`,
  `target/slice64-{base,after,fpfix,merged}/`, `bench/results/slice64-*`.
