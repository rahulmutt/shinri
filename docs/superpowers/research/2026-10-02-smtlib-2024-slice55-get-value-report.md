# SMT-LIB 2024 re-run — slice 55 (get-value echo, purified-term remap, symbol quoting) — shinri @ 1a9db044ea6b

## Headline

Slice 55 changed only what `get-value` and `get-model` print. It did not
touch solving. The bench confirms it is verdict-neutral on the four logics
(QF_UF, QF_DT, QF_UFLIA, QF_UFLRA, 18,146 rows):

- **0 `wrong` rows**, 0 status-suspect, 0 panic. Parse-error rows are
  identical to the base (1,263 both runs).
- 65 of 18,146 rows differ in recorded verdict against the slice-54 run.
  Every one is a resource-limit flip: 61 `timeout ↔ correct` (QF_UF 55,
  QF_DT 1, QF_UFLIA 5; see the transition table), 1 `timeout → oom` and 3
  `oom → timeout`. There is no `sat ↔ unsat` change and no `* → wrong`.
- Per Ruling 3, all 65 rows were re-run 3× on **both** binaries (65 rows × 2 binaries
  × 3 runs = 390 runs). No row gave a different *answer* on the two binaries; the only
  differences are `unsat` ↔ no answer within 25 s, and they occur
  **within a single binary across its own 3 runs** (QG-classification
  `gensys_icl*` rows right at the 20 s limit). That is timing noise, not a
  reproducible verdict difference.

Outside the bench the slice delivers the real output changes (spec §2–§3);
the oracle gates are in *Gates*.

## Defect found (pre-existing, not fixed here)

**Wrong `sat`: an atomic Bool constant used as a UF argument is not tied to
`true`/`false`.** Reproducer (exact):

```smt2
(set-logic QF_UF)(declare-const q Bool)(declare-fun P (Bool) Bool)(assert (P q))(assert (not (P true)))(assert (not (P false)))(check-sat)
```

Re-verified for this report with the after binary
(`target/slice55-after/shinri`, md5 `6a753b2e…`):

| solver | answer |
| --- | --- |
| shinri @ slice 55 | `sat` |
| shinri @ slice 54 (`target/slice54-after/shinri`, i.e. `main`) | `sat` |
| z3 | `unsat` |

The same file under `QF_UFLIA`, `QF_UFBV` and `QF_AUFLIA` headers also
answers `sat` on the after binary. It is pre-existing: it reproduces on the
slice-54 binary and is not caused by this branch.

**get-model symptom.** After the `sat`, `(get-model)` prints
`((define-fun q () Bool @elem0))`: `q` is bound to an abstract element
`@elem0`, which is neither `true` nor `false`, and `@elem0` is not a legal
SMT-LIB term (z3 rejects it when the oracle echoes it back). That is the
visible trace of the unsound `sat`.

**Root cause (from the Task 4 investigation).** Slice 54 purified only
*compound* Bool arguments into `bool!` proxies tied to the term. An *atomic*
non-literal Bool argument (a plain constant) is left as an opaque UF
argument; nothing forces it into `{true, false}`, so `P` may assign three
distinct results to `q`, `true` and `false`.

**Why this slice does not fix it.** Slice 55 has a verdict-neutrality
mandate (Global Constraint: no solving-stage edit; spec §7 criterion 2). A
fix is a solving change that would need its own bench run. Ruling 8: the
slice stays neutral, the defect is recorded here and put first in the queue.

**Consequence for the oracle (Ruling 8).** `bool_arg_oracle` excludes from
its z3 assertions every `(term value)` pair whose value starts with `@`. It
counts them and prints them as `n_abstract`, and it still requires 0 z3
rejections and `n_valued > 0`. Counts are in *Gates*. Pairs excluded this
way are *not* checked against z3; they are exactly the abstract-element
values of this defect.

If the user wants the soundness fix inside slice 55, the branch needs an
extra solving-stage task plus a bench re-run (the Ruling 8 "if wrong" cost).

## Commands

```bash
mise run ci
cargo nextest run -p shinri-solver --features oracle \
  -E 'binary(bool_arg_oracle) | binary(qfdt_oracle) | test(differential_qf_uflia_compound_args)'

cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice55-after && cp target/release/shinri target/slice55-after/shinri
md5sum target/slice55-after/shinri | tee target/slice55-after/md5.txt
date -u +%FT%TZ > target/slice55-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_UF,QF_DT,QF_UFLIA,QF_UFLRA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice55-after/shinri --run-id slice55 \
  > target/slice55-after/run.log 2>&1; date -u +%FT%TZ > target/slice55-after/finished.txt' &
BENCH_RUN_ID=slice55 mise run bench-report
```

Verdict comparison: a scratch script (not committed) joined
`bench/results/slice54/results.jsonl` and `bench/results/slice55/results.jsonl`
by `path` (key sets identical, 18,146 each) and counted
`(logic, base verdict, after verdict)` where the two differ. Re-runs:
each changed path, 3× per binary, `timeout 25 prlimit --as=3 GiB`
`taskset -c 12-23 <binary> bench/corpus/<path>`, first `sat|unsat|unknown`
line kept, 6 paths in parallel.

## Runs

| run | solver | md5 | started | finished | rows |
| --- | --- | --- | --- | --- | ---: |
| `bench/results/slice54/` (base, reused) | `target/slice54-after/shinri` (built at `6212fa5`) | `579f17b300bff4feec82b11bc8371fd3` | 2026-10-02T14:10Z | (slice-54 report) | 18,146 |
| `bench/results/slice55/` (after) | `target/slice55-after/shinri` (built at `1a9db04`) | `6a753b2e1c088e0eefefc0a5ae4b1b38` | 2026-10-02T18:34:35Z | 2026-10-02T20:29:06Z | 18,146 |

Both runs: `--timeout 20 --mem-mb 3072 --jobs 6`, logics QF_UF, QF_DT,
QF_UFLIA, QF_UFLRA. (Runs are git-ignored.)

## Success criteria (spec §7)

| # | Criterion | Result | Evidence |
| --- | --- | --- | --- |
| 1 | e1–e7 pass; at HEAD e1–e5 and e7 fail | PASS | tasks 2–3 reports (`.superpowers/sdd/…/task-{2,3}-report.md`); e1 observed `?` for `(+ a 1)` |
| 2 | 0 rows change verdict (operationalised by Ruling 3: re-run 3×, only reproducible differences count) | PASS | 65 changed rows, all `timeout`/`oom` resource flips; 0 `* → wrong`; 0 reproducible answer differences between the binaries (*Verdict comparison*) |
| 3 | Oracle: 0 disagreements, non-zero count | PASS | 22 tests discovered, 22 passed; per-family counts in *Gates* |
| 4 | `mise run ci` green, `cargo fmt --all` clean | PASS | 1,676 tests run, 1,676 passed (10 slow), 7 skipped; the ci task finished in 524.7 s |

## Per-logic matrix (after run)

| logic | total | correct | wrong | parse-error | oom | timeout | unknown |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_DT | 8700 | 8106 | 0 | 0 | 0 | 583 | 11 |
| QF_UF | 7503 | 7060 | 0 | 34 | 0 | 409 | 0 |
| QF_UFLIA | 659 | 143 | 0 | 0 | 7 | 492 | 17 |
| QF_UFLRA | 1284 | 44 | 0 | 1229 | 7 | 4 | 0 |
| all | 18146 | 15353 | 0 | 1263 | 14 | 1488 | 28 |

Base (slice 54), all rows: correct 15,330; timeout 1,509; parse-error 1,263;
`unknown:theory-refused` 17; oom 16; `unknown:sat-budget` 11; wrong 0.

## Verdict comparison

Changed rows (logic, base → after, count):

| logic | base → after | rows |
| --- | --- | ---: |
| QF_DT | timeout → correct | 1 |
| QF_UF | correct → timeout | 16 |
| QF_UF | timeout → correct | 39 |
| QF_UFLIA | correct → timeout | 3 |
| QF_UFLIA | timeout → correct | 2 |
| QF_UFLIA | timeout → oom | 1 |
| QF_UFLRA | oom → timeout | 3 |
| total | | 65 |

Net: correct +23, timeout −21, oom −2.

Re-runs (3× each, both binaries; 65 rows):

- 49 rows give the same single answer on all six runs (3 per binary).
  (Where it is `unsat`/`sat` the row was a bench-time flip; where it is no
  answer in 25 s, a resource-limit row.)
- 16 rows, all QF_UF `QG-classification/qg5/gensys_icl*` (`icl152`, `578`,
  `585`, `609`, `611`, `616`–`619`, `630`, `641`, `722`, `764`, `776`, `828`,
  `829`), give a mix of `unsat` and "no answer within 25 s" across their 3
  runs, on one or both binaries; 14 (row, binary) pairs flip within a single binary
  (for example `icl611` on the base, `icl152`/`icl578` on the after).
  They are the slice-54 QG-classification rows sitting on the 20 s limit
  (the same family as slice 54's "4 `correct → timeout` rows"). The only
  value any run produced other than "no answer" was `unsat`, the correct
  verdict; no run on either binary produced `sat` or any other answer.
- Therefore: no reproducible verdict difference; none of the changed rows
  is a defect of this slice.

Raw re-run lines are kept in the session scratchpad, not committed.

## What changed versus the spec

1. **Negative-numeral printing (spec §3.1, §6.2) was dropped** (Ruling 1).
   The parser never builds a negative constant from source: `(- 3)` is read as
   `Neg`, which already prints as `(- 3)`. If a negative `ConstVal` ever
   reaches the printer by simplification, the echo would be a bare negative
   literal (cosmetic, not a verdict).
2. **Bench base reused.** The base is the slice-54 bench run
   (`bench/results/slice54/`, binary `target/slice54-after/shinri`, built at
   `6212fa5`), not a fresh run at the spec's `a0d0fe9`. The slice is
   post-solve, so the slice-54 binary is the right comparison, and the same
   four logics, timeout, memory and jobs were used.
3. **Task 3 Step 1 proxy-value finding.** `bool!0` is in `internal_vals`
   (its value is `false`), so no extra loop for `bool!` proxies was
   needed and none was added.
4. **`e1` prints `?`.** The slice has no evaluator (spec §2), so the
   built-in application `(+ a 1)` echoes as `(((+ a 1) ?))`; the plan's
   test accepts `1` or `?` (Ruling 5) and `?` is what is observed. The V2
   evaluator is queued.
5. **Tester printing (Ruling 6, Task 1 deviation).** The plan assumed the
   legacy `is-C` spelling. Shinri's parser rejects `(is-mk v)`: minted
   testers are reserved and never bound. The printer therefore prints a
   tester application as the SMT-LIB 2.6 form `((_ is <quoted ctor>) x)`
   (`DtRole::Tester`), and the parser is unchanged (threat-model surface).
6. **Datatype constructor names in values are quoted (final-review fix).**
   `render_value_inner` in `shinri-dt` printed the constructor name raw, so
   `|mk a|` came out as `(mk a 0)`. It now goes through `quote_symbol`
   (output-only; probe `e5_quoted_datatype_constructor_value`).
6. **Ruling 7.** The "grep `orig_ite|eliminated_ite_vals` prints nothing"
   check is satisfied except for two history doc comments the brief itself
   required (`lib.rs:95`, `word_norm.rs:44`).
7. **Ruling 8, oracle `n_abstract`.** See *Defect found*.
8. **Ruling 4.** Branch not pushed, no PR opened; that happens at the
   finishing step with user consent.

## Gates

- `mise run ci`: green. 1,676 tests run, 1,676 passed (10 slow), 7 skipped,
  524.7 s; secrets scan clean (`no leaks found`). Slow tests are the
  `shinri-fp` float32 suites (up to 507 s, existing; the blocking tier
  budget is per AGENTS.md and untouched by this slice).
- Oracle gate (`--features oracle`):
  `binary(bool_arg_oracle) | binary(qfdt_oracle) | test(differential_qf_uflia_compound_args)`:
  **22 tests discovered, 22 passed** (non-zero).
- Oracle value-echo counts (Task 4; disagreements / n_valued / n_abstract):
  DT 0/269/8, UFLIA 0/384/21, UFLRA 0/385/12. Before-evidence at `a0d0fe9`:
  2 of 3 families fail on the `t0` echo.
- `cargo clippy --workspace --all-targets --features oracle` reports 18
  errors in `qfs_differential`. They predate this branch (Task 4's diff
  touches only `bool_arg_oracle.rs`), are outside the gate
  (`mise run lint` does not use `--features oracle`) and were not fixed.

## Queued for the next slice

Ordered. Items 1–3 are new from slice 55; the rest are carried.

1. **Wrong `sat`: a Bool constant as a UF argument (soundness; first).**
   Reproducer in *Defect found* above (`(P q)`, `(not (P true))`,
   `(not (P false))`: `sat` vs z3 `unsat`; QF_UF, QF_UFLIA, QF_UFBV,
   QF_AUFLIA). Tie the Bool constant to true/false, for example by
   extending the slice-54 purification to atomic non-literal Bool
   arguments. Then drop the oracle's `n_abstract` exclusion (Ruling 8) and
   re-check that `get-model` prints `true`/`false` for `q`. Needs its own
   bench run.
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
- **No corpus row exercises the fix.** Only 5 local files mint a proxy, and
  they were already `correct`. The slice's evidence is the probes and the
  oracle. A wider corpus (e.g. QF_AUFLIA / UFDT logics) would be needed for
  a bench-level signal.

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

- Spec: `docs/superpowers/specs/2026-10-02-shinri-slice55-get-value-echo-remap-design.md`
  (§7 criteria, §9 queue, §11 measured outcomes).
- Plan: `docs/superpowers/plans/2026-10-02-shinri-slice55-get-value-echo-remap.md`.
- Slice-54 report: `docs/superpowers/research/2026-10-02-smtlib-2024-slice54-uf-bool-arg-report.md`.
- Commits: `3a72724`, `1f2db78` (printer), `1e9c003`, `3ff5f16`, `100ab7e`
  (echo, tester printing, remap), `1a9db04` (oracle).
- Runs (git-ignored): `bench/results/slice55/` (after), `bench/results/slice54/` (base).
