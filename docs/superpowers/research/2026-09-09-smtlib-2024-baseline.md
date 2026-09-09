# SMT-LIB 2024 baseline — shinri @ 8de004d44944

Run-id `baseline-8de004d44944`, `mise run bench-run` with timeout 20 s / 3072 MB /
6 jobs on the devpod (cgroup cpu.max `800000 100000`, memory.max 34359738368 =
32 GiB). Started 2026-09-08T13:02:55Z, last result row written
2026-09-09T04:23Z — 257,671 instances over all 15 QF logics in the manifest,
about 15 h 20 m wall-clock. Reproduce with the same sha and
`bench/manifest.toml`.

A companion re-run, run-id `rerun-0fca46476479` (shinri sha `0fca46476479`,
same limits, started 2026-09-09T04:24:23Z), re-executes the 48,398 rows that
the baseline classified `oom` or `parse-error` under the final classifier. It
is the source in this document for parse-error diagnostics and for the
panic/oom split; the baseline's own `parse-error:-` bucket carries no
diagnostic because that field landed after the baseline run had started.

Both runs need `mise run bench-fetch` first, which downloads and verifies the
Zenodo archives and extracts them into `bench/corpus/`. The baseline then
reproduces with `BENCH_RUN_ID=baseline-8de004d44944 mise run bench-run`. There
is no mise task for `rerun`; the re-run reproduces with the binary directly:

```
target/release/shinri-bench rerun bench/results/baseline-8de004d44944/results.jsonl \
  --verdict oom,parse-error --timeout 20 --mem-mb 3072 --jobs 6 \
  --run-id rerun-0fca46476479
```

`BENCH_RUN_ID=<run-id> mise run bench-report` renders that run's `report.md`
from its `results.jsonl`.
The corpus is pinned by md5 per archive in `bench/manifest.toml` (Zenodo
record `10.5281/zenodo.11061097`, SMT-LIB release 2024, non-incremental). The
baseline's fixture pins no `solver_md5` — that field landed with the re-run —
so the baseline's binary is pinned only by its sha. Every instance the solver
answered reproduces with `target/release/shinri --stats <file>`; the oracles
with `z3 <file>` and `cvc5 --lang smt2 <file>`.

Both runs' `report.md` are committed beside this document as
`2026-09-09-smtlib-2024-baseline-report.md` and
`2026-09-09-smtlib-2024-rerun-report.md`; every `Cites` pointer below names
one of those two files and a section inside it.

## Headline

- shinri returns a decided answer on 126,007 of 257,671 rows (48.9%): 123,894
  `correct`, 742 `wrong` and 1,371 `unverified`. The correct-rate is 48.1%,
  and 742 of the answers are unsound. There are 0 `malformed` rows. The rows
  with no answer split into 66,416 `unknown` (a fence fired), 44,009
  `parse-error`, 11,058 `timeout`, 8,082 `panic` and 2,099 `oom`.
- There are 742 soundness failures. 741 are a decided `sat` where the
  benchmark and/or an oracle says `unsat`; one is the reverse direction
  (`QF_S/20230329-automatark-lu/instance10773.smt2`, `:status sat`, shinri
  `unsat`, z3 `sat`). Two clusters carry 687 of them: QF_ABV 359 and QF_DT
  328.
- `status-suspect` is 0. No row in the corpus had shinri contradict `:status`
  with both oracles siding with shinri.
- The baseline's `panic` and `oom` columns are superseded by the re-run. The
  true split is 8,082 `panic` and 2,099 `oom`; see "Panic and oom, corrected"
  below.
- The single largest gap is a parser gap, not a theory gap:
  `unsupported command: define-sort` accounts for 39,994 rows, all QF_FP, and
  by itself gates 99% of that logic (39,994 of 40,407).
- The second largest gap is the string stack: two fences,
  `unknown:str-indexof-replace` (26,363) and `unknown:str-predicate-polarity`
  (16,016), account for 42,379 rows, almost entirely QF_SLIA.
- QF_AX is 551 of 551 `unknown` on `theory-refused` — an entire logic with no
  implementation behind it.
- Worst decided-rates: QF_AX 0.0%, QF_FP 0.5%, QF_UFLRA 3.4%, QF_UFLIA 15.6%.
  Best: QF_BVFP 98.7%, QF_UF 94.7%, QF_DT 90.2%.

## Per-logic matrix

| logic | total | correct | wrong | status-suspect | parse-error | panic | oom | timeout | unknown | unverified | malformed | decided% | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_ABV | 15148 | 8454 | 359 | 0 | 26 | 5787 | 98 | 361 | 62 | 1 | 0 | 55.8 | 12 | 173 |
| QF_AUFBV | 75 | 18 | 0 | 0 | 13 | 5 | 6 | 19 | 14 | 0 | 0 | 24.0 | 195 | 783 |
| QF_AX | 551 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 551 | 0 | 0 | 0.0 | n/a | n/a |
| QF_BV | 46191 | 35840 | 0 | 0 | 1401 | 0 | 3597 | 5351 | 0 | 2 | 0 | 77.6 | 84 | 3394 |
| QF_BVFP | 17249 | 17032 | 1 | 0 | 0 | 0 | 0 | 215 | 0 | 1 | 0 | 98.7 | 15 | 51 |
| QF_DT | 8700 | 7849 | 328 | 0 | 0 | 0 | 0 | 507 | 11 | 5 | 0 | 90.2 | 6 | 11 |
| QF_FP | 40407 | 218 | 0 | 0 | 39998 | 0 | 15 | 173 | 0 | 3 | 0 | 0.5 | 51 | 2091 |
| QF_LIA | 13306 | 4787 | 2 | 0 | 0 | 0 | 576 | 3174 | 4764 | 3 | 0 | 36.0 | 68 | 2227 |
| QF_LRA | 1753 | 411 | 2 | 0 | 1063 | 0 | 2 | 181 | 94 | 0 | 0 | 23.4 | 4 | 1413 |
| QF_S | 18940 | 16025 | 2 | 0 | 0 | 0 | 0 | 8 | 2809 | 96 | 0 | 84.6 | 5 | 19 |
| QF_SLIA | 84395 | 24799 | 37 | 0 | 195 | 0 | 0 | 41 | 58063 | 1260 | 0 | 29.4 | 4 | 16 |
| QF_UF | 7503 | 7106 | 0 | 0 | 34 | 0 | 0 | 363 | 0 | 0 | 0 | 94.7 | 71 | 4349 |
| QF_UFBV | 1510 | 1208 | 0 | 0 | 50 | 0 | 80 | 141 | 31 | 0 | 0 | 80.0 | 101 | 664 |
| QF_UFLIA | 659 | 103 | 11 | 0 | 0 | 0 | 5 | 523 | 17 | 0 | 0 | 15.6 | 2497 | 13196 |
| QF_UFLRA | 1284 | 44 | 0 | 0 | 1229 | 0 | 10 | 1 | 0 | 0 | 0 | 3.4 | 4 | 76 |
| all | 257671 | 123894 | 742 | 0 | 44009 | 5792 | 4389 | 11058 | 66416 | 1371 | 0 | 48.1 | 11 | 675 |

Four logics are effectively unsolved and each for a different single reason:
QF_AX (0.0%) refuses the theory outright, QF_FP (0.5%) dies in the parser on
`define-sort`, QF_UFLRA (3.4%) dies in the parser on two sort-checking
diagnostics, and QF_UFLIA (15.6%) times out (523 of 659 rows). Note that the
`panic` and `oom` columns above are the baseline classifier's; the corrected
figures are in the next section.

### Panic and oom, corrected

The baseline binary derived no exit code when a child died from a signal, so
every signal death landed in the `oom` bucket by the classifier's
`rc == None` rule. The fix has two halves. The first recovers the signal and
reports it as `rc = 128 + signal`; every one of the 4,389 rows is a SIGABRT,
so they all come back as `rc 134`. The second adds a
`has overflowed its stack` / `fatal runtime error` clause to the `Panic` rule,
which runs before the `Oom` rule.

The second half is the one that produces the split, and the first half alone
would not have. With the signal recovery but the old `Panic` rule, all 4,389
rows carry `rc 134` and no `panicked at` line, so the `Oom` rule's
`rc == Some(134)` arm catches every one of them and the 2,290 stack overflows
stay misfiled as memory pressure. The two groups are told apart by stderr, not
by exit code: the 2,290 carry `thread 'main' (N) has overflowed its stack` and
`fatal runtime error: stack overflow`, and the 2,099 carry
`memory allocation of N bytes failed`. Both halves are in the merged code, and
`rerun-0fca46476479` re-classifies the affected rows.

Of the 4,389 rows the baseline called `oom`:

| re-classified as | count | logics |
| --- | ---: | --- |
| `panic` (Rust stack overflow) | 2290 | QF_BV 2180, QF_LIA 57, QF_ABV 53 |
| `oom` (genuine allocation failure) | 2099 | QF_BV 1417, QF_LIA 519, QF_UFBV 80, QF_ABV 45, QF_FP 15, QF_UFLRA 10, QF_AUFBV 6, QF_UFLIA 5, QF_LRA 2 |

Corrected corpus totals are therefore **8,082 `panic`** (5,792 from
the blast `unreachable!`, 2,290 stack overflows) and **2,099 `oom`**. Read the
per-logic matrix's `panic`/`oom` columns with that correction applied; every
other column is unaffected.

## Ranked gaps (by count)

Every non-`correct` verdict bucketed and sorted by count, per spec §9.2. The
`parse-error` rows and the `panic`/`oom` split come from
`2026-09-09-smtlib-2024-rerun-report.md › ## Ranked gaps`, because the
baseline predates the parse-error diagnostic and the signal-aware exit code;
every other bucket comes from
`2026-09-09-smtlib-2024-baseline-report.md › ## Ranked gaps`. Each report also
lists three cheapest reproducers per bucket.

| bucket | count | logics | source |
| --- | ---: | --- | --- |
| `parse-error:unsupported command: define-sort` | 39994 | QF_FP 39994 | re-run |
| `unknown:str-indexof-replace` | 26363 | QF_S 80, QF_SLIA 26283 | baseline |
| `unknown:str-predicate-polarity` | 16016 | QF_SLIA 16016 | baseline |
| `timeout` | 11058 | QF_ABV 361, QF_AUFBV 19, QF_BV 5351, QF_BVFP 215, QF_DT 507, QF_FP 173, QF_LIA 3174, QF_LRA 181, QF_S 8, QF_SLIA 41, QF_UF 363, QF_UFBV 141, QF_UFLIA 523, QF_UFLRA 1 | baseline |
| `panic:crates/shinri-bv/src/blast/mod.rs: internal error: entered unreachable code: non-BV builtin reached blast_word` | 5792 | QF_ABV 5787, QF_AUFBV 5 | baseline |
| `unknown:sat-budget` | 5548 | QF_DT 11, QF_S 1353, QF_SLIA 4184 | baseline |
| `unknown:theory-refused` | 5425 | QF_AX 551, QF_LIA 4764, QF_LRA 58, QF_SLIA 35, QF_UFLIA 17 | baseline |
| `unknown:str-model-rejected` | 4290 | QF_S 1033, QF_SLIA 3257 | baseline |
| `unknown:str-substr-at` | 3359 | QF_SLIA 3359 | baseline |
| `unknown:reglan-decl` | 3287 | QF_SLIA 3287 | baseline |
| `panic:thread 'main' (N) has overflowed its stack` | 2290 | QF_ABV 53, QF_BV 2180, QF_LIA 57 | re-run |
| `oom` | 2099 | QF_ABV 45, QF_AUFBV 6, QF_BV 1417, QF_FP 15, QF_LIA 519, QF_LRA 2, QF_UFBV 80, QF_UFLIA 5, QF_UFLRA 10 | re-run |
| `parse-error:sort error: NotApplicable` | 1858 | QF_LRA 762, QF_UFLRA 1096 | re-run |
| `unknown:str-int-conv` | 1616 | QF_SLIA 1616 | baseline |
| `unverified` | 1371 | QF_ABV 1, QF_BV 2, QF_BVFP 1, QF_DT 5, QF_FP 3, QF_LIA 3, QF_S 96, QF_SLIA 1260 | baseline |
| ``parse-error:invalid BV numeral suffix `N` `` | 1129 | QF_ABV 22, QF_AUFBV 12, QF_BV 1045, QF_UFBV 50 | re-run |
| `parse-error:sort error: Mismatch { expected: SortId(N), found: SortId(N) }` | 434 | QF_LRA 301, QF_UFLRA 133 | re-run |
| `unknown:str-regex` | 369 | QF_S 343, QF_SLIA 26 | baseline |
| `parse-error:unknown operator bvcomp` | 237 | QF_ABV 1, QF_BV 236 | re-run |
| `parse-error:sort error: Arity { expected: N, found: N }` | 125 | QF_ABV 3, QF_AUFBV 1, QF_BV 117, QF_FP 4 | re-run |
| `parse-error:unknown operator str.replace_re` | 98 | QF_SLIA 98 | re-run |
| `parse-error:unknown operator str.replace_re_all` | 97 | QF_SLIA 97 | re-run |
| `unknown:abv-fenced` | 62 | QF_ABV 62 | baseline |
| `unknown:theory-lira` | 36 | QF_LRA 36 | baseline |
| `parse-error:unknown operator !` | 34 | QF_UF 34 | re-run |
| `unknown:bv-uf-budget` | 23 | QF_UFBV 23 | baseline |
| `unknown:abv-uf-args` | 13 | QF_AUFBV 13 | baseline |
| `unknown:bv-uf-args` | 9 | QF_AUFBV 1, QF_UFBV 8 | baseline |
| `parse-error:(error S` | 3 | QF_BV 3 | re-run |

The buckets reconcile with the per-logic matrix: `parse-error` sums to 44,009,
`unknown` to 66,416, `panic` to 8,082, `timeout` to 11,058, `oom` to 2,099 and
`unverified` to 1,371 — 133,035 rows, which with 123,894 `correct` and 742
`wrong` is the corpus's 257,671.

Buckets below 100 rows are listed here for completeness and are **not** filed
as slices below. There are seven of them — `unknown:abv-fenced` 62,
`unknown:theory-lira` 36, `parse-error:unknown operator !` 34,
`unknown:bv-uf-budget` 23, `unknown:abv-uf-args` 13, `unknown:bv-uf-args` 9
and `parse-error:(error S` 3 — 180 rows in total, 0.07% of the corpus, and
none of them gates a logic. The one exception to the cut is
`str.replace_re` (98) and `str.replace_re_all` (97): they are filed as a
single 195-row slice below because they are a prerequisite for the regex
work, not because either count clears the bar on its own. The five `unknown`
fences among those seven are where the ABV engine (`abv-fenced`), the LIRA
path (`theory-lira`) and the BV/array UF handling (`bv-uf-budget`,
`abv-uf-args`, `bv-uf-args`) hit their own limits, at a scale that does not
yet justify a slice.

## Next slices (spec §5 priority order)

Priority is fixed by spec §5: `Wrong` > `Panic` > `ParseError` > `Unknown`
(by count) > `Timeout`/`Oom`.

1. **QF_ABV wrong answers — 359 instances, QF_ABV.**
   Cites `2026-09-09-smtlib-2024-baseline-report.md ›
   ## Wrong answers` (all 359 QF_ABV rows). Every one is `:status unsat`
   answered `sat`; 297 have an in-run z3 `unsat` on record and 62 rest on the
   hand adjudication below. Families: `dwp_formulas` 283, `brummayerbiere` 69,
   `brummayerbiere2` 5, `calc2` 2.
   Cheapest reproducer:
   `target/release/shinri QF_ABV/brummayerbiere/bubsort002un.smt2` (1,260
   bytes, expects `unsat`, z3 confirms `unsat` in-run).
   Proposed slice: *"QF_ABV wrong-sat: the array/BV engine reports a model
   that does not satisfy the array axioms"* — bisect on the
   `dwp_formulas`/`brummayerbiere` shape, add a model-check gate on the
   `abv` path in the same spirit as `str-model-rejected`.

2. **QF_DT wrong answers — 328 instances, QF_DT.**
   Cites `2026-09-09-smtlib-2024-baseline-report.md ›
   ## Wrong answers` (QF_DT rows). All `:status unsat` answered `sat`.
   Families: `20172804-Barrett` 166 (all with in-run z3 `unsat`) and
   `20230720-blocksworld` 162 (134 with in-run z3 `unsat`; the 28 that had z3
   `timeout` in-run were hand-re-run at 300 s against both oracles on
   2026-09-09 and 27 of them came back `unsat`, 1 undecided). The cluster is
   independently confirmed, not `:status`-only: 327 of the 328 rows carry a
   decided oracle `unsat`.
   Cheapest reproducer:
   `target/release/shinri QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l30072.cvc.smt2`
   (966 bytes).
   Proposed slice: *"QF_DT wrong-sat: datatype constructor/selector
   disequality is not enforced"* — the two families are distinct shapes
   (Barrett term-level datatypes vs. blocksworld BMC), so scope the slice to
   Barrett first and re-measure blocksworld.

3. **The remaining 55 wrong answers — QF_SLIA 37, QF_UFLIA 11, QF_S 2,
   QF_LIA 2, QF_LRA 2, QF_BVFP 1.**
   Cites `2026-09-09-smtlib-2024-baseline-report.md ›
   ## Wrong answers` (non-ABV/DT rows). Four distinct causes, all
   small, all soundness:
   - QF_SLIA 37 (`20230329-denghang` 35, `20190311-str-small-rw-Noetzli` 2) —
     `:status unknown`, shinri `sat`, z3 `unsat`. Reproducer:
     `QF_SLIA/20230329-denghang/instance55060.smt2` (1,057 bytes).
   - QF_UFLIA 11 (`mathsat/Wisa` 9, `wisas` 2) — reproducer:
     `QF_UFLIA/mathsat/Wisa/xs-05-08-4-2-5-4.smt2` (3,627 bytes).
   - QF_S 2, including the corpus's only wrong `unsat`:
     `QF_S/20230329-automatark-lu/instance10773.smt2` (2,322 bytes,
     `:status sat`, shinri `unsat`, z3 `sat`).
   - QF_LIA 2 (`calypto`), QF_LRA 2 (`keymaera`), QF_BVFP 1 (`ramalho`).
   Proposed slice: *"Four small wrong-answer clusters: triage QF_SLIA
   denghang, QF_UFLIA Wisa, the QF_S wrong-unsat, and the arithmetic pair"* —
   one slice, four independent repros; the QF_S wrong-`unsat` is the highest
   value single row because it is the only failure in the refutation
   direction.

4. **Panic: `non-BV builtin reached blast_word` — 5,792 instances,
   QF_ABV 5,787 / QF_AUFBV 5.**
   Cites `2026-09-09-smtlib-2024-baseline-report.md › ## Ranked gaps ›
   panic:crates/shinri-bv/src/blast/mod.rs: internal error: entered
   unreachable code: non-BV builtin reached blast_word — 5792`.
   Cheapest reproducer:
   `target/release/shinri QF_ABV/bench_ab/b334test0001.smt2` (722 bytes).
   Proposed slice: *"Blaster: reach a non-BV builtin in `blast_word` without
   an `unreachable!` — either lower it or return `Unknown` with a fence tag"*
   — this is 38% of QF_ABV and the largest crash class in the corpus.

5. **Panic: stack overflow — 2,290 instances, QF_BV 2,180 / QF_LIA 57 /
   QF_ABV 53.**
   Cites `2026-09-09-smtlib-2024-rerun-report.md › ## Ranked gaps ›
   panic:thread 'main' (N) has overflowed its stack — 2290`.
   Cheapest reproducer:
   `target/release/shinri QF_ABV/bmc-arrays/bf8.smt2` (493,591 bytes); the
   smallest QF_BV example is `QF_BV/bmc-bv/ex30.smt2` (565,248 bytes).
   All examples are large BMC files, so the recursion depth tracks term depth.
   Proposed slice: *"Make term traversal iterative (or bound it) so deep BMC
   formulas do not overflow the stack"* — likely a shared explicit-stack
   rewrite in the term walker rather than a per-crate fix, since it fires in
   three logics.

6. **`unsupported command: define-sort` — 39,994 instances, all QF_FP.**
   Cites `2026-09-09-smtlib-2024-rerun-report.md › ## Ranked gaps ›
   parse-error:unsupported command: define-sort — 39994`. This is a
   **parser** gap, not an FP-theory gap: the FP engine never runs on these
   files. It alone gates 99% of QF_FP
   (39,994 of 40,407 rows; the logic's decided-rate is 0.5%).
   Cheapest reproducer:
   `target/release/shinri QF_FP/wintersteiger/abs/abs-has-solution-8522.smt2`
   (622 bytes).
   Proposed slice: *"`define-sort`: sort abbreviations in the parser"* —
   highest instances-per-line-of-code ratio in this document by a wide
   margin, and it is the only thing standing between the existing FP engine
   and 40k instances of measurement.

7. **The remaining parse-error buckets — 4,015 instances.**
   All from `2026-09-09-smtlib-2024-rerun-report.md ›
   ## Ranked gaps`. In descending order:

   | bucket | count | logics | cheapest reproducer |
   | --- | ---: | --- | --- |
   | `sort error: NotApplicable` | 1858 | QF_UFLRA 1096, QF_LRA 762 | `QF_LRA/meti-tarski/polypaver/bench-exp-3d/polypaver-bench-exp-3d-chunk-0018.smt2` (769 B) |
   | `invalid BV numeral suffix \`N\`` | 1129 | QF_BV 1045, QF_UFBV 50, QF_ABV 22, QF_AUFBV 12 | `QF_BV/brummayerbiere/bitrev0128.smt2` (3097 B) |
   | `sort error: Mismatch { expected: SortId(N), found: SortId(N) }` | 434 | QF_LRA 301, QF_UFLRA 133 | `QF_UFLRA/FFT/smtlib.624916.smt2` (600 B) |
   | `unknown operator bvcomp` | 237 | QF_BV 236, QF_ABV 1 | `QF_BV/2020-Weber/extensions.smt2` (4147 B) |
   | `sort error: Arity { expected: N, found: N }` | 125 | QF_BV 117, QF_FP 4, QF_ABV 3, QF_AUFBV 1 | `QF_FP/schanda/spark/discrete.smt2` (428 B) |
   | `unknown operator str.replace_re` | 98 | QF_SLIA 98 | `QF_SLIA/20230403-webapp/lan-rep/lan_replace44.smt2` (1321 B) |
   | `unknown operator str.replace_re_all` | 97 | QF_SLIA 97 | `QF_SLIA/20230403-webapp/lan-rep-all/lan_replace_all44.smt2` (1325 B) |
   | `unknown operator !` | 34 | QF_UF 34 | `QF_UF/20170829-Rodin/smt4027072204816894856.smt2` (459 B) |
   | `(error S` | 3 | QF_BV 3 | `QF_BV/brummayerbiere/bitrev2048.smt2` (29049 B) |

   The two `sort error` buckets (2,292 rows) are the QF_LRA/QF_UFLRA story —
   together they are why QF_UFLRA sits at 3.4% decided. `bvcomp` and the BV
   numeral suffix are the QF_BV story: 1,281 of the 1,366 rows in those two
   buckets are QF_BV. `unknown operator !` is the SMT-LIB annotation form `(! t :named n)`, which the parser should
   accept and strip.
   Proposed slices, in the order the counts suggest: *"Real/Int sort
   checking: fix `NotApplicable` and `Mismatch` on meti-tarski and FFT"*;
   *"BV literals and `bvcomp`: accept `bvN` numerals with an index and lower
   `bvcomp`"*; *"Parse `(! t :attr)` annotations"*; *"`str.replace_re` /
   `str.replace_re_all`"* (195 rows, and a prerequisite for the regex work in
   slice 8 below).

8. **String fences — 55,300 `unknown` rows across QF_S and QF_SLIA.**
   Cites `2026-09-09-smtlib-2024-baseline-report.md ›
   ## Ranked gaps`. Ordered by count:

   | fence tag | count | logics |
   | --- | ---: | --- |
   | `unknown:str-indexof-replace` | 26363 | QF_SLIA 26283, QF_S 80 |
   | `unknown:str-predicate-polarity` | 16016 | QF_SLIA 16016 |
   | `unknown:str-model-rejected` | 4290 | QF_SLIA 3257, QF_S 1033 |
   | `unknown:str-substr-at` | 3359 | QF_SLIA 3359 |
   | `unknown:reglan-decl` | 3287 | QF_SLIA 3287 |
   | `unknown:str-int-conv` | 1616 | QF_SLIA 1616 |
   | `unknown:str-regex` | 369 | QF_S 343, QF_SLIA 26 |

   The top two alone are 42,379 rows and 73% of QF_SLIA's 58,063 `unknown`s.
   Cheapest reproducers:
   `QF_SLIA/2019-full_str_int/py-conbyte_cvc4/lib_int-distutils_get_build_version/8.smt2`
   (479 B, `str-indexof-replace`) and
   `QF_SLIA/2019-full_str_int/py-conbyte_cvc4/leetcode_int-validIPAddress/13.smt2`
   (456 B, `str-predicate-polarity`); both are in the same generated family,
   so one slice may move both counts.
   Note that `str-model-rejected` (4,290) is a *different* kind of row: the
   solver produced a model and then rejected it, i.e. the reduction is
   incomplete rather than absent. Also note the fences that fired **zero**
   times corpus-wide: `str-fenced`, `str-code-conv`, and `str-order` — the
   slice-31 two-free-variable `str.<` research effort has no measured demand
   in SMT-LIB 2024.
   Proposed slices: *"`str.indexof` / `str.replace` reduction"* (26,363);
   *"String predicate polarity: handle the negative occurrences the rewriter
   currently refuses"* (16,016); *"`str.substr` / `str.at` unfolding"*
   (3,359); *"`RegLan` declarations"* (3,287); *"`str.to_int` /
   `str.from_int`"* (1,616).

9. **`unknown:sat-budget` — 5,548 instances, QF_SLIA 4,184 / QF_S 1,353 /
   QF_DT 11.**
   Cites `2026-09-09-smtlib-2024-baseline-report.md ›
   ## Ranked gaps › unknown:sat-budget — 5548`. These are rows where the SAT
   search hit its budget rather than a missing feature, so they are a tuning
   target, not a modelling one.
   Cheapest reproducer:
   `QF_SLIA/20190311-str-small-rw-Noetzli/str-pred-small-rw/str-pred-small-rw_135.smt2`
   (731 bytes).
   Proposed slice: *"Measure and raise the string `sat-budget`: how many of
   the 5,548 decide at 2×/10× budget?"* — a measurement slice first; the
   answer decides whether this is a budget knob or a propagation bug.

10. **`unknown:theory-refused` — 5,425 instances, QF_LIA 4,764 / QF_AX 551 /
    QF_LRA 58 / QF_SLIA 35 / QF_UFLIA 17.**
    Cites `2026-09-09-smtlib-2024-baseline-report.md ›
    ## Ranked gaps › unknown:theory-refused — 5425`.
    QF_AX is 551 of 551 — an entire logic with no implementation; every QF_AX
    row in the corpus is this one fence. The QF_LIA share (4,764) is the
    larger count but a different cause: integer problems the linear-arithmetic
    front end declines.
    Cheapest reproducer for the QF_LIA share:
    `QF_LIA/pb2010/normalized-1096.cudf.paranoid.smt2` (316 bytes).
    Proposed slices: *"QF_AX: an extensional-array decision procedure"* (551
    rows, a whole logic, and the only way QF_AX ever leaves 0.0%); and
    *"QF_LIA `theory-refused`: characterise and shrink the refusal guard"*
    (4,764 rows, 36% of QF_LIA).

11. **Timeout and oom — 11,058 `timeout` and 2,099 corrected `oom`.**
    Cites `2026-09-09-smtlib-2024-baseline-report.md ›
    ## Perf tail › timeout+oom by logic` and the same file's
    `## Ranked gaps › timeout — 11058` and `oom — 4389` (the latter
    superseded by `2026-09-09-smtlib-2024-rerun-report.md ›
    ## Ranked gaps › oom — 2099`).
    Worst logics by combined count: QF_BV 8,948 of 46,191 rows, QF_LIA 3,750
    of 13,306, QF_UFLIA 528 of 659 (80% of the logic), QF_DT 507, QF_ABV 459.
    Cheapest timeout reproducer: `QF_LIA/check/int_incompleteness1.smt2`
    (342 bytes) — a small file that times out is a completeness problem, not
    a size problem. Cheapest oom reproducer:
    `QF_BV/brummayerbiere4/unconstrained10.smt2` (631 bytes).
    Proposed slices: *"QF_UFLIA perf: 80% of the logic exceeds 20 s"* (the
    highest-density perf failure, and the logic already has the corpus's
    worst median at 2,497 ms); *"QF_BV small-file oom: the `unconstrained`
    family allocates 4 GiB on a 631-byte input"*.

## Wrong answers

**Evidence standard.** Every one of the 742 `wrong` rows carries the oracle
answer that the run recorded, per spec §5's oracle rule. 652 rows have an
in-run z3 answer that is decided and contradicts shinri. The other 90 have z3
`timeout` at the run's 20 s limit, and all 90 were re-run by hand against both
oracles at a longer budget: the 62 QF_ABV rows at 120 s on 2026-09-08T23:57Z,
the 28 `QF_DT/20230720-blocksworld` rows at 300 s on 2026-09-09T11:15Z.

| group | rows | decided by an oracle, against shinri | undecided by both oracles |
| --- | ---: | ---: | ---: |
| in-run z3 decided | 652 | 652 | 0 |
| QF_ABV hand re-run at 120 s | 62 | 18 | 44 |
| QF_DT hand re-run at 300 s | 28 | 27 | 1 |
| **total** | **742** | **697** | **45** |

All 652 in-run answers are `unsat` except one, the corpus's single wrong
`unsat`, where z3 says `sat`. The QF_ABV 18 break down as 9 from z3 only, 4
from both z3 and cvc5, and 5 from cvc5 only. The QF_DT 27 break down as 7
from both z3 and cvc5 and 20 from z3 only; the single undecided row is
`QF_DT/20230720-blocksworld/blocksworld_from_5_4_17_to_12_6_8_negated_goal_bmc_16.smt2`,
where both oracles time out at 300 s. So 697 of the 742 rows carry a decided
independent solver answer contradicting shinri, and 45 rest on the benchmark's
own `:status unsat` and on nothing else.

Every one of the 742 rows shows `cvc5: -` in
`2026-09-09-smtlib-2024-baseline-report.md › ## Wrong answers`. That is the
adjudication rule, not a missing run: spec §5 consults cvc5 only
when z3 *agrees* with shinri on a `:status` contradiction, which is the
`StatusSuspect` test. A row where z3 contradicts shinri is already `Wrong`, so
cvc5 is never asked in-run. The cvc5 answers above come from the hand re-runs,
not from the run.

Not all 742 rows were reproduced by hand; the counts above are the exact
evidence each group carries. A per-family spot-check of 11 rows is recorded
separately.

| logic | family | rows | evidence |
| --- | --- | ---: | --- |
| QF_ABV | `dwp_formulas` | 283 | 272 in-run z3 `unsat`; 11 z3 `timeout`, hand-adjudicated at 120 s (9 decided `unsat`, 2 undecided) |
| QF_ABV | `brummayerbiere` | 69 | 23 in-run z3 `unsat`; 46 z3 `timeout`, hand-adjudicated (8 decided `unsat`, 38 undecided) |
| QF_ABV | `brummayerbiere2` | 5 | all z3 `timeout` in-run; hand-adjudicated (1 decided `unsat`, 4 undecided) |
| QF_ABV | `calc2` | 2 | in-run z3 `unsat` |
| QF_DT | `20172804-Barrett` | 166 | in-run z3 `unsat` |
| QF_DT | `20230720-blocksworld` | 162 | 134 in-run z3 `unsat`; 28 z3 `timeout`, hand-adjudicated at 300 s (27 decided `unsat`, 1 undecided) |
| QF_SLIA | `20230329-denghang` | 35 | `:status unknown`; in-run z3 `unsat` is the sole evidence |
| QF_UFLIA | `mathsat/Wisa` | 9 | in-run z3 `unsat` |
| QF_SLIA | `20190311-str-small-rw-Noetzli` | 2 | `:status unknown`; in-run z3 `unsat` is the sole evidence |
| QF_UFLIA | `wisas` | 2 | in-run z3 `unsat` |
| QF_S | `20230329-automatark-lu` | 2 | in-run z3 decided (one `unsat`, one `sat`) |
| QF_LIA | `calypto` | 2 | in-run z3 `unsat` |
| QF_LRA | `keymaera` | 2 | in-run z3 `unsat` |
| QF_BVFP | `ramalho/esbmc` | 1 | in-run z3 `unsat` |
| **total** | | **742** | |

Direction: 741 rows are shinri `sat` where the reference is `unsat`; exactly
one is shinri `unsat` where the reference is `sat`
(`QF_S/20230329-automatark-lu/instance10773.smt2`).

### Named smallest reproducers

QF_ABV (`:status unsat`, shinri `sat`):

- `QF_ABV/brummayerbiere/bubsort002un.smt2` (1,260 B) — in-run z3 `unsat`.
- `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_chgrp.i_ring_empty.il.wp.smt2` (1,472 B) — in-run z3 `unsat`.
- `QF_ABV/brummayerbiere/wchains002ue.smt2` (1,421 B) — in-run z3 `unsat`.
- `QF_ABV/brummayerbiere2/countbitstable016.smt2` (11,203 B) — in-run z3 `timeout`; z3 `unsat` at 120 s.
- `QF_ABV/calc2/calc2_sec2_shifter_bmc10.atlas.smt2` (129,767 B) — in-run z3 `unsat`.

QF_DT (`:status unsat`, shinri `sat`):

- `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l30072.cvc.smt2` (966 B).
- `QF_DT/20172804-Barrett/barrett-jsat/tests/v2/v2l20032.cvc.smt2` (1,001 B).
- `QF_DT/20230720-blocksworld/blocksworld_from_1_0_2_to_1_0_2_negated_goal_bmc_1.smt2` (6,049 B).
- `QF_DT/20230720-blocksworld/blocksworld_from_4_0_5_to_8_0_1_negated_goal_bmc_1.smt2` (6,347 B).

Strings and arithmetic:

- `QF_SLIA/20230329-denghang/instance55060.smt2` (1,057 B) — `:status unknown`, shinri `sat`, z3 `unsat`.
- `QF_SLIA/20190311-str-small-rw-Noetzli/str-pred-small-rw/str-pred-small-rw_370.smt2` (735 B) — same shape.
- `QF_S/20230329-automatark-lu/instance10773.smt2` (2,322 B) — the wrong `unsat`.
- `QF_LRA/keymaera/simple_example_2-node2406.smt2` (1,045 B).
- `QF_LIA/calypto/problem-001553.cvc.1.smt2` (6,484 B).
- `QF_UFLIA/mathsat/Wisa/xs-05-08-4-2-5-4.smt2` (3,627 B).
- `QF_BVFP/ramalho/esbmc/Float-no-simp9-main.smt2` (203,638 B).

Each reproduces with `target/release/shinri --stats <file>`, `z3 <file>` and
`cvc5 --lang smt2 <file>` from `bench/corpus/`.

## Perf tail

15,447 rows (6.0% of the corpus) are `timeout` or `oom` under the 20 s / 3 GB
budget. QF_BV carries 8,948 of them and QF_LIA 3,750 — between them 82% of
the perf tail. By density rather than count, QF_UFLIA is the worst logic in
the corpus: 528 of 659 rows (80%) exceed the budget, and its decided rows
have a median of 2,497 ms and a p90 of 13,196 ms, an order of magnitude above
every other logic.

| logic | timeout | oom | timeout+oom | total |
| --- | ---: | ---: | ---: | ---: |
| QF_ABV | 361 | 98 | 459 | 15148 |
| QF_AUFBV | 19 | 6 | 25 | 75 |
| QF_AX | 0 | 0 | 0 | 551 |
| QF_BV | 5351 | 3597 | 8948 | 46191 |
| QF_BVFP | 215 | 0 | 215 | 17249 |
| QF_DT | 507 | 0 | 507 | 8700 |
| QF_FP | 173 | 15 | 188 | 40407 |
| QF_LIA | 3174 | 576 | 3750 | 13306 |
| QF_LRA | 181 | 2 | 183 | 1753 |
| QF_S | 8 | 0 | 8 | 18940 |
| QF_SLIA | 41 | 0 | 41 | 84395 |
| QF_UF | 363 | 0 | 363 | 7503 |
| QF_UFBV | 141 | 80 | 221 | 1510 |
| QF_UFLIA | 523 | 5 | 528 | 659 |
| QF_UFLRA | 1 | 10 | 11 | 1284 |
| all | 11058 | 4389 | 15447 | 257671 |

(The `oom` column here is the baseline classifier's 4,389; 2,290 of those are
stack-overflow panics, not memory pressure. Correcting it does not change
which logics dominate — QF_BV and QF_LIA account for both the panics and the
genuine ooms.)

Size predicts the perf tail almost monotonically. The top decile carries
9,828 of the 15,447 rows and deciles 7–10 carry 14,672 of them; below 5 KB (deciles 1–6) the
tail is 775 rows in total.

| decile | bytes | rows | timeout+oom |
| ---: | --- | ---: | ---: |
| 1 | 240–859 | 25767 | 300 |
| 2 | 859–993 | 25767 | 24 |
| 3 | 993–1300 | 25767 | 47 |
| 4 | 1300–1498 | 25767 | 39 |
| 5 | 1498–2347 | 25767 | 107 |
| 6 | 2347–5009 | 25767 | 258 |
| 7 | 5009–14122 | 25767 | 921 |
| 8 | 14123–33653 | 25767 | 1492 |
| 9 | 33654–99988 | 25767 | 2431 |
| 10 | 99988–2044326719 | 25768 | 9828 |

The first decile's 300 rows are the interesting exception: files under 859
bytes that still exceed the budget are completeness failures, not scale
failures. `QF_LIA/check/int_incompleteness1.smt2` (342 B) and
`QF_BV/brummayerbiere4/unconstrained10.smt2` (631 B) are the two cheapest
entry points into that set.

## Method and caveats

- **Two run-ids.** `baseline-8de004d44944` is the full-corpus run and the
  source of every count in this document except the parse-error diagnostics
  and the panic/oom split. `rerun-0fca46476479` re-executes only the 48,398
  `oom` + `parse-error` rows under the final classifier, because two fields
  landed after the baseline had already started: the parse-error diagnostic
  string (so the baseline's whole 44,009 collapses into a single
  `parse-error:-` bucket) and the `128 + signal` exit-code recovery (so every
  signal death fell into `oom`). The re-run's per-logic matrix shows 0
  decided by construction — it only re-runs rows that were already failures —
  and must not be read as a regression.
- **As built — spec §9.3.** The success criterion asks that every `Wrong` row
  be reproduced by hand with `z3`/`cvc5`. That was not done for all 742. What
  was done: 652 rows carry the in-run oracle answer the harness recorded, and
  are cited as such rather than re-run; the 90 rows whose in-run z3 timed out
  were hand-re-run against both oracles at a longer budget (62 QF_ABV at
  120 s, 28 QF_DT at 300 s); and an 11-row per-family sample was hand-run
  across families as a spot-check that the harness's recorded answers match a
  fresh invocation. 742 rows × 2 oracles × 120 s is up to 49 CPU-hours and
  would have re-derived, for the 652, an answer the run already holds on
  record; the 90 undecided-in-run rows were the only ones where a hand re-run
  could add evidence, so the budget went there. Every `Wrong` row is filed as
  a named follow-up slice, per the other half of §9.3.
- **`status-suspect` is 0.** No row had shinri contradict `:status` with both
  oracles agreeing with shinri. The `wrong` count is therefore not diluted by
  bad benchmark metadata in the corpus, at least not detectably.
- **`unverified` (1,371) is not a wrong answer.** It means shinri decided,
  `:status` was absent or `unknown`, and the oracle could not confirm the
  answer within the same budget. QF_SLIA carries 1,260 of them and QF_S 96.
  These rows are excluded from `correct`, so the 48.1% correct-rate is a
  lower bound on this measure.
- **`:status` is benchmark metadata, not ground truth.** For the 44 QF_ABV
  and 1 QF_DT rows where no oracle decided even at the longer hand budget,
  `:status` is the only evidence that shinri is wrong. It is strong evidence
  — these families are old and widely used — but a slice that fails to
  reproduce a bug on one of those 45 rows should suspect the metadata before
  concluding the bug is fixed.
- **The 20 s / 3072 MB budget shapes the tail.** `timeout` (11,058) and `oom`
  (2,099 corrected) are budget-relative counts, not statements about
  decidability; a longer budget moves rows between `timeout` and `correct`.
  The oracle runs under the same wrapper, which is why 90 `wrong` rows have
  z3 `timeout`.
- **The corpus is pinned.** `bench/manifest.toml` records the Zenodo record
  (`10.5281/zenodo.11061097`, release 2024.04.23), the per-logic archive md5
  and the extracted `.smt2` count, so a later run diffs against this document
  only if it uses the same archives. Raw `results.jsonl` for both runs is
  git-ignored (69 MB for the baseline); both runs' rendered `report.md` are
  committed beside this document as `2026-09-09-smtlib-2024-baseline-report.md`
  and `2026-09-09-smtlib-2024-rerun-report.md`, so every `Cites` pointer above
  resolves inside the repository.
- **Fences that never fired.** `str-fenced`, `str-code-conv`, `str-order`,
  `abv-uf-budget`, `abv-engine`, `fp-crossing-conversion`, `bv-non-bv-atom`,
  `fp-non-bvfp-atom`, `fp-atoms-unsupported`, `fp-bv-atoms-unsupported`,
  `fpbv-uf-args`, `fpbv-uf-budget` and `theory-mixed-sort` do not appear in
  the ranked gaps at all. Absence here means the fence was never reached on
  this corpus, which is a real signal about where the remaining work is not.
  `bv-uf-args` and `abv-uf-args` did fire, 22 times between them; they are in
  the ranked gap list above.
