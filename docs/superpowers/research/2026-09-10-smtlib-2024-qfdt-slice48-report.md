# SMT-LIB 2024 QF_DT re-run — slice 48 — shinri @ 17f2ac31092a

Run-id `slice48`, `BENCH_LOGICS=QF_DT BENCH_RUN_ID=slice48 mise run bench-run`,
same limits as the baseline (20 s / 3072 MB / 6 jobs, cgroup `cpu.max`
`800000 100000`, `memory.max` 34359738368). Started 2026-09-10T16:28:08Z,
finished 2026-09-10T17:00:43Z — **32m35s wall-clock**, within the brief's
30–60 min budget this time (an interim read at row 8,000 correctly projected
the remaining ~700 rows would be timeout-dominated and take the bulk of the
remaining time). 8,700 QF_DT instances — the same paths as
`docs/superpowers/research/2026-09-09-smtlib-2024-baseline-report.md`, so
every row below is a same-path comparison, never a resample; all 8,700
baseline paths are present in this run (0 missing, 0 extra).
`BENCH_RUN_ID=slice48 mise run bench-report` renders
`bench/results/slice48/report.md` from `bench/results/slice48/results.jsonl`
(8,700 rows); this document narrates that report and a path-by-path
transition analysis against the baseline.

Baseline for comparison: `2026-09-09-smtlib-2024-baseline-report.md`,
run-id `baseline-8de004d44944`, QF_DT row (`total 8700, correct 7849,
wrong 328, timeout 507, unknown 11, unverified 5`).

**How the transitions were computed:** a small Python script
(`transitions.py`, not committed — scratch tooling) loads both
`results.jsonl` files keyed by `path`, intersects the key sets (8,700 common,
confirming a same-path comparison), and for every common path where
`baseline[path].verdict != new[path].verdict` buckets the pair
`(baseline_verdict, new_verdict)` per family (`path.split('/')[1]`). Every
count quoted below is a raw tally from that script's output, cross-checked by
hand: for each family, `new_verdict_count = baseline_verdict_count -
(sum of that verdict's outbound transitions) + (sum of that verdict's inbound
transitions)`, confirmed to close exactly for every verdict in every family
(shown inline below).

## Headline

- **The named corpus reproducer is fixed.** `barrett-jsat/tests/v1/v1l30072.cvc.smt2`
  (spec §1's corpus repro, the `collapse_lemma` check-time-merge case) now
  answers `unsat`, matching `:status`.
- **All 37 `tests/`-directory Barrett wrong rows are fixed, 37/37.** Every
  wrong answer in the non-`ite`-encoded corner of the Barrett family — the
  shape `tester_clash` was designed for — is gone.
- **Criterion 1 (Barrett wrong = 0) is MISSED: 166 → 32, not 0.** All 32
  residual wrong rows are concentrated in the `barrett-jsat/typed/`
  subdirectory (deeply nested `ite`-encoded instances), which this fix does
  not fully close. Decomposed below.
- **Criterion 2 (`correct → {timeout,unknown,oom}` = 0) is MISSED: 6, not 0.**
  All 6 are Barrett `correct → timeout`, all small/fast at baseline (4–14 ms).
  Decomposed below.
- **Criterion 5's premise is measurably WRONG.** `20230720-blocksworld` wrong
  rows moved: 162 → **190** (+28), and one blocksworld file flipped from a
  fast, correct `unsat` (47 ms) to a fast, wrong `sat` (27 ms) —
  deterministic on rerun, and bisected to a specific slice-48 commit despite
  the family containing zero explicit tester syntax. This directly
  contradicts the spec's stated premise that this slice does not touch
  blocksworld. See "The blocksworld premise was wrong" below.
- QF_DT `correct` rose from 7,849 to **7,978** (+129) — criterion 3 **PASSES**.
- The randomized generator (criterion 4) failed pre-slice and passes now —
  **PASSES**. See "Oracle evidence".

## Per-logic matrix (QF_DT only, this run)

Copied from `bench/results/slice48/report.md`.

| logic | total | correct | wrong | parse-error | panic | oom | timeout | unknown | unverified | decided% | median ms | p90 ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| QF_DT | 8700 | 7978 | 222 | 0 | 0 | 0 | 489 | 11 | 0 | 91.7 | 4 | 7 |

Baseline's same row, for reference: `total 8700, correct 7849, wrong 328,
parse-error 0, panic 0, oom 0, timeout 507, unknown 11, unverified 5,
decided% 90.2, median 6, p90 11`.

## Verdict counts, baseline vs. slice48

| verdict | baseline | slice48 | delta |
| --- | ---: | ---: | ---: |
| `correct` | 7849 | 7978 | +129 |
| `wrong` | 328 | 222 | -106 |
| `timeout` | 507 | 489 | -18 |
| `unknown:sat-budget` | 11 | 11 | +0 |
| `unverified` | 5 | 0 | -5 |

## Transitions (changed cells only, same-path comparison)

### Overall

| baseline | slice48 | count | families |
| --- | --- | ---: | --- |
| `wrong` | `correct` | 134 | 20172804-Barrett 134 |
| `timeout` | `wrong` | 31 | 20230720-blocksworld 31 |
| `correct` | `timeout` | 6 | 20172804-Barrett 6 |
| `unverified` | `timeout` | 5 | 20230720-blocksworld 5 |
| `wrong` | `timeout` | 5 | 20230720-blocksworld 4, 20172804-Barrett 1 |
| `timeout` | `correct` | 3 | 20172804-Barrett 3 |
| `correct` | `wrong` | 2 | 20230720-blocksworld 1, 20172804-Barrett 1 |

Unchanged: 8,514.

### Family: `20172804-Barrett` (n=8,000)

- baseline: `{correct: 7814, wrong: 166, unknown:sat-budget: 11, timeout: 9}`
- slice48: `{correct: 7944, wrong: 32, unknown:sat-budget: 11, timeout: 13}`
- transitions: `wrong→correct` 134, `correct→timeout` 6, `timeout→correct` 3,
  `correct→wrong` 1, `wrong→timeout` 1

Closure check: `correct` 7944 = 7814 − 6 (→timeout) − 1 (→wrong) + 134
(wrong→) + 3 (timeout→). `wrong` 32 = 166 − 134 (→correct) − 1 (→timeout) + 1
(correct→). `timeout` 13 = 9 − 3 (→correct) + 6 (correct→) + 1 (wrong→).
`unknown` unchanged at 11. All four close exactly.

### Family: `20210312-Bouvier` (n=200)

- baseline: `{timeout: 200}`
- slice48: `{timeout: 200}`
- transitions: none. Unaffected — this family was 100% timeout at baseline
  and stays 100% timeout; the slice changes nothing about it.

### Family: `20230720-blocksworld` (n=500)

- baseline: `{timeout: 298, wrong: 162, correct: 35, unverified: 5}`
- slice48: `{timeout: 276, wrong: 190, correct: 34}`
- transitions: `timeout→wrong` 31, `unverified→timeout` 5, `wrong→timeout` 4,
  `correct→wrong` 1

Closure check: `wrong` 190 = 162 − 4 (→timeout) + 31 (timeout→) + 1
(correct→). `timeout` 276 = 298 − 31 (→wrong) + 5 (unverified→) + 4
(wrong→). `correct` 34 = 35 − 1 (→wrong). `unverified` 0 = 5 − 5 (→timeout).
All four close exactly.

## Success criteria

| # | criterion | baseline | slice48 | verdict |
| --- | --- | ---: | ---: | --- |
| 1 | `20172804-Barrett` wrong = 0 | 166 | **32** | **MISS** (decomposed below) |
| 2 | `correct → {timeout,unknown,oom}` = 0 | — | **6** | **MISS** (decomposed below) |
| 3 | QF_DT `correct` ≥ 7,849 | 7849 | **7978** (+129) | **PASS** |
| 4 | randomized generator failed pre-slice, passes now | — | yes | **PASS** |
| 5 | `20230720-blocksworld` wrong (measured, not gated) | 162 | **190** (+28) | measured — premise contradicted, see below |

### Criterion 1 — decomposed, not relaxed

166 baseline Barrett wrong rows split cleanly along a directory boundary the
spec did not anticipate:

| subfamily | baseline wrong | fixed (`→correct`) | honest timeout (`→timeout`) | still/newly wrong |
| --- | ---: | ---: | ---: | ---: |
| `barrett-jsat/tests/` (non-`ite`) | 37 | 37 | 0 | **0** |
| `barrett-jsat/typed/` (nested `ite`) | 129 | 97 | 1 | **31** |
| plus one new regression, `correct → wrong` | — | — | — | **+1** |
| **total slice48 wrong** | 166 | 134 | 1 | **32** |

`tests/` is fixed **100%**, including the spec's own named corpus reproducer
(`v1l30072.cvc.smt2`). Every one of the 32 residual/new wrong rows is in
`typed/`, which encodes assertions through nested `ite` terms whose branch
conditions are testers — e.g. the failing file `typed_v1l30072.cvc.smt2`
contains `(ite ((_ is cons) x2) (car x2) ...)` — rather than a
top-level `(assert (is-cons x2))`.

**Investigation (not a fix).** `word_norm::normalize` eliminates any
non-Bool/non-String-sorted `ite(c, x, y)` into a fresh symbol `w` plus a
defining assertion `(ite c (= w x) (= w y))` (`crates/shinri-solver/src/word_norm.rs:80,148`)
— a *Boolean*-sorted `ite`, so Tseitin CNF-encodes it as ordinary clauses over
the tester atom `c` and the two branch equalities. This is structurally
different from a directly-asserted tester and is one candidate explanation
for why `tester_clash` (which iterates `asserted_testers`, populated only by
`DtSolver::assert`) can still miss a clash reached this way. A second,
unchanged-since-slice-39 candidate: `DtSolver::assert` (`lib.rs:888`) opens
with `if !lit.is_positive() { return None; }` — negative tester literals
(`¬is-D(t)`) are never recorded and never checked against the class they
constrain, a gap this slice's spec §8 discusses only as an *efficiency*
concern (Approach B), not explored as a possible source of the `typed/`
residual. **Neither hypothesis was confirmed**: a hand-built minimal case
(`¬is-cons(x) ∧ x = cons(...)`, both assertion orders) answers `unsat`
correctly on the current binary — the 2-constructor exhaustiveness split
apparently converts the negative tester into a positive one for the sibling
constructor before this gap can bite. The real mechanism needs a targeted
bisect on one of the 31 residual `typed/` files, which is genuinely harder
than the corpus's simple shapes and is queued below, not solved here.

### Criterion 2 — decomposed, not relaxed

All 6 `correct → timeout` rows are Barrett, all `typed/`, all small and fast
at baseline:

| path | bytes | baseline wall_ms | slice48 wall_ms |
| --- | ---: | ---: | ---: |
| `typed/v10/typed_v10l50025.cvc.smt2` | 1716 | 7 | 20004 (timeout) |
| `typed/v3/typed_v3l60096.cvc.smt2` | 1293 | 13 | 20005 (timeout) |
| `typed/v3/typed_v3l90023.cvc.smt2` | 2828 | 14 | 20004 (timeout) |
| `typed/v5/typed_v5l40035.cvc.smt2` | 1308 | 4 | 20007 (timeout) |
| `typed/v5/typed_v5l60030.cvc.smt2` | 1520 | 7 | 20004 (timeout) |
| `typed/v5/typed_v5l70010.cvc.smt2` | 1384 | 5 | 20003 (timeout) |

None of these overlap the `wrong → timeout` set (5 rows, listed in the
overall transition table) — they are strictly `correct → timeout`, so unlike
slice 47's criterion-3 miss there is no "wrong answer became an honest
timeout" component to net out here: **all 6 are a genuine cost of the fix**.
Re-checking `tester_clash` on every `check()` call, on these particular
`typed/`-shaped instances, is enough additional case-split churn to blow the
20 s budget on formulas that solved in single-digit milliseconds before.

**Beyond criterion 2's literal scope** (it only tracks `→{timeout,unknown,oom}`):
the 2 `correct → wrong` rows found in the transition matrix are a more severe
regression than a timeout — a previously-correct answer is now actively
wrong. Both were bisected; see the next section.

## The blocksworld premise was wrong

The spec's premise (§1, §9) is that blocksworld's 162 baseline wrong rows are
a *different* bug from Barrett's, because the family's `.smt2` sources
contain **zero occurrences of `(_ is C)`** — a rule about asserted testers
"cannot be their cause." That claim about the *source syntax* is true. It
does not mean the tester machinery is inert for blocksworld at *runtime*:

- `DtSolver::exhaustiveness_split` (`crates/shinri-dt/src/lib.rs:416`) mints
  tester atoms **internally** — `is_c_t = mk_app(tester, [t])` for every
  constructor of a multi-constructor datatype whenever a term's class isn't
  yet determined — and offers them to SAT as a case-split disjunction. This
  is exactly the exhaustiveness machinery blocksworld's 21-constructor enums
  and multi-field records need, with no user-written `(_ is C)` anywhere.
  Once SAT decides one of those split literals, it reaches `DtSolver::assert`
  and populates `asserted_testers` — the exact record this slice's Task 2
  changed from a monotone `HashSet` to a level-indexed `Vec` with real
  `push`/`pop`.
- **Measured:** blocksworld wrong rows rose 162 → **190** (+28), driven
  mostly by 31 previously-`timeout` rows now completing and landing on
  `wrong` (6 of those 31 are independently z3-confirmed `unsat` against
  shinri's `sat`; the other 25 have z3 itself timing out, so they are
  "wrong" only against the file's declared `:status`, not oracle-confirmed).
- **One row is a clean, deterministic new regression, not a timing
  artifact:** `blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2`
  answered `unsat` in 47 ms at baseline and answers `sat` in 27 ms here —
  both fast, both well inside budget, reproduced identically across 3
  reruns of the current binary. Bisecting the branch commit-by-commit
  (built each commit's `shinri-cli` in an isolated `git worktree`, no
  source files modified) pins the flip to **`e5cc3eea`, Task 2's
  `asserted_testers` refactor** — *before* Task 3's `tester_clash` even
  exists:

  | commit | task | this file's answer |
  | --- | --- | --- |
  | `7abe84ca` (pre-slice, `main`) | — | `unsat` (correct) |
  | `e5cc3eea` | T2 — level-indexed `asserted_testers` | **`sat` (wrong)** |
  | `c0957d4b` | T3 — `tester_clash` | `sat` (wrong, unchanged) |
  | `17f2ac31` (HEAD) | T4 — fence | `sat` (wrong, unchanged) |

  The same bisect run against the Barrett `correct → wrong` row
  (`typed/v3/typed_v3l70051.cvc.smt2`) pins that flip to a **different**
  commit — `c0957d4b`, Task 3's `tester_clash` itself:

  | commit | task | this file's answer |
  | --- | --- | --- |
  | `7abe84ca` (pre-slice) | — | `unsat` (correct) |
  | `e5cc3eea` | T2 | `unsat` (correct, unchanged) |
  | `c0957d4b` | T3 — `tester_clash` | **`sat` (wrong)** |
  | `17f2ac31` (HEAD) | T4 | `sat` (wrong, unchanged) |

**Conclusion: the premise that this slice does not touch blocksworld is
false as measured.** It is true that no *change in tester_clash's logic*
touches blocksworld's own bug (blocksworld's regression traces to Task 2's
bookkeeping refactor, not Task 3's new rule), but the family is not immune
to this slice the way §1/§9 assumed — the shared `asserted_testers` record
is live for it via internal exhaustiveness splitting, and changing that
record's lifetime (monotone → per-level) changed blocksworld's search
trajectory enough to flip one instance from correct to wrong. This is a
finding for the next slice to start from, not a blocker for this one (per
spec §6, criterion 5 is measured, not gated) — but it means blocksworld's
162-row bug and this slice's changes are not as cleanly separated as
assumed, and any future change to `asserted_testers`' semantics needs a
blocksworld regression check, not just a Barrett one.

## Oracle evidence

`cargo nextest run -p shinri-solver --features oracle -E 'binary(qfdt_oracle)' --no-capture`
→ **17 discovered** (non-zero, confirmed), **17 passed, 0 failed**, including:

```
qfdt_random_matches_z3: 300 iters, 144 sat / 152 unsat / 4 skipped, 0 mismatches
```

That same test **failed on pre-slice code**, quoted verbatim from commit
`90a061b8`'s message:

```
thread 'qfdt_random_matches_z3' panicked at crates/shinri-solver/tests/qfdt_oracle.rs:411:9:
assertion `left == right` failed: QF_DT SOUNDNESS DISAGREEMENT (iter 44): shinri=sat z3=unsat
Reproduce with this instance:
(set-logic QF_DT)(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))((cons (car tree) (cdr list)) (null))((node (children list)) (leaf (data nat)))))(declare-datatype Color ((red) (green) (blue)))(declare-fun n1 () nat)(declare-fun l1 () list)(declare-fun l2 () list)(declare-fun t1 () tree)(declare-fun c1 () Color)(assert (and ((_ is cons) l2)(not ((_ is null) (cons t1 l1)))((_ is null) (children (node l2)))(not (= null (children t1)))(not ((_ is null) (cdr null)))))(check-sat)
  left: "sat"
 right: "unsat"
```

That is success criterion 4.

The full unfiltered oracle gate, `cargo nextest run -p shinri-solver
--features oracle` (required per spec §5.1 because this slice touches a
shared theory solver, not just test files), ran at the current HEAD
(`17f2ac31`, unchanged since Task 5's sweep — confirmed via `git status`
clean and matching commit sha): **651 discovered, 651 passed, 0 failed, 3
skipped**, including `qfs_differential` (the string suite a filtered run
would silently skip) and both `fp_oracle` suites.

## Queued for the next slice

- **`20230720-blocksworld`, now 190 wrong rows (was 162).** Per this report's
  finding, `asserted_testers`'s level-indexing (Task 2) already measurably
  perturbs one blocksworld instance
  (`blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2`, bisected above),
  so the next slice's bisect should not assume the family is isolated from
  DT's tester bookkeeping. The cheapest standalone reproducer remains
  `blocksworld_from_0_18_1_to_17_2_0_negated_goal_bmc_5.smt2` (21,247 B,
  answers `sat` — wrong, `:status unsat` — in 0.95 s at baseline, 0.54 s
  here; unchanged verdict across this run). A real bisect on a 21–53 KB
  instance is still needed; this report only pins the *incidental* one-row
  regression, not blocksworld's own 162/190-row bug.
- **The 32 residual/new `20172804-Barrett/.../typed/` wrong rows.** All in
  the nested-`ite`-encoded subfamily; the two candidate mechanisms
  investigated above (word_norm's ite-elimination structurally hiding the
  tester from `asserted_testers`, and `DtSolver::assert`'s unconditional
  `¬is-D(t)` no-op) were **not confirmed** — a hand-built minimal negative-
  tester case answers correctly. Needs a genuine bisect on one of the 31
  residual files (e.g. `typed/v1/typed_v1l30072.cvc.smt2`, 1,716 B) or the
  newly-regressed `typed/v3/typed_v3l70051.cvc.smt2` (1,489 B, 9 ms —
  cheap to iterate on).
- **The 6 `correct → timeout` Barrett rows** (all `typed/`, all
  1,293–2,828 B, all sub-15ms at baseline) — a genuine performance cost of
  re-running `tester_clash` on every `check()` call, not a wrong-answer
  trade. Candidate mitigation: Approach B (§8, propagating `¬is-D(t)` instead
  of rediscovering the conflict on every branch).
- **Approach B (propagating `¬is-D(t)`), banked per spec §8.** The
  un-banking trigger was "`correct → timeout` (criterion 2) or a material
  rise in QF_DT `timeout`." **This run shows exactly that signal**: 6
  `correct → timeout` rows (criterion 2 missed) plus QF_DT's overall
  `timeout` bucket only fell modestly (507 → 489, -18) despite 137 Barrett
  rows leaving `wrong`/`timeout` for `correct` — i.e. the fix is trading some
  of its own gains for new timeouts on the harder `typed/` shapes. This is a
  measured thrash signal; the next slice should treat Approach B as a live
  candidate, not a deferred nice-to-have.
- **QF_DT's remaining `timeout`/`unknown` rows** — 489 timeout (was 507), 11
  `unknown:sat-budget` (unchanged) — out of scope per spec §2, still in the
  slice-46 queue.

## References

- Baseline — `2026-09-09-smtlib-2024-baseline.md`,
  `2026-09-09-smtlib-2024-baseline-report.md` (QF_DT row and `## Wrong
  answers`).
- Spec — `docs/superpowers/specs/2026-09-10-shinri-slice48-qfdt-tester-disjointness-design.md`,
  `## 11. Measured outcomes`.
- Raw results — `bench/results/slice48/results.jsonl` (8,700 rows,
  git-ignored), rendered report `bench/results/slice48/report.md`.
- Task 1's generator failure — commit `90a061b8`. Task 3's `tester_clash` —
  commit `c0957d4b`. Task 2's level-indexed `asserted_testers` — commit
  `e5cc3eea`. Task 4's defensive fence — commit `17f2ac31` (branch HEAD).
- The slice-47 report's structure and criterion-decomposition precedent —
  `2026-09-09-smtlib-2024-qfabv-slice47-report.md`.
