# SMT-LIB 2024 QF_DT re-run — slice 48 — shinri @ 17f2ac31092a (updated @ f27a340ceb77)

**Updated.** The measurement below (run-id `slice48`, commit `17f2ac31092a`)
found that this slice's own `asserted_testers` change had introduced a
wrong-`sat` soundness regression (blocksworld wrong rows 162 → 190, plus a
clean `correct → wrong` flip). A fix wave (commit `f27a340ceb77`) then split
`asserted_testers` into two records by consumer. **Every number in the
original measurement below is therefore stale for the shipped code.** The
true, current numbers are in "## Update — re-measure after the fix wave
(run-id `slice48b`)" immediately below. The original measurement is kept
intact and clearly labelled after it — do not read it as a description of
current behaviour, but do not skip it either: the regression it caught, and
the fix that followed, are the point of this slice.

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

## Update — re-measure after the fix wave (run-id `slice48b`)

**Commands, in order, and wall-clock:**

```
BENCH_LOGICS=QF_DT BENCH_RUN_ID=slice48b mise run bench-run
BENCH_RUN_ID=slice48b mise run bench-report
```

Same limits as baseline and the pre-fix run (20 s / 3072 MB / 6 jobs, cgroup
`cpu.max` `800000 100000`, `memory.max` 34359738368). Started
2026-09-10T17:53:49Z. The binary was built from commit `f27a340ceb77` (the
fix-wave commit — its fixture header records `"sha":"f27a340ceb77"`). All
8,700 QF_DT paths, 0 missing / 0 extra relative to both the baseline and the
pre-fix run — a true same-path, three-way comparison, never a resample.
`HEAD` advanced once more after this run started, to `f8b605e957e0` ("slice48
final-review fix wave — comments and test strength"); that commit's own
message states no executable logic changed outside two test bodies, and
`crates/` was not touched by this reporting task, so this measurement remains
representative of current `HEAD`.

Final line: `8700/8700 correct=7978 wrong=200 timeout=510 unknown=11
unverified=1`. `BENCH_RUN_ID=slice48b mise run bench-report` rendered
`bench/results/slice48b/report.md`.

**How the three-way comparison was computed:** a Python script
(`transitions.py`, scratch tooling, not committed) loads all three
`results.jsonl` files (`baseline-8de004d44944`, `slice48`, `slice48b`) keyed
by `path`, restricted to `QF_DT/` rows, confirms **8,700 paths common to all
three** (0 missing/extra in any direction), and for every common path
compares `verdict` pairwise, bucketing `(baseline_verdict, fixed_verdict)`
(and, separately, `(pre_fix_verdict, fixed_verdict)`) per family
(`path.split('/')[1]`, with `barrett-jsat/tests/` vs `barrett-jsat/typed/`
split by substring match for Barrett). Every count below is a raw tally from
that script, and every per-family verdict count closes exactly against
`new = old − outbound + inbound` (shown inline below), the same closure check
the original report used.

### Three-way verdict counts, overall (QF_DT, n=8,700)

| verdict | baseline | pre-fix (`slice48`) | fixed (`slice48b`) |
| --- | ---: | ---: | ---: |
| `correct` | 7,849 | 7,978 | **7,978** |
| `wrong` | 328 | 222 | **200** |
| `timeout` | 507 | 489 | **510** |
| `unknown:sat-budget` | 11 | 11 | **11** |
| `unverified` | 5 | 0 | **1** |

### Three-way wrong-row counts, per family

| family | baseline | pre-fix | fixed |
| --- | ---: | ---: | ---: |
| `20172804-Barrett` | 166 | 32 | **31** |
| `20172804-Barrett/barrett-jsat/tests/` | 37 | 0 | **0** |
| `20172804-Barrett/barrett-jsat/typed/` | 129 | 32 | **31** |
| `20230720-blocksworld` | 162 | 190 | **169** |
| `20210312-Bouvier` | 0 | 0 | **0** |

### Success criteria — baseline / pre-fix / fixed, with gates

| # | criterion | baseline | pre-fix | fixed | gate | verdict |
| --- | --- | ---: | ---: | ---: | --- | --- |
| 1 | `20172804-Barrett` wrong rows | 166 | 32 | **31** | 0 — hard gate | **MISS** |
| 2 | `correct → {timeout,unknown,oom}` | — | 6 | **7** | 0 — hard gate | **MISS** |
| 3 | QF_DT `correct` | 7,849 | 7,978 | **7,978** (+129 vs baseline) | ≥ 7,849 | **PASS** |
| 4 | generator failed pre-slice, passes now | — | yes | yes (evidence carried forward) | yes | **PASS** |
| 5 | `20230720-blocksworld` wrong rows | 162 | 190 | **169** | measured, NOT gated | measured |

**Both hard gates remain missed. Neither is relaxed here — both are
decomposed below with raw numbers and, where the gate is criterion 1 or the
`correct → wrong` count, every path listed individually.**

#### Criterion 1 — 31, not 0 (decomposed)

The fix wave repairs exactly **one** of the 32 pre-fix Barrett wrong rows:
`barrett-jsat/typed/v3/typed_v3l70051.cvc.smt2` — this is the same file the
pre-fix report bisected to `c0957d4b` (Task 3, `tester_clash` itself) as a
`correct → wrong` regression. It answers `correct` again in `slice48b`, at
9 ms — identical to its baseline wall-clock. The other 31 residual
`barrett-jsat/typed/` wrong rows are byte-for-byte the SAME 31 files, verdict
unchanged from pre-fix to fixed — the fix wave's record split does not move
this bisect forward at all; it remains open (queued below). All 37
`barrett-jsat/tests/` wrong rows stay fixed at 0/37, unchanged from pre-fix.

#### Criterion 2 — 7, not 6 (decomposed) — the un-banking trigger fired in an unexpected direction

Comparing the 6 pre-fix `correct → timeout` rows against the fixed run
directly:

| path | baseline wall_ms | pre-fix wall_ms | fixed wall_ms | note |
| --- | ---: | ---: | ---: | --- |
| `20172804-Barrett/barrett-jsat/typed/v10/typed_v10l50025.cvc.smt2` | 7 | 20,004 (timeout) | 20,004 (timeout) | unchanged |
| `20172804-Barrett/barrett-jsat/typed/v3/typed_v3l60096.cvc.smt2` | 13 | 20,005 (timeout) | 20,004 (timeout) | unchanged |
| `20172804-Barrett/barrett-jsat/typed/v3/typed_v3l90023.cvc.smt2` | 14 | 20,004 (timeout) | **18 (correct)** | **cured by the split** |
| `20172804-Barrett/barrett-jsat/typed/v5/typed_v5l40035.cvc.smt2` | 4 | 20,007 (timeout) | 20,003 (timeout) | unchanged |
| `20172804-Barrett/barrett-jsat/typed/v5/typed_v5l60030.cvc.smt2` | 7 | 20,004 (timeout) | 20,005 (timeout) | unchanged |
| `20172804-Barrett/barrett-jsat/typed/v5/typed_v5l70010.cvc.smt2` | 5 | 20,003 (timeout) | 20,004 (timeout) | unchanged |

`typed_v3l90023.cvc.smt2` is **cured**: the record split removes the
redundant `tester_clash` re-derivation churn that blew the pre-fix budget on
this specific file, and it now solves in 18 ms — faster than its own
baseline. That leaves 5 of the original 6 as unchanged genuine timeouts. But
the fix wave also introduces **two brand-new** `correct → timeout` rows that
were fine at both baseline and pre-fix:

| path | baseline wall_ms | pre-fix wall_ms | fixed wall_ms | note |
| --- | ---: | ---: | ---: | --- |
| `20172804-Barrett/barrett-jsat/tests/v1/v1l60099.cvc.smt2` | 37 | 39 (correct) | 20,006 (timeout) | **new — first-ever `tests/` timeout** |
| `20230720-blocksworld/blocksworld_from_3_5_0_to_8_0_0_negated_goal_bmc_14.smt2` | 4,368 | 18,315 (correct) | 20,006 (timeout) | **new — already-marginal file pushed over budget** |

Net: 6 − 1 (cured) + 2 (new) = **7**. `v1l60099.cvc.smt2` is notable because
it is in `barrett-jsat/tests/`, the subfamily previously measured 100%
clean of any wrong or timeout regression — this is the first timeout the
fix wave adds there. `blocksworld_..._bmc_14.smt2` was already slow at
pre-fix (18,315 ms, close to the 20 s cap) and the split's extra per-`check`
`tester_clash` cost tips it over. Both are a genuine, if small, performance
cost of the split — no wrong answer became either of these timeouts, so
unlike slice 47's criterion-3 miss there is no "regression converted to
honest timeout" component netting this down.

#### Beyond criterion 2's literal scope — `correct → wrong`, the harder regression

Baseline → fixed has exactly **one** `correct → wrong` row (down from 2
pre-fix, since the Barrett one above is now cured):

**`QF_DT/20230720-blocksworld/blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2`**
— `unsat` at 47 ms (baseline) → `sat` at 27 ms (pre-fix) → `sat` at 30 ms
(fixed). Deterministic, unchanged by the fix wave. This is the SAME file the
pre-fix report bisected to `e5cc3eea` (Task 2's levelling, *before*
`tester_clash` existed). **The fix wave's record split does not fix it,
because its cause is a different, pre-existing defect — in `shinri-euf`, not
in the `shinri-dt` tester bookkeeping this slice owns.** Root-caused below.
This is the complete list — there are no other `correct → wrong` rows
anywhere in the baseline → fixed comparison.

#### Root cause of `blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2` — a pre-existing `shinri-euf` defect, not this slice

(Carried forward from the untracked fix-wave report,
`.superpowers/sdd/2026-09-10-shinri-slice48-qfdt-tester-disjointness/fix-wave-report.md`
§5, which would otherwise vanish on merge since `.superpowers/` is
git-ignored.)

**Five-variant isolation, each row a `crates/shinri-dt/src/lib.rs` swap +
release rebuild:**

| variant | `bmc_2.smt2` answer |
| --- | --- |
| `main` (pre-slice) | `unsat` (correct) |
| branch HEAD (levelling + `tester_clash`) | `sat` (wrong) |
| HEAD with `tester_clash` disabled (levelling alone) | `sat` (wrong) |
| **fix (records split) + `tester_clash` — the shipped code** | **`sat` (wrong)** |
| fix (records split) with `tester_clash` disabled | `unsat` (correct) |

Row 3 (levelling alone, `tester_clash` fully disabled) proves Task 2's
levelling is BY ITSELF sufficient to flip this file, independent of Task 3's
`tester_clash` — a conflict rule cannot turn an `unsat` instance into `sat`
on its own, it can only change the search trajectory, so the wrong `sat` was
always a pre-existing hole that the levelling change happens to steer the
search into. Row 4 is the important one for this report: it is the actual
shipped fix, and it is **still wrong** — matching the measured `slice48b`
result above (`sat` at 30 ms) exactly. Only row 5, an artificial ablation
that also disables `tester_clash` (not something the shipped code does), gets
back to `unsat` — which shows `tester_clash` ALSO independently reaches this
same pre-existing hole on this file, through a different path than the
levelling did. Two different slice-48 mechanisms (Task 2's levelling and
Task 3's `tester_clash`) each independently flip this file into the same
pre-existing `shinri-euf` hole; fixing either mechanism's OWN bug (as the
fix wave did for the levelling) is not enough, because the other one reaches
the same hole on its own.

**Delta-debugging** the file against the invariant "z3 says `unsat`, shinri
says `sat`" reduced it to this 9-line query, which **also answers `sat` on
`main`** (i.e. this defect is not new — Task 2's levelling only changes
whether search reaches it):

```smt2
(set-logic QF_DT)
(declare-datatypes ((E 0)) (((A) (C) (H))))
(declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))
(declare-datatypes ((R 0)) (((R (right T)))))
(declare-fun p () R)(declare-fun q () R)(declare-fun u () R)(declare-fun c () E)
(assert (= (right p) (stack C empty)))
(assert (= q p))
(assert (ite (= c A) (= (right u) (right q)) (= (right u) (right q))))
(assert (= (right u) (stack H empty)))
(check-sat)
```

z3 says `unsat`; `main`, branch HEAD and the fix all say `sat`. Replacing the
degenerate `ite` with the plain unit equality
`(assert (= (right u) (right q)))` gives the correct `unsat` on every
variant — **the equality must be derived above decision level 0** (i.e.
inside a case split, here trivially both branches of the `ite`) to trigger
the defect.

An instrumented dump at the `shinri-dt` `Sat` return showed:

```
sat-ctor stack rep=ENodeId(0)      <- (stack C empty)
sat-ctor stack rep=ENodeId(0)      <- (stack H empty)   same class, same ctor
sat-sel  top   rep=ENodeId(14)     <- top(stack C empty), in C's class
sat-sel  top   rep=ENodeId(17)     <- top(stack H empty), in H's class
```

Two `stack` applications are merged into one class, yet their `top` selector
applications are never merged by congruence — so injectivity never derives
`C = H` and `constructor_clash` never fires. `shinri-dt` is locally consistent
at this point (a scan at the `Sat` return found zero asserted-but-disagreeing
testers over all 89 tester atoms in this instance), so no `shinri-dt` fence
can catch it — the defect is not in this theory.

**Root cause, in `crates/shinri-euf`:** `EGraph::add_term`
(`crates/shinri-euf/src/egraph.rs:137`) records `Undo::LookupInsert(sig)` for
the signature-table entry it installs when a term is first registered. That
means a term first registered at decision level > 0 has its congruence
registration **undone by the next backtrack** — while its `seen_terms` guard
(line 139) makes re-registration a permanent no-op afterward. The selector
applications `top(stack C empty)` / `top(stack H empty)` are minted mid-search
by `instantiate_injectivity_selectors` and bound via the seam's `bind_fresh`
at decision level ≥ 1, so they lose congruence permanently — injectivity
never fires, and the wrong `sat` follows. `Euf::new_var` already documents
this exact class of bug ("the I1 soundness bug") for the ⊤/⊥ sentinels, and
works around it by registering those specific terms at level 0; the general
case — any selector application minted mid-search over a record-shaped
datatype — was never fixed.

**This is a shared-core soundness defect, not a `shinri-dt` bug, and not
something this slice's fix wave could or should have touched** (per the
shared-core / full-oracle rule, it needs its own slice). It reproduces on
`main` today, independent of anything in slice 48.

**Note for the oracle:** `qfdt_oracle`'s generator reports 0 mismatches over
300 iterations while this defect is live. `gen_instance` only emits top-level
ground conjuncts, so every input literal lands at decision level 0 and the
generator structurally cannot produce the shape that triggers this defect (a
selector-app equality derived above level 0 over a record-shaped datatype) —
its 0 mismatches is not coverage of this bug. See "Queued for the next
slice".

#### Criterion 3, 4, 5 — brief re-statement with fixed numbers

**Criterion 3 (PASS, unchanged from pre-fix):** QF_DT `correct` is 7,978 in
both the pre-fix and fixed runs — the fix wave's per-file churn (described
above) nets to zero at the QF_DT-total granularity, still +129 over baseline.

**Criterion 4 (PASS, evidence carried forward, not re-run):** No `shinri-dt`
production logic differs between the `slice48b` binary (`f27a340ceb77`) and
the evidence already gathered against that same code path — commit
`90a061b8`'s pre-slice failure (`QF_DT SOUNDNESS DISAGREEMENT (iter 44):
shinri=sat z3=unsat`) and the fix-wave report's own oracle gate at
`f27a340ceb77` (`cargo nextest run -p shinri-solver --features oracle -E
'binary(qfdt_oracle)' --no-capture` → 17 discovered, 17 passed, 0 failed,
including `qfdt_random_matches_z3: 300 iters, 146 sat / 152 unsat / 2
skipped, 0 mismatches`). Re-running the identical binary against the
identical test would add cost for no new information, so it is cited rather
than reproduced. As noted above, this generator's 0 mismatches does not cover
the `shinri-euf` defect.

**Criterion 5 (measured, not gated — 169, and the premise is still
discarded):** blocksworld wrong rows moved 162 (baseline) → 190 (pre-fix) →
**169** (fixed). The fix wave's split moves 28 pre-fix `wrong` rows to an
honest `timeout` and 7 pre-fix `timeout` rows newly complete as `wrong`,
netting −21 from the pre-fix count but still **+7 over baseline**. §1/§9's
premise — that this family is untouched by this slice because its corpus
files contain zero `(_ is C)` syntax — remains measurably wrong: the shared
tester bookkeeping is live for this family via internal
`exhaustiveness_split` minting, exactly as the pre-fix measurement found.
Only the one clean `correct → wrong` row above has an identified root cause,
and that cause is `shinri-euf`, not whatever mechanism produces the family's
other 168 wrong rows (still unexplained, still queued).

#### Full transition matrix, baseline → fixed (`slice48b`), changed cells only

| baseline | fixed | count | families |
| --- | --- | ---: | --- |
| `wrong` | `correct` | 134 | 20172804-Barrett 134 |
| `timeout` | `wrong` | 17 | 20230720-blocksworld 17 |
| `wrong` | `timeout` | 12 | 20230720-blocksworld 11, 20172804-Barrett 1 |
| `correct` | `timeout` | 7 | 20172804-Barrett 6, 20230720-blocksworld 1 |
| `unverified` | `timeout` | 5 | 20230720-blocksworld 5 |
| `timeout` | `correct` | 3 | 20172804-Barrett 3 |
| `correct` | `wrong` | 1 | 20230720-blocksworld 1 |
| `timeout` | `unverified` | 1 | 20230720-blocksworld 1 |

Unchanged: 8,520 of 8,700.

**Per-family closure (`new = old − outbound + inbound`):**

*`20172804-Barrett` (n=8,000).* baseline `{correct: 7814, wrong: 166,
unknown:sat-budget: 11, timeout: 9}`; fixed `{correct: 7945, wrong: 31,
unknown:sat-budget: 11, timeout: 13}`. Transitions: `wrong→correct` 134,
`correct→timeout` 6, `timeout→correct` 3, `wrong→timeout` 1. `correct`:
7814 − 6 + 134 + 3 = 7945 ✓. `wrong`: 166 − 134 − 1 = 31 ✓. `timeout`:
9 − 3 + 6 + 1 = 13 ✓. `unknown` unchanged at 11 ✓.

*`20210312-Bouvier` (n=200).* baseline and fixed both `{timeout: 200}`. No
transitions — 100% timeout at baseline, unaffected by this slice or its fix,
same as the pre-fix run.

*`20230720-blocksworld` (n=500).* baseline `{wrong: 162, timeout: 298,
correct: 35, unverified: 5}`; fixed `{wrong: 169, timeout: 297, correct: 33,
unverified: 1}`. Transitions: `timeout→wrong` 17, `wrong→timeout` 11,
`unverified→timeout` 5, `correct→wrong` 1, `correct→timeout` 1,
`timeout→unverified` 1. `wrong`: 162 − 11 + 17 + 1 = 169 ✓. `timeout`:
298 − 17 − 1 + 11 + 5 + 1 = 297 ✓. `correct`: 35 − 1 − 1 = 33 ✓.
`unverified`: 5 − 5 + 1 = 1 ✓.

All four verdicts close exactly in every family; overall unchanged
8,520 = 8,700 − (134+17+12+7+5+3+1+1).

#### What the fix wave itself changed (`slice48` pre-fix → `slice48b` fixed, same bin... different commits)

For context, comparing the two post-slice runs directly (not against
baseline) isolates exactly what commit `f27a340ceb77` changed relative to
`17f2ac31092a`:

| pre-fix | fixed | count | families |
| --- | --- | ---: | --- |
| `wrong` | `timeout` | 28 | 20230720-blocksworld 28 |
| `timeout` | `wrong` | 7 | 20230720-blocksworld 7 |
| `correct` | `timeout` | 2 | 20172804-Barrett 1, 20230720-blocksworld 1 |
| `timeout` | `correct` | 1 | 20172804-Barrett 1 |
| `wrong` | `correct` | 1 | 20172804-Barrett 1 |
| `timeout` | `unverified` | 1 | 20230720-blocksworld 1 |

Unchanged: 8,660 of 8,700. This is a smaller, more surgical set of changes
than the baseline → fixed table above (which also carries the slice's net
effect over the original bug) — it isolates the fix wave's own contribution:
1 Barrett file cured (`typed_v3l70051.cvc.smt2`, the `correct → wrong`
regression), 1 Barrett timeout cured (`typed_v3l90023.cvc.smt2`), 2 new
timeouts (1 Barrett `tests/`, 1 blocksworld), and a further reshuffling of 35
blocksworld rows among `wrong`/`timeout`/`unverified` (net wrong −21, as
above) from the family's continuing sensitivity to the shared tester
bookkeeping.

### Queued for the next slice (current, fixed-code state — supersedes the pre-fix list below)

- **The pre-existing `shinri-euf` congruence-loss defect.**
  `EGraph::add_term` (`crates/shinri-euf/src/egraph.rs:137`) records its
  signature-table insert on the undo log, so a term first registered above
  decision level 0 loses congruence on the next backtrack and the
  `seen_terms` guard blocks re-registration forever; selector applications
  minted mid-search (e.g. by `instantiate_injectivity_selectors`) therefore
  lose congruence permanently, so injectivity never fires and the result is
  a wrong `sat`. Full mechanism, the five-variant isolation and the 9-line
  reduced repro are above ("Root cause of
  `blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2`"). It reproduces
  on `main`, independent of anything in slice 48. `Euf::new_var` already
  documents this class of bug ("the I1 soundness bug") for the ⊤/⊥
  sentinels, but the general case — any selector application minted
  mid-search over a record-shaped datatype — was never fixed. This is a
  shared-core change and needs its own slice with the full unfiltered
  oracle, not a `shinri-dt`-only fix. **To be explicit:**
  `blocksworld_from_6_0_2_to_2_5_1_negated_goal_bmc_2.smt2` still answers
  `sat` (wrong) for this reason — not because of anything slice 48 did;
  slice 48's own fix wave (the record split) is confirmed unable to touch
  it (five-variant isolation above).
- **`qfdt_oracle`'s generator cannot emit the shape that triggers the
  `shinri-euf` defect above.** `gen_instance` only emits top-level ground
  conjuncts, so every input literal lands at decision level 0, and the
  generator structurally cannot produce a selector-app equality (or a
  tester) derived above level 0 — exactly the shape both the `shinri-euf`
  defect and (historically) the `typed/` residual needed. Its 0 mismatches
  over 300 iterations is therefore not coverage of either live defect. The
  next slice's generator work extending it to disjunction-/`ite`-guarded
  testers and record-shaped datatypes must FAIL on this branch's current
  HEAD for the `shinri-euf` defect before its coverage claim is believed.
- **The 31 residual `20172804-Barrett/.../typed/` wrong rows** (was 32
  pre-fix; the fix wave cured exactly one of them,
  `typed_v3l70051.cvc.smt2`). Still needs a targeted bisect on one of the 31
  remaining files (e.g. `typed/v1/typed_v1l30072.cvc.smt2`, 1,716 B) — the
  fix wave did not move this forward, and neither candidate mechanism from
  the pre-fix investigation (word_norm's `ite`-elimination; `DtSolver::assert`'s
  negative-tester no-op) was confirmed.
- **The 7 `correct → timeout` rows** (was 6 pre-fix; the fix wave cured one
  Barrett timeout and introduced two new ones — one in `barrett-jsat/tests/`,
  previously 100% clean, one in blocksworld). A genuine, if small,
  performance cost of the record split, not a correctness trade — see
  criterion 2's decomposition above. Candidate mitigation unchanged: Approach
  B (spec §8, propagating `¬is-D(t)` instead of rediscovering the conflict on
  every branch); its un-banking trigger has now fired twice (pre-fix and
  fixed), a stronger signal than before.
- **`20230720-blocksworld`'s own 162 → 190 → 169-row bug** — still
  unexplained beyond the one `shinri-euf`-caused row above; still needs a
  genuine bisect on a 21–53 KB instance. The cheapest standalone reproducer
  remains `blocksworld_from_0_18_1_to_17_2_0_negated_goal_bmc_5.smt2`
  (21,247 B, answers `sat` — wrong, `:status unsat`).
- **QF_DT's remaining `timeout`/`unknown` rows** — 510 timeout (was 507
  baseline, 489 pre-fix), 11 `unknown:sat-budget` (unchanged throughout) —
  out of scope per spec §2, still in the slice-46 queue.

---

## Original slice48 measurement (pre-fix, commit `17f2ac31092a`) — SUPERSEDED, kept for history

**Everything from here to "## References" describes the pre-fix code
(commit `17f2ac31092a`) and is stale for the shipped fix (`f27a340ceb77`).
It is kept, unedited except for this notice and the section labels, because
the regression it found and the fix that followed are the most important
part of this slice's story — see the "Update" section above for the current,
authoritative numbers.**

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

## Success criteria (pre-fix)

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

## The blocksworld premise was wrong (pre-fix measurement; root cause of the one surviving regression identified above)

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

## Oracle evidence (pre-fix; cited, not re-run, in the Update section above)

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

## Queued for the next slice (pre-fix — superseded by the section of the same name in the Update above)

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
  `## 11. Measured outcomes` (both the pre-fix subsection and "Re-measured
  after the fix wave").
- Raw results, pre-fix — `bench/results/slice48/results.jsonl` (8,700 rows,
  git-ignored), rendered report `bench/results/slice48/report.md`.
- Raw results, fixed — `bench/results/slice48b/results.jsonl` (8,700 rows,
  git-ignored), rendered report `bench/results/slice48b/report.md`.
- Task 1's generator failure — commit `90a061b8`. Task 3's `tester_clash` —
  commit `c0957d4b`. Task 2's level-indexed `asserted_testers` — commit
  `e5cc3eea`. Task 4's defensive fence — commit `17f2ac31` (pre-fix HEAD).
  Task 5's whole-branch fix wave (splits `asserted_testers` by consumer,
  removes the pre-fix regression) — commit `f27a340c`. Task 6's final-review
  fix wave (comments and test strength; no executable logic changed outside
  test bodies) — commit `f8b605e9` (current branch HEAD).
- The fix wave's own findings, carried into this report because
  `.superpowers/` is git-ignored and vanishes on merge —
  `.superpowers/sdd/2026-09-10-shinri-slice48-qfdt-tester-disjointness/fix-wave-report.md`
  (the five-variant isolation, the `shinri-euf` root cause, and the 9-line
  reduced repro all come from its §1 and §5).
- The slice-47 report's structure and criterion-decomposition precedent —
  `2026-09-09-smtlib-2024-qfabv-slice47-report.md`.
