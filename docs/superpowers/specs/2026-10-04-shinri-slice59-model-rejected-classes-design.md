# Slice 59 — Classify the `str-model-rejected` population

Status: design approved in chat 2026-10-04. Picks up the slice-58 report's
queue item 1 (`docs/superpowers/research/2026-10-04-smtlib-2024-slice58-member-prefix-report.md`,
§ Queued for the next slice): "Classify the `str-model-rejected` population
… by the first violated assertion and the class shape". Scope ruling (owner,
in chat): keep the classification as shipped instrumentation (a
`fence_detail` carried solver → `--stats` → bench JSONL → report), not a
throwaway probe, so every later slice can report per-class movement.

**Area:** `shinri-theory` (`model.rs`, a diagnostic field on
`ModelBuilder`), `shinri-str` (`lib.rs`, `model_with` records the rebuild
outcome), `shinri-solver` (`lib.rs`, a reject-path classifier and
`last_fence_detail`), `shinri-cli` (`driver.rs`, the `stats:` line),
`shinri-bench` (`runner.rs`, `results.rs`, `report.rs`). No parser, SAT,
Combiner, word-equation, membership, normalize or lowering change. No
verdict change.

## 1. Summary

### 1.1 The population

Slice-58 run (`bench/results/slice58/results.jsonl`): 4,084 rows answer
`unknown:str-model-rejected`.

| logic / family | rows |
| --- | --- |
| QF_SLIA stringfuzz `transformed` | 1,327 |
| QF_SLIA stringfuzz `generated` | 1,212 |
| QF_SLIA Norn `HammingDistance` | 333 |
| QF_S woorpje `track01` | 157 |
| QF_SLIA Jiang `slent` | 111 |
| other (QF_S Jiang `slog`, woorpje `track02–04`, Norn, denghang, …) | 944 |

Corpus status: 446 `sat`, 314 `unsat`, 3,324 unknown. Wall time: median
8 ms, p90 33 ms. Today a row records only the fence name, so nothing says
which assertion failed or why.

### 1.2 The two rejection modes

`Solver::string_model_satisfies` (`crates/shinri-solver/src/lib.rs:1532`)
rejects a model when a top-level assertion

- evaluates to `Some(false)` (**violated**: the model is wrong), or
- evaluates to `None` while the strict gate is on (**unevaluable**: the
  slice-57 rebuild was adopted and set `require_strict_check`, and the
  evaluator cannot decide the assertion: compound arithmetic in
  `eval_num_val`, an operator `eval_bool` does not handle).

The two have different fixes (model construction vs evaluator coverage),
and the first split of the population is between them.

### 1.3 The rebuild outcome

`StrSolver::model_with` (`crates/shinri-str/src/lib.rs:1566`) builds the
default model, then on a violated input equation tries the slice-57
reconciliation rebuild. Four outcomes, none recorded today:

| outcome | meaning |
| --- | --- |
| `not-needed` | the default model holds every input equation |
| `adopted` | the rebuild holds every input equation and `concats_consistent`; strict gate on |
| `rejected` | the rebuild completed but failed `input_eqs_hold` or `concats_consistent` |
| `budget` | `reconciled_values` returned `None` (candidate-trial budget ran out) |

A string-path model that never reaches `model_with`'s check is `not-needed`.

## 2. Scope

In:

- A detail tag `<mode>:<kind>@<rebuild>` computed on the reject path only.
- Plumbing: `Solver::last_fence_detail`, a `detail=` field on the `stats:`
  line, a `fence_detail` JSONL field, a "Fence detail" report section.
- A full-corpus base/after bench run and a research report that ranks the
  classes, names a smallest reproducer per top class with an offline
  class-shape analysis, places the slice-58 guards, rules on the parked
  approach-2 parts and suffix G′, and recommends the next fix slice.

Out:

- Details for any other fence.
- Class-shape fields in the shipped tag (shape is analysed offline in the
  report, on the reproducers).
- A base-vs-after detail diff tool (the report compares by hand, as for
  verdicts today).
- Any change to what the gate accepts or rejects.

## 3. Approaches considered

1. **Separate `detail` field (chosen).** New `detail=` stats field and
   `fence_detail` JSONL field; the verdict key stays
   `unknown:str-model-rejected`, so every base/after comparison since slice
   46, and slice-58 criterion 3, still lines up.
2. **Fold the tag into the fence string** (`str-model-rejected/violated:…`).
   No new field, but one verdict splits into dozens; old and new runs stop
   matching and every fence criterion needs prefix matching. Rejected.
3. **Side-channel stderr line read from `stderr_head`.** `stderr_head` is
   truncated free text; fragile and not something later slices can rely
   on. Rejected.

Tag content: mode and atom kind (computed in the solver evaluator) plus the
rebuild outcome (recorded by `shinri-str`) were chosen over adding a class
shape, which would need a read-only hook into `shinri-str` classes at reject
time. Shape is answered offline in the report.

## 4. Design

### 4.1 Tag grammar

`<mode>:<kind>@<rebuild>`, for example `violated:word-eq@not-needed`,
`unevaluable:len-arith@adopted`.

- `mode` ∈ {`violated`, `unevaluable`}: the result of the **first** failing
  top-level assertion in `lowered` order (deterministic).
- `kind`, from the failing assertion with an outer `Not` stripped and
  recorded as a `not-` prefix:

  | kind | assertion head |
  | --- | --- |
  | `word-eq` | `=` over String operands |
  | `str-diseq` | `distinct` over String operands |
  | `memb` | `str.in_re` |
  | `str-pred` | `str.contains`, `str.prefixof`, `str.suffixof` |
  | `str-order` | `str.<`, `str.<=` |
  | `int-conv` | `str.to_int`, `str.from_int`, `str.to_code`, `str.from_code` occurring in the atom |
  | `len-arith` | an Int/Real comparison or `=` over Int/Real |
  | `bool` | `and`, `or`, `=>`, `ite`, `=`/`xor` over Bool |
  | `other:<op>` | anything else (`<op>` is the SMT-LIB operator name) |

  Precedence: `int-conv` is checked first (any conversion operator anywhere
  in the atom wins, so `(= (str.to_int x) 5)` is `int-conv`, not
  `len-arith`); the rest are by head.

  For `violated`, `kind` names the top-level assertion. For `unevaluable`,
  `kind` names the first leaf atom (in left-to-right descent) whose
  evaluation returned `None`: that leaf is the evaluator gap to fix. A
  `not-` prefix records the polarity of the atom as reached.
- `rebuild` ∈ {`not-needed`, `adopted`, `rejected`, `budget`} (§1.3).

### 4.2 Rebuild outcome (`shinri-theory`, `shinri-str`)

`ModelBuilder` gains `rebuild: RebuildOutcome` (an enum in
`shinri-theory::model`, default `NotNeeded`) with a setter and getter beside
`require_strict_check`/`strict_check_required`. `absorb` keeps the more
informative value, ordered `NotNeeded < Adopted < Rejected < Budget`.
`model_with` sets it on each branch of the existing match. It is a
diagnostic only: no code reads it to choose a verdict or a model.

### 4.3 Classifier (`shinri-solver`)

A reject-path function `model_reject_detail(&lowered, &model, strict,
rebuild) -> String` (with `rebuild = mb.rebuild_outcome()` read beside
`strict_check_required`) re-walks the assertions with the existing `eval_bool` and builds the
tag. It runs only after `string_model_satisfies` returned `false`, so the
accept path is unchanged. A small `kind_of(atom)` maps a term head to §4.1's
vocabulary; the `unevaluable` leaf search is a separate descent that stops at
the first `None` leaf.

`Solver` gains `last_fence_detail: Option<String>` and
`pub fn last_fence_detail(&self) -> Option<&str>`. It is set together with
`last_fence = Some("str-model-rejected")` and cleared where `last_fence` is
cleared (`lib.rs:768`), so a later `check-sat` never carries a stale detail.

### 4.4 CLI (`shinri-cli/src/driver.rs`)

The `stats:` line becomes
`stats: cmd=check-sat wall_ms=… outcome=… fence=… detail=…`, `detail=-`
when absent. The field is appended last; `parse_stats_fence` is unaffected.

### 4.5 Bench (`shinri-bench`)

- `runner.rs`: `parse_stats_detail(stderr) -> Option<String>` (last `stats:`
  line, `-`/absent → `None`), next to `parse_stats_fence`.
- `results.rs`: `Row` gains `fence_detail: Option<String>`, written after
  `fence`; a row without the key parses as `None` (old results files still
  load). `rerun` carries it through.
- `verdict.rs`: unchanged.
- `report.rs`: a "Fence detail" section after "Ranked gaps", rendered only
  when some row has a non-null `fence_detail`: one table per fence, rows =
  tags sorted by total count desc then tag, columns QF_S / QF_SLIA / total /
  example path. A run with no details renders byte-identical to today.

### 4.6 Cost

The classifier runs only on rows already answering `unknown`, once per
rejecting `check-sat`, and is linear in the assertion DAG it re-walks. The
`ModelBuilder` field is one enum. The extra stats field is a few bytes on
stderr, and only with `--stats`.

## 5. What this does not change

Which models the gate accepts, any verdict, any fence name, the verdict key,
"Ranked gaps", or anything on the accept path.

## 6. Tasks

1. `RebuildOutcome` on `ModelBuilder` (+ `absorb`), set in `model_with`.
2. Solver classifier, `last_fence_detail`, reset.
3. CLI `detail=` field.
4. Bench parse, `Row` field (+ backcompat), `rerun` passthrough.
5. Report "Fence detail" section.
6. Bench runs, triage, research report, queue rewrite, §11 outcomes.

## 7. Testing

### 7.1 Unit (`shinri-theory`, `shinri-str`)

- `absorb` keeps the more informative `RebuildOutcome` in both orders.
- `model_with` records each outcome: reuse the slice-57 tests that already
  reach `not-needed`, `adopted` and `budget` (zero trial budget), and add one
  reaching `rejected`.

### 7.2 Unit (`shinri-solver`)

- One test per `kind` in §4.1 for the `violated` mode.
- `unevaluable`: a compound `len-arith` leaf under the strict gate; a leaf
  under an `or` whose other disjunct is false.
- `not-` prefix; `bool` skeleton; first-failing-assertion order (two
  failing assertions, the first decides).
- `last_fence_detail` is cleared on the next `check-sat`.

### 7.3 End to end (`shinri-cli` / `script_e2e`, blocking tier)

- The `slice58_probes::g1_compatible_prefix` script under `--stats` emits
  `fence=str-model-rejected detail=<non-dash>`.
- An accepted `sat` emits `detail=-`.

### 7.4 Bench (`shinri-bench`)

- `parse_stats_detail`: present, `-`, absent, last line wins.
- JSONL round trip with `fence_detail`; an older row without the key
  parses as `None`.
- Report: section present with counts and order on a fixture with details;
  absent (output unchanged) on a fixture without.

### 7.5 Unchanged suites

Every existing solver, str, bench and oracle suite passes unchanged.

## 8. Measurement

Two runs per binary at default limits (20 s, 3072 MB, 6 jobs),
`slice59-base` at the branch point (crates identical to `de96d28`) and
`slice59` at the slice head (scope ruling, owner, in chat 2026-10-04):

- **Strings:** the full QF_S and QF_SLIA corpus (103,335 rows), where every
  row the classifier can touch lives (it runs only behind `on_string_path`).
- **Neutrality sample:** a seeded (seed 59) 2,000-row sample over the other
  seven logics (QF_BVFP, QF_DT, QF_LIA, QF_LRA, QF_UF, QF_UFLIA, QF_UFLRA),
  allocated in proportion to logic size with a floor of 100 rows per logic,
  run from a hard-linked corpus tree so row paths match the main corpus.
  Outside the string path the change is an unread `ModelBuilder` field and
  `detail=-` on the stats line; the sample checks that nothing else moved.
  A full all-logic run (~153,800 rows, ~7–8 h per binary) was considered and
  not chosen.

Every changed verdict is re-run 3× per binary, interleaved, with the bench's
command line (slice-53 triage method).

The research report
`docs/superpowers/research/2026-10-04-smtlib-2024-slice59-model-rejected-classes-report.md`
contains:

1. The ranked tag table, per logic, split by corpus status (`sat`, `unsat`,
   unknown).
2. Top classes: the smallest set covering ≥80% of the population, capped at
   eight. For each, the smallest reproducer by bytes and an offline
   class-shape analysis of it (minted concat, constant head/tail, several
   concats, cycle), traced with throwaway debug output that is not
   committed.
3. Where the slice-58 guards land: `g1`, `g3`, `rf2`, `rf3`; `rf4` is
   `sat-budget` and is noted as outside the population.
4. A ruling per parked item: constant-head strip, cited deep NF on the
   word-equation path, minted length links, suffix G′. Each item either has
   a reproducer now (named) or stays parked.
5. The recommended next fix slice and the rewritten queue.

### Success criteria

| # | criterion | kind |
| --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | hard; any hit stops the slice for a ruling |
| 2 | verdict-neutral on the string runs and the neutrality sample: every changed row is a non-reproducible timing flip (3/3 triage re-runs agree with base) | hard |
| 3 | every `unknown:str-model-rejected` row has a non-null `fence_detail`; no other row has one | hard |
| 4 | serial, interleaved timing on 150 sampled both-`correct` rows per string logic, and on 150 sampled `str-model-rejected` rows (the path the classifier runs on): summed wall time within ±5% of base | hard |
| 5 | `mise run ci` green; oracle suite (`--features oracle`) passes with the slice-58 discovered count (808 passed, 2 skipped) | hard |
| 6 | the report's named classes cover ≥80% of the population, each with a reproducer | hard |

## 9. Queued for the next slice

Written by the measurement report (§8 item 5). Carries slice-58 queue items
2 onward (bare-E and `Not(Eq)` arm removal; axiom memory measurement; solver
gate composes concats first; slice-57 deferred minors) unchanged unless the
classification re-ranks them.

## 10. References

- Slice-58 report, § Queued for the next slice (item 1); slice-58 spec
  `docs/superpowers/specs/2026-10-03-shinri-slice58-member-prefix-design.md`
  (§9).
- Slice-57 spec `docs/superpowers/specs/2026-10-03-shinri-slice57-str-model-reconcile-design.md`
  (the rebuild and strict gate).
- Code:
  - `crates/shinri-solver/src/lib.rs:768` (`last_fence` reset), `:1494`
    (the gate), `:1532` (`string_model_satisfies`), `:1609` (`eval_bool`)
  - `crates/shinri-str/src/lib.rs:1566` (`model_with`)
  - `crates/shinri-theory/src/model.rs:38` (`require_strict_check`), `:62`
    (`absorb`)
  - `crates/shinri-cli/src/driver.rs:163` (`stats:` line)
  - `crates/shinri-bench/src/runner.rs:197` (`parse_stats_fence`)
  - `crates/shinri-solver/tests/slice58_probes.rs:160` (`g1`)

## 11. Measured outcomes

Filled in after the bench runs.
