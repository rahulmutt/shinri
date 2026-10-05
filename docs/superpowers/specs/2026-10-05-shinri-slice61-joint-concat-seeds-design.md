# Slice 61 — Joint seeds for concat-subject memberships

Status: design approved in chat 2026-10-05. Picks up the slice-60 report's
queue items 2 and 3 (`docs/superpowers/research/2026-10-05-smtlib-2024-slice60-head-classes-report.md`,
§ Queued for the next slice; item 1 was closed by the Rule-E full-partition
variant `56997aa`). Scope rulings (owner, in chat): items 2 and 3 are one
mechanism and ship together; item 4 (concat-subject emptiness → `unsat`)
stays queued; this slice is model-side only.

**Area:** `shinri-str` (new `joint_seed.rs`; `model::class_len_in_model`
becomes `pub(crate)`; one call added in `lib.rs`
`model_with`). Tests in `shinri-str` and `shinri-solver`. No parser, SAT,
Combiner, word-equation, Rule-E, emptiness, lowering, model-gate or
bench-tool change.

## 1. Summary

### 1.1 The population

Base `5aa164a` (slice-60 variant): `violated:memb@not-needed` has 432 rows
among the `unknown:str-model-rejected` string rows: Norn 356, Jiang `slog`
44, stringfuzz z3str2 30 (28 of them `regex-035-*`), automatark 1,
denghang 1. The slice-60 trace of 5 Norn HammingDistance rows found no cap
hit; every failing membership has a **concat subject**.

### 1.2 Cause

`model::memb_seeds` (`crates/shinri-str/src/model.rs:467`) seeds only
memberships whose subject is a bare leaf (`if !is_leaf { continue; }`), and
each leaf gets a word for the intersection of its **own** bare memberships.
Nothing chooses a concat's operands jointly against the concat's regex.

- `QF_SLIA/2015-Norn/HammingDistance/norn-benchmark-531.smt2` (z3 `sat`):
  two positive memberships on `(str.++ var_8 "z" var_9)`, one negative on
  `(str.++ "b" var_8 "z" "b" var_9)`, bare `var_8, var_9 ∈ [a-u]*`. The
  leaves are seeded independently; the gate rejects the composed concat
  (`unknown`, `violated:memb@not-needed`, 33 ms).
- `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-035-reverse-fuzz.smt2`
  (z3 `sat`): only `(str.++ y x) ∈ b*`. Neither operand has a bare
  membership, so neither is seeded (same tag, 27 ms).

Seeds enter `string_values`' memo and concats are assembled from their
operands' memo values, so seeding the leaves jointly is sufficient; nothing
downstream changes.

## 2. Scope

In:

- `joint_seed::joint_seeds`, called after `memb_seeds`; its entries override
  the per-leaf seeds for the same leaves (§4).
- Unit tests, a probe file, an oracle file (§7).
- A full-corpus base/after bench run and a research report (§8).

Out (stay queued):

- Item 4: concat-subject memberships with a provably empty intersection
  stay `unknown`.
- Items 5 and 6 (oracle coverage, witness-search cost), the class-2 tag fix
  and length/membership conflict, class 3, candidate (c) for the 10
  HammingDistance gains, and every carried item.
- Retuning `CLASS_SPLIT_CAP`, `MEMB_SEARCH_STEP_CAP` or `FUEL_NODE_CAP`.

## 3. Approaches considered

1. **Joint derivative search over the concat's characters (chosen).** Group
   concat-subject memberships by shared free leaves; one DFS assigns the
   leaves a character at a time while advancing each constraint's
   derivative. Reuses `deriv`, `next_classes`, the dead-state memo and the
   step cap from `search_word`. Most code, but complete within its caps and
   prunes early.
2. **Generate and test.** Enumerate up to K words per leaf from its own
   language and test the cartesian product with `eval_membership`. Small,
   but blind: in HammingDistance the cross-operand constraints decide almost
   everything, so a small K misses and a large K explodes. Rejected.
3. **Push it into the search** (make Rule-E unfolding and the word-equation
   engine produce consistent operand values). The right home for `unsat`
   (item 4), but it is the SAT-order-sensitive machinery that slices 52–60
   kept tripping on. Rejected for this slice.

## 4. Design

### 4.1 Module and entry point

New module `crates/shinri-str/src/joint_seed.rs`:

```rust
pub(crate) fn joint_seeds(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    membs: &[(TermId, bool)],
    m: &ModelBuilder,
) -> FxHashMap<TermId, String>
```

`StrSolver::model_with` (`lib.rs` ~1583) calls it right after `memb_seeds`
with the same arguments and `extend`s the seed map with its result, so a
joint seed replaces the per-leaf seed of the same leaf. `string_values` and
the slice-57 reconcile path (`ReconcileInput.seeds`) consume the merged map
unchanged.

### 4.2 Eligible constraints

A membership `(atom, pos)` of `memb_true` is an eligible constraint iff:

- its subject is a `str.++`; nested concats are flattened into one operand
  list;
- every operand is a string constant or a nullary uninterpreted leaf;
- `regex::extract_const_regex` succeeds on its regex;
- the subject's equality class holds no string constant (the value is then
  dictated elsewhere).

Polarity is folded as everywhere else: `t ∉ R` becomes `t ∈ comp(R)`. A
constraint is `(operands: Vec<Operand>, rex: Rex)` with
`Operand::{Const(String), Leaf(TermId)}`.

Plan Task 0 traces `norn-benchmark-531` to confirm the subject-class check:
if the subject's class also holds minted Rule-E concats, those must not
disqualify it (only a string constant does).

### 4.3 Own languages and groups

- **Own language** of a leaf: the `inter` of its bare-membership regexes,
  collected under `memb_seeds`' rules (leaf subject, constant regex,
  polarity folded). A leaf with none gets Σ* (`regex-035`).
- **Groups:** union-find over leaves that co-occur in an eligible
  constraint. A group is its leaves, its constraints and their own
  languages.
- If any leaf of a group is `model::is_repair_pinned`, the whole group is
  skipped; its leaves keep their `memb_seeds` seeds (today's behaviour).
- A leaf repeated within or across constraints (`x·"a"·x`) is allowed: once
  assigned, later occurrences are fed as forced characters.
- A group yields a word for every leaf or nothing.

### 4.4 The search

**State.** `leaf_idx` (position in a fixed leaf order: first occurrence
walking the group's constraints in `memb_true` order); `own` (the current
leaf's own-language derivative); `rem` (characters left, §4.5); per
constraint `j` a cursor `(op_idx_j, d_j)`, the next unconsumed operand and
the derivative of `R_j` by everything consumed; `assigned` (finished
leaves' words).

**Advance.** At the start and after each leaf finishes, every constraint
consumes operands while its next operand is a `Const` or an assigned
`Leaf`, one `deriv` per character. A `d_j` that becomes `Empty` or exceeds
`FUEL_NODE_CAP` kills the branch.

**Character step for leaf `x`.** Active constraints are those whose next
operand is `x`. Classes are `next_classes(&inter([own, d_active…]))`, which
is the common refinement because `head_bounds` collects every `Inter`
member's head bounds. `None` (past `CLASS_SPLIT_CAP`) is a dead end, not a
verdict. Per class the witness is the smallest non-surrogate code point;
pure-surrogate classes are skipped (as in `search_word`). The character
advances `own` and every active `d_j`. A constraint waiting on a different
unassigned leaf is not advanced and consumes `x`'s whole word later in
*Advance*; it does not prune `x`'s characters, which costs search time
only.

**Leaf end.** When the leaf ends (§4.5), require `nullable(own)`, step each
active constraint past the `x` operand, run *Advance*, move to the next
leaf.

**Success.** All leaves assigned, every cursor past its last operand, every
`d_j` nullable.

**Mechanics** (copied from `search_word`): an explicit frame stack (no
recursion); a `dead` memo keyed on `(leaf_idx, rem, own, d_1..d_k)`; a step
cap `JOINT_SEARCH_STEP_CAP = MEMB_SEARCH_STEP_CAP` (10,000) per pass. Cap
hit or exhaustion: the pass finds nothing.

### 4.5 Length policy

1. **Pass 1, model lengths.** Each leaf's length is fixed at
   `model::class_len_in_model(leaf)` (made `pub(crate)`), the read
   `memb_seeds` uses; `rem`
   counts down and the leaf ends at `rem == 0`. These lengths respect every
   length pin the arith model satisfied.
2. **Pass 2, free lengths**, only if pass 1 finds nothing. Leaf lengths are
   free: at each character step for `x`, ending `x` is a choice whenever
   `nullable(own)` holds, tried before extending (bias to short words). One
   budget bounds the total leaf characters of the group:
   `JOINT_FREE_LEN_CAP = 64`; `rem` in the memo key becomes the remaining
   budget. Own step cap of 10,000.

A pass-2 word may violate a length assertion (`len x = 5`); the gate then
rejects it and the row stays `unknown`, the same trade `memb_seeds`'
shortest-word fallback makes. The gate evaluates `str.len` from the string
value (`shinri-solver/src/lib.rs` `eval_num_val`), so it catches this.

### 4.6 Soundness

Seeds are candidates only; the post-solve gate re-evaluates every
assertion. A search bug can turn a row `unknown`, never into a wrong `sat`.
The unit sweep (§7.1) independently re-checks every returned word set with
`eval_membership`.

### 4.7 Cost

Runs only in `model_with`, after the solver reached SAT, and only when an
eligible group exists. Rows without concat-subject memberships pay one scan
of `memb_true`. The SAT search, conflicts, Rule-E and emptiness are
untouched, so the slice-60 search-order churn mechanism does not apply.
Worst case per group: 2 passes × 10,000 steps × k derivatives, the order of
today's per-leaf `search_word`. Measured per §8.

## 5. What this does not change

`memb_seeds`, `search_word`, `search_shortest`, `next_classes`,
`rule_e_classes`, Rule-E, the slice-28 emptiness conflict, the gate and the
reconcile acceptance rules. A group that is ineligible, pinned or not
solved within the caps leaves the seed map exactly as `memb_seeds` built it.

## 6. Tasks

Ordered; the implementation plan details them.

0. Trace `norn-benchmark-531` and `regex-035-reverse-fuzz` at `5aa164a`
   (throwaway `eprintln!`s, reverted): subject class contents, model
   lengths of the leaves. Fix §4.2's subject-class check accordingly.
1. `joint_seed.rs`: constraint extraction, own languages, grouping (§4.2,
   §4.3) with unit tests.
2. The search, pass 1 (§4.4, §4.5) with unit tests and the sweep.
3. Pass 2 (§4.5) with unit tests.
4. Wire into `model_with`; probes (§7.2).
5. Oracle file (§7.3); gates.
6. Bench run and report (§8).

## 7. Testing

### 7.1 Unit (`shinri-str/src/joint_seed.rs`, blocking tier)

- **Grouping and eligibility.** Two constraints sharing `x` form one group;
  disjoint leaves form two; a pinned leaf skips its whole group; a non-leaf
  operand makes its constraint ineligible; a subject whose class holds a
  constant is skipped.
- **Search shapes.**
  - `regex-035`: `y·x ∈ b*`, no bare memberships.
  - The `norn-531` group inlined: two positive constraints, one negated,
    bare `[a-u]*`.
  - Repeated leaf: `x·"a"·x`.
  - Waiting constraint: `x·y ∈ R1` with `y·x ∈ R2`.
  - Pass-2 fallback: model lengths infeasible, free lengths feasible.
  - Cap hit: empty result.
- **Sweep.** A seeded deterministic generator (no new dependency) of a few
  thousand small groups over a 2–3 letter alphabet:
  - soundness: every returned word set satisfies every constraint and own
    language under `eval_membership`;
  - completeness: when no cap is hit, the search finds a solution iff
    brute-force enumeration up to total length 6 does.

### 7.2 Probes (`shinri-solver/tests/slice61_probes.rs`, blocking tier)

Slice-53 style: each `sat` case has a sibling that must not answer `sat`.

- `norn-benchmark-531` (inlined) answers `sat`; its `get-value` witness
  satisfies every assertion.
- `regex-035-reverse-fuzz` (inlined) answers `sat`.
- Jointly empty group (`x·y ∈ a*`, `x ∈ b+`): not `sat` (stays `unknown`;
  item 4 is queued).
- Length-pinned case that only pass 2 could satisfy: not a `sat` whose
  witness breaks the pin.

### 7.3 Oracle (`shinri-solver/tests/joint_seed_oracle.rs`, `--features oracle`)

Every §7.2 script plus seeded generated concat-subject scripts (1–3 leaves,
constants between them, 1–3 constraints with mixed polarity, optional bare
memberships and length pins) run against z3. Any shinri `sat`/`unsat` must
agree with z3; every `sat` witness is re-checked; shinri `unknown` is
allowed. The discovered count must be above zero and the suite total ≥ 831
plus this slice's oracle tests.

### 7.4 Unchanged suites

All existing `shinri-str` and `shinri-solver` tests pass without edits.

## 8. Measurement

Same harness and flags as slice 60: full QF_S and QF_SLIA, plus the seeded
neutrality sample for QF_BVFP, QF_DT, QF_LIA, QF_LRA, QF_UF, QF_UFLIA,
QF_UFLRA; base binary `5aa164a`; `--timeout 20 --mem-mb 3072 --jobs 6`.

The report (`docs/superpowers/research/YYYY-MM-DD-smtlib-2024-slice61-joint-concat-seeds-report.md`)
gives:

1. Verdict changes by `fence_detail` tag and by family (Norn, `slog`,
   z3str2 `regex-035-*`), with `correct` and `unverified` counted
   separately.
2. For a seeded sample of changed rows, whether pass 1 or pass 2 produced
   the adopted seed, from a throwaway trace build.
3. Triage of every changed row (3/3 re-runs).
4. Timing per §Success criteria, plus per-row timings for newly-`correct`
   rows.
5. The rewritten queue.

### Success criteria

| # | criterion | kind |
| --- | --- | --- |
| 1 | 0 rows `* → wrong`; 0 wrong answers in triage re-runs | hard; any hit stops the slice for a ruling |
| 2 | `violated:memb@not-needed` shrinks by ≥ 20% (≥ 87 rows) of its base count (432), those rows moving to `correct` | hard |
| 3 | no `correct → non-correct` change that reproduces in 3/3 triage re-runs | hard |
| 4 | serial, interleaved timing on 150 sampled both-`correct` rows per string logic: summed wall time within ±5% of base; any reproducible slowdown on newly-`correct` rows is reported | hard |
| 5 | `mise run ci` green; oracle suite passes with a discovered count ≥ 831 plus this slice's oracle tests | hard |
| 6 | neutrality sample: no verdict change other than non-reproducible timing flips | hard |

Criterion 2's bar is modest on purpose: most Norn rows have corpus status
`unknown`, so they count as `correct` only where z3 agrees within 20 s.

## 9. Queued for the next slice

Written by the measurement report (§8 item 5). Carries slice-60 queue items
4 onward and the candidate (c) note, re-ranked on the new `fence_detail`
counts.

## 10. References

- Slice-60 report, § Class 1: what is left; § Queued for the next slice
  (items 2–4); § Follow-up: Rule-E full-partition variant.
- Slice-60 spec `docs/superpowers/specs/2026-10-04-shinri-slice60-head-classes-design.md`
  (measurement harness, criteria format).
- Code:
  - `crates/shinri-str/src/model.rs:56` (`class_len_in_model`), `:91`
    (`string_values`), `:448`
    (`is_repair_pinned`), `:467` (`memb_seeds`)
  - `crates/shinri-str/src/lib.rs` ~1583 (`model_with`)
  - `crates/shinri-str/src/regex.rs:331` (`deriv`), `:422` (`head_bounds`),
    `:456` (`next_classes`), `:646` (`search_word`), `:387`
    (`eval_membership`)
  - `crates/shinri-str/src/memb.rs` ~636 (slice-28 emptiness grouping)
  - `crates/shinri-solver/src/lib.rs` `eval_num_val` (gate `str.len`)
