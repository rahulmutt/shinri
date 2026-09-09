# Slice 47 — QF_ABV wrong-`sat`: a model gate on the array layer, then the fixes it names

**Status:** design
**Date:** 2026-09-09
**Area:** `shinri-abv` (new `validate` module; `check::accessed_indices`),
`shinri-solver` (`abv_stage::solve_qfabv_with_models`, the `lib.rs` fence
table, the `qfabv_oracle` generator). No new crate, no new theory slot, no
parser surface change, no `Combiner` change.
**Predecessors:** slice 46 measured the defect
(`docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md § Next slices`,
rank 1). The array engine itself dates to
`docs/superpowers/specs/2026-06-23-shinri-qfabv-design.md`; slices 44–45 fixed
uninterpreted-application congruence in the blaster and did **not** touch this
cluster.

## 1. Summary

The first full SMT-LIB 2024 run reports **359 wrong answers in QF_ABV**, every
one `:status unsat` answered `sat`; 297 carry an in-run z3 `unsat` and the
remaining 62 were hand-adjudicated at 120 s (18 decided against shinri, 44
undecided by both oracles). Families: `dwp_formulas` 283, `brummayerbiere` 69,
`brummayerbiere2` 5, `calc2` 2. Bucket key:
`docs/superpowers/research/2026-09-09-smtlib-2024-baseline-report.md
› ## Wrong answers` (the QF_ABV rows).

Both reproduce on `8a61289a`:

```
$ target/release/shinri bench/corpus/QF_ABV/brummayerbiere/bubsort002un.smt2
sat            # :status unsat, in-run z3 unsat
$ target/release/shinri bench/corpus/QF_ABV/brummayerbiere/wchains002ue.smt2
sat            # :status unsat, in-run z3 unsat
```

They are **structurally different shapes**, which is the fact that shapes this
slice:

* `bubsort002un.smt2` (1,260 B) — 4 `select`s over a 2-deep `store` chain.
  The read-over-write and functional-consistency rules are both in play.
* `wchains002ue.smt2` (1,421 B) — **16 `store`s and zero `select`s**: pure
  store-chain equality.

The second shape has a nameable defect. `check::extensionality`'s positive
branch (`crates/shinri-abv/src/check.rs:125`) enforces array agreement only
over `accessed_indices`, and `accessed_indices`
(`crates/shinri-abv/src/check.rs:99`) is built **solely from `c.selects`**:

```rust
fn accessed_indices(ctx: &Context, c: &Collected, a: TermId, b: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    for &sel in &c.selects {
        if let Some((base, idx)) = select_parts(ctx, sel) {
            if base == a || base == b { out.push(idx); }
        }
    }
    out
}
```

With no selects the list is empty, the `Some(true)` branch emits no lemmas at
all, and every array-equality proxy is a **free Boolean** the SAT layer may set
at will. Store indices are never added to the index set. The negative branch
mints a witness, so array *dis*equality is enforced and array *equality* is
not.

The `bubsort` shape is **not yet diagnosed**. Two hypotheses are recorded in §9,
written down so task 3 can confirm or discard them; this slice bisects rather than guesses.

Because the number of independent causes is unknown, the slice restores
soundness **first**, with a model gate that is independent of how many causes
are later found, and then uses that gate as the instrument for finding them.

Two suspects were investigated and **closed** before this design:

* `check::array_pair` (`check.rs:71`) treats `Eq` and `Distinct` alike, which would
  invert the proxy's meaning on a `distinct` atom. `normalize_array_atoms`
  already desugars every array `Distinct` to `(not (= a b))` **before**
  collection and abstraction (`crates/shinri-abv/src/normalize.rs:1`–`:22`),
  so no `Distinct` array atom ever reaches `array_pair`. Not a defect.
* `distinct` on arrays does not appear in any of the three smallest named
  reproducers.

## 2. Scope

**In scope:** the 359 QF_ABV wrong-`sat` rows (rank 1 of the slice-46 queue).

**Out of scope, and reported unchanged in the closing re-run:**

* the 5,787 `non-BV builtin reached blast_word` panics (rank 4) — 38 % of
  QF_ABV, its own slice;
* the 2,290 stack overflows (rank 5);
* the 383 QF_ABV `parse-error`/`oom`/`timeout` rows;
* the QF_DT (328) and tail (55) wrong answers (ranks 2 and 3).

A QF_ABV re-run measures all of these. The success criteria in §7 bind only
the wrong-answer, correct-answer and timeout counts; every other column is
reported for the record, not gated.

## 3. The gate

### 3.1 Why the array layer alone is sufficient

`abstract_arrays` (`crates/shinri-abv/src/abstraction.rs:38`) produces the
abstraction by a single memoized substitution (`subst`, `:72`) that replaces

* every `select` subterm by a fresh read var of the element sort, and
* every array-eq atom by a fresh Bool proxy,

and rebuilds every other node **structurally unchanged**. The SAT solve
therefore already guarantees the Boolean/BV skeleton of the original
assertions is satisfied under the produced model. The only freedom the
abstraction introduces is in the read vars and the proxies: they are
unconstrained constants that the refinement lemmas are supposed to pin down.

Consequently a spurious `sat` can arise in exactly one way — the model gives
read vars or proxies values that **no actual array function can produce**.
Validating the array axioms is therefore sufficient; re-evaluating the whole
formula would re-derive a fact the SAT solve already establishes, at the cost
of a second implementation of BV semantics to keep in sync with the blaster.

This argument is load-bearing, so §3.4 pins the grammar it assumes and makes
every term outside that grammar a conservative rejection.

### 3.2 Array values

Evaluate every array-sorted term to a concrete finite function
`(default: Integer, overrides: BTreeMap<Integer, Integer>)`:

* a **declared array constant** — its `ArrayModel`
  (`crates/shinri-abv/src/model.rs`), already assembled on the SAT path for
  `get-model`; `points` become the overrides and `default` the default;
* `store(A, i, e)` — the value of `A` with the single point
  `val(i) ↦ val(e)` inserted (replacing any existing entry at that index);
* anything else — conservative rejection, per §3.4.

Index and element values come from `bridge.value_bv`, which blasts on demand
and reads the current SAT model for **any** BV-sorted term
(`crates/shinri-solver/src/abv_stage.rs:580`–`:611`), so no separate BV
evaluator is needed.

### 3.3 The three checks

**C1 — read soundness.** For every `(sel, r)` in `abs.read_of` where
`sel = select(A, i)`: require

```
lookup(value_of(A), val(i)) == val(r)
```

where `lookup` returns the override at that index if present and the default
otherwise. This is the array axiom itself, so it subsumes both functional
consistency and read-over-write: it holds for *every* pair of reads and every
store chain, not only for the pairs some lemma rule happened to enumerate.

**C2 — equality soundness.** For every array-eq atom `(= a b)` with proxy `p`:
require `bridge.value_bool(p)` to agree with whether `value_of(a)` and
`value_of(b)` are equal **as functions** — equal defaults, and equal lookups
across the union of the two override index sets. (Two finite-support functions
over a BV index space agree everywhere iff they agree on the union of their
supports and share a default; the support is always a strict subset of the
`2^w` index space at the widths in this corpus, and §3.4 rejects the degenerate
case rather than reasoning about it.)

C2 is precisely the check `wchains002ue` fails today: with zero selects nothing
constrains the proxies, so the model asserts an array equality that its own
array values contradict.

**C3 — proxy totality.** Every proxy in `abs.eq_proxy` must have a value in the
model. A proxy with no assignment means the abstraction's Boolean skeleton did
not force it, which is the same unconstrained-freedom failure as C2; treat a
missing value as a rejection rather than as "don't care".

If C1, C2 and C3 all hold, the model is a genuine QF_ABV witness and the `sat`
stands. If any fails, the `sat` is spurious.

### 3.4 The grammar, and conservative rejection

The §3.1 argument assumes every array-sorted term is a declared array constant
or a `store` chain over one. The validator walks each array-sorted term and
**rejects** (returns "cannot validate", which the caller treats exactly as a
failed check) when it meets an array-sorted term that is neither, including:

* an array-sorted `ite`;
* an array-sorted uninterpreted application, nullary or otherwise;
* an array whose `ArrayModel` could not be assembled;
* an array-eq atom whose operands have different index or element widths;
* an index or element term for which `bridge.value_bv` returns `None`;
* an array whose override support size equals `2^index_width` (the degenerate
  case C2's argument excludes).

Rejecting here costs at most a `sat` → `Unknown` downgrade on a shape the
engine may well be handling correctly. That is the right trade: an unfenced
fall-through on an unanticipated shape is how this class of bug reaches a user
in the first place. Each bullet gets its own unit fence (§6.1) so the list is
executable rather than aspirational.

### 3.5 Where it hooks

Inside `solve_qfabv_with_models`
(`crates/shinri-solver/src/abv_stage.rs:706`–`:748`), immediately after
`refine` returns `Sat` and in the same block that already builds the array
models, while `bridge`, `c` and `abs` are still live — the array models the
gate needs are the ones being built there anyway.

`AbvOutcome` gains a variant for the rejection so the signal survives the
return. `crates/shinri-solver/src/lib.rs:976` maps it to
`SolveOutcome::Unknown` with

```rust
self.last_fence = Some("abv-model-rejected");
```

joining the existing `abv-fenced` / `abv-uf-args` / `abv-uf-budget` /
`abv-engine` fences. The name and the mechanism mirror `str-model-rejected`
(`crates/shinri-solver/src/lib.rs:1474`), which exists for exactly this reason
on the string path: a deliberately incomplete engine that admits a SAT the
model builder cannot realise, caught by a post-solve gate rather than reported.

On rejection the gate also returns **which check failed and on which term**.
That is not diagnostics for its own sake — it is the instrument §5 uses to
bisect, and without it "which of the four families is still broken?" can only
be answered by a full corpus re-run against z3.

### 3.6 Cost

One pass over `abs.read_of` and `abs.eq_proxy` per QF_ABV `sat`, reusing
already-computed array models and already-blasted BV values. QF_ABV's median
solve is 12 ms and its p90 is 173 ms, so the pass is noise. §7 gates on the
measured p90 anyway rather than on this assertion.

## 4. The fix, so far as it is known

**Confirmed:** `accessed_indices` (`check.rs:99`) must also collect the store
index terms along the store chains of both operands, not only the indices of
selects whose base is syntactically `a` or `b`. For `a = b` where either side
is a store chain, agreement has to be enforced at every index either chain
writes; today those indices are invisible to the positive branch, which is why
a formula with no selects at all constrains nothing.

**Not yet diagnosed:** the `bubsort` shape. §6 records the hypotheses; task 3
bisects with the §3.5 rejection reason and fixes what it finds. This spec
deliberately does not pre-commit a fix for a cause it has not observed — the
recorded history here is that plan-stage code sketches ship soundness bugs.

## 5. Tasks

**Task 1 — extend the oracle generator, and watch it fail.**
`crates/shinri-solver/tests/qfabv_oracle.rs` equates only **bare array
constants** (`arrays[0]`, `arrays[1]`, `arrays[2]` at `:234`, `:239`, `:246`,
`:254`) and emits `Store` only as the direct operand of a `Select`
(`:177`–`:181`). The store-chain-equality shape is therefore unreachable, which
is how 359 wrong answers survived a green oracle suite. Add:

* array equalities whose operands are `store` chains of depth ≥ 2, over both
  the same and different base arrays;
* an instance shape with **zero selects**, so the `wchains` case is generated;
* store chains that write the same index twice (later write wins).

**Acceptance: the extended generator must FAIL on pre-slice `main`.** A green
run means the generator still does not reach the defect and the task is not
done.

**Task 2 — the gate.** New `crates/shinri-abv/src/validate.rs` implementing
§3, the `AbvOutcome` variant, the `abv_stage` hook, the `abv-model-rejected`
fence, and the §6.1 unit fences. After this commit shinri is **sound** on all
359 rows regardless of whether any later task succeeds.

**Task 3 — bisect and fix.** Drive the §3.5 rejection reason over the five
named reproducers (§8), fix each cause it names, starting with the §4
confirmed one. Each fix lands with a regression pin (§6.2).

**Task 4 — measure.**

```
BENCH_LOGICS=QF_ABV BENCH_RUN_ID=slice47 mise run bench-run
BENCH_RUN_ID=slice47 mise run bench-report
```

compared against the committed `baseline-8de004d44944` numbers. Iterate tasks
3 and 4 until §7 is met.

## 6. Testing

### 6.1 Fences for the gate

One unit test per §3.4 bullet, each constructing the term shape directly and
asserting the gate rejects rather than passes; one test each for C1, C2 and C3
rejecting a hand-built spurious model; and one test that a genuine model
passes all three (so the gate is not vacuously rejecting everything).

### 6.2 Regression pins

An e2e pin per fixed cause, driven from the smallest reproducer of its shape,
asserting `unsat`. `wchains002ue` and `bubsort002un` are both small enough to
inline as literal SMT-LIB.

### 6.3 Oracle

```
cargo nextest run -p shinri-solver --features oracle -E 'test(qfabv)'
```

`--features oracle` is **mandatory** — without it the suite silently runs 0
tests and reads as green. Confirm a **non-zero discovered count** before
treating the result as coverage; the expression form `-E 'test(...)'` is
required on the pinned nextest 0.9.140, where a positional `mod::name` filter
matches nothing.

Because this slice changes `shinri-abv` and the shared `abv_stage` bridge, the
closing oracle run is the **full unfiltered** suite, not the filtered one — a
filtered run has previously skipped the file that would have caught a
regression.

### 6.4 Tiers and hygiene

Unit and e2e tests run on the blocking PR tier and must stay inside its
10–15 min budget; the QF_ABV re-run is a manual `bench-*` task and never
enters `ci`. `cargo fmt --all` and `mise run lint` before push.

## 7. Success criteria

1. **QF_ABV `wrong` = 0** in the task-4 re-run, against 359 at baseline.
2. **QF_ABV `correct` ≥ 8,454**, the baseline count. A validator that
   over-rejects shows up here as `correct` → `unknown`: sound, but a real
   regression, and invisible without this second criterion.
3. **QF_ABV `timeout` ≤ 361**, the baseline count. Widening the extensionality
   index set over long store chains is the plausible way this slice buys
   soundness with wall-clock; `calc2_sec2_shifter_bmc10.atlas.smt2` (129,767 B)
   is the shape that would show it first.
4. `abv-model-rejected` fires on **0 rows** in the closing re-run. A non-zero
   count is not a failure — it is sound, and it is the honest report that a
   cause remains unfound — but it must be reported with its row count and its
   families, and queued as a follow-up slice rather than left unstated.
5. The extended generator failed on pre-slice `main` (task 1) and passes after
   task 3, with its discovered test count recorded.
6. Panic, parse-error and oom counts reported unchanged; any movement in them
   is explained.

Criteria 1–3 are measured numbers from a committed run report, not
code-complete claims.

## 8. Named reproducers

All paths relative to `bench/corpus/`.

| shape | file | size | evidence |
| --- | --- | ---: | --- |
| store chain, 0 selects | `QF_ABV/brummayerbiere/wchains002ue.smt2` | 1,421 B | in-run z3 `unsat` |
| selects over nested stores | `QF_ABV/brummayerbiere/bubsort002un.smt2` | 1,260 B | in-run z3 `unsat` |
| `dwp_formulas` (283 rows) | `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_chgrp.i_ring_empty.il.wp.smt2` | 1,472 B | in-run z3 `unsat` |
| `brummayerbiere2` | `QF_ABV/brummayerbiere2/countbitstable016.smt2` | 11,203 B | z3 `unsat` at 120 s |
| `calc2`, size stress | `QF_ABV/calc2/calc2_sec2_shifter_bmc10.atlas.smt2` | 129,767 B | in-run z3 `unsat` |

## 9. Hypotheses recorded, not adopted

Two candidate causes for the `bubsort` shape, written down so task 3 can
confirm or discard them rather than rediscover them. **Neither is a finding.**

1. `functional_consistency` (`check.rs:40`) relates two selects only when
   their base arrays are **syntactically identical** (`if ax != ay { continue }`).
   That is sound by design only if read-over-write and extensionality together
   cover every other route by which two array terms can be equal.
2. `refine` (`crates/shinri-abv/src/driver.rs:85`) returns `Sat` when a round
   adds no **new** lemma. That is a fixpoint on the lemma set, not on the
   axioms, so it is correct only if the per-round checks are exhaustive for the
   current model. §3's gate makes a premature `Sat` here surface as `Unknown`
   rather than as a wrong answer, which is the point of landing the gate first.

## 10. References

* Slice-46 baseline and ranked queue —
  `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md § Next slices`,
  rank 1.
* Per-row evidence —
  `docs/superpowers/research/2026-09-09-smtlib-2024-baseline-report.md
  › ## Wrong answers`.
* The array engine's original design —
  `docs/superpowers/specs/2026-06-23-shinri-qfabv-design.md`.
* The string-path precedent for a post-solve model gate —
  `crates/shinri-solver/src/lib.rs:1474` (`str-model-rejected`).
