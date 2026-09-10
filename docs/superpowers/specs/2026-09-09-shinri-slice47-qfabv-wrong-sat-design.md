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

Neither shape is yet diagnosed, and the reason is worth recording because an
earlier draft of this spec got it wrong.

`wchains002ue` asserts a store-chain **dis**equality, not an equality. Its
single assert is

```
(not (= (bvand (bvand (bvnot (ite (= CHAIN1 CHAIN2) #b1 #b0)) ...) ...) #b0))
```

so the model is forced to set the array-eq proxy **false**. `CHAIN1` and
`CHAIN2` are 8-deep `store` chains over the *same* base `a1`, writing the same
eight `(index, value)` pairs in opposite orders; the instance is `unsat`
because those writes commute under the formula's alignment constraints on `v6`
and `v7`. A false proxy routes through `extensionality`'s **negative** branch
(`crates/shinri-abv/src/check.rs:153`), which mints a witness index and emits
`p ∨ (a[w] ≠ b[w])` — that branch **is** implemented.

There is a real latent defect in the positive branch —
`accessed_indices` (`crates/shinri-abv/src/check.rs:99`) builds the
extensionality index set **solely from `c.selects`**:

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

so with no selects the `Some(true)` branch emits nothing and a *positively*
asserted array equality is unconstrained. But that is **not** what
`wchains002ue` exercises, and this spec does not claim it as the cause of any
measured row. It is a defect to fix and fence on its own terms (§4), not a
diagnosis.

§9 records two hypotheses for the shapes that *are* measured. Both are
hypotheses.

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

### 3.2 Arrays are PARTIAL: what a model actually pins

The obvious move — reuse `array_model` (`crates/shinri-abv/src/model.rs:108`)
— is **wrong**, twice over, and the validator must not do it:

* it pins `default: Integer::from(0u64)` unconditionally, which is a
  *rendering* choice for `get-model` output, not a semantic commitment. The
  model does not claim unwritten entries are zero;
* it silently drops conflicting reads (`model.rs:136`, `if !seen.contains(&iv)`
  — first occurrence wins), so it would **mask** exactly the
  functional-consistency violations C1 exists to catch.

The correct notion is a **partial** map. Only indices touched by a read or a
store are pinned; every other entry is free, and a free entry can be given any
value, so it can never witness a violation.

For an array-sorted term `A`, compute `base(A)` and `pins(A)`:

* `A` a declared array constant — `base(A) = A`, and
  `pins(A) = { val(i) ↦ val(read_of[sel]) }` over every `sel = select(A, i)`
  in `abs.read_of`. Two selects on `A` whose index values coincide but whose
  read values differ are a **C1 violation**, not a first-wins dedup;
* `A = store(B, i, e)` — `base(A) = base(B)` and
  `pins(A) = pins(B)` with `val(i) ↦ val(e)` overriding any existing entry;
* anything else — conservative rejection, per §3.4.

Index and element values come from `bridge.value_bv`, which blasts on demand
and reads the current SAT model for **any** BV-sorted term
(`crates/shinri-solver/src/abv_stage.rs:580`–`:611`), so no separate BV
evaluator is needed.

### 3.3 The checks — reject only DEFINITE violations

The governing rule: the gate rejects only when the model is **definitely** not
realizable. Where the pinned data leaves an entry free, the model has genuine
freedom and the gate must stay silent. A gate that rejected on
underdetermination would turn correct answers into fenced unknowns — sound,
but the regression §7's criterion 2 exists to catch.

**C1 — read soundness.** For every `sel = select(A, i)` with read var `r`: if
`pins(A)` has an entry at `val(i)`, require it to equal `val(r)`. No entry
means no constraint.

This is the array axiom itself, so it subsumes both functional consistency and
read-over-write: for `A` a bare constant it is the functional-consistency
conflict check, and for `A` a store chain it is read-over-write, unfolded to
the bottom of the chain in one step rather than one level per refinement round.

**C2-pos — a positively asserted equality that the pins refute.** For an
array-eq atom `(= a b)` whose proxy is **true**: reject if there is an index
`k` at which `pins(a)` and `pins(b)` are **both** defined and differ. If only
one side is pinned at `k` the other side is free there, so the equality is
still satisfiable and the gate stays silent.

**C2-neg — a negatively asserted equality that the pins force.** For an
array-eq atom `(= a b)` whose proxy is **false**: reject if the two arrays are
**definitely equal**, which holds when

1. `base(a) == base(b)`, and
2. every index in `keys(pins(a)) ∪ keys(pins(b))` is pinned on **both** sides
   with equal values.

Under those two conditions the arrays agree at every pinned index and both fall
through to the *same* base everywhere else, so no assignment to the free
entries can separate them — the disequality is unsatisfiable. A one-sided pin
at any index leaves that entry free on the other side, the arrays can be
separated there, and the gate stays silent.

C2-neg is the check `wchains002ue` needs: its two chains share the base `a1`
and write the same index set, so their pins coincide and the asserted
disequality is definitely violated.

**C3 — proxy totality.** Every proxy in `abs.eq_proxy` must have a value in the
model. A proxy with no assignment means the abstraction's Boolean skeleton did
not force it, which is the same unconstrained-freedom failure as C2; treat a
missing value as a rejection rather than as "don't care".

If C1, C2-pos, C2-neg and C3 all pass, the model is a genuine QF_ABV witness
and the `sat` stands. If any fails, the `sat` is spurious.

### 3.4 The grammar, and conservative rejection

The §3.1 argument assumes every array-sorted term is a declared array constant
or a `store` chain over one. The validator walks each array-sorted term and
**rejects** (returns "cannot validate", which the caller treats exactly as a
failed check) when it meets an array-sorted term that is neither, including:

* an array-sorted `ite`;
* an array-sorted uninterpreted application, nullary or otherwise;
* an array-eq atom whose operands have different index or element widths;
* an index or element term for which `bridge.value_bv` returns `None`, so the
  pin cannot be computed;
* a `store` chain that bottoms out in anything other than a declared array
  constant.

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

## 4. The fixes, so far as they are known

**No cause of a measured wrong answer is confirmed.** §1 explains why the
earlier candidate does not survive contact with its reproducer. Task 3 bisects
with the §3.5 rejection reason and fixes what it finds; §9 records the
hypotheses so they are confirmed or discarded rather than rediscovered.

One **independent latent defect** is confirmed and is fixed on its own terms,
not as a diagnosis: `accessed_indices` (`crates/shinri-abv/src/check.rs:99`)
must also collect the store index terms along the store chains of both
operands, not only the indices of selects whose base is syntactically `a` or
`b`. Today a positively asserted equality between two store chains with no
selects over them is enforced at zero indices. No row in the measured 359 is
known to depend on this; it gets a generator shape (§5 task 1) and a unit
fence (§6.1), and if it turns out to fix measured rows, so much the better.

This spec deliberately does not pre-commit a fix for a cause it has not
observed. The recorded history here is that plan-stage code sketches ship
soundness bugs.

## 5. Tasks

**Task 1 — extend the oracle generator, and watch it fail.**
`crates/shinri-solver/tests/qfabv_oracle.rs` equates only **bare array
constants** (`arrays[0]`, `arrays[1]`, `arrays[2]` at `:234`, `:239`, `:246`,
`:254`) and emits `Store` only as the direct operand of a `Select`
(`:177`–`:181`). The store-chain-equality shape is therefore unreachable, which
is how 359 wrong answers survived a green oracle suite. Add:

* array equalities whose operands are `store` chains of depth ≥ 2, over both
  the same and different base arrays;
* array **dis**equalities between two store chains over the **same** base that
  write the same index set in different orders — the `wchains002ue` shape, and
  the one C2-neg exists for;
* an instance shape with **zero selects**, so both chain shapes are generated
  with no read to rescue them;
* store chains that write the same index twice (later write wins).

**Acceptance: the extended generator must FAIL on pre-slice `main`.** A green
run means the generator still does not reach the defect and the task is not
done.

**Task 2 — the gate.** New `crates/shinri-abv/src/validate.rs` implementing
§3, the `AbvOutcome` variant, the `abv_stage` hook, the `abv-model-rejected`
fence, and the §6.1 unit fences. After this commit shinri is **sound** on all
359 rows regardless of whether any later task succeeds.

**Task 3 — bisect and fix.** Drive the §3.5 rejection reason over the five
named reproducers (§8), fix each cause it names. Also land the §4 latent
`accessed_indices` fix, which is independent of the bisect. Each fix lands with
a regression pin (§6.2).

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
asserting the gate rejects rather than passes. One test each for C1, C2-pos,
C2-neg and C3 rejecting a hand-built spurious model.

Then the tests that matter more, because §3.3's whole design is "reject only
definite violations" and the failure mode is over-rejection:

* C1 stays silent when `pins(A)` has no entry at the read's index;
* C2-pos stays silent when only **one** side is pinned at the differing index;
* C2-neg stays silent when the two chains have **different** bases, and again
  when they share a base but some index is pinned on one side only;
* a genuine model passes every check, so the gate is not vacuously rejecting.

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
| store-chain **dis**equality, same base, 0 selects | `QF_ABV/brummayerbiere/wchains002ue.smt2` | 1,421 B | in-run z3 `unsat` |
| selects over nested stores | `QF_ABV/brummayerbiere/bubsort002un.smt2` | 1,260 B | in-run z3 `unsat` |
| `dwp_formulas` (283 rows) | `QF_ABV/dwp_formulas/try5_small_difret_functions_wp_chgrp.i_ring_empty.il.wp.smt2` | 1,472 B | in-run z3 `unsat` |
| `brummayerbiere2` | `QF_ABV/brummayerbiere2/countbitstable016.smt2` | 11,203 B | z3 `unsat` at 120 s |
| `calc2`, size stress | `QF_ABV/calc2/calc2_sec2_shifter_bmc10.atlas.smt2` | 129,767 B | in-run z3 `unsat` |

## 9. Hypotheses recorded, not adopted

Candidate causes, written down so task 3 can confirm or discard them rather
than rediscover them. **None is a finding.**

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

## 11. Measured outcomes

Closing QF_ABV re-run, run-id `slice47`, measured at commit `ddabe7b3` (same
15,148 paths as the baseline). Full narrative, transition matrix and family
breakdowns:
`docs/superpowers/research/2026-09-09-smtlib-2024-qfabv-slice47-report.md`.

### Success criteria

| criterion | baseline | slice47 | verdict |
| --- | ---: | ---: | --- |
| 1. `wrong` = 0 | 359 | **0** | **PASS** |
| 2. `correct` ≥ 8,454 | 8,454 | **12,359** (+3,905) | **PASS** |
| 3. `timeout` ≤ 361 | 361 | **524** (+163) | **FAIL** |
| 4. `abv-model-rejected` fires on 0 rows | n/a | **0** | **PASS** |
| 5. extended generator failed pre-slice, passes now | — | yes | **PASS** |
| 6. panic / parse-error / oom reported, movement explained | 5787 / 26 / 98 | 2127 / 24 / 52 | reported below |

**Criterion 3 was missed, plainly.** `timeout` rose from 361 to 524 and the
cap is not relaxed. It is decomposed rather than left as a bare number: of
the 524, 333 were already `timeout` at baseline, and of the +163 that newly
entered the bucket, 62 were previously `wrong` (a wrong answer becoming an
honest timeout is this slice's purpose), 64 were previously `panic`, 3 were
`parse-error`/`unverified`, and only **62 were previously `correct`** (28
rows left the bucket in the other direction). The criterion counts every
timeout alike; the slice's actual effect on the bucket is overwhelmingly
"wrong answers and crashes became honest timeouts". The 62
`correct → timeout` rows (dwp_formulas 36, brummayerbiere 14,
brummayerbiere2 8, brummayerbiere3 3, stp 1) are a real regression and are
queued for the next slice, not absorbed into a passing verdict.

**Criterion 5's evidence.** `qfabv_oracle::qfabv_matches_z3` failed on
pre-slice `main` (task 1's report, verbatim):
`QF_ABV SOUNDNESS DISAGREEMENT (iter 3): shinri=Sat z3=unsat` on
`(= (store (store a0 i0 e0) i1 e1) (store (store a0 i0 e1) i1 e0))` with
`i0 != i1`, `e0 != e1`. `cargo nextest run -p shinri-solver --features
oracle -E 'test(qfabv)'` now discovers 7 tests, all 7 pass, including
`qfabv_matches_z3` in 3.141 s.

**`abv-model-rejected` fired on 0 rows** in the closing re-run — criterion
4's PASS condition. The gate never actually downgraded a corpus `sat`; every
changed row changed through a fix the gate's rejection reason pointed the
bisect at. The 21 unit fences in `validate.rs` are the executable record of
§3.4's grammar restrictions and did not fire on any real corpus row either.

**Criterion 6 — the panic movement, and §2's superseded expectation.** §2
scoped the 5,787 `blast_word` panics out of this slice and expected them
"reported unchanged". That expectation is superseded: the fix for the real
cause (below) required `prewarm_array_words` to blast index/element terms
before the first solve, and some of those terms mention a nested `select`
that `blast_word` cannot encode. Pairing the prewarm with `abstract_word` —
which rewrites such a term through its abstraction read-var before blasting
— is what converts a large slice of the panic bucket into real answers:
3,917 `panic → correct` transitions, 3,883 of them `egt`. `panic` fell from
5,787 to 2,127 (raw) as a welcome side effect of a fix this slice needed for
a different reason, not the unchanged count §2 anticipated. `parse-error`
(26 → 24) and `oom` (98 → 52) moved slightly as second-order effects of the
same transition churn; neither is attributed to a new defect.

### Both §9 hypotheses discarded; the real cause was neither

| hypothesis | verdict |
| --- | --- |
| §9 #1 — `functional_consistency` relates two selects only when their base arrays are syntactically identical | **DISCARDED as the cause of any measured row.** The restriction is real but was never reached — the checks never had a usable model to compare against. |
| §9 #2 — `refine` returns `Sat` at a lemma-set fixpoint that is not an axiom fixpoint | **DISCARDED as stated.** The loop does stop early, but not because a round's guards happened to agree with a real model — it stops because the model it read was fabricated. |

**The real cause.** `Sat::add_clause` backtracks to decision level 0 on any
clause added after a solve, destroying the assignment. `RealBridge::value_bv`
blasted words **on demand** and then read the **live** solver — so the first
query for a word that had never been blasted (an index or element term that
only ever appeared inside an abstracted-away `select`/`store`) wiped the
model, and every subsequent value read was
`value_of(v).unwrap_or(false)`: a fabricated `0`. An all-zero pseudo-model is
internally consistent with every array axiom, so round 0 of `refine` emitted
no lemma and reported `Sat` in round 0 without examining anything real.

The same corrupted values reached the model gate: `validate` reads the same
`value_bv`, so on `bubsort002un.smt2` it built its store-chain overlay and
its read comparisons from the same fabricated zeros and passed every check
on garbage — that is why the gate had a hole on that row. The two
rejections the gate *did* produce during the bisect
(`wchains002ue`'s `DiseqPinsForceEqual`, the minimal reproducer's
`ReadMismatch`) were sound outcomes but were also derived from the same
fabricated model, not genuine findings. The fix makes the value readers work
from a post-solve snapshot that is never mutated; a word the snapshot cannot
value returns `None` and is queued for the next solve instead of reading as
zero. `validate.rs` and `check.rs` were not changed — the diagnosis did not
call for it.

### The retracted claim

Commit `60b41c74`'s message states shinri is "sound on the 359 measured
QF_ABV wrong answers from here, whatever the remaining tasks find." That was
**false when written** and was retracted in the very next commit's message,
`b88a8349`: `bubsort002un.smt2`, one of the 359 measured rows, passed every
`validate` check and was still answered `sat`, because — as the bisect later
found — the checks were reading a fabricated model. Recorded here so the
claim is not repeated or rediscovered as new.

### Post-measurement correction

The `ddabe7b3` measurement's transition matrix shows 264 `correct → panic`
rows, all `dwp_formulas`, all the same `blast_word` message: the same
`prewarm_array_words` fix newly unlocked a dead branch of
`functional_consistency`'s lemma construction, and the write path that lemma
goes through (`RealBridge::ensure_atom`) never applied the aliasing rewrite
that the read path did, so it handed a raw select-mentioning term straight
to `blast_word`. Commits `741410ac` and `bdf85f59` fix this by running the
same aliasing rewrite in `ensure_atom`. This was **not** re-measured by a
full corpus re-run; it was verified by direct per-file measurement of all
264 regressed rows against the fixed binary (20 s timeout each), and all 264
came back `sat`, matching baseline's correct verdict — full recovery, no
new panics, timeouts, unknowns or wrong answers. So the shipped code's real
numbers (at `bdf85f59`, this branch's HEAD) are approximately `panic` 1,863
and `correct` 12,623 — the raw table above, corrected by that 264-row swing
in the single direction it moved. No other bucket is affected.

### Queued for the next slice

* The 62 `correct → timeout` rows behind criterion 3's miss.
* The remaining `blast_word` panic bucket (2,127 raw / ≈1,863 shipped) —
  still out of scope per §2; `check.rs` can still reach `blast_word` through
  a route this slice did not touch (raw index terms in lemma construction
  outside `ensure_atom`), deliberately deferred to the panic-bucket slice
  (slice-46 queue rank 4).
* The 53 stack-overflow rows and 24 `parse-error` rows, unchanged in kind,
  tracked under the slice-46 queue's existing ranks.
