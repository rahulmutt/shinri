# Slice 38 — Split passthrough audit (word-equation F-split under-guard)

**Status:** design
**Date:** 2026-07-22
**Area:** `shinri-str` word-equation resolver (`crates/shinri-str/src/wordeq.rs`)
**Predecessors:** slice 33 (single-atom propagation), slice 34 (alias
propagation + skolem exclusion), slice 35 (flattened-path `Conflict`/`Propagate`
downgrade), slice 37 (un-bank `Propagate` cite — approach B on the strip
citations).

## 1. Summary

`resolve_inner` (`wordeq.rs:568`) strips equal leading and trailing atoms from a
word equation before deciding a Nielsen F-split. Each strip cancels a pair via
`same_explain`; on the **EUF door** (two *distinct* terms that are equal only
because a MERGE placed them in one class) it cites the merge's antecedent leaves
into `just`. The identity door (`a == b`) and the equal-literal door push
nothing (`wordeq.rs:441-454`).

When a strip cancels a pair via the EUF door, the residual F-split it enables is
only valid *given that class equality also holds*. The emitted learnt clause,
however, is guarded by `¬eqn` alone:

```text
¬eqn ∨ (= v "") ∨ (= v ("ch" ++ z))        (char-peel, wordeq.rs:942)
¬eqn ∨ len_eq ∨ a_pref ∨ b_pref            (generic F-split, wordeq.rs:971)
```

`StepResult::Split { atoms, guard }` carries **no `just`** — the strip citation
`C` is dropped entirely, on both the flattened and the non-flattened routes. The
truthful clause is `(eqn ∧ C) → disjunction`, i.e. it also needs `¬C`. A learnt
clause is a **permanent** constraint that can drive UNSAT, and — unlike the
`Propagate` merge slice 37 fixed — **nothing backstops a wrong UNSAT** (the
post-solve model gate re-checks SAT witnesses, not learnt clauses). This is
therefore soundness-shaped: a potential wrong-UNSAT.

The window has **never been observed firing** (banked across slices 33-37: "the
model gate backstops SAT, not learnt clauses. Pre-slice-33 vintage, never
observed firing"). But the single-atom / alias propagation machinery built up in
slices 33-37 is exactly what makes a *distinct-atom* strip reachable (a
`Propagate`-merged `v ≈ u`, or a flattened concat rep, aligning as an F-split
head). That is why slice 37's Propagate fix was needed, and it is why this
sibling is worth closing now rather than waiting for a wild trigger.

**Deliverable bar (adjudicated at design time):** a *proactive soundness fix*.
A wrong-UNSAT is not backstopped, so — unlike the `Conflict → Saturated` *lift*
(a completeness gain that must wait for a measured trigger to justify buying back
its cost) — this fix lands on the analysis alone. Dump-and-diff and the oracle
differential characterize impact and prove no regression; they are not a gate on
whether the fix ships.

## 2. Mechanism (approach ①: the just-growth guard)

The fix lives entirely inside `resolve_inner`. `same_explain` grows `just`
**iff** an EUF-door strip fired (identity and literal doors push nothing —
`wordeq.rs:441-454`), so `just.len()` growing across the strip loops is an exact,
free signal that a non-identity class equality was load-bearing for the residual.

1. Snapshot at entry:

   ```rust
   let incoming_just = just.len();
   ```

   Nothing between function entry and the two F-split emission sites grows `just`
   except the head/tail strip loops (`wordeq.rs:581-591`): the occurs-check, the
   all-constant comparisons, the single-atom propagation, and
   `single_var_forced_length_conflict` either return `Conflict(just)` /
   `Propagate { just }` or fall through without pushing. So `incoming_just` is the
   citation count present *before* this invocation's strips, and any later growth
   is strip-attributable.

2. At **both** F-split emission sites — the char-peel two-way split
   (`wordeq.rs:911-949`) and the generic F-split (`wordeq.rs:952-979`) — guard the
   emission:

   ```rust
   if just.len() > incoming_just {
       // An EUF-door strip was load-bearing for this residual; the F-split
       // clause `¬eqn ∨ atoms` omits the strip's class equality, so it is
       // under-guarded (wrong-UNSAT shape). Wait for SAT to case-split
       // instead. Do NOT record the dedup key: a later round whose class
       // state no longer needs the non-identity strip can emit the split
       // cleanly.
       return StepResult::Saturated;
   }
   ```

   The guard is placed **before** `emitted.insert(key)` at each site, so the
   downgrade is non-permanent: the head-pair is not marked emitted, and a
   subsequent round in which the merge that caused the strip has been retracted
   re-attempts the split correctly. This is the same "restriction of *when* the
   lemma fires, never a global fact" posture as slice 35's downgrade.

**Why both paths are covered.** The guard is inside `resolve_inner`, which serves
both the direct no-concat call (`wordeq.rs:504`) and the flattened call
(`wordeq.rs:509`). The flattened-concat-rep window (a class rep that is itself a
CONCAT, structurally flattened so inner atoms are never rep-substituted) and the
non-flattened window (a `Propagate`-merged `v ≈ u` aligning as an F-split head on
a normal word) are both handled by the single snapshot-and-compare. This is the
decisive advantage over a wrapper-level arm, which sees only the flattened path.

**Why only the Split sites.** The `Conflict(just)` returns (occurs-check,
constant-length bound, char-set containment, `single_var_forced_length`) carry
`just` — including the slice-37 strip leaves — and have their own driver gate
(`side_clean` over `all_cond_roots`, `lib.rs:817`). They are correctly cited and
are out of scope. Only the `Split` arm drops `just`, so only the `Split` arm is
guarded here.

**Wrapper interaction.** `resolve_equation`'s flattened-path match
(`wordeq.rs:509-518`) keeps its `other => other` arm; a `Split` that
`resolve_inner` has already downgraded to `Saturated` is relayed unchanged. The
wrapper's doc comment (points 2/3, `wordeq.rs:469-481`) gains a point 4 noting
that `Split` is now guarded inside `resolve_inner` on both paths, so the wrapper
no longer needs a Split arm of its own.

## 3. Alternatives considered

- **② Coarse wrapper arm** — add `StepResult::Split { .. } => StepResult::Saturated`
  to the flattened-path wrapper match, symmetric to the existing
  `Conflict`/`Propagate` arms. Rejected: it is **not a complete soundness fix**.
  The non-flattened window (a non-identity strip on a normal word after a
  `Propagate`/user merge) stays open, and it over-downgrades syntactic-identity
  flattened splits (a broader, needless completeness loss). Approach ① is both
  more precise *and* more complete in coverage for a comparable diff size.

- **③ Cite the strips into the guard** (the completeness-preserving fix): thread
  `just` into `StepResult::Split` and emit `¬eqn ∨ ¬C ∨ atoms`. Rejected *for
  now*, **banked**. The Split guard is a single `Lit` turned into a SAT clause
  literal; `EqLeaf::Interface` leaves require Combiner expansion
  (`combiner.rs:791`) that the string theory cannot perform locally, so this is
  materially more plumbing than slice 37's Propagate cite (whose `just` flows
  into the explanation machinery the Combiner already expands). For a window
  never observed firing, that cost is not yet justified. This is the direct
  analog of slice 37's approach B: un-banked when a measured `decided → unknown`
  flip attributable to this slice's downgrade appears.

## 4. Scope fence (stays banked, unchanged)

- **Approach ③ (cite the strips)** — see §3; un-banked only on a measured
  completeness cost.
- **`Conflict → Saturated` lift** (`wordeq.rs:513`) — slice-35 vintage, no
  qualifying measured trigger; separate future slice.
- Standing bank otherwise unchanged: tracked skolem-TermId set, multi-atom
  variable-bearing propagation (slice-34 §10), `Context::declare_fun` user→user
  conformance (slice-36 §2), slice-28 §8, slice-27 typed-antecedent refactor,
  slice-29 approach-C, slice-31 §11 walls 1/2/4, the retracted wall-3 seam.

## 5. Verification plan

The fix only ever *removes* a lemma emission (`Split → Saturated`). The
differential risk is therefore one-directional: it can only turn a currently
`decided` answer into `unknown` (never the reverse, never a new disagreement).
A correct `unsat` that today depends on a post-non-identity-strip F-split would
regress to `unknown`; because the window is never-observed, the expected count is
zero.

- **dump-and-diff on the Split-emission path.** Instrument the two emission sites
  to dump `(family, direction, count)` when the new guard fires (i.e. when
  `just.len() > incoming_just` at a would-be Split). Run with `--no-capture`
  (passing runs swallow `eprintln` otherwise — a green 0-line run is a false
  negative). Identify any trigger by **family + direction + count**, never by an
  absolute `DefaultHasher` digest (digests are instrumentation-scoped and do not
  reproduce across differently-scoped runs). Expected: the guard fires zero times
  on the suite, or fires only on cases whose answer is unchanged.
- **Oracle differential.** `cargo nextest run -p shinri-solver --features oracle`
  (without `--features oracle` the `qfs_differential` suite silently runs 0
  tests — that is not coverage). Confirm a non-zero test count in the output.
- **`script_e2e`.** `cargo nextest run -p shinri-solver -E 'binary(script_e2e)'`
  locally pre-push; confirm non-zero discovery. Any z3-confirmed `unknown ↔
  decided` pin flip is an adjudicated flip recorded in the spec, not a blocker;
  a `sat ↔ unsat` disagreement is a hard blocker.
- **Full workspace gate** within the 10-15 min blocking-tier budget:
  `cargo nextest run --workspace` (the five `#[ignore]`d `shinri-fp`
  exhaustives stay ignored), `cargo fmt --all -- --check`, and
  `cargo clippy --workspace --all-targets -- -D warnings` all clean.
- **Merge on green** (merge commit), then delete the slice branch remote + local
  and prune.

## 6. Testing

**Best-effort end-to-end repro (bounded).** Attempt to construct an SMT script
whose pre-fix run emits a wrong `unsat` (or a z3-disagreeing `decided`) that the
post-fix run turns into `sat`/`unknown`, by forcing a non-identity EUF-door strip
ahead of an F-split — e.g. a prior propagation `v ≈ u` (or a flattened concat
rep) so that `v` and `u` align as cancellable heads, with a residual that
F-splits and whose learnt clause, minus `¬C`, excludes an otherwise-satisfiable
assignment. If found, pin it in `script_e2e` (assert the corrected answer). Given
"never observed firing," a natural repro may not exist; the search is
time-boxed, and its outcome (found / not found, with the shapes tried) is
recorded in the spec's measured-outcomes section.

**Unit fence (always).** In `wordeq.rs`'s test module, drive `resolve_inner`
directly:

- *Downgrade fires:* intern two **distinct** string atoms, `eq.merge` them into
  one class, then resolve an equation whose head/tail strip cancels that pair via
  the EUF door and whose residual would otherwise F-split. Assert the result is
  `StepResult::Saturated` (not `Split`), and — to prove the mechanism, not just
  the outcome — assert it via the `just`-growth path (the merged pair is the only
  reason the strip succeeds).
- *Guard does not over-fire:* an equation whose strips are all **identity**
  (same-TermId) or **equal-literal** cancellations, with a residual variable
  head, still returns `StepResult::Split`. This pins that the guard keys on the
  EUF door specifically, not on stripping in general — the common, sound F-split
  is unaffected.

## 7. Success criteria

1. The two unit fences pass: the downgrade fires on a non-identity-strip-then-
   F-split shape, and an identity-strip F-split still emits `Split`.
2. Best-effort repro: either a pinned `script_e2e` case demonstrating the
   prevented wrong-UNSAT, or a recorded, bounded negative result with the shapes
   attempted.
3. dump-and-diff shows the guard's completeness cost is exactly the measured set
   (expected empty): zero `sat ↔ unsat` disagreements, and every `decided →
   unknown` flip (if any) is z3-adjudicated and recorded.
4. Oracle differential green with a confirmed non-zero test count; `script_e2e`
   green with non-zero discovery.
5. Full workspace gate green within budget; `fmt --check` and `clippy -D
   warnings` clean.
6. The fix is confined to `resolve_inner` (snapshot + two guards) plus the
   wrapper doc-comment update; no change to `StepResult`, the wrapper match arms,
   or any `Conflict`/`Propagate` path.

## 8. Measured outcomes

Instrumentation (temporary `eprintln!("S38GUARD site=charpeel|generic
grew={} -> saturated", ...)` at each guard site, Task 2) has been removed in
Task 3; the guard code itself (Task 1, commit `ccfc0621`) is unchanged —
`git diff ccfc0621 -- crates/shinri-str/src/wordeq.rs` is empty.

**Instrumentation validation (unit fences — mechanism proof).** Before
removal, `cargo nextest run -p shinri-str -E 'test(after_euf_strip_downgrades)
+ test(identity_strip_split_still_emits)' --no-capture` → 3 tests run, 3
passed, with `S38GUARD site=charpeel grew=1 -> saturated` and `S38GUARD
site=generic grew=1 -> saturated` observed on the two downgrade fences and no
line on the non-over-fire fence. This confirms both guard sites are wired and
reachable, and that the 0-counts recorded below are real (not broken
instrumentation).

**dump-and-diff.** The guard fired **0 times per site** (charpeel=0,
generic=0) on every suite it ran against — the qfs oracle string suite, the
full oracle run, and `script_e2e`. Identified by family + direction + count,
per the verification plan; no `DefaultHasher` digest is recorded here.

**Oracle differential.** qfs string suite: **90 run / 90 passed** (1 skipped),
z3/cvc5 (mise) engaged — a non-zero, decided-differential-bearing run, not a
false-green 0-test run. Full oracle (all theories): **503 run / 503 passed**
(4 slow, 3 skipped). No `decided → unknown` flip. No `sat ↔ unsat`
disagreement anywhere.

**`script_e2e`.** **73 run / 73 passed** (1 skipped), non-zero discovery. No
pin's answer moved.

**Best-effort e2e repro.** **Not found.** Seven shapes were attempted (all
`set-logic QF_S`, cross-checked against z3 4.16.0 via mise):

| # | shape | shinri | z3 | S38GUARD | notes |
|---|-------|--------|-----|----------|-------|
| A | alias `(= u v)` + `(= (str.++ u x) (str.++ v y))` | sat | sat | 0 | correct |
| A2 | alias + `(= (str.++ u "a" x) (str.++ v "b"))` | unsat | unsat | 0 | correct |
| B | flat concat `(= s (str.++ t "x"))` + `(= (str.++ s y) (str.++ t "x" "z"))` | unknown | sat | 0 | sound (pre-existing incompleteness) |
| B2 | flat concat charpeel `(= s (str.++ t "a"))` + `(= (str.++ s w) (str.++ t "ab"))` | unknown | sat | 0 | sound |
| C | merge `(= t1 t2)` + `(= s (str.++ t1 "x"))` + `(= (str.++ s y) (str.++ t2 w))` | unknown | sat | 0 | sound |
| D | merge + `(= s (str.++ t1 "a"))` + `(= (str.++ s w) (str.++ t2 "b"))` | unknown | unsat | 0 | sound (Conflict-off-flat → Saturated) |
| E | merge `(= a b)` + `(= p (str.++ a x))` + `(= q (str.++ b y))` + `(= p q)` | unknown | sat | 0 | sound |

No candidate fired the guard (0 S38GUARD across all 7 shapes); in every case
shinri returned either z3's answer or a sound `unknown`, never a wrong
`unsat`. No base-vs-fix answer divergence was produced.

**Root cause of "never observed firing."** The word `normal_form` feeding
`resolve_equation` in the real pipeline is **rep-canonical** — it substitutes
the class representative for each atom. So two EUF-equal heads arrive at
`resolve_inner` as the SAME `TermId`, take the identity door (`a == b`,
pushes nothing), and `just` does not grow. The EUF door — and hence the guard
— is effectively unreachable end-to-end via the canonical pipeline. The
Task-1 unit fences reach the branch only by calling `resolve_equation`
directly with non-rep-canonical word arrays (two distinct TermIds that are
EUF-merged but not rep-substituted); that is the correct mechanism proof for
a window the canonical pipeline never produces. The guard is a zero-cost
defensive fence.

### Success criteria (§7), marked against the above

1. **Satisfied.** Both unit fences pass (3/3, including the non-over-fire
   fence), re-confirmed after de-instrumentation in Task 3.
2. **Satisfied (bounded negative result).** No pinned `script_e2e` repro; a
   time-boxed negative result is recorded above with all 7 shapes attempted.
3. **Satisfied.** dump-and-diff measured completeness cost is the expected
   empty set: 0 guard fires on every suite, 0 `sat ↔ unsat` disagreements, 0
   `decided → unknown` flips.
4. **Satisfied.** Oracle differential green with confirmed non-zero counts
   (90/90 qfs, 503/503 full); `script_e2e` green with non-zero discovery
   (73/73).
5. **Satisfied.** Full workspace gate green within budget (Task 3 Step 4);
   `fmt --check` and `clippy -D warnings` clean (see below).
6. **Satisfied, with one itemized, human-adjudicated exception.** The fix is
   confined to `resolve_inner` (snapshot + two guards) plus the wrapper
   doc-comment update; no change to the wrapper match arms or any
   `Conflict`/`Propagate` path. **Exception:** `#[derive(Debug)]` was added to
   `StepResult` (`wordeq.rs`) because the plan's own verbatim unit-test
   assertions format the result via `{r:?}`. This is behaviorally inert — every
   `StepResult` variant and field already derives/implements `Debug`
   transitively — and was accepted by human adjudication as outside the
   "no change to `StepResult`" fence in spirit but not in effect.
