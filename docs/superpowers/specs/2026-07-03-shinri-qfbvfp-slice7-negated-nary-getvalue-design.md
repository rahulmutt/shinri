# shinri QF_BVFP — Slice 7: negated n-ary soundness + get-value completeness

**Date:** 2026-07-03
**Status:** **Landed 2026-07-03** — commit range `c728429..dca4c66` (9 commits, on `main`, kept local).

<details><summary>Landing summary</summary>

**Scope closed:** C2, I1, I2 (both heads), item-4, item-5 — all five slice-6 follow-ups.

**Per-item resolution:**
- **C2** (negated n-ary arith `=` wrong-SAT) — `c728429`. The design's approach A ("generalize
  `lib.rs::lower`'s `Not(Eq)` arm to n-ary") was **architecturally unreachable**: `word_norm`
  expands every n-ary `=` to `(and …)` *before* `lower` runs, so `lower` never sees an intact
  n-ary Eq (verified: `lib.rs:307` normalize precedes `lib.rs:444` lower). Implemented instead as a
  **De Morgan rewrite in `word_norm`'s `Not` arm**: `(not (and (= a b) (= b c) …))` →
  `(or (not (= a b)) (not (= b c)) …)`. Every Eq stays binary (preserves the EUF binary-Eq
  invariant — an earlier attempt that skipped expansion under `Not` panicked shinri-euf and was
  reverted); `lower`'s existing binary `Not(Eq)` arm rewrites each pure-arith pair to `(or Lt Gt)`.
  Sound for every sort (Bool/UF/String regression pins added).
- **I1** (negated n-ary String `distinct` wrong-UNSAT) — `8742cc5`. Fold-only (approach A); the
  semantic-duplicate variant already answered correctly, so **no `shinri-str` change**. `word_norm`
  folds an n-ary `distinct` with any syntactically-equal operand pair to the `false` constant.
- **I2** (premature-SAT panics) — **two independent heads, both fixed at the genuine upstream cause
  (not assert-guarded):**
  - `sat/solver.rs:553` premature-SAT ← a **VMTF branch-heuristic bug** (`8aba7a9`): all never-bumped
    vars shared `stamp==0`, so `on_unassign` could drop a freed var from branching. Fixed with
    strictly-negative creation-ordered stamps (`u64→i64`). (C2's De Morgan rewrite is what *exposes*
    this at arity ≥5.)
  - `eq_engine.rs:366` explain-on-unconnected ← an **EUF diseq-map undo bug** (`bda6ad1`,`04df13d`):
    `assert_diseq`'s key-collision branch overwrote a diseq record without an undo entry, corrupting
    the map across `pop`. Fixed with a `DiseqUndo::InsertOverwrite` variant mirroring the proven
    `RekeyOverwrite` fix.
- **item-4** (nested-ite get-value) — `175b4ef`. `WordNorm.orig_ite` map keyed by the original
  (pre-rewrite) ite term; consumed in the get-value remap. get-model output unchanged.
- **item-5** (QF_ABV eliminated-ite get-value) — `82e0cd1`. `solve_qfabv_with_models` → 3-tuple
  returning internal-ite BV values via the pre-existing `SatBridge::value_bv` (no `shinri-abv`
  change). Array-model channel unchanged.

**Differential oracles:**
- NEW `nary_arith_oracle.rs` (`6eba66b`,`dca4c66`, QF_LIA, C2's family):
  `differential_qf_lia_nary: sat=104 unsat=96 unknown=0 z3_checked=200`, **0 disagreements**, of
  which **71 are genuine C2 bound-squeeze UNSATs** (independently union-find-verified; permanent
  `assert!(n_c2_unsat >= 10)` guard). Confirms the C2 De Morgan fix across 71 real cases.
- `qfs_matches_z3`: 85 sat / 133 unsat / 82 skipped, 84 z3-witnessed, 0 disagreements (unchanged).
- **String oracle re-baseline (design §4) DEFERRED:** widening `differential_qf_s_nary` past its
  I2-skirt seed `0xB000_9E37` to `0xB000_9E38` exposes a **separate pre-existing shinri-str
  wrong-UNSAT** (below), so the seed is left at `0xB000_9E37`.

**Verification (definition of done):**
- `cargo test --workspace` @ `dca4c66`: **63 suites, 0 failed**, exit 0 (~36 min).
- `cargo test -p shinri-solver --features oracle`: **19 suites, 0 failed, 0 disagreements**, exit 0.
- Clippy `--workspace --all-targets`: **0 net-new** — zero warnings in any slice-7-changed file;
  touched crates (solver=2 / sat=0 / theory=4) match the slice-6 known set.
- Canary sweep: clean (no test pins a wrong C2/I1 verdict).
- Debug no-panic pins: `premature_sat_string_family_*` 3/3, `diseq_undo_collision_no_debug_panic` 1/1.

**Filed follow-ups (all PRE-EXISTING at base `d7089c2` — confirmed by worktree; NOT introduced by
this slice; the widened oracle merely uncovered them):**
1. **shinri-str `distinct`-over-concat wrong-UNSAT** (BROAD-HIGH, own slice). At `Effort::Full`,
   `distinct("", s2++"a")` emits a unit conflict forcing `s2++"a"=""` (impossible), yielding
   wrong-UNSAT. Repro: `(not (distinct s3 "" (str.++ s2 "a")))∧(not (= (str.++ s3 "a") "" s3 s2))∧
   (distinct s3 (str.++ s2 "a"))` → z3 sat, shinri unsat. This is why the string oracle re-baseline
   is deferred. Diagnosis: `.superpowers/sdd/task-4b-report.md`.
2. **`shinri-sat/src/solver.rs:293` `analyze` index-out-of-bounds** on some `str.++`/`str.len`
   shapes (corrupt literal in conflict analysis); z3 sat. Surfaced by wide-seed oracle sweeps.
3. **`Evsids` sibling heuristic** — audit for the analogous never-bumped-var drop the VMTF fix closed
   (no evidence it has it; flagged for coverage).

</details>
**Plan:** 5 (post-Plan-4 completeness & robustness), third slice — the five follow-ups
filed by the slice-6 waves.
**Predecessors:** slice 6 (`22d75fb..2187a41`), whose landing + final review filed all
five items addressed here.
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md`

## 1. Goal & Scope

Close every follow-up left open after slice 6:

- **C2** — negated arith n-ary `=` **wrong-SAT** (pre-existing at base).
- **I1** — negated n-ary String `distinct` **wrong-UNSAT** (pre-existing string-theory
  defect).
- **I2** — debug-build **panics** in the string/eq premature-SAT family.
- **Item 4** — `get-value` on the OUTER term of a NESTED eliminated ite degrades to a
  sound `?` (completeness gap; no wrong value).
- **Item 5** — the QF_ABV path has no eliminated-ite `get-value` channel at all (same
  sound `?`).

**No new FP surface, no fence changes** — this is a soundness / conformance /
completeness slice.

In scope: `shinri-solver` (`lib.rs` lowering, `word_norm.rs`, `abv_stage.rs`),
`shinri-str`, and the `shinri-sat` / `shinri-theory` debug asserts.
Out of scope: anything touching the FP admission fence or adding a theory operator.

## 2. Component changes

### C2 — `lib.rs` `Not(Eq)` arm (~1027)

The binary `Not(Eq)` pure-arith special case rewrites `(not (= a b))` →
`(or (Lt a b) (Gt a b))` so the Arith theory enforces the disequality. It is guarded by
`eq_kids.len() == 2`, so n-ary `(not (= a b c …))` falls through to the generic
`(not (and …))` path, where the SAT solver can pick `¬Eq_euf` for one pair independently
of the Arith `Le∧Ge` companions → **wrong-SAT**.

**Fix (approach A):** lift the arity-2 guard. `(= a b c …)` means
`a=b ∧ b=c ∧ …`, so its negation over all-pure-arith operands is
`(or (or Lt_ab Gt_ab) (or Lt_bc Gt_bc) …)` — a disjunction of the per-adjacent-pair
diseqs. This is the exact negation dual of the n-ary `=` lowering already at
`lib.rs:917`. Mixed-EUF operands (any operand not `is_pure_arith`) stay on the generic
recursion, matching the current binary behaviour, so EUF/QF_UFLRA congruence is
unaffected.

Rejected alternative (B): eq ↔ (le ∧ ge) linking clauses that force `¬Eq ⇒ ¬(Le∧Ge)`
globally. More general, but touches the core encoding and risks perturbing the oracle
baselines — disproportionate blast radius for a targeted bug.

### I1 — `word_norm.rs` distinct expansion (~158)

`(distinct s1 s2 s2)` expands to a pairwise conjunction that **includes the self-pair
`(distinct s2 s2)`** (which is `false`), so the whole distinct is `false` and
`(not (distinct s1 s2 s2))` is `true` — the assertion should impose no constraint and
the query is **sat**. shinri answers unsat, so a distinct atom is driving a conflict
irrespective of assertion polarity / self-reference.

**Fix (approach A, primary):** in the distinct expansion, before building the pairwise
conjunction, if any two operands are syntactically identical, replace the entire
`(distinct …)` term with the `false` constant (an n-ary distinct with a repeated operand
is unsatisfiable-as-true). The self-distinct atom then never reaches string theory. This
is trivially sound and kills the filed repro at the source.

**Diagnosis sub-step (systematic-debugging), gates whether approach B is also needed:**
reproduce the filed case, then probe a *semantic*-duplicate variant — operands that are
distinct terms but merged equal via EUF (e.g. `(distinct s1 s2 s3) ∧ (= s2 s3)`), which
the syntactic fold in (A) does **not** catch. If that variant is also wrong-UNSAT, the
root cause is polarity/self-reference handling in `shinri-str` (the `eq_true` /
distinct-atom path around `shinri-str/src/lib.rs:107-136`) and we additionally fix it
there. Both branches stay in the negated-distinct family.

### I2 — `shinri-sat/src/solver.rs:553` + `shinri-theory/src/eq_engine.rs:366`

Two `debug_assert`s fire in the premature-SAT string/eq family before the existing sound
string self-check (`lib.rs:687`, `string_model_satisfies`) can downgrade to `Unknown`:

- `sat/solver.rs:553` — `check_model()` ("returned SAT but a clause is unsatisfied").
- `eq_engine.rs:366` — `explain: a,b not connected`.

Release builds return a verdict; only debug fuzzing trips these.

**Fix — diagnose first, then decide (no blanket relaxation):**

- If the state the assert observes is **genuinely inconsistent** at that point, the
  upstream theory state is the bug — fix that.
- If it is a **known, already-handled** premature-SAT interlude that the downstream
  string self-check will soundly downgrade, guard/relax the assert with a comment naming
  the family and citing the self-check that makes it safe.

The decision is recorded in the plan's task for I2 after the diagnosis; the spec does not
pre-commit to relaxing, because that could mask a real inconsistency.

### Item 4 — nested-ite `get-value` (`word_norm.rs` + `lib.rs:668`)

`ite_var` (`word_norm.rs:30`) is keyed by `rebuilt` — the ite AFTER its children are
rewritten. For a nested ite, the outer key embeds the inner ite's fresh var `w_inner`,
so it never matches the user's original (child-un-rewritten) query term → the get-value
remap loop misses → sound `?`.

**Fix:** record a parallel map `orig_ite: FxHashMap<TermId, TermId>` keyed by the
**original** term id `t` (available in `walk`) → `w`, populated alongside `ite_var`.
`ite_var` keeps its `rebuilt` key (needed for structural dedup during the walk). The
get-value remap loop (`lib.rs:668`) iterates `orig_ite` so a nested outer ite resolves to
its internal symbol's value. Additive; get-model output unchanged (`internal` filter is
untouched).

### Item 5 — QF_ABV eliminated-ite `get-value` channel (`abv_stage.rs`)

The eliminated-ite remap loop (`lib.rs:668-677`) runs only on the fp/bv path;
`abv_stage` never populates `eliminated_ite_vals`, so QF_ABV get-value on an eliminated
ite always degrades to `?`.

**Fix:** run the same original-term-keyed remap (from item 4) against the ABV model on
the ABV path, populating `eliminated_ite_vals`. word_norm runs before staging for all
paths, so the `ite_map` / `orig_ite` already exist when the ABV stage builds its model.

## 3. Data flow & ordering

Sequence soundness-first; each step lands independently green.

**0. Pre-flight (semantic, per the spec-assumed-paths lesson).** Before coding, confirm
each fix locus behaves as §2 assumes:

- C2's n-ary `Not(Eq)` actually reaches the generic path (not folded/simplified earlier).
- I1's self-pair reaches `word_norm` unsimplified (no earlier constant-fold of
  `(distinct x x)`).
- The ABV path's model is available at the point item 5 remaps.

Plus a **canary hunt**: grep e2e/unit tests pinned to the current wrong/degraded verdicts
(the C2/I1 repros; any `?`-pinned nested-ite or ABV get-value tests) so each is flipped
in the same commit that fixes the behaviour.

**Steps:** C2 → I1 (with diagnosis) → I2 (with diagnosis) → item 4 → item 5.

**TermId-layout note.** C2 and I1 add `mk_app` calls, shifting TermId numbering. I2's
panics are TermId-layout-sensitive, and the slice-6 `differential_qf_s_nary` seed
`0xB000_9E37` was chosen to *skirt* them. Consequences:

- Between C2/I1 and the I2 fix, the debug asserts may begin firing on the shifted layout —
  expected; that is what step I2 resolves.
- I2 lands **before** the string oracle is re-baselined. Once I2 is fixed, the seed no
  longer needs to dodge, so the string-family re-seed/re-run is gated on I2 completing.

## 4. Testing

Following the slice-6 pattern; z3 is the source of truth for every hard pin.

**e2e hard pins (`shinri-solver`), each z3-verified:**

- C2: `(not (= x y z)) ∧ x≤y ∧ x≥y ∧ y≤z ∧ y≥z` → **unsat**.
- I1: `(not (distinct s1 s2 s2)) ∧ (= s2 s1) ∧ (= s1 (str.++ s3 "ab"))` → **sat**.
- I1 semantic-duplicate variant (e.g. `(distinct s1 s2 s3) ∧ (= s2 s3)` shape) → z3
  verdict.
- Item 4: `get-value` on the outer term of a nested eliminated ite → **concrete value**
  (not `?`).
- Item 5: QF_ABV eliminated-ite `get-value` → **concrete value**.

**I2 debug pins:** run the two repros
(`(not (= s1 s2 s3)) ∧ (= s1 "a")` and the sibling premature-SAT case) under a **debug**
build asserting no panic.

**Differential oracle:** extend `differential_qf_uf_nary` and `differential_qf_s_nary`
with **negated** n-ary `=` / `distinct` generators (the exact family these bugs live in),
z3-checked. Re-baseline the string family seed post-I2 (drop the skirt constraint) and
record the new counts in the Status block.

**Unit:** `word_norm` self-pair-fold test; the new `orig_ite` original-term-keyed map.

## 5. Verification (definition of done)

- Full `cargo test --workspace` green — the multi-minute FP/SAT suites are run in the
  background by the implementer directly, not via looping subagents.
- Full differential oracle green; all pre-existing suite counts byte-identical to the
  slice-6 baseline **except** the deliberately-extended / re-seeded negated-n-ary
  families, whose new counts are recorded in the Status block.
- Clippy net-new zero against the slice-6 known set
  (solver=2 / fp=22 / parser=3 / theory=4 / str=9).
- Canary sweep clean; every flipped canary flipped intentionally with a z3-verified
  target.
- Debug build: no panic on the I2 repros.

## 6. Risks

- **I1 / I2 root causes are diagnosis-gated.** If I1's semantic-duplicate variant is also
  wrong, scope grows to the `shinri-str` polarity fix (still in-family). If I2's assert
  is observing a genuine inconsistency, the fix is upstream and larger. The plan carries
  both branches; the chosen branch is surfaced after the diagnosis sub-steps rather than
  pre-committed here.
- **No fence / FP-op change**, so the classic cross-slice canary break (admitting a QF_FP
  op or lifting a fence) does not apply. The residual canary risk is the TermId-layout
  shift from C2/I1, handled by ordering I2 before the string re-baseline (§3).
