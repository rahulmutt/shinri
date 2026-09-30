# Slice 52 — Strings: Bool `=` in the model gate, and two word-equation resolver holes

Status: design approved in chat 2026-09-30. Picks up the first item of the
slice-51 queue (`docs/superpowers/research/2026-09-30-smtlib-2024-slice51-escapes-report.md`,
`## Queued for the next slice`): the Noetzli pair, the only `wrong` rows left
in QF_S + QF_SLIA.

**Area:** `shinri-solver` (`lib.rs::eval_atom`, the post-solve string model
gate), `shinri-str` (`wordeq.rs::resolve_inner`, `lib.rs` E1 gate and
`input_cond_roots`). Tests in `shinri-solver` (unit, new `slice52_probes`,
`qfs_differential`, `qfs_fuzz_corpus`) and `shinri-str` (unit). No parser,
Combiner, SAT or arithmetic change.

## 1. Summary

### 1.1 The defects

Both Noetzli rows state that two string equalities disagree although they
always agree:

```
(assert (not (= (= "A" (str.++ y x)) (= "A" (str.++ x y)))))   ; _370
(assert (not (= (= "B" (str.++ y x)) (= "B" (str.++ x y)))))   ; _458
```

`y++x` and `x++y` are equal to a one-character constant under exactly the
same assignments, so both files are `unsat` (z3 4.16.0 agrees). shinri answers
`sat` with the model `x = ""`, `y = "E"`, which violates the assertion.

Two independent defects combine:

1. **The model gate cannot evaluate a Bool-sorted `=`.** The post-solve
   self-check `string_model_satisfies` (`crates/shinri-solver/src/lib.rs:1510`)
   calls `eval_bool`. For `=`/`distinct` it defers to `eval_atom`
   (`lib.rs:1667`), which only evaluates String and Int/Real operands and
   returns `None` otherwise. `None` counts as satisfied, so the gate passes the
   bogus model. The same formula written with `xor` is caught
   (`unknown:str-model-rejected`), because `eval_bool` has an `xor` arm.
2. **The string theory reaches a SAT candidate it has not justified.** Three
   holes, found by a trace in a throwaway worktree:
   - **(H1) empty residual vs several variables.** After a char-peel
     `y = "A" ++ k`, the equation `"A" = y ++ x` normalises to `[]` vs
     `[k, x]`. `resolve_inner` (`crates/shinri-str/src/wordeq.rs`) only
     propagates when the variable side is a single atom (`pair` block, ~836),
     so it falls through to `StepResult::Done` (~991). The empty-residual
     `Σlen ≤ 0` lemma in `lib.rs` (~690) is skipped, because `k` sits in a
     minted-split class.
   - **(H2) constant prefix of a constant.** `["AB"]` vs `["A", k, x]` walks the
     shared `A`, then breaks (~873): neither head is a variable, so no
     char-peel or F-split fires, and the result is `Done`. The unit test
     `prefix_of_constant_is_done_not_conflict` pins this. **Out of scope** (§9).
   - **(H3) an equation gated off by its own literal.** Under the Bool `=`, the
     word equation is decided at level > 0. `input_cond_roots`
     (`crates/shinri-str/src/lib.rs:270-322`) is built from every conditional
     input (dis)equality, **including the equation itself** and the sibling
     disequality that shares the `"A"` node. The E1 gate
     (`lib.rs:773`, `side_clean(input_cond_roots)`) therefore never resolves
     it: no split is emitted and final check returns `Sat`.

   `_370` goes through H3. R1 and R2 below go through H1.

### 1.2 Minimal reproducers (on `7bd2279`)

```
; R1                                           shinri: unknown (str-model-rejected)   expected: unsat
(declare-fun x () String) (declare-fun y () String)
(assert (= "A" (str.++ y x))) (assert (not (= "A" (str.++ x y))))

; R2                                           shinri: unknown (str-model-rejected)   expected: unsat
(assert (= "A" (str.++ y x))) (assert (not (= "A" x))) (assert (not (= "A" y)))

; distinct form of _370                        shinri: sat                            expected: unsat
(assert (distinct (= "A" (str.++ y x)) (= "A" (str.++ x y))))

; Bool proxy                                   shinri: sat                            expected: unsat
(declare-fun p () Bool)
(assert (= p (= "A" (str.++ y x)))) (assert (not (= p (= "A" (str.++ x y)))))

; xor form                                     shinri: unknown (str-model-rejected)   expected: unsat
(assert (xor (= "A" (str.++ y x)) (= "A" (str.++ x y))))

; AB (H2, queued)                              shinri: sat                            expected: unsat
(assert (not (= (= "AB" (str.++ y x)) (= "AB" (str.++ x y)))))
```

Control, already correct: `"A" = y++x`, `"" = x`, `"A" ≠ x++y` is `unsat`.

### 1.3 Spike evidence

A throwaway worktree tried H1 and H3 fixes (§3.2, §3.3):

- H1 alone: R1 and R2 become `unsat`, and the SAT controls stay `sat` with
  valid models.
- H1 + H3: `_370` becomes `unsat`.
- Both runs: `cargo nextest run -p shinri-str -p shinri-solver` 767 passed;
  oracle binaries `qfs_differential`, `qfs_fuzz_corpus`, `slice33_probes`,
  `slice34_probes`, `oracle` with `--features oracle` 113 passed.

The soundness of the H3 change and its step-budget cost were **not**
measured in the spike. §6 and §7 cover them.

## 2. Scope

**In:**

- §3.1: the model gate evaluates Bool-sorted `=`/`distinct`.
- §3.2: H1, `Propagate` for an empty residual against several free atoms.
- §3.3: H3, the E1 gate ignores the equation's own literal and conditional
  disequalities.

**Out** (queued in §10): H2; an audit of every `None` in `eval_bool`; the rest
of the slice-51 queue.

## 3. Design

### 3.1 Model gate: Bool-sorted `=` / `distinct`

In `eval_atom` (`crates/shinri-solver/src/lib.rs`), before the String branch:
if `sort_of(kids[0])` is Bool, evaluate both operands with `eval_bool`.

| op | both `Some` | otherwise |
| --- | --- | --- |
| `=` | `Some(a == b)` | `None` |
| `distinct` | `Some(a != b)` | `None` |

This matches the three-valued rule of the existing `xor` arm. `word_norm`
expands n-ary `=`/`distinct` to binary before this point; the existing
`kids.len() != 2 → None` guard stays.

The gate can only turn `sat` into `unknown`, never produce a verdict. It is a
backstop: with this change alone, `_370` becomes `unknown:str-model-rejected`.

### 3.2 H1: empty residual against several free atoms

In `resolve_inner`'s propagation block (`crates/shinri-str/src/wordeq.rs`,
beside the single-atom `pair` case), add:

> If one residual is empty and the other has **two or more** atoms, every one
> a free variable, return
> `Propagate { var: v, word: "" , just }`, where `v` is the first atom whose
> EUF class does not already contain `""`.
> If every atom's class already contains `""`, fall through (to `Done`, as
> today).

- **Soundness.** A concatenation equals `""` iff every part is `""`, so each
  merge is entailed by the equation plus the normal-form substitutions. The
  existing `Propagate` driver cites both: `Asserted(lit)` plus `nf_ante`, under
  `EqJust::Interface` (`crates/shinri-str/src/lib.rs` ~890).
- **Termination.** Each round merges one class into `""`'s class. The
  "already contains `""`" check means no atom is picked twice. The spike showed
  that always choosing `vs[0]` loops.
- **Cost.** No fuel, no fresh atom, no split, so no pressure on the
  `2_000_000` SAT step budget or `STRING_PATH_PIVOT_BUDGET`.
- **Minted skolems are allowed.** The slice-34 skolem exclusion guards the
  var–var `Propagate`: that merge unions two classes and replaces an F-split
  the model builder needs. A merge into `""` is a constant fact, not a class
  union, and R2's residual is `[] = [!strk0, x]`. The code comment records
  this.
- Mixed residuals (a constant or a non-variable atom among them) are
  unchanged. A non-empty constant already conflicts (~880); an empty constant
  is dropped by normalisation.

### 3.3 H3: the E1 gate ignores the equation's own literal and disequalities

**What the gate protects.** A resolution step that reads a normal form built
from a **branch-local merge** must not learn a global Conflict or Split that
fails to cite that merge (ce1..ce8, slices 33–38). `input_cond_roots` is the
set of classes that some conditional input literal could have merged.

**Two contributors that cannot cause that failure:**

1. **Conditional disequalities merge nothing.** They cannot make a normal form
   branch-local, so they do not contribute to the word-equation gate's view
   (below). **`input_cond_roots` and `all_cond_roots` are unchanged**: the
   membership channel (`memb::memb_check`), the order channel
   (`order_engine::order_fold_check`) and the global same-word conflicts keep
   reading them exactly as today.
2. **The equation's own literal.** Every result of resolving equation `e`
   already carries `lit(e)`: `Conflict` and `Propagate` cite
   `EqLeaf::Asserted(lit)`, and `Split` is guarded by `¬lit`. A merge caused
   only by `e` is therefore covered by its own citation.

**Mechanics.** Add a second structure, used **only** by the word-equation
gate at `lib.rs:773`: a contributor map,
`input_cond_contrib: FxHashMap<ENodeId, SmallVec<[CondSrc; 2]>>` with
`enum CondSrc { Eq(TermId), Propagation }`, mapping each root to what touched
it: a conditional input equality atom, or a level > 0 propagation merge. Only conditional
(level > 0), non-minted `eq_true` atoms and level > 0 propagation merges are
added. For equation `e`, a side is clean iff no flattened atom's root has a
contributor other than `CondSrc::Eq(e)`. The map lives in a new focused module
`crates/shinri-str/src/wordeq_gate.rs`; `side_clean` itself is unchanged.

- The propagation fold-in (`prop_merge_info`) feeds the map as
  `CondSrc::Propagation`, which is never exempt.
- At the intra-check propagation merge (the `Ok(())` arm), the map moves the
  contributors of both pre-merge roots onto the post-merge root (at any
  level), and adds `CondSrc::Propagation` when level > 0. This is at least as
  conservative as the existing set insertion.
- The debug-only E1 soundness invariant checks antecedent kinds, not set
  membership, so it needs no change.

**Fallback (agreed).** If the §6.3 oracle/fuzz runs find a wrong `unsat`, or
the §7 bench shows any `* → wrong` row, §3.3 is dropped. §3.1 and §3.2 still
ship, and H3 is queued with the evidence. The Noetzli pair then ends as
`unknown:str-model-rejected` (sound), not `unsat`.

## 4. What this does not change

- The SAT step budget, `STRING_PATH_BRANCH_BUDGET`, `STRING_PATH_PIVOT_BUDGET`.
- `all_cond_roots` and every gate that reads it.
- Tseitin encoding: Bool `=`/`distinct` already encode as iff/xor
  (`crates/shinri-solver/src/tseitin.rs:153-181`).
- The char-peel, F-split and single-atom `Propagate` paths.
- H2's pinned `Done` (`prefix_of_constant_is_done_not_conflict`).

## 5. Tasks

1. **T1: red pins.** New `crates/shinri-solver/tests/slice52_probes.rs`
   (modelled on `slice34_probes.rs`) with every §8 script. On `main` the
   `unsat` pins fail and the controls pass. The AB pin asserts "not `sat`".
2. **T2: model gate (§3.1).** Unit tests first: `eval_bool` on Bool `=` and
   `distinct` with both sides known true, known false, and one side unknown;
   `string_model_satisfies` rejects `_370`'s assertion under the model
   `x = ""`, `y = "E"`. Then the change. After T2, `_370`, `_458` and the
   `distinct` form answer `unknown`, not `sat`, and the AB pin passes. The
   Bool-proxy form stays `sat` until T4: `eval_bool` cannot evaluate the
   uninterpreted Bool constant `p`, which is part of the queued audit.
3. **T3: H1 (§3.2).** Unit tests first in the `wordeq.rs` test module, next to
   the slice-33/34 `Propagate` tests (~1692-1900):
   - `[] = [x, y]` propagates `x ≈ ""`;
   - with `x ≈ ""` already merged, it propagates `y`;
   - with every atom already `≈ ""`, it returns `Done`;
   - `[] = [!strk0, x]` propagates (skolem allowed);
   - `[] = [x, "A"]` still conflicts, unchanged.
   Then the change. R1 and R2 pins go green.
4. **T4: H3 (§3.3).** Unit tests first in `shinri-str`:
   - a conditional equation is clean for itself;
   - a conditional disequality alone leaves both sides clean;
   - a second conditional equality on the same class still blocks;
   - a level > 0 propagation merge still blocks.
   Then the change. The `_370`, `_458`, `distinct`, `xor` and Bool-proxy pins
   go green.
5. **T5: oracle and fuzz (§6.3).** Extend `qfs_differential` and
   `qfs_fuzz_corpus`, run both with `--features oracle`, and record the counts.
   A wrong `unsat` triggers the fallback.
6. **T6: measurement (§7).** QF_S + QF_SLIA bench re-run and report in
   `docs/superpowers/research/`.

## 6. Testing

### 6.1 Unit

As listed in T2–T4. `shinri-solver` unit tests use the crate's existing
`#[cfg(test)]` helpers; `shinri-str` unit tests go in the existing test
modules of `wordeq.rs` and `lib.rs`.

### 6.2 End to end

`slice52_probes.rs` (§8). Every `sat` control re-checks its model in-process.
This binary is not oracle-gated.

### 6.3 Oracle and fuzz (evidence for §3.3)

- **`qfs_differential.rs`:** a new generator family: `=`, `distinct` and `xor`
  over pairs of word equations, whose sides are a constant (length 0–2) and a
  permuted concat of 2–3 variables. Verdicts are checked against z3 (the
  harness is z3-only), and `sat` models are replayed through z3.
- **`qfs_fuzz_corpus.rs`** (already `#[ignore]`d; it enumerates the ce1..ce8
  class of word equations under `(or …)`): add Bool `=`/`distinct`/`xor`
  combinations of word equations to its assertion generator, behind the env
  switch `E1_BOOLEQ=1` so the default sample (and its seed sequence) is
  unchanged. Run it
  explicitly with `--ignored` before and after T4. **Any new WRONG-UNSAT or
  WRONG-SAT class is a stop**: triage it; if §3.3 caused it, take the fallback.
- Run with `cargo nextest run -p shinri-solver --features oracle`, and record
  the non-zero discovered count. Without `--features oracle` these run 0 tests.
- Blocking-tier budget: any new test measured over 5 min is `#[ignore]`d as
  exhaustive, with a smoke companion.

## 7. Measurement

**Comparison baseline:** `bench/results/slice51/` (fixture `924ecc98cd06`,
20 s timeout, `solver_md5 4347bd57…`), logics QF_S and QF_SLIA, same fixture
settings.

### Success criteria

1. `str-pred-small-rw_370` and `_458` go `wrong → correct` (`unsat`). Under the
   fallback: `wrong → unknown:str-model-rejected`.
2. The QF_S + QF_SLIA `wrong` count goes 2 → 0.
3. **0 rows go `* → wrong`.** Any such row is a hard stop: root-cause it, and
   if §3.3 caused it, take the fallback and re-run.
4. Every `correct → unknown/timeout` row is listed and triaged, and the
   `unknown:sat-budget` delta is reported (§3.3 enables resolution, and so
   splits, on equations it used to skip).
5. The standard gates are green: `mise run lint`, `mise run test`, the
   unfiltered oracle suite with a non-zero discovered count, and `mise run ci`.

## 8. Named reproducers

In `slice52_probes.rs`:

| name | script | expected |
| --- | --- | --- |
| `noetzli_370` | the `_370` assertion | `unsat` |
| `noetzli_458` | the `_458` assertion | `unsat` |
| `r1_unit_diseq` | R1 | `unsat` |
| `r2_both_vars_diseq` | R2 | `unsat` |
| `distinct_form` | `distinct` form | `unsat` |
| `xor_form` | `xor` form | `unsat` |
| `bool_proxy` | Bool proxy | `unsat` |
| `ab_prefix_h2` | AB | not `sat` (today `sat`; after T2 `unknown`; H2 queued) |
| `ctrl_single_eq` | `(= "A" (str.++ y x))` alone | `sat`, model checked |
| `ctrl_both_empty_ok` | `(= "" (str.++ y x))`, `(= "" (str.++ x y))` | `sat`, model checked |
| `ctrl_iff_true` | `(= (= "A" (str.++ y x)) (= "A" (str.++ x y)))` | `sat`, model checked |

## 9. Banked, not built

- **H2: constant-prefix residuals.** Strip the shared characters of two
  constant heads when one is a proper prefix of the other, and continue
  (reaching a char-peel). This changes `prefix_of_constant_is_done_not_conflict`
  and adds fuel-gated splits, for 0 known corpus rows. **Un-bank** when a
  corpus row or a fuzz shape needs it; the AB pin is the reproducer.
- **`eval_bool` audit.** Close every other `None` that can hide a wrong `sat`
  (uninterpreted Bool constants such as the Bool-proxy `p`, string
  predicates, compound arithmetic, `str.<`). Declined in favour of the
  minimal §3.1.

## 10. Queued for the next slice

- H2 (§9) and the `eval_bool` audit (§9).
- Carried from slice 51: the 4 denghang `unknown:str-model-rejected` rows
  (`instance46836`, `51681`, `52132`, `55189`); premature string SAT on
  decoded control-character regexes (68 rows, reproducer
  `automatark-lu/instance06924.smt2` assertions {1, 2, 3, 5}); surrogate
  support; `str.replace_re`/`str.replace_re_all` (195 parse-error rows).
- Carried from slice 50: the QF_SLIA `STRING_PATH_PIVOT_BUDGET` cliff; the
  Wisa final-check blow-up; `get-value` echoing purification names; the
  `Owner::Shared` definitional merge; `pending` is not backtracked; the
  blocksworld re-index churn measurement; the `blast_word` panic bucket.
- Not re-measured since the baseline: `wrong` rows in QF_LIA (calypto, 2),
  QF_LRA (keymaera, 2), QF_BVFP (ramalho, 1).

## 11. References

- Slice-51 report: `docs/superpowers/research/2026-09-30-smtlib-2024-slice51-escapes-report.md`
  (§ Queued for the next slice).
- Baseline: `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`
  (§ Next slices, rank 3).
- Code:
  - `crates/shinri-solver/src/lib.rs:1510` (`string_model_satisfies`), `:1584`
    (`eval_bool`), `:1667` (`eval_atom`)
  - `crates/shinri-str/src/wordeq.rs` (`resolve_inner`: `pair` ~836,
    constant-head walk ~873, `Done` ~991)
  - `crates/shinri-str/src/lib.rs:270-322` (`input_cond_roots`), `:773` (E1
    gate), ~890 (`Propagate` driver)
  - `crates/shinri-solver/src/tseitin.rs:153-181` (Bool `=`/`distinct`)
  - `crates/shinri-solver/tests/slice34_probes.rs`, `qfs_differential.rs`,
    `qfs_fuzz_corpus.rs`
- Corpus: `QF_SLIA/20190311-str-small-rw-Noetzli/str-pred-small-rw/str-pred-small-rw_370.smt2`, `_458.smt2`.

## 12. Measured outcomes

Run `slice52` (QF_S + QF_SLIA, 103,335 rows, fixture `fec6fb9dc574`,
`solver_md5 bc7ee313…`) against `slice51`. Full report:
`docs/superpowers/research/2026-09-30-smtlib-2024-slice52-str-bool-eq-report.md`.

| # | criterion | result |
| --- | --- | --- |
| 1 | `str-pred-small-rw_370` and `_458` `wrong → correct` (`unsat`) | **PASS**: both `unsat` (7 ms, 6 ms) |
| 2 | QF_S + QF_SLIA `wrong` 2 → 0 | **PASS**: 2 → 0 |
| 3 | 0 rows `* → wrong` | **PASS: 0** rows, no escalation |
| 4 | every `correct → unknown/timeout` row listed and triaged; `unknown:sat-budget` delta | **DONE**: 313 rows, all `unknown` (298 `sat-budget`, 15 `str-model-rejected`), 0 `timeout`; `sat-budget` +5 (QF_S), +497 (QF_SLIA). All are `:status unknown` rows that answered `sat` on slice 51 (z3 `sat`); 309 of 313 flip at Task 4 (H3 gate) |
| 5 | standard gates green, oracle count non-zero | **PASS**: test 1,611 passed / 8 skipped; oracle 701 discovered, 697 passed, 4 skipped; lint and `ci` green |

`correct`: QF_S 16,058 → 16,061 (+3, oracle-noise `unverified → correct`),
QF_SLIA 24,815 → 24,562 (−253: +2 Noetzli, +58 other inbound, −313
`correct → unknown`). parse-error 195 → 195 (same rows).

Deviations from the spec text: z3 answers `sat` (not `unsat`) for the AB (H2)
script, so `ab_prefix_h2` is a soundness check (§1.2/§8 were wrong); H1 needed
a length link (`str.len(v) ≈ 0` merged with the H1 merge, gated to H1 only;
a model-builder override was reverted after a wrong `sat`); `distinct_form`
and `xor_form` are a sound `unknown` (re-pinned to "not sat") and
`bool_proxy` is a known wrong `sat` (`#[ignore]`d), all three a minted-branch
completeness gap; the Noetzli pair passes by search order (swapping the
disjuncts gives `unknown`). New queued items: the 313 lost `sat` rows (H3
gate), the minted-branch gap, the R10/H3-contributor-map/combiner deferred
items; see the report's *Queued for the next slice*.
