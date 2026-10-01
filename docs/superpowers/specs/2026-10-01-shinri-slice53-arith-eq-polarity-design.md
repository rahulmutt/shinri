# Slice 53 — Arithmetic `=` under non-positive polarity, and the ramalho BVFP row

Status: design approved in chat 2026-10-01. Picks up the last corpus `wrong`
rows that no slice has re-measured since the baseline
(`docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`, § Next
slices, rank 3; carried in the slice-52 report's *Queued for the next slice*):
QF_LIA `calypto` (2), QF_LRA `keymaera` (2), QF_BVFP `ramalho` (1).

**Area:** `shinri-solver` (`lib.rs`: the preprocessing step before the
Combiner, `lower`, a new `arith_eq_atoms` collector). Ramalho track: possibly
one encoding function in `shinri-fp`/`shinri-bv` (§3.4). Tests in
`shinri-solver` (unit, new `slice53_probes`, a new oracle family in
`oracle.rs`). No parser, SAT, Combiner or arithmetic-theory change.

## 1. Summary

### 1.1 The rows (measured on `2ceef06`)

| row | `:status` | shinri | z3 4.16.0 |
| --- | --- | --- | --- |
| `QF_LRA/keymaera/simple_example_2-node2074.smt2` | unsat | `sat` (4 ms) | `unsat` |
| `QF_LRA/keymaera/simple_example_2-node2406.smt2` | unsat | `sat` (4 ms) | `unsat` |
| `QF_LIA/calypto/problem-001542.cvc.1.smt2` | unsat | `sat` (4 ms) | `unsat` |
| `QF_LIA/calypto/problem-001553.cvc.1.smt2` | unsat | `sat` (4 ms) | `unsat` |
| `QF_BVFP/ramalho/esbmc/Float-no-simp9-main.smt2` | unsat | `sat` (4 ms) | `unsat` |

All five are still wrong at HEAD. The corpus for these three logics was
fetched with `BENCH_LOGICS=QF_LIA,QF_LRA,QF_BVFP mise run bench-fetch`.

### 1.2 The defect (arithmetic rows)

`Solver::lower` (`crates/shinri-solver/src/lib.rs`, ~2272) rewrites every
arithmetic-sorted `(= a b)` to `(and E Le Ge)`, where `E` is the original
`Eq` atom (kept for EUF congruence), `Le = (<= a b)` and `Ge = (>= a b)`. That
is equivalent to `a = b` only in **positive** positions. Once the
conjunction sits under negation, the SAT solver can falsify it by setting `E`
false while `Le` and `Ge` stay true. Nothing ties `E` back to arithmetic, so
the result is a wrong `sat`.

Commit `07dd304` patched exactly one shape: a syntactic `(not (= a b))` over
pure-arithmetic operands lowers to `(or (< a b) (> a b))`. Its comment
describes the hazard. Every other non-positive position is still open:

- `not` over `or`/`and` (De Morgan), and `=>` antecedent/consequent: the
  keymaera rows are `(not (=> (and … (= sum 10)) (= sum' 10)))`;
- `ite` branches under negation;
- Bool `=` (iff): `lower` does not recurse into Bool `=` at all, so its
  arithmetic `=` children never get `Le`/`Ge`;
- the calypto rows: deeply nested `not`/`and`/`ite` over arithmetic.

Term-level `ite` conditions are not affected: `word_norm` lifts them before
`lower` runs.

### 1.3 Minimal reproducers (on `2ceef06`)

```
(and (not (or (= b 1) p)) (>= b 1) (<= b 1))           ; Real   sat ✗  (De Morgan)
(and (not (= b 1)) (>= b 1) (<= b 1))                  ; Real   unsat ✓ (07dd304 arm)
(not (=> (= a 1) (= (- a 1) 0)))                       ; Real   sat ✗  (implication)
(and (= a 1) (not (= (- a 1) 0)))                      ; Real   unsat ✓
(not (=> (= x 1) (= (- x 1) 0)))                       ; Int    sat ✗
(and (= x 1) (= p (= x 2)) p)                          ; Int    sat ✗  (Bool iff)
(and (>= x 1) (<= x 1) (not (ite p (= x 1) (= x 1))))  ; Int    sat ✗  (ite branches)
(and (= x 1) (xor p (= x 1)) p)                        ; Int    unsat ✓
(and (= x 1) (< (ite (= x 1) 1 0) 1))                  ; Int    unsat ✓ (term ite, lifted)
```

### 1.4 The ramalho row

QF_BVFP has no Int/Real, so the row does not reach the arithmetic `lower`
arm; it is a separate cause. Shape: ESBMC `signbit`/`fp.isNegative` over a
Float64 `minusZero`, 247 `=>`, 960 `=`, 102 `fp.isNegative`, 32 `fp.eq`,
32 `fp.add`. It is not yet minimized. Suspects: `fp.isNegative` on `-0.0`, or
`fp.eq` vs SMT `=` on zeros/NaN.

## 2. Scope

In scope:

- Make every arithmetic `=` atom mean `a = b` to arithmetic in every Boolean
  position (§3.1–3.3).
- Minimize, root-cause and, within the time box, fix the ramalho row (§3.4).

Out of scope:

- Removing the now-redundant `Not(Eq)` arm (§4; queued as a cleanup).
- Any `wrong` row the base run surfaces that the §3 fix does not resolve:
  list and queue it, do not chase it.
- QF_UF, QF_DT (no Int/Real); QF_FP (blocked by the `define-sort` parse
  gap); QF_ABV (not in the local corpus).

## 3. Design

Approach A from the brainstorm: a definitional equivalence per atom. The
rejected alternatives were a polarity-tracking `lower` (it still needs the
equivalence for both-polarity positions such as `ite` conditions and iff,
so it is A plus a more fragile traversal), and dropping `E` for
pure-arithmetic equalities (it would hide `x = y` from EUF when `x`/`y` are
also UF arguments, which risks QF_UFLIA/UFLRA regressions).

### 3.1 Collect the atoms

New private pass `arith_eq_atoms(&self, assertions: &[TermId]) -> Vec<TermId>`
on `Solver`. It walks the assertion DAG iteratively (an explicit stack, not
recursion; deep BMC formulas already overflow the stack elsewhere) with a
visited set keyed by `TermId`. It descends through every Boolean position:
`and`, `or`, `not`, `=>`, `xor`, `ite` (all three children when Bool-sorted),
Bool-sorted `=` and Bool-sorted `distinct`. It does not descend into
non-Bool terms.

It collects every **binary** `(= a b)` whose operands are Int- or
Real-sorted (`is_arith_sorted`). That is the same domain the positive arm
lowers today, pure-arithmetic or not. An n-ary arithmetic `=` (defence in
depth: `word_norm` already splits them) is collected as the binary
adjacent-pair `Eq` terms that `lower` builds for it, so the two stay in step.
Output order is first-visit order, deterministic, without duplicates.

### 3.2 Emit the axioms

For each collected `E = (= a b)`, mint `Le = (<= a b)` and `Ge = (>= a b)`
and append three assertions to the lowered list:

```
(or (not E) Le)
(or (not E) Ge)
(or (not Le) (not Ge) E)
```

The contrapositive of the third is `¬E → (< a b) ∨ (> a b)`, so `E` is
equivalent to `a = b` for arithmetic in every polarity. The clauses are
theory-valid, so they are sound in every scope. They are rebuilt on each
`check_sat` from the live assertions, so `push`/`pop` needs no extra
bookkeeping. The pass runs at the `lower` call site (~1167), on the
post-`word_norm` assertions, before the Combiner clones the context. All
minted terms therefore exist when `register_atom`/`classify` run.

### 3.3 Simplify the positive arm

`lower`'s arithmetic `Eq` arm returns the bare binary `E` (or, for an n-ary
chain, `(and E₁ E₂ …)`) instead of `(and E Le Ge)`. The axioms carry `Le`
and `Ge`. A top-level `E` unit-propagates `Le` and `Ge` at level 0, so
arithmetic gets the same facts it gets today, through one extra
propagation.

Unchanged: the `Not(Eq) → (or Lt Gt)` arm, the arithmetic `distinct` arms,
EUF/Bool/BV/FP/string `=`. They are sound, and removing the redundant arm is
not mixed into a soundness fix.

### 3.4 Ramalho track (time-boxed)

1. **Step 0.** Re-run the row after §3.1–3.3 to confirm it is untouched.
2. **Minimize.** A throwaway delta-debug script in the scratchpad (not
   committed) drops top-level assertions, then shrinks `=>` antecedents. The
   property it preserves: shinri `sat` and z3 `unsat`.
3. **Root-cause.** Compare the minimized core against the FP blaster's
   predicate encodings. If shinri prints a model, check it against z3 to find
   the violated assertion.
4. **Decide.** The time box is one plan task (steps 2–3).
   - **Local fix** (one encoding function in `shinri-fp`/`shinri-bv`, plus
     tests): land it in this slice. That means an e2e test with the
     minimized repro, a unit test for the encoding, and the existing
     `fp_oracle` suites green. The exhaustive `#[ignore]`d `shinri-fp` suites
     stay ignored (AGENTS.md). If the touched encoding is one of theirs,
     spot-run the relevant suite once and record the result.
   - **Otherwise:** commit the minimized repro as a passing known-bug marker
     that asserts today's `sat`, with a reason string (slice-52 R16 style).
     Queue the row with the cause hypothesis in the report. The row stays
     `wrong` and is reported as such.

## 4. What this does not change

The parser, the SAT core, the Combiner and the arithmetic theory are not
touched. The `Not(Eq)` and `distinct` lowering arms stay as they are; the
`Not(Eq)` arm becomes redundant and is queued for removal. The string model
gate (`string_model_satisfies`) is not touched.

## 5. Tasks

1. **Base run.** `slice53-base` on HEAD `2ceef06`, over QF_LIA, QF_LRA,
   QF_BVFP, QF_UFLIA, QF_UFLRA, QF_S and QF_SLIA (§7).
2. **Failing tests first.** `slice53_probes.rs` with the §6.2 cases, and the
   §6.3 oracle family. Confirm the probes fail and the oracle reports
   disagreements at HEAD; record those counts as "before" evidence.
3. **Fix.** §3.1–3.3, with the §6.1 unit tests first.
4. **Ramalho.** §3.4.
5. **Gates and re-run.** `mise run lint`, `mise run test`, and the oracle
   suite; then `slice53` over the same logics, the report, and §12.

## 6. Testing

### 6.1 Unit (`lib.rs` test module)

`arith_eq_atoms`:

- finds atoms under `not`/`=>`/`xor`/`ite`/Bool `=`/Bool `distinct`;
- deduplicates an atom shared by two assertions;
- ignores Bool-, BV- and String-sorted `=`.

Also: an assertion set with only a positive top-level `(= x 1)` lowers to
the bare `E` plus exactly three axiom assertions.

### 6.2 End to end (`crates/shinri-solver/tests/slice53_probes.rs`, blocking tier)

Each case asserts `unsat`. Each has a `sat` sibling (one bound relaxed) that
guards against over-refuting.

- §1.3's De Morgan, implication, Bool-iff and ite-branch cases, each in an
  Int (`QF_LIA`) and a Real (`QF_LRA`) version.
- `xor` and the term-`ite` case: regression pins (already `unsat`).
- A QF_UFLIA case where `x` and `y` are also arguments of `f`, and `x = y`
  sits under `=>`. It pins that EUF congruence still sees `x = y`
  (`f x ≠ f y` must stay `unsat`).
- The two keymaera files' assertions, inlined verbatim (about 1 KB each).
  The calypto rows (6–7 KB of `let`s) are covered by measurement (§7).
- Ramalho: the minimized repro, either as `unsat` (fixed) or as a known-bug
  marker (§3.4).

### 6.3 Oracle (feature `oracle`, `oracle.rs`)

New family `differential_qf_lia_lra_polarity`. A seeded LCG generator builds
1–3 arithmetic atoms (`=`, `distinct`, `<=`) over 2–3 variables with small
coefficients and constants. It nests them under random `not`/`or`/`and`/
`=>`/`xor`/`ite`/Bool-`=` shapes of depth ≤ 3, and conjoins 0–2 bound pins.
200 scripts per sort (Int, Real), compared with z3.

- After the fix: 0 disagreements. The sat and unsat counts are recorded, and
  both must be non-zero.
- At HEAD (task 2): the family must report at least one disagreement. If it
  does not, strengthen the generator until it does; that is the evidence it
  covers the defect.
- Runtime target < 30 s, well under the 5-minute rule.

Run with `cargo nextest run -p shinri-solver --features oracle`, and confirm
a non-zero discovered count. A filtered run uses
`-E 'test(differential_qf_lia_lra_polarity)'`.

## 7. Measurement

Two runs with `mise run bench-run` at default limits (20 s, 3072 MB, 6 jobs):
`slice53-base` at HEAD `2ceef06` before any change, and `slice53` at the
slice head. Both cover QF_LIA, QF_LRA, QF_BVFP, QF_UFLIA, QF_UFLRA, QF_S and
QF_SLIA. That is every local logic that can produce arithmetic `=` atoms
(string length constraints included), plus QF_BVFP for ramalho. QF_LIA/LRA/
BVFP have no run since the baseline, so `slice53-base`, not the baseline, is
the comparison. A `wrong` row in `slice53-base` beyond the five in §1.1 is
checked against the fix; if the fix does not resolve it, it is listed and
queued.

### Success criteria

| # | criterion | kind |
| --- | --- | --- |
| 1 | keymaera ×2 and calypto ×2: `wrong → correct` (`unsat`) | hard |
| 2 | ramalho: `wrong → correct`, **or** a minimized repro pinned as a known-bug marker plus a queued cause (§3.4) | hard (either branch) |
| 3 | 0 rows `* → wrong` in all 7 logics | hard; any hit stops the slice for a ruling |
| 4 | every `correct → unknown/timeout` row listed and triaged; net `correct` ≥ 0 per logic. A net loss stops the slice for a ruling (slice-52 H3 precedent) | hard |
| 5 | §6.3 catches the defect at HEAD and shows 0 disagreements after the fix; oracle discovered count non-zero; `mise run lint`, `mise run test` and `ci` green | hard |
| 6 | median/p90 ms per logic reported against `slice53-base`; the axioms add clauses, so timing is measured, not assumed | measured |

## 8. Named reproducers

- §1.3, the minimal shapes.
- `QF_LRA/keymaera/simple_example_2-node2074.smt2` (1,046 B) and
  `-node2406.smt2` (1,045 B).
- `QF_LIA/calypto/problem-001542.cvc.1.smt2` (7,412 B) and
  `-001553.cvc.1.smt2` (6,484 B).
- `QF_BVFP/ramalho/esbmc/Float-no-simp9-main.smt2` (203,638 B), to be
  replaced in the report by its minimized core.

## 9. Banked, not built

- A polarity-tracking `lower` (approach B): superseded by the equivalence.
- Dropping `E` for pure-arithmetic equalities (approach C): smaller, but
  risks EUF congruence in UF+arithmetic logics.

## 10. Queued for the next slice

- Remove the redundant `Not(Eq) → (or Lt Gt)` arm, if the measurement shows
  the axioms alone are not slower.
- Ramalho, if §3.4 ends on the marker branch.
- Every item carried in the slice-52 report's *Queued for the next slice*
  (unchanged by this slice).

## 11. References

- Baseline: `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`
  (§ Next slices, rank 3); rows in
  `docs/superpowers/research/2026-09-09-smtlib-2024-baseline-report.md`
  (lines 558, 887–890).
- Slice-52 report: `docs/superpowers/research/2026-10-01-smtlib-2024-slice52-str-bool-eq-report.md`
  (§ Queued for the next slice).
- Code:
  - `crates/shinri-solver/src/lib.rs:1167` (the `lower` call site)
  - `:1791` (`is_pure_arith`)
  - `:2272` (`lower`; positive `Eq` arm)
  - `:2378` (the `Not(Eq)` arm from `07dd304`)
  - `:2445` (Boolean recursion; no Bool-`=` case)
  - `crates/shinri-solver/src/word_norm.rs` (n-ary split, term-`ite` lift)
  - `crates/shinri-solver/tests/oracle.rs`, `nary_arith_oracle.rs`
    (existing generators: mostly conjunctions)

## 12. Measured outcomes

To be filled in from the `slice53` report.
