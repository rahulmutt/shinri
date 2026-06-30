# shinri QF_FP — Slice 2g Design: `fp.rem`

**Date:** 2026-06-30
**Status:** Approved design, pre-implementation
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (architecture)
**Roadmap:** `docs/superpowers/specs/2026-06-25-shinri-qffp-vertical-slice-design.md` (§3, Plan 2)

## 0. Where this slice sits

This is the **final arithmetic op of Plan 2** (Rounder + arithmetic). Landed already:
`fp.add/sub` (2a), `fp.mul` (2b), `fp.div` (2c), `fp.sqrt` (2c′), relations + `fp.min/max`
(2d), `fp.roundToIntegral` (2e), `fp.fma` (2f). `fp.rem` is the only Plan-2 arithmetic op
still fenced to `Unknown` (`fp_stage.rs` lists `FpRem` in its "anything else → false" arm;
there is no `blast/rem.rs` and no `ref_rem`). Landing it closes Plan 2; the roadmap then
moves to Plan 3 (conversions + symbolic-Real fence) and Plan 4 (QF_BVFP unification).

`fp.rem` is RM-less: core declares it `(F, F) -> F` (`shinri-core/src/term.rs:89`,
alongside `FpMin/FpMax`), so its dispatch and fence-support shape follow the `fp.min/max`
two-operand pattern — **not** the `(RM, F)`/`(RM, F, F)` shapes of the rounded ops.

## 1. Semantics (the spec we encode)

`fp.rem(x, y) = x − y·n`, where `n = roundTiesToEven(x/y)` taken as an **exact integer**.
The result is **exact** and always representable (`|r| ≤ |y|/2`), and the operation is
**mode-independent** (there is no `RoundingMode` operand). Special cases (IEEE 754 §6.3 /
SMT-LIB `FloatingPoint`):

| Case | Result |
|---|---|
| any NaN operand | canonical NaN |
| `rem(±∞, y)` | NaN |
| `rem(x, ±0)` | NaN |
| `rem(x, ±∞)`, `x` finite | `x` (unchanged, faithful bits) |
| `rem(±0, y)`, `y` finite nonzero | `±0` with the **sign of `x`** |
| general result `= 0` | sign = **sign of `x`** |

The "tie" in `roundTiesToEven(x/y)` is the residue tie: when `2·|residue| == |y|` exactly,
`n` rounds so that it is even; this is what makes `|r| ≤ |y|/2` (not `< |y|`).

## 2. Reference oracle — `ref_rem` in `reference.rs`

A pure exact-`Rational` evaluator: the trusted golden semantics **and** the constant-folder
that `rewrite` will use. Logic:

1. Build `Rational` values for `x`, `y` via the existing `class_to_rational` path; read
   sign/special flags.
2. Dispatch the special-case table in §1 directly (no datapath).
3. Finite `x`, finite-nonzero `y`: `q = x / y`; `n = round-half-even(q)` using the existing
   `div_rem` + tie-to-even helpers already in `reference.rs`; `r = x − n·y` as an exact
   rational (necessarily dyadic and representable). Encode `r` into `(eb, sb)` with **no
   second rounding** — `r` is exact, so the encode is faithful (mirrors the
   "exactly representable → re-encode introduces no second rounding" note in
   `ref_round_to_integral`).
4. Zero result carries the **sign of `x`**.

`ref_rem` is unit-tested in isolation (specials + exact cases + ties) before any circuit
is asserted against it.

## 3. Circuit — `blast/rem.rs` (explicit reduction loop)

**Why a loop, not `udivurem`.** `fp.div` reuses a fixed-width `udivurem` (W = 2·sb+2)
because it needs only `sb` quotient bits + guard/round/sticky; the exponent is computed
separately. `fp.rem` needs the **full** integer quotient `n`, which for a large exponent
gap is astronomically large (≈2^2098 for Float64). Feeding the existing fixed-width
`udivurem` at width `~(sb + ED_MAX)` costs **O(ed²)** gates (~4–5M for Float64) and
materializes `n`. An explicit reduction loop that keeps the **residue narrow (~sb bits)**
and shifts its exponent costs **O(ed·sb)** (~250K for Float64) and produces the residue
`r` directly — the value `fp.rem` returns. Both have the same inherent `O(ed)` sequential
depth, but the loop is ~`ed/sb` ≈ 40× fewer gates. Soundness is equal (both exact) and is
guaranteed by bit-identical validation against `ref_rem` + the z3 differential.

**Pipeline:** unpack → special-case detect → exact reduction loop → round-to-even
correction → normalize → pack → special-case mux.

1. **Unpack** `x`, `y` → `(sign, signed exp, explicit sig, isNaN, isInf, isZero)` via the
   shared operand path.
2. **Special-case detect:** compute the NaN/∞/0 predicates for the final mux.
3. **Reduction loop**, unrolled to `ED_MAX` = the maximum unbiased exponent difference for
   the format (a compile-time function of `eb, sb`). Each stage: if the running residue's
   exponent ≥ `exp_y`, conditional-subtract a shifted `y` and shift the residue; the residue
   register stays ~`sb` bits wide. The loop also emits the **final quotient LSB** — the
   parity needed for the tie case. After the loop the residue magnitude is in `[0, |y|)`.
4. **Round-to-even correction:** compare `2·residue` against `|y|`. If `>` , or (`==` and
   the quotient parity is odd → round to even), set `r = residue − y`. Combine with the
   sign of `x`. This yields `|r| ≤ |y|/2`.
5. **Normalize:** LZC + left-shift (reuse `lzc` / `normalize`), because cancellation can
   drop the residue's exponent far below `exp_y` (possibly into the subnormal range).
6. **Pack:** reassemble `sign | exp | sig`. **No rounder** — `fp.rem` never rounds its
   result; the residue is exact.
7. **Special-case mux:** override the datapath output with the §1 table (canonical NaN /
   passthrough `x` / signed zero).

## 4. Dispatch + fence

- **`shinri-fp/src/lib.rs`:** new `FpRem =>` arm calling
  `blast::rem::fp_rem(b, &xw, &yw, eb, sb)` — **two FP operands, no RM**.
- **`shinri-fp/src/blast/mod.rs`:** declare `pub mod rem;`.
- **`shinri-solver/src/fp_stage.rs`:** add an `FpRem` arm to `is_supported_fp_word`
  mirroring `FpMin/FpMax` (`kids.len() == 2` && both operands recursively supported);
  remove `FpRem` from the "anything else (FpRem, …) → false" comment; extend the
  slice-enumeration doc-comment to mention slice 2g.

## 5. Canary repoint (budgeted, expected — not a surprise)

Per the established cross-slice pattern: admitting `fp.rem` flips every prior
`*_malformed_is_unknown` canary that nested `fp.rem` as its out-of-scope trigger from
`Unknown` to decidable, breaking it. As part of this slice:

1. Run the **whole** `cargo test -p shinri-solver --test fp_e2e` (the per-task review and
   the new op's own tests will not catch this — a self-contained new op looks clean in
   isolation).
2. `grep -n 'fp.rem\|FpRem' crates/shinri-solver/tests/` to find stale canaries.
3. Repoint each to nest **`fp.to_real`** (the FP→Real direction). Rationale: `fp.to_real`
   needs an FP↔Reals combination deferred to "a later combination design" — it stays
   fenced for **all of v1**, so this repoint should be the last one needed. The FP→Real
   direction specifically (not `to_fp`-from-Real, which Plan 3 partially admits for
   *constant* Reals) has no partial admission anywhere in v1. It trips the same
   unsupported-FP-op fence the canary is meant to guard.

## 6. Validation

- **Bit-identical vs `reference.rs`:** each gadget asserted equal to `ref_rem` —
  **exhaustive on `(3,5)`** (all 256² operand pairs), **randomized on Float16/Float32**.
  Explicitly seed `±0`, `±∞`, NaN (canonical + non-canonical payload), subnormals, normals,
  exact-tie residues (`2·r0 == |y|`), and large exponent gaps.
- **Deep-gap stress regression:** one deliberate worst-case (e.g. Float32 max-normal `rem`
  min-subnormal) asserting the query **solves and matches `ref_rem` without overflowing the
  SAT core** — the explicit guard against the `fp.div` deep-circuit stack-overflow failure
  mode (fixed by the iterative conflict minimizer; this confirms `fp.rem`'s deeper circuits
  stay within it).
- **z3 differential:** extend the feature-gated `fp_oracle.rs` corpus with `fp.rem` over
  feasible formats/gaps; agree on SAT/UNSAT.
- **End-to-end:** known SAT/UNSAT scripts with `get-model` round-trips (e.g.
  `(assert (fp.eq (fp.rem x y) z))`); a new `fp_rem_malformed_is_unknown` canary nesting
  `fp.to_real`.
- **Non-regression:** the full workspace `cargo test` stays green; the QF_BV path and the
  FP-private `Blaster` are untouched.

## 7. Soundness contract (unchanged from parent)

Anything outside this slice's scope returns `Unknown`, never a wrong verdict: FP+BV mixing
(until Plan 4), FP+EUF/Arith/Arrays, all conversions and any Real bridge (Plan 3+).
Sort/width errors are caught at sort-check in `shinri-core` before blasting.

## 8. Decisions locked for slice 2g

| Decision | Choice |
|---|---|
| Op | `fp.rem` — closes Plan 2 |
| RM operand | None — `(F, F) -> F`, mirrors `fp.min/max` dispatch/fence shape |
| Result | Exact, mode-independent, always representable (`|r| ≤ |y|/2`) |
| Circuit | Explicit reduction loop, O(ed·sb) (not full-width `udivurem`, O(ed²)) |
| Rounder | None — residue is exact; pack does not round |
| Oracle | `ref_rem` in `reference.rs`, exact-rational; round-half-even `n` |
| Canary repoint | `fp.to_real` (FP→Real) — durable for all of v1 |
| Deep-path testing | Deliberate worst-gap stress regression + exhaustive `(3,5)` |
