# shinri QF_FP — Slice 2c′: `fp.sqrt` Design

**Date:** 2026-06-26
**Status:** Approved design, pre-implementation
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (architecture, approved)
**Roadmap:** `docs/superpowers/specs/2026-06-26-shinri-qffp-slice2c-div-design.md` §1 (Plan 2 sub-slice table)
**Builds on:** Slice 2c (landed 2026-06-26 — `blast/operand.rs`, the op-agnostic 5-mode rounder `round.rs` with the `ExtFp` contract, `lzc.rs`, `rm.rs`, the `fp.div` datapath with its `prenormalize` + **remainder→sticky** machinery, and `ref_div`'s exact-reference + IEEE special-table pattern)

This document specifies **Plan 2's sub-slice 2c′**: the `fp.sqrt` datapath. Per the brainstorming
decision on 2026-06-26, the original 2c (`fp.div` + `fp.sqrt`) was split — `fp.div` landed in 2c and
`fp.sqrt` is delivered here, reusing the remainder→sticky pattern 2c proved.

It does **not** revise the parent architecture — the engine model (eager bit-blast to the shared
`Blaster`), the `unpack → datapath → round → special-case → pack` pipeline, the `ExtFp` → `round()`
contract, and the soundness fence are all unchanged. Plan 2's remaining datapaths (`fma`, `rem`,
`roundToIntegral`, `min`/`max`) stay fenced to `Unknown`.

## 1. Why this slice / how it relates to `fp.div`

`fp.sqrt` is **unary** (operand + rounding mode) and reuses the 2c pipeline shape —
`unpack → prenormalize → datapath → ExtFp → round() → special-case mux` — but with three genuine
differences from `fp.div`:

1. **No `shinri-bv` primitive exists.** Division reused `shinri_bv::blast::div::udivurem`; the BV
   theory has **no `bvsqrt`**, so sqrt needs a *new* integer square-root circuit. This is the
   central new component of the slice.
2. **The exact-rational reference breaks.** `ref_div` returns an exact `Rational` quotient then
   calls `round_rational`. √(rational) is **irrational** — it cannot materialize as a `Rational`.
   `ref_sqrt` needs a different correctly-rounded oracle (§5).
3. **Exponent parity.** `√(m · 2^E)` splits on whether `E` is even or odd; the odd case folds a
   factor of 2 into the significand before the root (§4, Step B).

Two things are *simpler* than div:
- **No result leading-zero count.** After parity handling the radicand is in `[1, 4)`, so
  `√radicand ∈ [1, 2)` — the result's leading 1 is always at a fixed index. No `lzc` on the result
  (div needed one because a quotient lands in `[0.5, 2)`).
- **No divide-by-zero wrinkle.** `sqrt(±0)` is just a signed zero; the special table is smaller.

**Decision (2026-06-26): square-root primitive — restoring digit-recurrence.** A classic
shift-subtract-restore digit recurrence emits one result bit per iteration and naturally produces
both `floor(√R)` **and** the remainder `R − floor(√R)²` — exactly the remainder→sticky primitive
this slice needs, and the direct analogue of the restoring divider 2c trusts. Newton–Raphson (fewer
iterations, multiply-heavy, still needs a final remainder/correction check) and a non-restoring
variant (saves the restore step but adds sign-tracking and a remainder-correction add) were both
rejected for the same reasons div rejected them: throughput is not a concern at these operand widths,
and both add unproven machinery. The primitive lives in `shinri-fp` (`blast/sqrt.rs`), not
`shinri-bv`, because there is no BV-level `bvsqrt` consumer.

**Decision (2026-06-26): exact reference — round-by-squaring.** `ref_sqrt` computes the
correctly-rounded result with **exact integer arithmetic only**: scale the dyadic operand value,
take an integer floor-isqrt, then decide the rounding direction and detect ties by **squaring the
candidate result(s) and comparing as exact integers**. No irrational and no floating point ever
appears, so the oracle cannot have a last-bit error. The floor-isqrt building block is added to
`shinri-num` as `Integer::sqrt_rem` (§5), keeping `reference.rs` thin and the primitive reusable.

**Plan 2 sub-slice roadmap (updated):**

| # | Sub-slice | Delivers | Status |
|---|---|---|---|
| ~~2a~~ ✅ | `lzc.rs`, `round.rs` (5-mode), `blast/add.rs`, `rm.rs`; `fp.add`/`fp.sub` | landed |
| ~~2b~~ ✅ | `blast/operand.rs`, `blast/mul.rs`, `ref_mul`; `fp.mul` | landed |
| ~~2c~~ ✅ | `blast/div.rs`, `ref_div`; `fp.div` end-to-end | landed |
| **2c′** (this spec) | `blast/sqrt.rs`, `ref_sqrt`, `Integer::sqrt_rem`; `fp.sqrt` end-to-end | — |
| 2d | `fp.fma` | — |
| 2e | `fp.rem`, `fp.roundToIntegral`, `fp.min`/`fp.max` | — |

## 2. Scope & what changes

One new datapath, one reference function, one new `shinri-num` primitive, a small shared-helper
extraction, and two fence extensions. No architecture revision.

| File | Change |
|---|---|
| `crates/shinri-num/src/integer.rs` | **new** `Integer::sqrt_rem(&self) -> (Integer, Integer)` — exact floor-isqrt + remainder, with unit tests (§5) |
| `crates/shinri-fp/src/blast/normalize.rs` | **new** — `prenormalize` extracted out of `div.rs` into one shared, verified copy (§3) |
| `crates/shinri-fp/src/blast/div.rs` | use the shared `prenormalize`; drop the private copy |
| `crates/shinri-fp/src/blast/sqrt.rs` | **new** — the `fp.sqrt` datapath incl. the restoring integer-sqrt circuit (§4) |
| `crates/shinri-fp/src/blast/mod.rs` | register the `sqrt` and `normalize` modules |
| `crates/shinri-fp/src/reference.rs` | **new** `ref_sqrt` — round-by-squaring + IEEE special table (§5) |
| `crates/shinri-fp/src/lib.rs` | `blast_word` gains an `FpSqrt` arm (§6) |
| `crates/shinri-solver/src/fp_stage.rs` | add `FpSqrt` (RM, F) to `is_supported_fp_word` + `fp_atom_is_supported` (§6) |

**Still fenced to `Unknown`** (soundness contract unchanged): `fma`/`rem`/`roundToIntegral`/
`min`/`max`, all conversions, FP+BV mixing (Plan 4), FP+EUF/Arith/Arrays, and the Real bridge.
Slice 2c′ only **removes** `fp.sqrt` from the fenced set.

## 3. Shared operand + prenormalize helpers

`blast/operand.rs` already provides `Operand` / `to_operand` (sign, signed unbiased exponent in
`exp_w(eb)` bits, explicit significand, and `is_nan`/`is_inf`/`is_zero` flags) and the special-bit
constructors (`canon_nan_bits`, `inf_pattern_bits`, `signed_zero_bits`) — all reused as-is.

`prenormalize` (significand → leading 1 at index `sb-1`, with `exp_n = exp − shift`) currently lives
private inside `div.rs`. Both `fp.div` and `fp.sqrt` need it, so it is **extracted into a new
`blast/normalize.rs`** as `pub(crate) fn prenormalize`, and `div.rs` switches to the shared copy.
This is a mechanical move — no behavior change — and keeps a single verified implementation.

## 4. The `fp.sqrt` datapath (`blast/sqrt.rs`)

`pub fn fp_sqrt(b: &mut Blaster, x: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit>`.

Let `sbu = sb as usize`, `ew = exp_w(eb)`. Unpack `ox = to_operand(b, x, eb, sb)`.

**Step A — prenormalize.** `(sig_n, exp_n) = prenormalize(&ox.sig, &ox.exp)`. For finite nonzero
inputs `sig_n ∈ [2^(sb-1), 2^sb)` with `x = sig_n · 2^(exp_n − (sb−1))` (the `round()`/`ExtFp`
convention 2c established).

**Step B — exponent parity.** Decompose the (signed) exponent `exp_n = 2·h + c` with `c ∈ {0,1}` by
floor-division: `c = exp_n & 1` (LSB), `h = exp_n arithmetic-shr 1`. Form the **radicand mantissa**
`B = sig_n << c`, so `B ∈ [2^(sb-1), 2^(sb+1))` — the odd-exponent factor of 2 is absorbed into the
significand, leaving an even residual exponent `2h`.

**Step C — integer square root.** Choose radicand width `Wr = 2·(sb+2)`. Left-align `B` into a
`Wr`-bit word so the restoring digit recurrence produces a quotient `Q` of `sb+2` bits plus a
remainder `rem`. Because `B`'s value sits in `[1, 4)`, `√ ∈ [1, 2)` and **`Q`'s leading 1 is at a
fixed index** — no result `lzc`. The recurrence (one bit per iteration, `sb+2` iterations) maintains
a partial root `q` and partial remainder, at each step testing `(q<<1 | 1)·... ` via shift-subtract
and restoring on underflow; it yields `Q = floor(√radicand)` and `rem = radicand − Q²`. The exact
bit positions / shift constants are pinned by the §7 tiny-exhaustive test.

**Step D — GRS + sticky.** With `Q`'s leading 1 at the fixed top index: `sig = Q[top sb bits]`,
`G = Q[next bit]`, `R = Q[next bit]`, and **`S = OR(remaining low Q bits) OR (rem ≠ 0)`** — the
remainder→sticky fold proven in 2c (a non-perfect-square radicand has `rem ≠ 0`, forcing the round
to see an inexact result).

**Step E — exponent out.** `norm_exp = h + (correction const)`, where the constant reconciles the
radicand left-alignment shift with the `ExtFp` convention; pinned by the §7 exhaustive test.

**Step F — round.** Build `ext = ExtFp { sign: ox.sign /*provisional*/, exp: norm_exp, sig,
grs: (G, R, S) }` and call `round(b, ext, eb, sb, rm)` — reused unchanged. (The final sign is forced
by the special-case mux in §4.1, since the only sign-bearing results are the signed zeros.)

### 4.1 Special-case mux (overrides the rounded datapath)

Priority **NaN > Inf > Zero**, mirroring `div::special_case` but for the unary sqrt table. Let
`neg_nonzero = ox.sign AND NOT ox.is_zero` (any negative input that isn't `-0`).

- **NaN** when `want_nan = ox.is_nan OR neg_nonzero` (i.e. `ox.is_nan OR (ox.sign AND NOT
  ox.is_zero)`). This covers sNaN/qNaN inputs plus every negative nonzero value — `-∞`, `-normal`,
  `-subnormal` → `canon_nan_bits`.
- **Inf** when `ox.is_inf AND NOT ox.sign` (`+∞`) → `inf_pattern_bits(.., sign = 0)`.
- **Zero** when `ox.is_zero` → `signed_zero_bits(.., sign = ox.sign)` (**sign preserved**:
  `sqrt(+0)=+0`, `sqrt(-0)=-0`).
- Otherwise (finite positive nonzero) → the rounded datapath result, whose **sign is always `+`**.

Implemented as the same `mux2` cascade as div (zero, then inf, then nan override), so NaN wins ties.

## 5. Reference (`ref_sqrt`) and `Integer::sqrt_rem`

**`shinri-num` — `Integer::sqrt_rem(&self) -> (Integer, Integer)`.** Returns `(s, r)` with
`s = floor(√self)`, `r = self − s²`, `r ≥ 0`. Defined for `self ≥ 0` (panics/`debug_assert` on
negative, matching the crate's other partial ops). Implemented with a standard exact bignum
floor-isqrt (bit-by-bit or Newton-with-final-correction on `Integer`), using **only existing
`shinri-num` ops** (the crate has zero runtime dependencies). Unit-tested directly: perfect squares,
non-squares (remainder bookkeeping), 0/1, and large multi-limb values cross-checked against the
`num-bigint` dev-dependency.

**`ref_sqrt(eb, sb, a: &Integer, mode: RoundMode) -> Integer`.** Decode `a` (reusing `decode` /
`FpClass`). Special table identical in spirit to §4.1:

1. NaN in → `canonical_nan`.
2. Negative & nonzero (incl. `-∞`) → `canonical_nan`.
3. `+∞` → `inf_pattern(.., +)`.
4. `±0` → `zero_pattern(.., sign of input)`.
5. Finite positive nonzero → **round-by-squaring**:
   - The decoded value is dyadic: `v = M · 2^P` (integer `M`, signed `P`). Scale so the target
     significand bits land as integers: pick an even shift `2k` large enough that
     `R = M · 2^(2k − P)` (an exact integer, choosing `k` to clear `P`'s parity and supply ≥ `sb+2`
     fractional bits), and `√v = √R · 2^(−k)`.
   - `(s, r) = R.sqrt_rem()` gives `s = floor(√R)`, so `√v ∈ [s·2^(−k), (s+1)·2^(−k))`, exact when
     `r = 0`.
   - Determine the truncated `sb`-bit significand + unbiased exponent from `s` (its bit length is
     fixed by construction), then choose the correctly-rounded neighbor using **exact integer
     comparisons of squared candidates**: for round-to-nearest compare `R` against the squared
     midpoint between the two candidate representable values (`4R` vs `4s² + 4s + 1`-style integer
     tests so the `+0.5` ulp is exact), with `r ≠ 0` distinguishing strict inequality from a true
     tie; RNE/RNA resolve ties, RTP/RTN/RTZ pick the directed neighbor. All comparisons are integer
     multiplies/compares — no `Rational`, no float.
   - Handle subnormal/overflow rounding of the result through the same encode path `ref_div` uses
     (so subnormal results and the round-to-`+∞`/max boundary stay consistent with the rest of the
     reference).

This makes `ref_sqrt` a bit-exact oracle the datapath is diff-tested against (§7).

## 6. Wiring & soundness fence

**`lib.rs` `blast_word`.** New arm under `Op::Builtin(op)`:

```text
FpSqrt => {
    let rm  = self.rm_sel(ctx, args[0]);
    let xw  = self.blast_word(ctx, args[1]);
    crate::blast::sqrt::fp_sqrt(&mut self.b, &xw, &rm, eb, sb)
}
```

(`fp.sqrt` is `(RoundingMode, FP) → FP`; `args = [rm, x]`.)

**`fp_stage.rs` fence.** `fp.sqrt` is currently `Unknown`. Admit it:
- `is_supported_fp_word`: add an `FpSqrt` arm — `(RM, F)`, i.e. `kids.len() == 2`, `kids[0]` a
  `RoundingMode` term, `kids[1]` a `is_supported_fp_word`. (Distinct from the existing unary
  `FpAbs`/`FpNeg` arm, which has no RM operand, and from the ternary `FpAdd/Sub/Mul/Div` arm.)
- ensure `FpSqrt` reaches blasting in `fp_atom_is_supported` like the other admitted ops.

Everything else stays fenced; the change only **removes** `fp.sqrt` from the `Unknown` set.

## 7. Testing (mirrors 2c)

1. **`Integer::sqrt_rem` unit tests** (in `shinri-num`): perfect squares, non-squares with remainder
   check, 0/1, and large multi-limb values diffed against `num-bigint` (dev-dep).
2. **`fp_sqrt_tiny_exhaustive_all_modes`** — `(eb=3, sb=5)`, **all 256 input encodings × 5 rounding
   modes** vs `ref_sqrt` (1280 solves total — unary, far cheaper than div's 256²; runs un-gated).
3. **`fp_sqrt_float32_specials_and_random`** — `(eb=8, sb=24)`: the specials list (±0, ±∞, NaN,
   ±1, min normal/subnormal, max normal, a few negatives to exercise the NaN path) plus ~200
   deterministic-LCG random inputs × 5 modes vs `ref_sqrt`.
4. **Differential-vs-z3 oracle** for `fp.sqrt` over all five modes, bounded by a `SQRT_ITERS`
   constant (analogue of `DIV_ITERS`) for tractable gated runs; z3 supports `fp.sqrt`, so the 2c
   harness carries over directly.
5. **End-to-end** SAT/UNSAT + symbolic-RM + `get-model` smoke test through the solver, mirroring the
   `fp.div` end-to-end test, confirming the fence now admits `fp.sqrt`.

Gated/long suites (z3 oracle, float32 sweep) are run in background by the author per the established
workflow, not left to subagent loops.

## 8. Risks & mitigations

- **Restoring-sqrt off-by-one / bit-position constants** (Step C/E) — the highest-risk piece. Pinned
  by the un-gated tiny-exhaustive test (§7.2) which covers every `(eb=3,sb=5)` input across all
  modes, so any constant error fails fast and locally.
- **`sqrt_rem` correctness on large values** — covered by the direct `num-bigint` diff (§7.1) before
  it is ever used by `ref_sqrt`.
- **Round-by-squaring tie detection** — the one subtle reference path; the exhaustive tiny sweep
  exercises exact midpoints at small width, and the z3 oracle cross-checks float32.
- **Width `Wr = 2·(sb+2)` for binary128** reaches ~230 bits; the `const_n` total-mask guard added in
  2c (i128 overflow for `n ≥ 128`) already covers this — reuse it, do not reintroduce `1 << n`.
