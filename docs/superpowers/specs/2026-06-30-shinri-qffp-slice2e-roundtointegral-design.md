# shinri QF-FP slice 2e — fp.roundToIntegral

**Date:** 2026-06-30
**Status:** Design (approved in brainstorming)
**Track:** QF-FP, follows slice 2d (relations + fp.min/fp.max)

## Goal

Add `(fp.roundToIntegral RM x)` — round a floating-point value to the
nearest integer-valued float according to the rounding mode — to shinri's
bit-blasted QF-FP path. Single FP operand plus a `RoundingMode`, producing an
FP word. This is the lightest of the three remaining Plan-2 rounding-bearing
ops (`fp.roundToIntegral`, `fp.fma`, `fp.rem`); `fp.fma`, `fp.rem`, and the
whole conversion suite stay fenced to `unknown`.

## Background / current state

The op is already parsed and **sort-checked**: `BuiltinOp::FpRoundToIntegral`
shares the `(RoundingMode, Float) -> Float` arm with `FpSqrt` at
`crates/shinri-core/src/context.rs:505`. What's missing is the reference
semantics, the circuit, the dispatch arm, and the fence admission.

The FP crate already provides everything this slice builds on:

- `unpack` / `blast::operand` — operand unpacking to
  `{ sign, exp, sig, is_nan, is_inf, is_zero }`.
- `round.rs`: the shared rounder `round(b, ExtFp, eb, sb, rm)` and the public
  `shift_right_sticky(b, x, amt) -> (shifted, sticky)` helper. The per-RM
  increment decision currently lives **inline** in `round()` Step 2
  (`round.rs:79-93`).
- `rm.rs`: `RmSel` (one-hot 5-mode selector), `literal`, `symbolic`.
- `reference.rs`: `decode`, exact `Rational` value of a class, the sign-aware
  tie logic at `reference.rs:315-325`, `round_rational(eb, sb, &Rational, mode)`
  (exact correctly-rounded encode), `canonical_nan`, and the `ref_*`
  differential references for every shipped op.
- The soundness fence in `crates/shinri-solver/src/fp_stage.rs`
  (`is_supported_fp_word`, `fp_atom_is_supported`) positively enumerates every
  op the blaster handles, so an unhandled FP op fails **closed**.

## Semantics

`fp.roundToIntegral RM x` (IEEE `roundToIntegral`, SMT-LIB `fp.roundToIntegral`):

- `x` is NaN → canonical NaN.
- `x` is ±∞ → `x` unchanged.
- `x` is ±0 → `x` unchanged.
- Otherwise round the exact value of `x` to an integer per `RM` and return that
  integer as a float. The result integer's magnitude is ≤ `|x|`, so it is always
  exactly representable and the result is always **finite**.
- **Sign preservation on a zero result:** when the rounded integer is `0` (e.g.
  `fp.roundToIntegral RNE -0.4 = -0.0`), the result carries the **sign of the
  input**, not `+0`.

All five rounding modes (`RNE, RNA, RTP, RTN, RTZ`) are supported, literal or
symbolic.

## Why this is a shallow slice

The input significand is already normalized (`1.fff` for normals; subnormals
have `|x| < 1` and fall in the zero/one special case). Rounding to integral
therefore **never moves the leading bit** except by an at-most-one carry. That
removes three sub-circuits that the general `round()` needs:

- **No leading-zero-count / renormalize** — result exponent = `input_exp`, or
  `input_exp + 1` on a single carry-out.
- **No subnormal-denormalize path** — any subnormal has `|x| < 1` and is handled
  by the `|x| < 1` special case (rounds to sign-preserving ±0 or ±1).
- **No overflow-to-∞** — the result magnitude is ≤ `|x|`, which was already
  representable.

The datapath is non-iterative: two barrel shifts plus one conditional
increment. Materially lighter than `fp.div`/`fp.sqrt`, which matters for the
known deep-circuit / SAT recursion-depth risk on bit-blasted FP ops.

## Design

### 1. Reference — `reference.rs::ref_round_to_integral(eb, sb, bits, mode) -> Integer`

Exact, on bit-patterns:

1. `decode` → class. NaN → `canonical_nan(eb, sb)`; ±∞ → `bits`; ±0 → `bits`.
2. Else take the exact `Rational` value `v` and round it to an integer `n` using
   the existing sign-aware tie logic (`reference.rs:315-325`).
3. If `n == 0`: return the **sign-preserving** zero (input sign bit, exp and
   trailing all zero).
4. Else return `round_rational(eb, sb, &Rational::from(n), mode)` — an
   exactly-representable integer rounds back to itself in every mode, so this
   re-encodes `n` without introducing a second rounding.

### 2. Shared rounding-increment helper

Extract `round()` Step 2 (`round.rs:79-93`) into:

```rust
pub fn rounding_increment(
    b: &mut Blaster, sign: BitLit, g: BitLit, r: BitLit, s: BitLit,
    lsb: BitLit, rm: &RmSel,
) -> BitLit
```

placed in `round.rs`. Refactor `round()` to call it — a pure, behavior-
preserving extraction (the existing FP oracle suite guards against regression).
Both `round()` and the new circuit use the single source of truth for per-RM
semantics, guaranteeing bit-identical rounding across all ops.

### 3. Circuit — new `blast/roundint.rs::fp_round_to_integral(b, x, rm, eb, sb) -> Vec<BitLit>`

1. Unpack `x` (reuse `blast::operand`).
2. Compute the fractional-bit count `f = clamp((sb-1) − unbiased_exp, 0, sb)`
   (small unsigned, saturated like `round()`'s denormalize-shift computation).
3. `shift_right_sticky(sig, f)` lands guard/round/sticky at fixed slots; the
   right-shifted value is the integer part, right-aligned.
4. `rounding_increment(b, sign, g, r, s, lsb, rm)` → add the increment at the
   LSB of the shifted value, then shift left by `f` to clear the fraction bits
   and place the increment back at position `f`.
5. Single-bit carry-out → `exp + 1` and significand `1.000…` (one mux, no LZC).
6. Final special-case mux over the unpacked flags: NaN → canonical NaN,
   ±∞ → input, ±0 → input, and sign-preserving ±1 / ±0 when `|x| < 1`
   (`f >= sb`, i.e. the integer part is empty).

### 4. Dispatch — `lib.rs` `blast_word`

Add an arm mirroring `FpSqrt` (`crates/shinri-fp/src/lib.rs:113`):

```rust
FpRoundToIntegral => {
    let rm = self.blast_rm(ctx, kids[0]);
    let xw = self.blast_word(ctx, kids[1]);
    crate::blast::roundint::fp_round_to_integral(&mut self.b, &xw, &rm, eb, sb)
}
```

Register `pub mod roundint;` in `crates/shinri-fp/src/blast/mod.rs`.

### 5. Fence — `fp_stage.rs::is_supported_fp_word`

Add `FpRoundToIntegral` to the `FpSqrt` arm (`fp_stage.rs:144-149`): same
`(RoundingMode, Float)` shape — `kids.len() == 2`, `is_rounding_mode_term(kids[0])`,
`is_supported_fp_word(kids[1])`. Every other FP op stays fail-closed.

## Testing

Matches the established slice cadence.

- **Reference unit tests** (`reference.rs`): known Float32 values across all five
  modes; the ±0 / ±∞ / NaN specials; the sign-preserving-zero cases
  (`-0.4` RNE → `-0.0`, `-0.5` RTN → `-1.0`); the `|x| < 1` boundary
  (`0.5`, `-0.5`, `0.4999…`); the carry-renormalize case
  (`fp.roundToIntegral RNE` of a value whose integer part is all ones → next
  power of two with `exp + 1`).
- **Differential-vs-z3 oracle** (`fp_oracle.rs`): random instances over all five
  modes and all formats, with a bounded iteration count consistent with the
  gated-suite policy (the multi-minute FP gate suites are run in the background
  by the implementer, not via looped subagents).
- **End-to-end** (`fp_e2e.rs`): SAT/UNSAT + symbolic-RM + `get-model`, plus a
  fence canary confirming a malformed `fp.roundToIntegral` still returns
  `unknown`.

## Non-goals

- `fp.fma`, `fp.rem`, and the conversion suite (`to_fp`, `to_ubv`, `to_sbv`,
  constant-Real, `fp.to_real`) remain fenced to `unknown`.
- No changes to the SAT core, Tseitin encoder, or model extraction.
- No persistent/incremental bit-blasting (re-blast per `check-sat`, as today).

**Soundness contract:** anything out of scope returns `unknown`, never a wrong
SAT/UNSAT verdict.
