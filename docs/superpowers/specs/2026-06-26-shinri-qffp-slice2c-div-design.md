# shinri QF_FP — Slice 2c: `fp.div` Design

**Date:** 2026-06-26
**Status:** Approved design, pre-implementation
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (architecture, approved)
**Roadmap:** `docs/superpowers/specs/2026-06-25-shinri-qffp-slice2a-add-design.md` §1 (Plan 2 sub-slice table) and `docs/superpowers/specs/2026-06-25-shinri-qffp-slice2b-mul-design.md` §1
**Builds on:** Slice 2b (landed 2026-06-25 — the shared `Operand`/`to_operand` in `blast/operand.rs`, the op-agnostic 5-mode rounder `round.rs` with the `ExtFp` contract, `lzc.rs`, `rm.rs`, and the `fp.mul` datapath, all bit-identical to `reference.rs`)

This document specifies the **first half of Plan 2's sub-slice 2c**: the `fp.div` datapath. Per the
brainstorming decision on 2026-06-26, the original 2c (`fp.div` + `fp.sqrt`) is **split** — `fp.div`
lands here (2c), and `fp.sqrt` is deferred to a follow-up slice (**2c′**) that reuses the
remainder→sticky machinery proven here.

It does **not** revise the parent architecture — the engine model (eager bit-blast to the shared
`Blaster`), the `unpack → datapath → round → special-case → pack` pipeline, the `ExtFp` → `round()`
contract, and the soundness fence are all unchanged. Plan 2's remaining datapaths (`sqrt`, `fma`,
`rem`, `roundToIntegral`, `min`/`max`) stay fenced to `Unknown`.

## 1. Why this slice / how it relates to `fp.mul`

`fp.div` is structurally a clone of the `fp.mul` slice — `unpack → datapath → LZC-normalize →
ExtFp → round() → special-case mux` — with three things swapped:

1. **Core operation:** an unsigned divide (reusing `shinri-bv`'s restoring divider) instead of the
   multiply.
2. **Special-case table:** divide-by-zero (`x/0 → ±∞`) is the new wrinkle absent from `mul`.
3. **Sticky derivation:** the division **remainder** must fold into the sticky bit `S`, because a
   quotient — unlike a product — is generally not exact.

That third point forces the one genuinely new structural piece: an **operand pre-normalization**
step that `fp.mul` did not need (§4, Step A).

**Decision (2026-06-26): divider primitive.** Reuse `shinri_bv::blast::div::udivurem`, the existing
unsigned **restoring** divider that already returns `(quotient, remainder)` — exactly the
remainder→sticky primitive this slice needs. A custom non-restoring/SRT divider (fewer gates) and a
Newton–Raphson reciprocal (hardware-FPU style) were both rejected: division throughput is not a
current concern, and both add unproven machinery, with Newton still needing a final remainder check
for correct rounding. Restoring division is O(n²) gates but the operand width here (`2·sb+2 ≈ 50`
for Float32) is small, and the divider is already exhaustively tested in `shinri-bv`.

**Plan 2 sub-slice roadmap (updated):**

| # | Sub-slice | Delivers | Status |
|---|---|---|---|
| ~~2a~~ ✅ | `lzc.rs`, `round.rs` (5-mode), `blast/add.rs`, `rm.rs`; `fp.add`/`fp.sub` | landed |
| ~~2b~~ ✅ | `blast/operand.rs`, `blast/mul.rs`, `ref_mul`; `fp.mul` | landed |
| **2c** (this spec) | `blast/div.rs`, `ref_div`; `fp.div` end-to-end | — |
| 2c′ | `blast/sqrt.rs`, `ref_sqrt`; `fp.sqrt` (reuses remainder→sticky) | — |
| 2d | `fp.fma` | — |
| 2e | `fp.rem`, `fp.roundToIntegral`, `fp.min`/`fp.max` | — |

## 2. Scope & what changes

One new datapath, one reference function, two one-line fence extensions. No architecture revision.

| File | Change |
|---|---|
| `crates/shinri-fp/src/blast/div.rs` | **new** — the `fp.div` datapath (§4) |
| `crates/shinri-fp/src/blast/mod.rs` | register the `div` module |
| `crates/shinri-fp/src/reference.rs` | **new** `ref_div` — exact-rational quotient + IEEE special tables (§5) |
| `crates/shinri-fp/src/lib.rs` | `blast_word` gains an `FpDiv` arm (§6) |
| `crates/shinri-solver/src/fp_stage.rs` | add `FpDiv` to `is_supported_fp_word` + `fp_atom_is_supported` (§6) |

**Still fenced to `Unknown`** (soundness contract unchanged): `sqrt`/`fma`/`rem`/`roundToIntegral`/
`min`/`max`, all conversions, FP+BV mixing (Plan 4), FP+EUF/Arith/Arrays, and the Real bridge.
Slice 2c only **removes** `fp.div` from the fenced set.

## 3. Shared operand helper (reused as-is)

`blast/operand.rs` already provides `Operand` (signed unbiased exponent in `exp_w` bits, an explicit
`sb`-bit significand with the hidden bit materialized, and `is_nan`/`is_inf`/`is_zero` flags) and the
`to_operand` constructor, plus the result-pattern builders `canon_nan_bits` / `inf_pattern_bits` /
`signed_zero_bits`. `fp.div` consumes all of these unchanged — no new shared helpers.

## 4. The `fp_div` datapath

Signature mirrors `fp_mul`:

```rust
pub fn fp_div(b: &mut Blaster, x: &[BitLit], y: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit>
```

Let `ew = exp_w(eb)`, `sbu = sb as usize`, `W = 2*sbu + 2` (dividend/divisor width),
`F = sbu + 2` (fractional bits of the quotient).

`let ox = to_operand(b, x, eb, sb); let oy = to_operand(b, y, eb, sb);`

The datapath only needs to be correct for **finite-nonzero ÷ finite-nonzero**; every other operand
class (Zero/Inf/NaN) is overridden by §4.6's special-case mux, so garbage produced here for those
inputs is harmless.

### 4.1 Step A — operand pre-normalization (new vs `fp.mul`)

`fp.mul` fed operand significands straight to the multiplier because a product is **exact** (finite
bits), so the post-multiply LZC merely repositions real bits. A quotient is **not** exact: when the
ratio `Q < 1`, a raw post-divide LZC would left-fill the low bits with *fake* zeros, discarding real
quotient precision. The fix is to pre-normalize each operand significand so the ratio lands in a
known narrow range and the fractional precision is computed explicitly.

For each operand `o ∈ {ox, oy}`:
- `k = lzc(o.sig)` — leading-zero count placing the leading 1 at index `sb-1`.
- `sig_norm = o.sig << k` (now `sig_norm ∈ [2^(sb-1), 2^sb)` for finite-nonzero operands).
- `exp_n = o.exp - k` (signed, `ew` bits) — keeps the operand value invariant, since
  `value = sig · 2^(exp-(sb-1)) = sig_norm · 2^((exp-k)-(sb-1))`.

Yielding `(xsig_norm, exp_x_n)` and `(ysig_norm, exp_y_n)`.

### 4.2 Step B — divide with fixed fractional bits

- `D = zero_extend(xsig_norm, W) << F` (the constant shift `F`, built as an `ew`/`W`-bit constant).
- `divisor = zero_extend(ysig_norm, W)`.
- `let (quot, rem) = shinri_bv::blast::div::udivurem(b, &D, &divisor);` — `quot`, `rem` each `W` bits.

Because both normalized significands lie in `[2^(sb-1), 2^sb)`, the true ratio `Q ∈ (1/2, 2)`, so
`quot = floor(Q · 2^F) ∈ [2^(F-1), 2^(F+1))` — its leading 1 is at index `F` or `F-1`, hence
**`lz ∈ {sb-1, sb}` only**. Bounding `lz` to two values is the entire purpose of Step A and is what
makes a fixed `F` sufficient.

### 4.3 Step C — normalize and extract GRS

Identical in shape to `fp_mul`:
- `let lz = lzc(b, &quot);` then `let quot_n = bvshl(b, &quot, &zero_extend(lz, W));` (leading 1 at `W-1`).
- `sig = quot_n[(W - sbu)..W]` — top `sb` bits, hidden at index `sb-1`.
- `g = quot_n[W - sbu - 1]`, `r = quot_n[W - sbu - 2]`.
- `s = OR(quot_n[0 .. W - sbu - 2]) OR (rem != 0)` — the remainder folds into the sticky bit. (Test
  `rem != 0` with an OR-reduction over all `W` bits of `rem`.)

With `W - sbu = sbu + 2` and `lz ∈ {sb-1, sb}`, the bits read for `g` and `r` are always **real
computed quotient bits**, never left-fill zeros; everything below `r` plus the nonzero-remainder
flag is captured by `s`. This is the remainder→sticky pattern `fp.sqrt` (2c′) will reuse.

### 4.4 Step D — exponent

`E = exp_x_n - exp_y_n + (sb-1) - lz` (signed, `ew` bits; build `(sb-1)` as an `ew` constant, then
`bvadd`/`bvsub`).

Derivation: extracting the top `sb` bits after a left shift of `lz` gives
`Sig ≈ quot >> (W - sb - lz)`, and equating the rounder's interpretation
`Sig · 2^(E-(sb-1))` to the true quotient value `Q · 2^(exp_x_n - exp_y_n)` cancels to the formula
above. It is the same shape as `fp.mul`'s `norm_exp = exp_sum + 1 - lz`, with `1` replaced by
`(sb-1)` and `exp_sum` replaced by `exp_x_n - exp_y_n`.

**Headroom:** `exp_w = eb + 6` is unchanged and ample. Worst-case `|E| ≈ 2·bias + sb`, which for
every IEEE format (incl. Float128, `eb=15`) is far below `2^(eb+5)`. The tiny-exhaustive and
Float32 differential tests exercise the signed exponent arithmetic end-to-end.

### 4.5 Step E — round

```rust
let ext = ExtFp { sign: b.xor2(ox.sign, oy.sign), exp: E, sig, grs: (g, r, s) };
let rounded = round(b, ext, eb, sb, rm);
```

### 4.6 Step F — special-case mux

Priority **NaN > Inf > Zero**, with `res_sign = ox.sign XOR oy.sign` for all cases (including
specials and zeros), exactly as `fp.mul`. Conditions:

- `want_nan = ox.is_nan OR oy.is_nan OR (ox.is_zero AND oy.is_zero) OR (ox.is_inf AND oy.is_inf)`
- `want_inf = (ox.is_inf AND NOT oy.is_inf) OR (oy.is_zero AND NOT ox.is_zero)` — the `x/0 → ±∞`
  case (IEEE *divByZero*; no exception flags are in scope for v1).
- `want_zero = (ox.is_zero AND NOT oy.is_zero) OR (oy.is_inf AND NOT ox.is_inf)`

Applied to the rounded word as `mux2(want_zero, zero_bits, ·)` → `mux2(want_inf, inf_bits, ·)` →
`mux2(want_nan, nan_bits, ·)`, reusing `signed_zero_bits` / `inf_pattern_bits(res_sign)` /
`canon_nan_bits`.

This table is verified against all ten IEEE division class combinations:

| x \\ y | 0 | finite≠0 | ∞ | NaN |
|---|---|---|---|---|
| **0** | NaN | ±0 | ±0 | NaN |
| **finite≠0** | ±∞ | normal (datapath) | ±0 | NaN |
| **∞** | ±∞ | ±∞ | NaN | NaN |
| **NaN** | NaN | NaN | NaN | NaN |

(`±` is `res_sign`.) Each non-`normal`, non-`NaN` cell is reproduced by `want_inf`/`want_zero`
above; `NaN` cells by `want_nan`; the `normal` cell falls through to the rounded datapath result.

## 5. Reference `ref_div`

A near-clone of `ref_mul`, same `decode → class ladder → class_to_rational → round_rational`
skeleton, with the §4.6 division special-case table substituted for multiplication's, and exact
`Rational` division for the finite-nonzero case:

```rust
/// Result sign is sign_a XOR sign_b (including specials and zeros).
pub fn ref_div(eb: u32, sb: u32, a: &Integer, b: &Integer, mode: RoundMode) -> Integer {
    // decode a, b; sign = is_negative(a) ^ is_negative(b)
    // 1. either NaN                       -> canonical_nan
    // 2. (a_zero && b_zero) || (a_inf && b_inf) -> canonical_nan
    // 3. a_inf || b_zero(&& a finite-nonzero)   -> inf_pattern(sign)   // x/0, inf/finite
    // 4. b_inf || a_zero                        -> zero_pattern(sign)  // finite/inf, 0/finite
    // 5. finite/finite-nonzero: round_rational(eb, sb, &(ra / rb), mode)
}
```

`Rational` division is exact, so this is a trusted oracle independent of the gate-level datapath.
The arm ordering above is written to respect the same NaN > Inf > Zero priority as §4.6 (NaN arms
precede the Inf/Zero arms).

## 6. Fence wiring

Two one-line additions, exactly like 2b:
- `crates/shinri-fp/src/lib.rs` — a `FpDiv` arm in `blast_word`, reading `kids[1]`/`kids[2]` as the
  two FP operands and `kids[0]` as the rounding mode (same shape as the `FpMul` arm), calling
  `fp_div`.
- `crates/shinri-solver/src/fp_stage.rs` — add `FpDiv` to both `is_supported_fp_word` and
  `fp_atom_is_supported`, removing it from the fenced set.

## 7. Testing (mirrors 2b's three-tier strategy)

1. **`fp_div_tiny_exhaustive_all_modes`** — all `256×256` `(eb,sb)=(3,5)` input pairs × all five
   rounding modes, asserting `eval_word(fp_div(...)) == ref_div(...)`. This exhaustively covers every
   divide-by-zero, subnormal, zero, inf, and NaN combination at the tiny width.
2. **`fp_div_float32_specials_and_random`** — the `(8,24)` specials list (zeros, ±∞, NaN, ±1, min
   normal/subnormal, max normal) crossed with itself, plus ~200 deterministic-LCG random pairs ×
   five modes, vs `ref_div`.
3. **Differential-vs-Z3 oracle** — `fp.div` over all five rounding modes, matching the existing
   `fp.mul` Z3 differential harness.
4. **End-to-end** SAT/UNSAT + symbolic-rounding-mode + `(get-model)` test through the solver, like
   the existing `fp.mul` end-to-end test.

## 8. Soundness

Unchanged from the parent contract: `fp.div` is admitted through the FP soundness fence only after
the datapath is bit-identical to `ref_div` across the tiny-exhaustive and Float32 differential
suites and the Z3 oracle. Anything still out of scope returns `unknown`, never a wrong verdict.
