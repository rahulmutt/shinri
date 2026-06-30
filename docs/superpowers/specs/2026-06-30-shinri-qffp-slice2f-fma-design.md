# shinri QF-FP slice 2f — fp.fma

**Date:** 2026-06-30
**Status:** Design (approved in brainstorming)
**Track:** QF-FP, follows slice 2e (fp.roundToIntegral)

## Goal

Add `(fp.fma RM x y z)` = `round(x·y + z)` with **exactly one rounding** to
shinri's bit-blasted QF-FP path. Three FP operands plus a `RoundingMode`,
producing an FP word. This is the last remaining Plan-2 arithmetic op besides
`fp.rem`; `fp.rem` and the whole conversion suite stay fenced to `unknown`.

The defining IEEE constraint is the **single rounding**: the exact real value
`x·y + z` is formed at full width and rounded once. The naive "call `fp_mul`
then `fp_add`" rounds twice and is wrong — which is exactly why `fma` needs its
own datapath.

## Background / current state

The op is already parsed and **sort-checked**: `BuiltinOp::FpFma` carries the
`(RoundingMode, Float, Float, Float) -> Float` shape. What's missing is the
reference semantics, the circuit, the dispatch arm, and the fence admission.

The FP crate already provides everything this slice builds on:

- `unpack` / `blast::operand::to_operand` — operand unpacking to
  `{ sign, exp (signed, exp_w bits), sig (sb bits, hidden at sb-1), is_nan,
  is_inf, is_zero }`. Zero/subnormal operands get `exp = emin`, hidden bit 0.
- `blast/mul.rs::fp_mul` — the exact `2·sb` significand product plus the uniform
  LZC normalize (`prod_n = prod << lz`, `norm_exp = ex+ey+1-lz`) that already
  absorbs subnormal inputs (gated by `mul`'s `(3,5)` exhaustive test).
- `blast/add.rs::fp_add` — the magnitude-order hi/lo selection, sticky-collecting
  right-align, effective add/sub, carry/LZC normalize, and the zero-sum sign
  rule (`reference.rs` `ref_add`).
- `round.rs`: the shared rounder `round(b, ExtFp, eb, sb, rm)` (subnormal
  denormalize, increment, carry-renormalize, overflow→∞, underflow→subnormal/
  zero) and the public `shift_right_sticky(b, x, amt)` helper.
- `rm.rs`: `RmSel` (one-hot 5-mode selector), `literal`, `symbolic`.
- `reference.rs`: `decode`, `class_to_rational`, `round_rational`, `canonical_nan`,
  `inf_pattern`, `zero_pattern`, `ref_is_negative`, plus the `ref_*` differential
  references for every shipped op (`ref_add`, `ref_mul` are the templates here).
- The soundness fence in `crates/shinri-solver/src/fp_stage.rs`
  (`is_supported_fp_word`, `fp_atom_is_supported`) positively enumerates every op
  the blaster handles, so an unhandled FP op fails **closed**.

## Semantics

`fp.fma RM x y z` (IEEE `fusedMultiplyAdd`, SMT-LIB `fp.fma`):

- Any operand NaN → canonical NaN.
- Invalid product `0·∞` (either order) → canonical NaN, regardless of `z`.
- Product is ±∞ (x or y ∞, not the invalid case): if `z` is ∞ of the **opposite**
  sign → canonical NaN; otherwise the product's signed ∞.
- `z` is ±∞ (product finite) → `z` unchanged.
- Otherwise the result is the exact real `x·y + z`, rounded **once** under `RM`.
- **Exact-zero sum sign rule:** when `x·y + z` is exactly `0`, the result is `-0`
  iff `(prod_sign ∧ sign_z) ∨ RM = roundTowardNegative`, else `+0`, where
  `prod_sign = sign_x ⊕ sign_y`. (Same rule as `fp.add`, with the product sign on
  the left.)

All five rounding modes (`RNE, RNA, RTP, RTN, RTZ`) are supported, literal or
symbolic.

## Design

### 1. Reference — `reference.rs::ref_fma(eb, sb, x, y, z, mode) -> Integer`

Exact, on bit-patterns; fuses `ref_mul` and `ref_add`:

1. `decode` x, y, z. `prod_sign = ref_is_negative(x) ⊕ ref_is_negative(y)`.
2. **NaN:** any operand NaN → `canonical_nan(eb, sb)`.
3. **Invalid product:** `x.zero ∧ y.inf` or `x.inf ∧ y.zero` → `canonical_nan`.
4. **Infinities:**
   - Product ∞ (`x.inf ∨ y.inf`, not invalid): if `z.inf ∧ sign_z ≠ prod_sign`
     → `canonical_nan`; else `inf_pattern(eb, sb, prod_sign)`.
   - Else `z.inf` → `inf_pattern(eb, sb, sign_z)`.
5. **Finite:** `v = class_to_rational(x)·class_to_rational(y) + class_to_rational(z)`
   (exact `Rational`). If `v == 0` → `zero_pattern(eb, sb, neg)` with
   `neg = (prod_sign ∧ sign_z) ∨ (mode == Rtn)`. Else
   `round_rational(eb, sb, &v, mode)` — the single rounding.

Because it forms the exact product-plus-addend before one `round_rational`, this
is the trusted definition of single-rounding and the differential oracle.

### 2. Circuit — `blast/fma.rs::fp_fma(b, x, y, z, rm, eb, sb) -> Vec<BitLit>`

The chosen scheme: **`fp_add`'s datapath at significand width `2·sb`**, with `z`
zero-extended so both addends share one significand format. Non-iterative (no SAT
recursion-depth blowup).

1. **Product significand (exact, reuse `mul`'s path):** `prod = xsig·ysig`
   (`2sb` bits); uniform LZC normalize → `prod_n` (leading bit at index `2sb-1`),
   `norm_exp = ex + ey + 1 - lz`. No rounding here. Subnormal inputs are absorbed
   by this normalize.
2. **Two addends in one `2sb`-significand format** (common scale
   `value = sig · 2^(e-(2sb-1))`):
   - **product:** sig = `prod_n`, exp = `norm_exp`, sign = `prod_sign`.
   - **z:** `zsig << sb` (the `sb`-bit `z` significand placed in the top half, so
     its hidden bit lands at index `2sb-1`), exp = `ez`, sign = `sign_z`.
     Scale check: `(zsig << sb) · 2^(ez-(2sb-1)) = zsig · 2^(ez-(sb-1))`. ✓
   - **Zero-product clamp:** when `x.zero ∨ y.zero`, the product significand is 0
     and its LZC-of-zero `norm_exp` is garbage; force the product exp to `emin` so
     it behaves as a true `±0` addend and the add skeleton's zero handling (with
     `prod_sign`) governs the result.
3. **Add skeleton at width `2sb+3`** (the `fp_add` structure, verbatim in shape):
   magnitude-order the two addends into hi/lo by `(exp, sig)`; prepend 3 GRS
   columns; sticky-collecting right-shift lo by `hi.exp - lo.exp`; effective add
   if signs equal else subtract (hi ≥ lo so the difference is non-negative);
   normalize by add-carry (shift right 1, exp+1) or LZC left-shift (exp-=lz),
   tracking the exponent of the leading bit.
4. **Single round.** The normalized mantissa is `2sb+3` wide. Extract the **top
   `sb` bits** as the significand and collapse the remaining low bits into
   `(G, R, S)` = (bit just below the significand, next bit, OR of all the rest) —
   the `mul`-style GRS extraction (`add` keeps exactly 3 GRS columns because its
   mantissa is `sb+3`; here it is `2sb+3`, so the surplus folds into sticky).
   Build `ExtFp { sign = res_sign, exp = leading-bit exp, sig, grs }` and call the
   shared `round()` **once**. `round()` supplies subnormal denormalize,
   carry-renormalize, overflow→∞, and underflow→subnormal/zero.
5. **Special-case mux** (priority NaN > Inf > product-zero / cancel-zero >
   normal), the union of the reference's product-formation specials and
   `fp_add`'s zero-sum sign rule:
   - `want_nan = x.nan ∨ y.nan ∨ z.nan ∨ (x.zero ∧ y.inf) ∨ (x.inf ∧ y.zero) ∨
     (prod_inf ∧ z.inf ∧ (sign_z ⊕ prod_sign))`, where
     `prod_inf = (x.inf ∨ y.inf) ∧ ¬invalid`.
   - `any_inf = prod_inf ∨ z.inf`; inf sign = `prod_inf ? prod_sign : sign_z`.
   - Cancel-zero (exact-zero finite sum) → `zero_pattern` with
     `neg = (prod_sign ∧ sign_z) ∨ RTN` (the zero-product clamp routes the
     `0·finite + z` case through this same handling).

Exact bit offsets and the guard-column width fall out of the `(3,5)` exhaustive
gate — the same empirical method that fixed `mul`'s `CORR=1` exponent offset.

### 3. Dispatch — `lib.rs` `blast_word`

Add an arm mirroring the three-FP-operand shape:

```rust
FpFma => {
    let rm = self.blast_rm(ctx, kids[0]);
    let xw = self.blast_word(ctx, kids[1]);
    let yw = self.blast_word(ctx, kids[2]);
    let zw = self.blast_word(ctx, kids[3]);
    crate::blast::fma::fp_fma(&mut self.b, &xw, &yw, &zw, &rm, eb, sb)
}
```

Register `pub mod fma;` in `crates/shinri-fp/src/blast/mod.rs`.

### 4. Fence — `fp_stage.rs::is_supported_fp_word`

Add an `FpFma` arm: same `(RoundingMode, Float, Float, Float)` shape —
`kids.len() == 4`, `is_rounding_mode_term(kids[0])`, and `kids[1]`, `kids[2]`,
`kids[3]` each recursively `is_supported_fp_word`. Every other FP op stays
fail-closed.

## Testing

Matches the established slice cadence.

- **Reference unit tests** (`reference.rs`): known Float32 fma triples across all
  five modes; a **single-rounding witness** (a triple where `mul`-then-`add`
  double-rounds to a different bit pattern than the fused result); the specials
  (`0·∞`, `∞ + (−∞)`, `z` is ∞, NaN propagation); the product-zero + `±0`
  sign-rule cases; a massive-cancellation case (`x·y ≈ −z`); a subnormal-product
  case.
- **Bit-identical gate** (`blast/fma.rs` tests): `(3,5)` exhaustive over a bounded
  triple sample × 5 modes vs `ref_fma`; Float32 specials + bounded random.
- **Differential-vs-z3 oracle** (`fp_oracle.rs`): random `fp.fma` instances over
  all five modes and all formats, with a bounded iteration count consistent with
  the gated-suite policy.
- **End-to-end** (`fp_e2e.rs`): SAT/UNSAT + symbolic-RM + `get-model`, plus a
  fence canary confirming a malformed (arity-3) `fp.fma` still returns `unknown`.
- **Depth caution.** `fma` is the deepest datapath shipped so far (`2sb`
  multiply + `2sb` LZC and barrel shifts + the rounder). Per the known
  deep-circuit / SAT recursion-depth risk for bit-blasted FP ops (observed on
  `fp.div`), the multi-minute FP gate suites are **bounded** and **run in the
  background by the implementer**, not via looped subagents.

## Non-goals

- `fp.rem` and the conversion suite (`to_fp`, `to_fp_unsigned`, `fp.to_ubv`,
  `fp.to_sbv`, constant-Real `to_fp`, `fp.to_real`) remain fenced to `unknown`.
  The conversion suite additionally needs QF-BVFP unification (one shared
  `Blaster`), which the FP stage currently defers.
- No changes to the SAT core, Tseitin encoder, or model extraction.
- No persistent/incremental bit-blasting (re-blast per `check-sat`, as today).

**Soundness contract:** anything out of scope returns `unknown`, never a wrong
SAT/UNSAT verdict.
