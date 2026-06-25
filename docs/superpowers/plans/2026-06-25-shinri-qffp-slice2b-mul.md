# QF_FP Slice 2b — `fp.mul` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bit-blast `fp.mul` for QF_FP end-to-end (parse → blast → SAT → model) by reusing the slice-2a op-agnostic rounder and the `shinri-bv` multiplier, validated bit-identical to a new exact-rational reference oracle (`ref_mul`) and differentially against z3.

**Architecture:** Eager bit-blasting into the slice-1 `FpBlaster`. `fp.mul` is structurally simpler than `fp.add` — no operand ordering, no alignment shift, no add/sub split. It unpacks both operands (the shared `to_operand` helper lifted out of `add.rs`), XORs the signs, sums the unbiased exponents, multiplies the two `sb`-bit significands to a full `2·sb`-bit product (zero-extend then `bvmul`), renormalizes the product with a single uniform leading-zero-count + left-shift (handling subnormal inputs in one path), builds an `ExtFp`, and calls the slice-2a `round()`. A final IEEE special-case mux overrides for NaN / `0·∞` / ∞ / zero. Everything out of scope stays a sound `Unknown`.

**Tech Stack:** Rust, `shinri-fp` crate (depends on `shinri-bv`, `shinri-core`, `shinri-num`), the `shinri-sat` CDCL core for tests, `easy_smt` + z3 for the differential oracle (feature-gated).

## Global Constraints

- **Bit layout** (fixed by the foundation): a Float word is `W = eb + sb` bits, **LSB→MSB**, MSB-to-LSB meaning `[ sign(1) | exponent(eb) | trailing-significand(sb-1) ]`. `sb` **includes** the hidden bit.
- **Soundness contract:** anything outside the now-supported ops (`FpAbs`/`FpNeg`/`FpAdd`/`FpSub` and, after this slice, `FpMul`) returns `Unknown`, never a wrong SAT/UNSAT. `div`/`sqrt`/`fma`/`rem`/`roundToIntegral`/`min`/`max`, all conversions, FP+BV mixing, FP+EUF/Arith/Arrays, and any Real bridge stay fenced.
- **Validation anchor:** the `fp.mul` datapath MUST be bit-identical to `reference.rs::ref_mul` (added in Task 1). Exhaustive on the `(3,5)` tiny format over all five modes; randomized on Float32. The slice-2a `round()` is reused **unchanged** — 2b adds no rounder logic.
- **No new external dependencies.** Reuse `shinri-bv` helpers (`bvmul`, `bvadd`, `bvsub`, `bvshl`) and `Blaster` primitives (`and2`, `or2`, `xor2`, `not1`, `mux2`, `one`, `zero`). The significand multiply uses `shinri_bv::blast::arith::bvmul`, which **truncates to its input width** — so both significands are zero-extended to `2·sb` bits before the call to obtain the full `2·sb`-bit product.
- **`RoundingMode` encoding:** unchanged from 2a — the `rm.rs` selector (`literal`/`symbolic`) and `FpBlaster::blast_rm` already exist; `fp.mul` consumes them identically to `fp.add`.
- **Reference rounding-mode type:** `reference.rs` uses its own `RoundMode { Rne, Rna, Rtp, Rtn, Rtz }`; map `shinri_core::RoundingMode` → `reference::RoundMode` 1:1 in tests (the `rmode` helper already exists in the test modules).
- **Sign rule (mul):** result sign is `sign_x XOR sign_y` **always**, including specials and zeros. There is NO mode-dependent zero-sign rule (unlike `fp.add`'s `RTN` rule).

---

## File Structure

| File | Status | Responsibility |
|---|---|---|
| `crates/shinri-fp/src/reference.rs` | Modify | Add `ref_mul` (exact-rational golden `fp.mul`). |
| `crates/shinri-fp/src/blast/operand.rs` | Create | Shared `Operand` + `to_operand` + the canonical-NaN / inf / signed-zero pattern builders, lifted out of `add.rs` so `add` and `mul` share one copy. |
| `crates/shinri-fp/src/blast/add.rs` | Modify | Delete the now-shared `Operand`/`to_operand`/pattern-builder copies; import them from `operand`. |
| `crates/shinri-fp/src/blast/mul.rs` | Create | The `fp.mul` datapath + IEEE special-case mux. |
| `crates/shinri-fp/src/blast/mod.rs` | Modify | Add `pub mod operand;` and `pub mod mul;`. |
| `crates/shinri-fp/src/lib.rs` | Modify | `blast_word` gains an `FpMul` arm. |
| `crates/shinri-solver/src/fp_stage.rs` | Modify | Admit `FpMul` in `is_supported_fp_word`; flip the `fp_mul_word_is_not_supported` test to a positive test + a `fp.div`-fenced negative test. |
| `crates/shinri-solver/tests/fp_e2e.rs` | Modify | End-to-end `fp.mul` SAT/UNSAT + symbolic-RM + get-model. |
| `crates/shinri-solver/tests/fp_oracle.rs` | Modify | Differential-vs-z3 over `fp.mul`, all five modes. |

Task ordering: **1 (ref_mul) → 2 (shared operand) → 3 (mul datapath) → 4 (lib wiring) → 5 (fence) → 6 (e2e) → 7 (oracle) → 8 (sweep).** Task 1 is independent of Task 2 and may be done in either order before Task 3.

---

### Task 1: Exact-rational reference `fp.mul` (`ref_mul`)

The golden oracle the datapath is checked against. Pure Rust over `shinri-num::Rational`; no circuit. Reuses the existing `decode`, `class_to_rational`, `round_rational`, `canonical_nan`, `inf_pattern`, `zero_pattern`, and `RoundMode` already in `reference.rs` (added in slice 2a).

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (append a function + tests)

**Interfaces:**
- Consumes: `decode(eb, sb, &Integer) -> FpClass`, `class_to_rational(eb, sb, &FpClass) -> Option<Rational>`, `round_rational(eb, sb, &Rational, RoundMode) -> Integer`, `canonical_nan(eb, sb) -> Integer`, `inf_pattern(eb, sb, bool) -> Integer`, `zero_pattern(eb, sb, bool) -> Integer`, `ref_is_negative(&FpClass) -> bool`, `FpClass`, `RoundMode` (all already in `reference.rs`).
- Produces: `pub fn ref_mul(eb: u32, sb: u32, a: &Integer, b: &Integer, mode: RoundMode) -> Integer` — canonical NaN for `NaN·x` and `0·∞`; signed ∞ for `∞·finite-nonzero`; signed zero for `0·finite`; else `round_rational(exact_product)`. Result sign is always `sign_a XOR sign_b`.

- [ ] **Step 1: Write the failing test**

Append to the `#[cfg(test)] mod tests` block in `reference.rs`:

```rust
#[test]
fn ref_mul_known_float32() {
    let (eb, sb) = (8u32, 24u32);
    // 1.0 * 1.0 = 1.0
    assert_eq!(ref_mul(eb, sb, &i(0x3F80_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x3F80_0000));
    // 2.0 * 3.0 = 6.0 = 0x40C00000
    assert_eq!(ref_mul(eb, sb, &i(0x4000_0000), &i(0x4040_0000), RoundMode::Rne), i(0x40C0_0000));
    // 2.0 * -1.0 = -2.0 = 0xC0000000  (sign = XOR)
    assert_eq!(ref_mul(eb, sb, &i(0x4000_0000), &i(0xBF80_0000), RoundMode::Rne), i(0xC000_0000));
    // -1.0 * -1.0 = 1.0  (sign XOR cancels)
    assert_eq!(ref_mul(eb, sb, &i(0xBF80_0000), &i(0xBF80_0000), RoundMode::Rne), i(0x3F80_0000));
    // +inf * 2.0 = +inf
    assert_eq!(ref_mul(eb, sb, &i(0x7F80_0000), &i(0x4000_0000), RoundMode::Rne), i(0x7F80_0000));
    // +inf * -2.0 = -inf
    assert_eq!(ref_mul(eb, sb, &i(0x7F80_0000), &i(0xC000_0000), RoundMode::Rne), i(0xFF80_0000));
    // +inf * +0 = canonical NaN
    assert_eq!(ref_mul(eb, sb, &i(0x7F80_0000), &i(0x0000_0000), RoundMode::Rne), i(0x7FC0_0000));
    // -inf * +0 = canonical NaN
    assert_eq!(ref_mul(eb, sb, &i(0xFF80_0000), &i(0x0000_0000), RoundMode::Rne), i(0x7FC0_0000));
    // NaN * 1.0 = canonical NaN
    assert_eq!(ref_mul(eb, sb, &i(0x7FC0_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x7FC0_0000));
    // +0 * +0 = +0 ; +0 * -0 = -0 (sign XOR) ; -2.0 * +0 = -0
    assert_eq!(ref_mul(eb, sb, &i(0x0000_0000), &i(0x0000_0000), RoundMode::Rne), i(0x0000_0000));
    assert_eq!(ref_mul(eb, sb, &i(0x0000_0000), &i(0x8000_0000), RoundMode::Rne), i(0x8000_0000));
    assert_eq!(ref_mul(eb, sb, &i(0xC000_0000), &i(0x0000_0000), RoundMode::Rne), i(0x8000_0000));
    // overflow: max-normal * 2.0 = +inf. Max normal float32 = 0x7F7FFFFF.
    assert_eq!(ref_mul(eb, sb, &i(0x7F7F_FFFF), &i(0x4000_0000), RoundMode::Rne), i(0x7F80_0000));
}
```

(`i` is the `fn i(v: u64) -> Integer { Integer::from(v) }` helper already defined in the `reference.rs` test module.)

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp ref_mul_known_float32`
Expected: FAIL — `cannot find function ref_mul in this scope`.

- [ ] **Step 3: Write the implementation**

Append to `reference.rs` (after `ref_add`). The XOR sign is computed once and reused for all non-NaN result patterns.

```rust
/// Exact-rational golden `fp.mul RM a b`. `a`, `b` are W=eb+sb bit patterns.
/// Result sign is always sign_a XOR sign_b (including specials and zeros).
pub fn ref_mul(eb: u32, sb: u32, a: &Integer, b: &Integer, mode: RoundMode) -> Integer {
    let ca = decode(eb, sb, a);
    let cb = decode(eb, sb, b);
    use FpClass::*;
    let sign = ref_is_negative(&ca) ^ ref_is_negative(&cb); // XOR sign
    // 1. NaN propagation.
    if matches!(ca, Nan) || matches!(cb, Nan) { return canonical_nan(eb, sb); }
    // 2. 0 * inf = NaN (either order). Must precede the inf arm.
    let a_zero = matches!(ca, Zero { .. });
    let b_zero = matches!(cb, Zero { .. });
    let a_inf = matches!(ca, Inf { .. });
    let b_inf = matches!(cb, Inf { .. });
    if (a_zero && b_inf) || (a_inf && b_zero) { return canonical_nan(eb, sb); }
    // 3. inf * finite-nonzero = signed inf.
    if a_inf || b_inf { return inf_pattern(eb, sb, sign); }
    // 4. zero * finite = signed zero.
    if a_zero || b_zero { return zero_pattern(eb, sb, sign); }
    // 5. finite * finite: exact rational product, then round.
    let ra = class_to_rational(eb, sb, &ca).unwrap();
    let rb = class_to_rational(eb, sb, &cb).unwrap();
    let prod = ra * rb;
    round_rational(eb, sb, &prod, mode)
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp ref_mul_known_float32`
Expected: PASS.

- [ ] **Step 5: Add an exhaustive (3,5) self-consistency test and run**

```rust
#[test]
fn ref_mul_tiny_total_and_commutative() {
    // Every (a,b,mode) on (3,5) produces a valid 8-bit encoding and is
    // commutative (fp.mul is commutative, NaN canonical too).
    let (eb, sb) = (3u32, 5u32);
    let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
    for a in 0u64..256 {
        for b in 0u64..256 {
            for m in modes {
                let r1 = ref_mul(eb, sb, &Integer::from(a), &Integer::from(b), m);
                let r2 = ref_mul(eb, sb, &Integer::from(b), &Integer::from(a), m);
                assert_eq!(r1, r2, "mul not commutative a={a:#x} b={b:#x} m={m:?}");
                assert!(r1 < Integer::from(256u64), "out-of-range result {a:#x}*{b:#x}");
            }
        }
    }
}
```

Run: `cargo test -p shinri-fp ref_mul_tiny_total_and_commutative`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): exact-rational reference fp.mul (ref_mul) for slice 2b"
```

---

### Task 2: Lift the shared `Operand` helper into `blast/operand.rs`

`add.rs` defines `Operand`, `to_operand`, and the three result-pattern builders (`canon_nan_bits`, `inf_pattern_bits`, `signed_zero_bits`). `fp.mul` needs all five. Move them to a shared module so there is one copy. Pure refactor — the existing `fp.add` tests must stay green with no behavior change.

**Files:**
- Create: `crates/shinri-fp/src/blast/operand.rs`
- Modify: `crates/shinri-fp/src/blast/add.rs` (delete the moved items, import from `operand`)
- Modify: `crates/shinri-fp/src/blast/mod.rs` (add `pub mod operand;`)

**Interfaces:**
- Consumes: `crate::unpack::unpack`, `crate::round::exp_w`, `shinri_bv::{BitLit, Blaster}` and `shinri_bv::blast::arith::bvsub`.
- Produces (in `crate::blast::operand`):
  - `pub(crate) struct Operand { pub sign: BitLit, pub exp: Vec<BitLit>, pub sig: Vec<BitLit>, pub is_nan: BitLit, pub is_inf: BitLit, pub is_zero: BitLit }` — `exp` signed unbiased width `exp_w(eb)`, `sig` `sb` bits LSB→MSB with hidden bit at index `sb-1`.
  - `pub(crate) fn to_operand(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Operand`
  - `pub(crate) fn canon_nan_bits(b: &Blaster, eb: u32, sb: u32) -> Vec<BitLit>`
  - `pub(crate) fn inf_pattern_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit>`
  - `pub(crate) fn signed_zero_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit>`

- [ ] **Step 1: Create `blast/operand.rs` with the moved code**

Create `crates/shinri-fp/src/blast/operand.rs`. Copy the bodies verbatim from the current `add.rs` (the `Operand` struct at `add.rs:11-18`, `to_operand` at `add.rs:20-48`, and the three pattern builders at `add.rs:213-232`), changing the struct fields to `pub` and the four items to `pub(crate)`:

```rust
//! Shared unpacked-operand form and IEEE result-pattern builders for the FP
//! arithmetic datapaths (fp.add, fp.mul, …).

use shinri_bv::{BitLit, Blaster};
use crate::round::exp_w;
use crate::unpack::unpack;

/// Effective unbiased exponent (signed, exp_w bits) and explicit significand
/// (sb bits, hidden bit materialized) for an unpacked operand.
pub(crate) struct Operand {
    pub sign: BitLit,
    pub exp: Vec<BitLit>,   // signed unbiased, exp_w
    pub sig: Vec<BitLit>,   // sb bits LSB→MSB, hidden bit at index sb-1
    pub is_nan: BitLit,
    pub is_inf: BitLit,
    pub is_zero: BitLit,
}

pub(crate) fn to_operand(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Operand {
    let u = unpack(b, bits, eb, sb);
    let ew = exp_w(eb);
    let bias = (1i128 << (eb - 1)) - 1;
    let mut field: Vec<BitLit> = u.exp.clone();
    while field.len() < ew { field.push(b.zero()); }
    let bias_v: Vec<BitLit> = {
        let v = bias & ((1i128 << ew) - 1);
        (0..ew).map(|i| if (v >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    };
    let unbiased = shinri_bv::blast::arith::bvsub(b, &field, &bias_v); // exp - bias
    let mut field_zero = b.one();
    for &e in &u.exp { let ne = b.not1(e); field_zero = b.and2(field_zero, ne); }
    let emin_v: Vec<BitLit> = {
        let v = (1 - bias) & ((1i128 << ew) - 1);
        (0..ew).map(|i| if (v >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    };
    let exp: Vec<BitLit> = (0..ew).map(|i| b.mux2(field_zero, emin_v[i], unbiased[i])).collect();
    let hidden = b.not1(field_zero);
    let mut sig: Vec<BitLit> = u.sig.clone();      // sb-1 bits
    sig.push(hidden);                               // index sb-1 = hidden
    Operand { sign: u.sign, exp, sig, is_nan: u.is_nan, is_inf: u.is_inf, is_zero: u.is_zero }
}

#[allow(clippy::needless_range_loop)] // index arithmetic bounds are load-bearing
pub(crate) fn canon_nan_bits(b: &Blaster, eb: u32, sb: u32) -> Vec<BitLit> {
    // exp all ones; sig MSB (index sb-2) set; sign 0.
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    for i in (sb as usize - 1)..(sb as usize - 1 + eb as usize) { v[i] = b.one(); } // exp
    v[sb as usize - 2] = b.one(); // sig MSB
    v
}
#[allow(clippy::needless_range_loop)] // index arithmetic bounds are load-bearing
pub(crate) fn inf_pattern_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit> {
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    for i in (sb as usize - 1)..(sb as usize - 1 + eb as usize) { v[i] = b.one(); } // exp all ones
    v[(eb + sb) as usize - 1] = sign;
    v
}
pub(crate) fn signed_zero_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit> {
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    v[(eb + sb) as usize - 1] = sign;
    v
}
```

- [ ] **Step 2: Register the module**

In `crates/shinri-fp/src/blast/mod.rs`, add `pub mod operand;` (alphabetical placement is fine):

```rust
pub mod add;
pub mod classify;
pub mod compare;
pub mod operand;
pub mod structural;
```

- [ ] **Step 3: Delete the moved items from `add.rs` and import from `operand`**

In `crates/shinri-fp/src/blast/add.rs`:
1. Delete the `Operand` struct (lines `11-18`), `to_operand` (lines `20-48`), `canon_nan_bits`, `inf_pattern_bits`, `signed_zero_bits` (lines `213-232`).
2. At the top of `add.rs`, add the import:

```rust
use crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};
```

The remaining `add.rs`-local helpers (`fp_add`, `bits_equal`, `unsigned_ge`, `signed_gt`, `const_ew`, `zero_extend`, `select_operands`, `special_case`) stay. `select_operands` constructs `Operand { … }` — with the fields now `pub`, that still compiles from within the crate.

- [ ] **Step 4: Run the full crate tests to verify no behavior change**

Run: `cargo test -p shinri-fp`
Expected: PASS — every slice-1 and slice-2a test (`fp_add_tiny_exhaustive_all_modes`, `fp_add_float32_specials_and_random`, the rounder/lzc/rm tests) green. This is a pure refactor; no test changes.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/blast/operand.rs crates/shinri-fp/src/blast/add.rs crates/shinri-fp/src/blast/mod.rs
git commit -m "refactor(fp): lift shared Operand/to_operand + pattern builders into blast/operand.rs"
```

---

### Task 3: The `fp.mul` datapath (`blast/mul.rs`)

Unpack → XOR sign → sum exponents → full-width significand multiply → uniform LZC normalize → build `ExtFp` → `round()` → IEEE special-case mux. Validated bit-identical to `ref_mul`, exhaustive on `(3,5)` across all five modes.

**Files:**
- Create: `crates/shinri-fp/src/blast/mul.rs`
- Modify: `crates/shinri-fp/src/blast/mod.rs` (add `pub mod mul;`)

**Interfaces:**
- Consumes: `crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits}`, `crate::round::{ExtFp, exp_w, round}`, `crate::rm::RmSel`, `crate::lzc::lzc`, `shinri_bv::blast::arith::{bvmul, bvadd, bvsub}`, `shinri_bv::blast::shift::bvshl`, `Blaster` primitives.
- Produces: `pub fn fp_mul(b: &mut Blaster, x: &[BitLit], y: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit>` — the `W=eb+sb` result word.

**The datapath contract (read before implementing).** Both operands come from `to_operand`: `exp` is the signed unbiased exponent (width `exp_w(eb)`), `sig` is the `sb`-bit explicit significand (hidden bit at index `sb-1`; value `sig · 2^(exp-(sb-1))`). The product of two such values is `(sig_x · sig_y) · 2^((exp_x+exp_y) - 2(sb-1))`. We:
1. **Sign** = `sign_x XOR sign_y`.
2. **Exp** = `exp_x + exp_y` in `exp_w(eb)` signed bits.
3. **Product** = zero-extend `sig_x`, `sig_y` to `2·sb` bits, `bvmul` → `prod` (`2·sb` bits, the exact integer `sig_x·sig_y ∈ [0, 2^(2sb))`). The product's binary point sits so that an MSB-aligned `prod` (leading 1 at index `2sb-1`) represents a value in `[1,2)` after normalization.
4. **Normalize** (uniform LZC): `lz = lzc(prod)` over `2·sb` width; `prod_n = prod << lz` places the leading 1 at index `2sb-1`. The ExtFp significand is the top `sb` bits of `prod_n`; `G`, `R` are the next two bits; `S` = OR of the remaining low `2sb-sb-2` bits. The normalized exponent is `norm_exp = (exp_x + exp_y) - lz + CORR`, where `CORR` accounts for the fixed reinterpretation of the `2·sb`-wide integer product as a `[1,2)`-scaled significand (derived below).
5. Build `ExtFp { sign, exp: norm_exp, sig, grs:(G,R,S) }`, call `round()` (slice-2a, unchanged).
6. Special-case mux overrides `round()`'s output, priority NaN > Inf > Zero > normal.

**Deriving `CORR`.** Let `P = sig_x · sig_y` (the `2·sb`-bit integer in `prod`). Each `sig` is an integer in `[0, 2^sb)` representing `sig · 2^(exp-(sb-1))`. So the true product value is `P · 2^((exp_x+exp_y) - 2(sb-1))`. After `prod_n = P << lz`, the top bit (index `2sb-1`) has integer weight `2^(2sb-1)`. The rounder's `ExtFp` expects `sig` (top `sb` bits, hidden bit at index `sb-1`) to mean `sig_val · 2^(norm_exp-(sb-1))` with `sig_val ∈ [2^(sb-1), 2^sb)`. Equate: taking the top `sb` bits of `prod_n` divides `prod_n` by `2^(2sb-sb)=2^sb`, i.e. `sig_val = floor(prod_n / 2^sb)` and `P = prod_n >> lz`. Working the powers of two through (full algebra in the design doc §4), the exponent that makes `sig_val · 2^(norm_exp-(sb-1))` equal the true product is:

```
norm_exp = (exp_x + exp_y) + (sb - 1) - lz
```

so `CORR = sb - 1`. **Treat this as provisional**: the exhaustive `(3,5)` test in Step 4 is the gate. If it fails with a consistent power-of-two (exponent) offset, adjust `CORR` by that offset and document; if it fails on significand/GRS bits, the bug is in the bit-slice indices, not `CORR`.

**Exponent headroom.** `exp_w(eb) = eb + 6`. `fp.mul` sums two exponents (each as low as `emin = 1-bias`) and subtracts `lz` (≤ `2sb`). The exhaustive `(3,5)` test is the gate that `eb+6` holds for products; if it overflows, widen `exp_w` in `round.rs` (a one-line change, re-run the slice-2a rounder tests) and document the new bound.

- [ ] **Step 1: Write the failing test (exhaustive (3,5))**

Create `crates/shinri-fp/src/blast/mul.rs` with the test module (mirrors `add.rs`'s test harness):

```rust
//! fp.mul datapath: unpack → sign/exp → multiply → normalize → round → special-case.

use shinri_bv::{BitLit, Blaster};
use crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};
use crate::round::{exp_w, round, ExtFp};
use crate::rm::RmSel;
use crate::lzc::lzc;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{ref_mul, RoundMode};
    use crate::rm;
    use shinri_num::Integer;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn const_bits(b: &Blaster, eb: u32, sb: u32, value: u64) -> Vec<BitLit> {
        (0..(eb + sb)).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    }
    fn eval_word(b: Blaster, word: &[BitLit]) -> u64 {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars { s.new_var(); }
        for c in &cnf.clauses {
            let ls: Vec<Lit> = c.iter().map(|bl| Lit::new(Var::new(bl.var), bl.pos)).collect();
            s.add_clause(&ls);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let mut v = 0u64;
        for (i, bl) in word.iter().enumerate() {
            let raw = s.value_of(Var::new(bl.var)).unwrap();
            if if bl.pos { raw } else { !raw } { v |= 1 << i; }
        }
        v
    }
    fn rmode(m: RoundMode) -> shinri_core::RoundingMode {
        match m {
            RoundMode::Rne => shinri_core::RoundingMode::Rne,
            RoundMode::Rna => shinri_core::RoundingMode::Rna,
            RoundMode::Rtp => shinri_core::RoundingMode::Rtp,
            RoundMode::Rtn => shinri_core::RoundingMode::Rtn,
            RoundMode::Rtz => shinri_core::RoundingMode::Rtz,
        }
    }

    #[test]
    fn fp_mul_tiny_exhaustive_all_modes() {
        let (eb, sb) = (3u32, 5u32);
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        for a in 0u64..256 {
            for bb in 0u64..256 {
                for m in modes {
                    let want = ref_mul(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                    let mut bl = Blaster::new();
                    let xv = const_bits(&bl, eb, sb, a);
                    let yv = const_bits(&bl, eb, sb, bb);
                    let sel = rm::literal(&bl, rmode(m));
                    let word = fp_mul(&mut bl, &xv, &yv, &sel, eb, sb);
                    assert_eq!(Integer::from(eval_word(bl, &word)), want,
                        "fp.mul a={a:#x} b={bb:#x} m={m:?}");
                }
            }
        }
    }

    #[test]
    fn fp_mul_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        let specials = [0x0000_0000u64, 0x8000_0000, 0x7F80_0000, 0xFF80_0000, 0x7FC0_0000,
                        0x3F80_0000, 0xBF80_0000, 0x4000_0000, 0x0000_0001, 0x8000_0001,
                        0x7F7F_FFFF, 0x0080_0000];
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        let mut state: u64 = 0x6D17_5EED;
        let mut next = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state >> 16 };
        let mut cases: Vec<(u64, u64)> = Vec::new();
        for &s1 in &specials { for &s2 in &specials { cases.push((s1, s2)); } }
        for _ in 0..200 { cases.push((next() & 0xFFFF_FFFF, next() & 0xFFFF_FFFF)); }
        for (a, bb) in cases {
            for m in modes {
                let want = ref_mul(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                let mut bl = Blaster::new();
                let xv = const_bits(&bl, eb, sb, a);
                let yv = const_bits(&bl, eb, sb, bb);
                let sel = rm::literal(&bl, rmode(m));
                let word = fp_mul(&mut bl, &xv, &yv, &sel, eb, sb);
                assert_eq!(Integer::from(eval_word(bl, &word)), want,
                    "fp.mul32 a={a:#x} b={bb:#x} m={m:?}");
            }
        }
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp fp_mul_tiny_exhaustive_all_modes`
Expected: FAIL — `cannot find function fp_mul`.

- [ ] **Step 3: Write the datapath**

Add above the test module. The product datapath width is `2·sb`; normalize is a single uniform LZC + left-shift; the special-case mux mirrors `add.rs::special_case` but with the mul tables.

```rust
fn const_ew(b: &Blaster, ew: usize, v: i128) -> Vec<BitLit> {
    let u = v & ((1i128 << ew) - 1);
    (0..ew).map(|i| if (u >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
}
fn zero_extend(b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit> {
    let mut out = x.to_vec(); while out.len() < to { out.push(b.zero()); } out
}

pub fn fp_mul(b: &mut Blaster, x: &[BitLit], y: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let pw = 2 * sbu;                 // product width
    let ox = to_operand(b, x, eb, sb);
    let oy = to_operand(b, y, eb, sb);

    // --- Sign: XOR. ---
    let res_sign = b.xor2(ox.sign, oy.sign);

    // --- Exponent: sum of the two unbiased exponents (signed, ew bits). ---
    let exp_sum = shinri_bv::blast::arith::bvadd(b, &ox.exp, &oy.exp);

    // --- Significand product: zero-extend to 2*sb, bvmul → full 2*sb product. ---
    let xe = zero_extend(b, &ox.sig, pw);
    let ye = zero_extend(b, &oy.sig, pw);
    let prod = shinri_bv::blast::arith::bvmul(b, &xe, &ye);     // pw bits

    // --- Normalize (uniform LZC): left-shift leading 1 to index pw-1. ---
    let lz = lzc(b, &prod);                                     // count_width(pw) bits
    let lz_ew = zero_extend(b, &lz, ew);
    let prod_n = shinri_bv::blast::shift::bvshl(b, &prod, &lz_ew);
    // norm_exp = exp_sum + (sb-1) - lz.
    let corr = const_ew(b, ew, (sb as i128) - 1);
    let exp_corr = shinri_bv::blast::arith::bvadd(b, &exp_sum, &corr);
    let norm_exp = shinri_bv::blast::arith::bvsub(b, &exp_corr, &lz_ew);

    // --- Build ExtFp from prod_n. Top sb bits = sig (hidden at index pw-1);
    //     next bit = G, next = R, OR of the rest = S. ---
    // prod_n indices: [pw-1] hidden ... [pw-sb] sig LSB ... down to [0].
    // sig (LSB→MSB) = prod_n[pw-sb .. pw].
    let sig: Vec<BitLit> = prod_n[(pw - sbu)..pw].to_vec();
    // G = prod_n[pw-sb-1], R = prod_n[pw-sb-2] (guard against tiny widths: pw-sb = sb >= 2).
    let g = prod_n[pw - sbu - 1];
    let r = if pw - sbu >= 2 { prod_n[pw - sbu - 2] } else { b.zero() };
    // S = OR of all remaining low bits below R, i.e. prod_n[0 .. pw-sb-2].
    let mut s = b.zero();
    let s_hi = if pw - sbu >= 2 { pw - sbu - 2 } else { 0 };
    for i in 0..s_hi { s = b.or2(s, prod_n[i]); }

    let ext = ExtFp { sign: res_sign, exp: norm_exp, sig, grs: (g, r, s) };
    let rounded = round(b, ext, eb, sb, rm);

    // --- Special-case mux (overrides rounded). ---
    special_case(b, &rounded, &ox, &oy, res_sign, eb, sb)
}

/// IEEE fp.mul special cases override the datapath result.
/// Priority NaN > Inf > Zero > normal. `res_sign` = sign_x XOR sign_y.
fn special_case(b: &mut Blaster, normal: &[BitLit], ox: &Operand, oy: &Operand,
                res_sign: BitLit, eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);
    // NaN if either input NaN, or (0 * inf) in either order.
    let either_nan = b.or2(ox.is_nan, oy.is_nan);
    let zero_times_inf = {
        let a = b.and2(ox.is_zero, oy.is_inf);
        let c = b.and2(ox.is_inf, oy.is_zero);
        b.or2(a, c)
    };
    let want_nan = b.or2(either_nan, zero_times_inf);
    // Inf result if either input inf (and not the NaN case): sign = res_sign.
    let any_inf = b.or2(ox.is_inf, oy.is_inf);
    let inf_bits = inf_pattern_bits(b, eb, sb, res_sign);
    // Zero result if either input zero (finite * 0): sign = res_sign.
    let any_zero = b.or2(ox.is_zero, oy.is_zero);
    let zero_bits = signed_zero_bits(b, eb, sb, res_sign);

    let mut out = normal.to_vec();
    for i in 0..w { out[i] = b.mux2(any_zero, zero_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(any_inf, inf_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_nan, nan[i], out[i]); }
    out
}
```

> Reuse points: `shinri_bv::blast::arith::{bvmul, bvadd, bvsub}` and `shinri_bv::blast::shift::bvshl` are all `pub` (slice 2a's `add.rs`/`round.rs` already import from these exact paths). `lzc`, `round`, `ExtFp`, `exp_w`, and the `operand` items come from earlier tasks. No re-exports needed.

- [ ] **Step 4: Run the exhaustive tiny test (the gate)**

Run: `cargo test -p shinri-fp fp_mul_tiny_exhaustive_all_modes`
Expected: PASS — 256×256×5 = 327,680 solver runs; may take a minute. The panic message identifies any failing `(a, b, mode)`. If failures share a constant exponent offset, adjust `CORR` per Task 3's derivation note; if the exponent overflows `exp_w`, widen `exp_w(eb)` in `round.rs` and re-run the slice-2a rounder tests. Do not weaken the test.

- [ ] **Step 5: Run the Float32 specials/random test**

Run: `cargo test -p shinri-fp fp_mul_float32_specials_and_random`
Expected: PASS.

- [ ] **Step 6: Register the module and commit**

In `crates/shinri-fp/src/blast/mod.rs`, add `pub mod mul;`. Then:

```bash
git add crates/shinri-fp/src/blast/mul.rs crates/shinri-fp/src/blast/mod.rs
git commit -m "feat(fp): fp.mul datapath (multiply/normalize/round/special) bit-identical to ref_mul"
```

---

### Task 4: Wire `FpMul` into `FpBlaster::blast_word` (`lib.rs`)

Add the `FpMul` operator arm next to `FpAdd`/`FpSub`. RM blasting and operand blasting reuse the existing machinery.

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs`

**Interfaces:**
- Consumes: `crate::blast::mul::fp_mul`, the existing `FpBlaster::blast_rm` and `blast_word`, `shinri_core::BuiltinOp::FpMul`.
- Produces: `blast_word` handles `FpMul`.

- [ ] **Step 1: Write the failing test**

Add to the `lower_tests` module in `lib.rs` (mirrors the existing `lower_fp_add_eq_atom`):

```rust
#[test]
fn lower_fp_mul_eq_atom() {
    use shinri_core::BuiltinOp;
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let yf = ctx.declare_fun("y", &[], f32);
    let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let mul = ctx.mk_app(Op::Builtin(BuiltinOp::FpMul), &[rne, x, y]).unwrap();
    let one = ctx.mk_fp_const(8, 24, Integer::from(0x3F80_0000u64));
    let eq = ctx.mk_eq(mul, one).unwrap();
    let lo = lower(&mut ctx, &[eq]);
    assert!(lo.atom_lit.contains_key(&eq), "core = over fp.mul must be surrogated");
    assert!(lo.var_bits.contains_key(&x) && lo.var_bits.contains_key(&y), "x,y exported");
}
```

> If `lower`'s returned struct field names differ in this file (e.g. `atom_lit`/`var_bits`), match the names used by the existing `lower_fp_add_eq_atom` test verbatim — read it first.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp lower_fp_mul_eq_atom`
Expected: FAIL — `blast_word` hits the `other => unreachable!` arm on `FpMul`.

- [ ] **Step 3: Add the `FpMul` arm to `blast_word`**

In the `Op::Builtin(op)` match inside `blast_word`, immediately after the `FpSub` arm and before `other =>`:

```rust
                    FpMul => {
                        let rm = self.blast_rm(ctx, kids[0]);
                        let xw = self.blast_word(ctx, kids[1]);
                        let yw = self.blast_word(ctx, kids[2]);
                        crate::blast::mul::fp_mul(&mut self.b, &xw, &yw, &rm, eb, sb)
                    }
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `cargo test -p shinri-fp lower_fp_mul_eq_atom`
Expected: PASS.

- [ ] **Step 5: Run the full crate test sweep**

Run: `cargo test -p shinri-fp`
Expected: PASS (all slice-1 + slice-2a + slice-2b unit tests).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): wire FpMul into blast_word"
```

---

### Task 5: Admit `fp.mul` through the soundness fence (`fp_stage.rs`)

`is_supported_fp_word`'s arithmetic arm currently matches `FpAdd | FpSub`. Extend it to `FpAdd | FpSub | FpMul` (identical `(RM, F, F)` shape check). `fp_atom_is_supported` recurses through `is_supported_fp_word` for operands, so it needs **no** change. Flip the existing `fp_mul_word_is_not_supported` test (now wrong) into a positive test, and add a `fp.div`-fenced negative test to preserve "future ops default to fenced" coverage.

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs`

**Interfaces:**
- Extends: `is_supported_fp_word(ctx, t) -> bool` (private). Signatures unchanged; one new accepted word shape (`FpMul`).

- [ ] **Step 1: Update the tests (rename the stale negative test, add a fenced sibling)**

In the `tests` module of `fp_stage.rs`, replace `fp_mul_word_is_not_supported` (lines `276-286`) with these two tests:

```rust
    #[test]
    fn fp_mul_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let mul = ctx.mk_app(Op::Builtin(BuiltinOp::FpMul), &[rne, x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[mul]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.mul is in scope as of slice 2b");
    }

    #[test]
    fn fp_div_word_is_not_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let div = ctx.mk_app(Op::Builtin(BuiltinOp::FpDiv), &[rne, x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[div]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(!fp_atoms_fully_supported(&ctx, &atoms), "fp.div stays fenced until slice 2c");
    }
```

- [ ] **Step 2: Run tests to verify the new state**

Run: `cargo test -p shinri-solver --lib fp_stage`
Expected: `fp_mul_word_is_supported` FAILS (fp.mul not yet admitted); `fp_div_word_is_not_supported` PASSES already.

- [ ] **Step 3: Extend `is_supported_fp_word`**

In `fp_stage.rs`, change the arithmetic arm (line `134`) to include `FpMul`:

```rust
        // FpAdd / FpSub / FpMul: (RM, F, F). RM operand must be a RoundingMode
        // term (literal const or nullary RM variable); both FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpAdd | BuiltinOp::FpSub | BuiltinOp::FpMul), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 3
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
                && is_supported_fp_word(ctx, kids[2])
        }
```

Update the doc comment on `is_supported_fp_word` (lines `109-118`) to mention `FpMul` is in scope as of slice 2b, and the `// Anything else (FpMul, FpDiv, …)` comment at line `141` to drop `FpMul` (now `// Anything else (FpDiv, FpFma, …)`).

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-solver --lib fp_stage`
Expected: PASS — `fp_mul_word_is_supported`, `fp_div_word_is_not_supported`, plus the existing `fp_add_word_is_supported`, `fp_add_with_symbolic_rm_is_supported`, `fp_mixed_with_bv_is_fenced`.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): admit fp.mul words through the FP soundness fence"
```

---

### Task 6: End-to-end witness + symbolic-RM SAT tests (`fp_e2e.rs`)

Prove the whole seam: parse a script with `fp.mul` → SAT/UNSAT → `get-model` round-trip, plus a symbolic-RM query. Uses the `(_ +oo 8 24)` / `(_ +zero 8 24)` special forms (NOT `(fp #b…)` literals, which route through `FpFromBits` and trip the fence — see the ENCODING NOTE at the top of `fp_e2e.rs`).

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs`

**Interfaces:**
- Consumes: the existing `fn run(src: &str) -> (SolveOutcome, String)` helper (returns the outcome and the rendered model/response string) and `SolveOutcome`.

- [ ] **Step 1: Write the failing tests**

Append to `fp_e2e.rs` (mirroring the slice-2a `fp_add_*` tests' style). Because finite `(fp #b…)` literals trip the fence, the multiplicands are specials whose product is exact in every mode.

```rust
// ── Slice-2b end-to-end: fp.mul SAT/UNSAT + symbolic-RM + get-model ───────────

#[test]
fn fp_mul_inf_times_two_is_inf_sat() {
    // SAT: fp.mul(RNE, +inf, +inf) = +inf (inf * inf = inf, exact).
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.mul RNE (_ +oo 8 24) (_ +oo 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_mul_inf_times_zero_is_nan_sat() {
    // SAT: fp.mul(RNE, +inf, +zero) = NaN; x asserted isNaN.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (_ +zero 8 24)))
(assert (fp.isNaN (fp.mul RNE (_ +oo 8 24) x)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat); // +inf * +0 = NaN
}

#[test]
fn fp_mul_inf_times_zero_not_inf_unsat() {
    // UNSAT: (+inf * +0) is NaN, never +inf, so isInfinite of it cannot hold.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (_ +zero 8 24)))
(assert (fp.isInfinite (fp.mul RNE (_ +oo 8 24) x)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_mul_symbolic_rm_sat() {
    // SAT: ∃ rounding mode rm. fp.eq x (fp.mul rm +inf +inf).
    // inf * inf = +inf regardless of rounding.
    let src = "\
(set-logic QF_FP)
(declare-fun rm () RoundingMode)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.mul rm (_ +oo 8 24) (_ +oo 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_mul_sat_get_model_round_trip() {
    // After SAT, the model must render x = +inf. (+inf * +inf = +inf, exact.)
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.mul RNE (_ +oo 8 24) (_ +oo 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
    assert!(
        model.contains("(fp #b0 #b11111111 #b00000000000000000000000)"),
        "model must render x as +inf: {model}"
    );
}
```

- [ ] **Step 2: Run tests to verify they pass**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS for all five new tests (plus the pre-existing slice-1/2a e2e tests). If any returns `Unknown`, the fence (Task 5) or wiring (Task 4) is incomplete — fix there, not by weakening the test.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): end-to-end fp.mul SAT/UNSAT + symbolic-RM + get-model"
```

---

### Task 7: Differential-vs-z3 oracle over `fp.mul` (`fp_oracle.rs`)

Add a `fp.mul` generator + differential test, mirroring the existing `gen_arith_script` / `differential_qf_fp_add_sub` (which already cover add/sub). Reuses `z3_outcome_arith`, `RMS`, `Lcg`, `N_ITERS`, `shinri_outcome`.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs`

**Interfaces:**
- Consumes: `Lcg`, `RMS`, `N_ITERS`, `shinri_outcome`, `z3_outcome_arith` (all already in the file).
- Produces: `fn gen_mul_script(rng: &mut Lcg) -> String` and `#[test] fn differential_qf_fp_mul()`.

- [ ] **Step 1: Add the mul generator**

Append to `fp_oracle.rs` (inside the `#![cfg(feature = "oracle")]` module), modeled on `gen_arith_script` but emitting `fp.mul`:

```rust
/// Generate a random QF_FP script with fp.mul over all five rounding modes.
/// Declares three fp32 variables (x, y, z) and optionally a symbolic rounding
/// mode; builds 1–3 assertions mixing fp.mul with fp.eq/=/fp.isNaN atoms, some
/// negated, so both SAT and UNSAT witnesses arise across iterations.
fn gen_mul_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let use_sym_rm = rng.below(4) == 0;
    if use_sym_rm {
        s.push_str("(declare-fun rm () RoundingMode)\n");
    }
    let rm = |rng: &mut Lcg| -> String {
        if use_sym_rm && rng.below(2) == 0 {
            "rm".to_string()
        } else {
            RMS[rng.below(RMS.len() as u64) as usize].to_string()
        }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = format!("(fp.mul {} x y)", rm(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq z {term})"),
            1 => format!("(= z {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 {
            s.push_str(&format!("(assert (not {atom}))\n"));
        } else {
            s.push_str(&format!("(assert {atom})\n"));
        }
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_fp_mul() {
    let mut rng = Lcg(0x00B0_0B5_FACE);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_mul_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_FP mul DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
        }
    }
    println!("differential_qf_fp_mul: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}
```

> `0x00B0_0B5_FACE` is a fresh, valid-hex seed distinct from the add/sub test's `0x00AD_D5AB_0001`. `z3_outcome_arith` already forwards every `(declare-fun …)`/`(assert …)` line verbatim (it is generator-agnostic), so no z3-driver change is needed.

- [ ] **Step 2: Run the oracle (requires z3 on PATH)**

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_mul -- --nocapture`
Expected: PASS, printing nonzero `sat` and `unsat` counts and zero disagreements. If z3 is unavailable in this environment, the test is skipped by the feature gate — note that in the task report and run it wherever z3 is present.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential-vs-z3 oracle for fp.mul over all five modes"
```

---

### Task 8: Full workspace non-regression sweep + clippy

**Files:** none (verification only).

- [ ] **Step 1: Run the whole workspace test suite**

Run: `cargo test --workspace`
Expected: PASS — all crates green, QF_BV and QF_FP slice-1/2a paths untouched.

- [ ] **Step 2: Run clippy (the repo's lint gate)**

Run: `cargo clippy --workspace --all-targets`
Expected: no new warnings in `shinri-fp` / `shinri-solver`. Fix any introduced by the new code (unused imports, needless clones/ranges) and re-run. The `#[allow(clippy::needless_range_loop)]` annotations on the moved pattern builders (Task 2) carry over the slice-2a suppressions.

- [ ] **Step 3: Final commit (if clippy fixes were needed)**

```bash
git add -A
git commit -m "chore(fp): clippy cleanups for slice-2b mul"
```

---

## Self-Review

**1. Spec coverage** (against `2026-06-25-shinri-qffp-slice2b-mul-design.md`):
- §2 file changes: `blast/mul.rs` → Task 3; `blast/mod.rs` → Tasks 2,3; `reference.rs` `ref_mul` → Task 1; `lib.rs` `FpMul` arm → Task 4; `fp_stage.rs` fence → Task 5. ✓
- §3 shared `Operand`/`to_operand` lifted → Task 2. ✓
- §4 datapath (XOR sign, exp sum, full-width multiply via zero-extend+`bvmul`, uniform LZC normalize, ExtFp+`round`, special-case mux) → Task 3. ✓ Exponent-headroom checkpoint → Task 3 Step 4 note. ✓ XOR zero-sign → Task 3 `special_case`. ✓
- §5 `ref_mul` (NaN, 0·∞-before-inf, signed ∞, signed zero, exact-rational product, no cancellation arm) → Task 1. ✓
- §6 wiring (`blast_word` `FpMul`) → Task 4; fence (`is_supported_fp_word` only; `fp_atom_is_supported` recurses, no change) → Task 5. ✓
- §7 model path unchanged + get-value on mul term → Task 6 (`fp_mul_sat_get_model_round_trip`). ✓
- §8 test plan: datapath vs `ref_mul` exhaustive (3,5) + Float32 (Tasks 1,3), exp-width gate (Task 3), symbolic-RM (Tasks 5,6), differential z3 (Task 7), e2e witness + non-regression (Tasks 6,8). ✓ Specials seeded: NaN·x, 0·∞ both orders, ∞·finite, ±0·±finite, ±0·±0, subnormal pairs (Float32 specials include `0x0000_0001`, `0x0080_0000`), overflow boundary (`0x7F7F_FFFF`). ✓
- §9 decisions: uniform LZC (Task 3), shared operand (Task 2), XOR sign (Tasks 1,3), rounder reused unchanged (Task 3 imports `round`), exp_w provisional/test-gated (Task 3), soundness (Task 5). ✓

**2. Placeholder scan:** No "TBD"/"implement later". Every code step shows complete code; every test step shows assertions. The `CORR`/`exp_w` notes are explicit, gated adjustments with concrete fallbacks, not deferred work.

**3. Type consistency:** `ref_mul(eb, sb, &a, &b, mode) -> Integer` defined Task 1, used Tasks 1,3. `Operand` (pub fields) + `to_operand`/`canon_nan_bits`/`inf_pattern_bits`/`signed_zero_bits` defined in `blast/operand.rs` Task 2, consumed Tasks 2(add),3(mul). `fp_mul(b, x, y, rm, eb, sb) -> Vec<BitLit>` defined Task 3, called identically Task 4. `special_case(b, normal, ox, oy, res_sign, eb, sb)` is mul-local to Task 3 (note: its signature differs from `add.rs::special_case`, which takes `cancel_zero, rm` — these are two separate functions in two modules, no collision). `RmSel`, `ExtFp`, `exp_w`, `round`, `lzc` reused unchanged from slice 2a. `run(src) -> (SolveOutcome, String)` (Task 6) and `z3_outcome_arith`/`RMS`/`Lcg`/`N_ITERS`/`shinri_outcome` (Task 7) match the landed file symbols. ✓
