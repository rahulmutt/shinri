# QF_FP slice 2f — fp.fma Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit `(fp.fma RM x y z)` = `round(x·y + z)` through the QF_FP soundness fence and bit-blast it correctly — with **exactly one rounding** — across all five rounding modes and all formats.

**Architecture:** Mirror every prior FP op slice: an exact `ref_*` golden in `reference.rs`, a gate-level circuit in `blast/fma.rs`, a `blast_word` dispatch arm, a fence admission in `fp_stage.rs`, and the standard test trio (in-circuit reference cross-check, differential-vs-z3 oracle, end-to-end). The datapath is `fp_add`'s skeleton generalized to significand width `2·sb`: form the **exact** `2·sb`-bit product (reusing `mul`'s product+normalize, no rounding), zero-extend `z`'s significand into the same `2·sb` format so both addends share one scale, run the magnitude-order → sticky-align → effective add/sub → carry/LZC-normalize skeleton, then collapse the top `sb` bits + guard/round/sticky into the shared `round()` **once**. A zero product (whose LZC-of-zero exponent is garbage) is clamped to `emin` so it flows through the add's zero handling.

**Tech Stack:** Rust, `shinri-fp` (depends on `shinri-bv` `Blaster`), `shinri-num` (`Integer`/`Rational`), `shinri-sat` for the in-test SAT eval, `z3` + `easy_smt` for the oracle.

## Global Constraints

- **Single rounding is the defining contract.** The exact real `x·y + z` is formed at full width and rounded once. Never round the product before adding `z` (that is double-rounding and wrong); the whole reason `fp.fma` has its own datapath rather than calling `fp_mul`+`fp_add`.
- **Soundness contract:** anything out of scope returns `unknown`, never a wrong SAT/UNSAT verdict. The fence (`is_supported_fp_word`) positively enumerates supported ops; an unhandled FP op must fail closed (the `blast_word` `unreachable!` arm stays an internal invariant, never user-reachable).
- **No new dependencies.** Reuse `shinri-bv` blast primitives (`adder`, `bvadd`, `bvsub`, `bvmul`, `bvshl`, `compare::{sgt, ult}`) and the FP crate's `round.rs`/`operand.rs`/`normalize.rs`/`lzc.rs` helpers.
- **Bit-identical rounding across ops:** the single shared `round()` is the only rounder; `fp.fma` builds an `ExtFp` and calls it once.
- **Formats:** must work for arbitrary `(eb, sb)` — tests cover a tiny format `(3,5)` (sampled, ternary) and Float32 `(8,24)`. `exp_w(eb) = eb + 6`.
- **Significand convention:** `sb` bits LSB→MSB, hidden/leading bit at index `sb-1`; exponent is signed unbiased, `exp_w(eb)` bits. Product significand is `2·sb` bits, hidden at `2·sb-1`, value `= sig · 2^(exp-(2·sb-1))`.
- **Deep-circuit caution:** `fp.fma` is the deepest datapath shipped (`2sb` multiply + `2sb` LZC and barrel shifts + the rounder). Per the known SAT recursion-depth risk on bit-blasted FP ops (observed on `fp.div`/`fp.sqrt`), the differential oracle is **bounded** and **run in the background by the implementer**, not via looped subagents.
- **No persistent/incremental blasting; no SAT/Tseitin/model changes.**

---

### Task 1: Reference golden `ref_fma`

Exact, bit-pattern golden used by every later cross-check. Fuses the `ref_mul` and `ref_add` special-case cascades, then rounds the exact `x·y + z` once.

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (add `ref_fma` after `ref_mul`, ~line 560; add tests to the existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `decode`, `FpClass`, `class_to_rational`, `canonical_nan`, the private `inf_pattern` and `zero_pattern`, `ref_is_negative`, `round_rational`, `RoundMode`, and `shinri_num::{Integer, Rational}` — all already in `reference.rs`.
- Produces: `pub fn ref_fma(eb: u32, sb: u32, x: &Integer, y: &Integer, z: &Integer, mode: RoundMode) -> Integer`

- [ ] **Step 1: Write the failing tests**

Add to `mod tests` in `reference.rs`. (Float32 patterns: `1.0=0x3F80_0000`, `-1.0=0xBF80_0000`, `2.0=0x4000_0000`, `3.0=0x4040_0000`, `7.0=0x40E0_0000`, `+inf=0x7F80_0000`, `-inf=0xFF80_0000`, `NaN=0x7FC0_0000`, `+0=0`, `-0=0x8000_0000`. Single-rounding witness: `a=1+2^-23=0x3F80_0001`, `-(1+2^-22)=0xBF80_0002`, `2^-46=0x2880_0000`.)

```rust
#[test]
fn ref_fma_finite_and_single_rounding() {
    let (eb, sb) = (8u32, 24u32);
    let fma = |x: u64, y: u64, z: u64, m| {
        ref_fma(eb, sb, &Integer::from(x), &Integer::from(y), &Integer::from(z), m)
    };
    // 2*3 + 1 = 7.
    assert_eq!(fma(0x4000_0000, 0x4040_0000, 0x3F80_0000, RoundMode::Rne),
               Integer::from(0x40E0_0000u64));
    // Single-rounding witness: a = 1 + 2^-23, a*a = 1 + 2^-22 + 2^-46.
    // Fused a*a + (-(1+2^-22)) = 2^-46 exactly (= 0x2880_0000).
    // The double-rounded mul-then-add would give +0 (round(a*a) = 1+2^-22, then -itself).
    assert_eq!(fma(0x3F80_0001, 0x3F80_0001, 0xBF80_0002, RoundMode::Rne),
               Integer::from(0x2880_0000u64));
    // Exact-zero sum sign rule: 1*1 + (-1) = 0 -> +0 (RNE) / -0 (RTN).
    assert_eq!(fma(0x3F80_0000, 0x3F80_0000, 0xBF80_0000, RoundMode::Rne),
               Integer::from(0u64));
    assert_eq!(fma(0x3F80_0000, 0x3F80_0000, 0xBF80_0000, RoundMode::Rtn),
               Integer::from(0x8000_0000u64));
}

#[test]
fn ref_fma_specials() {
    let (eb, sb) = (8u32, 24u32);
    let fma = |x: u64, y: u64, z: u64, m| {
        ref_fma(eb, sb, &Integer::from(x), &Integer::from(y), &Integer::from(z), m)
    };
    let nan = canonical_nan(eb, sb);
    // Any NaN operand -> canonical NaN.
    assert_eq!(fma(0x7FC0_0000, 0x3F80_0000, 0x3F80_0000, RoundMode::Rne), nan);
    // 0 * inf -> NaN (invalid product), regardless of z.
    assert_eq!(fma(0x0000_0000, 0x7F80_0000, 0x3F80_0000, RoundMode::Rne), nan);
    // product +inf, z = -inf (opposite sign) -> NaN.
    assert_eq!(fma(0x7F80_0000, 0x3F80_0000, 0xFF80_0000, RoundMode::Rne), nan);
    // product +inf, z finite -> +inf.
    assert_eq!(fma(0x7F80_0000, 0x4000_0000, 0x3F80_0000, RoundMode::Rne),
               Integer::from(0x7F80_0000u64));
    // product finite, z = +inf -> +inf.
    assert_eq!(fma(0x3F80_0000, 0x3F80_0000, 0x7F80_0000, RoundMode::Rne),
               Integer::from(0x7F80_0000u64));
    // product -inf (neg * pos), z finite -> -inf.
    assert_eq!(fma(0xFF80_0000, 0x3F80_0000, 0x3F80_0000, RoundMode::Rne),
               Integer::from(0xFF80_0000u64));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp ref_fma -- --nocapture`
Expected: FAIL — `cannot find function ref_fma in this scope`.

- [ ] **Step 3: Write the implementation**

Add to `reference.rs` after `ref_mul` (before `ref_div`):

```rust
/// Exact-rational golden `fp.fma RM x y z` = round(x·y + z) with a SINGLE
/// rounding. `x`, `y`, `z` are W=eb+sb bit patterns. Product sign = sign_x ⊕
/// sign_y. The exact real x·y + z is formed at infinite precision and rounded
/// once via `round_rational`.
pub fn ref_fma(eb: u32, sb: u32, x: &Integer, y: &Integer, z: &Integer, mode: RoundMode) -> Integer {
    use FpClass::*;
    let cx = decode(eb, sb, x);
    let cy = decode(eb, sb, y);
    let cz = decode(eb, sb, z);
    // 1. NaN propagation (any operand).
    if matches!(cx, Nan) || matches!(cy, Nan) || matches!(cz, Nan) {
        return canonical_nan(eb, sb);
    }
    let prod_sign = ref_is_negative(&cx) ^ ref_is_negative(&cy);
    let x_zero = matches!(cx, Zero { .. });
    let y_zero = matches!(cy, Zero { .. });
    let x_inf = matches!(cx, Inf { .. });
    let y_inf = matches!(cy, Inf { .. });
    // 2. Invalid product 0·∞ (either order) -> NaN. Precedes the inf arm.
    if (x_zero && y_inf) || (x_inf && y_zero) {
        return canonical_nan(eb, sb);
    }
    let prod_inf = x_inf || y_inf;
    let z_inf = matches!(cz, Inf { .. });
    let z_sign = ref_is_negative(&cz);
    // 3. Infinities.
    if prod_inf {
        // product is ±∞; ∞ + (∓∞) is invalid.
        if z_inf && (z_sign != prod_sign) {
            return canonical_nan(eb, sb);
        }
        return inf_pattern(eb, sb, prod_sign);
    }
    if z_inf {
        return inf_pattern(eb, sb, z_sign);
    }
    // 4. Finite: exact x·y + z, rounded once.
    let rx = class_to_rational(eb, sb, &cx).unwrap();
    let ry = class_to_rational(eb, sb, &cy).unwrap();
    let rz = class_to_rational(eb, sb, &cz).unwrap();
    let v = rx * ry + rz;
    let zero = Rational::new(Integer::zero(), Integer::one());
    if v == zero {
        // IEEE exact-zero-sum sign rule (product sign on the left).
        let neg = (prod_sign && z_sign) || matches!(mode, RoundMode::Rtn);
        return zero_pattern(eb, sb, neg);
    }
    round_rational(eb, sb, &v, mode)
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp ref_fma -- --nocapture`
Expected: PASS (both tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): exact ref_fma golden (single-rounding) for slice 2f"
```

---

### Task 2: Extract the shared `significand_product` helper from `fp_mul`

Pure, behavior-preserving extraction so `fp.fma` reuses the *exact* product+normalize without rounding (and without duplicating it). The existing `mul` `(3,5)` exhaustive test is the regression guard — same pattern slice 2e used to extract `rounding_increment`.

**Files:**
- Modify: `crates/shinri-fp/src/blast/mul.rs` (extract the product+normalize block, currently lines 30-46, into a `pub(crate) fn`; call it from `fp_mul`)

**Interfaces:**
- Consumes: `Operand` (operand.rs), `exp_w` (round.rs), `lzc` (lzc.rs), the private `const_ew`/`zero_extend` (same module), `bvadd`/`bvsub`/`bvmul`/`bvshl` (shinri-bv).
- Produces: `pub(crate) fn significand_product(b: &mut Blaster, ox: &Operand, oy: &Operand, eb: u32, sb: u32) -> (Vec<BitLit>, Vec<BitLit>)` returning `(prod_n, norm_exp)` — `prod_n` is the `2·sb`-bit normalized product (leading bit at index `2·sb-1`), `norm_exp` the signed `exp_w(eb)`-bit exponent of that leading bit.

- [ ] **Step 1: Add the helper and rewire `fp_mul`**

Insert this function in `mul.rs` (e.g. just above `fp_mul`):

```rust
/// Exact normalized significand product, shared by `fp.mul` and `fp.fma`.
/// Returns (prod_n, norm_exp): `prod_n` is the 2·sb-bit product left-shifted so
/// its leading 1 sits at index 2·sb-1; `norm_exp` (signed, exp_w bits) is the
/// exponent of that leading bit, so the product value = prod_n · 2^(norm_exp -
/// (2·sb-1)). No rounding. (Garbage norm_exp when the product is 0 — the caller
/// special-cases a zero product.)
pub(crate) fn significand_product(b: &mut Blaster, ox: &Operand, oy: &Operand, eb: u32, sb: u32)
    -> (Vec<BitLit>, Vec<BitLit>) {
    let ew = exp_w(eb);
    let pw = 2 * sb as usize;
    let exp_sum = shinri_bv::blast::arith::bvadd(b, &ox.exp, &oy.exp);
    let xe = zero_extend(b, &ox.sig, pw);
    let ye = zero_extend(b, &oy.sig, pw);
    let prod = shinri_bv::blast::arith::bvmul(b, &xe, &ye);
    let lz = lzc(b, &prod);
    let lz_ew = zero_extend(b, &lz, ew);
    let prod_n = shinri_bv::blast::shift::bvshl(b, &prod, &lz_ew);
    let corr = const_ew(b, ew, 1i128);
    let exp_corr = shinri_bv::blast::arith::bvadd(b, &exp_sum, &corr);
    let norm_exp = shinri_bv::blast::arith::bvsub(b, &exp_corr, &lz_ew);
    (prod_n, norm_exp)
}
```

Then replace the product+normalize block in `fp_mul` (currently `mul.rs:30-46`, from the `// --- Significand product` comment through the `norm_exp = ...` line) with:

```rust
    // --- Significand product + normalize (shared with fp.fma). ---
    let (prod_n, norm_exp) = significand_product(b, &ox, &oy, eb, sb);
```

(The earlier `let pw = 2 * sbu;`, `res_sign`, `exp_sum` removal: `exp_sum` now lives inside the helper, so delete the old `let exp_sum = ...` line in `fp_mul`; keep `pw`/`sbu`/`res_sign` — `pw` is still used by the GRS extraction below, `res_sign` by `special_case`.)

- [ ] **Step 2: Run the existing mul regression tests**

Run: `cargo test -p shinri-fp --lib fp_mul -- --nocapture`
Expected: PASS — `fp_mul_tiny_exhaustive_all_modes` and `fp_mul_float32_specials_and_random` still green (proves the extraction preserved behavior).

- [ ] **Step 3: Confirm the whole crate still builds clean**

Run: `cargo test -p shinri-fp --lib && cargo clippy -p shinri-fp --all-targets`
Expected: PASS, no unused-import / dead-code / clippy warnings.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-fp/src/blast/mul.rs
git commit -m "refactor(fp): extract shared significand_product from fp_mul"
```

---

### Task 3: `fp.fma` circuit

The gate-level datapath, cross-checked against `ref_fma` inside the module (same harness pattern as `blast/mul.rs`).

**Files:**
- Create: `crates/shinri-fp/src/blast/fma.rs`
- Modify: `crates/shinri-fp/src/blast/mod.rs` (add `pub mod fma;`, alphabetical — between `div` and `minmax`)

**Interfaces:**
- Consumes: `to_operand`/`Operand`/`canon_nan_bits`/`inf_pattern_bits`/`signed_zero_bits` (operand.rs); `significand_product` (mul.rs, Task 2); `const_n`/`zero_extend` (normalize.rs); `lzc` (lzc.rs); `exp_w`/`shift_right_sticky`/`round`/`ExtFp` (round.rs); `bvadd`/`bvsub`/`adder`/`bvshl` (shinri-bv arith/shift); `compare::{sgt, ult}` (shinri-bv); `RmSel` (rm.rs).
- Produces: `pub fn fp_fma(b: &mut Blaster, x: &[BitLit], y: &[BitLit], z: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit>`

- [ ] **Step 1: Register the module**

In `crates/shinri-fp/src/blast/mod.rs`, add (alphabetical, between `pub mod div;` and `pub mod minmax;`):

```rust
pub mod fma;
```

- [ ] **Step 2: Write the failing circuit tests**

Create `crates/shinri-fp/src/blast/fma.rs` with ONLY the test module first (so it fails to compile against a missing `fp_fma`), modeled on `blast/mul.rs`'s harness:

```rust
//! fp.fma datapath: exact 2·sb product → z aligned at the same scale → effective
//! add/sub → normalize → SINGLE round → special-case. Generalizes fp_add to
//! significand width 2·sb. No double rounding.

#[cfg(test)]
mod tests {
    use crate::blast::fma::fp_fma;
    use crate::reference::{ref_fma, RoundMode};
    use crate::rm;
    use shinri_bv::{BitLit, Blaster};
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
    const MODES: &[RoundMode] = &[RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];

    fn check(eb: u32, sb: u32, a: u64, b2: u64, c: u64, m: RoundMode) {
        let want = ref_fma(eb, sb, &Integer::from(a), &Integer::from(b2), &Integer::from(c), m);
        let mut bl = Blaster::new();
        let xv = const_bits(&bl, eb, sb, a);
        let yv = const_bits(&bl, eb, sb, b2);
        let zv = const_bits(&bl, eb, sb, c);
        let sel = rm::literal(&bl, rmode(m));
        let word = fp_fma(&mut bl, &xv, &yv, &zv, &sel, eb, sb);
        assert_eq!(Integer::from(eval_word(bl, &word)), want,
            "fp.fma a={a:#x} b={b2:#x} c={c:#x} m={m:?}");
    }

    #[test]
    fn fp_fma_tiny_sampled_all_modes() {
        // Format (3,5): full triple space is 256^3 (too large to enumerate), so
        // cross-product a curated set of "interesting" patterns and add random
        // triples. Each tiny-format SAT solve is pure constant propagation (fast).
        let (eb, sb) = (3u32, 5u32);
        // Layout: sign(bit7) | exp(bits4-6) | trailing-sig(bits0-3). bias=3.
        // ±0, ±inf, NaN, ±1.0, ±2.0, ±0.5, smallest subnormal, max normal.
        let pats: &[u64] = &[
            0x00, 0x80,             // ±0
            0x70, 0xF0,             // ±inf  (exp=0b111, trailing 0)
            0x78,                   // NaN   (exp=0b111, trailing nonzero)
            0x30, 0xB0,             // ±1.0  (exp field = bias = 3)
            0x40, 0xC0,             // ±2.0  (exp field 4)
            0x20, 0xA0,             // ±0.5  (exp field 2)
            0x01, 0x81,             // ± smallest subnormal (exp 0, trailing 1)
            0x6F, 0xEF,             // ± max normal (exp 6, trailing 0xF)
        ];
        for &a in pats {
            for &bb in pats {
                for &c in pats {
                    for &m in MODES { check(eb, sb, a, bb, c, m); }
                }
            }
        }
        // Random triples over the full 8-bit space.
        let mut state = 0xFEED_F00D_1234_5678u64;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); (state >> 24) & 0xFF };
        for _ in 0..600 {
            let (a, bb, c) = (rand(), rand(), rand());
            for &m in MODES { check(eb, sb, a, bb, c, m); }
        }
    }

    #[test]
    fn fp_fma_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        // Curated triples incl. the single-rounding witness and specials.
        let curated: &[(u64, u64, u64)] = &[
            (0x4000_0000, 0x4040_0000, 0x3F80_0000),   // 2*3+1 = 7
            (0x3F80_0001, 0x3F80_0001, 0xBF80_0002),   // single-rounding witness -> 2^-46
            (0x3F80_0000, 0x3F80_0000, 0xBF80_0000),   // 1*1-1 = 0
            (0x7FC0_0000, 0x3F80_0000, 0x3F80_0000),   // NaN propagation
            (0x0000_0000, 0x7F80_0000, 0x3F80_0000),   // 0*inf -> NaN
            (0x7F80_0000, 0x3F80_0000, 0xFF80_0000),   // +inf + (-inf) -> NaN
            (0x7F80_0000, 0x4000_0000, 0x3F80_0000),   // +inf product, finite z -> +inf
            (0x3F80_0000, 0x3F80_0000, 0x7F80_0000),   // finite product, z=+inf -> +inf
            (0x0080_0000, 0x0080_0000, 0x0000_0001),   // subnormal-scale product + tiny z
        ];
        let mut state = 0x0FMA_5EED_u64 ^ 0x1234_5678;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); (state >> 16) & 0xFFFF_FFFF };
        for iter in 0..500u64 {
            let (a, bb, c) = if (iter as usize) < curated.len() {
                curated[iter as usize]
            } else {
                (rand(), rand(), rand())
            };
            for &m in MODES { check(eb, sb, a, bb, c, m); }
        }
    }
}
```

Note for the implementer: the `(3,5)` patterns use the layout `sign(bit7) | exp(bits4-6) | trailing-sig(bits0-3)`, `bias=3` (verified in the comments above). The cross-check is against `ref_fma`, so even a mislabeled-but-valid pattern still tests a real value — but the labels are correct as written. **Fix the seed literal** `0x0FMA_5EED_u64` (not valid hex) to any `u64`, e.g. `0x0F_A5_EE_D0_u64`.

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-fp --lib fp_fma -- --nocapture`
Expected: FAIL — `cannot find function fp_fma` (and the `0x0FMA_5EED` literal error if not yet fixed).

- [ ] **Step 4: Write the circuit implementation**

Prepend to `fma.rs` (above the test module):

```rust
use shinri_bv::{BitLit, Blaster};
use shinri_bv::blast::arith::{adder, bvadd, bvsub};
use shinri_bv::blast::shift::bvshl;
use shinri_bv::blast::compare::{sgt, ult};
use crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};
use crate::blast::mul::significand_product;
use crate::blast::normalize::{const_n, zero_extend};
use crate::lzc::lzc;
use crate::round::{exp_w, shift_right_sticky, round, ExtFp};
use crate::rm::RmSel;

pub fn fp_fma(b: &mut Blaster, x: &[BitLit], y: &[BitLit], z: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let pw = 2 * sbu;            // product / addend significand width
    let mw = pw + 3;             // mantissa width with 3 GRS columns below
    let ox = to_operand(b, x, eb, sb);
    let oy = to_operand(b, y, eb, sb);
    let oz = to_operand(b, z, eb, sb);

    // ---- Exact product (no rounding). prod_n: pw bits, leading at pw-1. ----
    let prod_sign = b.xor2(ox.sign, oy.sign);
    let (prod_n, norm_exp0) = significand_product(b, &ox, &oy, eb, sb);
    // Zero-product clamp: prod is 0 and norm_exp0 is garbage when x or y is 0.
    // Force exp = emin so the product behaves as a true ±0 addend.
    let prod_zero = b.or2(ox.is_zero, oy.is_zero);
    let bias = (1i128 << (eb - 1)) - 1;
    let emin = const_n(b, ew, 1 - bias);
    let prod_exp: Vec<BitLit> = (0..ew).map(|i| b.mux2(prod_zero, emin[i], norm_exp0[i])).collect();

    // ---- z as a pw-significand addend at the same scale (hidden bit at pw-1). ----
    // value = (zsig << sb) · 2^(ez-(pw-1)) = zsig · 2^(ez-(sb-1)). ✓
    let mut z_sig: Vec<BitLit> = vec![b.zero(); sbu]; // low half 0
    z_sig.extend_from_slice(&oz.sig);                 // high half = z significand
    let z_exp = oz.exp.clone();
    let z_sign = oz.sign;

    // ---- Magnitude-order the two pw-significand addends into hi/lo (by exp, then sig). ----
    let exp_gt = sgt(b, &prod_exp, &z_exp);
    let exp_eq = bits_equal(b, &prod_exp, &z_exp);
    let sig_ge = { let lt = ult(b, &prod_n, &z_sig); b.not1(lt) };
    let tie = b.and2(exp_eq, sig_ge);
    let p_ge_z = b.or2(exp_gt, tie);
    let (hi_sign, hi_exp, hi_sig) =
        select3(b, p_ge_z, (prod_sign, &prod_exp, &prod_n), (z_sign, &z_exp, &z_sig), ew, pw);
    let (lo_sign, lo_exp, lo_sig) =
        select3(b, p_ge_z, (z_sign, &z_exp, &z_sig), (prod_sign, &prod_exp, &prod_n), ew, pw);

    // ---- Align lo to hi: right-shift lo by (hi_exp - lo_exp), collecting sticky. ----
    let exp_diff = bvsub(b, &hi_exp, &lo_exp); // >= 0 since hi >= lo
    let zb = b.zero();
    let mut hi_ext: Vec<BitLit> = vec![zb; 3]; hi_ext.extend_from_slice(&hi_sig); // mw
    let mut lo_ext: Vec<BitLit> = vec![zb; 3]; lo_ext.extend_from_slice(&lo_sig); // mw
    let (lo_shifted, lo_sticky) = shift_right_sticky(b, &lo_ext, &exp_diff);
    let mut lo_aln = lo_shifted;
    lo_aln[0] = b.or2(lo_aln[0], lo_sticky);

    // ---- Operate: effective add if signs equal, else subtract (hi >= lo). ----
    let same_sign = { let xs = b.xor2(hi_sign, lo_sign); b.not1(xs) };
    let sum_add = bvadd(b, &hi_ext, &lo_aln);
    let sum_sub = bvsub(b, &hi_ext, &lo_aln);
    let mant: Vec<BitLit> = (0..mw).map(|i| b.mux2(same_sign, sum_add[i], sum_sub[i])).collect();
    let add_carry = { let (_s, c) = adder(b, &hi_ext, &lo_aln, b.zero()); b.and2(same_sign, c) };

    // Exact-zero finite result (full cancellation, incl. both addends zero).
    let cancel_zero = {
        let mut az = b.one();
        for &m in &mant { let nm = b.not1(m); az = b.and2(az, nm); }
        let nc = b.not1(add_carry);
        b.and2(az, nc)
    };
    let res_sign = hi_sign;
    let base_exp = hi_exp.clone();

    // ---- Normalize. Case A (add carry): >>1, exp+1. Case B: LZC left-shift. ----
    let mut mant_a: Vec<BitLit> = Vec::with_capacity(mw);
    for i in 0..mw { let hb = if i + 1 < mw { mant[i + 1] } else { add_carry }; mant_a.push(hb); }
    mant_a[0] = b.or2(mant_a[0], mant[0]); // preserve dropped sticky on >>1
    let one_ew = const_n(b, ew, 1);
    let exp_a = bvadd(b, &base_exp, &one_ew);
    let lz = lzc(b, &mant);                 // count_width(mw) bits
    let lz_ew = zero_extend(b, &lz, ew);
    let mant_b = bvshl(b, &mant, &lz_ew);
    let exp_b = bvsub(b, &base_exp, &lz_ew);
    let mant_n: Vec<BitLit> = (0..mw).map(|i| b.mux2(add_carry, mant_a[i], mant_b[i])).collect();
    let exp_n: Vec<BitLit> = (0..ew).map(|i| b.mux2(add_carry, exp_a[i], exp_b[i])).collect();

    // ---- Single round: top sb bits as significand; (G,R,S) = mul-style. ----
    // Leading bit at index mw-1; top sb bits = mant_n[mw-sb .. mw].
    let sig: Vec<BitLit> = mant_n[(mw - sbu)..mw].to_vec();
    let g = mant_n[mw - sbu - 1];
    let r = mant_n[mw - sbu - 2];
    let mut s = b.zero();
    for bit in mant_n.iter().take(mw - sbu - 2) { s = b.or2(s, *bit); }
    let ext = ExtFp { sign: res_sign, exp: exp_n, sig, grs: (g, r, s) };
    let rounded = round(b, ext, eb, sb, rm);

    // ---- Special-case mux (priority NaN > Inf > cancel-zero > normal). ----
    special_case(b, &rounded, &ox, &oy, &oz, prod_sign, cancel_zero, rm, eb, sb)
}

fn bits_equal(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    let mut acc = b.one();
    for i in 0..x.len() { let d = b.xor2(x[i], y[i]); let s = b.not1(d); acc = b.and2(acc, s); }
    acc
}

/// Field-select a (sign, exp, sig) triple: `sel` ? a : c. `exp` width ew, `sig` width pw.
fn select3(b: &mut Blaster, sel: BitLit,
           a: (BitLit, &[BitLit], &[BitLit]), c: (BitLit, &[BitLit], &[BitLit]),
           ew: usize, pw: usize) -> (BitLit, Vec<BitLit>, Vec<BitLit>) {
    let sign = b.mux2(sel, a.0, c.0);
    let exp = (0..ew).map(|i| b.mux2(sel, a.1[i], c.1[i])).collect();
    let sig = (0..pw).map(|i| b.mux2(sel, a.2[i], c.2[i])).collect();
    (sign, exp, sig)
}

/// IEEE fp.fma special cases override the datapath result.
#[allow(clippy::too_many_arguments)]
fn special_case(b: &mut Blaster, normal: &[BitLit], ox: &Operand, oy: &Operand, oz: &Operand,
                prod_sign: BitLit, cancel_zero: BitLit, rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);
    // Invalid product 0·∞ (either order).
    let invalid = {
        let a = b.and2(ox.is_zero, oy.is_inf);
        let c = b.and2(ox.is_inf, oy.is_zero);
        b.or2(a, c)
    };
    let any_nan = { let t = b.or2(ox.is_nan, oy.is_nan); b.or2(t, oz.is_nan) };
    // prod_inf = (x or y inf) and not invalid.
    let any_xy_inf = b.or2(ox.is_inf, oy.is_inf);
    let not_invalid = b.not1(invalid);
    let prod_inf = b.and2(any_xy_inf, not_invalid);
    // ∞ + (∓∞): product ∞ and z ∞ with opposite sign.
    let inf_sign_clash = {
        let opp = b.xor2(prod_sign, oz.sign);
        let both = b.and2(prod_inf, oz.is_inf);
        b.and2(both, opp)
    };
    let want_nan = { let t = b.or2(any_nan, invalid); b.or2(t, inf_sign_clash) };
    // Inf result: product ∞ (sign = prod_sign) or z ∞ (sign = z.sign).
    let any_inf = b.or2(prod_inf, oz.is_inf);
    let inf_sign = b.mux2(prod_inf, prod_sign, oz.sign);
    let inf_bits = inf_pattern_bits(b, eb, sb, inf_sign);
    // Exact-zero sum sign rule: -0 iff (prod_sign ∧ z.sign) ∨ RTN. (RTN = rm.sel[3].)
    let both_neg = b.and2(prod_sign, oz.sign);
    let rtn = rm.sel[3];
    let zero_neg = b.or2(both_neg, rtn);
    let zero_bits = signed_zero_bits(b, eb, sb, zero_neg);

    let mut out = normal.to_vec();
    for i in 0..w { out[i] = b.mux2(cancel_zero, zero_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(any_inf, inf_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_nan, nan[i], out[i]); }
    out
}
```

- [ ] **Step 5: Run the circuit tests**

Run: `cargo test -p shinri-fp --lib fp_fma -- --nocapture`
Expected: PASS — `fp_fma_tiny_sampled_all_modes` and `fp_fma_float32_specials_and_random`. If the `(3,5)` sample surfaces an exponent off-by-one (the way `mul`'s `CORR=1` did), the divergence prints the exact `a/b/c/mode`; adjust the normalize/exponent arithmetic and re-run (the reference is the oracle).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/blast/fma.rs crates/shinri-fp/src/blast/mod.rs
git commit -m "feat(fp): fp.fma circuit (single-rounding, fp_add skeleton at 2·sb) for slice 2f"
```

---

### Task 4: Dispatch + soundness-fence admission

Wire `fp.fma` into `blast_word` and admit it through the fence so end-to-end queries reach the circuit (and malformed ones still fail closed).

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` (add a `blast_word` match arm, after the `FpRoundToIntegral` arm at line 118-122)
- Modify: `crates/shinri-solver/src/fp_stage.rs` (add an `FpFma` arm to `is_supported_fp_word`; add a fence unit test)

**Interfaces:**
- Consumes: `crate::blast::fma::fp_fma` (Task 3), `BuiltinOp::FpFma` (already in `shinri-core`).
- Produces: a supported `(RoundingMode, Float, Float, Float) -> Float` op end-to-end.

- [ ] **Step 1: Add the dispatch arm in `lib.rs`**

In `blast_word`, immediately after the `FpRoundToIntegral => { … }` arm (lines 118-122), add:

```rust
                    FpFma => {
                        let rm = self.blast_rm(ctx, kids[0]);
                        let xw = self.blast_word(ctx, kids[1]);
                        let yw = self.blast_word(ctx, kids[2]);
                        let zw = self.blast_word(ctx, kids[3]);
                        crate::blast::fma::fp_fma(&mut self.b, &xw, &yw, &zw, &rm, eb, sb)
                    }
```

- [ ] **Step 2: Admit it in the fence**

In `crates/shinri-solver/src/fp_stage.rs`, add this arm to `is_supported_fp_word` (after the `FpMin | FpMax` arm at lines 152-157, before the catch-all `_ => false`):

```rust
        // FpFma: (RM, F, F, F) -> F. RM operand must be a RoundingMode term;
        // all three FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpFma), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 4
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
                && is_supported_fp_word(ctx, kids[2])
                && is_supported_fp_word(ctx, kids[3])
        }
```

- [ ] **Step 3: Add a fence unit test in `fp_stage.rs`**

In `fp_stage.rs` `mod tests`, add (mirroring `fp_sqrt_word_is_supported`, line 323):

```rust
    #[test]
    fn fp_fma_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let z = fp_var(&mut ctx, "z");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let fma = ctx.mk_app(Op::Builtin(BuiltinOp::FpFma), &[rne, x, y, z]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[fma]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.fma is in scope as of slice 2f");
        // Malformed (missing the third FP operand) must NOT be admitted.
        let bad = ctx.mk_app(Op::Builtin(BuiltinOp::FpFma), &[rne, x, y]);
        if let Ok(bad) = bad {
            assert!(!super::is_supported_fp_word(&ctx, bad), "arity-3 fp.fma rejected");
        }
    }
```

- [ ] **Step 4: Run the fence test + crate build**

Run: `cargo test -p shinri-solver --lib fp_fma_word_is_supported -- --nocapture && cargo build -p shinri-fp -p shinri-solver`
Expected: PASS + clean build (no `unreachable!`-arm regressions).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/lib.rs crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): admit fp.fma through the FP soundness fence + dispatch"
```

---

### Task 5: End-to-end + differential-vs-z3 oracle

The standard slice test surface: SMT-LIB → solver SAT/UNSAT/get-model/symbolic-RM/fence-canary, plus a bounded z3 differential.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` (add a slice-2f block)
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (add `gen_fma_script` + `differential_qf_fp_fma`)

**Interfaces:**
- Consumes: `run` + `SolveOutcome` (fp_e2e.rs); `Lcg`/`RMS`/`N_ITERS`/`shinri_outcome`/`z3_outcome_arith` (fp_oracle.rs).
- Produces: gated coverage proving solver-level correctness.

- [ ] **Step 1: Write the end-to-end tests**

Append to `crates/shinri-solver/tests/fp_e2e.rs`:

```rust
// ── Slice-2f end-to-end: fp.fma SAT/UNSAT + symbolic-RM + fence canary ──

#[test]
fn fp_fma_nan_when_zero_times_inf_sat() {
    // 0 * +inf + x is NaN regardless of x: fp.isNaN holds -> SAT.
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (fp.isNaN (fp.fma RNE (_ +zero 8 24) (_ +oo 8 24) x))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_fma_inf_product_finite_addend_sat() {
    // (+inf) * x + y, with x = +1.0-ish nonzero and y finite, is +inf.
    // Use isInfinite over a symbolic-but-constrained query: SAT.
    let (o, _) = run(
        "(declare-fun y () Float32) \
         (assert (fp.isInfinite (fp.fma RTP (_ +oo 8 24) (_ +oo 8 24) y))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat); // +inf * +inf + y = +inf
}

#[test]
fn fp_fma_inf_minus_inf_is_nan_sat() {
    // (+inf)*(+inf) + (-inf) = +inf + (-inf) = NaN.
    let (o, _) = run(
        "(assert (fp.isNaN (fp.fma RNE (_ +oo 8 24) (_ +oo 8 24) (_ -oo 8 24)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_fma_symbolic_rm_sat_get_model() {
    // w = fma(rm, x, y, z) with symbolic rm and operands: SAT, model renders.
    let (o, model) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) \
         (declare-fun z () Float32) (declare-fun w () Float32) \
         (declare-fun rm () RoundingMode) \
         (assert (fp.eq w (fp.fma rm x y z))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triples: {model}");
}

#[test]
fn fp_fma_malformed_is_unknown() {
    // Fence canary: an fma whose operand is an unsupported FP word (fp.rem is out
    // of scope) must trip the fence -> Unknown, never SAT/UNSAT.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) (declare-fun w () Float32) \
         (assert (fp.eq w (fp.fma RNE x y (fp.rem x y)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}
```

Note for the implementer: confirm the special-constant surface forms `(_ +zero 8 24)`, `(_ +oo 8 24)`, `(_ -oo 8 24)` parse in this harness (they are used by `fp_oracle.rs` and existing `fp_e2e.rs` add/mul tests — grep `+oo` in `fp_e2e.rs`). If `fp.rem` is not yet a recognized op token in the parser (it is parsed+sort-checked per the foundation, so it should be), and the canary therefore fails to parse rather than returning Unknown, swap the unsupported inner op for `(fp.roundToIntegral RNE x)` nested under a *malformed* shape — but the intended canary is "in-scope op tree containing one out-of-scope op ⇒ whole query Unknown", so prefer keeping `fp.rem`.

- [ ] **Step 2: Run the e2e tests**

Run: `cargo test -p shinri-solver --test fp_e2e fp_fma -- --nocapture`
Expected: PASS — NaN/inf specials SAT, symbolic-RM SAT + model renders, malformed → Unknown.

- [ ] **Step 3: Commit the e2e tests**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): end-to-end fp.fma specials + symbolic-RM + fence canary"
```

- [ ] **Step 4: Add the oracle generator + differential test**

Append to `crates/shinri-solver/tests/fp_oracle.rs` (mirror `gen_sqrt_script`/`differential_qf_fp_sqrt`). Each of x/y/z is 50% a variable, 50% a special constant, which keeps many instances shallow enough to decide fast (the same tactic `gen_rel_script` uses):

```rust
/// Random QF_FP with fp.fma over all five rounding modes (ternary op). Operands
/// mix variables and special constants to keep instances decidable-fast.
fn gen_fma_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n\
         (declare-fun w () (_ FloatingPoint 8 24))\n",
    );
    let use_sym_rm = rng.below(4) == 0;
    if use_sym_rm {
        s.push_str("(declare-fun rm () RoundingMode)\n");
    }
    let rm = |rng: &mut Lcg| -> String {
        if use_sym_rm && rng.below(2) == 0 { "rm".to_string() }
        else { RMS[rng.below(RMS.len() as u64) as usize].to_string() }
    };
    const SPECIALS: &[&str] = &[
        "(_ +zero 8 24)", "(_ -zero 8 24)", "(_ +oo 8 24)", "(_ -oo 8 24)", "(_ NaN 8 24)",
    ];
    let vars = ["x", "y", "z"];
    let operand = |rng: &mut Lcg| -> String {
        if rng.below(2) == 0 { vars[rng.below(3) as usize].to_string() }
        else { SPECIALS[rng.below(SPECIALS.len() as u64) as usize].to_string() }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = format!("(fp.fma {} {} {} {})", rm(rng), operand(rng), operand(rng), operand(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq w {term})"),
            1 => format!("(= w {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 { s.push_str(&format!("(assert (not {atom}))\n")); }
        else { s.push_str(&format!("(assert {atom})\n")); }
    }
    s.push_str("(check-sat)\n");
    s
}

// fp.fma is the DEEPEST FP datapath (2·sb multiply + 2·sb LZC/shifts + the
// rounder). Bound this oracle well below N_ITERS, mirroring SQRT_ITERS/DIV_ITERS:
// z3 refutes hard conjoined symbolic-fma UNSAT instances in <1s via its native FP
// theory, but our eager bit-blaster must grind a full propositional refutation
// over multiple deep circuits — minutes-to-hours. Such instances carry no
// correctness signal (a disagreement can only arise where both solvers decide),
// so bound below the first intractable iter rather than wait it out. Start at 20;
// lower it (after confirming zero disagreement up to that point) if a late
// instance grinds. Do NOT raise without first adding a per-instance wall-clock
// timeout — a higher bound will hang on a hard UNSAT.
const FMA_ITERS: usize = 20;

#[test]
fn differential_qf_fp_fma() {
    let mut rng = Lcg(0x00FA_2D11_6C03_55);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..FMA_ITERS {
        let src = gen_fma_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown { n_unknown += 1; continue; }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"]).build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!("QF_FP fma DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    println!("differential_qf_fp_fma: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}
```

- [ ] **Step 5: Run the oracle (background — multi-minute, needs z3 on PATH)**

Per the gate-suite policy, run this yourself in the background, do not loop a subagent:

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_fma -- --nocapture`
Expected: PASS, prints `differential_qf_fp_fma: sat=… unsat=… unknown=…` with both `sat > 0` and `unsat > 0` and zero disagreements. If an instance grinds before `FMA_ITERS`, lower the bound below the first intractable iter (only after confirming no disagreement up to that point) and record the iter in the rationale comment — mirror the `SQRT_ITERS` note. If `sat`/`unsat` coverage is one-sided at the bound, adjust the `Lcg` seed until both appear (as `differential_qf_fp_sqrt` does).

- [ ] **Step 6: Commit the oracle**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential-vs-z3 oracle for fp.fma over all five modes"
```

---

## Self-Review

**Spec coverage:**
- Semantics (NaN→NaN, 0·∞→NaN, ∞±∞→NaN, product-∞ / z-∞ sign rules, exact `x·y+z` rounded once, exact-zero sign rule, all 5 modes, literal+symbolic RM) → Task 1 (golden) + Task 3 (circuit) + their tests.
- Single rounding → Task 1 forms the exact `Rational` then one `round_rational`; Task 3 feeds one `ExtFp` to one `round()`. Witness in both Task 1 and Task 3 tests.
- `fp_add`-skeleton-at-2·sb scheme, zero-extended z, zero-product clamp, mul-style GRS extraction → Task 3 implementation + comments.
- Reuse mul's exact product+normalize (DRY) → Task 2 extraction (`significand_product`), guarded by mul's exhaustive gate.
- Dispatch + fence admission + fail-closed → Task 4 (+ malformed canary in Task 5).
- Test trio (reference unit, oracle, e2e) → Tasks 1/3 (unit), 5 (oracle + e2e).
- Deep-circuit/SAT-recursion caution → Task 5 `FMA_ITERS` bound + background-run instruction.
- Non-goals (fp.rem + conversion suite stay fenced) → enforced by the unchanged fence; canary in Task 5 confirms an `fp.rem`-nested tree stays Unknown.

**Placeholder scan:** No "TBD"/"add error handling"/bare "write tests". Two explicit implementer notes (Task 3 `(3,5)` pattern-label sanity-check + the `0x0FMA_5EED` literal fix; Task 5 special-form parse check) are concrete fix-it instructions, not deferred work. The `FMA_ITERS=20` bound is a real starting value with tuning criteria, mirroring the shipped `SQRT_ITERS`/`DIV_ITERS`.

**Type consistency:** `fp_fma(b, x, y, z, rm, eb, sb) -> Vec<BitLit>` and `ref_fma(eb, sb, x, y, z, mode) -> Integer` used identically across Tasks 1/3/4/5. `significand_product(b, ox, oy, eb, sb) -> (Vec<BitLit>, Vec<BitLit>)` defined in Task 2, consumed in Task 3. Local helpers `bits_equal`/`select3`/`special_case` defined and consumed within `fma.rs` (Task 3). `BuiltinOp::FpFma` matches the existing core variant. `rm.sel[3]` = RTN selector (same indexing `round()` and `fp_add` use).
