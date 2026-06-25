# shinri QF_FP — Slice 1 (Rounding-Free Vertical Slice) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stand up a new `shinri-fp` crate and wire it into the solver so a pure-QF_FP query over the rounding-free operator set (`fp.abs`, `fp.neg`, the 7 classification predicates, `fp.eq`, NaN-aware core `=`) parses → bit-blasts → solves → returns SAT/UNSAT with a `get-model` witness.

**Architecture:** `shinri-fp` is an eager bit-blasting front-end exactly like `shinri-bv`. It uses `shinri_bv::Blaster` as a pure gate/clause factory (one/zero/fresh/and2/or2/xor2/mux2/not1/full_adder), keeps its **own** word cache and variable-bit map (the Blaster's `cache` is `pub(crate)` to `shinri-bv`), and returns a `shinri_bv::Lowered` so the solver can reuse the existing `replay_bv_cnf` replay machinery. A new `fp_stage.rs` mirrors `bv_stage.rs` (detect/collect/fence). FP gets its **own** `Blaster` (BV+FP unification is a later plan); a query mixing FP with BV or any other theory fences to `Unknown`.

**Tech Stack:** Rust 2021, `shinri-core` (term/sort layer — FP sorts/ops already landed), `shinri-bv` (`Blaster`, `BitLit`, `Lowered`, `model::pack`), `shinri-num` (`Integer`/`Rational`), `shinri-sat`, `shinri-theory` (`ModelVal`), `shinri-parser`, `rustc-hash`.

**Spec:** `docs/superpowers/specs/2026-06-25-shinri-qffp-vertical-slice-design.md`.

## Global Constraints

- Rust edition `2021`; workspace `rust-version = "1.96.0"`.
- **No new external runtime dependencies.** `shinri-fp` depends only on existing workspace crates (`shinri-core`, `shinri-bv`, `shinri-num`, `shinri-sat`, `rustc-hash`) plus `easy_smt` **dev-dependency** for the feature-gated oracle (already used by `shinri-solver`'s `qfbv_oracle.rs`).
- Out-of-scope / malformed input must surface as a sound `Unknown`, **never a wrong SAT/UNSAT** and **never a panic** on user input (`debug_assert!` for internal invariants only).
- FP bit layout is MSB→LSB `[ sign(1) | exponent(eb) | trailing-significand(sb-1) ]`; total width `W = eb + sb`. `sb` **includes** the hidden bit. Exponent bias = `2^(eb-1) - 1`. Valid formats require `eb >= 2`, `sb >= 2`.
- The Blaster bit order is **LSB→MSB** (index 0 = least significant), matching `shinri_bv::Blaster::blast_word` and `shinri_bv::model::pack`. All FP `Vec<BitLit>` words use this order.
- Soundness-critical: FP `=`/`distinct` MUST be surrogated (collected as FP atoms), or they route to EUF as uninterpreted functions and can answer wrongly. `collect_fp_atoms` includes Eq/Distinct over Float-sorted operands (mirrors `collect_bv_atoms`).
- Follow existing patterns exactly: crate layout mirrors `shinri-bv`; the solver stage mirrors `bv_stage.rs`; gadget tests mirror the concrete-input SAT-solve pattern in `shinri-bv`'s `lower_const_atom_no_var_bits` test.

---

## File Structure

**New crate `crates/shinri-fp/`:**
- `Cargo.toml` — crate manifest; workspace members entry.
- `src/lib.rs` — public `lower(ctx, fp_atoms) -> shinri_bv::Lowered`; `FpBlaster` wrapper (own cache + var_bits); FP atom dispatch.
- `src/reference.rs` — exact scalar oracle: `decode`, `FpClass`, classification/eq/abs/neg semantics, and the rounding core (`round_rational`).
- `src/unpack.rs` — `unpack(&mut Blaster, &[BitLit], eb, sb) -> Unpacked` (sign/exp/explicit-sig/flags).
- `src/pack.rs` — `pack(&mut Blaster, &Unpacked, eb, sb) -> Vec<BitLit>` with NaN canonicalization (deferred use; provided for symmetry/tests).
- `src/blast/mod.rs` — `pub mod classify; pub mod compare; pub mod structural;`.
- `src/blast/classify.rs` — the 7 classification predicate gadgets.
- `src/blast/compare.rs` — `fp_eq` and NaN-aware `core_eq` atom gadgets.
- `src/blast/structural.rs` — `abs`/`neg` word gadgets.
- `src/model.rs` — re-export/thin wrapper over `shinri_bv::model::pack` for FP value reconstruction (kept separate so later plans can specialize).

**Modified — solver:**
- `crates/shinri-solver/Cargo.toml` — add `shinri-fp` dependency.
- `crates/shinri-solver/src/fp_stage.rs` — **new**: `solver_uses_fp`, `collect_fp_atoms`, `has_non_fp_theory_atom`, `FpSurrogates`.
- `crates/shinri-solver/src/lib.rs` — wire the FP stage (detect→fence→lower→replay→model); add `fp_var_bits` field; FP model extraction.
- `crates/shinri-solver/src/model.rs` — render `ModelVal::Float`.
- `crates/shinri-solver/tests/fp_e2e.rs` — **new**: end-to-end SAT/UNSAT/get-model.
- `crates/shinri-solver/tests/fp_oracle.rs` — **new**: feature-gated differential-vs-z3.

**Modified — theory & parser:**
- `crates/shinri-theory/src/types.rs` — add `ModelVal::Float { eb, sb, bits }`.
- `crates/shinri-parser/src/print.rs:51-52` — replace `<fp>`/`<rm>` placeholders with real rendering.

Tasks 1–7 build the `shinri-fp` crate. Tasks 8–9 are the theory/parser carry-forwards. Tasks 10–12 are solver wiring + tests. Each task ends with a green test and a commit.

---

### Task 1: Create the `shinri-fp` crate skeleton + the rounding-free reference oracle

**Files:**
- Create: `crates/shinri-fp/Cargo.toml`
- Create: `crates/shinri-fp/src/lib.rs`
- Create: `crates/shinri-fp/src/reference.rs`
- Modify: `Cargo.toml` (workspace `members`)
- Test: `crates/shinri-fp/src/reference.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Produces:
  - `enum FpClass { Nan, Inf { sign: bool }, Zero { sign: bool }, Subnormal { sign: bool, sig: Integer }, Normal { sign: bool, biased_exp: u64, sig: Integer } }` (`sign==true` means negative).
  - `fn decode(eb: u32, sb: u32, bits: &Integer) -> FpClass`.
  - `fn ref_is_nan/ref_is_inf/ref_is_zero/ref_is_normal/ref_is_subnormal/ref_is_negative/ref_is_positive(c: &FpClass) -> bool`.
  - `fn ref_fp_eq(a: &FpClass, b: &FpClass) -> bool` (IEEE `fp.eq`: NaN≠anything, +0==−0).
  - `fn ref_core_eq(eb, sb, a: &Integer, b: &Integer) -> bool` (theory `=`: NaN==NaN, +0≠−0, else bit-equal).
  - `fn ref_abs(eb, sb, bits: &Integer) -> Integer` (clear sign bit).
  - `fn ref_neg(eb, sb, bits: &Integer) -> Integer` (flip sign bit).
  - helper `fn field(bits: &Integer, lo: u32, width: u32) -> Integer` (extract `[lo, lo+width)`).

- [ ] **Step 1: Create the crate manifest**

Create `crates/shinri-fp/Cargo.toml`:

```toml
[package]
name = "shinri-fp"
version = "0.1.0"
edition = "2021"
rust-version = "1.96.0"

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-bv = { path = "../shinri-bv" }
shinri-num = { path = "../shinri-num" }
rustc-hash = "2"

[dev-dependencies]
shinri-sat = { path = "../shinri-sat" }
```

> Confirm the `rustc-hash` version string matches the other crates' manifests (e.g. `crates/shinri-bv/Cargo.toml`); copy it verbatim. If they use a workspace dependency table, mirror that form instead.

- [ ] **Step 2: Register the crate in the workspace**

In the root `Cargo.toml`, add `"crates/shinri-fp"` to the `members` array (keep the list sorted/grouped as the file already does).

- [ ] **Step 3: Create the lib root**

Create `crates/shinri-fp/src/lib.rs`:

```rust
//! shinri-fp: eager bit-blasting of QF_FP to CNF, reusing the shinri-bv Blaster
//! as a gate/clause factory. See
//! docs/superpowers/specs/2026-06-25-shinri-qffp-vertical-slice-design.md.

pub mod reference;
```

- [ ] **Step 4: Write the failing test**

Create `crates/shinri-fp/src/reference.rs` with only the test module first:

```rust
//! Exact scalar reference oracle for QF_FP — the trusted golden semantics.
//! Slice 1 covers decode + classification + fp.eq/core-= + abs/neg.
//! Bit layout MSB->LSB: [ sign(1) | exp(eb) | trailing-sig(sb-1) ], W = eb+sb.

use shinri_num::Integer;

#[cfg(test)]
mod tests {
    use super::*;

    // Float32 (eb=8, sb=24) reference encodings.
    fn i(v: u64) -> Integer { Integer::from(v) }

    #[test]
    fn decode_and_classify_float32() {
        let (eb, sb) = (8u32, 24u32);
        // +zero = 0x00000000
        assert!(ref_is_zero(&decode(eb, sb, &i(0x0000_0000))));
        assert!(!ref_is_negative(&decode(eb, sb, &i(0x0000_0000))));
        // -zero = 0x80000000
        assert!(ref_is_zero(&decode(eb, sb, &i(0x8000_0000))));
        assert!(ref_is_negative(&decode(eb, sb, &i(0x8000_0000))));
        // +inf = 0x7F800000
        assert!(ref_is_inf(&decode(eb, sb, &i(0x7F80_0000))));
        // -inf = 0xFF800000
        assert!(ref_is_inf(&decode(eb, sb, &i(0xFF80_0000))));
        assert!(ref_is_negative(&decode(eb, sb, &i(0xFF80_0000))));
        // NaN = 0x7FC00000 (and any non-zero sig with exp all ones)
        assert!(ref_is_nan(&decode(eb, sb, &i(0x7FC0_0000))));
        assert!(ref_is_nan(&decode(eb, sb, &i(0x7F80_0001)))); // sNaN payload
        // 1.0 = 0x3F800000 is normal, positive
        let one = decode(eb, sb, &i(0x3F80_0000));
        assert!(ref_is_normal(&one));
        assert!(ref_is_positive(&one));
        // smallest subnormal = 0x00000001
        let sub = decode(eb, sb, &i(0x0000_0001));
        assert!(ref_is_subnormal(&sub));
    }

    #[test]
    fn fp_eq_and_core_eq_semantics() {
        let (eb, sb) = (8u32, 24u32);
        let pz = i(0x0000_0000);
        let nz = i(0x8000_0000);
        let nan = i(0x7FC0_0000);
        // fp.eq: +0 == -0, NaN != NaN
        assert!(ref_fp_eq(&decode(eb, sb, &pz), &decode(eb, sb, &nz)));
        assert!(!ref_fp_eq(&decode(eb, sb, &nan), &decode(eb, sb, &nan)));
        // core =: +0 != -0, NaN == NaN (canonical), bit-equal otherwise
        assert!(!ref_core_eq(eb, sb, &pz, &nz));
        assert!(ref_core_eq(eb, sb, &nan, &nan));
        assert!(ref_core_eq(eb, sb, &pz, &pz));
    }

    #[test]
    fn abs_and_neg_bits() {
        let (eb, sb) = (8u32, 24u32);
        // neg(1.0)= -1.0 = 0xBF800000 ; abs(-1.0)=1.0=0x3F800000
        assert_eq!(ref_neg(eb, sb, &i(0x3F80_0000)), i(0xBF80_0000));
        assert_eq!(ref_abs(eb, sb, &i(0xBF80_0000)), i(0x3F80_0000));
        assert_eq!(ref_abs(eb, sb, &i(0x3F80_0000)), i(0x3F80_0000));
    }
}
```

- [ ] **Step 5: Run test to verify it fails**

Run: `cargo test -p shinri-fp reference`
Expected: FAIL — `decode`, `FpClass`, etc. not defined (compile error).

- [ ] **Step 6: Implement the oracle**

Add above the test module in `crates/shinri-fp/src/reference.rs`:

```rust
/// Classified value of an FP bit pattern. `sign == true` means negative.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum FpClass {
    Nan,
    Inf { sign: bool },
    Zero { sign: bool },
    Subnormal { sign: bool, sig: Integer },
    Normal { sign: bool, biased_exp: u64, sig: Integer },
}

/// Extract the bit field `[lo, lo+width)` (LSB index 0) as a non-negative Integer.
pub fn field(bits: &Integer, lo: u32, width: u32) -> Integer {
    let two = Integer::from(2u64);
    // shifted = bits / 2^lo
    let mut shifted = bits.clone();
    for _ in 0..lo {
        shifted = shifted.div_rem(&two).0;
    }
    // modulus = 2^width
    let mut modulus = Integer::one();
    for _ in 0..width {
        modulus = modulus * two.clone();
    }
    shifted.div_rem(&modulus).1
}

/// Decode an (eb, sb) bit pattern into its classified value.
pub fn decode(eb: u32, sb: u32, bits: &Integer) -> FpClass {
    let w = eb + sb;
    let sign = !field(bits, w - 1, 1).is_zero();
    let exp = field(bits, sb - 1, eb);              // eb-bit exponent field
    let sig = field(bits, 0, sb - 1);               // (sb-1)-bit trailing significand
    let exp_all_ones = {
        let two = Integer::from(2u64);
        let mut m = Integer::one();
        for _ in 0..eb { m = m * two.clone(); }
        m - Integer::one()
    };
    let exp_u = exp.to_i128().unwrap_or(-1);
    if exp == exp_all_ones {
        if sig.is_zero() { FpClass::Inf { sign } } else { FpClass::Nan }
    } else if exp.is_zero() {
        if sig.is_zero() { FpClass::Zero { sign } } else { FpClass::Subnormal { sign, sig } }
    } else {
        FpClass::Normal { sign, biased_exp: exp_u as u64, sig }
    }
}

pub fn ref_is_nan(c: &FpClass) -> bool { matches!(c, FpClass::Nan) }
pub fn ref_is_inf(c: &FpClass) -> bool { matches!(c, FpClass::Inf { .. }) }
pub fn ref_is_zero(c: &FpClass) -> bool { matches!(c, FpClass::Zero { .. }) }
pub fn ref_is_subnormal(c: &FpClass) -> bool { matches!(c, FpClass::Subnormal { .. }) }
pub fn ref_is_normal(c: &FpClass) -> bool { matches!(c, FpClass::Normal { .. }) }

pub fn ref_is_negative(c: &FpClass) -> bool {
    // NaN is neither negative nor positive; zeros carry a sign but are NOT
    // "negative" under fp.isNegative (per SMT-LIB: isNegative excludes zeros).
    match c {
        FpClass::Nan => false,
        FpClass::Zero { .. } => false,
        FpClass::Inf { sign }
        | FpClass::Subnormal { sign, .. }
        | FpClass::Normal { sign, .. } => *sign,
    }
}

pub fn ref_is_positive(c: &FpClass) -> bool {
    match c {
        FpClass::Nan => false,
        FpClass::Zero { .. } => false,
        FpClass::Inf { sign }
        | FpClass::Subnormal { sign, .. }
        | FpClass::Normal { sign, .. } => !*sign,
    }
}

/// IEEE `fp.eq`: NaN compares unequal to everything (incl. itself); +0 == -0;
/// otherwise equal iff the same value (same class, sign for non-zero, fields).
pub fn ref_fp_eq(a: &FpClass, b: &FpClass) -> bool {
    use FpClass::*;
    match (a, b) {
        (Nan, _) | (_, Nan) => false,
        (Zero { .. }, Zero { .. }) => true, // +0 == -0
        (Inf { sign: s1 }, Inf { sign: s2 }) => s1 == s2,
        (Normal { sign: s1, biased_exp: e1, sig: g1 },
         Normal { sign: s2, biased_exp: e2, sig: g2 }) => s1 == s2 && e1 == e2 && g1 == g2,
        (Subnormal { sign: s1, sig: g1 }, Subnormal { sign: s2, sig: g2 }) => s1 == s2 && g1 == g2,
        _ => false,
    }
}

/// Theory core `=`: NaN == NaN (the theory has exactly one NaN value), +0 != -0,
/// otherwise bit-pattern equality. Note: non-canonical NaN payloads all denote
/// the single NaN value, so any two NaNs are core-equal.
pub fn ref_core_eq(eb: u32, sb: u32, a: &Integer, b: &Integer) -> bool {
    let ca = decode(eb, sb, a);
    let cb = decode(eb, sb, b);
    match (&ca, &cb) {
        (FpClass::Nan, FpClass::Nan) => true,
        (FpClass::Nan, _) | (_, FpClass::Nan) => false,
        _ => a == b,
    }
}

pub fn ref_abs(eb: u32, sb: u32, bits: &Integer) -> Integer {
    let w = eb + sb;
    let two = Integer::from(2u64);
    let mut sign_mask = Integer::one();
    for _ in 0..(w - 1) { sign_mask = sign_mask * two.clone(); }
    // clear the sign bit: bits AND NOT signbit  ==  bits - (bit*signmask)
    if field(bits, w - 1, 1).is_zero() { bits.clone() } else { bits.clone() - sign_mask }
}

pub fn ref_neg(eb: u32, sb: u32, bits: &Integer) -> Integer {
    let w = eb + sb;
    let two = Integer::from(2u64);
    let mut sign_mask = Integer::one();
    for _ in 0..(w - 1) { sign_mask = sign_mask * two.clone(); }
    if field(bits, w - 1, 1).is_zero() { bits.clone() + sign_mask } else { bits.clone() - sign_mask }
}
```

> Confirm the exact `Integer` API: `div_rem(&Integer) -> (Integer, Integer)`, `is_zero`, `one`, `to_i128`, `Integer::from(u64)`, and `*`/`-`/`+` operators are all used by `shinri-bv` (`blast/mod.rs`) and `shinri-solver` (`model.rs`) — match those call shapes. If `div_rem` borrows differently, mirror `model.rs`'s usage verbatim.

- [ ] **Step 7: Run test to verify it passes**

Run: `cargo test -p shinri-fp reference`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add Cargo.toml crates/shinri-fp/Cargo.toml crates/shinri-fp/src/lib.rs crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): shinri-fp crate skeleton + rounding-free reference oracle"
```

---

### Task 2: Reference oracle — the rounding core

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs`
- Test: `crates/shinri-fp/src/reference.rs`

**Interfaces:**
- Consumes: `FpClass`, `field`, `decode` (Task 1).
- Produces:
  - `enum RoundMode { Rne, Rna, Rtp, Rtn, Rtz }`.
  - `fn class_to_rational(eb: u32, sb: u32, c: &FpClass) -> Option<Rational>` (None for NaN/Inf).
  - `fn round_rational(eb: u32, sb: u32, value: &Rational, mode: RoundMode) -> Integer` — round an **exact** real into the `(eb,sb)` bit pattern (overflow→∞, underflow→subnormal/zero), used by Plan 2's datapaths.

> This task builds the rounding core now (per spec §4.1) so later plans inherit a trusted reference. No slice-1 operator consumes it; it is validated against known IEEE encodings here.

- [ ] **Step 1: Write the failing test**

Add to the test module in `crates/shinri-fp/src/reference.rs`:

```rust
#[test]
fn round_known_float32_encodings() {
    use shinri_num::Rational;
    let (eb, sb) = (8u32, 24u32);
    fn rat(n: i64, d: i64) -> Rational {
        Rational::new(Integer::from(n.unsigned_abs()) * if n < 0 { Integer::from(-1i64) } else { Integer::one() },
                      Integer::from(d as u64))
    }
    // 1.0 -> 0x3F800000
    assert_eq!(round_rational(eb, sb, &rat(1, 1), RoundMode::Rne), Integer::from(0x3F80_0000u64));
    // 2.0 -> 0x40000000
    assert_eq!(round_rational(eb, sb, &rat(2, 1), RoundMode::Rne), Integer::from(0x4000_0000u64));
    // 0.5 -> 0x3F000000
    assert_eq!(round_rational(eb, sb, &rat(1, 2), RoundMode::Rne), Integer::from(0x3F00_0000u64));
    // -1.0 -> 0xBF800000
    assert_eq!(round_rational(eb, sb, &rat(-1, 1), RoundMode::Rne), Integer::from(0xBF80_0000u64));
    // 0.1 (not representable) RNE -> 0x3DCCCCCD
    assert_eq!(round_rational(eb, sb, &rat(1, 10), RoundMode::Rne), Integer::from(0x3DCC_CCCDu64));
    // 0.1 RTZ -> 0x3DCCCCCC (truncates toward zero)
    assert_eq!(round_rational(eb, sb, &rat(1, 10), RoundMode::Rtz), Integer::from(0x3DCC_CCCCu64));
    // exact zero -> +0
    assert_eq!(round_rational(eb, sb, &rat(0, 1), RoundMode::Rne), Integer::from(0u64));
}
```

> Confirm `shinri_num::Rational::new(num: Integer, den: Integer)` and `numer()`/`denom()` accessors against `crates/shinri-solver/src/model.rs::format_rational` (which calls `r.numer()`/`r.denom()`). If the constructor differs (e.g. `Rational::from((n, d))`), adapt the `rat` helper; the seven assertions are the contract.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp round_known_float32_encodings`
Expected: FAIL — `round_rational`/`RoundMode` undefined.

- [ ] **Step 3: Implement the rounding core**

Add above the test module in `crates/shinri-fp/src/reference.rs`:

```rust
use shinri_num::Rational;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RoundMode { Rne, Rna, Rtp, Rtn, Rtz }

/// Exact rational value of a finite FP class (None for NaN/Inf).
/// value = (-1)^sign * significand * 2^(exp - bias - (sb-1)), with the hidden
/// bit added for normals.
pub fn class_to_rational(eb: u32, sb: u32, c: &FpClass) -> Option<Rational> {
    let bias = (1i64 << (eb - 1)) - 1;
    let pow2 = |k: i64| -> Rational {
        // 2^k as a Rational (k may be negative).
        let mut acc = Integer::one();
        let two = Integer::from(2u64);
        for _ in 0..k.unsigned_abs() { acc = acc * two.clone(); }
        if k >= 0 { Rational::new(acc, Integer::one()) } else { Rational::new(Integer::one(), acc) }
    };
    let signed = |r: Rational, sign: bool| if sign { Rational::new(Integer::from(-1i64), Integer::one()) * r } else { r };
    match c {
        FpClass::Nan | FpClass::Inf { .. } => None,
        FpClass::Zero { .. } => Some(Rational::new(Integer::zero(), Integer::one())),
        FpClass::Subnormal { sign, sig } => {
            // value = sig * 2^(1 - bias - (sb-1))
            let m = Rational::new(sig.clone(), Integer::one());
            Some(signed(m * pow2(1 - bias - (sb as i64 - 1)), *sign))
        }
        FpClass::Normal { sign, biased_exp, sig } => {
            // mantissa = (2^(sb-1) + sig) ; value = mantissa * 2^(exp - bias - (sb-1))
            let hidden = {
                let two = Integer::from(2u64);
                let mut acc = Integer::one();
                for _ in 0..(sb - 1) { acc = acc * two.clone(); }
                acc
            };
            let mant = Rational::new(hidden + sig.clone(), Integer::one());
            Some(signed(mant * pow2(*biased_exp as i64 - bias - (sb as i64 - 1)), *sign))
        }
    }
}

/// Round an exact real `value` into the (eb, sb) bit pattern under `mode`.
/// Handles sign of zero from the sign of `value` (0 -> +0). Overflow -> inf,
/// underflow -> subnormal/zero.
pub fn round_rational(eb: u32, sb: u32, value: &Rational, mode: RoundMode) -> Integer {
    let zero = Rational::new(Integer::zero(), Integer::one());
    let sign = *value < zero; // sign bit
    let bias = (1i64 << (eb - 1)) - 1;
    let emax = bias;            // max unbiased exponent for normals
    let emin = 1 - bias;        // min unbiased exponent for normals
    // Work with the magnitude.
    let mag = if sign { Rational::new(Integer::from(-1i64), Integer::one()) * value.clone() } else { value.clone() };

    let pack = |sign: bool, exp_field: u64, sig: Integer| -> Integer {
        let two = Integer::from(2u64);
        let mut sig_scale = Integer::one(); // 2^0 — sig occupies bits [0, sb-1)
        let _ = &mut sig_scale;
        let mut exp_scale = Integer::one();
        for _ in 0..(sb - 1) { exp_scale = exp_scale * two.clone(); }
        let mut sign_scale = exp_scale.clone();
        for _ in 0..eb { sign_scale = sign_scale * two.clone(); }
        let mut out = sig; // trailing sig in [0, sb-1)
        out = out + Integer::from(exp_field) * exp_scale;
        if sign { out = out + sign_scale; }
        out
    };

    if mag == zero {
        return pack(sign, 0, Integer::zero()); // signed zero
    }

    // Decompose mag = m * 2^e with 2^(sb-1) <= m_int < 2^sb after scaling,
    // by finding the exponent E such that 2^E <= mag < 2^(E+1).
    // Then the (sb-1) fractional bits + round bit decide the mantissa.
    // Implemented via exact rational scaling. (Reference impl — clarity over speed.)
    //
    // Step A: find unbiased exponent E (floor log2 of mag).
    let two_r = Rational::new(Integer::from(2u64), Integer::one());
    let half = Rational::new(Integer::one(), Integer::from(2u64));
    let mut e: i64 = 0;
    let mut m = mag.clone();
    while m >= two_r { m = m * half.clone(); e += 1; }
    while m < Rational::new(Integer::one(), Integer::one()) { m = m * two_r.clone(); e -= 1; }
    // now 1 <= m < 2, value = m * 2^e

    // Step B: choose target precision. Normal if e >= emin, else subnormal at emin.
    let (target_exp, frac_bits) = if e >= emin {
        (e, sb as i64 - 1)
    } else {
        (emin, sb as i64 - 1 - (emin - e)) // fewer significand bits for subnormals
    };
    // scaled = significand * 2^frac_bits as an exact rational, where significand
    // includes the hidden 1 for normals.
    let scale = {
        let mut acc = Integer::one();
        let two = Integer::from(2u64);
        let k = (target_exp - e).unsigned_abs();
        for _ in 0..k { acc = acc * two.clone(); }
        if target_exp - e >= 0 { Rational::new(Integer::one(), acc) } else { Rational::new(acc, Integer::one()) }
    };
    // value / 2^target_exp, then * 2^frac_bits
    let mut scaled = mag.clone() * scale; // = m * 2^(e - target_exp)
    let pow_frac = {
        let mut acc = Integer::one();
        let two = Integer::from(2u64);
        for _ in 0..frac_bits.max(0) { acc = acc * two.clone(); }
        Rational::new(acc, Integer::one())
    };
    scaled = scaled * pow_frac;

    // Split into integer quotient q and remainder fraction for rounding.
    let q = scaled.numer().div_rem(scaled.denom()).0; // floor(scaled) since scaled >= 0
    let q_rat = Rational::new(q.clone(), Integer::one());
    let frac = scaled.clone() - q_rat; // in [0,1)

    let round_up = match mode {
        RoundMode::Rtz => false,
        RoundMode::Rtp => !sign && frac > zero, // toward +inf: round magnitude up only if positive
        RoundMode::Rtn => sign && frac > zero,  // toward -inf
        RoundMode::Rne => {
            if frac > half { true }
            else if frac < half { false }
            else { // tie -> to even
                !q.div_rem(&Integer::from(2u64)).1.is_zero()
            }
        }
        RoundMode::Rna => frac >= half,
    };
    let mut mant_int = if round_up { q + Integer::one() } else { q };

    // mant_int now has (frac_bits+1) integer bits for normals (leading hidden 1),
    // or fewer for subnormals. Detect carry that bumps the exponent.
    let mut final_exp = target_exp;
    let hidden_pos = {
        // the hidden-bit position value: 2^frac_bits (normals). For subnormals the
        // significand has no implicit leading 1; carry into it promotes to normal.
        let mut acc = Integer::one();
        let two = Integer::from(2u64);
        for _ in 0..frac_bits.max(0) { acc = acc * two.clone(); }
        acc
    };
    let two_hidden = hidden_pos.clone() * Integer::from(2u64);
    if mant_int >= two_hidden {
        // rounding overflowed the significand: divide by 2, bump exponent.
        mant_int = mant_int.div_rem(&Integer::from(2u64)).0;
        final_exp += 1;
    }

    // Overflow to infinity.
    if final_exp > emax {
        let exp_all_ones: u64 = (1u64 << eb) - 1;
        return pack(sign, exp_all_ones, Integer::zero());
    }

    // Build the encoded fields.
    let exp_all_ones: u64 = (1u64 << eb) - 1;
    let trailing_mask = hidden_pos.clone() - Integer::one(); // low frac_bits bits
    if mant_int < hidden_pos {
        // Subnormal (no hidden bit set) — exponent field 0.
        let sig = mant_int.div_rem(&hidden_pos).1; // mant_int (already < hidden_pos)
        let _ = &exp_all_ones;
        let _ = &trailing_mask;
        return pack(sign, 0, sig);
    }
    // Normal: strip the hidden bit, set the biased exponent.
    let trailing = mant_int.div_rem(&hidden_pos).1;
    let biased = (final_exp + bias) as u64;
    pack(sign, biased, trailing)
}
```

> This reference rounder favors clarity over speed (exact-rational scaling, no float ops). It is **not** on any hot path; it exists to be the trusted oracle. Confirm `Rational` supports `<`, `>=`, `>`, `==`, `*`, `-`, `.numer()`, `.denom()` (used by `format_rational`); if comparison operators are not derived, add a helper that compares `a.numer()*b.denom()` vs `b.numer()*a.denom()`.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp round_known_float32_encodings`
Expected: PASS. If a specific encoding is off by one ULP, the bug is in the tie/round-bit logic — fix `round_up` and re-run. Do not change the expected constants (they are the IEEE-754 canonical encodings).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): exact-rational rounding core in the reference oracle"
```

---

### Task 3: FP word-blasting substrate — `FpBlaster`, `unpack`, `pack`

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs`
- Create: `crates/shinri-fp/src/unpack.rs`
- Create: `crates/shinri-fp/src/pack.rs`
- Test: `crates/shinri-fp/src/lib.rs`

**Interfaces:**
- Consumes: `shinri_bv::{BitLit, Blaster}`; `shinri_core::{Context, TermId, TermNode, Op, ConstVal}`; `ctx.fp_widths`, `ctx.fp_const_value` (foundation).
- Produces:
  - `struct FpBlaster { pub b: Blaster, cache: FxHashMap<TermId, Vec<BitLit>>, var_bits: FxHashMap<TermId, Vec<BitLit>> }`.
  - `impl FpBlaster { fn new() -> Self; fn blast_word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit>; fn exported_var_bits(&self) -> FxHashMap<TermId, Vec<BitLit>>; }`.
  - `struct Unpacked { sign: BitLit, exp: Vec<BitLit>, sig: Vec<BitLit>, is_nan: BitLit, is_inf: BitLit, is_zero: BitLit }`.
  - `fn unpack::unpack(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Unpacked`.
  - `fn pack::pack(b: &mut Blaster, u: &Unpacked, eb: u32, sb: u32) -> Vec<BitLit>` (NaN-canonicalizing).

- [ ] **Step 1: Write the failing test**

Append a test module to `crates/shinri-fp/src/lib.rs`:

```rust
#[cfg(test)]
mod blast_tests {
    use super::*;
    use shinri_core::{Context, Op};
    use shinri_num::Integer;

    #[test]
    fn blast_const_and_var_words_have_width_w() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        // a float constant (+zero) and a float variable
        let z = ctx.mk_fp_const(8, 24, Integer::zero());
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();

        let mut fb = FpBlaster::new();
        let zb = fb.blast_word(&ctx, z);
        let xb = fb.blast_word(&ctx, x);
        assert_eq!(zb.len(), 32, "Float32 word is W=eb+sb=32 bits");
        assert_eq!(xb.len(), 32);
        // +zero constant: every bit is the pinned-false constant (var 0, pos=false).
        for bit in &zb {
            assert_eq!(bit.var, 0, "constant bits use the pinned var 0");
            assert!(!bit.pos, "+zero bits are all false");
        }
        // the variable is exported for model extraction
        let vb = fb.exported_var_bits();
        assert!(vb.contains_key(&x));
        assert_eq!(vb[&x].len(), 32);
        assert!(!vb.contains_key(&z), "constants are not exported as variables");
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp blast_const_and_var_words_have_width_w`
Expected: FAIL — `FpBlaster` undefined.

- [ ] **Step 3: Implement `FpBlaster` in `lib.rs`**

Add to `crates/shinri-fp/src/lib.rs` (and declare the new modules):

```rust
pub mod pack;
pub mod unpack;

use rustc_hash::FxHashMap;
use shinri_bv::{BitLit, Blaster};
use shinri_core::{ConstVal, Context, Op, TermId, TermNode};

/// FP-side blaster: wraps a `shinri_bv::Blaster` (used purely as a gate/clause
/// factory) with its own word cache and variable-bit map, since the Blaster's
/// internal cache is private to shinri-bv.
pub struct FpBlaster {
    pub b: Blaster,
    cache: FxHashMap<TermId, Vec<BitLit>>,
    var_bits: FxHashMap<TermId, Vec<BitLit>>,
}

impl FpBlaster {
    pub fn new() -> Self {
        FpBlaster { b: Blaster::new(), cache: FxHashMap::default(), var_bits: FxHashMap::default() }
    }

    /// Blast an FP-sorted term to its W=eb+sb bit word (LSB→MSB), memoized.
    /// Slice 1 handles FP constants and nullary FP variables; FP operator nodes
    /// (abs/neg) are added in Task 5 via `structural`.
    pub fn blast_word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        if let Some(v) = self.cache.get(&t) {
            return v.clone();
        }
        let result = match ctx.term_node(t).clone() {
            TermNode::Const { val: ConstVal::Float(_), .. } => {
                let (eb, sb, bits) = ctx.fp_const_value(t).expect("FP const");
                let w = eb + sb;
                let two = shinri_num::Integer::from(2u64);
                let mut remaining = bits.clone();
                (0..w).map(|_| {
                    let (q, r) = remaining.div_rem(&two);
                    remaining = q;
                    if r.is_zero() { self.b.zero() } else { self.b.one() }
                }).collect()
            }
            TermNode::App { op: Op::Uninterpreted(_), args, sort } => {
                debug_assert!(ctx.children(args).is_empty(), "non-nullary FP fn out of scope");
                let (eb, sb) = ctx.fp_widths(sort).expect("FP-sorted variable");
                let bits: Vec<BitLit> = (0..(eb + sb)).map(|_| self.b.fresh()).collect();
                self.var_bits.insert(t, bits.clone());
                bits
            }
            other => {
                // Task 5 extends this with abs/neg. Until then, unreachable for slice-1 words.
                let _ = other;
                unreachable!("blast_word: unsupported FP word node (slice 1)");
            }
        };
        self.cache.insert(t, result.clone());
        result
    }

    /// Bits cached for every FP *variable* term (for model extraction).
    pub fn exported_var_bits(&self) -> FxHashMap<TermId, Vec<BitLit>> {
        self.var_bits.clone()
    }
}

impl Default for FpBlaster {
    fn default() -> Self { Self::new() }
}
```

- [ ] **Step 4: Implement `unpack.rs`**

Create `crates/shinri-fp/src/unpack.rs`:

```rust
//! Decompose an FP bit word into sign / exponent / explicit significand / flags.

use shinri_bv::{BitLit, Blaster};

/// Unpacked FP operand. `sig` is the (sb-1)-bit trailing significand (LSB→MSB);
/// the hidden bit is implicit (1 for normal, 0 for subnormal) and recomputed by
/// consumers as needed. Flags are derived from the exponent/significand fields.
pub struct Unpacked {
    pub sign: BitLit,
    pub exp: Vec<BitLit>,   // eb bits, LSB→MSB
    pub sig: Vec<BitLit>,   // sb-1 bits, LSB→MSB
    pub is_nan: BitLit,
    pub is_inf: BitLit,
    pub is_zero: BitLit,
}

/// `bits` is the W=eb+sb word, LSB→MSB.
pub fn unpack(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Unpacked {
    let w = (eb + sb) as usize;
    debug_assert_eq!(bits.len(), w);
    let sign = bits[w - 1];
    let exp: Vec<BitLit> = bits[(sb as usize - 1)..(sb as usize - 1 + eb as usize)].to_vec();
    let sig: Vec<BitLit> = bits[0..(sb as usize - 1)].to_vec();

    // exp_all_ones = AND of all exp bits ; exp_all_zero = AND of all (NOT exp bits)
    let and_all = |b: &mut Blaster, lits: &[BitLit]| -> BitLit {
        let mut acc = b.one();
        for &l in lits { acc = b.and2(acc, l); }
        acc
    };
    let nor_all = |b: &mut Blaster, lits: &[BitLit]| -> BitLit {
        // true iff all lits are false
        let mut acc = b.one();
        for &l in lits { let nl = b.not1(l); acc = b.and2(acc, nl); }
        acc
    };
    let exp_all_ones = and_all(b, &exp);
    let exp_all_zero = nor_all(b, &exp);
    let sig_all_zero = nor_all(b, &sig);
    let sig_nonzero = b.not1(sig_all_zero);

    let is_inf = b.and2(exp_all_ones, sig_all_zero);
    let is_nan = b.and2(exp_all_ones, sig_nonzero);
    let is_zero = b.and2(exp_all_zero, sig_all_zero);

    Unpacked { sign, exp, sig, is_nan, is_inf, is_zero }
}
```

- [ ] **Step 5: Implement `pack.rs`**

Create `crates/shinri-fp/src/pack.rs`:

```rust
//! Reassemble an FP bit word from an Unpacked form, canonicalizing NaN.

use crate::unpack::Unpacked;
use shinri_bv::{BitLit, Blaster};

/// Pack sign|exp|sig back to W=eb+sb bits (LSB→MSB). If `u.is_nan` is set, emit
/// the canonical quiet NaN pattern (sign 0, exp all ones, sig MSB = 1, rest 0).
pub fn pack(b: &mut Blaster, u: &Unpacked, eb: u32, sb: u32) -> Vec<BitLit> {
    debug_assert_eq!(u.exp.len(), eb as usize);
    debug_assert_eq!(u.sig.len(), sb as usize - 1);
    let one = b.one();
    let zero = b.zero();

    // Canonical NaN fields.
    // exp: all ones ; sig: only MSB set ; sign: 0.
    let mut out: Vec<BitLit> = Vec::with_capacity((eb + sb) as usize);
    // trailing significand bits [0 .. sb-1)
    for i in 0..(sb as usize - 1) {
        // canonical NaN sig: MSB (index sb-2) = 1, others 0.
        let canon = if i == (sb as usize - 2) { one } else { zero };
        out.push(b.mux2(u.is_nan, canon, u.sig[i]));
    }
    // exponent bits
    for i in 0..(eb as usize) {
        out.push(b.mux2(u.is_nan, one, u.exp[i]));
    }
    // sign bit: 0 for canonical NaN
    out.push(b.mux2(u.is_nan, zero, u.sign));
    out
}
```

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo test -p shinri-fp blast_const_and_var_words_have_width_w`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-fp/src/lib.rs crates/shinri-fp/src/unpack.rs crates/shinri-fp/src/pack.rs
git commit -m "feat(fp): FpBlaster word substrate + unpack/pack gadgets"
```

---

### Task 4: Classification gadgets (`blast/classify.rs`)

**Files:**
- Create: `crates/shinri-fp/src/blast/mod.rs`
- Create: `crates/shinri-fp/src/blast/classify.rs`
- Modify: `crates/shinri-fp/src/lib.rs` (add `pub mod blast;`)
- Test: `crates/shinri-fp/src/blast/classify.rs`

**Interfaces:**
- Consumes: `Blaster` primitives; `crate::unpack::{unpack, Unpacked}`.
- Produces (in `crate::blast::classify`):
  - `fn is_nan/is_inf/is_zero/is_normal/is_subnormal/is_negative/is_positive(b: &mut Blaster, u: &Unpacked) -> BitLit`.

**Test method (shared by Tasks 4–6):** build a `Blaster`, blast the gadget over a **constant** bit word (each bit is `b.one()` or `b.zero()`), solve the CNF with a `NoTheory` SAT solver, read the output literal's value, and compare to the reference oracle. This is the pattern from `shinri-bv`'s `lower_const_atom_no_var_bits` test.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-fp/src/blast/classify.rs` with the module doc and a test module:

```rust
//! Bit-blasted FP classification predicates over an Unpacked operand.

use shinri_bv::{BitLit, Blaster};
use crate::unpack::Unpacked;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{decode, ref_is_nan, ref_is_inf, ref_is_zero, ref_is_normal,
                           ref_is_subnormal, ref_is_negative, ref_is_positive};
    use crate::unpack::unpack;
    use shinri_num::Integer;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    /// Build constant bits (LSB→MSB) for `value` of width W=eb+sb in a Blaster.
    fn const_bits(b: &Blaster, eb: u32, sb: u32, value: u64) -> Vec<BitLit> {
        let w = eb + sb;
        (0..w).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    }

    /// Solve the Blaster's CNF and return the boolean value of `lit`.
    fn eval(b: Blaster, lit: BitLit) -> bool {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars { s.new_var(); }
        for clause in &cnf.clauses {
            let lits: Vec<Lit> = clause.iter().map(|bl| Lit::new(Var::new(bl.var), bl.pos)).collect();
            s.add_clause(&lits);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let raw = s.value_of(Var::new(lit.var)).unwrap();
        if lit.pos { raw } else { !raw }
    }

    fn check_all(eb: u32, sb: u32, value: u64) {
        let cls = decode(eb, sb, &Integer::from(value));
        // each predicate gets its own fresh Blaster (independent solve)
        macro_rules! one {
            ($gadget:path, $reference:expr) => {{
                let mut b = Blaster::new();
                let bits = const_bits(&b, eb, sb, value);
                let u = unpack(&mut b, &bits, eb, sb);
                let lit = $gadget(&mut b, &u);
                assert_eq!(eval(b, lit), $reference, "value={:#x} gadget={}", value, stringify!($gadget));
            }};
        }
        one!(is_nan, ref_is_nan(&cls));
        one!(is_inf, ref_is_inf(&cls));
        one!(is_zero, ref_is_zero(&cls));
        one!(is_normal, ref_is_normal(&cls));
        one!(is_subnormal, ref_is_subnormal(&cls));
        one!(is_negative, ref_is_negative(&cls));
        one!(is_positive, ref_is_positive(&cls));
    }

    #[test]
    fn classify_float32_representatives() {
        let (eb, sb) = (8, 24);
        for v in [0x0000_0000u64, 0x8000_0000, 0x7F80_0000, 0xFF80_0000, 0x7FC0_0000,
                  0x3F80_0000, 0xBF80_0000, 0x0000_0001, 0x8000_0001] {
            check_all(eb, sb, v);
        }
    }

    #[test]
    fn classify_tiny_format_exhaustive() {
        // (3,5): W=8 bits, all 256 patterns, against the reference.
        let (eb, sb) = (3, 5);
        for v in 0u64..256 { check_all(eb, sb, v); }
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp classify`
Expected: FAIL — `is_nan` etc. not defined.

- [ ] **Step 3: Implement the gadgets**

Add above the test module in `crates/shinri-fp/src/blast/classify.rs`:

```rust
pub fn is_nan(_b: &mut Blaster, u: &Unpacked) -> BitLit { u.is_nan }
pub fn is_inf(_b: &mut Blaster, u: &Unpacked) -> BitLit { u.is_inf }
pub fn is_zero(_b: &mut Blaster, u: &Unpacked) -> BitLit { u.is_zero }

/// exp is neither all-zero nor all-ones ⇒ normal. Equivalent to
/// NOT(is_nan OR is_inf OR is_zero OR is_subnormal); compute directly from flags.
pub fn is_normal(b: &mut Blaster, u: &Unpacked) -> BitLit {
    // normal = NOT exp_all_zero AND NOT exp_all_ones.
    // Reconstruct exp_all_ones / exp_all_zero from u.exp.
    let mut all_ones = b.one();
    for &e in &u.exp { all_ones = b.and2(all_ones, e); }
    let mut all_zero = b.one();
    for &e in &u.exp { let ne = b.not1(e); all_zero = b.and2(all_zero, ne); }
    let not_ones = b.not1(all_ones);
    let not_zero = b.not1(all_zero);
    b.and2(not_ones, not_zero)
}

/// subnormal = exp_all_zero AND sig != 0.
pub fn is_subnormal(b: &mut Blaster, u: &Unpacked) -> BitLit {
    let mut all_zero = b.one();
    for &e in &u.exp { let ne = b.not1(e); all_zero = b.and2(all_zero, ne); }
    let mut sig_all_zero = b.one();
    for &s in &u.sig { let ns = b.not1(s); sig_all_zero = b.and2(sig_all_zero, ns); }
    let sig_nonzero = b.not1(sig_all_zero);
    b.and2(all_zero, sig_nonzero)
}

/// isNegative: sign set AND NOT NaN AND NOT zero (SMT-LIB excludes zeros & NaN).
pub fn is_negative(b: &mut Blaster, u: &Unpacked) -> BitLit {
    let not_nan = b.not1(u.is_nan);
    let not_zero = b.not1(u.is_zero);
    let t = b.and2(u.sign, not_nan);
    b.and2(t, not_zero)
}

/// isPositive: sign clear AND NOT NaN AND NOT zero.
pub fn is_positive(b: &mut Blaster, u: &Unpacked) -> BitLit {
    let not_sign = b.not1(u.sign);
    let not_nan = b.not1(u.is_nan);
    let not_zero = b.not1(u.is_zero);
    let t = b.and2(not_sign, not_nan);
    b.and2(t, not_zero)
}
```

Create `crates/shinri-fp/src/blast/mod.rs`:

```rust
pub mod classify;
pub mod compare;
pub mod structural;
```

> `compare` and `structural` modules are created in Tasks 5; to keep this task compiling on its own, create empty stub files now: `crates/shinri-fp/src/blast/compare.rs` and `crates/shinri-fp/src/blast/structural.rs` each containing only `//! (filled in Task 5)`. Task 5 replaces them.

Add `pub mod blast;` to `crates/shinri-fp/src/lib.rs`.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp classify`
Expected: PASS (both representative and the 256-pattern exhaustive `(3,5)` test).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/blast/ crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): classification predicate gadgets (exhaustive on tiny format)"
```

---

### Task 5: Structural (`abs`/`neg`) and compare (`fp.eq`, core `=`) gadgets

**Files:**
- Modify: `crates/shinri-fp/src/blast/structural.rs`
- Modify: `crates/shinri-fp/src/blast/compare.rs`
- Test: `crates/shinri-fp/src/blast/compare.rs`

**Interfaces:**
- Consumes: `Blaster` primitives; `crate::unpack::{unpack, Unpacked}`.
- Produces:
  - `fn structural::abs(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit>` (clear sign bit).
  - `fn structural::neg(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit>` (flip sign bit).
  - `fn compare::fp_eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit`.
  - `fn compare::core_eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit`.

- [ ] **Step 1: Write the failing test**

Replace `crates/shinri-fp/src/blast/compare.rs` with the module doc + test module:

```rust
//! fp.eq and NaN-aware core `=` over two FP bit words.

use shinri_bv::{BitLit, Blaster};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::structural::{abs, neg};
    use crate::reference::{decode, ref_abs, ref_core_eq, ref_fp_eq, ref_neg};
    use shinri_num::Integer;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn const_bits(b: &Blaster, eb: u32, sb: u32, value: u64) -> Vec<BitLit> {
        (0..(eb + sb)).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    }
    fn eval_lit(b: Blaster, lit: BitLit) -> bool {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars { s.new_var(); }
        for c in &cnf.clauses {
            let ls: Vec<Lit> = c.iter().map(|bl| Lit::new(Var::new(bl.var), bl.pos)).collect();
            s.add_clause(&ls);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let raw = s.value_of(Var::new(lit.var)).unwrap();
        if lit.pos { raw } else { !raw }
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
            if (if bl.pos { raw } else { !raw }) { v |= 1 << i; }
        }
        v
    }

    #[test]
    fn abs_neg_words_match_reference() {
        let (eb, sb) = (8, 24);
        for v in [0x3F80_0000u64, 0xBF80_0000, 0x7FC0_0000, 0x8000_0000] {
            let mut b = Blaster::new();
            let bits = const_bits(&b, eb, sb, v);
            let a = abs(&mut b, &bits, eb, sb);
            assert_eq!(eval_word(b, &a), ref_abs(eb, sb, &Integer::from(v)).to_i128().unwrap() as u64);
            let mut b2 = Blaster::new();
            let bits2 = const_bits(&b2, eb, sb, v);
            let n = neg(&mut b2, &bits2, eb, sb);
            assert_eq!(eval_word(b2, &n), ref_neg(eb, sb, &Integer::from(v)).to_i128().unwrap() as u64);
        }
    }

    #[test]
    fn fp_eq_and_core_eq_match_reference() {
        let (eb, sb) = (8, 24);
        let cases = [
            (0x0000_0000u64, 0x8000_0000u64), // +0 vs -0
            (0x7FC0_0000, 0x7FC0_0000),       // NaN vs NaN
            (0x7F80_0001, 0x7FC0_0000),       // sNaN vs qNaN (both NaN)
            (0x3F80_0000, 0x3F80_0000),       // 1.0 vs 1.0
            (0x3F80_0000, 0x4000_0000),       // 1.0 vs 2.0
        ];
        for (x, y) in cases {
            let mut b = Blaster::new();
            let xb = const_bits(&b, eb, sb, x);
            let yb = const_bits(&b, eb, sb, y);
            let lit = fp_eq(&mut b, &xb, &yb, eb, sb);
            let want = ref_fp_eq(&decode(eb, sb, &Integer::from(x)), &decode(eb, sb, &Integer::from(y)));
            assert_eq!(eval_lit(b, lit), want, "fp_eq({x:#x},{y:#x})");

            let mut b2 = Blaster::new();
            let xb2 = const_bits(&b2, eb, sb, x);
            let yb2 = const_bits(&b2, eb, sb, y);
            let lit2 = core_eq(&mut b2, &xb2, &yb2, eb, sb);
            let want2 = ref_core_eq(eb, sb, &Integer::from(x), &Integer::from(y));
            assert_eq!(eval_lit(b2, lit2), want2, "core_eq({x:#x},{y:#x})");
        }
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp compare`
Expected: FAIL — `abs`/`neg`/`fp_eq`/`core_eq` undefined.

- [ ] **Step 3: Implement `structural.rs`**

Replace `crates/shinri-fp/src/blast/structural.rs`:

```rust
//! Sign-only FP word ops: fp.abs (clear sign), fp.neg (flip sign).

use shinri_bv::{BitLit, Blaster};

pub fn abs(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    debug_assert_eq!(bits.len(), w);
    let mut out = bits.to_vec();
    out[w - 1] = b.zero(); // sign bit := 0
    out
}

pub fn neg(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    debug_assert_eq!(bits.len(), w);
    let mut out = bits.to_vec();
    out[w - 1] = b.not1(bits[w - 1]); // sign bit := NOT sign
    out
}
```

- [ ] **Step 4: Implement `compare.rs` gadgets**

Add above the test module in `crates/shinri-fp/src/blast/compare.rs`:

```rust
use crate::unpack::unpack;

/// Bitwise equality of two equal-length words.
fn bits_eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    debug_assert_eq!(x.len(), y.len());
    let mut acc = b.one();
    for i in 0..x.len() {
        let xn = b.xor2(x[i], y[i]);   // 1 if differ
        let same = b.not1(xn);
        acc = b.and2(acc, same);
    }
    acc
}

/// IEEE `fp.eq`: false if either is NaN; +0 == -0; else bit-equal among finite/inf.
/// Since +0 and -0 differ only in the sign bit and all-other-bits-zero, comparing
/// the magnitude (all bits except sign) handles zeros, BUT two different non-zero
/// values with equal magnitude and opposite sign (e.g. +1 vs -1) must compare
/// UNEQUAL. So: equal iff (both zero) OR (not NaN AND full-bit-equal).
pub fn fp_eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let neither_nan = {
        let nx = b.not1(ux.is_nan);
        let ny = b.not1(uy.is_nan);
        b.and2(nx, ny)
    };
    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let full_eq = bits_eq(b, x, y);
    let finite_eq = b.and2(neither_nan, full_eq);
    // (both_zero) OR (neither_nan AND full_eq); both_zero already implies neither_nan.
    let eq = b.or2(both_zero, finite_eq);
    // ensure NaN forces false even if full_eq held (NaN==NaN bit-equal): mask by neither_nan.
    b.and2(eq, neither_nan)
}

/// Theory core `=`: NaN == NaN (any NaN payloads), +0 != -0, else bit-equal.
pub fn core_eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let both_nan = b.and2(ux.is_nan, uy.is_nan);
    let neither_nan = {
        let nx = b.not1(ux.is_nan);
        let ny = b.not1(uy.is_nan);
        b.and2(nx, ny)
    };
    let full_eq = bits_eq(b, x, y);
    let finite_eq = b.and2(neither_nan, full_eq);
    b.or2(both_nan, finite_eq)
}
```

> Note the `fp_eq` masking: `both_zero` implies neither operand is NaN, so the final `AND neither_nan` keeps zeros equal while forcing any NaN pair to false. Verify against the test's NaN-vs-NaN case (must be `false` under `fp_eq`, `true` under `core_eq`).

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-fp compare`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/blast/structural.rs crates/shinri-fp/src/blast/compare.rs
git commit -m "feat(fp): abs/neg word ops + fp.eq and NaN-aware core = gadgets"
```

---

### Task 6: `lower()` entry + FP atom dispatch + `model.rs`

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs`
- Create: `crates/shinri-fp/src/model.rs`
- Test: `crates/shinri-fp/src/lib.rs`

**Interfaces:**
- Consumes: `FpBlaster` (Task 3); classify/compare/structural gadgets (Tasks 4–5); `shinri_bv::Lowered`, `shinri_bv::BitLit`.
- Produces:
  - `fn lower(ctx: &mut Context, fp_atoms: &[TermId]) -> shinri_bv::Lowered` — keyed by the **original** atom TermId (matching `shinri_bv::lower`'s contract).
  - `FpBlaster::blast_word` extended to handle `FpAbs`/`FpNeg` operator nodes.
  - `FpBlaster::blast_atom(&mut self, ctx, t) -> BitLit` dispatching the 7 classifications, `FpEq`, and core `=`/`distinct` over Float operands.
  - `crate::model::pack` re-export.

- [ ] **Step 1: Write the failing test**

Append to the test module in `crates/shinri-fp/src/lib.rs`:

```rust
#[cfg(test)]
mod lower_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

    #[test]
    fn lower_isnan_atom_keys_and_vars() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();

        let lo = lower(&mut ctx, &[isnan]);
        assert!(lo.atom_lit.contains_key(&isnan), "keyed by original atom TermId");
        assert!(lo.var_bits.contains_key(&x), "x exported for model extraction");
        assert_eq!(lo.var_bits[&x].len(), 32);
        assert!(lo.cnf.num_vars >= 1);
    }

    #[test]
    fn lower_core_eq_over_floats_is_an_atom() {
        let mut ctx = Context::new();
        let f32 = ctx.fp_sort(8, 24);
        let xf = ctx.declare_fun("x", &[], f32);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let pz = ctx.mk_fp_const(8, 24, Integer::zero());
        let eq = ctx.mk_eq(x, pz).unwrap();
        let lo = lower(&mut ctx, &[eq]);
        assert!(lo.atom_lit.contains_key(&eq), "FP core = must be surrogated");
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp lower_`
Expected: FAIL — `lower` undefined.

- [ ] **Step 3: Extend `blast_word` for `FpAbs`/`FpNeg`**

In `crates/shinri-fp/src/lib.rs`, replace the `other => { … unreachable!(…) }` arm of `FpBlaster::blast_word` with:

```rust
            TermNode::App { op: Op::Builtin(op), args, sort } => {
                use shinri_core::BuiltinOp::*;
                let (eb, sb) = ctx.fp_widths(sort).expect("FP-sorted op result");
                let kids = ctx.children(args).to_vec();
                match op {
                    FpAbs => {
                        let w = self.blast_word(ctx, kids[0]);
                        crate::blast::structural::abs(&mut self.b, &w, eb, sb)
                    }
                    FpNeg => {
                        let w = self.blast_word(ctx, kids[0]);
                        crate::blast::structural::neg(&mut self.b, &w, eb, sb)
                    }
                    other => unreachable!("blast_word: FP op {other:?} is out of slice-1 scope"),
                }
            }
            other => unreachable!("blast_word: unsupported FP word node {other:?} (slice 1)"),
```

- [ ] **Step 4: Add `blast_atom` and `lower`**

Add to `impl FpBlaster` in `crates/shinri-fp/src/lib.rs`:

```rust
    /// Blast a Bool-sorted FP atom to a single BitLit.
    pub fn blast_atom(&mut self, ctx: &Context, t: TermId) -> BitLit {
        use shinri_core::BuiltinOp::*;
        let node = ctx.term_node(t).clone();
        let TermNode::App { op, args, .. } = node else {
            unreachable!("FP atom must be an application");
        };
        let kids = ctx.children(args).to_vec();
        match op {
            Op::Builtin(Eq) => {
                // core = over Float operands (NaN-aware).
                let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
                let x = self.blast_word(ctx, kids[0]);
                let y = self.blast_word(ctx, kids[1]);
                crate::blast::compare::core_eq(&mut self.b, &x, &y, eb, sb)
            }
            Op::Builtin(Distinct) => {
                let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
                let x = self.blast_word(ctx, kids[0]);
                let y = self.blast_word(ctx, kids[1]);
                let eq = crate::blast::compare::core_eq(&mut self.b, &x, &y, eb, sb);
                self.b.not1(eq)
            }
            Op::Builtin(FpEq) => {
                let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
                let x = self.blast_word(ctx, kids[0]);
                let y = self.blast_word(ctx, kids[1]);
                crate::blast::compare::fp_eq(&mut self.b, &x, &y, eb, sb)
            }
            Op::Builtin(classify @ (FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite
                                    | FpIsNaN | FpIsNegative | FpIsPositive)) => {
                let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operand");
                let w = self.blast_word(ctx, kids[0]);
                let u = crate::unpack::unpack(&mut self.b, &w, eb, sb);
                use crate::blast::classify as c;
                match classify {
                    FpIsNormal => c::is_normal(&mut self.b, &u),
                    FpIsSubnormal => c::is_subnormal(&mut self.b, &u),
                    FpIsZero => c::is_zero(&mut self.b, &u),
                    FpIsInfinite => c::is_inf(&mut self.b, &u),
                    FpIsNaN => c::is_nan(&mut self.b, &u),
                    FpIsNegative => c::is_negative(&mut self.b, &u),
                    FpIsPositive => c::is_positive(&mut self.b, &u),
                    _ => unreachable!(),
                }
            }
            other => unreachable!("blast_atom: FP atom {other:?} out of slice-1 scope"),
        }
    }
```

Add the free `lower` function and `pub mod model;` at module scope in `crates/shinri-fp/src/lib.rs`:

```rust
pub mod model;

/// Blast all `fp_atoms` via one FpBlaster and return a `shinri_bv::Lowered`
/// (reused so the solver's `replay_bv_cnf` applies unchanged). `atom_lit` is
/// keyed by the ORIGINAL atom TermId.
pub fn lower(ctx: &mut Context, fp_atoms: &[TermId]) -> shinri_bv::Lowered {
    let mut fb = FpBlaster::new();
    let mut atom_lit: FxHashMap<TermId, BitLit> = FxHashMap::default();
    for &atom in fp_atoms {
        let lit = fb.blast_atom(ctx, atom);
        atom_lit.insert(atom, lit);
    }
    let var_bits = fb.exported_var_bits();
    shinri_bv::Lowered { cnf: fb.b.finish(), atom_lit, var_bits }
}
```

> `shinri_bv::Lowered` fields (`cnf`, `atom_lit`, `var_bits`) are `pub` (see `crates/shinri-bv/src/lib.rs`), so `shinri-fp` can construct it directly. No rewrite pass in slice 1 (constant folding is Plan 2); atoms blast as-is.

- [ ] **Step 5: Create `model.rs`**

Create `crates/shinri-fp/src/model.rs`:

```rust
//! FP model reconstruction. Slice 1 reuses the BV bit-packer: an FP value is
//! the W=eb+sb unsigned bit pattern read from the SAT assignment (LSB→MSB).

pub use shinri_bv::model::pack;
```

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo test -p shinri-fp lower_`
Expected: PASS. Then run the whole crate: `cargo test -p shinri-fp` — all gadget + oracle + lower tests pass.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-fp/src/lib.rs crates/shinri-fp/src/model.rs
git commit -m "feat(fp): lower() entry + FP atom/word dispatch + model packer"
```

---

### Task 7: Solver stage `fp_stage.rs` (detect / collect / fence)

**Files:**
- Modify: `crates/shinri-solver/Cargo.toml` (add `shinri-fp` dependency)
- Create: `crates/shinri-solver/src/fp_stage.rs`
- Modify: `crates/shinri-solver/src/lib.rs` (`mod fp_stage;`)
- Test: `crates/shinri-solver/src/fp_stage.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode, Lit, Var}`.
- Produces:
  - `fn solver_uses_fp(ctx, assertions: &[TermId]) -> bool`.
  - `fn collect_fp_atoms(ctx, assertions: &[TermId]) -> Vec<TermId>` (FP predicates + Eq/Distinct over Float operands).
  - `fn has_non_fp_theory_atom(ctx, assertions, fp_atoms: &[TermId]) -> bool`.
  - `struct FpSurrogates { atom_to_lit: FxHashMap<TermId, Lit>, var_bits: FxHashMap<TermId, Vec<Var>> }`.

- [ ] **Step 1: Add the dependency**

In `crates/shinri-solver/Cargo.toml` `[dependencies]`, add: `shinri-fp = { path = "../shinri-fp" }`.

- [ ] **Step 2: Write the failing test**

Create `crates/shinri-solver/src/fp_stage.rs` with the test module first:

```rust
//! FP lowering stage: detect QF_FP queries, collect FP atoms, enforce the
//! mixed-theory fence. Mirrors bv_stage.rs. FP gets its own Blaster (QF_BVFP
//! unification is a later plan), so BV atoms count as non-FP and trigger the fence.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Lit, Op, SortNode, TermId, TermNode, Var};

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Op;
    use shinri_num::Integer;

    fn fp_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.fp_sort(8, 24);
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn detects_fp_and_collects_eq_and_predicate() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        let pz = ctx.mk_fp_const(8, 24, Integer::zero());
        let eq = ctx.mk_eq(x, pz).unwrap();
        let assertions = vec![isnan, eq];
        assert!(solver_uses_fp(&ctx, &assertions));
        let atoms = collect_fp_atoms(&ctx, &assertions);
        assert!(atoms.contains(&isnan), "FP predicate collected");
        assert!(atoms.contains(&eq), "FP equality collected (soundness)");
        assert_eq!(atoms.len(), 2);
        assert!(!has_non_fp_theory_atom(&ctx, &assertions, &atoms));
    }

    #[test]
    fn fp_mixed_with_bv_is_fenced() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
        // a BV atom alongside FP
        let bvs = ctx.bv_sort(8);
        let bf = ctx.declare_fun("b", &[], bvs);
        let bvar = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let one = ctx.mk_bv_const(8, Integer::from(1u64));
        let ult = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[bvar, one]).unwrap();
        let assertions = vec![isnan, ult];
        let atoms = collect_fp_atoms(&ctx, &assertions);
        assert!(atoms.contains(&isnan));
        assert!(has_non_fp_theory_atom(&ctx, &assertions, &atoms),
                "BV atom alongside FP must trigger the fence");
    }
}
```

- [ ] **Step 3: Run test to verify it fails**

Run: `cargo test -p shinri-solver fp_stage`
Expected: FAIL — `solver_uses_fp` etc. undefined / `mod fp_stage` not declared.

- [ ] **Step 4: Implement the stage**

Add `mod fp_stage;` near the other `mod bv_stage;` declarations in `crates/shinri-solver/src/lib.rs`.

Add above the test module in `crates/shinri-solver/src/fp_stage.rs`:

```rust
/// Surrogate maps produced by lowering FP atoms (parallel to `BvSurrogates`).
pub struct FpSurrogates {
    pub atom_to_lit: FxHashMap<TermId, Lit>,
    pub var_bits: FxHashMap<TermId, Vec<Var>>,
}

fn is_fp_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::Float(_, _))
}

/// True if `op` is any FP builtin (word op, predicate, classification, or conversion).
fn is_fp_op(op: &Op) -> bool {
    use BuiltinOp::*;
    matches!(op, Op::Builtin(
        FpAbs | FpNeg | FpAdd | FpSub | FpMul | FpDiv | FpFma | FpSqrt | FpRem
        | FpRoundToIntegral | FpMin | FpMax | FpLeq | FpLt | FpGeq | FpGt | FpEq
        | FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite | FpIsNaN
        | FpIsNegative | FpIsPositive | FpFromBits
        | ToFp { .. } | ToFpUnsigned { .. } | FpToUbv(_) | FpToSbv(_) | FpToReal
    ))
}

/// FP PREDICATES (Bool-sorted FP atoms): comparisons + classifications.
fn is_fp_predicate(op: &Op) -> bool {
    use BuiltinOp::*;
    matches!(op, Op::Builtin(
        FpLeq | FpLt | FpGeq | FpGt | FpEq
        | FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite | FpIsNaN
        | FpIsNegative | FpIsPositive
    ))
}

/// True if any subterm has a Float sort or an FP builtin op.
pub fn solver_uses_fp(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return false; }
        if is_fp_sorted(ctx, t) { return true; }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                if is_fp_op(op) { return true; }
                ctx.children(*args).to_vec().into_iter().any(|c| walk(ctx, c, seen))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a, &mut seen))
}

/// Collect Bool-sorted FP atoms: FP predicates, plus Eq/Distinct over Float operands.
/// SOUNDNESS-CRITICAL: FP (dis)equalities ARE included (else they route to EUF).
pub fn collect_fp_atoms(ctx: &Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut out: Vec<TermId> = Vec::new();
    let mut in_set: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, out: &mut Vec<TermId>,
            in_set: &mut rustc_hash::FxHashSet<TermId>,
            visited: &mut rustc_hash::FxHashSet<TermId>) {
        if !visited.insert(t) { return; }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            let is_atom = match op {
                _ if is_fp_predicate(op) => true,
                Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) =>
                    kids.iter().any(|&k| is_fp_sorted(ctx, k)),
                _ => false,
            };
            if is_atom && in_set.insert(t) { out.push(t); return; }
            for k in kids { walk(ctx, k, out, in_set, visited); }
        }
    }
    for &a in assertions { walk(ctx, a, &mut out, &mut in_set, &mut visited); }
    out
}

/// Mixed-theory fence (conservative). True if any Bool-sorted atom outside the
/// FP set is not pure Boolean structure — including BV atoms (BVFP waits for
/// Plan 4) and arith/EUF/array atoms. When true, the caller returns Unknown.
pub fn has_non_fp_theory_atom(ctx: &Context, assertions: &[TermId], fp_atoms: &[TermId]) -> bool {
    let fp_set: rustc_hash::FxHashSet<TermId> = fp_atoms.iter().copied().collect();
    let mut visited: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, fp_set: &rustc_hash::FxHashSet<TermId>,
            visited: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if fp_set.contains(&t) { return false; }
        if !visited.insert(t) { return false; }
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                let kids: Vec<TermId> = ctx.children(*args).to_vec();
                let is_bool_structure = matches!(op, Op::Builtin(
                    BuiltinOp::Not | BuiltinOp::And | BuiltinOp::Or
                    | BuiltinOp::Implies | BuiltinOp::Xor | BuiltinOp::Ite));
                let is_bool_eq = matches!(op, Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct))
                    && kids.first().is_some_and(|&k| ctx.sort_of(k) == ctx.bool_sort());
                if is_bool_structure || is_bool_eq {
                    return kids.iter().any(|&k| walk(ctx, k, fp_set, visited));
                }
                if ctx.sort_of(t) == ctx.bool_sort() {
                    // Bool-sorted, not an FP atom, not Boolean structure → fence.
                    return true;
                }
                kids.iter().any(|&k| walk(ctx, k, fp_set, visited))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a, &fp_set, &mut visited))
}
```

> `SortNode::Float(_, _)` and the FP `BuiltinOp` variants are from the landed foundation (`crates/shinri-core/src/sort.rs`, `term.rs`). Confirm the variant spellings against `term.rs` if the compiler complains.

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-solver fp_stage`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/Cargo.toml crates/shinri-solver/src/fp_stage.rs crates/shinri-solver/src/lib.rs
git commit -m "feat(solver): fp_stage detect/collect/fence (FP-private, BVFP fenced)"
```

---

### Task 8: `ModelVal::Float` + solver model rendering

**Files:**
- Modify: `crates/shinri-theory/src/types.rs` (add `ModelVal::Float`)
- Modify: `crates/shinri-solver/src/model.rs` (render it)
- Test: `crates/shinri-solver/src/model.rs`

**Interfaces:**
- Produces: `ModelVal::Float { eb: u32, sb: u32, bits: shinri_core::Integer }`; `format_modelval` renders it as `(fp #b<sign> #b<exp> #b<trailing-sig>)`.

- [ ] **Step 1: Write the failing test**

Add to the test module in `crates/shinri-solver/src/model.rs`:

```rust
#[test]
fn format_float_modelval_as_fp_triple() {
    use shinri_theory::types::ModelVal;
    // Float32 +zero: sign 0, exp 00000000, sig 0*23
    let pz = ModelVal::Float { eb: 8, sb: 24, bits: shinri_num::Integer::from(0u64) };
    assert_eq!(
        format_modelval(&pz),
        "(fp #b0 #b00000000 #b00000000000000000000000)"
    );
    // Float32 -0: sign bit set (2^31)
    let nz = ModelVal::Float { eb: 8, sb: 24, bits: shinri_num::Integer::from(1u64 << 31) };
    assert_eq!(
        format_modelval(&nz),
        "(fp #b1 #b00000000 #b00000000000000000000000)"
    );
    // Float32 +inf = 0x7F800000: sign 0, exp 11111111, sig 0
    let inf = ModelVal::Float { eb: 8, sb: 24, bits: shinri_num::Integer::from(0x7F80_0000u64) };
    assert_eq!(
        format_modelval(&inf),
        "(fp #b0 #b11111111 #b00000000000000000000000)"
    );
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver format_float_modelval_as_fp_triple`
Expected: FAIL — no `ModelVal::Float` variant.

- [ ] **Step 3: Add the variant**

In `crates/shinri-theory/src/types.rs`, extend `ModelVal` (keep existing variants):

```rust
    /// A floating-point value: `(eb, sb, bits)` where `bits` is the W=eb+sb
    /// unsigned bit pattern, MSB→LSB `[sign | exp | trailing-sig]`.
    Float { eb: u32, sb: u32, bits: shinri_core::Integer },
```

- [ ] **Step 4: Render it in `format_modelval`**

In `crates/shinri-solver/src/model.rs`, add an arm to the `match v` in `format_modelval` (reusing the existing `field`-style extraction via `format_bin_fixed`):

```rust
        ModelVal::Float { eb, sb, bits } => {
            // Split bits MSB→LSB into sign(1) | exp(eb) | trailing-sig(sb-1).
            let two = shinri_num::Integer::from(2u64);
            // sign = top bit; exp = next eb bits; sig = low sb-1 bits.
            // Extract low (sb-1) bits.
            let mut modulus = shinri_num::Integer::one();
            for _ in 0..(sb - 1) { modulus = modulus * two.clone(); }
            let sig = bits.div_rem(&modulus).1;
            // shift right by (sb-1) to get exp|sign
            let mut hi = bits.clone();
            for _ in 0..(sb - 1) { hi = hi.div_rem(&two).0; }
            let mut exp_mod = shinri_num::Integer::one();
            for _ in 0..*eb { exp_mod = exp_mod * two.clone(); }
            let exp = hi.div_rem(&exp_mod).1;
            let mut sign = hi.clone();
            for _ in 0..*eb { sign = sign.div_rem(&two).0; }
            format!(
                "(fp #b{} #b{} #b{})",
                format_bin_fixed(&sign, 1),
                format_bin_fixed(&exp, *eb),
                format_bin_fixed(&sig, sb - 1),
            )
        }
```

> `format_bin_fixed(val, width)` already exists in this file (MSB-first, zero-padded). Reuse it. `Integer::div_rem`, `one`, and `from` are already used here (see `format_hex_fixed`/`format_bin_fixed`).

- [ ] **Step 5: Fix any other exhaustive `match ModelVal` sites**

Run: `cargo build -p shinri-theory -p shinri-solver`
Expected: if any other `match` over `ModelVal` is now non-exhaustive (e.g. in `shinri-theory`), add a `ModelVal::Float { .. } => …` arm. FP values are produced only by the FP model path, so in theory-internal matches that never see them, use `unreachable!("Float model values are produced only by the FP stage")`. List each site you touched in the commit body.

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo test -p shinri-solver format_float_modelval_as_fp_triple`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-theory/src/types.rs crates/shinri-solver/src/model.rs
git commit -m "feat(model): ModelVal::Float + (fp ...) rendering"
```

---

### Task 9: Parser printer carry-forward (`print.rs` placeholders)

**Files:**
- Modify: `crates/shinri-parser/src/print.rs`
- Test: `crates/shinri-parser/src/print.rs` (or the existing `roundtrip` test module)

**Interfaces:**
- Consumes: `ctx.fp_const_value`, `ctx.rm_const_value` (foundation).
- Produces: `print_term` renders `ConstVal::Float` as `(fp #b… #b… #b…)` and `ConstVal::Rm` as its `RNE`/… token.

> Per the parent design's carry-forward (§8), these placeholders become a wrong-output bug once any printing path renders FP/RM constants. `print_term` is `pub use`'d from the parser crate, so fixing it now removes the latent bug even though slice-1's `get-model` path uses the solver's `format_modelval`.

- [ ] **Step 1: Write the failing test**

Add to the test module in `crates/shinri-parser/src/print.rs` (mirror the file's existing test setup):

```rust
#[test]
fn prints_fp_const_and_rm() {
    use shinri_core::{Context, term::RoundingMode};
    use shinri_num::Integer;
    let mut ctx = Context::new();
    // Float32 +zero
    let pz = ctx.mk_fp_const(8, 24, Integer::zero());
    assert_eq!(print_term(&ctx, pz), "(fp #b0 #b00000000 #b00000000000000000000000)");
    // rounding mode
    let rne = ctx.mk_rm_const(RoundingMode::Rne);
    assert_eq!(print_term(&ctx, rne), "RNE");
}
```

> If `print_term`'s signature differs (e.g. takes `&mut String` or returns via a writer), match the existing tests in this file; the two rendered strings are the contract.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser prints_fp_const_and_rm`
Expected: FAIL — currently renders `<fp>` / `<rm>`.

- [ ] **Step 3: Implement real rendering**

In `crates/shinri-parser/src/print.rs`, replace lines 51-52:

```rust
            ConstVal::Float(_) => out.push_str("<fp>"),
            ConstVal::Rm(_) => out.push_str("<rm>"),
```

with:

```rust
            ConstVal::Float(_) => {
                let (eb, sb, bits) = ctx.fp_const_value(t).expect("Float const");
                out.push_str(&format_fp_triple(eb, sb, bits));
            }
            ConstVal::Rm(_) => {
                let rm = ctx.rm_const_value(t).expect("RM const");
                out.push_str(match rm {
                    shinri_core::term::RoundingMode::Rne => "RNE",
                    shinri_core::term::RoundingMode::Rna => "RNA",
                    shinri_core::term::RoundingMode::Rtp => "RTP",
                    shinri_core::term::RoundingMode::Rtn => "RTN",
                    shinri_core::term::RoundingMode::Rtz => "RTZ",
                });
            }
```

Add a `format_fp_triple` free helper near the top of `print.rs` (mirroring the binary-field split; `t` is the `TermId` in scope at the match — confirm the surrounding code binds it, else thread `t` through):

```rust
/// Render an FP literal as `(fp #b<sign> #b<exp> #b<trailing-sig>)`.
fn format_fp_triple(eb: u32, sb: u32, bits: &shinri_num::Integer) -> String {
    use shinri_num::Integer;
    let two = Integer::from(2u64);
    let bin = |val: &Integer, width: u32| -> String {
        let mut rem = val.clone();
        let mut b: Vec<u8> = Vec::with_capacity(width as usize);
        for _ in 0..width { let (q, r) = rem.div_rem(&two); b.push(r.to_i128().unwrap_or(0) as u8); rem = q; }
        b.reverse();
        b.iter().map(|&x| if x == 1 { '1' } else { '0' }).collect()
    };
    // low (sb-1) bits = trailing sig; next eb bits = exp; top bit = sign.
    let mut sig_mod = Integer::one();
    for _ in 0..(sb - 1) { sig_mod = sig_mod * two.clone(); }
    let sig = bits.div_rem(&sig_mod).1;
    let mut hi = bits.clone();
    for _ in 0..(sb - 1) { hi = hi.div_rem(&two).0; }
    let mut exp_mod = Integer::one();
    for _ in 0..eb { exp_mod = exp_mod * two.clone(); }
    let exp = hi.div_rem(&exp_mod).1;
    let mut sign = hi;
    for _ in 0..eb { sign = sign.div_rem(&two).0; }
    format!("(fp #b{} #b{} #b{})", bin(&sign, 1), bin(&exp, eb), bin(&sig, sb - 1))
}
```

> If `shinri-num` is not already a direct dependency of `shinri-parser`, it is (the parser builds `Integer` for BV/FP literals). Confirm `use` paths against the file's existing imports.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-parser prints_fp_const_and_rm`
Expected: PASS. Also run `cargo test -p shinri-parser` to confirm the existing `roundtrip.rs` suite is still green.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-parser/src/print.rs
git commit -m "fix(parser): render FP literals and rounding modes (carry-forward)"
```

---

### Task 10: Wire the FP stage into the solver pipeline + FP model extraction

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs`
- Test: `crates/shinri-solver/src/lib.rs` (`#[cfg(test)]`)

**Interfaces:**
- Consumes: `crate::fp_stage::{solver_uses_fp, collect_fp_atoms, has_non_fp_theory_atom}`; `shinri_fp::lower`; existing `replay_bv_cnf`; `ModelVal::Float`.
- Produces: a `self.fp_var_bits: FxHashMap<TermId, Vec<Var>>` field; FP atoms surrogated into the encoder; FP model values inserted.

- [ ] **Step 1: Write the failing test**

Add a test module to `crates/shinri-solver/src/lib.rs` (next to `string_routing_tests`):

```rust
#[cfg(test)]
mod fp_routing_tests {
    use super::*;

    #[test]
    fn isnan_is_sat() {
        // (assert (fp.isNaN x)) is satisfiable (x = NaN).
        let src = "(declare-fun x () Float32) (assert (fp.isNaN x)) (check-sat)";
        assert_eq!(run_outcome(src), SolveOutcome::Sat);
    }

    #[test]
    fn zero_and_inf_is_unsat() {
        // x cannot be both zero and infinite.
        let src = "(declare-fun x () Float32) \
                   (assert (fp.isZero x)) (assert (fp.isInfinite x)) (check-sat)";
        assert_eq!(run_outcome(src), SolveOutcome::Unsat);
    }

    #[test]
    fn pos_zero_neg_zero_core_distinct_but_fp_eq() {
        // (= x (_ +zero 8 24)) ∧ (= x (_ -zero 8 24)) is UNSAT under core =.
        let src = "(declare-fun x () Float32) \
                   (assert (= x (_ +zero 8 24))) (assert (= x (_ -zero 8 24))) (check-sat)";
        assert_eq!(run_outcome(src), SolveOutcome::Unsat);
    }

    #[test]
    fn fp_mixed_with_bv_is_unknown() {
        let src = "(declare-fun x () Float32) (declare-fun b () (_ BitVec 8)) \
                   (assert (fp.isNaN x)) (assert (bvult b #x01)) (check-sat)";
        assert_eq!(run_outcome(src), SolveOutcome::Unknown);
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver fp_routing_tests`
Expected: FAIL — FP queries currently fall through to the Combiner (likely `Unknown` or wrong), and the wiring/field don't exist.

- [ ] **Step 3: Add the `fp_var_bits` field**

In `crates/shinri-solver/src/lib.rs`, in `struct Solver` add next to `bv_var_bits` (line ~65):

```rust
    fp_var_bits: rustc_hash::FxHashMap<TermId, Vec<shinri_core::Var>>,
```

and initialize it in `Solver::new` next to `bv_var_bits: …` (line ~90):

```rust
            fp_var_bits: rustc_hash::FxHashMap::default(),
```

- [ ] **Step 4: Lower FP atoms alongside BV (before the SAT clone)**

In `check_sat`, immediately after the `lowered_bv` block (after line ~361, before the `lowered: Vec<TermId>` map), add:

```rust
        // ── FP path (QF_FP, FP-private Blaster) ────────────────────────────────
        // Pure-FP queries lower their FP atoms to CNF here. A query that ALSO
        // uses BV (or any non-FP theory atom) is fenced to Unknown — BVFP
        // unification is a later plan. (If lowered_bv is Some, the BV fence above
        // already caught FP atoms as non-BV and returned Unknown, so FP only runs
        // when there is no BV.)
        let lowered_fp: Option<shinri_bv::Lowered> =
            if lowered_bv.is_none() && crate::fp_stage::solver_uses_fp(&self.ctx, &assertions) {
                let fp_atoms = crate::fp_stage::collect_fp_atoms(&self.ctx, &assertions);
                if crate::fp_stage::has_non_fp_theory_atom(&self.ctx, &assertions, &fp_atoms) {
                    return SolveOutcome::Unknown;
                }
                Some(shinri_fp::lower(&mut self.ctx, &fp_atoms))
            } else {
                None
            };
```

- [ ] **Step 5: Replay the FP CNF and merge surrogates**

In the block that replays the BV CNF (the `match lowered_bv { Some(lo) => { … } None => { … } }` around line 384-397), extend it so FP is replayed too. Replace that block with:

```rust
        let mut surrogate_map: rustc_hash::FxHashMap<TermId, shinri_core::Lit> =
            rustc_hash::FxHashMap::default();
        match lowered_bv {
            Some(lo) => {
                let surrogates = self.replay_bv_cnf(&mut sat, lo);
                self.bv_var_bits = surrogates.var_bits;
                surrogate_map.extend(surrogates.atom_to_lit);
            }
            None => {
                self.bv_var_bits.clear();
            }
        }
        match lowered_fp {
            Some(lo) => {
                // Reuse replay_bv_cnf: it allocates a fresh contiguous var block,
                // so FP and BV namespaces never collide.
                let surrogates = self.replay_bv_cnf(&mut sat, lo);
                self.fp_var_bits = surrogates.var_bits;
                surrogate_map.extend(surrogates.atom_to_lit);
            }
            None => {
                self.fp_var_bits.clear();
            }
        }
        let bv_atom_lit: Option<rustc_hash::FxHashMap<TermId, shinri_core::Lit>> =
            if surrogate_map.is_empty() { None } else { Some(surrogate_map) };
```

> `replay_bv_cnf` is generic over the lowered CNF and allocates its own fresh var block each call, so calling it twice (BV then FP) is safe — the second block starts above the first. The merged `surrogate_map` feeds `enc.set_bv_surrogates` unchanged (the encoder treats any mapped TermId as a pre-blasted literal regardless of which theory produced it).

- [ ] **Step 6: Extract FP model values**

In the `SolveResult::Sat` arm, right after the BV model extraction loop (`for (&term, sat_vars) in &self.bv_var_bits { … }`, ~line 496-507), add:

```rust
                // FP model extraction: pack each FP constant's bits into ModelVal::Float.
                for (&term, sat_vars) in &self.fp_var_bits {
                    let width = sat_vars.len() as u32;
                    let bits_bool: Vec<bool> = sat_vars
                        .iter()
                        .map(|&v| sat.value_of(v).unwrap_or(false))
                        .collect();
                    let packed = shinri_bv::model::pack(width, &bits_bool);
                    // recover (eb, sb) from the term's Float sort.
                    if let Some((eb, sb)) = self.ctx.fp_widths(self.ctx.sort_of(term)) {
                        use shinri_theory::types::ModelVal;
                        model.values.insert(term, ModelVal::Float { eb, sb, bits: packed });
                    }
                }
```

- [ ] **Step 7: Run test to verify it passes**

Run: `cargo test -p shinri-solver fp_routing_tests`
Expected: PASS (all four: SAT, UNSAT, core-=-zero UNSAT, mixed→Unknown).

- [ ] **Step 8: Run the full solver suite (non-regression)**

Run: `cargo test -p shinri-solver`
Expected: PASS — the BV/string/array/arith paths are untouched (FP only runs when `lowered_bv.is_none()` and FP is present).

- [ ] **Step 9: Commit**

```bash
git add crates/shinri-solver/src/lib.rs
git commit -m "feat(solver): wire FP stage + FP model extraction (pure QF_FP end-to-end)"
```

---

### Task 11: End-to-end get-model integration test

**Files:**
- Create: `crates/shinri-solver/tests/fp_e2e.rs`

**Interfaces:**
- Consumes: the solver's public command-execution + `get_model_string`/`get_value` API.

- [ ] **Step 1: Write the test**

Create `crates/shinri-solver/tests/fp_e2e.rs`. Mirror the harness an existing `crates/shinri-solver/tests/*.rs` uses to drive a script through the public API (check a sibling test for the exact entry points — e.g. `Solver::new`, `Parser::new`, `next_command`, `execute`, `get_model_string`):

```rust
use shinri_parser::Parser;
use shinri_solver::{SolveOutcome, Solver};

/// Drive a script; return (last outcome, model string after the last check-sat).
fn run(src: &str) -> (SolveOutcome, String) {
    let mut s = Solver::new();
    let mut p = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(cmd) = p.next_command(s.ctx_mut()) {
        let cmd = cmd.expect("parse");
        use shinri_solver::CommandResponse;
        match s.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    let model = s.get_model_string();
    (outcome, model)
}

#[test]
fn isnan_sat_model_is_a_nan() {
    let (o, model) = run("(declare-fun x () Float32) (assert (fp.isNaN x)) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
    // The model must define x as an (fp ...) triple whose exponent is all ones
    // and significand non-zero. We assert the rendering shape only.
    assert!(model.contains("(fp #b"), "model must render x as an fp triple: {model}");
}

#[test]
fn isnegative_and_isinfinite_sat() {
    let (o, _) = run("(declare-fun x () Float32) \
                      (assert (fp.isNegative x)) (assert (fp.isInfinite x)) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat); // x = -inf
}

#[test]
fn fp_eq_pos_neg_zero_is_sat() {
    // +0 fp.eq -0 holds, so this is SAT (any x works since both consts are concrete).
    let (o, _) = run("(assert (fp.eq (_ +zero 8 24) (_ -zero 8 24))) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}
```

> If `CommandResponse` is not re-exported at the crate root, import it from wherever the sibling tests do (it is used by `run_outcome` inside `lib.rs`, so it is at least `pub(crate)`; a `tests/` file needs a `pub` path — if missing, drive via `s.check_sat()` after executing declarations/asserts instead, mirroring the BV oracle test's direct-API style).

- [ ] **Step 2: Run the test**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS. If `CommandResponse`/`ctx_mut`/`get_model_string` visibility blocks the harness, adapt to the sibling tests' exact API (the assertions are the contract).

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): end-to-end QF_FP SAT/UNSAT + get-model rendering"
```

---

### Task 12: Differential-vs-z3 oracle (feature-gated)

**Files:**
- Create: `crates/shinri-solver/tests/fp_oracle.rs`

**Interfaces:**
- Consumes: the public solver API; `easy_smt` (existing dev-dependency, used by `qfbv_oracle.rs`); z3 on PATH.

- [ ] **Step 1: Write the feature-gated differential test**

Create `crates/shinri-solver/tests/fp_oracle.rs`, mirroring `crates/shinri-solver/tests/qfbv_oracle.rs` (copy its `Lcg`, its z3 setup via `easy_smt`, and its disagreement-panic structure). Restrict generation to the slice-1 op set: random Float32 constants and one variable `x`, atoms drawn from `{fp.isNaN, fp.isInfinite, fp.isZero, fp.isNormal, fp.isSubnormal, fp.isNegative, fp.isPositive, fp.eq, =}` over `x` and constants, combined with `and`/`or`/`not`:

```rust
//! Differential oracle: shinri-solver vs z3 on random rounding-free QF_FP.
//! Run: cargo test -p shinri-solver --features oracle --test fp_oracle -- --nocapture
//! Requires `z3` on PATH. Guarded by `#[cfg(feature = "oracle")]`.
#![cfg(feature = "oracle")]

use shinri_solver::{SolveOutcome, Solver};

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 { self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1); self.0 >> 16 }
    fn below(&mut self, n: u64) -> u64 { self.next() % n }
}

const N_ITERS: usize = 200;

/// Build one random rounding-free QF_FP script body (declarations + asserts),
/// returning the full SMT-LIB source (shared by shinri and z3).
fn gen_script(rng: &mut Lcg) -> String {
    // 32-bit constants as (fp #b.. #b.. #b..) via (_ to_fp ...) bitcast OR the
    // special forms; here we use random 32-bit patterns as (fp ...) triples.
    let preds = ["fp.isNaN","fp.isInfinite","fp.isZero","fp.isNormal",
                 "fp.isSubnormal","fp.isNegative","fp.isPositive"];
    let mut s = String::from("(set-logic QF_FP)\n(declare-fun x () Float32)\n");
    let n_asserts = 1 + rng.below(3);
    for _ in 0..n_asserts {
        let p = preds[rng.below(preds.len() as u64) as usize];
        // half the time negate
        if rng.below(2) == 0 {
            s.push_str(&format!("(assert ({} x))\n", p));
        } else {
            s.push_str(&format!("(assert (not ({} x)))\n", p));
        }
    }
    s.push_str("(check-sat)\n");
    s
}

fn shinri_outcome(src: &str) -> SolveOutcome {
    use shinri_parser::Parser;
    use shinri_solver::CommandResponse;
    let mut s = Solver::new();
    let mut p = Parser::new(src);
    let mut o = SolveOutcome::Unknown;
    while let Some(cmd) = p.next_command(s.ctx_mut()) {
        match s.execute(cmd.expect("parse")) {
            CommandResponse::Sat => o = SolveOutcome::Sat,
            CommandResponse::Unsat => o = SolveOutcome::Unsat,
            CommandResponse::Unknown => o = SolveOutcome::Unknown,
            _ => {}
        }
    }
    o
}

#[test]
fn differential_qf_fp_rounding_free() {
    let mut rng = Lcg(0xF10A7);
    let z3 = easy_smt::ContextBuilder::new().solver("z3", ["-smt2", "-in"]).build().unwrap();
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown { continue; } // sound abstention
        // z3 via raw script: feed the same source, read sat/unsat.
        z3.raw_send(&src).unwrap();
        let z = z3.raw_recv_check_sat().unwrap(); // adapt to easy_smt's API used in qfbv_oracle.rs
        z3.raw_send("(reset)\n").unwrap();
        let z_outcome = match z {
            easy_smt::Response::Sat => SolveOutcome::Sat,
            easy_smt::Response::Unsat => SolveOutcome::Unsat,
            _ => continue,
        };
        assert_eq!(ours, z_outcome, "QF_FP DISAGREEMENT (iter {iter}):\n{src}");
    }
}
```

> The `easy_smt` send/recv calls above are a sketch — **copy the exact z3-driving idiom from `crates/shinri-solver/tests/qfbv_oracle.rs`** (around its `easy_smt` setup at line ~444 and its check-sat read). The contract: same script to both engines, `assert_eq!` the SAT/UNSAT verdict, skip when shinri returns `Unknown`. Confirm the `oracle` feature exists in `crates/shinri-solver/Cargo.toml` (it gates `qfbv_oracle.rs`); reuse it.

- [ ] **Step 2: Run the oracle (requires z3)**

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle -- --nocapture`
Expected: PASS — no SAT/UNSAT disagreements over 200 random rounding-free instances. (z3 4.16.0 is at `~/.local/share/mise/installs/.../z3`; ensure it is on PATH, e.g. via `mise`.)

- [ ] **Step 3: Run the entire workspace test suite (final non-regression)**

Run: `cargo test --workspace`
Expected: PASS — every existing crate's tests plus the new `shinri-fp` tests.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential-vs-z3 oracle for rounding-free QF_FP"
```

---

## Self-Review

**Spec coverage** (against `2026-06-25-shinri-qffp-vertical-slice-design.md`):
- §4.1 new crate `shinri-fp` — Task 1 (skeleton). ✓
- §4.1 `reference.rs` built in full (round core) — Tasks 1 (rounding-free) + 2 (rounding core). ✓
- §4.1 `unpack`/`pack` — Task 3. ✓
- §4.1 `blast/classify` (7 predicates) — Task 4. ✓
- §4.1 `blast/compare` (`fp.eq` + NaN-aware core `=`) and `blast/structural` (`abs`/`neg`) — Task 5. ✓
- §4.1 `lib.rs` `lower()` + dispatch, `model.rs` — Task 6. ✓
- §4.2 `fp_stage.rs` (`solver_uses_fp`/`collect_fp_atoms`/`has_non_fp_theory_atom`, soundness-critical FP `=` collection, BV-mixed fence) — Task 7 + Task 10 wiring. ✓
- §4.2 surrogate replay reusing `replay_bv_cnf`; FP-private Blaster; pure-FP routing — Task 10. ✓
- §4.2 slice-1 Real boundary → `Unknown` (Real-FP conversions are non-FP atoms, fenced) — covered by `has_non_fp_theory_atom` (any non-FP Bool atom fences); `FpToReal` is in `is_fp_op` for detection but never collected as an FP atom, so it fences. ✓ *(Note: `fp.to_real` is Real-sorted, not Bool-sorted, so it is reached only as a subterm; a top-level assert containing it is a non-FP Bool atom elsewhere or routes to arith → fenced. No slice-1 op produces it.)*
- §4.3 printer carry-forward (`print.rs:51-52`) — Task 9. ✓ Plus the real get-model path (`ModelVal::Float` + `format_modelval`) — Task 8. ✓
- §4.4 validation: golden-vs-oracle exhaustive on `(3,5)` + Float32 reps (Tasks 4–5); equality-gadget +0/−0/NaN cases (Task 5); end-to-end SAT/UNSAT/get-model (Tasks 10–11); differential-vs-z3 feature-gated (Task 12); non-regression `cargo test --workspace` (Task 12). ✓
- §5 soundness: every out-of-scope construct → `Unknown` via the fence; no wrong verdict. ✓

**Placeholder scan:** No `TBD`/`TODO`/"handle edge cases". Explicit adapt-points are flagged with the exact fallback: `Integer`/`Rational` API confirmations (Tasks 1–2), the parser/solver test-harness entry-point names (Tasks 9, 11), and the `easy_smt` z3 idiom to copy verbatim from `qfbv_oracle.rs` (Task 12). These are existing-API confirmations, not unspecified work.

**Type consistency:** `FpClass`/`decode`/`ref_*` (Task 1) consumed unchanged in Tasks 2/4/5. `Unpacked { sign, exp, sig, is_nan, is_inf, is_zero }` (Task 3) consumed identically in Tasks 4/5/6. `FpBlaster { b, cache, var_bits }` with `blast_word`/`blast_atom`/`exported_var_bits` (Tasks 3/6) and `lower() -> shinri_bv::Lowered` (Task 6) consumed by the solver in Task 10. `fp_stage` fn signatures (Task 7) match their call sites in Task 10. `ModelVal::Float { eb, sb, bits }` (Task 8) constructed identically in Task 10's extraction and rendered in Task 8's `format_modelval`. Bit order LSB→MSB and the `[sign|exp|sig]` layout are consistent across `blast_word`, `unpack`, `pack`, `model::pack`, `format_modelval`, and `format_fp_triple`.
