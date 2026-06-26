# QF_FP Slice 2c — `fp.div` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bit-blast `fp.div` for QF_FP end-to-end (parse → blast → SAT → model) by reusing the slice-2a op-agnostic rounder, the shared `Operand` helper, and the `shinri-bv` restoring divider (`udivurem`), validated bit-identical to a new exact-rational reference oracle (`ref_div`) and differentially against z3.

**Architecture:** Eager bit-blasting into the slice-1 `FpBlaster`. `fp.div` is the `fp.mul` datapath with three swaps: an unsigned **divide** instead of the multiply, a **divide-by-zero → ±∞** special-case table, and a **remainder-folds-into-sticky** rounding-info derivation. Because a quotient is not exact (unlike a product), the operands' significands are first **pre-normalized** into `[2^(sb-1), 2^sb)` (LZC + left-shift, exponent adjusted) so the ratio lands in `(1/2, 2)` and a fixed number of fractional quotient bits suffices. The pipeline is: unpack both operands → XOR signs → pre-normalize each significand → `dividend = xsig_n << F`, divide by `ysig_n` via `udivurem` (width `W = 2·sb+2`, `F = sb+2`) → uniform LZC normalize of the quotient → build `ExtFp` (top `sb` bits = significand, next two = G/R, `S = OR(rest) OR (rem≠0)`) → slice-2a `round()` → IEEE special-case mux. Everything out of scope stays a sound `Unknown`.

**Tech Stack:** Rust, `shinri-fp` crate (depends on `shinri-bv`, `shinri-core`, `shinri-num`), the `shinri-sat` CDCL core for tests, `easy_smt` + z3 for the differential oracle (feature-gated).

## Global Constraints

- **Bit layout** (fixed by the foundation): a Float word is `W_fp = eb + sb` bits, **LSB→MSB**, MSB-to-LSB meaning `[ sign(1) | exponent(eb) | trailing-significand(sb-1) ]`. `sb` **includes** the hidden bit. (Note: this `W_fp` is the packed-word width; the datapath's internal divide width is the separate `W = 2·sb+2` below.)
- **Soundness contract:** anything outside the now-supported ops (`FpAbs`/`FpNeg`/`FpAdd`/`FpSub`/`FpMul` and, after this slice, `FpDiv`) returns `Unknown`, never a wrong SAT/UNSAT. `sqrt`/`fma`/`rem`/`roundToIntegral`/`min`/`max`, all conversions, FP+BV mixing, FP+EUF/Arith/Arrays, and any Real bridge stay fenced.
- **Validation anchor:** the `fp.div` datapath MUST be bit-identical to `reference.rs::ref_div` (added in Task 1). Exhaustive on the `(3,5)` tiny format over all five modes; randomized on Float32. The slice-2a `round()` is reused **unchanged** — 2c adds no rounder logic.
- **No new external dependencies.** Reuse `shinri-bv` helpers (`shinri_bv::blast::div::udivurem`, `bvadd`, `bvsub`, `bvshl`) and `Blaster` primitives (`and2`, `or2`, `xor2`, `not1`, `mux2`, `one`, `zero`). `udivurem(b, dividend, divisor) -> (Vec<BitLit>, Vec<BitLit>)` requires **equal-width** dividend and divisor; both are zero-extended to `W = 2·sb+2` bits before the call.
- **`RoundingMode` encoding:** unchanged from 2a — the `rm.rs` selector (`literal`/`symbolic`) and `FpBlaster::blast_rm` already exist; `fp.div` consumes them identically to `fp.mul`.
- **Reference rounding-mode type:** `reference.rs` uses its own `RoundMode { Rne, Rna, Rtp, Rtn, Rtz }`; map `shinri_core::RoundingMode` → `reference::RoundMode` 1:1 in tests (the `rmode` helper already exists in the test modules).
- **Sign rule (div):** result sign is `sign_x XOR sign_y` **always**, including specials and zeros. No mode-dependent zero-sign rule.
- **Divide-by-zero:** `finite-nonzero / ±0 → ±∞` (IEEE *divByZero*). No exception flags are in scope for v1.
- **Shared `Operand` helper already exists** (`blast/operand.rs`, landed in slice 2b) — `to_operand`, `canon_nan_bits`, `inf_pattern_bits`, `signed_zero_bits`. No lift/refactor task this slice.

## File Structure

| File | Status | Responsibility |
|---|---|---|
| `crates/shinri-fp/src/reference.rs` | Modify | Add `ref_div` (exact-rational golden `fp.div`). |
| `crates/shinri-fp/src/blast/div.rs` | Create | The `fp.div` datapath (pre-normalize → divide → normalize → round → special-case mux). |
| `crates/shinri-fp/src/blast/mod.rs` | Modify | Add `pub mod div;`. |
| `crates/shinri-fp/src/lib.rs` | Modify | `blast_word` gains an `FpDiv` arm. |
| `crates/shinri-solver/src/fp_stage.rs` | Modify | Admit `FpDiv` in `is_supported_fp_word`; flip `fp_div_word_is_not_supported` to a positive test + add an `fp.sqrt`-fenced negative test. |
| `crates/shinri-solver/tests/fp_e2e.rs` | Modify | End-to-end `fp.div` SAT/UNSAT + symbolic-RM + get-model. |
| `crates/shinri-solver/tests/fp_oracle.rs` | Modify | Differential-vs-z3 over `fp.div`, all five modes. |

Task ordering: **1 (ref_div) → 2 (div datapath) → 3 (lib wiring) → 4 (fence) → 5 (e2e) → 6 (oracle) → 7 (sweep).** Task 1 is independent and may be done first.

---

### Task 1: Exact-rational reference `fp.div` (`ref_div`)

The golden oracle the datapath is checked against. Pure Rust over `shinri-num::Rational`; no circuit. Reuses the existing `decode`, `class_to_rational`, `round_rational`, `canonical_nan`, `inf_pattern`, `zero_pattern`, `ref_is_negative`, `FpClass`, and `RoundMode` already in `reference.rs`.

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (append a function + tests)

**Interfaces:**
- Consumes: `decode(eb, sb, &Integer) -> FpClass`, `class_to_rational(eb, sb, &FpClass) -> Option<Rational>`, `round_rational(eb, sb, &Rational, RoundMode) -> Integer`, `canonical_nan(eb, sb) -> Integer`, `inf_pattern(eb, sb, bool) -> Integer`, `zero_pattern(eb, sb, bool) -> Integer`, `ref_is_negative(&FpClass) -> bool`, `FpClass`, `RoundMode` (all already in `reference.rs`).
- Produces: `pub fn ref_div(eb: u32, sb: u32, a: &Integer, b: &Integer, mode: RoundMode) -> Integer` — canonical NaN for `NaN/x`, `0/0`, `∞/∞`; signed ∞ for `∞/finite` and `finite-nonzero/0`; signed zero for `finite/∞` and `0/finite-nonzero`; else `round_rational(exact_quotient)`. Result sign is always `sign_a XOR sign_b`.

- [ ] **Step 1: Write the failing test**

Append to the `#[cfg(test)] mod tests` block in `reference.rs`:

```rust
#[test]
fn ref_div_known_float32() {
    let (eb, sb) = (8u32, 24u32);
    // 6.0 / 2.0 = 3.0 = 0x40400000
    assert_eq!(ref_div(eb, sb, &i(0x40C0_0000), &i(0x4000_0000), RoundMode::Rne), i(0x4040_0000));
    // 1.0 / 2.0 = 0.5 = 0x3F000000
    assert_eq!(ref_div(eb, sb, &i(0x3F80_0000), &i(0x4000_0000), RoundMode::Rne), i(0x3F00_0000));
    // -1.0 / 2.0 = -0.5 = 0xBF000000  (sign = XOR)
    assert_eq!(ref_div(eb, sb, &i(0xBF80_0000), &i(0x4000_0000), RoundMode::Rne), i(0xBF00_0000));
    // 1.0 / 3.0 = 0x3EAAAAAB (RNE), 0x3EAAAAAA (RTZ)
    assert_eq!(ref_div(eb, sb, &i(0x3F80_0000), &i(0x4040_0000), RoundMode::Rne), i(0x3EAA_AAAB));
    assert_eq!(ref_div(eb, sb, &i(0x3F80_0000), &i(0x4040_0000), RoundMode::Rtz), i(0x3EAA_AAAA));
    // 1.0 / +0 = +inf  (divByZero, sign +)
    assert_eq!(ref_div(eb, sb, &i(0x3F80_0000), &i(0x0000_0000), RoundMode::Rne), i(0x7F80_0000));
    // 1.0 / -0 = -inf  (divByZero, sign -)
    assert_eq!(ref_div(eb, sb, &i(0x3F80_0000), &i(0x8000_0000), RoundMode::Rne), i(0xFF80_0000));
    // -2.0 / +0 = -inf
    assert_eq!(ref_div(eb, sb, &i(0xC000_0000), &i(0x0000_0000), RoundMode::Rne), i(0xFF80_0000));
    // +0 / +0 = canonical NaN
    assert_eq!(ref_div(eb, sb, &i(0x0000_0000), &i(0x0000_0000), RoundMode::Rne), i(0x7FC0_0000));
    // +inf / +inf = canonical NaN
    assert_eq!(ref_div(eb, sb, &i(0x7F80_0000), &i(0x7F80_0000), RoundMode::Rne), i(0x7FC0_0000));
    // +inf / 2.0 = +inf
    assert_eq!(ref_div(eb, sb, &i(0x7F80_0000), &i(0x4000_0000), RoundMode::Rne), i(0x7F80_0000));
    // 2.0 / +inf = +0 ; -2.0 / +inf = -0
    assert_eq!(ref_div(eb, sb, &i(0x4000_0000), &i(0x7F80_0000), RoundMode::Rne), i(0x0000_0000));
    assert_eq!(ref_div(eb, sb, &i(0xC000_0000), &i(0x7F80_0000), RoundMode::Rne), i(0x8000_0000));
    // +0 / 2.0 = +0 ; +0 / -2.0 = -0 (sign XOR)
    assert_eq!(ref_div(eb, sb, &i(0x0000_0000), &i(0x4000_0000), RoundMode::Rne), i(0x0000_0000));
    assert_eq!(ref_div(eb, sb, &i(0x0000_0000), &i(0xC000_0000), RoundMode::Rne), i(0x8000_0000));
    // NaN / 1.0 = canonical NaN
    assert_eq!(ref_div(eb, sb, &i(0x7FC0_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x7FC0_0000));
    // overflow: max-normal / 0.5 = +inf. Max normal = 0x7F7FFFFF, 0.5 = 0x3F000000.
    assert_eq!(ref_div(eb, sb, &i(0x7F7F_FFFF), &i(0x3F00_0000), RoundMode::Rne), i(0x7F80_0000));
}
```

(`i` is the `fn i(v: u64) -> Integer { Integer::from(v) }` helper already defined in the `reference.rs` test module. The `1/3` encodings `0x3EAAAAAB`/`0x3EAAAAAA` are the standard IEEE-754 binary32 round-to-nearest / round-toward-zero results.)

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp ref_div_known_float32`
Expected: FAIL — `cannot find function ref_div in this scope`.

- [ ] **Step 3: Write the implementation**

Append to `reference.rs` (after `ref_mul`). The XOR sign is computed once and reused for all non-NaN result patterns. Arm order respects NaN > Inf > Zero priority.

```rust
/// Exact-rational golden `fp.div RM a b`. `a`, `b` are W=eb+sb bit patterns.
/// Result sign is always sign_a XOR sign_b (including specials and zeros).
pub fn ref_div(eb: u32, sb: u32, a: &Integer, b: &Integer, mode: RoundMode) -> Integer {
    let ca = decode(eb, sb, a);
    let cb = decode(eb, sb, b);
    use FpClass::*;
    let sign = ref_is_negative(&ca) ^ ref_is_negative(&cb); // XOR sign
    let a_zero = matches!(ca, Zero { .. });
    let b_zero = matches!(cb, Zero { .. });
    let a_inf = matches!(ca, Inf { .. });
    let b_inf = matches!(cb, Inf { .. });
    // 1. NaN propagation, then 0/0 and inf/inf = NaN.
    if matches!(ca, Nan) || matches!(cb, Nan) { return canonical_nan(eb, sb); }
    if (a_zero && b_zero) || (a_inf && b_inf) { return canonical_nan(eb, sb); }
    // 2. Inf result: inf/finite, or finite-nonzero/0 (divByZero). (a_inf && b_inf
    //    already handled above; here b_zero implies a is finite-nonzero.)
    if a_inf || b_zero { return inf_pattern(eb, sb, sign); }
    // 3. Zero result: finite/inf, or 0/finite-nonzero. (a_zero && b_zero handled;
    //    here a_zero implies b is finite-nonzero.)
    if b_inf || a_zero { return zero_pattern(eb, sb, sign); }
    // 4. finite-nonzero / finite-nonzero: exact rational quotient, then round.
    let ra = class_to_rational(eb, sb, &ca).unwrap();
    let rb = class_to_rational(eb, sb, &cb).unwrap();
    let quot = ra / rb;
    round_rational(eb, sb, &quot, mode)
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp ref_div_known_float32`
Expected: PASS.

- [ ] **Step 5: Add an exhaustive (3,5) totality test and run**

```rust
#[test]
fn ref_div_tiny_total_and_canonical() {
    // Every (a,b,mode) on (3,5) produces a valid 8-bit encoding; NaN inputs and
    // 0/0, inf/inf produce the canonical NaN (0x7C for (3,5): exp all ones, sig MSB).
    let (eb, sb) = (3u32, 5u32);
    let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
    let nan = canonical_nan(eb, sb);
    for a in 0u64..256 {
        for b in 0u64..256 {
            let ca = decode(eb, sb, &Integer::from(a));
            let cb = decode(eb, sb, &Integer::from(b));
            let a_nan = matches!(ca, FpClass::Nan);
            let b_nan = matches!(cb, FpClass::Nan);
            for m in modes {
                let r = ref_div(eb, sb, &Integer::from(a), &Integer::from(b), m);
                assert!(r < Integer::from(256u64), "out-of-range result {a:#x}/{b:#x}");
                if a_nan || b_nan {
                    assert_eq!(r, nan, "NaN input must yield canonical NaN a={a:#x} b={b:#x} m={m:?}");
                }
            }
        }
    }
}
```

Run: `cargo test -p shinri-fp ref_div_tiny_total_and_canonical`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): exact-rational reference fp.div (ref_div) for slice 2c"
```

---

### Task 2: The `fp.div` datapath (`blast/div.rs`)

Unpack → XOR sign → pre-normalize each significand → divide (`udivurem`, width `W=2·sb+2`, fractional bits `F=sb+2`) → uniform LZC normalize of the quotient → build `ExtFp` with `S` folding the division remainder → `round()` → IEEE special-case mux. Validated bit-identical to `ref_div`, exhaustive on `(3,5)` across all five modes.

**Files:**
- Create: `crates/shinri-fp/src/blast/div.rs`
- Modify: `crates/shinri-fp/src/blast/mod.rs` (add `pub mod div;`)

**Interfaces:**
- Consumes: `crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits}`, `crate::round::{ExtFp, exp_w, round}`, `crate::rm::RmSel`, `crate::lzc::lzc`, `shinri_bv::blast::div::udivurem`, `shinri_bv::blast::arith::{bvadd, bvsub}`, `shinri_bv::blast::shift::bvshl`, `Blaster` primitives.
- Produces: `pub fn fp_div(b: &mut Blaster, x: &[BitLit], y: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit>` — the `W_fp=eb+sb` result word.

**The datapath contract (read before implementing).** Both operands come from `to_operand`: `exp` is the signed unbiased exponent (width `exp_w(eb)`), `sig` is the `sb`-bit explicit significand (hidden bit at index `sb-1`; value `sig · 2^(exp-(sb-1))`). The datapath need only be correct for **finite-nonzero ÷ finite-nonzero**; every other operand class (Zero/Inf/NaN) is overridden by the special-case mux, so garbage there is harmless. For a finite-nonzero operand `sig ≠ 0`, so `lzc(sig) < sb` and pre-normalization is well-defined.

1. **Sign** = `sign_x XOR sign_y`.
2. **Pre-normalize** each `sig` (new vs `fp.mul`): `k = lzc(sig)`; `sig_norm = sig << k` (leading 1 now at index `sb-1`, so `sig_norm ∈ [2^(sb-1), 2^sb)`); `exp_n = exp - k` (keeps the value invariant: `sig·2^(exp-(sb-1)) = sig_norm·2^((exp-k)-(sb-1))`).
3. **Divide.** `dividend = zero_extend(xsig_norm, W) << F`, `divisor = zero_extend(ysig_norm, W)`, with `W = 2·sb+2`, `F = sb+2`. `(quot, rem) = udivurem(dividend, divisor)` — each `W` bits. Since both normalized significands are in `[2^(sb-1), 2^sb)`, the true ratio `Q ∈ (1/2, 2)`, so `quot = floor(Q·2^F) ∈ [2^(F-1), 2^(F+1))` and its leading 1 is at index `F` or `F-1` — hence `lz ∈ {sb-1, sb}` only. This bound is the whole purpose of step 2.
4. **Normalize.** `lz = lzc(quot)`; `quot_n = quot << lz` places the leading 1 at index `W-1`. The `ExtFp` significand is the top `sb` bits `quot_n[W-sb .. W]`; `G = quot_n[W-sb-1]`, `R = quot_n[W-sb-2]`; `S = OR(quot_n[0 .. W-sb-2]) OR (rem ≠ 0)` — the nonzero division remainder folds into sticky. With `W-sb = sb+2`, the bits read for `G`/`R` are always real computed quotient bits, never left-fill zeros.
5. **Exponent.** `norm_exp = (exp_x_n - exp_y_n) + (sb-1) - lz` (signed, `exp_w(eb)` bits). Same shape as `fp.mul`'s `exp_sum + 1 - lz`. Derivation in design §4.4.
6. Build `ExtFp { sign, exp: norm_exp, sig, grs:(G,R,S) }`, call `round()` (slice-2a, unchanged).
7. Special-case mux overrides `round()`, priority NaN > Inf > Zero > normal.

**Exponent headroom.** `exp_w(eb) = eb + 6` is unchanged and ample: worst-case `|norm_exp| ≈ 2·bias + sb ≪ 2^(eb+5)` for every format. The exhaustive `(3,5)` test in Step 4 is the gate; if it overflows, widen `exp_w` in `round.rs` (one line) and re-run the slice-2a rounder tests.

- [ ] **Step 1: Write the failing test (exhaustive (3,5))**

Create `crates/shinri-fp/src/blast/div.rs` with the imports and test module (mirrors `mul.rs`'s test harness):

```rust
//! fp.div datapath: unpack → pre-normalize → divide → normalize → round → special-case.

use shinri_bv::{BitLit, Blaster};
use crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};
use crate::round::{exp_w, round, ExtFp};
use crate::rm::RmSel;
use crate::lzc::lzc;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{ref_div, RoundMode};
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
    fn fp_div_tiny_exhaustive_all_modes() {
        let (eb, sb) = (3u32, 5u32);
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        for a in 0u64..256 {
            for bb in 0u64..256 {
                for m in modes {
                    let want = ref_div(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                    let mut bl = Blaster::new();
                    let xv = const_bits(&bl, eb, sb, a);
                    let yv = const_bits(&bl, eb, sb, bb);
                    let sel = rm::literal(&bl, rmode(m));
                    let word = fp_div(&mut bl, &xv, &yv, &sel, eb, sb);
                    assert_eq!(Integer::from(eval_word(bl, &word)), want,
                        "fp.div a={a:#x} b={bb:#x} m={m:?}");
                }
            }
        }
    }

    #[test]
    fn fp_div_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        let specials = [0x0000_0000u64, 0x8000_0000, 0x7F80_0000, 0xFF80_0000, 0x7FC0_0000,
                        0x3F80_0000, 0xBF80_0000, 0x4000_0000, 0x0000_0001, 0x8000_0001,
                        0x7F7F_FFFF, 0x0080_0000];
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        let mut state: u64 = 0x51C0_1A5E;
        let mut next = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state >> 16 };
        let mut cases: Vec<(u64, u64)> = Vec::new();
        for &s1 in &specials { for &s2 in &specials { cases.push((s1, s2)); } }
        for _ in 0..200 { cases.push((next() & 0xFFFF_FFFF, next() & 0xFFFF_FFFF)); }
        for (a, bb) in cases {
            for m in modes {
                let want = ref_div(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                let mut bl = Blaster::new();
                let xv = const_bits(&bl, eb, sb, a);
                let yv = const_bits(&bl, eb, sb, bb);
                let sel = rm::literal(&bl, rmode(m));
                let word = fp_div(&mut bl, &xv, &yv, &sel, eb, sb);
                assert_eq!(Integer::from(eval_word(bl, &word)), want,
                    "fp.div32 a={a:#x} b={bb:#x} m={m:?}");
            }
        }
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp fp_div_tiny_exhaustive_all_modes`
Expected: FAIL — `cannot find function fp_div`.

- [ ] **Step 3: Write the datapath**

Add above the test module:

```rust
fn const_n(b: &Blaster, n: usize, v: i128) -> Vec<BitLit> {
    let u = v & ((1i128 << n) - 1);
    (0..n).map(|i| if (u >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
}
fn zero_extend(b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit> {
    let mut out = x.to_vec(); while out.len() < to { out.push(b.zero()); } out
}

/// Pre-normalize `sig` (sb bits) so its leading 1 sits at index sb-1, returning
/// (sig_norm, exp_n) with exp_n = exp - shift (signed, ew bits). For a nonzero
/// significand sig_norm lands in [2^(sb-1), 2^sb).
fn prenormalize(b: &mut Blaster, sig: &[BitLit], exp: &[BitLit], sbu: usize, ew: usize)
    -> (Vec<BitLit>, Vec<BitLit>) {
    let k = lzc(b, sig);                                 // count_width(sb) bits
    let k_sb = zero_extend(b, &k, sbu);
    let sig_norm = shinri_bv::blast::shift::bvshl(b, sig, &k_sb);
    let k_ew = zero_extend(b, &k, ew);
    let exp_n = shinri_bv::blast::arith::bvsub(b, exp, &k_ew);
    (sig_norm, exp_n)
}

pub fn fp_div(b: &mut Blaster, x: &[BitLit], y: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let w = 2 * sbu + 2;              // divide width
    let f = sbu + 2;                  // quotient fractional bits
    let ox = to_operand(b, x, eb, sb);
    let oy = to_operand(b, y, eb, sb);

    // --- Sign: XOR. ---
    let res_sign = b.xor2(ox.sign, oy.sign);

    // --- Pre-normalize both significands into [2^(sb-1), 2^sb). ---
    let (xsig_n, exp_x_n) = prenormalize(b, &ox.sig, &ox.exp, sbu, ew);
    let (ysig_n, exp_y_n) = prenormalize(b, &oy.sig, &oy.exp, sbu, ew);

    // --- Divide: dividend = xsig_n << F, divisor = ysig_n, both width W. ---
    let xz = zero_extend(b, &xsig_n, w);
    let shift_f = const_n(b, w, f as i128);
    let dividend = shinri_bv::blast::shift::bvshl(b, &xz, &shift_f);
    let divisor = zero_extend(b, &ysig_n, w);
    let (quot, rem) = shinri_bv::blast::div::udivurem(b, &dividend, &divisor);  // W bits each

    // --- Normalize quotient: leading 1 to index W-1. ---
    let lz = lzc(b, &quot);                              // count_width(W) bits
    let lz_w = zero_extend(b, &lz, w);
    let quot_n = shinri_bv::blast::shift::bvshl(b, &quot, &lz_w);

    // --- Exponent: norm_exp = exp_x_n - exp_y_n + (sb-1) - lz. ---
    let lz_ew = zero_extend(b, &lz, ew);
    let diff = shinri_bv::blast::arith::bvsub(b, &exp_x_n, &exp_y_n);
    let corr = const_n(b, ew, (sb as i128) - 1);
    let with_corr = shinri_bv::blast::arith::bvadd(b, &diff, &corr);
    let norm_exp = shinri_bv::blast::arith::bvsub(b, &with_corr, &lz_ew);

    // --- Build ExtFp from quot_n. Top sb bits = sig (hidden at index W-1);
    //     next bit = G, next = R, OR of the rest (+ rem != 0) = S. ---
    let sig: Vec<BitLit> = quot_n[(w - sbu)..w].to_vec();
    let g = quot_n[w - sbu - 1];
    let r = quot_n[w - sbu - 2];
    let mut s_acc = b.zero();
    for bit in quot_n.iter().take(w - sbu - 2) { s_acc = b.or2(s_acc, *bit); }
    // Fold a nonzero division remainder into the sticky bit.
    let mut rem_nz = b.zero();
    for bit in &rem { rem_nz = b.or2(rem_nz, *bit); }
    let s = b.or2(s_acc, rem_nz);

    let ext = ExtFp { sign: res_sign, exp: norm_exp, sig, grs: (g, r, s) };
    let rounded = round(b, ext, eb, sb, rm);

    // --- Special-case mux (overrides rounded). ---
    special_case(b, &rounded, &ox, &oy, res_sign, eb, sb)
}

/// IEEE fp.div special cases override the datapath result.
/// Priority NaN > Inf > Zero > normal. `res_sign` = sign_x XOR sign_y.
fn special_case(b: &mut Blaster, normal: &[BitLit], ox: &Operand, oy: &Operand,
                res_sign: BitLit, eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);
    let not_x_inf = b.not1(ox.is_inf);
    let not_y_inf = b.not1(oy.is_inf);
    let not_x_zero = b.not1(ox.is_zero);
    let not_y_zero = b.not1(oy.is_zero);

    // NaN if either input NaN, or 0/0, or inf/inf.
    let either_nan = b.or2(ox.is_nan, oy.is_nan);
    let zero_over_zero = b.and2(ox.is_zero, oy.is_zero);
    let inf_over_inf = b.and2(ox.is_inf, oy.is_inf);
    let nan_pair = b.or2(zero_over_zero, inf_over_inf);
    let want_nan = b.or2(either_nan, nan_pair);

    // Inf result: (x_inf AND NOT y_inf) OR (y_zero AND NOT x_zero).  [x/0 -> ±inf]
    let inf_a = b.and2(ox.is_inf, not_y_inf);
    let inf_c = b.and2(oy.is_zero, not_x_zero);
    let want_inf = b.or2(inf_a, inf_c);
    let inf_bits = inf_pattern_bits(b, eb, sb, res_sign);

    // Zero result: (x_zero AND NOT y_zero) OR (y_inf AND NOT x_inf).
    let zero_d = b.and2(ox.is_zero, not_y_zero);
    let zero_e = b.and2(oy.is_inf, not_x_inf);
    let want_zero = b.or2(zero_d, zero_e);
    let zero_bits = signed_zero_bits(b, eb, sb, res_sign);

    let mut out = normal.to_vec();
    for i in 0..w { out[i] = b.mux2(want_zero, zero_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_inf, inf_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_nan, nan[i], out[i]); }
    out
}
```

> Reuse points: `shinri_bv::blast::div::udivurem`, `shinri_bv::blast::arith::{bvadd, bvsub}`, and `shinri_bv::blast::shift::bvshl` are all `pub`. `bvshl` accepts a shift-amount word of a different width than the value being shifted (as in `fp.mul`). `lzc`, `round`, `ExtFp`, `exp_w`, and the `operand` items come from already-landed code.

- [ ] **Step 4: Run the exhaustive tiny test (the gate)**

Run: `cargo test -p shinri-fp fp_div_tiny_exhaustive_all_modes`
Expected: PASS — 256×256×5 = 327,680 solver runs; may take a minute or two (division circuits are larger than multiply). The panic message identifies any failing `(a, b, mode)`. If failures share a constant exponent offset, re-derive the `(sb-1)` correction per the contract; if the exponent overflows `exp_w`, widen `exp_w(eb)` in `round.rs` and re-run the slice-2a rounder tests. Do not weaken the test.

- [ ] **Step 5: Run the Float32 specials/random test**

Run: `cargo test -p shinri-fp fp_div_float32_specials_and_random`
Expected: PASS.

- [ ] **Step 6: Register the module and commit**

In `crates/shinri-fp/src/blast/mod.rs`, add `pub mod div;` (alphabetical placement is fine). Then:

```bash
git add crates/shinri-fp/src/blast/div.rs crates/shinri-fp/src/blast/mod.rs
git commit -m "feat(fp): fp.div datapath (prenormalize/divide/normalize/round/special) bit-identical to ref_div"
```

---

### Task 3: Wire `FpDiv` into `FpBlaster::blast_word` (`lib.rs`)

Add the `FpDiv` operator arm next to `FpMul`. RM blasting and operand blasting reuse the existing machinery.

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs`

**Interfaces:**
- Consumes: `crate::blast::div::fp_div`, the existing `FpBlaster::blast_rm` and `blast_word`, `shinri_core::BuiltinOp::FpDiv`.
- Produces: `blast_word` handles `FpDiv`.

- [ ] **Step 1: Write the failing test**

Add to the `lower_tests` module in `lib.rs` (mirrors the existing `lower_fp_mul_eq_atom`):

```rust
#[test]
fn lower_fp_div_eq_atom() {
    use shinri_core::BuiltinOp;
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let yf = ctx.declare_fun("y", &[], f32);
    let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let div = ctx.mk_app(Op::Builtin(BuiltinOp::FpDiv), &[rne, x, y]).unwrap();
    let one = ctx.mk_fp_const(8, 24, Integer::from(0x3F80_0000u64));
    let eq = ctx.mk_eq(div, one).unwrap();
    let lo = lower(&mut ctx, &[eq]);
    assert!(lo.atom_lit.contains_key(&eq), "core = over fp.div must be surrogated");
    assert!(lo.var_bits.contains_key(&x) && lo.var_bits.contains_key(&y), "x,y exported");
}
```

> Match the `lower`-result field names (`atom_lit`/`var_bits`) used by the existing `lower_fp_mul_eq_atom` test in this file verbatim — read it first.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp lower_fp_div_eq_atom`
Expected: FAIL — `blast_word` hits the `other => unreachable!` arm on `FpDiv`.

- [ ] **Step 3: Add the `FpDiv` arm to `blast_word`**

In the `Op::Builtin(op)` match inside `blast_word`, immediately after the `FpMul` arm and before `other =>`:

```rust
                    FpDiv => {
                        let rm = self.blast_rm(ctx, kids[0]);
                        let xw = self.blast_word(ctx, kids[1]);
                        let yw = self.blast_word(ctx, kids[2]);
                        crate::blast::div::fp_div(&mut self.b, &xw, &yw, &rm, eb, sb)
                    }
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `cargo test -p shinri-fp lower_fp_div_eq_atom`
Expected: PASS.

- [ ] **Step 5: Run the full crate test sweep**

Run: `cargo test -p shinri-fp`
Expected: PASS (all slice-1 + slice-2a + slice-2b + slice-2c unit tests).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): wire FpDiv into blast_word"
```

---

### Task 4: Admit `fp.div` through the soundness fence (`fp_stage.rs`)

`is_supported_fp_word`'s arithmetic arm (line `134`) currently matches `FpAdd | FpSub | FpMul`. Extend it to also include `FpDiv` (identical `(RM, F, F)` shape check). `fp_atom_is_supported` recurses through `is_supported_fp_word`, so it needs **no** change. Flip the existing `fp_div_word_is_not_supported` test (now wrong) into a positive test, and add an `fp.sqrt`-fenced negative test to preserve "future ops default to fenced" coverage.

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs`

**Interfaces:**
- Extends: `is_supported_fp_word(ctx, t) -> bool` (private). Signature unchanged; one new accepted word shape (`FpDiv`).

- [ ] **Step 1: Update the tests (flip the stale negative test, add a fenced sibling)**

In the `tests` module of `fp_stage.rs`, replace `fp_div_word_is_not_supported` (the test at line `289`) with these two tests:

```rust
    #[test]
    fn fp_div_word_is_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let y = fp_var(&mut ctx, "y");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let div = ctx.mk_app(Op::Builtin(BuiltinOp::FpDiv), &[rne, x, y]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[div]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.div is in scope as of slice 2c");
    }

    #[test]
    fn fp_sqrt_word_is_not_supported() {
        let mut ctx = Context::new();
        let x = fp_var(&mut ctx, "x");
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let sqrt = ctx.mk_app(Op::Builtin(BuiltinOp::FpSqrt), &[rne, x]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[sqrt]).unwrap();
        let atoms = collect_fp_atoms(&ctx, &[isnan]);
        assert!(!fp_atoms_fully_supported(&ctx, &atoms), "fp.sqrt stays fenced until slice 2c'");
    }
```

> `fp.sqrt` is `(RM, F)` — a two-argument app (one RM + one FP operand), unlike the three-argument arithmetic ops. Match the `fp_var` / `collect_fp_atoms` / `fp_atoms_fully_supported` helper names used verbatim by the existing `fp_mul_word_is_supported` test — read it first; if any differ, use the landed names.

- [ ] **Step 2: Run tests to verify the new state**

Run: `cargo test -p shinri-solver --lib fp_stage`
Expected: `fp_div_word_is_supported` FAILS (fp.div not yet admitted); `fp_sqrt_word_is_not_supported` PASSES already.

- [ ] **Step 3: Extend `is_supported_fp_word`**

In `fp_stage.rs`, change the arithmetic arm (line `134`) to include `FpDiv`:

```rust
        // FpAdd / FpSub / FpMul / FpDiv: (RM, F, F). RM operand must be a RoundingMode
        // term (literal const or nullary RM variable); both FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpAdd | BuiltinOp::FpSub | BuiltinOp::FpMul | BuiltinOp::FpDiv), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 3
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
                && is_supported_fp_word(ctx, kids[2])
        }
```

Update the doc comment on `is_supported_fp_word` (lines `111`–`114`) to mention `FpDiv` is in scope as of slice 2c, and the `// Anything else (FpDiv, FpFma, ...)` comment at line `141` to drop `FpDiv` (now `// Anything else (FpFma, FpSqrt, FpRem, ...)`).

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-solver --lib fp_stage`
Expected: PASS — `fp_div_word_is_supported`, `fp_sqrt_word_is_not_supported`, plus the existing `fp_add_word_is_supported`, `fp_mul_word_is_supported`, `fp_add_with_symbolic_rm_is_supported`, `fp_mixed_with_bv_is_fenced`.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): admit fp.div words through the FP soundness fence"
```

---

### Task 5: End-to-end witness + symbolic-RM SAT tests (`fp_e2e.rs`)

Prove the whole seam: parse a script with `fp.div` → SAT/UNSAT → `get-model` round-trip, plus a symbolic-RM query and the new **divide-by-zero** path on a symbolic finite operand. Uses the `(_ +oo 8 24)` / `(_ +zero 8 24)` / `(_ -oo 8 24)` special forms (NOT `(fp #b…)` literals, which route through `FpFromBits` and trip the fence — see the ENCODING NOTE at the top of `fp_e2e.rs`).

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs`

**Interfaces:**
- Consumes: the existing `fn run(src: &str) -> (SolveOutcome, String)` helper (returns the outcome and the rendered model/response string) and `SolveOutcome`.

- [ ] **Step 1: Write the failing tests**

Append to `fp_e2e.rs` (mirroring the slice-2b `fp_mul_*` tests' style). All operands are specials or unconstrained variables, so nothing routes through `(fp #b…)`.

```rust
// ── Slice-2c end-to-end: fp.div SAT/UNSAT + symbolic-RM + divByZero + get-model ──

#[test]
fn fp_div_inf_by_zero_is_inf_sat() {
    // SAT: fp.div(RNE, +inf, +zero) = +inf, and x asserted = +inf.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.div RNE (_ +oo 8 24) (_ +zero 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_div_zero_by_zero_is_nan_sat() {
    // SAT: fp.div(RNE, +zero, +zero) = NaN.
    let src = "\
(set-logic QF_FP)
(assert (fp.isNaN (fp.div RNE (_ +zero 8 24) (_ +zero 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_div_zero_by_zero_not_zero_unsat() {
    // UNSAT: 0/0 is NaN, and NaN is never fp.eq to +zero.
    let src = "\
(set-logic QF_FP)
(assert (fp.eq (fp.div RNE (_ +zero 8 24) (_ +zero 8 24)) (_ +zero 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_div_by_zero_symbolic_finite_sat() {
    // SAT: a normal y divided by +zero is ±inf (divByZero). Solver picks y normal.
    let src = "\
(set-logic QF_FP)
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isNormal y))
(assert (fp.isInfinite (fp.div RNE y (_ +zero 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_div_symbolic_rm_sat() {
    // SAT: ∃ rounding mode rm. fp.eq x (fp.div rm +inf +zero); +inf/+0 = +inf for any rm.
    let src = "\
(set-logic QF_FP)
(declare-fun rm () RoundingMode)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.div rm (_ +oo 8 24) (_ +zero 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_div_sat_get_model_round_trip() {
    // After SAT, the model must render x = +inf. (+inf / +zero = +inf, exact.)
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.div RNE (_ +oo 8 24) (_ +zero 8 24))))
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

> If `fp.isNormal`/`fp.isInfinite`/`fp.isNaN` render under slightly different keywords in this codebase's parser, match the spellings used by the landed slice-2b `fp_mul_*` e2e tests — read them first.

- [ ] **Step 2: Run tests to verify they pass**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS for all six new tests (plus the pre-existing slice-1/2a/2b e2e tests). If any returns `Unknown`, the fence (Task 4) or wiring (Task 3) is incomplete — fix there, not by weakening the test.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): end-to-end fp.div SAT/UNSAT + symbolic-RM + divByZero + get-model"
```

---

### Task 6: Differential-vs-z3 oracle over `fp.div` (`fp_oracle.rs`)

Add a `fp.div` generator + differential test, mirroring the existing `gen_mul_script` / `differential_qf_fp_mul`. Reuses `z3_outcome_arith`, `RMS`, `Lcg`, `N_ITERS`, `shinri_outcome`.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs`

**Interfaces:**
- Consumes: `Lcg`, `RMS`, `N_ITERS`, `shinri_outcome`, `z3_outcome_arith` (all already in the file).
- Produces: `fn gen_div_script(rng: &mut Lcg) -> String` and `#[test] fn differential_qf_fp_div()`.

- [ ] **Step 1: Add the div generator + differential test**

Append to `fp_oracle.rs` (inside the `#![cfg(feature = "oracle")]` module), modeled on `gen_mul_script` but emitting `fp.div`:

```rust
/// Generate a random QF_FP script with fp.div over all five rounding modes.
/// Declares three fp32 variables (x, y, z) and optionally a symbolic rounding
/// mode; builds 1–3 assertions mixing fp.div with fp.eq/=/fp.isNaN atoms, some
/// negated, so both SAT and UNSAT witnesses arise across iterations.
fn gen_div_script(rng: &mut Lcg) -> String {
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
        let term = format!("(fp.div {} x y)", rm(rng));
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
fn differential_qf_fp_div() {
    let mut rng = Lcg(0x00D1_F00D_2C3D);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_div_script(&mut rng);
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
                "QF_FP div DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
        }
    }
    println!("differential_qf_fp_div: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}
```

> `0x00D1_F00D_2C3D` is a fresh, valid-hex seed distinct from the mul test's `0x00B0_0B5_FACE` and the add/sub test's seed. `z3_outcome_arith` forwards every `(declare-fun …)`/`(assert …)` line verbatim (generator-agnostic), so no z3-driver change is needed.

- [ ] **Step 2: Run the oracle (requires z3 on PATH)**

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_div -- --nocapture`
Expected: PASS, printing nonzero `sat` and `unsat` counts and zero disagreements. If z3 is unavailable in this environment, the test is skipped by the feature gate — note that in the task report and run it wherever z3 is present.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential-vs-z3 oracle for fp.div over all five modes"
```

---

### Task 7: Full workspace non-regression sweep + clippy

**Files:** none (verification only).

- [ ] **Step 1: Run the whole workspace test suite**

Run: `cargo test --workspace`
Expected: PASS — all crates green, QF_BV and QF_FP slice-1/2a/2b paths untouched.

- [ ] **Step 2: Run clippy (the repo's lint gate)**

Run: `cargo clippy --workspace --all-targets`
Expected: no new warnings in `shinri-fp` / `shinri-solver`. Fix any introduced by the new code (unused imports, needless clones/ranges) and re-run.

- [ ] **Step 3: Final commit (if clippy fixes were needed)**

```bash
git add -A
git commit -m "chore(fp): clippy cleanups for slice-2c div"
```

---

## Self-Review

**1. Spec coverage** (against `2026-06-26-shinri-qffp-slice2c-div-design.md`):
- §2 file changes: `blast/div.rs` → Task 2; `blast/mod.rs` → Task 2; `reference.rs` `ref_div` → Task 1; `lib.rs` `FpDiv` arm → Task 3; `fp_stage.rs` fence → Task 4. ✓
- §3 shared `Operand` reused as-is (no lift task) — Task 2 imports from `blast/operand.rs`. ✓
- §4 datapath: Step A pre-normalize → Task 2 `prenormalize`; Step B divide (`udivurem`, `W=2·sb+2`, `F=sb+2`) → Task 2; Step C normalize + GRS + remainder→sticky → Task 2; Step D exponent `exp_x_n - exp_y_n + (sb-1) - lz` → Task 2; Step E round → Task 2; Step F special-case mux → Task 2 `special_case`. Exponent-headroom checkpoint → Task 2 Step 4 note. ✓
- §4.6 / §5 divide-by-zero → ±∞ table → Task 1 `ref_div` arms + Task 2 `special_case` (`want_inf` includes `y_zero AND NOT x_zero`). All ten IEEE class combinations covered by the `(3,5)` exhaustive (Tasks 1,2). ✓
- §6 fence wiring (`blast_word` `FpDiv` → Task 3; `is_supported_fp_word` arm → Task 4; `fp_atom_is_supported` recurses, no change). ✓
- §7 tests: tiny-exhaustive + Float32 vs `ref_div` (Tasks 1,2); differential z3 (Task 6); e2e SAT/UNSAT + symbolic-RM + get-model + divByZero (Task 5). ✓
- §8 soundness: `fp.div` admitted only after bit-identical validation; everything else stays `Unknown` (Task 4 + the `fp_sqrt_word_is_not_supported` guard). ✓

**2. Placeholder scan:** No "TBD"/"implement later". Every code step shows complete code; every test step shows assertions. The exponent-headroom note is an explicit, test-gated fallback, not deferred work.

**3. Type consistency:** `ref_div(eb, sb, &a, &b, mode) -> Integer` defined Task 1, used Tasks 1,2. `fp_div(b, x, y, rm, eb, sb) -> Vec<BitLit>` defined Task 2, called identically Task 3. `prenormalize(b, sig, exp, sbu, ew) -> (Vec<BitLit>, Vec<BitLit>)` and `special_case(b, normal, ox, oy, res_sign, eb, sb)` are div-local to Task 2 (its `special_case` is a separate module-private function from `add.rs`/`mul.rs`'s same-named ones — no collision). `udivurem(b, dividend, divisor) -> (Vec<BitLit>, Vec<BitLit>)`, `lzc(b, bits) -> Vec<BitLit>`, `bvshl`/`bvadd`/`bvsub`, `RmSel`, `ExtFp`, `exp_w`, `round`, and the `operand` items are reused unchanged with their landed signatures. `run(src) -> (SolveOutcome, String)` (Task 5) and `z3_outcome_arith`/`RMS`/`Lcg`/`N_ITERS`/`shinri_outcome` (Task 6) match the landed file symbols. Internal width invariant checked: `W = 2·sb+2`, `F = sb+2`, `W-sb-2 = sb ≥ 0`, `lz ∈ {sb-1, sb}` so `quot_n[W-sb-1]`/`quot_n[W-sb-2]` are real bits. ✓
