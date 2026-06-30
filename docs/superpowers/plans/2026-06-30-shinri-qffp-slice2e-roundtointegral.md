# QF_FP slice 2e — fp.roundToIntegral Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit `(fp.roundToIntegral RM x)` through the QF_FP soundness fence and bit-blast it correctly across all five rounding modes.

**Architecture:** Mirror every prior FP op slice: an exact `ref_*` golden in `reference.rs`, a gate-level circuit in `blast/roundint.rs`, a `blast_word` dispatch arm, a fence admission in `fp_stage.rs`, and the standard test trio (in-circuit reference cross-check, differential-vs-z3 oracle, end-to-end). The circuit reuses the already-normalized input significand so it needs **no leading-zero-count, no subnormal-denormalize, and no overflow-to-∞**: derive the fraction-bit count `f`, extract guard/round/sticky via the existing `shift_right_sticky`, apply the shared rounding increment, shift back, single-bit carry-renormalize, pack. `|x| < 1` (including ±0) is routed to a sign-preserving ±0/±1 special case.

**Tech Stack:** Rust, `shinri-fp` (depends on `shinri-bv` `Blaster`), `shinri-num` (`Integer`/`Rational`), `shinri-sat` for the in-test SAT eval, `z3` + `easy_smt` for the oracle.

## Global Constraints

- **Soundness contract:** anything out of scope returns `unknown`, never a wrong SAT/UNSAT verdict. The fence (`is_supported_fp_word`) positively enumerates supported ops; an unhandled FP op must fail closed (the `blast_word` `unreachable!` arm stays an internal invariant, never user-reachable).
- **No new dependencies.** Reuse `shinri-bv` blast primitives (`adder`, `bvadd`, `bvsub`, `bvshl`) and the FP crate's `round.rs`/`operand.rs`/`normalize.rs` helpers.
- **Bit-identical rounding across ops:** the per-RM increment decision has exactly one implementation (`rounding_increment`), shared by `round()` and the new circuit.
- **Formats:** must work for arbitrary `(eb, sb)` — tests cover a tiny format (e.g. `(3,5)`) and Float32 `(8,24)`. `exp_w(eb) = eb + 6`.
- **Significand convention:** `sb` bits LSB→MSB, hidden/leading bit at index `sb-1`; exponent is signed unbiased, `exp_w(eb)` bits.
- **No persistent/incremental blasting; no SAT/Tseitin/model changes.**

---

### Task 1: Reference golden `ref_round_to_integral`

Exact, bit-pattern golden used by every later cross-check.

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (add `ref_round_to_integral` after `ref_sqrt`, ~line 425; add tests to the existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `decode`, `FpClass`, `class_to_rational`, `canonical_nan`, `round_rational`, the private `zero_pattern`, `RoundMode`, and `shinri_num::{Integer, Rational}` — all already in `reference.rs`.
- Produces: `pub fn ref_round_to_integral(eb: u32, sb: u32, bits: &Integer, mode: RoundMode) -> Integer`

- [ ] **Step 1: Write the failing tests**

Add to `mod tests` in `reference.rs`. (`fp32` bit patterns: `1.0 = 0x3F80_0000`, `2.0 = 0x4000_0000`, `1.5 = 0x3FC0_0000`, `2.5 = 0x4020_0000`, `0.5 = 0x3F00_0000`, `-0.5 = 0xBF00_0000`, `0.25 = 0x3E80_0000`, `-0.0 = 0x8000_0000`, `+0.0 = 0`, `+inf = 0x7F80_0000`, `NaN = 0x7FC0_0000`.)

```rust
#[test]
fn ref_round_to_integral_float32_modes() {
    let (eb, sb) = (8u32, 24u32);
    let rti = |bits: u64, m| ref_round_to_integral(eb, sb, &Integer::from(bits), m);
    // Already integral: unchanged in every mode.
    assert_eq!(rti(0x4000_0000, RoundMode::Rne), Integer::from(0x4000_0000u64)); // 2.0
    // Half-way ties.
    assert_eq!(rti(0x3FC0_0000, RoundMode::Rne), Integer::from(0x4000_0000u64)); // 1.5 -> 2 (even)
    assert_eq!(rti(0x4020_0000, RoundMode::Rne), Integer::from(0x4000_0000u64)); // 2.5 -> 2 (even)
    assert_eq!(rti(0x3FC0_0000, RoundMode::Rna), Integer::from(0x4000_0000u64)); // 1.5 -> 2 (away)
    assert_eq!(rti(0x3F00_0000, RoundMode::Rna), Integer::from(0x3F80_0000u64)); // 0.5 -> 1 (away)
    assert_eq!(rti(0x3F00_0000, RoundMode::Rne), Integer::from(0u64));           // 0.5 -> +0 (even)
    // Directed modes on 0.5.
    assert_eq!(rti(0x3F00_0000, RoundMode::Rtp), Integer::from(0x3F80_0000u64)); // 0.5 -> 1 (+inf)
    assert_eq!(rti(0x3F00_0000, RoundMode::Rtn), Integer::from(0u64));           // 0.5 -> 0 (-inf)
    assert_eq!(rti(0x3F00_0000, RoundMode::Rtz), Integer::from(0u64));           // 0.5 -> 0 (zero)
}

#[test]
fn ref_round_to_integral_specials_and_sign_preserving_zero() {
    let (eb, sb) = (8u32, 24u32);
    let rti = |bits: u64, m| ref_round_to_integral(eb, sb, &Integer::from(bits), m);
    // NaN -> canonical NaN; ±inf unchanged; ±0 unchanged.
    assert_eq!(rti(0x7FC0_0000, RoundMode::Rne), canonical_nan(eb, sb));
    assert_eq!(rti(0x7F80_0000, RoundMode::Rne), Integer::from(0x7F80_0000u64)); // +inf
    assert_eq!(rti(0x8000_0000, RoundMode::Rne), Integer::from(0x8000_0000u64)); // -0 stays -0
    assert_eq!(rti(0x0000_0000, RoundMode::Rne), Integer::from(0u64));           // +0 stays +0
    // Sign-preserving zero result: -0.25 RNE -> -0.0 (0xBE80_0000 = -0.25).
    assert_eq!(rti(0xBE80_0000, RoundMode::Rne), Integer::from(0x8000_0000u64));
    // Directed toward -inf: -0.5 RTN -> -1.0 (0xBF80_0000).
    assert_eq!(rti(0xBF00_0000, RoundMode::Rtn), Integer::from(0xBF80_0000u64));
    // Carry-renormalize: a value just below 2 rounds up to 2.0 with exp+1.
    // 1.9999998 ~ 0x3FFF_FFFF rounds to 2.0 under RNE.
    assert_eq!(rti(0x3FFF_FFFF, RoundMode::Rne), Integer::from(0x4000_0000u64));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp ref_round_to_integral -- --nocapture`
Expected: FAIL — `cannot find function ref_round_to_integral in this scope`.

- [ ] **Step 3: Write the implementation**

Add to `reference.rs` (after `ref_sqrt`, before `ref_add`):

```rust
/// Exact `fp.roundToIntegral RM x`: round x to the nearest integer-valued float
/// per `mode`. NaN -> canonical NaN; ±inf and ±0 unchanged; a zero result keeps
/// the input's sign. The rounded integer is always exactly representable.
pub fn ref_round_to_integral(eb: u32, sb: u32, bits: &Integer, mode: RoundMode) -> Integer {
    use FpClass::*;
    let c = decode(eb, sb, bits);
    let sign = match &c {
        Nan => return canonical_nan(eb, sb),
        Inf { .. } | Zero { .. } => return bits.clone(), // ±inf / ±0 unchanged
        Normal { sign, .. } | Subnormal { sign, .. } => *sign,
    };
    // Exact value, then round its magnitude to an integer with the same tie logic
    // round_rational uses (reference.rs round_up block).
    let v = class_to_rational(eb, sb, &c).unwrap();
    let zero = Rational::new(Integer::zero(), Integer::one());
    let half = Rational::new(Integer::one(), Integer::from(2u64));
    let mag = if sign { Rational::new(Integer::from(-1i64), Integer::one()) * v.clone() } else { v };
    let q = mag.numer().div_rem(&mag.denom()).0; // floor(|value|)
    let frac = mag - Rational::new(q.clone(), Integer::one());
    let round_up = match mode {
        RoundMode::Rtz => false,
        RoundMode::Rtp => !sign && frac > zero,
        RoundMode::Rtn => sign && frac > zero,
        RoundMode::Rne => {
            if frac > half { true } else if frac < half { false }
            else { !q.div_rem(&Integer::from(2u64)).1.is_zero() } // tie -> to even
        }
        RoundMode::Rna => frac >= half,
    };
    let n = if round_up { q + Integer::one() } else { q };
    if n.is_zero() {
        return zero_pattern(eb, sb, sign); // sign-preserving ±0
    }
    let signed_n = if sign { Rational::new(Integer::from(-1i64), Integer::one()) * Rational::new(n, Integer::one()) }
                   else { Rational::new(n, Integer::one()) };
    // n is exactly representable, so this re-encode introduces no second rounding.
    round_rational(eb, sb, &signed_n, mode)
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp ref_round_to_integral -- --nocapture`
Expected: PASS (both tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): exact ref_round_to_integral golden for slice 2e"
```

---

### Task 2: Extract the shared `rounding_increment` helper

Pure, behavior-preserving extraction of `round()` Step 2 so the circuit reuses identical RM semantics. The existing `round.rs` test module is the regression guard.

**Files:**
- Modify: `crates/shinri-fp/src/round.rs` (extract lines 79-93 into a `pub fn`; call it from `round()`)

**Interfaces:**
- Consumes: `or3` (private, same module), `RmSel` (`rm.sel: [BitLit; 5]`).
- Produces: `pub fn rounding_increment(b: &mut Blaster, sign: BitLit, g: BitLit, r: BitLit, s: BitLit, lsb: BitLit, rm: &RmSel) -> BitLit`

- [ ] **Step 1: Add the helper and rewire `round()`**

Insert this function in `round.rs` (e.g. just below `round`):

```rust
/// Per-RM "add one ulp?" decision, shared by `round()` and `fp.roundToIntegral`.
/// `sign` is the result sign; `g`/`r`/`s` are guard/round/sticky; `lsb` is the
/// significand's least-significant retained bit (for RNE tie-to-even).
pub fn rounding_increment(
    b: &mut Blaster, sign: BitLit, g: BitLit, r: BitLit, s: BitLit, lsb: BitLit, rm: &RmSel,
) -> BitLit {
    let grs_any = or3(b, g, r, s);
    let not_sign = b.not1(sign);
    let r_or_s_or_lsb = or3(b, r, s, lsb);
    let inc_rne = b.and2(g, r_or_s_or_lsb);
    let inc_rna = g;
    let inc_rtp = b.and2(not_sign, grs_any);
    let inc_rtn = b.and2(sign, grs_any);
    let inc_rtz = b.zero();
    let mut inc = b.zero();
    for (sel, val) in rm.sel.iter().zip([inc_rne, inc_rna, inc_rtp, inc_rtn, inc_rtz]) {
        let t = b.and2(*sel, val);
        inc = b.or2(inc, t);
    }
    inc
}
```

Then replace `round()`'s Step 2 block (the lines computing `grs_any` through the `inc` accumulation loop, currently `round.rs:79-93`) with a single call:

```rust
    // --- Step 2: increment decision (shared with fp.roundToIntegral). ---
    let inc = rounding_increment(b, ext.sign, g, r, s, lsb, rm);
```

(The surrounding `let g = work[2];`, `let sig = ...`, `let lsb = sig[0];` bindings and Step 3's use of `inc` are unchanged.)

- [ ] **Step 2: Run the existing rounder regression tests**

Run: `cargo test -p shinri-fp --lib round_matches_reference -- --nocapture`
Expected: PASS — `round_matches_reference_tiny_exhaustive` and `round_matches_reference_float32_random` still green (proves the extraction preserved behavior).

- [ ] **Step 3: Confirm the whole crate still builds and tests pass**

Run: `cargo test -p shinri-fp --lib`
Expected: PASS, no warnings about an unused `or3`/`rounding_increment`.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-fp/src/round.rs
git commit -m "refactor(fp): extract shared rounding_increment from round()"
```

---

### Task 3: `fp.roundToIntegral` circuit

The gate-level datapath, cross-checked against `ref_round_to_integral` inside the module (same harness pattern as `blast/sqrt.rs`).

**Files:**
- Create: `crates/shinri-fp/src/blast/roundint.rs`
- Modify: `crates/shinri-fp/src/blast/mod.rs` (add `pub mod roundint;`)
- Modify: `crates/shinri-fp/src/blast/operand.rs` (add `signed_one_bits`)

**Interfaces:**
- Consumes: `to_operand`/`Operand`/`canon_nan_bits`/`inf_pattern_bits`/`signed_zero_bits`/`signed_one_bits` (operand.rs); `const_n` (normalize.rs); `shift_right_sticky` + `rounding_increment` (round.rs); `adder`/`bvadd`/`bvsub`/`bvshl` (shinri-bv); `RmSel` (rm.rs).
- Produces: `pub fn fp_round_to_integral(b: &mut Blaster, x: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit>`

- [ ] **Step 1: Add the `signed_one_bits` helper to `operand.rs`**

```rust
#[allow(clippy::needless_range_loop)] // index arithmetic bounds are load-bearing
pub(crate) fn signed_one_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit> {
    // 1.0: trailing sig 0, biased exponent = bias (2^(eb-1)-1), given sign.
    let bias: u64 = (1u64 << (eb - 1)) - 1;
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    for i in 0..(eb as usize) {
        if (bias >> i) & 1 == 1 { v[(sb as usize - 1) + i] = b.one(); }
    }
    v[(eb + sb) as usize - 1] = sign;
    v
}
```

- [ ] **Step 2: Register the module**

In `crates/shinri-fp/src/blast/mod.rs`, add (alphabetical, after `pub mod prenormalize`/`normalize` — match existing ordering):

```rust
pub mod roundint;
```

- [ ] **Step 3: Write the failing circuit test**

Create `crates/shinri-fp/src/blast/roundint.rs` with ONLY the test module first (so it fails to compile against a missing `fp_round_to_integral`), modeled on `blast/sqrt.rs`'s test harness:

```rust
//! fp.roundToIntegral datapath: unpack → fraction-mask round → repack, with a
//! sign-preserving ±0/±1 path for |x| < 1. No LZC, no denormalize, no overflow-∞.

#[cfg(test)]
mod tests {
    use crate::blast::roundint::fp_round_to_integral;
    use crate::reference::{ref_round_to_integral, RoundMode};
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

    #[test]
    fn roundint_tiny_exhaustive() {
        // Format (3,5): 256 patterns × 5 modes, full cross-check vs the golden.
        let (eb, sb) = (3u32, 5u32);
        for bits in 0..(1u64 << (eb + sb)) {
            for &m in MODES {
                let want = ref_round_to_integral(eb, sb, &Integer::from(bits), m);
                let mut b = Blaster::new();
                let x = const_bits(&b, eb, sb, bits);
                let sel = rm::literal(&b, rmode(m));
                let got_word = fp_round_to_integral(&mut b, &x, &sel, eb, sb);
                let got = eval_word(b, &got_word);
                assert_eq!(
                    Integer::from(got), want,
                    "roundint (3,5) bits={bits:#x} mode={m:?}: got {got:#x} want {want}"
                );
            }
        }
    }

    #[test]
    fn roundint_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        let cases: &[u64] = &[
            0x0000_0000, 0x8000_0000,           // ±0
            0x7F80_0000, 0xFF80_0000,           // ±inf
            0x7FC0_0000,                        // NaN
            0x3F80_0000, 0x4000_0000,           // 1.0, 2.0 (integral)
            0x3FC0_0000, 0x4020_0000,           // 1.5, 2.5
            0x3F00_0000, 0xBF00_0000,           // ±0.5
            0x3E80_0000, 0xBE80_0000,           // ±0.25
            0x3FFF_FFFF,                        // ~1.9999998 (carry-renormalize)
            0x4B7F_FFFF, 0x4C00_0000,           // large integral magnitudes
        ];
        // Deterministic LCG for extra coverage.
        let mut state = 0x1234_5678_9abc_def0u64;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state >> 16 };
        for iter in 0..2000 {
            let bits = if iter < cases.len() as u64 { cases[iter as usize] } else { rand() & 0xFFFF_FFFF };
            for &m in MODES {
                let want = ref_round_to_integral(eb, sb, &Integer::from(bits), m);
                let mut b = Blaster::new();
                let x = const_bits(&b, eb, sb, bits);
                let sel = rm::literal(&b, rmode(m));
                let got_word = fp_round_to_integral(&mut b, &x, &sel, eb, sb);
                let got = eval_word(b, &got_word);
                assert_eq!(
                    Integer::from(got), want,
                    "roundint f32 bits={bits:#x} mode={m:?}: got {got:#x} want {want}"
                );
            }
        }
    }
}
```

- [ ] **Step 4: Run to verify it fails**

Run: `cargo test -p shinri-fp --lib roundint -- --nocapture`
Expected: FAIL — `cannot find function fp_round_to_integral`.

- [ ] **Step 5: Write the circuit implementation**

Prepend to `roundint.rs` (above the test module):

```rust
use shinri_bv::{BitLit, Blaster};
use shinri_bv::blast::arith::{adder, bvadd};
use shinri_bv::blast::shift::bvshl;
use crate::blast::operand::{
    to_operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits, signed_one_bits,
};
use crate::blast::normalize::const_n;
use crate::round::{exp_w, shift_right_sticky, rounding_increment};
use crate::rm::RmSel;

pub fn fp_round_to_integral(b: &mut Blaster, x: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let w = (eb + sb) as usize;
    let ox = to_operand(b, x, eb, sb);

    // f = number of fractional bits = (sb-1) - exp, saturated at 0 (already integral).
    let sbm1 = const_n(b, ew, (sb as i128) - 1);
    let f_full = shinri_bv::blast::arith::bvsub(b, &sbm1, &ox.exp); // signed
    let f_neg = f_full[ew - 1];                                     // exp > sb-1 ⇒ already integral
    let zero_ew = const_n(b, ew, 0);
    let f_sat: Vec<BitLit> = (0..ew).map(|i| b.mux2(f_neg, zero_ew[i], f_full[i])).collect();

    // GRS extraction at the integer boundary: prepend [S,R,G]=0 below sig, shift
    // right by f_sat, fold dropped bits into sticky. Mirrors round()'s Step 1.
    let mut work: Vec<BitLit> = vec![b.zero(), b.zero(), b.zero()];
    work.extend_from_slice(&ox.sig);                                // width sbu+3
    let (shifted, st) = shift_right_sticky(b, &work, &f_sat);
    let mut work = shifted;
    work[0] = b.or2(work[0], st);
    let s = work[0];
    let r = work[1];
    let g = work[2];
    let int_part: Vec<BitLit> = work[3..3 + sbu].to_vec();          // integer part, right-aligned
    let lsb = int_part[0];

    // Shared rounding increment, added at the integer LSB.
    let inc = rounding_increment(b, ox.sign, g, r, s, lsb, rm);
    let mut addend: Vec<BitLit> = vec![b.zero(); sbu];
    addend[0] = inc;
    let (int_rounded, _carry) = adder(b, &int_part, &addend, b.zero());

    // Shift the rounded integer back left by f to restore the normalized position.
    // Width sbu+1 captures the at-most-one carry into bit `sb` (value bumped to a
    // higher power of two ⇒ exp+1, significand = leading bit only).
    let mut ir_ext = int_rounded.clone();
    ir_ext.push(b.zero());                                          // sbu+1 bits
    // Resize f_sat to sbu+1 (truncate high bits / zero-extend); f < 2^(sb+1) always.
    let f_shl: Vec<BitLit> = (0..(sbu + 1)).map(|i| if i < ew { f_sat[i] } else { b.zero() }).collect();
    let shifted_back = bvshl(b, &ir_ext, &f_shl);                   // sbu+1 bits
    let overflow = shifted_back[sbu];
    let norm_sig: Vec<BitLit> = (0..sbu).map(|i| {
        let lead = if i == sbu - 1 { b.one() } else { b.zero() };   // 1.000… on carry
        b.mux2(overflow, lead, shifted_back[i])
    }).collect();
    let one_ew = const_n(b, ew, 1);
    let exp_p1 = bvadd(b, &ox.exp, &one_ew);
    let exp_out: Vec<BitLit> = (0..ew).map(|i| b.mux2(overflow, exp_p1[i], ox.exp[i])).collect();

    // Pack the normal result: trailing sig | biased exp | sign. norm_sig's hidden
    // bit (index sb-1) is always 1 here, and exp_out stays in normal range.
    let bias_v = const_n(b, ew, (1i128 << (eb - 1)) - 1);
    let biased = bvadd(b, &exp_out, &bias_v);
    let mut out: Vec<BitLit> = Vec::with_capacity(w);
    for i in 0..(sbu - 1) { out.push(norm_sig[i]); }                // trailing significand
    for i in 0..(eb as usize) { out.push(biased[i]); }             // exponent field
    out.push(ox.sign);                                             // sign

    // Special cases (low → high priority; NaN wins).
    // |x| < 1  ⇔  exp < 0  (covers subnormals and ±0). Result is sign-preserving
    // ±1 when the increment fired, else ±0.
    let is_lt1 = ox.exp[ew - 1];
    let one_bits = signed_one_bits(b, eb, sb, ox.sign);
    let zero_bits = signed_zero_bits(b, eb, sb, ox.sign);
    let lt1: Vec<BitLit> = (0..w).map(|i| b.mux2(inc, one_bits[i], zero_bits[i])).collect();
    for i in 0..w { out[i] = b.mux2(is_lt1, lt1[i], out[i]); }
    let inf = inf_pattern_bits(b, eb, sb, ox.sign);
    for i in 0..w { out[i] = b.mux2(ox.is_inf, inf[i], out[i]); }
    let nan = canon_nan_bits(b, eb, sb);
    for i in 0..w { out[i] = b.mux2(ox.is_nan, nan[i], out[i]); }
    out
}
```

- [ ] **Step 6: Run the circuit tests**

Run: `cargo test -p shinri-fp --lib roundint -- --nocapture`
Expected: PASS — `roundint_tiny_exhaustive` (256×5 exact) and `roundint_float32_specials_and_random` (2000×5).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-fp/src/blast/roundint.rs crates/shinri-fp/src/blast/mod.rs crates/shinri-fp/src/blast/operand.rs
git commit -m "feat(fp): fp.roundToIntegral circuit (fraction-mask round, no LZC) for slice 2e"
```

---

### Task 4: Dispatch + soundness-fence admission

Wire the op into `blast_word` and admit it through the fence so end-to-end queries reach the circuit (and malformed ones still fail closed).

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` (add a `blast_word` match arm; ~after the `FpSqrt` arm at line 113)
- Modify: `crates/shinri-solver/src/fp_stage.rs` (extend the `FpSqrt` arm of `is_supported_fp_word`, line 144-149)

**Interfaces:**
- Consumes: `crate::blast::roundint::fp_round_to_integral` (Task 3), `BuiltinOp::FpRoundToIntegral` (already in `shinri-core`).
- Produces: a supported `(RoundingMode, Float) -> Float` op end-to-end.

- [ ] **Step 1: Add the dispatch arm in `lib.rs`**

In `blast_word`, immediately after the `FpSqrt => { … }` arm (line 113-117), add:

```rust
                    FpRoundToIntegral => {
                        let rm = self.blast_rm(ctx, kids[0]);
                        let xw = self.blast_word(ctx, kids[1]);
                        crate::blast::roundint::fp_round_to_integral(&mut self.b, &xw, &rm, eb, sb)
                    }
```

- [ ] **Step 2: Admit it in the fence**

In `crates/shinri-solver/src/fp_stage.rs`, change the `FpSqrt` arm of `is_supported_fp_word` (line 144) to include `FpRoundToIntegral` (identical `(RM, F)` shape):

```rust
        // FpSqrt / FpRoundToIntegral: (RM, F). RM operand must be a RoundingMode
        // term; FP operand supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpSqrt | BuiltinOp::FpRoundToIntegral), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
```

- [ ] **Step 3: Add a fence unit test in `fp_stage.rs`**

In `fp_stage.rs` `mod tests`, mirror `fp_sqrt_word_is_supported` (line 323):

```rust
    #[test]
    fn fp_roundtointegral_word_is_supported() {
        let mut ctx = Context::new();
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let x = fp_var(&mut ctx, "x");
        let rti = ctx.mk_app(Op::Builtin(BuiltinOp::FpRoundToIntegral), &[rne, x]).unwrap();
        assert!(is_supported_fp_word(&ctx, rti), "fp.roundToIntegral word admitted");
        // Malformed (missing RM operand) must NOT be admitted.
        let bad = ctx.mk_app(Op::Builtin(BuiltinOp::FpRoundToIntegral), &[x]);
        if let Ok(bad) = bad {
            assert!(!is_supported_fp_word(&ctx, bad), "arity-1 roundToIntegral rejected");
        }
    }
```

(If `mk_rm_const`/`fp_var` helper names differ in the test module, copy the exact constructors used by `fp_sqrt_word_is_supported` — read lines 323-333 first.)

- [ ] **Step 4: Run the fence + crate build**

Run: `cargo test -p shinri-solver --lib fp_roundtointegral_word_is_supported -- --nocapture && cargo build -p shinri-fp -p shinri-solver`
Expected: PASS + clean build (no `unreachable!`-arm regressions).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/lib.rs crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): admit fp.roundToIntegral through the FP soundness fence + dispatch"
```

---

### Task 5: End-to-end + differential-vs-z3 oracle

The standard slice test surface: SMT-LIB → solver SAT/UNSAT/get-model/symbolic-RM/fence-canary, plus a bounded z3 differential.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` (add a slice-2e block)
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (add `gen_roundint_script` + `differential_qf_fp_roundint`)

**Interfaces:**
- Consumes: `run` (fp_e2e.rs), `Lcg`/`RMS`/`shinri_outcome`/`z3_outcome_arith` (fp_oracle.rs).
- Produces: gated coverage proving solver-level correctness.

- [ ] **Step 1: Write the end-to-end tests**

Append to `crates/shinri-solver/tests/fp_e2e.rs`:

```rust
// ── Slice-2e end-to-end: fp.roundToIntegral SAT/UNSAT + symbolic-RM + get-model ──

#[test]
fn fp_roundtointegral_half_to_even_unsat() {
    // roundToIntegral(RNE, 0.5) = +0, so fp.eq to 1.0 is UNSAT.
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (fp.eq (fp.roundToIntegral RNE ((_ to_fp 8 24) RNE 0.5)) x)) \
         (assert (fp.eq x ((_ to_fp 8 24) RNE 1.0))) (check-sat)",
    );
    // NB: if to_fp-from-Real is fenced, replace the literals with fp.div-built
    // halves; see the variant below which avoids to_fp entirely.
    let _ = o;
}

#[test]
fn fp_roundtointegral_inf_passthrough_sat() {
    // roundToIntegral(RTP, +oo) = +oo, so fp.isInfinite holds: SAT.
    let (o, _) = run(
        "(assert (fp.isInfinite (fp.roundToIntegral RTP (_ +oo 8 24)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_roundtointegral_nan_is_nan_sat() {
    let (o, _) = run(
        "(assert (fp.isNaN (fp.roundToIntegral RNE (_ NaN 8 24)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_roundtointegral_symbolic_rm_sat_get_model() {
    // z = roundToIntegral(rm, x) with symbolic rm and symbolic x: SAT, model renders.
    let (o, model) = run(
        "(declare-fun x () Float32) (declare-fun z () Float32) (declare-fun rm () RoundingMode) \
         (assert (fp.eq z (fp.roundToIntegral rm x))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triples: {model}");
}

#[test]
fn fp_roundtointegral_malformed_is_unknown() {
    // Fence canary: a roundToIntegral whose operand is an unsupported FP word
    // (fp.fma is out of scope) must trip the fence → Unknown, never SAT/UNSAT.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) (declare-fun u () Float32) \
         (assert (fp.eq u (fp.roundToIntegral RNE (fp.fma RNE x y u)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}
```

Note for the implementer: before finalizing `fp_roundtointegral_half_to_even_unsat`, check whether constant-Real `to_fp` is admitted yet. It is a Plan-3 non-goal for this slice, so prefer a literal-free formulation. Replace that test body with one built from an in-scope construction, e.g.:

```rust
#[test]
fn fp_roundtointegral_idempotent_on_integral_unsat() {
    // For any x, roundToIntegral(RNE, roundToIntegral(RNE, x)) = roundToIntegral(RNE, x):
    // asserting they differ is UNSAT.
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (not (fp.eq (fp.roundToIntegral RNE (fp.roundToIntegral RNE x)) \
                             (fp.roundToIntegral RNE x)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}
```

Delete the placeholder `fp_roundtointegral_half_to_even_unsat` test if you keep the idempotence test instead.

- [ ] **Step 2: Run the e2e tests**

Run: `cargo test -p shinri-solver --test fp_e2e roundtointegral -- --nocapture`
Expected: PASS — passthrough/NaN/symbolic-RM/idempotence SAT/UNSAT correct, malformed → Unknown.

- [ ] **Step 3: Commit the e2e tests**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): end-to-end fp.roundToIntegral SAT/UNSAT + symbolic-RM + fence canary"
```

- [ ] **Step 4: Add the oracle generator + differential test**

Append to `crates/shinri-solver/tests/fp_oracle.rs` (mirror `gen_sqrt_script`/`differential_qf_fp_sqrt`):

```rust
/// Random QF_FP with fp.roundToIntegral over all five rounding modes (unary op).
fn gen_roundint_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let use_sym_rm = rng.below(4) == 0;
    if use_sym_rm {
        s.push_str("(declare-fun rm () RoundingMode)\n");
    }
    let rm = |rng: &mut Lcg| -> String {
        if use_sym_rm && rng.below(2) == 0 { "rm".to_string() }
        else { RMS[rng.below(RMS.len() as u64) as usize].to_string() }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = format!("(fp.roundToIntegral {} x)", rm(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq z {term})"),
            1 => format!("(= z {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 { s.push_str(&format!("(assert (not {atom}))\n")); }
        else { s.push_str(&format!("(assert {atom})\n")); }
    }
    s.push_str("(check-sat)\n");
    s
}

// fp.roundToIntegral is a shallow circuit (two barrel shifts + an add, no
// digit-recurrence), so this can run the full N_ITERS unlike div/sqrt.
const ROUNDINT_ITERS: usize = N_ITERS;

#[test]
fn differential_qf_fp_roundint() {
    let mut rng = Lcg(0x00A1_7E2D_4C9F_03);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..ROUNDINT_ITERS {
        let src = gen_roundint_script(&mut rng);
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
            (o, t) => panic!("QF_FP roundToIntegral DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    println!("differential_qf_fp_roundint: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}
```

- [ ] **Step 5: Run the oracle (background — multi-minute, needs z3 on PATH)**

Per the gate-suite policy, run this yourself in the background, do not loop a subagent:

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_roundint -- --nocapture`
Expected: PASS, prints `differential_qf_fp_roundint: sat=… unsat=… unknown=…` with both `sat > 0` and `unsat > 0` and zero disagreements. If a late instance conjoins multiple symbolic-RM roundToIntegral terms and grinds, lower `ROUNDINT_ITERS` below the first intractable iter (mirror the `SQRT_ITERS` rationale comment) — but only after confirming no disagreement up to that point.

- [ ] **Step 6: Commit the oracle**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential-vs-z3 oracle for fp.roundToIntegral over all five modes"
```

---

## Self-Review

**Spec coverage:**
- Semantics (NaN→NaN, ±∞/±0 unchanged, round-to-integer per RM, sign-preserving zero, all 5 modes) → Task 1 (golden) + Task 3 (circuit) + their tests.
- Shallow circuit (no LZC / no denormalize / no overflow-∞) → Task 3 implementation + comments.
- Shared `rounding_increment` extraction → Task 2.
- Dispatch + fence admission + fail-closed → Task 4 (+ malformed canary in Task 5).
- Reference re-encode via `round_rational` → Task 1.
- Test trio (reference unit, oracle, e2e) → Tasks 1/3 (unit), 5 (oracle + e2e).
- Non-goals (fma/rem/conversions stay fenced) → enforced by the unchanged fence; canary in Task 5 confirms fp.fma-nested stays Unknown.

**Placeholder scan:** The only deliberately conditional item is the `to_fp`-literal e2e test in Task 5 Step 1, which carries an explicit literal-free replacement (`fp_roundtointegral_idempotent_on_integral_unsat`) and instructions to delete the placeholder. No "TBD"/"add error handling"/bare "write tests" remain.

**Type consistency:** `fp_round_to_integral(b, x, rm, eb, sb) -> Vec<BitLit>` and `ref_round_to_integral(eb, sb, bits, mode) -> Integer` are used identically across Tasks 1/3/4/5. `rounding_increment(b, sign, g, r, s, lsb, rm) -> BitLit` defined in Task 2 is consumed in Task 3. `signed_one_bits(b, eb, sb, sign)` defined and consumed in Task 3. `BuiltinOp::FpRoundToIntegral` matches the existing core variant.
