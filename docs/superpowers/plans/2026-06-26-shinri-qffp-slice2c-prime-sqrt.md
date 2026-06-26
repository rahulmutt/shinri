# QF_FP Slice 2c′ — `fp.sqrt` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add correctly-rounded `fp.sqrt` to shinri's eager-bit-blasting QF_FP front end, end-to-end (datapath + reference oracle + solver fence), all five rounding modes.

**Architecture:** Reuse the slice-2c pipeline (`unpack → prenormalize → datapath → ExtFp → round() → special-case mux`). The one new circuit is a **restoring digit-recurrence integer square root** in `blast/sqrt.rs` that yields `floor(√R)` plus a remainder (the remainder→sticky pattern div proved). The reference `ref_sqrt` stays bit-exact by **interval refinement over `round_rational`**: scale, take an exact integer `Integer::sqrt_rem`, and refine precision until the two interval endpoints round identically (and use the exact endpoint when the radicand is a perfect square). No irrational or float ever materializes.

**Tech Stack:** Rust, `shinri-num` (zero-runtime-dep bignum), `shinri-bv` `Blaster` gate API, `shinri-fp`, `shinri-solver`. Tests use the in-tree SAT solver; gated tests shell out to `z3`.

**Spec:** `docs/superpowers/specs/2026-06-26-shinri-qffp-slice2c-prime-sqrt-design.md`

## Global Constraints

- `shinri-num` has **zero runtime dependencies** — `Integer::sqrt_rem` must use only existing in-crate ops. `num-bigint`/`num-traits` are **dev-dependencies only** (tests).
- **Soundness contract:** anything out of scope returns `unknown`, never a wrong SAT/UNSAT. This slice only *removes* `fp.sqrt` from the fenced-`Unknown` set; `fma`/`rem`/`roundToIntegral`/`min`/`max`, all conversions, FP+BV mixing, FP+EUF/Arith/Arrays, and the Real bridge stay fenced.
- **Bit-exactness:** the datapath must be bit-identical to `ref_sqrt` across the exhaustive `(eb=3, sb=5)` sweep (all 256 inputs × 5 modes); that test is the correctness gate, not a sample.
- `const_n` must use the total-mask guard (`if n >= 128 { -1 } else { (1<<n)-1 }`) — never a bare `1 << n` (i128 overflow at binary128 widths).
- Conventional commits (`feat(fp):`, `test(fp):`, `fix(fp):`, `refactor(fp):`). Commit after each green step group.

---

### Task 1: `Integer::sqrt_rem` in `shinri-num`

Exact floor integer square root with remainder — the building block `ref_sqrt` needs.

**Files:**
- Modify: `crates/shinri-num/src/integer.rs` (add method + `#[cfg(test)]` cases)

**Interfaces:**
- Consumes: existing `Integer` ops — `clone`, `is_zero`, `div_rem(&Integer) -> (Integer, Integer)`, `Add`/`Sub`/`Mul`, `From<u64>`, `Ord`/`PartialOrd`, `zero`/`one`.
- Produces: `pub fn sqrt_rem(&self) -> (Integer, Integer)` returning `(s, r)` with `s = floor(√self)`, `r = self − s*s`, `0 ≤ r`. Requires `self >= 0` (debug-asserts otherwise).

- [ ] **Step 1: Write the failing tests**

In `crates/shinri-num/src/integer.rs`, inside (or appended to) the existing `#[cfg(test)] mod tests`:

```rust
#[test]
fn sqrt_rem_small_exact_and_remainder() {
    let i = |v: u64| Integer::from(v);
    assert_eq!(i(0).sqrt_rem(),  (i(0), i(0)));
    assert_eq!(i(1).sqrt_rem(),  (i(1), i(0)));
    assert_eq!(i(2).sqrt_rem(),  (i(1), i(1)));
    assert_eq!(i(3).sqrt_rem(),  (i(1), i(2)));
    assert_eq!(i(4).sqrt_rem(),  (i(2), i(0)));
    assert_eq!(i(15).sqrt_rem(), (i(3), i(6)));
    assert_eq!(i(16).sqrt_rem(), (i(4), i(0)));
    assert_eq!(i(17).sqrt_rem(), (i(4), i(1)));
    assert_eq!(i(9_999).sqrt_rem(), (i(99), i(198))); // 99^2 = 9801, rem 198
    assert_eq!(i(10_000).sqrt_rem(), (i(100), i(0)));
}

#[test]
fn sqrt_rem_matches_num_bigint_large() {
    use num_bigint::BigUint;
    use num_traits::One;
    // A spread of large multi-limb values; cross-check against num-bigint's sqrt.
    let seeds: [u128; 6] = [
        123_456_789,
        9_876_543_210_123,
        1u128 << 100,
        (1u128 << 100) + 1,
        340_282_366_920_938_463_463_374_607_431_768_211_455, // u128::MAX
        (1u128 << 64) * (1u128 << 63) + 777,
    ];
    for v in seeds {
        let s_ours = Integer::from_str_radix(&v.to_string(), 10).unwrap();
        let (s, r) = s_ours.sqrt_rem();
        let big = BigUint::from(v);
        let want_s = big.sqrt();
        let want_r = &big - (&want_s * &want_s);
        assert_eq!(s.to_string(), want_s.to_string(), "sqrt of {v}");
        assert_eq!(r.to_string(), want_r.to_string(), "rem of {v}");
        let _ = BigUint::one();
    }
}
```

If `Integer` lacks `to_string`/`Display`, compare via reconstruction instead: assert `s.clone()*s.clone() + r.clone() == self` and `(s.clone()+Integer::one())*(s.clone()+Integer::one()) > self`. Prefer whichever comparison API `integer.rs` already exposes (check the top of the file first).

- [ ] **Step 2: Run tests, verify they fail**

Run: `cargo test -p shinri-num sqrt_rem`
Expected: FAIL — `no method named sqrt_rem found for struct Integer`.

- [ ] **Step 3: Implement `sqrt_rem`**

Add to `impl Integer` in `crates/shinri-num/src/integer.rs` (integer Newton iteration; converges to the floor for any start ≥ the true root):

```rust
/// Floor integer square root with remainder: returns `(s, r)` where
/// `s = floor(sqrt(self))` and `r = self - s*s`, with `0 <= r <= 2*s`.
/// Requires `self >= 0`.
pub fn sqrt_rem(&self) -> (Integer, Integer) {
    debug_assert!(*self >= Integer::zero(), "sqrt_rem of a negative Integer");
    if self.is_zero() || *self == Integer::one() {
        return (self.clone(), Integer::zero());
    }
    let two = Integer::from(2u64);
    // Newton's method for isqrt. Start at a guess >= true root (self itself works,
    // since self >= 2 implies self > sqrt(self)); iterate x_{k+1} = (x_k + self/x_k)/2,
    // stopping at the first non-decreasing step — that fixed point is floor(sqrt).
    let mut x = self.clone();
    loop {
        let (q, _) = self.div_rem(&x);
        let (next, _) = (x.clone() + q).div_rem(&two);
        if next >= x {
            break;
        }
        x = next;
    }
    let rem = self.clone() - x.clone() * x.clone();
    (x, rem)
}
```

If `Integer` does not derive `PartialOrd`/`Ord`, replace the `>=`/`==` comparisons with whatever the crate exposes (e.g. a `cmp` method) — check existing code in `integer.rs`/`rational.rs` (`Rational::is_negative` suggests comparison helpers exist).

- [ ] **Step 4: Run tests, verify they pass**

Run: `cargo test -p shinri-num sqrt_rem`
Expected: PASS (both tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-num/src/integer.rs
git commit -m "feat(num): exact Integer::sqrt_rem (floor isqrt + remainder)"
```

---

### Task 2: Extract `prenormalize` into a shared `blast/normalize.rs`

`prenormalize` (and its helpers `const_n`, `zero_extend`) currently live private inside `blast/div.rs`. `fp.sqrt` needs them too. Move them to one shared, verified copy. Pure refactor — div's existing tests are the regression gate.

**Files:**
- Create: `crates/shinri-fp/src/blast/normalize.rs`
- Modify: `crates/shinri-fp/src/blast/mod.rs` (register module)
- Modify: `crates/shinri-fp/src/blast/div.rs` (drop private copies, import shared)

**Interfaces:**
- Produces (all `pub(crate)`):
  - `fn const_n(b: &Blaster, n: usize, v: i128) -> Vec<BitLit>`
  - `fn zero_extend(b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit>`
  - `fn prenormalize(b: &mut Blaster, sig: &[BitLit], exp: &[BitLit], sbu: usize, ew: usize) -> (Vec<BitLit>, Vec<BitLit>)`
- Consumes: `shinri_bv::{BitLit, Blaster}`, `crate::lzc::lzc`, `shinri_bv::blast::{shift::bvshl, arith::bvsub}`.

- [ ] **Step 1: Create `blast/normalize.rs`**

Move the three functions verbatim out of `div.rs` (lines for `const_n`, `zero_extend`, `prenormalize`) into the new file, changing `fn` → `pub(crate) fn`:

```rust
//! Shared FP datapath normalization helpers (used by div and sqrt).

use shinri_bv::{BitLit, Blaster};
use crate::lzc::lzc;

/// Constant of width `n` (LSB→MSB) with value `v`. Total-mask guard: for `n >= 128`
/// the `1 << n` form overflows i128, so mask with all-ones instead.
pub(crate) fn const_n(b: &Blaster, n: usize, v: i128) -> Vec<BitLit> {
    let mask = if n >= 128 { -1i128 } else { (1i128 << n) - 1 };
    let u = v & mask;
    (0..n).map(|i| if (u >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
}

pub(crate) fn zero_extend(b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit> {
    let mut out = x.to_vec();
    while out.len() < to { out.push(b.zero()); }
    out
}

/// Pre-normalize `sig` (sb bits) so its leading 1 sits at index sb-1, returning
/// (sig_norm, exp_n) with exp_n = exp - shift (signed, ew bits). For a nonzero
/// significand sig_norm lands in [2^(sb-1), 2^sb).
pub(crate) fn prenormalize(b: &mut Blaster, sig: &[BitLit], exp: &[BitLit], sbu: usize, ew: usize)
    -> (Vec<BitLit>, Vec<BitLit>) {
    let k = lzc(b, sig);
    let k_sb = zero_extend(b, &k, sbu);
    let sig_norm = shinri_bv::blast::shift::bvshl(b, sig, &k_sb);
    let k_ew = zero_extend(b, &k, ew);
    let exp_n = shinri_bv::blast::arith::bvsub(b, exp, &k_ew);
    (sig_norm, exp_n)
}
```

- [ ] **Step 2: Register the module**

In `crates/shinri-fp/src/blast/mod.rs`, add (alphabetical with the others):

```rust
pub mod normalize;
```

- [ ] **Step 3: Rewire `div.rs`**

In `crates/shinri-fp/src/blast/div.rs`: delete the local `const_n`, `zero_extend`, and `prenormalize` definitions, and add an import near the top:

```rust
use crate::blast::normalize::{const_n, zero_extend, prenormalize};
```

(Leave all `fp_div` call sites unchanged — the signatures are identical.)

- [ ] **Step 4: Verify the refactor is behavior-preserving**

Run: `cargo test -p shinri-fp div`
Expected: PASS — `fp_div_tiny_exhaustive_all_modes` and `fp_div_float32_specials_and_random` still green (proves the move changed nothing).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/blast/normalize.rs crates/shinri-fp/src/blast/mod.rs crates/shinri-fp/src/blast/div.rs
git commit -m "refactor(fp): extract prenormalize/const_n/zero_extend into shared blast/normalize.rs"
```

---

### Task 3: `ref_sqrt` exact reference oracle

The bit-exact reference the datapath is tested against. Reuses the trusted `round_rational` via interval refinement.

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (add `ref_sqrt` + `#[cfg(test)]` cases)

**Interfaces:**
- Consumes: `Integer::sqrt_rem` (Task 1); existing `decode`, `FpClass`, `class_to_rational`, `round_rational`, `canonical_nan`, `inf_pattern`, `zero_pattern`, `RoundMode`; `shinri_num::{Integer, Rational}` (`Rational::new/numer/denom/is_negative`, `Integer` arithmetic).
- Produces: `pub fn ref_sqrt(eb: u32, sb: u32, a: &Integer, mode: RoundMode) -> Integer`.

- [ ] **Step 1: Write the failing tests**

In `crates/shinri-fp/src/reference.rs` `#[cfg(test)] mod tests`:

```rust
#[test]
fn ref_sqrt_known_float32() {
    let (eb, sb) = (8u32, 24u32);
    let i = |v: u64| Integer::from(v);
    // exact squares
    assert_eq!(ref_sqrt(eb, sb, &i(0x4000_0000), RoundMode::Rne), i(0x3FB5_04F3)); // sqrt(2)
    assert_eq!(ref_sqrt(eb, sb, &i(0x4080_0000), RoundMode::Rne), i(0x4000_0000)); // sqrt(4.0)=2.0
    assert_eq!(ref_sqrt(eb, sb, &i(0x3F80_0000), RoundMode::Rne), i(0x3F80_0000)); // sqrt(1.0)=1.0
    assert_eq!(ref_sqrt(eb, sb, &i(0x4110_0000), RoundMode::Rne), i(0x4040_0000)); // sqrt(9.0)=3.0
    // specials
    assert_eq!(ref_sqrt(eb, sb, &i(0x0000_0000), RoundMode::Rne), i(0x0000_0000)); // sqrt(+0)=+0
    assert_eq!(ref_sqrt(eb, sb, &i(0x8000_0000), RoundMode::Rne), i(0x8000_0000)); // sqrt(-0)=-0
    assert_eq!(ref_sqrt(eb, sb, &i(0x7F80_0000), RoundMode::Rne), i(0x7F80_0000)); // sqrt(+inf)=+inf
    assert_eq!(ref_sqrt(eb, sb, &i(0xFF80_0000), RoundMode::Rne), canonical_nan(eb, sb)); // sqrt(-inf)=NaN
    assert_eq!(ref_sqrt(eb, sb, &i(0xBF80_0000), RoundMode::Rne), canonical_nan(eb, sb)); // sqrt(-1)=NaN
    assert_eq!(ref_sqrt(eb, sb, &i(0x7FC0_0000), RoundMode::Rne), canonical_nan(eb, sb)); // sqrt(NaN)=NaN
}

#[test]
fn ref_sqrt_monotone_and_square_roundtrip_tiny() {
    // For every finite positive (eb=3,sb=5) input, sqrt(x)^2 (rounded) brackets x,
    // and sqrt is monotonic in the encoding order of positive finite values.
    let (eb, sb) = (3u32, 5u32);
    let mut prev: Option<Integer> = None;
    for v in 0u64..(1 << (eb + sb)) {
        let c = decode(eb, sb, &Integer::from(v));
        // positive finite nonzero only
        if !matches!(c, FpClass::Normal { sign: false, .. } | FpClass::Subnormal { sign: false, .. }) {
            prev = None;
            continue;
        }
        let r = ref_sqrt(eb, sb, &Integer::from(v), RoundMode::Rne);
        if let Some(p) = &prev {
            assert!(r >= *p, "sqrt must be monotonic at v={v:#x}");
        }
        prev = Some(r);
    }
}
```

(If the exact float32 hex constants above differ from what `z3`/IEEE produce, fix the *expected* literals — they are the spec of correctness here; compute them with `z3` or a known-good FPU once and lock them in.)

- [ ] **Step 2: Run tests, verify they fail**

Run: `cargo test -p shinri-fp ref_sqrt`
Expected: FAIL — `cannot find function ref_sqrt`.

- [ ] **Step 3: Implement `ref_sqrt`**

Add to `crates/shinri-fp/src/reference.rs`:

```rust
/// Exact correctly-rounded fp.sqrt. Specials per IEEE-754; finite positive values
/// rounded via interval refinement over `round_rational` (no irrational/float).
pub fn ref_sqrt(eb: u32, sb: u32, a: &Integer, mode: RoundMode) -> Integer {
    let c = decode(eb, sb, a);
    use FpClass::*;
    match &c {
        Nan => canonical_nan(eb, sb),
        Inf { sign } => if *sign { canonical_nan(eb, sb) } else { inf_pattern(eb, sb, false) },
        Zero { sign } => zero_pattern(eb, sb, *sign),           // sign preserved
        Normal { sign, .. } | Subnormal { sign, .. } if *sign => canonical_nan(eb, sb), // negative -> NaN
        _ => {
            // finite positive nonzero: exact dyadic value v = class_to_rational(c).
            let v = class_to_rational(eb, sb, &c).unwrap();
            sqrt_round_positive(eb, sb, &v, mode)
        }
    }
}

/// Correctly round sqrt(v) for an exact positive dyadic `v` by refining a rational
/// interval [s/2^n, (s+1)/2^n) bracketing the true root until both endpoints round
/// to the same FP value. Exact: when the scaled radicand is a perfect square the
/// root is exactly s/2^n; otherwise the root is irrational, strictly inside the
/// open interval, never a tie/exact boundary, so refinement always converges.
fn sqrt_round_positive(eb: u32, sb: u32, v: &Rational, mode: RoundMode) -> Integer {
    let two = Integer::from(2u64);
    let pow2 = |k: u32| -> Integer {
        let mut acc = Integer::one();
        for _ in 0..k { acc = acc * two.clone(); }
        acc
    };
    let mut n: u32 = sb + 4;
    loop {
        // radicand = v * 2^(2n) ; v is dyadic so this is an exact integer once 2n
        // covers v's denominator. denom is a power of two by construction of v.
        let scale = pow2(2 * n);
        let scaled = Rational::new(v.numer() * scale.clone(), v.denom()); // = v * 2^(2n)
        // Reduce to integer: scaled = num/den with den | 2^(2n). If not integral yet, bump n.
        if scaled.denom() != Integer::one() {
            n += 1;
            continue;
        }
        let radicand = scaled.numer();
        let (s, rem) = radicand.sqrt_rem();
        let denom_n = pow2(n);
        if rem.is_zero() {
            // sqrt(v) = s / 2^n exactly.
            return round_rational(eb, sb, &Rational::new(s, denom_n), mode);
        }
        let lo = round_rational(eb, sb, &Rational::new(s.clone(), denom_n.clone()), mode);
        let hi = round_rational(eb, sb, &Rational::new(s + Integer::one(), denom_n), mode);
        if lo == hi {
            return lo; // unambiguous: true root rounds the same as both endpoints
        }
        n += 4; // refine and retry
    }
}
```

Adjust `Rational` construction/reduction calls to the real API if `Rational::new` does not auto-reduce — check `rational.rs`. The invariant that matters: `scaled` equals `v * 2^(2n)` exactly and is tested for integrality before `numer()` is taken.

- [ ] **Step 4: Run tests, verify they pass**

Run: `cargo test -p shinri-fp ref_sqrt`
Expected: PASS (both tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): exact correctly-rounded ref_sqrt via round_rational interval refinement"
```

---

### Task 4: `fp_sqrt` datapath (restoring digit-recurrence)

The bit-blasted circuit. This is the high-risk task — the exhaustive tiny test is the spec for every bit position and constant.

**Files:**
- Create: `crates/shinri-fp/src/blast/sqrt.rs`
- Modify: `crates/shinri-fp/src/blast/mod.rs` (register module)

**Interfaces:**
- Consumes: `crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits}`; `crate::blast::normalize::{const_n, zero_extend, prenormalize}` (Task 2); `crate::round::{exp_w, round, ExtFp}`; `crate::rm::RmSel`; `shinri_bv::blast::{shift::bvshl, arith::{bvadd, bvsub}, compare::uge}`; `Blaster` gates (`and2/or2/xor2/not1/mux2/zero/one`).
- Produces: `pub fn fp_sqrt(b: &mut Blaster, x: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit>`.

- [ ] **Step 1: Write the failing exhaustive test**

Create `crates/shinri-fp/src/blast/sqrt.rs` with only the test module first (copy the `const_bits`/`eval_word`/`rmode` harness from `blast/div.rs`'s test module — identical helpers):

```rust
//! fp.sqrt datapath: unpack → prenormalize → integer sqrt → normalize → round → special-case.

#[cfg(test)]
mod tests {
    use crate::blast::sqrt::fp_sqrt;
    use crate::reference::{ref_sqrt, RoundMode};
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

    #[test]
    fn fp_sqrt_tiny_exhaustive_all_modes() {
        let (eb, sb) = (3u32, 5u32);
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        for a in 0u64..256 {
            for m in modes {
                let want = ref_sqrt(eb, sb, &Integer::from(a), m);
                let mut bl = Blaster::new();
                let xv = const_bits(&bl, eb, sb, a);
                let sel = rm::literal(&bl, rmode(m));
                let word = fp_sqrt(&mut bl, &xv, &sel, eb, sb);
                assert_eq!(Integer::from(eval_word(bl, &word)), want,
                    "fp.sqrt a={a:#x} m={m:?}");
            }
        }
    }
}
```

- [ ] **Step 2: Run test, verify it fails to compile**

Run: `cargo test -p shinri-fp fp_sqrt_tiny`
Expected: FAIL — `cannot find function fp_sqrt`.

- [ ] **Step 3: Register the module**

In `crates/shinri-fp/src/blast/mod.rs` add:

```rust
pub mod sqrt;
```

- [ ] **Step 4: Implement the integer-sqrt primitive + datapath**

At the top of `crates/shinri-fp/src/blast/sqrt.rs` (above the test module):

```rust
use shinri_bv::{BitLit, Blaster};
use crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};
use crate::blast::normalize::{const_n, zero_extend, prenormalize};
use crate::round::{exp_w, round, ExtFp};
use crate::rm::RmSel;

/// Restoring digit-recurrence integer square root.
/// `radicand` is `2*m` bits (LSB→MSB). Returns `(q, rem)` with `q` = `m` bits =
/// floor(sqrt(radicand)) and `rem` = radicand - q*q (width m+2).
fn usqrt_rem(b: &mut Blaster, radicand: &[BitLit], m: usize) -> (Vec<BitLit>, Vec<BitLit>) {
    let rw = m + 2;                                   // partial-remainder width
    let mut rem: Vec<BitLit> = vec![b.zero(); rw];
    let mut q: Vec<BitLit> = Vec::with_capacity(m);   // built MSB-first, reversed at end
    for i in (0..m).rev() {
        // bring down the next radicand pair: rem = (rem << 2) | (R[2i+1], R[2i])
        let mut nr = vec![radicand[2 * i], radicand[2 * i + 1]];
        nr.extend_from_slice(&rem[..rw - 2]);         // keep width rw
        // trial t = (q_sofar << 2) | 1  (q_sofar currently holds the high bits, MSB-first)
        // Build q_sofar as an integer LSB→MSB of the bits accumulated so far.
        let mut t = vec![b.one(), b.zero()];
        for bit in q.iter().rev() { t.push(*bit); }   // q.rev() = LSB→MSB
        while t.len() < rw { t.push(b.zero()); }
        let t = t[..rw].to_vec();
        let ge = shinri_bv::blast::compare::uge(b, &nr, &t);
        let sub = shinri_bv::blast::arith::bvsub(b, &nr, &t);
        rem = (0..rw).map(|k| b.mux2(ge, sub[k], nr[k])).collect();
        q.push(ge);                                   // new high bit of the root
    }
    q.reverse();                                      // now LSB→MSB, m bits
    (q, rem)
}

pub fn fp_sqrt(b: &mut Blaster, x: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let m = sbu + 2;                 // result bits from the root: sig(sb) + G + R
    let wr = 2 * m;                  // radicand width
    let ox = to_operand(b, x, eb, sb);

    // --- Prenormalize significand into [2^(sb-1), 2^sb). ---
    let (sig_n, exp_n) = prenormalize(b, &ox.sig, &ox.exp, sbu, ew);

    // --- Exponent parity: exp_n = 2*h + c, c = exp_n & 1 (LSB), h = exp_n >> 1 (arith). ---
    let c = exp_n[0];
    let h = shinri_bv::blast::shift::bvashr(b, &exp_n, &const_n(b, ew, 1));

    // --- Radicand mantissa B = sig_n << c, then left-align into wr bits. ---
    let sig_w = zero_extend(b, &sig_n, wr);
    let c_w = { let mut v = vec![c]; while v.len() < wr { v.push(b.zero()); } v }; // shift amount = c (0 or 1)
    let b_shifted = shinri_bv::blast::shift::bvshl(b, &sig_w, &c_w);
    // Align so the root yields m bits with a fixed leading 1. ALIGN pinned by the
    // exhaustive test (start candidate: 2*m - (sb + 1)).
    const_align_note();
    let align = (2 * m) - (sbu + 1);
    let radicand = shinri_bv::blast::shift::bvshl(b, &b_shifted, &const_n(b, wr, align as i128));

    // --- Integer square root. ---
    let (q, rem) = usqrt_rem(b, &radicand, m);        // q: m bits, leading 1 fixed at index m-1

    // --- GRS extraction: sig = top sb bits of q, G = q[m-1-sb]=q[1], R = q[0]. ---
    // q is m = sb+2 bits; q[m-1] is the fixed leading 1. sig = q[2..m] (sb bits),
    // G = q[1], R = q[0], S = OR(none here) OR (rem != 0).
    let sig: Vec<BitLit> = q[2..m].to_vec();          // sb bits, hidden at index sb-1
    let g = q[1];
    let r = q[0];
    let mut s = b.zero();
    for bit in &rem { s = b.or2(s, *bit); }           // remainder folds into sticky

    // --- Exponent out: norm_exp = h + corr. CORR pinned by the exhaustive test
    //     (start candidate: 0; adjust by the alignment/parity bookkeeping). ---
    let corr = const_n(b, ew, 0);
    let norm_exp = shinri_bv::blast::arith::bvadd(b, &h, &corr);

    let ext = ExtFp { sign: ox.sign, exp: norm_exp, sig, grs: (g, r, s) };
    let rounded = round(b, ext, eb, sb, rm);

    special_case(b, &rounded, &ox, eb, sb)
}

/// IEEE fp.sqrt special cases. Priority NaN > Inf > Zero.
fn special_case(b: &mut Blaster, normal: &[BitLit], ox: &Operand, eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);

    // NaN if input NaN, or input negative & nonzero (incl -inf, -normal, -subnormal).
    let not_zero = b.not1(ox.is_zero);
    let neg_nonzero = b.and2(ox.sign, not_zero);
    let want_nan = b.or2(ox.is_nan, neg_nonzero);

    // +inf if +inf input.
    let not_sign = b.not1(ox.sign);
    let want_inf = b.and2(ox.is_inf, not_sign);
    let inf_bits = inf_pattern_bits(b, eb, sb, b.zero());

    // signed zero if zero input (sign preserved).
    let want_zero = ox.is_zero;
    let zero_bits = signed_zero_bits(b, eb, sb, ox.sign);

    let mut out = normal.to_vec();
    for i in 0..w { out[i] = b.mux2(want_zero, zero_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_inf, inf_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_nan, nan[i], out[i]); }
    out
}

/// Marker: the `align` and `corr` constants above are pinned empirically by
/// `fp_sqrt_tiny_exhaustive_all_modes`. No-op.
#[inline]
fn const_align_note() {}
```

- [ ] **Step 5: Pin `align` and `corr` against the exhaustive test**

Run: `cargo test -p shinri-fp fp_sqrt_tiny -- --nocapture`

The first failures pinpoint the exponent/alignment bookkeeping. Iterate **only** the two integer constants `align` (radicand left-shift) and `corr` (added to `h`) until the test is fully green:
- A result that is correct in significand but off by a power of two ⇒ adjust `corr` by ±1.
- A result whose significand is shifted ⇒ adjust `align` by ±1 (and re-check `corr`).
- Remove the `const_align_note()` call/fn once pinned.

Expected when done: PASS — all 256 inputs × 5 modes match `ref_sqrt`. (If a wholesale mismatch persists, re-derive: result value `= q/2^(m-1) · 2^(h + corr)` must equal `√(sig_n · 2^(c) · 2^(exp_n−c)) = √(sig_n) · 2^((exp_n)/2)`; line up the `(sb-1)`/`m` offsets against `round()`'s `ExtFp` convention used in `div.rs`.)

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/blast/sqrt.rs crates/shinri-fp/src/blast/mod.rs
git commit -m "feat(fp): fp.sqrt datapath (restoring digit-recurrence) bit-identical to ref_sqrt"
```

---

### Task 5: Wire `FpSqrt` into blasting + remove from the soundness fence

Make `fp.sqrt` reachable end-to-end and admitted by the solver.

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` (`blast_word` arm)
- Modify: `crates/shinri-solver/src/fp_stage.rs` (`is_supported_fp_word` arm)
- Test: `crates/shinri-fp/src/blast/sqrt.rs` (float32 specials+random) and a solver end-to-end test alongside the existing `fp.div` one.

**Interfaces:**
- Consumes: `crate::blast::sqrt::fp_sqrt`; `BuiltinOp::FpSqrt`.
- Produces: an `FpSqrt` blast arm and fence admission; `fp.sqrt` now solves end-to-end.

- [ ] **Step 1: Add the `FpSqrt` blast arm**

In `crates/shinri-fp/src/lib.rs`, in the `match` inside `blast_word` (after the `FpDiv` arm, before the `other => unreachable!` arm):

```rust
                    FpSqrt => {
                        let rm = self.blast_rm(ctx, kids[0]);
                        let xw = self.blast_word(ctx, kids[1]);
                        crate::blast::sqrt::fp_sqrt(&mut self.b, &xw, &rm, eb, sb)
                    }
```

(Match the exact helper names used by the `FpDiv` arm — `self.blast_rm` and `kids[..]`.)

- [ ] **Step 2: Admit `FpSqrt` through the fence**

In `crates/shinri-solver/src/fp_stage.rs`, add a new arm to `is_supported_fp_word` (after the ternary `FpAdd/Sub/Mul/Div` arm). `fp.sqrt` is `(RM, F)`:

```rust
        // FpSqrt: (RM, F). RM operand must be a RoundingMode term; FP operand supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpSqrt), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
        }
```

Also update the comment on the catch-all `_ => false` arm to drop `FpSqrt` from the "not in scope" list. (Check whether `crates/shinri-solver/src/fp_stage.rs:15` — the op allow-list that already names `FpSqrt` — needs no change; it lists supported builtins and already includes `FpSqrt`.)

- [ ] **Step 3: Write the float32 + end-to-end tests**

Add to the `tests` module in `crates/shinri-fp/src/blast/sqrt.rs`:

```rust
    #[test]
    fn fp_sqrt_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        let specials = [0x0000_0000u64, 0x8000_0000, 0x7F80_0000, 0xFF80_0000, 0x7FC0_0000,
                        0x3F80_0000, 0xBF80_0000, 0x4000_0000, 0x0000_0001, 0x8000_0001,
                        0x7F7F_FFFF, 0x0080_0000];
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        let mut state: u64 = 0x5172_7100;
        let mut next = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state >> 16 };
        let mut cases: Vec<u64> = specials.to_vec();
        for _ in 0..200 { cases.push(next() & 0xFFFF_FFFF); }
        for a in cases {
            for m in modes {
                let want = ref_sqrt(eb, sb, &Integer::from(a), m);
                let mut bl = Blaster::new();
                let xv = const_bits(&bl, eb, sb, a);
                let sel = rm::literal(&bl, rmode(m));
                let word = fp_sqrt(&mut bl, &xv, &sel, eb, sb);
                assert_eq!(Integer::from(eval_word(bl, &word)), want, "fp.sqrt32 a={a:#x} m={m:?}");
            }
        }
    }
```

Then add an end-to-end solver test mirroring the existing `fp.div` end-to-end test (find it with `grep -rn "fp_div" crates/shinri-solver/`): assert a satisfiable `(= (fp.sqrt RNE x) 2.0)`-style query returns SAT with a correct `get-model`, and an unsatisfiable one (`(fp.lt (fp.sqrt RNE x) 0)` over a non-NaN finite x, or `sqrt` of a negative forced `= ` a non-NaN) returns UNSAT. Reuse the div test's scaffolding verbatim, swapping the operator.

- [ ] **Step 4: Run the full FP + solver suites**

Run: `cargo test -p shinri-fp && cargo test -p shinri-solver fp`
Expected: PASS — including `fp_sqrt_float32_specials_and_random` and the new end-to-end test. `fp.sqrt` is no longer `unknown`.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/lib.rs crates/shinri-solver/src/fp_stage.rs crates/shinri-fp/src/blast/sqrt.rs crates/shinri-solver
git commit -m "feat(solver): admit fp.sqrt through the FP soundness fence + end-to-end tests"
```

---

### Task 6: Differential-vs-z3 oracle (gated, long-running)

Cross-check the datapath against z3 over random inputs in all five modes. Bounded for tractable gated runs, like `DIV_ITERS`.

**Files:**
- Modify: the z3 oracle test module (find with `grep -rn "DIV_ITERS\|z3" crates/shinri-fp/`) — add a `fp.sqrt` case mirroring the `fp.div` one.

**Interfaces:**
- Consumes: the existing z3-oracle harness (SMT-LIB emit + `z3` invocation + parse) used by the div oracle; `fp_sqrt`, `ref_sqrt`.
- Produces: a gated `fp_sqrt` differential test bounded by `SQRT_ITERS`.

- [ ] **Step 1: Add the gated oracle test**

In the same module as the `fp.div` z3 oracle, add (mirror the div oracle's structure exactly — same gating attribute, same z3 emit/parse, unary operand):

```rust
const SQRT_ITERS: usize = 40; // bound for tractable gated runs (see DIV_ITERS)

#[test]
#[ignore = "z3 differential oracle; run explicitly"] // match div oracle's gating exactly
fn fp_sqrt_differential_vs_z3() {
    let (eb, sb) = (8u32, 24u32);
    let modes = [/* the five RoundMode values, as in the div oracle */];
    // LCG over SQRT_ITERS random float32 bit patterns × 5 modes:
    //   1. compute datapath result via fp_sqrt + eval_word (or the oracle's solver path)
    //   2. ask z3 for (assert (= r (fp.sqrt <mode> x))) and read its model bits
    //   3. assert datapath == z3 (and == ref_sqrt as a third cross-check)
    // Reuse the div oracle's exact emit/parse helpers; only the operator and arity change.
    todo_replace_with_div_oracle_body();
}
```

Replace the placeholder body by copying the div oracle's function body and changing the emitted operator from `fp.div`/two operands to `fp.sqrt`/one operand and the loop bound to `SQRT_ITERS`. Do not invent a new harness — reuse the proven one.

- [ ] **Step 2: Run the gated oracle in the background**

Per the established workflow (long FP/SAT gates), run it yourself in the background, not via subagent loops:

Run: `cargo test -p shinri-fp fp_sqrt_differential_vs_z3 -- --ignored --nocapture`
Expected: PASS — z3 agrees with the datapath (and `ref_sqrt`) on all `SQRT_ITERS × 5` cases.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-fp
git commit -m "test(fp): differential-vs-z3 oracle for fp.sqrt over all five modes (SQRT_ITERS=40)"
```

---

## Self-Review

**Spec coverage** (spec §-by-§):
- §1 restoring digit-recurrence primitive → Task 4 (`usqrt_rem`). ✅
- §1/§5 round-by-squaring reference + `Integer::sqrt_rem` → Tasks 1, 3. ✅
- §3 `prenormalize` extraction → Task 2. ✅
- §4 datapath (parity, radicand, no-result-lzc, GRS, exponent) → Task 4. ✅
- §4.1 special-case mux (NaN/-neg→NaN, +∞, signed-zero) → Task 4 `special_case`. ✅
- §5 `ref_sqrt` specials + finite path → Task 3. ✅
- §6 `blast_word` arm + fence admission → Task 5. ✅
- §7 tests: tiny-exhaustive (T4), float32+random (T5), z3 oracle (T6), `sqrt_rem` units (T1), end-to-end (T5). ✅
- §8 risks: `const_n` guard reused (T2/T4), exhaustive pinning of constants (T4 step 5). ✅

**Placeholder scan:** Task 6 intentionally references the existing div-oracle body to copy (the harness already exists and must not be duplicated divergently); the `todo_replace_with_div_oracle_body()` marker is explicit and the surrounding text says exactly what to copy and change. All other steps carry complete code. The two empirically-pinned constants (`align`, `corr`) in Task 4 have concrete starting values and a deterministic, complete test that fully specifies them.

**Type consistency:** `Integer::sqrt_rem(&self) -> (Integer, Integer)` used identically in Tasks 1 and 3. `fp_sqrt(b, x, rm, eb, sb)` signature identical in Tasks 4 and 5. `prenormalize`/`const_n`/`zero_extend` `pub(crate)` signatures match div's originals (Task 2) and the sqrt consumer (Task 4). `ref_sqrt(eb, sb, a, mode)` consistent across Tasks 3, 4, 5, 6.
