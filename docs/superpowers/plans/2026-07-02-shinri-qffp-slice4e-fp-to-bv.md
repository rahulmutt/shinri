# QF_FP Slice 4e: FP→BV (`fp.to_ubv` / `fp.to_sbv`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit both FP→BV conversion faces (`fp.to_ubv`, `fp.to_sbv`) with SMT-LIB-correct unspecified-result semantics (fresh word + congruence), closing Plan 4.

**Architecture:** A new `fp_to_int` gadget in `shinri-fp` (decode → one right-shift-with-sticky → shared `rounding_increment` → range check → ok-mux over fresh bits), a new `blast_fp_to_bv` dispatch entry (the first BV-sorted FP op), Ackermann-style congruence constraints across same-signature applications via a registry on the `Lowerer`, and a fence lift in `shinri-solver` that also extends the support walk to BV atoms (which can now embed FP subterms).

**Tech Stack:** Rust workspace (`cargo test`), z3 4.16 on PATH for the differential oracle (feature `oracle`).

**Spec:** `docs/superpowers/specs/2026-07-02-shinri-qffp-slice4e-fp-to-bv-design.md`

## Global Constraints

- **Soundness contract:** anything out of scope returns `Unknown`, never a wrong SAT/UNSAT verdict. The remaining fence after this slice is exactly `fp.to_real` + symbolic-Real `to_fp`.
- **Unspecified semantics (z3-probed, spec §2):** result on NaN/±∞/out-of-range is an uninterpreted function of `(RM, x)` per `(face, m, eb, sb)` — unconstrained value, congruent across equal arguments. Pinning a value or skipping congruence is UNSOUND.
- **Round FIRST, then range-check the rounded integer** (spec §2: −0.5 RNE → in-range 0; 255.5 RNE → 256, out of 8-bit range).
- **Regression is an oracle:** existing verdicts must stay byte-identical; full `cargo test --workspace` green at the end.
- **Long suites run in background in-session, NOT via subagents** (the shinri-fp exhaustive gate takes ~40 min). Per-task steps below use targeted `cargo test -p … <name>` invocations, which are fast.
- **House style:** LSB→MSB bit words; explicit index loops with `#[allow(clippy::needless_range_loop)]` where indices are load-bearing; comments state constraints, not narration.
- Commit after every task with the given message; do not push.

---

### Task 1: Reference goldens (`round_rational_to_integer`, `ref_to_ubv`, `ref_to_sbv`)

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (new fns after `ref_to_fp_ubv`, ~line 428; tests in the existing `#[cfg(test)]` module at the bottom of the file)

**Interfaces:**
- Consumes: `decode(eb, sb, bits: &Integer) -> FpClass` (reference.rs:34), `class_to_rational(eb, sb, &FpClass) -> Option<Rational>` (reference.rs:218, returns `None` for NaN/Inf), `RoundMode` enum (`Rne | Rna | Rtp | Rtn | Rtz`), `shinri_num::{Integer, Rational}` (`Integer` has `Ord`, `Add`, `Sub`, `Mul`, `div_rem`, `is_zero`; `Rational` has `numer()`, `denom()`, `Ord`).
- Produces (used by Tasks 2 and 6):
  - `pub fn round_rational_to_integer(q: &Rational, mode: RoundMode) -> Integer`
  - `pub fn ref_to_ubv(eb: u32, sb: u32, m: u32, bits: &Integer, mode: RoundMode) -> Option<Integer>` — `None` = unspecified; `Some(n)` with `n ∈ [0, 2^m−1]`.
  - `pub fn ref_to_sbv(eb: u32, sb: u32, m: u32, bits: &Integer, mode: RoundMode) -> Option<Integer>` — `Some` holds the **two's-complement m-bit pattern** (negative `n` encoded as `n + 2^m`), so it compares directly against circuit output.

- [ ] **Step 1: Write the failing tests**

Append to the tests module in `reference.rs`. Inputs are derived via `round_rational` (exactly representable values are mode-independent), never hand-encoded hex:

```rust
#[test]
fn ref_fp_to_bv_round_then_range_check() {
    use RoundMode::*;
    let f = |v: i64, d: i64| Rational::new(Integer::from(v), Integer::from(d));
    let enc = |q: &Rational| round_rational(5, 11, q, Rne); // exact values: mode-free
    // -0.5: rounded result decides the range check (spec §2 / z3 probes 5).
    let neg_half = enc(&f(-1, 2));
    assert_eq!(ref_to_ubv(5, 11, 8, &neg_half, Rne), Some(Integer::zero()), "RNE(-0.5)=0 in range");
    assert_eq!(ref_to_ubv(5, 11, 8, &neg_half, Rtz), Some(Integer::zero()));
    assert_eq!(ref_to_ubv(5, 11, 8, &neg_half, Rtp), Some(Integer::zero()));
    assert_eq!(ref_to_ubv(5, 11, 8, &neg_half, Rtn), None, "RTN(-0.5)=-1 out of range");
    // 255.5 into ubv8 (z3 probes 6/7).
    let v255_5 = enc(&f(511, 2));
    assert_eq!(ref_to_ubv(5, 11, 8, &v255_5, Rtz), Some(Integer::from(255u64)));
    assert_eq!(ref_to_ubv(5, 11, 8, &v255_5, Rtn), Some(Integer::from(255u64)));
    assert_eq!(ref_to_ubv(5, 11, 8, &v255_5, Rne), None, "rounds to 256");
    assert_eq!(ref_to_ubv(5, 11, 8, &v255_5, Rna), None);
    assert_eq!(ref_to_ubv(5, 11, 8, &v255_5, Rtp), None);
    // NaN / ±inf → None under every mode, both faces. ±inf built via
    // round_rational overflow: 1e9 ≫ (5,11) max finite 65504 → ±inf under RNE.
    let nan = canonical_nan(5, 11);
    let pinf = round_rational(5, 11, &f(1_000_000_000, 1), Rne);
    let ninf = round_rational(5, 11, &f(-1_000_000_000, 1), Rne);
    for md in [Rne, Rna, Rtp, Rtn, Rtz] {
        for bits in [&nan, &pinf, &ninf] {
            assert_eq!(ref_to_ubv(5, 11, 8, bits, md), None);
            assert_eq!(ref_to_sbv(5, 11, 8, bits, md), None);
        }
    }
}

#[test]
fn ref_fp_to_sbv_bounds_and_encoding() {
    use RoundMode::*;
    let f = |v: i64, d: i64| Rational::new(Integer::from(v), Integer::from(d));
    let enc = |q: &Rational| round_rational(5, 11, q, Rne);
    // INT_MIN = -128 is in range for sbv8 and encodes as 0x80.
    assert_eq!(ref_to_sbv(5, 11, 8, &enc(&f(-128, 1)), Rtz), Some(Integer::from(0x80u64)));
    // -128.5 RTZ truncates to -128 (in range); RTN goes to -129 (out).
    assert_eq!(ref_to_sbv(5, 11, 8, &enc(&f(-257, 2)), Rtz), Some(Integer::from(0x80u64)));
    assert_eq!(ref_to_sbv(5, 11, 8, &enc(&f(-257, 2)), Rtn), None);
    // 127.5: RNE→128 out; RTZ→127 in.
    assert_eq!(ref_to_sbv(5, 11, 8, &enc(&f(255, 2)), Rne), None);
    assert_eq!(ref_to_sbv(5, 11, 8, &enc(&f(255, 2)), Rtz), Some(Integer::from(127u64)));
    // -1 encodes as 0xFF; -0.0 → 0 (both faces).
    assert_eq!(ref_to_sbv(5, 11, 8, &enc(&f(-1, 1)), Rtz), Some(Integer::from(0xFFu64)));
    let neg_zero = round_rational(5, 11, &f(-1, 100000), Rtp); // tiny negative, RTP → -0
    assert_eq!(ref_to_ubv(5, 11, 8, &neg_zero, Rtz), Some(Integer::zero()));
    assert_eq!(ref_to_sbv(5, 11, 8, &neg_zero, Rtz), Some(Integer::zero()));
    // m=1 degenerate ranges: ubv1 [0,1], sbv1 [-1,0].
    let one = enc(&f(1, 1));
    assert_eq!(ref_to_ubv(5, 11, 1, &one, Rtz), Some(Integer::one()));
    assert_eq!(ref_to_sbv(5, 11, 1, &one, Rtz), None, "1 > sbv1 max 0");
    assert_eq!(ref_to_sbv(5, 11, 1, &enc(&f(-1, 1)), Rtz), Some(Integer::one()), "-1 = 0b1");
}

#[test]
fn round_rational_to_integer_all_modes() {
    use RoundMode::*;
    let f = |v: i64, d: i64| Rational::new(Integer::from(v), Integer::from(d));
    let n = |v: i64| Integer::from(v);
    // 2.5: RNE tie-to-even → 2; RNA away → 3.
    assert_eq!(round_rational_to_integer(&f(5, 2), Rne), n(2));
    assert_eq!(round_rational_to_integer(&f(5, 2), Rna), n(3));
    // 3.5: RNE tie-to-even → 4.
    assert_eq!(round_rational_to_integer(&f(7, 2), Rne), n(4));
    // -2.5: RNE → -2; RNA → -3; RTZ → -2; RTP → -2; RTN → -3.
    assert_eq!(round_rational_to_integer(&f(-5, 2), Rne), n(-2));
    assert_eq!(round_rational_to_integer(&f(-5, 2), Rna), n(-3));
    assert_eq!(round_rational_to_integer(&f(-5, 2), Rtz), n(-2));
    assert_eq!(round_rational_to_integer(&f(-5, 2), Rtp), n(-2));
    assert_eq!(round_rational_to_integer(&f(-5, 2), Rtn), n(-3));
    // Exact integer passes through under every mode.
    for md in [Rne, Rna, Rtp, Rtn, Rtz] {
        assert_eq!(round_rational_to_integer(&f(7, 1), md), n(7));
        assert_eq!(round_rational_to_integer(&f(0, 1), md), n(0));
    }
}
```


- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp --lib ref_fp_to_bv ref_fp_to_sbv round_rational_to_integer 2>&1 | tail -20`
Expected: compile error — `round_rational_to_integer`, `ref_to_ubv`, `ref_to_sbv` not found.

- [ ] **Step 3: Implement the three functions**

Insert after `ref_to_fp_ubv` (reference.rs:427):

```rust
/// Round an exact rational to an INTEGER under `mode` — no FP format involved.
/// The integer-rounding core shared by the FP→BV goldens (`fp.to_ubv`/`fp.to_sbv`
/// round the real value of the float to an integer, THEN range-check).
pub fn round_rational_to_integer(q: &Rational, mode: RoundMode) -> Integer {
    let zero = Rational::new(Integer::zero(), Integer::one());
    let half = Rational::new(Integer::one(), Integer::from(2u64));
    let neg = *q < zero;
    let mag = if neg { Rational::new(Integer::from(-1i64), Integer::one()) * q.clone() } else { q.clone() };
    let fl = mag.numer().div_rem(&mag.denom()).0; // floor(mag), mag >= 0
    let frac = mag - Rational::new(fl.clone(), Integer::one()); // in [0, 1)
    let round_up = match mode {
        RoundMode::Rtz => false,
        RoundMode::Rtp => !neg && frac > zero, // toward +inf: magnitude up only if positive
        RoundMode::Rtn => neg && frac > zero,  // toward -inf
        RoundMode::Rne => frac > half
            || (frac == half && !fl.div_rem(&Integer::from(2u64)).1.is_zero()),
        RoundMode::Rna => frac >= half,
    };
    let n = if round_up { fl + Integer::one() } else { fl };
    if neg { Integer::zero() - n } else { n }
}

/// `((_ fp.to_ubv m) rm x)` golden: `None` = SMT-LIB-unspecified (NaN, ±inf, or
/// the ROUNDED integer outside [0, 2^m-1]); `Some(n)` otherwise.
pub fn ref_to_ubv(eb: u32, sb: u32, m: u32, bits: &Integer, mode: RoundMode) -> Option<Integer> {
    let q = class_to_rational(eb, sb, &decode(eb, sb, bits))?; // None on NaN/inf
    let n = round_rational_to_integer(&q, mode);
    let two = Integer::from(2u64);
    let mut hi = Integer::one();
    for _ in 0..m { hi = hi * two.clone(); } // 2^m
    if n < Integer::zero() || n >= hi { return None; }
    Some(n)
}

/// `((_ fp.to_sbv m) rm x)` golden: range [-2^(m-1), 2^(m-1)-1]; a negative
/// in-range value is returned as its two's-complement m-bit PATTERN (n + 2^m)
/// so callers compare directly against circuit words.
pub fn ref_to_sbv(eb: u32, sb: u32, m: u32, bits: &Integer, mode: RoundMode) -> Option<Integer> {
    let q = class_to_rational(eb, sb, &decode(eb, sb, bits))?;
    let n = round_rational_to_integer(&q, mode);
    let two = Integer::from(2u64);
    let mut half = Integer::one();
    for _ in 0..(m - 1) { half = half * two.clone(); } // 2^(m-1)
    let hi = half.clone() * two.clone();               // 2^m
    let lo = Integer::zero() - half.clone();
    if n < lo || n >= half { return None; }
    Some(if n < Integer::zero() { n + hi } else { n })
}
```

If `Rational` lacks a `Mul`-by-`Rational` or the exact API differs, follow the idioms already in `round_rational` (reference.rs:257-345) — it uses the same operations.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp --lib ref_fp_to_bv ref_fp_to_sbv round_rational_to_integer 2>&1 | tail -5`
Expected: `3 passed`.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): ref_to_ubv/ref_to_sbv — FP→BV goldens over round_rational_to_integer (slice 4e)"
```

---

### Task 2: The `fp_to_int` gadget

**Files:**
- Modify: `crates/shinri-fp/src/convert.rs` (gadget after `to_fp_int` ~line 192; tests in the existing test module)

**Interfaces:**
- Consumes: `to_operand(b, bits, eb, sb) -> Operand` (`blast/operand.rs:19`; fields `sign, exp /* exp_w(eb) signed unbiased */, sig /* sb bits, hidden at sb-1 */, is_nan, is_inf, is_zero`), `exp_w`, `shift_right_sticky(b, x, amt) -> (Vec<BitLit>, BitLit)` (round.rs:185), `rounding_increment(b, sign, g, r, s, lsb, rm) -> BitLit` (round.rs:162), `const_n` (blast/normalize.rs), `sign_extend` (convert.rs:15, private, same file), `bvadd`/`bvneg`/`bvsub` (`shinri_bv::blast::arith`), `Blaster::fresh()`.
- Produces (used by Task 3):
  - `pub fn fp_to_int(b: &mut Blaster, x: &[BitLit], eb: u32, sb: u32, m: u32, signed_face: bool, rm: &RmSel) -> (Vec<BitLit>, BitLit)` — `(m-bit result word LSB→MSB, ok)`. `ok = 1` iff the result is specified; when `ok = 0` the result bits are fresh unconstrained variables.

- [ ] **Step 1: Write the failing gate tests**

Add to convert.rs's test module. Extend the harness first — `eval_word` (convert.rs:229) evaluates one word; the gadget returns a word AND an ok bit, so evaluate them in one solve:

```rust
fn eval_word_and_ok(b: Blaster, word: &[BitLit], ok: BitLit) -> (u64, bool) {
    let mut all = word.to_vec();
    all.push(ok);
    let v = eval_word(b, &all);
    (v & ((1u64 << word.len()) - 1), (v >> word.len()) & 1 == 1)
}
```

(For `word.len() == 64` the mask expression overflows — use `u64::MAX` when `word.len() >= 64`.)

```rust
#[test]
fn fp_to_int_tiny_exhaustive_both_faces() {
    // Every (3,5) pattern (8 bits), both faces, all five modes, m ∈ {1, 4, 8}:
    // bit-exact vs golden on Some; circuit ok ≡ golden is_some() on EVERY input.
    for &(core_rm, ref_rm) in &MODES {
        for m in [1u32, 4, 8] {
            for a in 0u64..256 {
                for signed in [true, false] {
                    let want = if signed {
                        ref_to_sbv(3, 5, m, &Integer::from(a), ref_rm)
                    } else {
                        ref_to_ubv(3, 5, m, &Integer::from(a), ref_rm)
                    };
                    let mut b = Blaster::new();
                    let xw = const_bits(&b, 3, 5, a);
                    let sel = rm::literal(&b, core_rm);
                    let (got_w, ok_l) = fp_to_int(&mut b, &xw, 3, 5, m, signed, &sel);
                    let (got, ok) = eval_word_and_ok(b, &got_w, ok_l);
                    assert_eq!(ok, want.is_some(),
                        "(3,5)→{}bv{m} mode {ref_rm:?} a={a:#x}: ok={ok} want_some={}",
                        if signed { "s" } else { "u" }, want.is_some());
                    if let Some(w) = want {
                        assert_eq!(Integer::from(got), w,
                            "(3,5)→{}bv{m} mode {ref_rm:?} a={a:#x}: got {got:#x} want {w}",
                            if signed { "s" } else { "u" });
                    }
                }
            }
        }
    }
}

#[test]
fn fp_to_int_f16_f32_specials_and_random() {
    // (5,11) and (8,24) sources into m ∈ {8, 32, 64}; seeded specials + PRNG.
    let mut state = 0xDEAD_BEEF_0123_4567u64;
    let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state };
    for (eb, sb) in [(5u32, 11u32), (8, 24)] {
        let w = eb + sb;
        // Specials: NaN, ±inf, ±0, ±1, max-finite, min-subnormal, and values
        // straddling the m-bit range edges (derived via round_rational — exact).
        let f = |v: i64, d: i64| Rational::new(Integer::from(v), Integer::from(d));
        let enc = |q: Rational| {
            let bits = crate::reference::round_rational(eb, sb, &q, RoundMode::Rne);
            // Integer → u64 via the test-side field helper.
            let mut v = 0u64;
            for i in 0..w { if !crate::reference::field(&bits, i, 1).is_zero() { v |= 1 << i; } }
            v
        };
        let mut cases: Vec<u64> = vec![
            enc(f(1_000_000_000, 1)),        // overflows f16 → +inf; huge for f32
            enc(f(-1_000_000_000, 1)),
            1 << (w - 1),                     // -0
            0,                                // +0
            1,                                // min subnormal
            enc(f(1, 1)), enc(f(-1, 1)),
            enc(f(255, 1)), enc(f(256, 1)), enc(f(511, 2)),      // ubv8 edges
            enc(f(-128, 1)), enc(f(-129, 1)), enc(f(-257, 2)),   // sbv8 edges
        ];
        for _ in 0..120 { cases.push(rand() & ((1u64 << w) - 1)); }
        for &(core_rm, ref_rm) in &MODES {
            for m in [8u32, 32, 64] {
                for &a in &cases {
                    for signed in [true, false] {
                        let want = if signed {
                            ref_to_sbv(eb, sb, m, &Integer::from(a), ref_rm)
                        } else {
                            ref_to_ubv(eb, sb, m, &Integer::from(a), ref_rm)
                        };
                        let mut b = Blaster::new();
                        let xw = const_bits(&b, eb, sb, a);
                        let sel = rm::literal(&b, core_rm);
                        let (got_w, ok_l) = fp_to_int(&mut b, &xw, eb, sb, m, signed, &sel);
                        let (got, ok) = eval_word_and_ok(b, &got_w, ok_l);
                        assert_eq!(ok, want.is_some(),
                            "({eb},{sb})→bv{m} signed={signed} mode {ref_rm:?} a={a:#x}");
                        if let Some(wv) = want {
                            assert_eq!(Integer::from(got), wv,
                                "({eb},{sb})→bv{m} signed={signed} mode {ref_rm:?} a={a:#x}: got {got:#x}");
                        }
                    }
                }
            }
        }
    }
}
```

Trim the mode×m×case product if runtime exceeds ~90s (e.g. drop the f32 source to 3 modes) — note any trim in the commit message. Imports needed in the test module: `ref_to_ubv`, `ref_to_sbv` (add to the existing `use crate::reference::…` line).

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp --lib fp_to_int 2>&1 | tail -5`
Expected: compile error — `fp_to_int` not found.

- [ ] **Step 3: Implement `fp_to_int`**

Insert after `to_fp_int` (convert.rs:192). Update the file header comment (line 1) to mention the FP→BV face. Add `bvadd` to the arith import (line 6) and `to_operand` is already imported (line 7); add `shift_right_sticky, rounding_increment` to the round import (line 9); `crate::blast::compare` is NOT needed here.

```rust
/// `((_ fp.to_ubv m) rm x)` (`signed_face = false`) and `((_ fp.to_sbv m) rm x)`
/// (`signed_face = true`): round the real value of `x` to an integer per `rm`,
/// THEN range-check the rounded integer (SMT-LIB; z3-verified in the slice-4e
/// spec). Returns `(m-bit word, ok)`: `ok = 0` on NaN/±inf/out-of-range, in
/// which case the word is FRESH UNCONSTRAINED bits (the SMT-LIB "unspecified
/// value"; cross-application congruence is the dispatch layer's job, not ours).
#[allow(clippy::needless_range_loop)] // indices are load-bearing: parallel-indexed words
pub fn fp_to_int(
    b: &mut Blaster, x: &[BitLit], eb: u32, sb: u32, m: u32, signed_face: bool, rm: &RmSel,
) -> (Vec<BitLit>, BitLit) {
    let mu = m as usize;
    let sbu = sb as usize;
    let ew = exp_w(eb);
    let o = to_operand(b, x, eb, sb);

    // --- 1. shift amount: amt = m - e (signed, width wa). Every in-range case
    //     has e <= m-1 so amt >= 1; amt <= 0 (e >= m ⇒ |value| >= 2^m) is the
    //     out-of-range short-circuit. wa holds m and e without wrap (same
    //     width argument as to_fp_int's clamp). ---
    let bits_for_m = (64 - (m as u64).leading_zeros()) as usize + 1;
    let wa = ew.max(bits_for_m) + 1;
    let e_wide = sign_extend(b, &o.exp, wa);
    let m_const = const_n(b, wa, m as i128);
    let amt = bvsub(b, &m_const, &e_wide);
    let amt_neg = amt[wa - 1];
    let mut amt_zero = b.one();
    for &bit in &amt { let nb = b.not1(bit); amt_zero = b.and2(amt_zero, nb); }
    let oor_high = b.or2(amt_neg, amt_zero);
    // (amt < 0 reads as huge-unsigned in bvlshr → register drains to 0 with full
    // sticky; harmless — oor_high overrides everything downstream.)

    // --- 2. fixed-point register R = |value| · 2^P: [P = sb+1 fraction | m+1
    //     integer] bits. sig placed at the top corresponds to e = m; shifting
    //     right by amt = m - e aligns exactly, bits below R[0] fold into the
    //     shift sticky. ---
    let p = sbu + 1;
    let wr = (mu + 1) + p;
    let mut r0 = vec![b.zero(); wr];
    for i in 0..sbu { r0[wr - sbu + i] = o.sig[i]; }
    let (r, sticky_shift) = shift_right_sticky(b, &r0, &amt);

    // --- 3. GRS + shared rounding increment on the magnitude. ---
    let g = r[p - 1];
    let rd = r[p - 2]; // p = sb+1 >= 3 for every real format
    let mut s = sticky_shift;
    for i in 0..(p - 2) { s = b.or2(s, r[i]); }
    let int_part: Vec<BitLit> = r[p..].to_vec(); // m+1 bits
    let inc = rounding_increment(b, o.sign, g, rd, s, int_part[0], rm);
    let mut inc_w = vec![b.zero(); mu + 1];
    inc_w[0] = inc;
    let mag = bvadd(b, &int_part, &inc_w); // rounded |result|, m+1 bits (2^m visible)

    // --- 4. range check per face + sign application. ---
    let mag_top = mag[mu]; // the 2^m bit
    let mut mag_zero = b.one();
    for &bit in &mag { let nb = b.not1(bit); mag_zero = b.and2(mag_zero, nb); }
    let low: Vec<BitLit> = mag[..mu].to_vec();
    let (fits, res): (BitLit, Vec<BitLit>) = if !signed_face {
        // ubv: 0 <= mag <= 2^m - 1, and a negative value only if it rounded to 0.
        let not_top = b.not1(mag_top);
        let not_sign = b.not1(o.sign);
        let sign_ok = b.or2(not_sign, mag_zero);
        (b.and2(not_top, sign_ok), low)
    } else {
        // sbv: positive needs mag <= 2^(m-1)-1; negative admits mag = 2^(m-1)
        // (INT_MIN). Result is the two's-complement of the magnitude when negative.
        let mag_msb = mag[mu - 1];
        let not_top = b.not1(mag_top);
        let not_msb = b.not1(mag_msb);
        let mut rest_zero = b.one();
        for i in 0..(mu - 1) { let nb = b.not1(mag[i]); rest_zero = b.and2(rest_zero, nb); }
        let pos_ok = b.and2(not_top, not_msb);
        let neg_bound = b.or2(not_msb, rest_zero); // mag <= 2^(m-1)
        let neg_ok = b.and2(not_top, neg_bound);
        let fits = b.mux2(o.sign, neg_ok, pos_ok);
        let neg = bvneg(b, &low);
        let res: Vec<BitLit> = (0..mu).map(|i| b.mux2(o.sign, neg[i], low[i])).collect();
        (fits, res)
    };

    // --- 5. ok + unspecified mux: fresh unconstrained bits on ¬ok. ---
    let not_nan = b.not1(o.is_nan);
    let not_inf = b.not1(o.is_inf);
    let not_oor = b.not1(oor_high);
    let finite = b.and2(not_nan, not_inf);
    let in_rng = b.and2(not_oor, fits);
    let ok = b.and2(finite, in_rng);
    let out: Vec<BitLit> = (0..mu).map(|i| {
        let fresh = b.fresh();
        b.mux2(ok, res[i], fresh)
    }).collect();
    (out, ok)
}
```

Notes for the implementer:
- Zero input needs no special mux: `sig = 0` → `mag = 0`, GRS = 0, `fits` holds for both faces (−0 included via `mag_zero` / `neg_bound`).
- Subnormals flow through the generic path: `to_operand` gives `e = emin`, hidden bit 0; `amt` is large; the register drains into sticky, and the value rounds to 0 or ±1.
- `m = 1`: `mag[mu - 1] = mag[0]`, `rest_zero` loop is empty (`rest_zero = 1`) — degenerate but correct: sbv1 admits only {0, −1}.
- `rd = r[p - 2]`: `p = sb + 1` and SMT-LIB formats have `sb ≥ 2`, so `p ≥ 3`; if a `debug_assert!(p >= 2)` feels warranted, add it.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp --lib fp_to_int 2>&1 | tail -5`
Expected: `2 passed` (plus the Task 1 tests still green).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/convert.rs
git commit -m "feat(fp): fp_to_int gadget — FP→BV via single shift+sticky, shared rounding_increment, ok-mux over fresh bits (slice 4e)"
```

---

### Task 3: Dispatch + congruence plumbing (`blast_fp_to_bv`, `FpToBvApp` registry)

**Files:**
- Modify: `crates/shinri-bv/src/blast/mod.rs` (new `FpToBvApp` struct + `WordSink` default method, next to `rm_cache` at line 57)
- Modify: `crates/shinri-bv/src/lib.rs` (re-export `FpToBvApp` alongside `WordSink`)
- Modify: `crates/shinri-fp/src/lib.rs` (new `pub fn blast_fp_to_bv`)
- Modify: `crates/shinri-fp/src/lower.rs` (registry field + `WordSink` override + dispatch in `word()` at line 40-44; tests in the existing module)

**Interfaces:**
- Consumes: `fp_to_int` (Task 2), `blast_rm` (shinri-fp/src/lib.rs:85), `core_eq(b, x, y, eb, sb) -> BitLit` (`crate::blast::compare`, NaN-aware SMT value equality), `RmSel { sel: [BitLit; 5] }`.
- Produces (used by Task 4's solver path — no signature changes there, the Lowerer routes internally):
  - In shinri-bv: `pub struct FpToBvApp { pub key: (bool, u32, u32, u32), pub rm: [BitLit; 5], pub operand: Vec<BitLit>, pub result: Vec<BitLit> }` (`key = (signed_face, m, eb, sb)`), and `WordSink::fp2bv_apps(&mut self) -> &mut Vec<FpToBvApp>` with an `unreachable!` default.
  - In shinri-fp: `pub fn blast_fp_to_bv<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> Vec<BitLit>` — blasts a BV-sorted `FpToUbv`/`FpToSbv` term AND emits congruence clauses against every prior same-key application.

**Spec refinement (record in code comments):** the spec's §6 says "`blast_fp_word` gains the two arms", but `blast_fp_word`'s preamble requires an FP-sorted result (lib.rs:124). The faithful realization is this sibling entry point dispatched from `Lowerer::word` — same architecture, correct sort discipline.

- [ ] **Step 1: Write the failing congruence tests**

In `crates/shinri-fp/src/lower.rs` tests (the module already builds ctx + Lowerer; it needs a SAT solve harness — copy the `eval` pattern from convert.rs tests but return the `SolveResult` instead of asserting Sat):

```rust
fn solve_with_units(lw: Lowerer, units: &[(BitLit, bool)]) -> shinri_sat::SolveResult {
    use shinri_sat::{Lit, NoProof, NoTheory, Solver, SolverConfig, Var, Vmtf};
    let cnf = lw.b.finish();
    let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
    for _ in 0..cnf.num_vars { s.new_var(); }
    for c in &cnf.clauses {
        let ls: Vec<Lit> = c.iter().map(|bl| Lit::new(Var::new(bl.var), bl.pos)).collect();
        s.add_clause(&ls);
    }
    for &(bl, want) in units {
        s.add_clause(&[Lit::new(Var::new(bl.var), bl.pos == want)]);
    }
    s.solve()
}

#[test]
fn fp_to_bv_congruence_equal_args_force_equal_results() {
    // Spec §2 probe-2 shape: x = y (SMT value equality) ∧ isNaN x ∧
    // to_ubv(RNE,x) ≠ to_ubv(RNE,y) must be UNSAT — the two applications are
    // distinct TermIds, so only the emitted congruence clauses can close it.
    let mut ctx = Context::new();
    let f16 = ctx.fp_sort(5, 11);
    let mk = |ctx: &mut Context, n: &str, s| {
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    };
    let x = mk(&mut ctx, "x", f16);
    let y = mk(&mut ctx, "y", f16);
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let ux = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, x]).unwrap();
    let uy = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, y]).unwrap();
    let eq_xy = ctx.mk_eq(x, y).unwrap();
    let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
    let eq_uv = ctx.mk_eq(ux, uy).unwrap();
    let mut lw = Lowerer::new();
    let l_eq = lw.atom(&ctx, eq_xy);
    let l_nan = lw.atom(&ctx, isnan);
    let l_uv = lw.atom(&ctx, eq_uv);
    let r = solve_with_units(lw, &[(l_eq, true), (l_nan, true), (l_uv, false)]);
    assert_eq!(r, shinri_sat::SolveResult::Unsat, "congruence must bind equal-arg applications");
}

#[test]
fn fp_to_bv_unspecified_free_across_modes_and_faces() {
    // Probe-4 shape: same NaN operand, DIFFERENT rounding modes → results may
    // differ (SAT). Also different faces (ubv vs sbv) are independent functions.
    let mut ctx = Context::new();
    let f16 = ctx.fp_sort(5, 11);
    let f = ctx.declare_fun("x", &[], f16);
    let x = ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap();
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let rtz = ctx.mk_rm_const(shinri_core::RoundingMode::Rtz);
    let u1 = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, x]).unwrap();
    let u2 = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rtz, x]).unwrap();
    let s1 = ctx.mk_app(Op::Builtin(BuiltinOp::FpToSbv(8)), &[rne, x]).unwrap();
    let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
    let ne_modes = ctx.mk_eq(u1, u2).unwrap();
    let ne_faces = ctx.mk_eq(u1, s1).unwrap();
    let mut lw = Lowerer::new();
    let l_nan = lw.atom(&ctx, isnan);
    let l_m = lw.atom(&ctx, ne_modes);
    let l_f = lw.atom(&ctx, ne_faces);
    let r = solve_with_units(lw, &[(l_nan, true), (l_m, false), (l_f, false)]);
    assert_eq!(r, shinri_sat::SolveResult::Sat,
        "different modes / different faces are unconstrained relative to each other");
}
```

Add the needed imports to the test module (`BuiltinOp` is already imported; add `BitLit` if missing). Add `shinri-sat` to shinri-fp's `[dev-dependencies]` if not present (convert.rs tests already use it — it is).

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp --lib fp_to_bv_congruence fp_to_bv_unspecified 2>&1 | tail -5`
Expected: panic — `Lowerer::word` routes the BV-sorted `FpToUbv` into `blast_bv_word`, which hits its crossing `unreachable!` arm (or a sort-rule error). Failing for the RIGHT reason: dispatch doesn't exist yet.

- [ ] **Step 3: Implement plumbing**

3a. `crates/shinri-bv/src/blast/mod.rs`, after the `WordSink` trait's `rm_cache` (line 59), add the struct above the trait and the method inside it:

```rust
/// One admitted FP→BV application (fp.to_ubv / fp.to_sbv), recorded by the
/// lowering driver so later same-signature applications can emit congruence
/// constraints (the SMT-LIB "unspecified value" is an uninterpreted FUNCTION
/// of (RM, x) — equal arguments must yield equal results even out of range).
#[derive(Clone)]
pub struct FpToBvApp {
    /// (signed_face, m, eb, sb) — applications constrain each other iff equal.
    pub key: (bool, u32, u32, u32),
    pub rm: [BitLit; 5],
    pub operand: Vec<BitLit>,
    pub result: Vec<BitLit>,
}
```

and in the trait:

```rust
    /// Registry of FP→BV applications for unspecified-value congruence. Only
    /// meaningful for sinks that lower FP→BV conversions (shinri-fp's Lowerer);
    /// pure-BV lowering never calls this.
    fn fp2bv_apps(&mut self) -> &mut Vec<FpToBvApp> {
        unreachable!("pure BV lowering has no FP→BV conversions")
    }
```

3b. `crates/shinri-bv/src/lib.rs`: add `FpToBvApp` to the existing `pub use` that exports `WordSink` (grep `pub use` there for the exact line).

3c. `crates/shinri-fp/src/lib.rs`, after `blast_fp_word` (line 245):

```rust
/// BV-sorted FP→BV dispatch: `fp.to_ubv` / `fp.to_sbv` (slice 4e). A sibling of
/// `blast_fp_word` rather than an arm of it — the result sort is BitVec, and
/// blast_fp_word's preamble asserts an FP sort. Called from `Lowerer::word`'s
/// BV branch. Blasts the gadget, then emits congruence clauses against every
/// prior same-key application: (core_eq(x_i, x_j) ∧ rm_i = rm_j) → res_i = res_j
/// — core_eq because the trigger is SMT VALUE equality (any-NaN = any-NaN;
/// blasted FP words are not payload-canonicalized).
pub fn blast_fp_to_bv<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> Vec<BitLit> {
    use shinri_core::BuiltinOp::*;
    let TermNode::App { op, args, .. } = ctx.term_node(t).clone() else {
        unreachable!("blast_fp_to_bv: FP→BV must be an application");
    };
    let (signed_face, m) = match op {
        Op::Builtin(FpToUbv(m)) => (false, m),
        Op::Builtin(FpToSbv(m)) => (true, m),
        other => unreachable!("blast_fp_to_bv: not an FP→BV op: {other:?}"),
    };
    let kids = ctx.children(args).to_vec();
    let rm = blast_rm(sink, ctx, kids[0]);
    let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[1])).expect("FP operand");
    let xw = sink.word(ctx, kids[1]);
    let (word, _ok) = crate::convert::fp_to_int(sink.blaster(), &xw, eb, sb, m, signed_face, &rm);
    // Congruence vs. every prior application with the same signature. O(k²) in
    // the per-formula application count — k is tiny; hash-consing already
    // dedups syntactically identical terms before we get here.
    let key = (signed_face, m, eb, sb);
    let prior: Vec<shinri_bv::FpToBvApp> =
        sink.fp2bv_apps().iter().filter(|a| a.key == key).cloned().collect();
    for pa in prior {
        let b = sink.blaster();
        let x_eq = crate::blast::compare::core_eq(b, &pa.operand, &xw, eb, sb);
        let mut rm_eq = b.one();
        for j in 0..5 {
            let d = b.xor2(pa.rm[j], rm.sel[j]);
            let nd = b.not1(d);
            rm_eq = b.and2(rm_eq, nd);
        }
        let cond = b.and2(x_eq, rm_eq);
        let ncond = b.not1(cond);
        for i in 0..(m as usize) {
            let d = b.xor2(pa.result[i], word[i]);
            let nd = b.not1(d);
            let imp = b.or2(ncond, nd);
            b.add_clause(&[imp]); // cond → (res_prior[i] ↔ res_new[i])
        }
    }
    sink.fp2bv_apps().push(shinri_bv::FpToBvApp {
        key, rm: rm.sel, operand: xw, result: word.clone(),
    });
    word
}
```

(Constraining the FULL result word — not just the fresh branch — is correct: when both applications are in-range the datapaths already agree, so the implication is vacuously satisfied there. Spec §5.)

3d. `crates/shinri-fp/src/lower.rs`: add the field + override + dispatch:

```rust
pub struct Lowerer {
    pub b: Blaster,
    cache: FxHashMap<TermId, Vec<BitLit>>,
    // (existing rm_cache comment)
    rm_cache: FxHashMap<TermId, [BitLit; 5]>,
    // FP→BV application registry for unspecified-value congruence (slice 4e).
    fp2bv_apps: Vec<FpToBvApp>,
}
```

Initialize `fp2bv_apps: Vec::new()` in `new()`; import `FpToBvApp` (and `BuiltinOp`) at the top; add to the `WordSink` impl:

```rust
    fn fp2bv_apps(&mut self) -> &mut Vec<FpToBvApp> {
        &mut self.fp2bv_apps
    }
```

Replace the BV branch of `word()` (lines 40-44):

```rust
        let bits = if ctx.bv_width(sort).is_some() {
            // BV-sorted node. fp.to_ubv/to_sbv are the one BV-sorted FP-op
            // family (admitted in 4e) — route them to the FP dispatch; every
            // other BV-sorted node goes to the BV blaster. (Still-crossing ops
            // are fenced before lowering, so blast_bv_word's unreachable! arm
            // stays an internal invariant.)
            if matches!(ctx.term_node(t),
                TermNode::App { op: Op::Builtin(BuiltinOp::FpToUbv(_) | BuiltinOp::FpToSbv(_)), .. })
            {
                crate::blast_fp_to_bv(self, ctx, t)
            } else {
                blast_bv_word(self, ctx, t)
            }
        } else if ctx.fp_widths(sort).is_some() {
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp --lib fp_to_bv_congruence fp_to_bv_unspecified 2>&1 | tail -5`
Expected: `2 passed`.
Also run: `cargo test -p shinri-bv --lib 2>&1 | tail -3` — pure-BV sinks must be untouched (default method never called).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/mod.rs crates/shinri-bv/src/lib.rs crates/shinri-fp/src/lib.rs crates/shinri-fp/src/lower.rs
git commit -m "feat(fp): blast_fp_to_bv dispatch + FpToBvApp congruence registry — unspecified FP→BV as UF of (rm, x) (slice 4e)"
```

---

### Task 4: Fence lift + BV-atom support walk + canary repoints

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs` (crossing set line 77-78 + doc comment 50-67; new support fns; arm edits at lines 268, 276, 286, 295; comment 297; unit-test repoints at 564-570, 607-609, 656-662)
- Modify: `crates/shinri-solver/src/lib.rs` (new check after line 400; stale comments 349-354 and 393-397)

**Interfaces:**
- Consumes: `is_supported_fp_word`, `is_rounding_mode_term` (fp_stage.rs, private), `collect_bv_atoms` output shape.
- Produces: `pub fn bv_atoms_fp_supported(ctx: &Context, bv_atoms: &[TermId]) -> bool` (called from solver lib.rs). Internal: `is_supported_fp_to_bv`, `bv_subtree_fp_supported` (mutually recursive with `is_supported_fp_word`).

- [ ] **Step 1: Pre-flight canary hunt (standing cross-slice lesson — BEFORE any fence edit)**

Run: `grep -rn "to_ubv\|to_sbv\|FpToUbv\|FpToSbv" crates/ --include="*.rs" | grep -v "^crates/shinri-core\|^crates/shinri-parser"`
Expected hits to flip/repoint (verify nothing beyond these; investigate anything extra):
- `fp_stage.rs:564-570` — "Still crossing: fp.to_sbv" assertion
- `fp_stage.rs:607-609` — "fp.to_sbv is crossing" assertion
- `fp_stage.rs:656-662` — "nested fp.to_ubv still crossing" assertion
- `fp_stage.rs:57, 77-78, 297` — comments + the crossing-set match arm
- `fp_e2e.rs:643-645` — the FP→int script in `to_fp_bv_crossing_and_symbolic_real_are_unknown`
- `solver/src/lib.rs:351` — remaining-fence comment
- Task-3 additions in shinri-fp/shinri-bv (expected, ours)

- [ ] **Step 2: Write the failing unit tests (new + repointed canaries)**

In fp_stage.rs tests:

```rust
#[test]
fn fp_to_bv_faces_admitted_real_bridge_still_crossing() {
    // Slice 4e: fp.to_ubv/fp.to_sbv are no longer crossing; the PERMANENT
    // fence is fp.to_real + symbolic-Real to_fp.
    let mut ctx = Context::new();
    let f32s = ctx.fp_sort(8, 24);
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let xf = ctx.declare_fun("x", &[], f32s);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let ubv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, x]).unwrap();
    let sbv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToSbv(32)), &[rne, x]).unwrap();
    assert!(!uses_crossing_conversion(&ctx, &[ubv]), "fp.to_ubv admitted (slice 4e)");
    assert!(!uses_crossing_conversion(&ctx, &[sbv]), "fp.to_sbv admitted (slice 4e)");
    // fp.to_real: crossing forever (v1 Real bridge).
    let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap();
    assert!(uses_crossing_conversion(&ctx, &[toreal]), "fp.to_real stays fenced");
    // Symbolic-Real to_fp nested INSIDE an admitted to_ubv: the DAG walk still nets it.
    let real = ctx.real_sort();
    let rf = ctx.declare_fun("r", &[], real);
    let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
    let sreal = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, r]).unwrap();
    let nested = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, sreal]).unwrap();
    assert!(uses_crossing_conversion(&ctx, &[nested]), "nested symbolic-Real to_fp still crossing");
}

#[test]
fn bv_atoms_embedded_fp_support_walk() {
    // First slice where a BV atom can legally contain FP subterms. A supported
    // to_ubv under a BV atom passes; an UNSUPPORTED FP shape (FP-sorted ite)
    // under the to_ubv must fence.
    let mut ctx = Context::new();
    let f32s = ctx.fp_sort(8, 24);
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let xf = ctx.declare_fun("x", &[], f32s);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let ubv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, x]).unwrap();
    let c = ctx.mk_bv_const(8, Integer::from(3u64));
    let atom_ok = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[ubv, c]).unwrap();
    assert!(bv_atoms_fp_supported(&ctx, &[atom_ok]), "supported FP operand under BV atom passes");
    // FP-sorted ite is not a supported FP word.
    let bs = ctx.bool_sort();
    let pf = ctx.declare_fun("p", &[], bs);
    let p = ctx.mk_app(Op::Uninterpreted(pf), &[]).unwrap();
    let ite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[p, x, x]).unwrap();
    let ubv_bad = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(8)), &[rne, ite]).unwrap();
    let atom_bad = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[ubv_bad, c]).unwrap();
    assert!(!bv_atoms_fp_supported(&ctx, &[atom_bad]), "unsupported FP shape under BV atom fences");
}
```

(Adjust `Ite`/`bool_sort` construction to the Context API if the names differ — grep fp_stage.rs's existing tests for `Ite` precedent; if none exists, a non-nullary FP UF `declare_fun("g", &[f32s], f32s)` applied to `x` is an equally unsupported shape and simpler to build.)

Repoint the three existing assertions found in Step 1:
- fp_stage.rs:564-570: replace the fp.to_sbv build+assert with `FpToReal`: `let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap(); assert!(super::uses_crossing_conversion(&ctx, &[toreal]), "fp.to_real still crossing");` (drop the now-unused `rm` var or reuse it).
- fp_stage.rs:607-609: flip to `assert!(!uses_crossing_conversion(&ctx, &[sbv]), "fp.to_sbv admitted (slice 4e)");`
- fp_stage.rs:656-662: flip to `assert!(!uses_crossing_conversion(&ctx, &[nested]), "to_fp over fp.to_ubv fully admitted (4d+4e)");` — the durable nested canary now lives in the new test above.

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test -p shinri-solver --lib fp_to_bv_faces_admitted bv_atoms_embedded 2>&1 | tail -5`
Expected: compile error on `bv_atoms_fp_supported`, and the admitted-faces assertions fail (ops still in the crossing set). The three repointed tests also fail.

- [ ] **Step 4: Implement the fence lift**

4a. `uses_crossing_conversion` (fp_stage.rs:77-78): delete the `FpToUbv(_)` and `FpToSbv(_)` lines from the `=> true` pattern, leaving `Op::Builtin(BuiltinOp::FpToReal) => true`. Rewrite the doc comment (lines 50-67): crossing set is now exactly `FpToReal` (permanent Real bridge) + `ToFp`'s symbolic-Real face; note FP→BV admitted in 4e.

4b. New support fns (fp_stage.rs, after `is_rounding_mode_term`):

```rust
/// A supported FP→BV application (slice 4e): (RM, F) with a blastable RM and a
/// recursively supported FP operand. Unlike int→FP's BV child (4d), the FP
/// operand DOES need the recursive check — the FP blaster is not total.
fn is_supported_fp_to_bv(ctx: &Context, t: TermId) -> bool {
    let TermNode::App { op: Op::Builtin(BuiltinOp::FpToUbv(_) | BuiltinOp::FpToSbv(_)), args, .. } =
        ctx.term_node(t)
    else {
        return false;
    };
    let kids = ctx.children(*args).to_vec();
    kids.len() == 2
        && is_rounding_mode_term(ctx, kids[0])
        && is_supported_fp_word(ctx, kids[1])
}

/// Walk a BV-sorted subtree hunting embedded FP→BV applications; each must be
/// fully supported. Mutually recursive with `is_supported_fp_word`: since 4e a
/// BV subtree can contain FP subtrees (via fp.to_ubv/to_sbv) and vice versa
/// (via int→FP / bitcast / fp-constructor BV children), so the old "BV blaster
/// is total" sort-check argument (4c/4d) holds only modulo this walk.
fn bv_subtree_fp_supported(ctx: &Context, root: TermId) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return true; }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            if matches!(op, Op::Builtin(BuiltinOp::FpToUbv(_) | BuiltinOp::FpToSbv(_))) {
                // The FP operand is checked by is_supported_fp_word (which
                // re-enters this walk for ITS BV children); no further descent.
                return is_supported_fp_to_bv(ctx, t);
            }
            return ctx.children(*args).to_vec().into_iter().all(|k| walk(ctx, k, seen));
        }
        true
    }
    walk(ctx, root, &mut seen)
}

/// Solver-facing: every collected BV atom's operands must pass the embedded-FP
/// support walk. Until 4e BV atoms could not contain FP subterms, so this is
/// the first slice that support-checks the BV side at all.
pub fn bv_atoms_fp_supported(ctx: &Context, bv_atoms: &[TermId]) -> bool {
    bv_atoms.iter().all(|&a| {
        let TermNode::App { args, .. } = ctx.term_node(a) else { return true; };
        ctx.children(*args).to_vec().into_iter().all(|k| bv_subtree_fp_supported(ctx, k))
    })
}
```

4c. Replace the four bare BV-sort checks inside `is_supported_fp_word` with sort check ∧ walk, updating each arm's comment:
- line 268 (ToFp 1-arg): `1 => matches!(…BitVec…) && bv_subtree_fp_supported(ctx, kids[0]),`
- line 276 (ToFp 2-arg BV face): `|| (matches!(…BitVec…) && bv_subtree_fp_supported(ctx, kids[1]))`
- line 286 (ToFpUnsigned): append `&& bv_subtree_fp_supported(ctx, kids[1])`
- line 295 (FpFromBits): `kids.iter().all(|&k| matches!(…BitVec…) && bv_subtree_fp_supported(ctx, k))`
- line 297 catch-all comment: remove `fp.to_ubv/fp.to_sbv` from the not-in-scope list (they never appear as FP WORDS — they are BV-sorted; note that instead).

4d. Solver call site, `crates/shinri-solver/src/lib.rs` after the `fp_atoms_fully_supported` block (line 398-400):

```rust
                // Slice 4e: BV atoms can now embed FP subterms (fp.to_ubv/
                // fp.to_sbv). Any unsupported FP shape reachable through a BV
                // atom must fence BEFORE lowering, same argument as above.
                if !crate::fp_stage::bv_atoms_fp_supported(&self.ctx, &bv_atoms) {
                    return SolveOutcome::Unknown;
                }
```

Update the stale comment at lines 393-397 (remove "BV atoms need no support check…", point at the new check) and the remaining-fence list at lines 349-354 (now: `fp.to_real` / symbolic-Real `to_fp`).

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-solver --lib 2>&1 | tail -5`
Expected: all fp_stage unit tests pass, including the new + repointed canaries.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs crates/shinri-solver/src/lib.rs
git commit -m "feat(solver): lift the fence for FP→BV; BV-atom embedded-FP support walk; repoint crossing canaries at the Real bridge (slice 4e)"
```

---

### Task 5: e2e tests (`fp_e2e.rs`) + e2e canary repoint

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` (new slice-4e block after the slice-4d block; repoint lines 631-654)

**Interfaces:**
- Consumes: the `run(src) -> (SolveOutcome, String)` helper (fp_e2e.rs:7). FP literals in scripts use the `(fp #b… #b… #b…)` constructor (admitted 4c, folds) and `(_ NaN 5 11)` / `(_ +oo 5 11)` special forms — do NOT use negative Real literals.

- [ ] **Step 1: Repoint the e2e crossing canary**

In `to_fp_bv_crossing_and_symbolic_real_are_unknown` (line 631): delete the fp.to_sbv script (lines 643-645); update the comment (633-638) to say the remaining fence is only the Real bridge. The symbolic-Real and fp.to_real scripts stay.

- [ ] **Step 2: Write the failing e2e tests**

Key encodings used below, format (5,11): `-0.5` = `(fp #b1 #b01110 #b0000000000)`, `255.5` = `(fp #b0 #b10110 #b1111111100)`, `42.0` = `(fp #b0 #b10100 #b0101000000)`, `-128.0` = `(fp #b1 #b10110 #b0000000000)`. (Sanity-derivation: value = (1 + frac/1024) · 2^(biasedExp − 15); e.g. 255.5 = 1.99609375 · 2^7, frac = 0.99609375·1024 = 1020 = `1111111100`.)

```rust
// ── Slice-4e: FP→BV (fp.to_ubv / fp.to_sbv) now solves ──────────────────────

#[test]
fn fp_to_ubv_sat_unsat_with_model() {
    // 42.0 → ubv8 is specified: equals #x2A (any mode; exact integer).
    let (o, model) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) (declare-fun a () (_ BitVec 8)) \
         (assert (fp.eq x (fp #b0 #b10100 #b0101000000))) \
         (assert (= a ((_ fp.to_ubv 8) RTZ x))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("x") && model.contains("a"), "model surfaces both vars");
    let (o2, _) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) \
         (assert (fp.eq x (fp #b0 #b10100 #b0101000000))) \
         (assert (distinct ((_ fp.to_ubv 8) RTZ x) #x2A)) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Unsat, "42.0 → ubv8 must be exactly #x2A");
}

#[test]
fn fp_to_bv_round_then_range_boundary_trio() {
    // The z3-probed spec-§2 boundary semantics, pinned end-to-end.
    let cases = [
        // -0.5 RNE rounds to 0 → in range → specified 0.
        ("(assert (distinct ((_ fp.to_ubv 8) RNE (fp #b1 #b01110 #b0000000000)) #x00)) (check-sat)",
         SolveOutcome::Unsat),
        // 255.5 RTZ → 255 → specified #xFF.
        ("(assert (distinct ((_ fp.to_ubv 8) RTZ (fp #b0 #b10110 #b1111111100)) #xFF)) (check-sat)",
         SolveOutcome::Unsat),
        // 255.5 RNE → 256 → OUT of range → unspecified: may equal #x07.
        ("(assert (= ((_ fp.to_ubv 8) RNE (fp #b0 #b10110 #b1111111100)) #x07)) (check-sat)",
         SolveOutcome::Sat),
    ];
    for (s, want) in cases {
        let (o, _) = run(s);
        assert_eq!(o, want, "boundary pin: {s}");
    }
}

#[test]
fn fp_to_sbv_int_min_and_unspecified() {
    // -128.0 → sbv8 = #x80 (INT_MIN in range); NaN → sbv8 unconstrained.
    let (o, _) = run(
        "(assert (distinct ((_ fp.to_sbv 8) RTZ (fp #b1 #b10110 #b0000000000)) #x80)) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat, "-128.0 → sbv8 is exactly #x80");
    let (o2, _) = run(
        "(assert (= ((_ fp.to_sbv 8) RNE (_ NaN 5 11)) #x11)) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Sat, "unspecified sbv value is unconstrained (can be 0x11)");
}

#[test]
fn fp_to_bv_congruence_e2e() {
    // Probe-2 shape: equal args force equal results even when unspecified.
    let (o, _) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) (declare-fun y () (_ FloatingPoint 5 11)) \
         (assert (= x y)) (assert (fp.isNaN x)) \
         (assert (distinct ((_ fp.to_ubv 8) RNE x) ((_ fp.to_ubv 8) RNE y))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat, "congruence: equal (rm, x) → equal results");
    // Probe-1 shape: different unspecified inputs may differ.
    let (o2, _) = run(
        "(declare-fun a () (_ BitVec 8)) (declare-fun b () (_ BitVec 8)) \
         (assert (= a ((_ fp.to_ubv 8) RNE (_ NaN 5 11)))) \
         (assert (= b ((_ fp.to_ubv 8) RNE (_ +oo 5 11)))) \
         (assert (distinct a b)) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Sat, "NaN and +oo results are independent");
}

#[test]
fn fp_to_bv_under_bv_atom() {
    // First legal FP subterm under a BV atom: (bvult (fp.to_ubv …) k).
    let (o, _) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) \
         (assert (fp.eq x (fp #b0 #b10100 #b0101000000))) \
         (assert (bvult ((_ fp.to_ubv 8) RTZ x) #x10)) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat, "42 < 16 is false");
    let (o2, _) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) \
         (assert (fp.eq x (fp #b0 #b10100 #b0101000000))) \
         (assert (bvult ((_ fp.to_ubv 8) RTZ x) #x30)) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Sat, "42 < 48");
}
```

- [ ] **Step 3: Run to verify the new tests pass and the suite is green**

Run: `cargo test -p shinri-solver --test fp_e2e 2>&1 | tail -5`
Expected: all pass (the Task 4 fence lift is already in). If any new test returns `Unknown`, the fence lift missed a path — debug before proceeding (check `bv_atoms_fp_supported` and the crossing walk first).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): e2e FP→BV SAT/UNSAT + boundary trio + congruence pins; repoint the crossing canary at the Real bridge (slice 4e)"
```

---

### Task 6: Differential z3 oracle

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (new generator + test after `differential_qf_bvfp_int_to_fp`, line 1174)

**Interfaces:**
- Consumes: `Lcg`, `shinri_outcome`, `z3_outcome_mixed` (fp_oracle.rs:959), `N_ITERS = 200`. Test file is gated `#[cfg(feature = "oracle")]` — match the existing attribute placement.

- [ ] **Step 1: Write the generator + test**

```rust
/// FP→BV: a random source bit-pattern (naturally hitting NaN/±inf/subnormal/
/// out-of-range) pinned via the 1-arg to_fp bitcast, converted under a random
/// face/width/mode, then related to a random BV constant. One in four scripts
/// is instead a two-application congruence probe (equal-forced operands,
/// distinct results) — the encoding must agree with z3's UF-of-(rm,x) reading.
fn gen_fp_to_bv_script(rng: &mut Lcg) -> String {
    const MS: &[u32] = &[4, 8, 16];
    let m = MS[rng.below(MS.len() as u64) as usize];
    let (eb, sb) = if rng.below(2) == 0 { (5u32, 11u32) } else { (8, 24) };
    let w = (eb + sb) as usize;
    let bits = rng.next() & if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let face = if rng.below(2) == 0 { "fp.to_ubv" } else { "fp.to_sbv" };
    const RMS: &[&str] = &["RNE", "RNA", "RTP", "RTN", "RTZ"];
    let rm = RMS[rng.below(RMS.len() as u64) as usize];
    if rng.below(4) == 0 {
        return format!(
            "(declare-fun x () (_ FloatingPoint {eb} {sb}))\n\
             (declare-fun y () (_ FloatingPoint {eb} {sb}))\n\
             (assert (= x ((_ to_fp {eb} {sb}) #b{bits:0w$b})))\n\
             (assert (= y x))\n\
             (assert (distinct ((_ {face} {m}) {rm} x) ((_ {face} {m}) {rm} y)))\n\
             (check-sat)\n"
        );
    }
    let k = rng.next() & ((1u64 << m) - 1);
    const RELS: &[&str] = &["=", "bvult", "bvule", "bvugt"];
    let rel = RELS[rng.below(RELS.len() as u64) as usize];
    let mw = m as usize;
    format!(
        "(declare-fun x () (_ FloatingPoint {eb} {sb}))\n\
         (declare-fun a () (_ BitVec {m}))\n\
         (assert (= x ((_ to_fp {eb} {sb}) #b{bits:0w$b})))\n\
         (assert (= a ((_ {face} {m}) {rm} x)))\n\
         (assert ({rel} a #b{k:0mw$b}))\n\
         (check-sat)\n"
    )
}

#[test]
fn differential_qf_bvfp_fp_to_bv() {
    let mut rng = Lcg(0x4E_F92A_11);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_fp_to_bv_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown { n_unknown += 1; continue; }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_mixed(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_BVFP FP→BV SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_bvfp_fp_to_bv: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)");
    assert!(n_unknown == 0, "no admitted-face script may fence ({n_unknown} unknown)");
    assert!(n_z3_checked > 0, "z3 never returned a concrete verdict");
}
```

(Named width args in `format!` — `{bits:0w$b}` needs `w` in scope as `usize`; if the named-capture form fights the borrow of `w`, use explicit `format!("… #b{:0width$b} …", bits, width = w)`.)

- [ ] **Step 2: Run the new oracle test**

Run: `cargo test -p shinri-solver --test fp_oracle --features oracle differential_qf_bvfp_fp_to_bv -- --nocapture 2>&1 | tail -8`
Expected: PASS with the printed sat/unsat/z3_checked line; **zero disagreements, zero unknown**. A disagreement here is a soundness bug — do NOT weaken the test; debug the encoding (suspects, in order: congruence emission, range-check bounds, RTN/RTP sign handling in `rounding_increment` wiring).

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential z3 oracle for FP→BV incl. congruence probes (slice 4e)"
```

---

### Task 7: Full-workspace verification + docs

**Files:**
- Modify: `docs/superpowers/specs/2026-07-02-shinri-qffp-slice4e-fp-to-bv-design.md` (Status line)
- Modify: `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (mark Plan 4 complete, if it tracks slice status — check its conventions against how 4c/4d were recorded)

- [ ] **Step 1: Run the full pre-existing differential oracle suite (background)**

Run in background (in-session, NOT via a subagent — standing lesson):
`cargo test -p shinri-solver --test fp_oracle --features oracle -- --nocapture`
Expected: every pre-existing count line **byte-identical** to the 4d baseline (compare against the numbers recorded in the 4d spec header); the new test's line added.

- [ ] **Step 2: Run the full workspace suite (background, ~40+ min)**

Run in background: `cargo test --workspace 2>&1 | tail -30`
Expected: EXIT 0, zero failures. The shinri-fp exhaustive gate is the long pole. While it runs, do Step 3.

- [ ] **Step 3: Stale-comment sweep**

Run: `grep -rn "to_ubv\|to_sbv" crates/ --include="*.rs" | grep -i "cross\|fence\|unknown\|not.*support\|future\|later"`
Every hit must describe the POST-4e world (admitted; remaining fence = Real bridge). Fix stragglers — this exact class of stale comment needed a follow-up commit in 4d (65d8fde).

- [ ] **Step 4: Update docs**

Spec status line → `**Status:** Landed — …` with the verification numbers (workspace exit code, suite counts, oracle sat/unsat/z3_checked counts, canaries repointed), mirroring the 4d spec's landed header. Parent design: record Plan 4 complete the same way 4c/4d were recorded.

- [ ] **Step 5: Verify workspace green, then commit**

Only after Step 2's background run exits 0:

```bash
git add -A docs crates
git commit -m "docs(qffp): mark slice-4e landed — FP→BV admitted, Plan 4 complete"
```

---

## Plan Self-Review (done at write time)

- **Spec coverage:** §3 goldens → Task 1; §4 gadget → Task 2; §5 congruence + §6 dispatch → Task 3; §6 fence + BV-atom walk → Task 4; §7 gadget gate → Task 2, congruence pins → Tasks 3/5, e2e → Task 5, oracle → Task 6, canary repoint → Tasks 4/5, workspace net → Task 7. §2 boundary semantics pinned in Tasks 1 and 5.
- **Known deliberate deviation from spec text:** `blast_fp_to_bv` as a sibling of `blast_fp_word` (sort-discipline reality), recorded in Task 3.
- **Type consistency:** `fp_to_int(b, x, eb, sb, m, signed_face, rm) -> (Vec<BitLit>, BitLit)` used identically in Tasks 2/3; `FpToBvApp` fields consistent between Tasks 3's struct and emission code; `ref_to_ubv/ref_to_sbv -> Option<Integer>` consistent across Tasks 1/2.
- **Watch-outs for the executor:** shinri-num `Integer`/`Rational` operator surface (follow `round_rational`'s idioms if `Mul`/`Sub` forms differ); `Context` test-builder API names (`mk_eq`, `mk_rm_const`, `mk_bv_const`, `declare_fun` — all used in existing tests cited by line); `format!` named width captures in Task 6.
