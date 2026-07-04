//! The shared FP rounder: ExtFp → packed word. Bit-identical to round_rational.

use crate::rm::RmSel;
use shinri_bv::blast::arith::{adder, bvadd, bvsub};
use shinri_bv::blast::shift::{bvlshr, bvshl};
use shinri_bv::{BitLit, Blaster};

/// Canonical pre-pack intermediate. See the rounder contract in the plan.
pub struct ExtFp {
    pub sign: BitLit,
    pub exp: Vec<BitLit>, // signed two's complement, width exp_w(eb)
    pub sig: Vec<BitLit>, // sb bits LSB→MSB, hidden bit at index sb-1
    pub grs: (BitLit, BitLit, BitLit), // (guard, round, sticky)
}

/// Signed exponent width: eb + 6 gives ample headroom for the largest formats
/// (verified by exhaustive (3,5) + Float32 tests).
pub fn exp_w(eb: u32) -> usize {
    eb as usize + 6
}

fn or3(b: &mut Blaster, x: BitLit, y: BitLit, z: BitLit) -> BitLit {
    let t = b.or2(x, y);
    b.or2(t, z)
}

/// Build a constant signed value of width `w` (LSB→MSB) in the Blaster.
fn const_i(b: &Blaster, w: usize, value: i128) -> Vec<BitLit> {
    let u = (value) & ((1i128 << w) - 1);
    (0..w)
        .map(|i| if (u >> i) & 1 == 1 { b.one() } else { b.zero() })
        .collect()
}

pub fn round(b: &mut Blaster, ext: ExtFp, eb: u32, sb: u32, rm: &RmSel) -> Vec<BitLit> {
    let bias = (1i128 << (eb - 1)) - 1;
    let emin = 1 - bias;
    let emax = bias;
    let ew = exp_w(eb);
    let sbu = sb as usize;

    // Working significand: [G, R, S] below sig[0]. Index 0 = S, 1 = R, 2 = G,
    // 3.. = sig (so sig[0] at index 3). Width = sbu + 3.
    let (g0, r0, s0) = ext.grs;
    let mut work: Vec<BitLit> = Vec::with_capacity(sbu + 3);
    work.push(s0);
    work.push(r0);
    work.push(g0);
    work.extend_from_slice(&ext.sig);

    // --- Step 1: subnormal denormalize. shift = max(0, emin - exp). ---
    // shift_amt = emin - exp (signed). Compute as a small unsigned, saturated.
    let emin_const = const_i(b, ew, emin);
    let shift_signed = bvsub(b, &emin_const, &ext.exp); // emin - exp
                                                        // positive iff MSB == 0 and nonzero. We right-shift `work` by `shift_signed`
                                                        // (treated unsigned; if shift_signed is "negative" i.e. exp > emin, its large
                                                        // unsigned value saturates the shifter to 0 via the overflow path, which is
                                                        // what we want only when exp >= emin). Guard: when exp >= emin, force shift 0.
    let exp_ge_emin = {
        // exp - emin >= 0  ⇔  (exp - emin) MSB == 0
        let diff = bvsub(b, &ext.exp, &emin_const);
        b.not1(diff[ew - 1])
    };
    // shift word: if exp_ge_emin then 0 else shift_signed (which is then >0, small).
    let zero_ew: Vec<BitLit> = const_i(b, ew, 0);
    let shift_word: Vec<BitLit> = (0..ew)
        .map(|i| b.mux2(exp_ge_emin, zero_ew[i], shift_signed[i]))
        .collect();
    // Sticky-collecting right shift of `work` by `shift_word`.
    let (shifted, shifted_sticky) = shift_right_sticky(b, &work, &shift_word);
    let mut work = shifted;
    work[0] = b.or2(work[0], shifted_sticky); // fold dropped bits into S
                                              // After denormalize, the effective exponent is clamped to emin when shifting
                                              // occurred. Track the post-step exponent.
    let exp_after_denorm: Vec<BitLit> = (0..ew)
        .map(|i| b.mux2(exp_ge_emin, ext.exp[i], emin_const[i]))
        .collect();

    // Re-extract S,R,G and the sb significand from `work`.
    let s = work[0];
    let r = work[1];
    let g = work[2];
    let sig: Vec<BitLit> = work[3..3 + sbu].to_vec();
    let lsb = sig[0];

    // --- Step 2: increment decision (shared with fp.roundToIntegral). ---
    let inc = rounding_increment(b, ext.sign, g, r, s, lsb, rm);

    // --- Step 3: add inc to the sb-bit significand; detect carry-out. ---
    let mut addend: Vec<BitLit> = vec![b.zero(); sbu];
    addend[0] = inc;
    let (sum, carry) = adder(b, &sig, &addend, b.zero());
    // On carry-out (sig was all ones → 2^sb), shift right 1 and exp += 1.
    // After increment the significand width is sbu; carry means hidden overflowed.
    let one_ew = const_i(b, ew, 1);
    let exp_plus1 = bvadd(b, &exp_after_denorm, &one_ew);
    let final_exp: Vec<BitLit> = (0..ew)
        .map(|i| b.mux2(carry, exp_plus1[i], exp_after_denorm[i]))
        .collect();
    // sig after possible 1-bit normalize: if carry, the new significand is
    // (sum >> 1) with the carry as the new MSB (value 2^(sb-1)). Since sum was
    // all-zero after wrap (2^sb mod 2^sb = 0), shifting gives the hidden bit set.
    let mut norm_sig: Vec<BitLit> = Vec::with_capacity(sbu);
    for i in 0..sbu {
        let shifted_bit = if i + 1 < sbu { sum[i + 1] } else { b.one() }; // carry fills top
        norm_sig.push(b.mux2(carry, shifted_bit, sum[i]));
    }

    // --- Step 4: overflow. exp_signed > emax. Saturation is mode-dependent
    // (IEEE-754 / SMT-LIB FP): RNE/RNA -> +-infinity; RTZ -> +-max_finite;
    // RTP -> +infinity / -max_finite; RTN -> +max_finite / -infinity. ---
    let emax_const = const_i(b, ew, emax);
    // overflow iff final_exp > emax (signed). final_exp - emax > 0 and not negative.
    let over_diff = bvsub(b, &final_exp, &emax_const);
    let over_pos = b.not1(over_diff[ew - 1]);
    let over_nonzero = {
        let mut acc = b.zero();
        for &bit in &over_diff {
            acc = b.or2(acc, bit);
        }
        acc
    };
    let overflow = b.and2(over_pos, over_nonzero);
    // sat_to_max = Rtz | (Rtp & sign) | (Rtn & !sign). RmSel.sel order is
    // [Rne, Rna, Rtp, Rtn, Rtz] (indices 0..4).
    let not_sign = b.not1(ext.sign);
    let rtp_sat = b.and2(rm.sel[2], ext.sign);
    let rtn_sat = b.and2(rm.sel[3], not_sign);
    let sat_to_max = {
        let t = b.or2(rm.sel[4], rtp_sat);
        b.or2(t, rtn_sat)
    };

    // --- Step 5: pack sign | biased_exp | trailing. ---
    // biased_exp = final_exp + bias, truncated to eb bits. Subnormal-clamped case:
    // when the significand's hidden bit is 0 the value is subnormal and the biased
    // field is 0 — but final_exp already equals emin there and (emin + bias) = 1,
    // so we special-case: if hidden bit (norm_sig[sb-1]) == 0 ⇒ exp field 0.
    let bias_const = const_i(b, ew, bias);
    let biased = bvadd(b, &final_exp, &bias_const);
    let hidden = norm_sig[sbu - 1];
    let not_hidden = b.not1(hidden);
    let exp_all_ones: Vec<BitLit> = (0..eb as usize).map(|_| b.one()).collect();
    let zero_eb: Vec<BitLit> = (0..eb as usize).map(|_| b.zero()).collect();
    // max-finite exponent field: all ones except LSB 0 (value 2^eb - 2).
    let exp_max_finite: Vec<BitLit> = (0..eb as usize)
        .map(|i| if i == 0 { b.zero() } else { b.one() })
        .collect();

    let mut out: Vec<BitLit> = Vec::with_capacity((eb + sb) as usize);
    // trailing significand sig[0..sb-1]; zeroed on infinity-overflow, all ones
    // on max_finite-overflow.
    #[allow(clippy::needless_range_loop)] // norm_sig[i] — index is the operand, not just a counter
    for i in 0..(sbu - 1) {
        let non_overflow = norm_sig[i];
        let overflow_bit = b.mux2(sat_to_max, b.one(), b.zero());
        out.push(b.mux2(overflow, overflow_bit, non_overflow));
    }
    // exponent field eb bits.
    for i in 0..(eb as usize) {
        // normal: biased[i]; subnormal (not_hidden): 0; overflow: all-ones or
        // max-finite depending on sat_to_max.
        let normal_or_sub = b.mux2(not_hidden, zero_eb[i], biased[i]);
        let overflow_bit = b.mux2(sat_to_max, exp_max_finite[i], exp_all_ones[i]);
        out.push(b.mux2(overflow, overflow_bit, normal_or_sub));
    }
    // sign bit (preserved through overflow).
    out.push(ext.sign);
    out
}

/// Per-RM "add one ulp?" decision, shared by `round()` and `fp.roundToIntegral`.
/// `sign` is the result sign; `g`/`r`/`s` are guard/round/sticky; `lsb` is the
/// significand's least-significant retained bit (for RNE tie-to-even).
pub fn rounding_increment(
    b: &mut Blaster,
    sign: BitLit,
    g: BitLit,
    r: BitLit,
    s: BitLit,
    lsb: BitLit,
    rm: &RmSel,
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
    for (sel, val) in rm
        .sel
        .iter()
        .zip([inc_rne, inc_rna, inc_rtp, inc_rtn, inc_rtz])
    {
        let t = b.and2(*sel, val);
        inc = b.or2(inc, t);
    }
    inc
}

/// Right-shift `x` (LSB→MSB) by `amt` (unsigned LSB→MSB), returning the shifted
/// word AND a sticky bit = OR of every bit shifted out below index 0. Built from
/// `bvlshr` plus a parallel sticky: a bit is "lost" iff it was set and its index
/// < amt. Implemented as: lost = x AND NOT(mask of kept positions); sticky = OR(lost).
pub fn shift_right_sticky(b: &mut Blaster, x: &[BitLit], amt: &[BitLit]) -> (Vec<BitLit>, BitLit) {
    let n = x.len();
    let shifted = bvlshr(b, x, amt);
    // Reconstruct dropped bits: drop = x XOR (shifted << amt) is fragile; instead
    // shift `shifted` back left and compare to x — any difference was dropped.
    let back = bvshl(b, &shifted, amt);
    let mut sticky = b.zero();
    for i in 0..n {
        let diff = b.xor2(x[i], back[i]); // 1 where a set bit was lost
        sticky = b.or2(sticky, diff);
    }
    (shifted, sticky)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{round_rational, RoundMode};
    use crate::rm;
    use shinri_num::{Integer, Rational};
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn eval_word(b: Blaster, word: &[BitLit]) -> u64 {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars {
            s.new_var();
        }
        for c in &cnf.clauses {
            let ls: Vec<Lit> = c
                .iter()
                .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
                .collect();
            s.add_clause(&ls);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let mut v = 0u64;
        for (i, bl) in word.iter().enumerate() {
            let raw = s.value_of(Var::new(bl.var)).unwrap();
            if if bl.pos { raw } else { !raw } {
                v |= 1 << i;
            }
        }
        v
    }

    /// Build the rounder input (normalized contract) for a finite nonzero value.
    /// Returns (sign, exp_signed, sig: Vec<bool> LSB→MSB of len sb, g, r, s).
    fn decompose(eb: u32, sb: u32, value: &Rational) -> (bool, i64, Vec<bool>, bool, bool, bool) {
        let _ = eb;
        let zero = Rational::new(Integer::zero(), Integer::one());
        let sign = *value < zero;
        let neg1 = Rational::new(Integer::from(-1i64), Integer::one());
        let mag = if sign {
            neg1 * value.clone()
        } else {
            value.clone()
        };
        let two = Rational::new(Integer::from(2u64), Integer::one());
        let half = Rational::new(Integer::one(), Integer::from(2u64));
        // E = floor(log2(mag)); m = mag / 2^E ∈ [1,2)
        let mut e: i64 = 0;
        let mut m = mag.clone();
        while m >= two {
            m = m * half.clone();
            e += 1;
        }
        while m < Rational::new(Integer::one(), Integer::one()) {
            m = m * two.clone();
            e -= 1;
        }
        // X = m * 2^(sb-1) ∈ [2^(sb-1), 2^sb): the normalized significand + fraction.
        let mut scale = Integer::one();
        for _ in 0..(sb - 1) {
            scale *= Integer::from(2u64);
        }
        let x = m * Rational::new(scale, Integer::one());
        let isig = x.numer().div_rem(&x.denom()).0; // floor
        let frac = x.clone() - Rational::new(isig.clone(), Integer::one()); // [0,1)
                                                                            // G,R,S from frac.
        let f2 = frac * two.clone();
        let g_int = f2.numer().div_rem(&f2.denom()).0;
        let g = !g_int.is_zero();
        let f2b = f2 - Rational::new(g_int, Integer::one());
        let f4 = f2b * Rational::new(Integer::from(2u64), Integer::one());
        let r_int = f4.numer().div_rem(&f4.denom()).0;
        let r = !r_int.is_zero();
        let f4b = f4 - Rational::new(r_int, Integer::one());
        let s = f4b != zero;
        // sig bits LSB→MSB.
        let mut sig = Vec::with_capacity(sb as usize);
        let mut rem = isig.clone();
        let two_i = Integer::from(2u64);
        for _ in 0..sb {
            let (q, rr) = rem.div_rem(&two_i);
            sig.push(!rr.is_zero());
            rem = q;
        }
        (sign, e, sig, g, r, s)
    }

    #[allow(clippy::too_many_arguments)] // test helper — bundling into a struct is a larger refactor
    fn build_ext(
        b: &Blaster,
        eb: u32,
        sb: u32,
        sign: bool,
        exp: i64,
        sig: &[bool],
        g: bool,
        r: bool,
        s: bool,
    ) -> ExtFp {
        let bit = |x: bool| if x { b.one() } else { b.zero() };
        let ew = exp_w(eb);
        // two's-complement exp.
        let uexp = (exp as i128) & ((1i128 << ew) - 1);
        let expv: Vec<BitLit> = (0..ew).map(|i| bit((uexp >> i) & 1 == 1)).collect();
        let sigv: Vec<BitLit> = sig.iter().map(|&x| bit(x)).collect();
        let _ = sb;
        ExtFp {
            sign: bit(sign),
            exp: expv,
            sig: sigv,
            grs: (bit(g), bit(r), bit(s)),
        }
    }

    fn rmode(rm: RoundMode) -> shinri_core::RoundingMode {
        match rm {
            RoundMode::Rne => shinri_core::RoundingMode::Rne,
            RoundMode::Rna => shinri_core::RoundingMode::Rna,
            RoundMode::Rtp => shinri_core::RoundingMode::Rtp,
            RoundMode::Rtn => shinri_core::RoundingMode::Rtn,
            RoundMode::Rtz => shinri_core::RoundingMode::Rtz,
        }
    }

    #[test]
    fn round_matches_reference_tiny_exhaustive() {
        let (eb, sb) = (3u32, 5u32);
        let modes = [
            RoundMode::Rne,
            RoundMode::Rna,
            RoundMode::Rtp,
            RoundMode::Rtn,
            RoundMode::Rtz,
        ];
        // Enumerate every value REPRESENTABLE as a starting magnitude by decoding
        // each (3,5) finite pattern to its rational, then re-rounding — plus a set
        // of between-grid rationals to exercise G/R/S. We iterate all 256 patterns
        // and, for finite non-zero ones, also test the midpoint to the next pattern.
        use crate::reference::{class_to_rational, decode, FpClass};
        for pat in 0u64..256 {
            let cls = decode(eb, sb, &Integer::from(pat));
            if matches!(
                cls,
                FpClass::Nan | FpClass::Inf { .. } | FpClass::Zero { .. }
            ) {
                continue;
            }
            let v = class_to_rational(eb, sb, &cls).unwrap();
            // also a value 3/8 of the way to the next ULP up, to force rounding.
            let ulp_probe = v.clone()
                + Rational::new(
                    Integer::from(3u64),
                    Integer::from(8u64) * {
                        let mut p = Integer::one();
                        for _ in 0..(sb - 1) {
                            p *= Integer::from(2u64);
                        }
                        p
                    },
                );
            for value in [v.clone(), ulp_probe.clone()] {
                for m in modes {
                    let want = round_rational(eb, sb, &value, m);
                    let (sg, e, sig, g, r, s) = decompose(eb, sb, &value);
                    let mut b = Blaster::new();
                    let ext = build_ext(&b, eb, sb, sg, e, &sig, g, r, s);
                    let sel = rm::literal(&b, rmode(m));
                    let word = round(&mut b, ext, eb, sb, &sel);
                    assert_eq!(
                        Integer::from(eval_word(b, &word)),
                        want,
                        "round mismatch pat={pat:#x} value!=grid m={m:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn round_overflow_saturates_by_mode() {
        // (3,5): +inf=0x70, +max_finite=0x6F, -inf=0xF0, -max_finite=0xEF.
        // exp = emax+1 = 4 (unbiased) forces overflow; sig all ones (hidden set).
        let (eb, sb) = (3u32, 5u32);
        let emax: i64 = (1i64 << (eb - 1)) - 1; // 3
        let sig = [true; 5]; // all ones, hidden bit (top) set.
        let cases: [(bool, RoundMode, u64); 10] = [
            (false, RoundMode::Rne, 0x70),
            (false, RoundMode::Rna, 0x70),
            (false, RoundMode::Rtz, 0x6F),
            (false, RoundMode::Rtp, 0x70),
            (false, RoundMode::Rtn, 0x6F),
            (true, RoundMode::Rne, 0xF0),
            (true, RoundMode::Rna, 0xF0),
            (true, RoundMode::Rtz, 0xEF),
            (true, RoundMode::Rtp, 0xEF),
            (true, RoundMode::Rtn, 0xF0),
        ];
        for (sign, m, want) in cases {
            let mut b = Blaster::new();
            let ext = build_ext(&b, eb, sb, sign, emax + 1, &sig, false, false, false);
            let sel = rm::literal(&b, rmode(m));
            let word = round(&mut b, ext, eb, sb, &sel);
            assert_eq!(eval_word(b, &word), want, "sign={sign} mode={m:?}");
        }
    }

    #[test]
    fn round_matches_reference_float32_random() {
        let (eb, sb) = (8u32, 24u32);
        let modes = [
            RoundMode::Rne,
            RoundMode::Rna,
            RoundMode::Rtp,
            RoundMode::Rtn,
            RoundMode::Rtz,
        ];
        // deterministic LCG
        let mut state: u64 = 0xD1CE_5EED;
        let mut next = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            state >> 16
        };
        for _ in 0..400 {
            // random rational n/d with modest magnitude incl. subnormal range.
            let n = (next() % 2_000_000) as i64 - 1_000_000;
            if n == 0 {
                continue;
            }
            let d = 1i64 << (next() % 30); // up to 2^29 → reaches subnormals
            let value = Rational::new(
                Integer::from(n.unsigned_abs())
                    * if n < 0 {
                        Integer::from(-1i64)
                    } else {
                        Integer::one()
                    },
                Integer::from(d as u64),
            );
            for m in modes {
                let want = round_rational(eb, sb, &value, m);
                let (sg, e, sig, g, r, s) = decompose(eb, sb, &value);
                let mut b = Blaster::new();
                let ext = build_ext(&b, eb, sb, sg, e, &sig, g, r, s);
                let sel = rm::literal(&b, rmode(m));
                let word = round(&mut b, ext, eb, sb, &sel);
                assert_eq!(
                    Integer::from(eval_word(b, &word)),
                    want,
                    "fp32 round n={n} d={d} m={m:?}"
                );
            }
        }
    }
}
