//! Exact-rational rows for the fp.to_real bridge (QF_FP slice 9). For a format
//! (eb,sb) and a concrete (sign, biased-exponent-field e), the finite value is
//! `(-1)^sign * significand * 2^(e - bias - (sb-1))` (reference::class_to_rational),
//! re-expressed as a linear form `K + Σ coeffs[i]*bit_i` over the (sb-1)
//! significand bits so the solver can pin it under an exponent guard.

use shinri_num::{Integer, Rational};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteRow {
    pub k: Rational,
    pub coeffs: Vec<Rational>, // len == sb-1, LSB first
}

/// 2^k as a Rational (k may be negative).
fn pow2(k: i64) -> Rational {
    let mut acc = Integer::one();
    let two = Integer::from(2u64);
    for _ in 0..k.unsigned_abs() {
        acc *= two.clone();
    }
    if k >= 0 {
        Rational::new(acc, Integer::one())
    } else {
        Rational::new(Integer::one(), acc)
    }
}

/// The finite fp.to_real row for (sign, exponent-field `e`); `None` iff `e` is
/// all-ones (NaN/Inf — the caller emits the special-constant rows instead).
pub fn to_real_finite_row(eb: u32, sb: u32, sign: bool, e: u64) -> Option<FiniteRow> {
    let all_ones = (1u64 << eb) - 1;
    if e == all_ones {
        return None;
    }
    let bias = (1i64 << (eb - 1)) - 1;
    let sgn = if sign {
        Rational::new(Integer::from(-1i64), Integer::one())
    } else {
        Rational::new(Integer::one(), Integer::one())
    };
    // Normal: scale 2^(e-bias-(sb-1)), hidden bit 2^(sb-1).
    // Subnormal/zero (e==0): scale 2^(1-bias-(sb-1)), no hidden bit.
    let (scale, hidden) = if e == 0 {
        (pow2(1 - bias - (sb as i64 - 1)), Integer::zero())
    } else {
        let mut h = Integer::one();
        for _ in 0..(sb - 1) {
            h *= Integer::from(2u64);
        }
        (pow2(e as i64 - bias - (sb as i64 - 1)), h)
    };
    let k = sgn.clone() * Rational::new(hidden, Integer::one()) * scale.clone();
    let coeffs = (0..(sb - 1))
        .map(|i| sgn.clone() * pow2(i as i64) * scale.clone())
        .collect();
    Some(FiniteRow { k, coeffs })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{class_to_rational, decode};

    /// 2^k as a non-negative Integer (k >= 0), mirroring reference.rs's local
    /// pow-by-repeated-mul idiom (Integer has no Shl operator).
    fn pow2i(k: u32) -> Integer {
        let mut acc = Integer::one();
        let two = Integer::from(2u64);
        for _ in 0..k {
            acc *= two.clone();
        }
        acc
    }

    // Reconstruct the (eb+sb)-bit integer from (sign, e, sig) and compare the
    // row's K + Σ coeffs[i]*bit_i against the golden class_to_rational.
    fn check(eb: u32, sb: u32, sign: bool, e: u64, sig: u64) {
        let w = eb + sb;
        let bits: Integer = Integer::from(sign as u64) * pow2i(w - 1)
            + Integer::from(e) * pow2i(sb - 1)
            + Integer::from(sig);
        let golden = class_to_rational(eb, sb, &decode(eb, sb, &bits));
        match to_real_finite_row(eb, sb, sign, e) {
            None => assert!(golden.is_none(), "all-ones must be NaN/Inf: {eb} {sb} {e}"),
            Some(row) => {
                assert_eq!(row.coeffs.len(), (sb - 1) as usize);
                let mut v = row.k.clone();
                for i in 0..(sb - 1) {
                    if (sig >> i) & 1 == 1 {
                        v = v + row.coeffs[i as usize].clone();
                    }
                }
                assert_eq!(Some(v), golden, "mismatch eb={eb} sb={sb} s={sign} e={e} sig={sig}");
            }
        }
    }

    #[test]
    fn f16_rows_match_reference() {
        let (eb, sb) = (5u32, 11u32);
        for e in 0..(1u64 << eb) {
            for &sign in &[false, true] {
                for &sig in &[0u64, 1, 5, (1 << (sb - 1)) - 1] {
                    check(eb, sb, sign, e, sig);
                }
            }
        }
    }

    #[test]
    fn f32_normal_subnormal_zero_match_reference() {
        let (eb, sb) = (8u32, 24u32);
        for &e in &[0u64, 1, 127, 200, (1 << eb) - 2] {
            for &sign in &[false, true] {
                for &sig in &[0u64, 1, 12345, (1 << (sb - 1)) - 1] {
                    check(eb, sb, sign, e, sig);
                }
            }
        }
    }

    #[test]
    fn signed_zero_is_zero() {
        let row = to_real_finite_row(5, 11, true, 0).unwrap();
        assert_eq!(row.k, Rational::zero()); // e=0,sig=0 ⇒ 0
    }
}
