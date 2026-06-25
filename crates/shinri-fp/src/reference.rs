//! Exact scalar reference oracle for QF_FP — the trusted golden semantics.
//! Slice 1 covers decode + classification + fp.eq/core-= + abs/neg.
//! Bit layout MSB->LSB: [ sign(1) | exp(eb) | trailing-sig(sb-1) ], W = eb+sb.

use shinri_num::Integer;

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
    // NaN is neither negative nor positive (per IEEE 754 / SMT-LIB).
    // Signed zeros DO carry a sign: fp.isNegative(-0) = true.
    match c {
        FpClass::Nan => false,
        FpClass::Zero { sign }
        | FpClass::Inf { sign }
        | FpClass::Subnormal { sign, .. }
        | FpClass::Normal { sign, .. } => *sign,
    }
}

pub fn ref_is_positive(c: &FpClass) -> bool {
    // NaN is neither negative nor positive (per IEEE 754 / SMT-LIB).
    // Signed zeros DO carry a sign: fp.isPositive(+0) = true.
    match c {
        FpClass::Nan => false,
        FpClass::Zero { sign }
        | FpClass::Inf { sign }
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
