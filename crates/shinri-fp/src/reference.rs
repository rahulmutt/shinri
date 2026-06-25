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
    // scale = 2^(-target_exp): mag / 2^target_exp gives the normalised mantissa m.
    let scale = {
        let mut acc = Integer::one();
        let two = Integer::from(2u64);
        let k = target_exp.unsigned_abs();
        for _ in 0..k { acc = acc * two.clone(); }
        if target_exp >= 0 { Rational::new(Integer::one(), acc) } else { Rational::new(acc, Integer::one()) }
    };
    // value / 2^target_exp, then * 2^frac_bits  => m * 2^frac_bits
    let mut scaled = mag.clone() * scale; // = mag / 2^target_exp = m (1 <= m < 2 for normals)
    let pow_frac = {
        let mut acc = Integer::one();
        let two = Integer::from(2u64);
        for _ in 0..frac_bits.max(0) { acc = acc * two.clone(); }
        Rational::new(acc, Integer::one())
    };
    scaled = scaled * pow_frac;

    // Split into integer quotient q and remainder fraction for rounding.
    let q = scaled.numer().div_rem(&scaled.denom()).0; // floor(scaled) since scaled >= 0
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
}
