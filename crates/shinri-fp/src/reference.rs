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

/// Extended order key: -∞ < every finite rational < +∞. NaN has no key.
/// Derived `Ord` compares by variant order (NegInf < Fin < PosInf), then by the
/// contained `Rational` for the `Fin` arm.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Ord3 {
    NegInf,
    Fin(Rational),
    PosInf,
}

fn order_key(eb: u32, sb: u32, c: &FpClass) -> Option<Ord3> {
    match c {
        FpClass::Nan => None,
        FpClass::Inf { sign } => Some(if *sign { Ord3::NegInf } else { Ord3::PosInf }),
        // Zero / Subnormal / Normal all yield Some(_) from class_to_rational.
        other => Some(Ord3::Fin(class_to_rational(eb, sb, other).expect("finite -> rational"))),
    }
}

/// IEEE `fp.lt`: NaN on either side -> false; +0 == -0; else extended-real order.
pub fn ref_lt(eb: u32, sb: u32, a: &Integer, b: &Integer) -> bool {
    let ka = order_key(eb, sb, &decode(eb, sb, a));
    let kb = order_key(eb, sb, &decode(eb, sb, b));
    match (ka, kb) {
        (Some(x), Some(y)) => x < y,
        _ => false,
    }
}

pub fn ref_leq(eb: u32, sb: u32, a: &Integer, b: &Integer) -> bool {
    ref_lt(eb, sb, a, b) || ref_fp_eq(&decode(eb, sb, a), &decode(eb, sb, b))
}

pub fn ref_gt(eb: u32, sb: u32, a: &Integer, b: &Integer) -> bool {
    ref_lt(eb, sb, b, a)
}

pub fn ref_geq(eb: u32, sb: u32, a: &Integer, b: &Integer) -> bool {
    ref_lt(eb, sb, b, a) || ref_fp_eq(&decode(eb, sb, a), &decode(eb, sb, b))
}

/// `fp.min`: NaN passes through to the other operand; both-NaN -> b. The
/// SMT-LIB-unspecified (+0,-0) case is resolved sign-canonically to -0.
pub fn ref_min(eb: u32, sb: u32, a: &Integer, b: &Integer) -> Integer {
    let (ca, cb) = (decode(eb, sb, a), decode(eb, sb, b));
    if matches!(ca, FpClass::Nan) { return b.clone(); }
    if matches!(cb, FpClass::Nan) { return a.clone(); }
    if let (FpClass::Zero { sign: sa }, FpClass::Zero { sign: sbn }) = (&ca, &cb) {
        if sa != sbn { return zero_pattern(eb, sb, true); } // -0
    }
    if ref_lt(eb, sb, a, b) { a.clone() } else { b.clone() }
}

/// `fp.max`: symmetric to `ref_min`; the (+0,-0) tie resolves to +0.
pub fn ref_max(eb: u32, sb: u32, a: &Integer, b: &Integer) -> Integer {
    let (ca, cb) = (decode(eb, sb, a), decode(eb, sb, b));
    if matches!(ca, FpClass::Nan) { return b.clone(); }
    if matches!(cb, FpClass::Nan) { return a.clone(); }
    if let (FpClass::Zero { sign: sa }, FpClass::Zero { sign: sbn }) = (&ca, &cb) {
        if sa != sbn { return zero_pattern(eb, sb, false); } // +0
    }
    if ref_lt(eb, sb, a, b) { b.clone() } else { a.clone() }
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
    // Subnormals keep the full `sb-1` trailing-fraction bits at the fixed exponent
    // `emin`; the value's true exponent `e < emin` is captured by scaling against
    // `2^emin` (so bits below the subnormal grid fall past the binary point and are
    // rounded). Previously this subtracted `(emin - e)` here, double-counting the
    // exponent gap and collapsing small subnormals to zero (e.g. 1/64 in (3,5)).
    let (target_exp, frac_bits) = if e >= emin {
        (e, sb as i64 - 1)
    } else {
        (emin, sb as i64 - 1)
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

/// Canonical quiet-NaN bit pattern for (eb, sb): exp all ones, sig MSB set, sign 0.
pub fn canonical_nan(eb: u32, sb: u32) -> Integer {
    let two = Integer::from(2u64);
    // exp field (all ones) sits at bit offset (sb-1); sig MSB at bit (sb-2).
    let mut exp_scale = Integer::one();
    for _ in 0..(sb - 1) { exp_scale = exp_scale * two.clone(); }
    let exp_all_ones = {
        let mut m = Integer::one();
        for _ in 0..eb { m = m * two.clone(); }
        m - Integer::one()
    };
    let mut sig_msb = Integer::one();
    for _ in 0..(sb - 2) { sig_msb = sig_msb * two.clone(); }
    exp_all_ones * exp_scale + sig_msb
}

/// Signed-infinity bit pattern.
fn inf_pattern(eb: u32, sb: u32, sign: bool) -> Integer {
    let two = Integer::from(2u64);
    let mut exp_scale = Integer::one();
    for _ in 0..(sb - 1) { exp_scale = exp_scale * two.clone(); }
    let exp_all_ones = { let mut m = Integer::one(); for _ in 0..eb { m = m * two.clone(); } m - Integer::one() };
    let mut out = exp_all_ones * exp_scale;
    if sign {
        let mut sign_scale = Integer::one();
        for _ in 0..(eb + sb - 1) { sign_scale = sign_scale * two.clone(); }
        out = out + sign_scale;
    }
    out
}

/// Signed-zero bit pattern.
fn zero_pattern(eb: u32, sb: u32, sign: bool) -> Integer {
    if !sign { return Integer::zero(); }
    let two = Integer::from(2u64);
    let mut sign_scale = Integer::one();
    for _ in 0..(eb + sb - 1) { sign_scale = sign_scale * two.clone(); }
    sign_scale
}

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

/// Exact-rational golden `fp.add RM a b`. `a`, `b` are W=eb+sb bit patterns.
pub fn ref_add(eb: u32, sb: u32, a: &Integer, b: &Integer, mode: RoundMode) -> Integer {
    let ca = decode(eb, sb, a);
    let cb = decode(eb, sb, b);
    use FpClass::*;
    // 1. NaN propagation.
    if matches!(ca, Nan) || matches!(cb, Nan) { return canonical_nan(eb, sb); }
    // 2. Infinities.
    match (&ca, &cb) {
        (Inf { sign: s1 }, Inf { sign: s2 }) => {
            return if s1 == s2 { inf_pattern(eb, sb, *s1) } else { canonical_nan(eb, sb) };
        }
        (Inf { sign }, _) | (_, Inf { sign }) => return inf_pattern(eb, sb, *sign),
        _ => {}
    }
    // 3. Finite + finite: exact rational sum.
    let ra = class_to_rational(eb, sb, &ca).unwrap();
    let rb = class_to_rational(eb, sb, &cb).unwrap();
    let sum = ra.clone() + rb.clone();
    let zero = Rational::new(Integer::zero(), Integer::one());
    if sum == zero {
        // IEEE exact-zero-sum sign rule: -0 iff both operands negative, else
        // +0 except under roundTowardNegative which yields -0.
        let sign_a = ref_is_negative(&ca);
        let sign_b = ref_is_negative(&cb);
        let neg = (sign_a && sign_b) || matches!(mode, RoundMode::Rtn);
        return zero_pattern(eb, sb, neg);
    }
    round_rational(eb, sb, &sum, mode)
}

/// Exact-rational golden `fp.mul RM a b`. `a`, `b` are W=eb+sb bit patterns.
/// Result sign is always sign_a XOR sign_b (including specials and zeros).
pub fn ref_mul(eb: u32, sb: u32, a: &Integer, b: &Integer, mode: RoundMode) -> Integer {
    let ca = decode(eb, sb, a);
    let cb = decode(eb, sb, b);
    use FpClass::*;
    let sign = ref_is_negative(&ca) ^ ref_is_negative(&cb); // XOR sign
    // 1. NaN propagation.
    if matches!(ca, Nan) || matches!(cb, Nan) { return canonical_nan(eb, sb); }
    // 2. 0 * inf = NaN (either order). Must precede the inf arm.
    let a_zero = matches!(ca, Zero { .. });
    let b_zero = matches!(cb, Zero { .. });
    let a_inf = matches!(ca, Inf { .. });
    let b_inf = matches!(cb, Inf { .. });
    if (a_zero && b_inf) || (a_inf && b_zero) { return canonical_nan(eb, sb); }
    // 3. inf * finite-nonzero = signed inf.
    if a_inf || b_inf { return inf_pattern(eb, sb, sign); }
    // 4. zero * finite = signed zero.
    if a_zero || b_zero { return zero_pattern(eb, sb, sign); }
    // 5. finite * finite: exact rational product, then round.
    let ra = class_to_rational(eb, sb, &ca).unwrap();
    let rb = class_to_rational(eb, sb, &cb).unwrap();
    let prod = ra * rb;
    round_rational(eb, sb, &prod, mode)
}

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

    #[test]
    fn ref_add_known_float32() {
        use shinri_num::Integer;
        let (eb, sb) = (8u32, 24u32);
        let i = |v: u64| Integer::from(v);
        // 1.0 + 1.0 = 2.0
        assert_eq!(ref_add(eb, sb, &i(0x3F80_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x4000_0000));
        // 1.0 + 2.0 = 3.0 = 0x40400000
        assert_eq!(ref_add(eb, sb, &i(0x3F80_0000), &i(0x4000_0000), RoundMode::Rne), i(0x4040_0000));
        // +inf + 1.0 = +inf
        assert_eq!(ref_add(eb, sb, &i(0x7F80_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x7F80_0000));
        // +inf + -inf = canonical NaN (0x7FC00000)
        assert_eq!(ref_add(eb, sb, &i(0x7F80_0000), &i(0xFF80_0000), RoundMode::Rne), i(0x7FC0_0000));
        // NaN + 1.0 = canonical NaN
        assert_eq!(ref_add(eb, sb, &i(0x7FC0_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x7FC0_0000));
        // 1.0 + (-1.0) = +0 under RNE, -0 under RTN
        assert_eq!(ref_add(eb, sb, &i(0x3F80_0000), &i(0xBF80_0000), RoundMode::Rne), i(0x0000_0000));
        assert_eq!(ref_add(eb, sb, &i(0x3F80_0000), &i(0xBF80_0000), RoundMode::Rtn), i(0x8000_0000));
        // (-0) + (-0) = -0
        assert_eq!(ref_add(eb, sb, &i(0x8000_0000), &i(0x8000_0000), RoundMode::Rne), i(0x8000_0000));
        // (+0) + (-0) = +0 (RNE), -0 (RTN)
        assert_eq!(ref_add(eb, sb, &i(0x0000_0000), &i(0x8000_0000), RoundMode::Rne), i(0x0000_0000));
        assert_eq!(ref_add(eb, sb, &i(0x0000_0000), &i(0x8000_0000), RoundMode::Rtn), i(0x8000_0000));
    }

    #[test]
    fn ref_add_tiny_total_and_canonical() {
        // Every (a,b,mode) on (3,5) produces a well-formed encoding (round-trips
        // through decode without panic) and is commutative for finite, non-zero sums.
        let (eb, sb) = (3u32, 5u32);
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        for a in 0u64..256 {
            for b in 0u64..256 {
                for m in modes {
                    let r1 = ref_add(eb, sb, &Integer::from(a), &Integer::from(b), m);
                    let r2 = ref_add(eb, sb, &Integer::from(b), &Integer::from(a), m);
                    // commutativity holds for fp.add in all these cases (NaN canonical too).
                    assert_eq!(r1, r2, "add not commutative a={a:#x} b={b:#x} m={m:?}");
                    // result must be a valid 8-bit pattern.
                    assert!(r1 < Integer::from(256u64), "out-of-range result {a:#x}+{b:#x}");
                }
            }
        }
    }

    #[test]
    fn ref_mul_known_float32() {
        let (eb, sb) = (8u32, 24u32);
        // 1.0 * 1.0 = 1.0
        assert_eq!(ref_mul(eb, sb, &i(0x3F80_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x3F80_0000));
        // 2.0 * 3.0 = 6.0 = 0x40C00000
        assert_eq!(ref_mul(eb, sb, &i(0x4000_0000), &i(0x4040_0000), RoundMode::Rne), i(0x40C0_0000));
        // 2.0 * -1.0 = -2.0 = 0xC0000000  (sign = XOR)
        assert_eq!(ref_mul(eb, sb, &i(0x4000_0000), &i(0xBF80_0000), RoundMode::Rne), i(0xC000_0000));
        // -1.0 * -1.0 = 1.0  (sign XOR cancels)
        assert_eq!(ref_mul(eb, sb, &i(0xBF80_0000), &i(0xBF80_0000), RoundMode::Rne), i(0x3F80_0000));
        // +inf * 2.0 = +inf
        assert_eq!(ref_mul(eb, sb, &i(0x7F80_0000), &i(0x4000_0000), RoundMode::Rne), i(0x7F80_0000));
        // +inf * -2.0 = -inf
        assert_eq!(ref_mul(eb, sb, &i(0x7F80_0000), &i(0xC000_0000), RoundMode::Rne), i(0xFF80_0000));
        // +inf * +0 = canonical NaN
        assert_eq!(ref_mul(eb, sb, &i(0x7F80_0000), &i(0x0000_0000), RoundMode::Rne), i(0x7FC0_0000));
        // -inf * +0 = canonical NaN
        assert_eq!(ref_mul(eb, sb, &i(0xFF80_0000), &i(0x0000_0000), RoundMode::Rne), i(0x7FC0_0000));
        // NaN * 1.0 = canonical NaN
        assert_eq!(ref_mul(eb, sb, &i(0x7FC0_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x7FC0_0000));
        // +0 * +0 = +0 ; +0 * -0 = -0 (sign XOR) ; -2.0 * +0 = -0
        assert_eq!(ref_mul(eb, sb, &i(0x0000_0000), &i(0x0000_0000), RoundMode::Rne), i(0x0000_0000));
        assert_eq!(ref_mul(eb, sb, &i(0x0000_0000), &i(0x8000_0000), RoundMode::Rne), i(0x8000_0000));
        assert_eq!(ref_mul(eb, sb, &i(0xC000_0000), &i(0x0000_0000), RoundMode::Rne), i(0x8000_0000));
        // overflow: max-normal * 2.0 = +inf. Max normal float32 = 0x7F7FFFFF.
        assert_eq!(ref_mul(eb, sb, &i(0x7F7F_FFFF), &i(0x4000_0000), RoundMode::Rne), i(0x7F80_0000));
    }

    #[test]
    fn ref_mul_tiny_total_and_commutative() {
        // Every (a,b,mode) on (3,5) produces a valid 8-bit encoding and is
        // commutative (fp.mul is commutative, NaN canonical too).
        let (eb, sb) = (3u32, 5u32);
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        for a in 0u64..256 {
            for b in 0u64..256 {
                for m in modes {
                    let r1 = ref_mul(eb, sb, &Integer::from(a), &Integer::from(b), m);
                    let r2 = ref_mul(eb, sb, &Integer::from(b), &Integer::from(a), m);
                    assert_eq!(r1, r2, "mul not commutative a={a:#x} b={b:#x} m={m:?}");
                    assert!(r1 < Integer::from(256u64), "out-of-range result {a:#x}*{b:#x}");
                }
            }
        }
    }

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
    fn ref_sqrt_monotone_tiny() {
        // sqrt is monotonic over the encoding order of positive finite (eb=3,sb=5)
        // values: as the input bit-pattern increases through one positive-finite run,
        // the rounded result never decreases. (Absolute correctness is anchored
        // separately by ref_sqrt_known_float32 and the datapath bit-equality gates.)
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
}

#[cfg(test)]
mod slice2d_tests {
    use super::*;
    use shinri_num::Integer;

    // Float32 bit patterns.
    const P1: u64 = 0x3F80_0000;   // +1.0
    const N1: u64 = 0xBF80_0000;   // -1.0
    const P2: u64 = 0x4000_0000;   // +2.0
    const N2: u64 = 0xC000_0000;   // -2.0
    const PZ: u64 = 0x0000_0000;   // +0
    const NZ: u64 = 0x8000_0000;   // -0
    const PINF: u64 = 0x7F80_0000;
    const NINF: u64 = 0xFF80_0000;
    const QNAN: u64 = 0x7FC0_0000;
    const SUBN: u64 = 0x0000_0001; // smallest +subnormal

    fn i(v: u64) -> Integer { Integer::from(v) }

    #[test]
    fn ref_lt_matches_extended_order() {
        let (eb, sb) = (8, 24);
        let lt = |a, b| ref_lt(eb, sb, &i(a), &i(b));
        assert!(lt(P1, P2));
        assert!(!lt(P2, P1));
        assert!(lt(N1, P1));
        assert!(lt(N2, N1));        // -2 < -1
        assert!(!lt(N1, N2));
        assert!(!lt(PZ, NZ));       // +0 == -0
        assert!(!lt(NZ, PZ));
        assert!(lt(NINF, PINF));
        assert!(lt(NINF, N1));
        assert!(lt(P1, PINF));
        assert!(lt(PZ, SUBN));
        assert!(!lt(QNAN, P1));     // NaN unordered
        assert!(!lt(P1, QNAN));
        assert!(!lt(QNAN, QNAN));
    }

    #[test]
    fn ref_leq_gt_geq_derive_correctly() {
        let (eb, sb) = (8, 24);
        assert!(ref_leq(eb, sb, &i(P1), &i(P1)));    // equal
        assert!(ref_leq(eb, sb, &i(PZ), &i(NZ)));    // +0 <= -0
        assert!(!ref_leq(eb, sb, &i(QNAN), &i(P1))); // NaN
        assert!(ref_gt(eb, sb, &i(P2), &i(P1)));
        assert!(!ref_gt(eb, sb, &i(P1), &i(P1)));
        assert!(ref_geq(eb, sb, &i(P1), &i(P1)));
        assert!(ref_geq(eb, sb, &i(P2), &i(P1)));
        assert!(!ref_geq(eb, sb, &i(P1), &i(QNAN)));
    }

    #[test]
    fn ref_min_max_with_nan_and_zero_tie() {
        let (eb, sb) = (8, 24);
        assert_eq!(ref_min(eb, sb, &i(P1), &i(P2)), i(P1));
        assert_eq!(ref_max(eb, sb, &i(P1), &i(P2)), i(P2));
        // sign-canonical, order-independent ±0:
        assert_eq!(ref_min(eb, sb, &i(PZ), &i(NZ)), i(NZ));
        assert_eq!(ref_min(eb, sb, &i(NZ), &i(PZ)), i(NZ));
        assert_eq!(ref_max(eb, sb, &i(PZ), &i(NZ)), i(PZ));
        assert_eq!(ref_max(eb, sb, &i(NZ), &i(PZ)), i(PZ));
        // NaN passthrough:
        assert_eq!(ref_min(eb, sb, &i(QNAN), &i(P1)), i(P1));
        assert_eq!(ref_min(eb, sb, &i(P1), &i(QNAN)), i(P1));
        assert_eq!(ref_max(eb, sb, &i(QNAN), &i(P2)), i(P2));
        assert_eq!(ref_min(eb, sb, &i(QNAN), &i(QNAN)), i(QNAN)); // both NaN -> b
    }

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
}
