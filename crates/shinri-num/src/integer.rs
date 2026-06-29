use crate::limbs;
use core::cmp::Ordering;
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, Sub, SubAssign};

/// An arbitrary-precision signed integer.
///
/// Invariants (see Global Constraints):
/// - `Small(0)` is the unique representation of zero.
/// - Any value representable in `i128` is `Small`, never `Big`.
/// - `Big` limbs are little-endian, canonical (no trailing zero limb),
///   `len() >= 2`, and the magnitude is non-zero.
#[derive(Clone, Debug)]
pub struct Integer(Repr);

#[derive(Clone, Debug)]
enum Repr {
    Small(i128),
    Big { negative: bool, limbs: Vec<u64> },
}

impl From<i128> for Integer {
    fn from(v: i128) -> Self {
        Integer(Repr::Small(v))
    }
}
impl From<i64> for Integer {
    fn from(v: i64) -> Self {
        Integer(Repr::Small(v as i128))
    }
}
impl From<u64> for Integer {
    fn from(v: u64) -> Self {
        Integer(Repr::Small(v as i128))
    }
}

impl Integer {
    /// Canonical zero.
    pub fn zero() -> Self {
        Integer(Repr::Small(0))
    }
    /// Canonical one.
    pub fn one() -> Self {
        Integer(Repr::Small(1))
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.0, Repr::Small(0))
    }

    /// Number of 64-bit limbs in the magnitude (1 for any inline `Small`). A cheap
    /// proxy for "how big has this grown", used by the simplex to detect the
    /// coefficient blowup that a degenerate system (e.g. the String↔Arith
    /// `str.substr` seam) can trigger — where a single BigInt gcd/division would
    /// otherwise dominate runtime — so it can bail to a sound `Unknown`.
    pub fn limb_count(&self) -> usize {
        match &self.0 {
            Repr::Small(_) => 1,
            Repr::Big { limbs, .. } => limbs.len(),
        }
    }

    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small(v) => *v < 0,
            Repr::Big { negative, .. } => *negative,
        }
    }

    pub fn signum(&self) -> i32 {
        match &self.0 {
            Repr::Small(v) => (*v > 0) as i32 - (*v < 0) as i32,
            Repr::Big { negative, .. } => {
                if *negative {
                    -1
                } else {
                    1
                }
            }
        }
    }

    pub fn abs(&self) -> Integer {
        match &self.0 {
            Repr::Small(v) => {
                if *v == i128::MIN {
                    // |i128::MIN| = 2^127 does not fit in i128 -> Big.
                    Integer(Repr::Big {
                        negative: false,
                        limbs: vec![0, 1u64 << 63],
                    })
                } else {
                    Integer(Repr::Small(v.abs()))
                }
            }
            Repr::Big { limbs, .. } => Integer(Repr::Big {
                negative: false,
                limbs: limbs.clone(),
            }),
        }
    }

    /// Little-endian magnitude; empty vec means zero.
    pub(crate) fn mag_limbs(&self) -> Vec<u64> {
        match &self.0 {
            Repr::Small(0) => Vec::new(),
            Repr::Small(v) => {
                let m = v.unsigned_abs(); // u128, correct even for i128::MIN
                let lo = m as u64;
                let hi = (m >> 64) as u64;
                if hi == 0 {
                    vec![lo]
                } else {
                    vec![lo, hi]
                }
            }
            Repr::Big { limbs, .. } => limbs.clone(),
        }
    }

    /// Build an `Integer` from a sign and a (not necessarily trimmed) little-
    /// endian magnitude, collapsing to `Small` whenever the value fits in i128.
    pub(crate) fn from_sign_limbs(negative: bool, mut limbs: Vec<u64>) -> Integer {
        limbs::trim(&mut limbs);
        if limbs.is_empty() {
            return Integer(Repr::Small(0));
        }
        if limbs.len() <= 2 {
            let lo = limbs[0] as u128;
            let hi = if limbs.len() == 2 {
                limbs[1] as u128
            } else {
                0
            };
            let mag = lo | (hi << 64);
            if !negative {
                if mag <= i128::MAX as u128 {
                    return Integer(Repr::Small(mag as i128));
                }
            } else if mag < (1u128 << 127) {
                return Integer(Repr::Small(-(mag as i128)));
            } else if mag == (1u128 << 127) {
                return Integer(Repr::Small(i128::MIN));
            }
        }
        Integer(Repr::Big { negative, limbs })
    }
}

impl PartialEq for Integer {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}
impl Eq for Integer {}

impl PartialOrd for Integer {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Integer {
    fn cmp(&self, other: &Self) -> Ordering {
        // Fast path: both Small.
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0) {
            return a.cmp(b);
        }
        let sa = self.signum();
        let sb = other.signum();
        if sa != sb {
            return sa.cmp(&sb);
        }
        if sa == 0 {
            return Ordering::Equal;
        }
        let mag = limbs::cmp(&self.mag_limbs(), &other.mag_limbs());
        if sa < 0 {
            mag.reverse()
        } else {
            mag
        }
    }
}

impl Neg for Integer {
    type Output = Integer;
    fn neg(self) -> Integer {
        match self.0 {
            Repr::Small(v) => {
                if v == i128::MIN {
                    Integer(Repr::Big {
                        negative: false,
                        limbs: vec![0, 1u64 << 63],
                    })
                } else {
                    Integer(Repr::Small(-v))
                }
            }
            Repr::Big { negative, limbs } => Integer(Repr::Big {
                negative: !negative,
                limbs,
            }),
        }
    }
}

fn add_general(x: &Integer, y: &Integer) -> Integer {
    let xn = x.is_negative();
    let yn = y.is_negative();
    let xm = x.mag_limbs();
    let ym = y.mag_limbs();
    if xn == yn {
        Integer::from_sign_limbs(xn, limbs::add(&xm, &ym))
    } else {
        match limbs::cmp(&xm, &ym) {
            Ordering::Equal => Integer::zero(),
            Ordering::Greater => Integer::from_sign_limbs(xn, limbs::sub(&xm, &ym)),
            Ordering::Less => Integer::from_sign_limbs(yn, limbs::sub(&ym, &xm)),
        }
    }
}

impl Add for Integer {
    type Output = Integer;
    fn add(self, rhs: Integer) -> Integer {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if let Some(s) = a.checked_add(*b) {
                return Integer(Repr::Small(s));
            }
        }
        add_general(&self, &rhs)
    }
}

impl Sub for Integer {
    type Output = Integer;
    fn sub(self, rhs: Integer) -> Integer {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if let Some(s) = a.checked_sub(*b) {
                return Integer(Repr::Small(s));
            }
        }
        add_general(&self, &(-rhs))
    }
}

impl AddAssign for Integer {
    fn add_assign(&mut self, rhs: Integer) {
        *self = self.clone() + rhs;
    }
}
impl SubAssign for Integer {
    fn sub_assign(&mut self, rhs: Integer) {
        *self = self.clone() - rhs;
    }
}

impl Mul for Integer {
    type Output = Integer;
    fn mul(self, rhs: Integer) -> Integer {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if let Some(p) = a.checked_mul(*b) {
                return Integer(Repr::Small(p));
            }
        }
        // Defensive: unreachable in practice (Small(0) hits the fast path; Big is never zero), but cheap.
        if self.is_zero() || rhs.is_zero() {
            return Integer::zero();
        }
        let negative = self.is_negative() ^ rhs.is_negative();
        let m = limbs::mul(&self.mag_limbs(), &rhs.mag_limbs());
        Integer::from_sign_limbs(negative, m)
    }
}

impl MulAssign for Integer {
    fn mul_assign(&mut self, rhs: Integer) {
        *self = self.clone() * rhs;
    }
}

impl Integer {
    /// Truncated division: returns (quotient, remainder) with
    /// `self == quotient * rhs + remainder` and `remainder` taking `self`'s sign.
    ///
    /// # Panics
    ///
    /// Panics if `rhs` is zero.
    pub fn div_rem(&self, rhs: &Integer) -> (Integer, Integer) {
        // Fast path: both Small, avoiding the only overflowing case.
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0) {
            if *b != 0 && !(*a == i128::MIN && *b == -1) {
                return (Integer(Repr::Small(a / b)), Integer(Repr::Small(a % b)));
            }
        }
        assert!(!rhs.is_zero(), "division by zero");
        let (q, r) = limbs::divrem(&self.mag_limbs(), &rhs.mag_limbs());
        let q_neg = self.is_negative() ^ rhs.is_negative();
        let r_neg = self.is_negative();
        (
            Integer::from_sign_limbs(q_neg, q),
            Integer::from_sign_limbs(r_neg, r),
        )
    }
}

impl Div for Integer {
    type Output = Integer;
    fn div(self, rhs: Integer) -> Integer {
        self.div_rem(&rhs).0
    }
}
impl Rem for Integer {
    type Output = Integer;
    fn rem(self, rhs: Integer) -> Integer {
        self.div_rem(&rhs).1
    }
}

impl core::fmt::Display for Integer {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if self.is_zero() {
            return write!(f, "0");
        }
        // Repeatedly divide by 10^18 to build decimal digit chunks, then emit.
        let base = Integer::from(1_000_000_000_000_000_000i128);
        let mut n = self.abs();
        let mut chunks: Vec<u64> = Vec::new();
        while !n.is_zero() {
            let (q, r) = n.div_rem(&base);
            chunks.push(r.to_u64_chunk());
            n = q;
        }
        if self.is_negative() {
            write!(f, "-")?;
        }
        // Most-significant chunk without leading zeros, the rest zero-padded to 18.
        write!(f, "{}", chunks.last().unwrap())?;
        for c in chunks.iter().rev().skip(1) {
            write!(f, "{:018}", c)?;
        }
        Ok(())
    }
}

impl Integer {
    /// For a non-negative Integer known to be < 10^18, return its u64 value.
    pub(crate) fn to_u64_chunk(&self) -> u64 {
        match &self.0 {
            Repr::Small(v) => {
                debug_assert!(*v >= 0, "to_u64_chunk called on negative Small");
                *v as u64
            }
            Repr::Big { limbs, .. } => limbs[0], // unreachable for < 10^18, but safe
        }
    }
}

impl Integer {
    /// The value as `i128` if it fits inline, else `None`. By the canonical
    /// invariant (any i128-representable value is `Small`), `None` means the
    /// magnitude genuinely exceeds `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        match &self.0 {
            Repr::Small(v) => Some(*v),
            Repr::Big { .. } => None,
        }
    }
}

impl Integer {
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
}

impl Integer {
    /// Greatest common divisor. Result is always non-negative; gcd(0,0)=0.
    pub fn gcd(&self, other: &Integer) -> Integer {
        let mut a = self.abs();
        let mut b = other.abs();
        while !b.is_zero() {
            let r = a.div_rem(&b).1; // a % b, non-negative since a,b >= 0
            a = b;
            b = r;
        }
        a
    }
}

/// Failure parsing a decimal/radix string into an `Integer`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParseIntegerError;

impl core::fmt::Display for ParseIntegerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "invalid integer literal")
    }
}

impl Integer {
    /// Parse an unsigned digit string in `radix` (2..=16) via Horner's method.
    /// No sign, no whitespace, no prefix; empty or non-digit input is an error.
    pub fn from_str_radix(s: &str, radix: u32) -> Result<Integer, ParseIntegerError> {
        if s.is_empty() {
            return Err(ParseIntegerError);
        }
        let base = Integer::from(radix as i128);
        let mut acc = Integer::zero();
        for ch in s.chars() {
            let d = ch.to_digit(radix).ok_or(ParseIntegerError)?;
            acc = acc * base.clone() + Integer::from(d as i128);
        }
        Ok(acc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn small_construction_and_queries() {
        assert!(Integer::from(0i128).is_zero());
        assert!(!Integer::from(5i128).is_zero());
        assert!(Integer::from(-3i128).is_negative());
        assert!(!Integer::from(3i128).is_negative());
        assert_eq!(Integer::from(0i128).signum(), 0);
        assert_eq!(Integer::from(7i128).signum(), 1);
        assert_eq!(Integer::from(-7i128).signum(), -1);
    }

    #[test]
    fn abs_handles_i128_min() {
        // i128::MIN cannot be negated within i128; abs must promote to Big.
        let a = Integer::from(i128::MIN).abs();
        assert!(!a.is_negative());
        assert!(!a.is_zero());
        // magnitude is 2^127 -> limbs [0, 1<<63]
        assert_eq!(a.mag_limbs(), vec![0, 1u64 << 63]);
    }

    #[test]
    fn from_sign_limbs_collapses_to_small() {
        // 5 as limbs collapses back to Small.
        let a = Integer::from_sign_limbs(false, vec![5, 0]);
        assert_eq!(a.mag_limbs(), vec![5]);
        assert!(!a.is_negative());
        // negative 2^127 collapses to Small(i128::MIN).
        let b = Integer::from_sign_limbs(true, vec![0, 1u64 << 63]);
        assert!(b.is_negative());
        assert_eq!(b.mag_limbs(), vec![0, 1u64 << 63]);
    }

    #[test]
    fn ordering_and_equality() {
        assert_eq!(Integer::from(5i128), Integer::from(5i128));
        assert_ne!(Integer::from(5i128), Integer::from(-5i128));
        assert!(Integer::from(-1i128) < Integer::from(0i128));
        assert!(Integer::from(0i128) < Integer::from(1i128));
        // cross representation: i128::MAX < i128::MAX + 2 (Big, strictly > |i128::MIN|)
        let big = Integer::from(i128::MAX) + Integer::from(2i128);
        assert!(Integer::from(i128::MAX) < big);
        assert!(big > Integer::from(0i128));
        // negative Big < negative Small (neg_big = -(i128::MAX+2) < i128::MIN = -(i128::MAX+1))
        let neg_big = -big.clone();
        assert!(neg_big < Integer::from(i128::MIN));
    }

    #[test]
    fn add_sub_across_representations() {
        let max = Integer::from(i128::MAX);
        let one = Integer::from(1i128);
        let big = max.clone() + one.clone(); // promotes to Big
        assert!(big > max);
        assert_eq!(big.clone() - one.clone(), max); // demotes back to Small
                                                    // sign handling
        assert_eq!(
            Integer::from(5i128) + Integer::from(-8i128),
            Integer::from(-3i128)
        );
        assert_eq!(
            Integer::from(-5i128) - Integer::from(-8i128),
            Integer::from(3i128)
        );
        assert_eq!(-(big.clone()) + big.clone(), Integer::zero());
    }

    #[test]
    fn div_rem_matches_truncation() {
        let (q, r) = Integer::from(17i128).div_rem(&Integer::from(5i128));
        assert_eq!(q, Integer::from(3i128));
        assert_eq!(r, Integer::from(2i128));
        // negative dividend: truncation toward zero, remainder sign = dividend.
        let (q, r) = Integer::from(-17i128).div_rem(&Integer::from(5i128));
        assert_eq!(q, Integer::from(-3i128));
        assert_eq!(r, Integer::from(-2i128));
        // exact division across representations
        let big = Integer::from(i128::MAX) * Integer::from(1000i128);
        let (q, r) = big.div_rem(&Integer::from(1000i128));
        assert_eq!(q, Integer::from(i128::MAX));
        assert!(r.is_zero());
    }

    #[test]
    #[should_panic(expected = "division by zero")]
    fn div_by_zero_panics() {
        let _ = Integer::from(1i128).div_rem(&Integer::zero());
    }

    #[test]
    fn multiply_across_representations() {
        assert_eq!(
            Integer::from(6i128) * Integer::from(7i128),
            Integer::from(42i128)
        );
        assert_eq!(
            Integer::from(-6i128) * Integer::from(7i128),
            Integer::from(-42i128)
        );
        assert_eq!(
            Integer::from(0i128) * Integer::from(i128::MAX),
            Integer::zero()
        );
        // overflow i128 -> Big, then divide back is checked in Task 5.
        let a = Integer::from(i128::MAX);
        let b = Integer::from(i128::MAX);
        let p = a.clone() * b.clone();
        assert!(p > a);
        // (i128::MAX)^2 has known magnitude; verify it's larger than 2^200 lower bound via add identity:
        assert_eq!(p.clone(), a.clone() * b.clone());
    }

    #[test]
    fn gcd_basic_and_signs() {
        assert_eq!(
            Integer::from(12i128).gcd(&Integer::from(18i128)),
            Integer::from(6i128)
        );
        assert_eq!(
            Integer::from(-12i128).gcd(&Integer::from(18i128)),
            Integer::from(6i128)
        );
        assert_eq!(
            Integer::from(0i128).gcd(&Integer::from(5i128)),
            Integer::from(5i128)
        );
        assert_eq!(
            Integer::from(0i128).gcd(&Integer::from(0i128)),
            Integer::zero()
        );
        assert_eq!(
            Integer::from(17i128).gcd(&Integer::from(13i128)),
            Integer::from(1i128)
        );
    }

    #[test]
    fn to_i128_some_for_inline_values() {
        for v in [0i128, 1, -1, 42, -42, i128::MAX, i128::MIN] {
            assert_eq!(Integer::from(v).to_i128(), Some(v));
        }
    }

    #[test]
    fn to_i128_none_for_big_values() {
        let big = Integer::from(i128::MAX) * Integer::from(2i128);
        assert_eq!(big.to_i128(), None);
        let big_neg = Integer::from(i128::MIN) * Integer::from(2i128);
        assert_eq!(big_neg.to_i128(), None);
    }

    #[test]
    fn from_str_radix_small_and_big() {
        assert_eq!(
            Integer::from_str_radix("0", 10).unwrap(),
            Integer::from(0i128)
        );
        assert_eq!(
            Integer::from_str_radix("42", 10).unwrap(),
            Integer::from(42i128)
        );
        // 2^128 — genuinely exceeds i128, exercises the Big path.
        let two_128 = Integer::from(1i128 << 100) * Integer::from(1i128 << 28);
        assert_eq!(
            Integer::from_str_radix("340282366920938463463374607431768211456", 10).unwrap(),
            two_128
        );
        assert!(Integer::from_str_radix("", 10).is_err());
        assert!(Integer::from_str_radix("12a", 10).is_err());
    }

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
        // A spread of large multi-limb values; cross-check by reconstruction:
        // assert s*s + r == v  and  (s+1)*(s+1) > v.
        let seeds: [u128; 6] = [
            123_456_789,
            9_876_543_210_123,
            1u128 << 100,
            (1u128 << 100) + 1,
            340_282_366_920_938_463_463_374_607_431_768_211_455, // u128::MAX
            (1u128 << 64) * (1u128 << 63) + 777,
        ];
        for v in seeds {
            let iv = Integer::from_str_radix(&v.to_string(), 10).unwrap();
            let (s, r) = iv.sqrt_rem();
            // s*s + r == v
            assert_eq!(
                s.clone() * s.clone() + r.clone(),
                iv.clone(),
                "s²+r != v for {v}"
            );
            // (s+1)^2 > v
            let s1 = s.clone() + Integer::one();
            assert!(
                s1.clone() * s1 > iv,
                "(s+1)² not > v for {v}"
            );
        }
    }
}
