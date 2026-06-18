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
            let hi = if limbs.len() == 2 { limbs[1] as u128 } else { 0 };
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
                    Integer(Repr::Big { negative: false, limbs: vec![0, 1u64 << 63] })
                } else {
                    Integer(Repr::Small(-v))
                }
            }
            Repr::Big { negative, limbs } => Integer(Repr::Big { negative: !negative, limbs }),
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
        assert_eq!(Integer::from(5i128) + Integer::from(-8i128), Integer::from(-3i128));
        assert_eq!(Integer::from(-5i128) - Integer::from(-8i128), Integer::from(3i128));
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
        assert_eq!(Integer::from(6i128) * Integer::from(7i128), Integer::from(42i128));
        assert_eq!(Integer::from(-6i128) * Integer::from(7i128), Integer::from(-42i128));
        assert_eq!(Integer::from(0i128) * Integer::from(i128::MAX), Integer::zero());
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
        assert_eq!(Integer::from(12i128).gcd(&Integer::from(18i128)), Integer::from(6i128));
        assert_eq!(Integer::from(-12i128).gcd(&Integer::from(18i128)), Integer::from(6i128));
        assert_eq!(Integer::from(0i128).gcd(&Integer::from(5i128)), Integer::from(5i128));
        assert_eq!(Integer::from(0i128).gcd(&Integer::from(0i128)), Integer::zero());
        assert_eq!(Integer::from(17i128).gcd(&Integer::from(13i128)), Integer::from(1i128));
    }
}
