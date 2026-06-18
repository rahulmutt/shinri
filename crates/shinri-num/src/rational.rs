use crate::Integer;
use core::cmp::Ordering;
use core::ops::{Add, Div, Mul, Neg, Sub};

/// An exact rational. Invariant: `denom > 0`, `gcd(|numer|, denom) == 1`,
/// and zero is exactly `0/1`.
#[derive(Clone, Debug)]
pub struct Rational {
    numer: Integer,
    denom: Integer,
}

impl Rational {
    pub fn new(numer: Integer, denom: Integer) -> Rational {
        assert!(!denom.is_zero(), "zero denominator");
        let mut n = numer;
        let mut d = denom;
        if d.is_negative() {
            n = -n;
            d = -d;
        }
        let g = n.gcd(&d);
        // g >= 1 whenever n != 0 (and gcd(0,d)=d, so 0/d -> 0/1).
        if g != Integer::one() {
            n = n.div_rem(&g).0;
            d = d.div_rem(&g).0;
        }
        Rational { numer: n, denom: d }
    }

    pub fn from_int(n: Integer) -> Rational {
        Rational { numer: n, denom: Integer::one() }
    }
    pub fn zero() -> Rational {
        Rational { numer: Integer::zero(), denom: Integer::one() }
    }
    pub fn one() -> Rational {
        Rational { numer: Integer::one(), denom: Integer::one() }
    }

    pub fn numer(&self) -> &Integer {
        &self.numer
    }
    pub fn denom(&self) -> &Integer {
        &self.denom
    }
    pub fn is_zero(&self) -> bool {
        self.numer.is_zero()
    }
    pub fn is_negative(&self) -> bool {
        self.numer.is_negative()
    }
    pub fn signum(&self) -> i32 {
        self.numer.signum()
    }

    pub fn recip(&self) -> Rational {
        assert!(!self.is_zero(), "reciprocal of zero");
        Rational::new(self.denom.clone(), self.numer.clone())
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Self) -> bool {
        // Both canonical, so field-wise equality suffices.
        self.numer == other.numer && self.denom == other.denom
    }
}
impl Eq for Rational {}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Rational {
    fn cmp(&self, other: &Self) -> Ordering {
        // a/b vs c/d with b,d > 0  <=>  a*d vs c*b
        let lhs = self.numer.clone() * other.denom.clone();
        let rhs = other.numer.clone() * self.denom.clone();
        lhs.cmp(&rhs)
    }
}

impl Add for Rational {
    type Output = Rational;
    fn add(self, o: Rational) -> Rational {
        let numer = self.numer.clone() * o.denom.clone() + o.numer.clone() * self.denom.clone();
        let denom = self.denom * o.denom;
        Rational::new(numer, denom)
    }
}
impl Sub for Rational {
    type Output = Rational;
    fn sub(self, o: Rational) -> Rational {
        self + (-o)
    }
}
impl Mul for Rational {
    type Output = Rational;
    fn mul(self, o: Rational) -> Rational {
        Rational::new(self.numer * o.numer, self.denom * o.denom)
    }
}
impl Div for Rational {
    type Output = Rational;
    fn div(self, o: Rational) -> Rational {
        assert!(!o.is_zero(), "division by zero");
        Rational::new(self.numer * o.denom, self.denom * o.numer)
    }
}
impl Neg for Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        Rational { numer: -self.numer, denom: self.denom }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Integer;

    fn r(n: i128, d: i128) -> Rational {
        Rational::new(Integer::from(n), Integer::from(d))
    }

    #[test]
    fn canonicalization() {
        // 2/4 -> 1/2
        assert_eq!(r(2, 4), r(1, 2));
        // sign moves to numerator; denominator positive
        let neg = r(1, -2);
        assert!(neg.is_negative());
        assert_eq!(*neg.denom(), Integer::from(2i128));
        assert_eq!(*neg.numer(), Integer::from(-1i128));
        // zero is 0/1
        assert!(r(0, 5).is_zero());
        assert_eq!(*r(0, 5).denom(), Integer::from(1i128));
    }

    #[test]
    fn arithmetic() {
        assert_eq!(r(1, 2) + r(1, 3), r(5, 6));
        assert_eq!(r(1, 2) - r(1, 3), r(1, 6));
        assert_eq!(r(2, 3) * r(3, 4), r(1, 2));
        assert_eq!(r(2, 3) / r(4, 9), r(3, 2));
        assert_eq!(-r(2, 3), r(-2, 3));
    }

    #[test]
    fn ordering() {
        assert!(r(1, 3) < r(1, 2));
        assert!(r(-1, 2) < r(0, 1));
        assert!(r(3, 2) > r(1, 1));
    }

    #[test]
    #[should_panic(expected = "zero denominator")]
    fn zero_denominator_panics() {
        let _ = Rational::new(Integer::from(1i128), Integer::zero());
    }
}
