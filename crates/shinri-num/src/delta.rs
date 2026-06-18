use crate::Rational;
use core::cmp::Ordering;
use core::ops::{Add, Neg, Sub};

/// A value `c + k·δ` where `δ` is a positive infinitesimal, used to encode
/// strict inequalities in the Dutertre–de Moura simplex (spec §6.5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeltaRational {
    c: Rational,
    k: Rational,
}

impl DeltaRational {
    pub fn new(c: Rational, k: Rational) -> Self {
        DeltaRational { c, k }
    }
    pub fn from_rational(c: Rational) -> Self {
        DeltaRational { c, k: Rational::zero() }
    }
    pub fn c(&self) -> &Rational {
        &self.c
    }
    pub fn k(&self) -> &Rational {
        &self.k
    }
    pub fn scale(&self, factor: &Rational) -> DeltaRational {
        DeltaRational {
            c: self.c.clone() * factor.clone(),
            k: self.k.clone() * factor.clone(),
        }
    }
}

impl PartialOrd for DeltaRational {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for DeltaRational {
    fn cmp(&self, other: &Self) -> Ordering {
        self.c.cmp(&other.c).then_with(|| self.k.cmp(&other.k))
    }
}

impl Add for DeltaRational {
    type Output = DeltaRational;
    fn add(self, o: DeltaRational) -> DeltaRational {
        DeltaRational { c: self.c + o.c, k: self.k + o.k }
    }
}
impl Sub for DeltaRational {
    type Output = DeltaRational;
    fn sub(self, o: DeltaRational) -> DeltaRational {
        DeltaRational { c: self.c - o.c, k: self.k - o.k }
    }
}
impl Neg for DeltaRational {
    type Output = DeltaRational;
    fn neg(self) -> DeltaRational {
        DeltaRational { c: -self.c, k: -self.k }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Integer, Rational};

    fn rat(n: i128, d: i128) -> Rational {
        Rational::new(Integer::from(n), Integer::from(d))
    }

    #[test]
    fn lexicographic_ordering() {
        // 1 + 0d  <  1 + 1d   (same c, larger k)
        let a = DeltaRational::new(rat(1, 1), rat(0, 1));
        let b = DeltaRational::new(rat(1, 1), rat(1, 1));
        assert!(a < b);
        // 1 + 5d  <  2 + 0d    (c dominates)
        let c = DeltaRational::new(rat(1, 1), rat(5, 1));
        let d = DeltaRational::new(rat(2, 1), rat(0, 1));
        assert!(c < d);
    }

    #[test]
    fn arithmetic_componentwise() {
        let a = DeltaRational::new(rat(1, 2), rat(1, 1));
        let b = DeltaRational::new(rat(1, 3), rat(2, 1));
        let s = a.clone() + b.clone();
        assert_eq!(*s.c(), rat(5, 6));
        assert_eq!(*s.k(), rat(3, 1));
        let scaled = a.scale(&rat(2, 1));
        assert_eq!(*scaled.c(), rat(1, 1));
        assert_eq!(*scaled.k(), rat(2, 1));
        let n = -b;
        assert_eq!(*n.c(), rat(-1, 3));
        assert_eq!(*n.k(), rat(-2, 1));
    }
}
