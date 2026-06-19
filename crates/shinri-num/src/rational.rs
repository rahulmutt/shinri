use crate::integer::Integer;
use core::cmp::Ordering;
use core::ops::{Add, Div, Mul, Neg, Sub};

/// Exact rational with an unboxed i128 fast path (spec §7). `pub struct(Repr)`
/// with a private `Repr` keeps the variants encapsulated, mirroring `Integer`,
/// so external code cannot construct a non-canonical value.
#[derive(Clone, Debug)]
pub struct Rational(Repr);

#[derive(Clone, Debug)]
enum Repr {
    /// Canonical: `d > 0`, `gcd(|n|, d) == 1`, zero is `{ n: 0, d: 1 }`.
    Small { n: i128, d: i128 },
    /// Canonical and genuinely exceeds the i128 pair (`denom > 0`, reduced).
    Big { numer: Integer, denom: Integer },
}

fn igcd(a: i128, b: i128) -> i128 {
    let mut a = a.unsigned_abs();
    let mut b = b.unsigned_abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    // Safe: the only case where the gcd magnitude reaches 2^127 is gcd(MIN, MIN),
    // which `small_canon` pre-empts via the `d < 0` checked_neg path.
    a as i128
}

impl Rational {
    /// Canonicalize a raw i128 pair into `Small`, or `None` if it cannot stay in
    /// i128 (only the `i128::MIN` denominator-negation case). `d` must be non-zero.
    fn small_canon(mut n: i128, mut d: i128) -> Option<Rational> {
        debug_assert!(d != 0);
        if n == 0 {
            return Some(Rational(Repr::Small { n: 0, d: 1 }));
        }
        if d < 0 {
            n = n.checked_neg()?;
            d = d.checked_neg()?;
        }
        let g = igcd(n, d);
        Some(Rational(Repr::Small { n: n / g, d: d / g }))
    }

    /// Build from `Integer` components: sign-fix, reduce, then DEMOTE to `Small`
    /// when both components fit i128 (keeping the hot path unboxed after a
    /// temporary excursion to bignum), else keep `Big`. `denom` must be non-zero.
    fn from_components(numer: Integer, denom: Integer) -> Rational {
        debug_assert!(!denom.is_zero(), "Rational with zero denominator");
        let (mut numer, mut denom) = if denom.is_negative() {
            (-numer, -denom)
        } else {
            (numer, denom)
        };
        let g = numer.gcd(&denom);
        if !g.is_zero() && g != Integer::one() {
            let (qn, _) = numer.div_rem(&g);
            let (qd, _) = denom.div_rem(&g);
            numer = qn;
            denom = qd;
        }
        match (numer.to_i128(), denom.to_i128()) {
            (Some(n), Some(d)) => Rational(Repr::Small { n, d }),
            _ => Rational(Repr::Big { numer, denom }),
        }
    }

    pub fn new(numer: Integer, denom: Integer) -> Rational {
        assert!(!denom.is_zero(), "Rational denominator must be non-zero");
        if let (Some(n), Some(d)) = (numer.to_i128(), denom.to_i128()) {
            if let Some(r) = Rational::small_canon(n, d) {
                return r;
            }
        }
        Rational::from_components(numer, denom)
    }

    pub fn from_int(n: Integer) -> Rational {
        Rational::new(n, Integer::one())
    }

    pub fn zero() -> Rational {
        Rational(Repr::Small { n: 0, d: 1 })
    }

    pub fn one() -> Rational {
        Rational(Repr::Small { n: 1, d: 1 })
    }

    /// The numerator, by value (the `Small` variant has no `Integer` to borrow).
    pub fn numer(&self) -> Integer {
        match &self.0 {
            Repr::Small { n, .. } => Integer::from(*n),
            Repr::Big { numer, .. } => numer.clone(),
        }
    }

    /// The denominator, by value.
    pub fn denom(&self) -> Integer {
        match &self.0 {
            Repr::Small { d, .. } => Integer::from(*d),
            Repr::Big { denom, .. } => denom.clone(),
        }
    }

    pub fn is_zero(&self) -> bool {
        match &self.0 {
            Repr::Small { n, .. } => *n == 0,
            Repr::Big { numer, .. } => numer.is_zero(),
        }
    }

    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small { n, .. } => *n < 0,
            Repr::Big { numer, .. } => numer.is_negative(),
        }
    }

    pub fn signum(&self) -> i32 {
        match &self.0 {
            Repr::Small { n, .. } => (*n > 0) as i32 - (*n < 0) as i32,
            Repr::Big { numer, .. } => numer.signum(),
        }
    }

    pub fn recip(&self) -> Rational {
        assert!(!self.is_zero(), "recip of zero");
        match &self.0 {
            Repr::Small { n, d } => Rational::small_canon(*d, *n)
                .unwrap_or_else(|| Rational::from_components(Integer::from(*d), Integer::from(*n))),
            Repr::Big { numer, denom } => Rational::from_components(denom.clone(), numer.clone()),
        }
    }

    /// (numerator, denominator) as `Integer`s — used by the bignum fallback paths.
    fn components(&self) -> (Integer, Integer) {
        (self.numer(), self.denom())
    }
}

macro_rules! rat_binop {
    ($trait:ident, $method:ident, $small:expr, $big:expr) => {
        impl $trait for Rational {
            type Output = Rational;
            fn $method(self, rhs: Rational) -> Rational {
                if let (Repr::Small { n: an, d: ad }, Repr::Small { n: bn, d: bd }) =
                    (&self.0, &rhs.0)
                {
                    if let Some(res) = ($small)(*an, *ad, *bn, *bd) {
                        return res;
                    }
                }
                let (an, ad) = self.components();
                let (bn, bd) = rhs.components();
                let (num, den) = ($big)(an, ad, bn, bd);
                Rational::from_components(num, den)
            }
        }
    };
}

rat_binop!(
    Add,
    add,
    |an: i128, ad: i128, bn: i128, bd: i128| -> Option<Rational> {
        let ae = an.checked_mul(bd)?;
        let bdp = bn.checked_mul(ad)?;
        let num = ae.checked_add(bdp)?;
        let den = ad.checked_mul(bd)?;
        Rational::small_canon(num, den)
    },
    |an: Integer, ad: Integer, bn: Integer, bd: Integer| {
        (an * bd.clone() + bn * ad.clone(), ad * bd)
    }
);

rat_binop!(
    Sub,
    sub,
    |an: i128, ad: i128, bn: i128, bd: i128| -> Option<Rational> {
        let ae = an.checked_mul(bd)?;
        let bdp = bn.checked_mul(ad)?;
        let num = ae.checked_sub(bdp)?;
        let den = ad.checked_mul(bd)?;
        Rational::small_canon(num, den)
    },
    |an: Integer, ad: Integer, bn: Integer, bd: Integer| {
        (an * bd.clone() - bn * ad.clone(), ad * bd)
    }
);

rat_binop!(
    Mul,
    mul,
    |an: i128, ad: i128, bn: i128, bd: i128| -> Option<Rational> {
        let num = an.checked_mul(bn)?;
        let den = ad.checked_mul(bd)?;
        Rational::small_canon(num, den)
    },
    |an: Integer, ad: Integer, bn: Integer, bd: Integer| { (an * bn, ad * bd) }
);

rat_binop!(
    Div,
    div,
    |an: i128, ad: i128, bn: i128, bd: i128| -> Option<Rational> {
        assert!(bn != 0, "division by zero rational");
        let num = an.checked_mul(bd)?;
        let den = ad.checked_mul(bn)?;
        if den == 0 {
            return None;
        }
        Rational::small_canon(num, den)
    },
    |an: Integer, ad: Integer, bn: Integer, bd: Integer| {
        assert!(!bn.is_zero(), "division by zero rational");
        (an * bd, ad * bn)
    }
);

impl Neg for Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        match self.0 {
            Repr::Small { n, d } => match n.checked_neg() {
                Some(nn) => Rational(Repr::Small { n: nn, d }),
                None => Rational::from_components(-Integer::from(n), Integer::from(d)),
            },
            Repr::Big { numer, denom } => Rational::from_components(-numer, denom),
        }
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Rational) -> bool {
        match (&self.0, &other.0) {
            (Repr::Small { n: an, d: ad }, Repr::Small { n: bn, d: bd }) => an == bn && ad == bd,
            (
                Repr::Big {
                    numer: an,
                    denom: ad,
                },
                Repr::Big {
                    numer: bn,
                    denom: bd,
                },
            ) => an == bn && ad == bd,
            // Canonical: a value is Small iff it fits, so Small and Big are never equal.
            _ => false,
        }
    }
}

impl Eq for Rational {}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        if let (Repr::Small { n: an, d: ad }, Repr::Small { n: bn, d: bd }) = (&self.0, &other.0) {
            if let (Some(l), Some(r)) = (an.checked_mul(*bd), bn.checked_mul(*ad)) {
                return l.cmp(&r);
            }
        }
        // Cross-multiply over Integer (denominators are positive, so sign is preserved).
        let (an, ad) = self.components();
        let (bn, bd) = other.components();
        (an * bd).cmp(&(bn * ad))
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
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
        assert_eq!(neg.denom(), Integer::from(2i128));
        assert_eq!(neg.numer(), Integer::from(-1i128));
        // zero is 0/1
        assert!(r(0, 5).is_zero());
        assert_eq!(r(0, 5).denom(), Integer::from(1i128));
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
    #[should_panic(expected = "Rational denominator must be non-zero")]
    fn zero_denominator_panics() {
        let _ = Rational::new(Integer::from(1i128), Integer::zero());
    }

    #[test]
    #[should_panic(expected = "division by zero rational")]
    fn div_by_zero_rational_panics() {
        let _ = Rational::one() / Rational::zero();
    }

    #[test]
    #[should_panic(expected = "recip of zero")]
    fn recip_of_zero_panics() {
        let _ = Rational::zero().recip();
    }

    #[test]
    fn small_tag_and_reduction() {
        // 2/4 reduces to 1/2 and stays Small
        let r = Rational::new(Integer::from(2i128), Integer::from(4i128));
        assert!(matches!(r, Rational(Repr::Small { n: 1, d: 2 })));
        // negative denominator normalizes onto the numerator
        let r2 = Rational::new(Integer::from(1i128), Integer::from(-2i128));
        assert!(matches!(r2, Rational(Repr::Small { n: -1, d: 2 })));
    }

    #[test]
    fn overflow_promotes_to_big() {
        let r = Rational::from_int(Integer::from(i128::MAX) * Integer::from(2i128));
        assert!(matches!(r, Rational(Repr::Big { .. })));
    }

    #[test]
    fn demotes_back_to_small_when_it_fits() {
        // Big value 2*i128::MAX, divided by 2 -> i128::MAX, which fits -> Small
        let big = Rational::from_int(Integer::from(i128::MAX) * Integer::from(2i128));
        assert!(matches!(big, Rational(Repr::Big { .. })));
        let halved = big / Rational::from_int(Integer::from(2i128));
        assert!(matches!(halved, Rational(Repr::Small { .. })));
        assert_eq!(halved, Rational::from_int(Integer::from(i128::MAX)));
    }

    #[test]
    fn fast_path_arithmetic_and_ordering() {
        let half = Rational::new(Integer::from(1i128), Integer::from(2i128));
        let third = Rational::new(Integer::from(1i128), Integer::from(3i128));
        assert_eq!(
            half.clone() + third.clone(),
            Rational::new(Integer::from(5i128), Integer::from(6i128))
        );
        assert!((half.clone() - half.clone()).is_zero());
        assert_eq!(
            half.clone() * third.clone(),
            Rational::new(Integer::from(1i128), Integer::from(6i128))
        );
        assert_eq!(
            half.clone() / third.clone(),
            Rational::new(Integer::from(3i128), Integer::from(2i128))
        );
        assert!(third < half);
        assert_eq!(half.recip(), Rational::from_int(Integer::from(2i128)));
    }
}
