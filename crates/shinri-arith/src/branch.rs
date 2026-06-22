//! Branch-and-bound support: integer floor/ceil of a δ-value, used to build the
//! split clause `(x ≤ ⌊v⌋) ∨ (x ≥ ⌈v⌉)` for a fractional Int problem var.

use crate::bounds::BoundKind;
use shinri_num::{DeltaRational, Integer, Rational};

/// Integer floor/ceil of `c + k·δ`. δ is a positive infinitesimal, so when `c`
/// is itself an integer the result depends on the sign of `k`.
pub fn floor_ceil(value: &DeltaRational) -> (Integer, Integer) {
    let c = value.c();
    let k = value.k();
    let f = floor_rational(c);
    if &Rational::from_int(f.clone()) == c {
        // c is an exact integer; δ breaks the tie.
        if !k.is_zero() && !k.is_negative() {
            // c + (positive δ): floor = c, ceil = c+1
            (f.clone(), f + Integer::one())
        } else if k.is_negative() {
            // c − δ: floor = c−1, ceil = c
            (f.clone() - Integer::one(), f)
        } else {
            // exact integer (k == 0): floor == ceil == c
            (f.clone(), f)
        }
    } else {
        // c non-integer: |kδ| < distance to nearest integer, so δ is irrelevant.
        (f.clone(), f + Integer::one())
    }
}

/// Round a bound on an integer-valued variable to an integer `DeltaRational`
/// (k = 0), absorbing strictness:
///   Upper, non-strict  `x ≤ rhs`  ⟹ `x ≤ ⌊rhs⌋`
///   Upper, strict      `x < rhs`  ⟹ `x ≤ ⌈rhs⌉ − 1`
///   Lower, non-strict  `x ≥ rhs`  ⟹ `x ≥ ⌈rhs⌉`
///   Lower, strict      `x > rhs`  ⟹ `x ≥ ⌊rhs⌋ + 1`
pub(crate) fn round_int_bound(rhs: &Rational, kind: BoundKind, strict: bool) -> DeltaRational {
    let floor = floor_rational(rhs);
    let is_int = &Rational::from_int(floor.clone()) == rhs;
    let ceil = if is_int {
        floor.clone()
    } else {
        floor.clone() + Integer::one()
    };
    let bound = match (kind, strict) {
        (BoundKind::Upper, false) => floor,
        (BoundKind::Upper, true) => ceil - Integer::one(),
        (BoundKind::Lower, false) => ceil,
        (BoundKind::Lower, true) => floor + Integer::one(),
    };
    DeltaRational::from_rational(Rational::from_int(bound))
}

/// `⌊n/d⌋` for a Rational `n/d` (d > 0 in canonical form). Uses truncating
/// `div_rem` and corrects toward −∞ for negative non-exact values.
pub(crate) fn floor_rational(r: &Rational) -> Integer {
    let n = r.numer();
    let d = r.denom();
    let (q, rem) = n.div_rem(&d);
    if rem.is_zero() || !n.is_negative() {
        q
    } else {
        // n negative, non-exact: truncation rounded toward zero ⇒ subtract 1.
        q - Integer::one()
    }
}

#[cfg(test)]
mod tests {
    use super::{floor_ceil, round_int_bound};
    use crate::bounds::BoundKind;
    use shinri_num::{DeltaRational, Integer, Rational};

    fn r(n: i128, d: i128) -> Rational {
        Rational::new(Integer::from(n), Integer::from(d))
    }

    fn dri(n: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::from_int(Integer::from(n)))
    }

    #[test]
    fn round_int_bound_handles_all_cases() {
        // Upper, non-strict: x <= 5/2  ⟹  x <= 2
        assert_eq!(round_int_bound(&r(5, 2), BoundKind::Upper, false), dri(2));
        // Upper, strict: x < 5 (int rhs)  ⟹  x <= 4
        assert_eq!(
            round_int_bound(&Rational::from_int(5i128.into()), BoundKind::Upper, true),
            dri(4)
        );
        // Upper, strict: x < 5/2  ⟹  x <= 2  (ceil(5/2)-1 = 3-1 = 2)
        assert_eq!(round_int_bound(&r(5, 2), BoundKind::Upper, true), dri(2));
        // Lower, non-strict: x >= 5/2  ⟹  x >= 3
        assert_eq!(round_int_bound(&r(5, 2), BoundKind::Lower, false), dri(3));
        // Lower, strict: x > 5 (int rhs)  ⟹  x >= 6
        assert_eq!(
            round_int_bound(&Rational::from_int(5i128.into()), BoundKind::Lower, true),
            dri(6)
        );
        // Negative: x <= -5/2  ⟹  x <= -3
        assert_eq!(round_int_bound(&r(-5, 2), BoundKind::Upper, false), dri(-3));
    }

    #[test]
    fn floor_ceil_handles_fractions_and_delta() {
        // 5/2 → (2, 3)
        let v = DeltaRational::from_rational(r(5, 2));
        assert_eq!(floor_ceil(&v), (Integer::from(2i128), Integer::from(3i128)));
        // integer 5 with +δ → (5, 6)
        let v = DeltaRational::new(Rational::from_int(5i128.into()), Rational::one());
        assert_eq!(floor_ceil(&v), (Integer::from(5i128), Integer::from(6i128)));
        // integer 5 with −δ → (4, 5)
        let v = DeltaRational::new(Rational::from_int(5i128.into()), -Rational::one());
        assert_eq!(floor_ceil(&v), (Integer::from(4i128), Integer::from(5i128)));
        // −5/2 → (−3, −2)
        let v = DeltaRational::from_rational(r(-5, 2));
        assert_eq!(
            floor_ceil(&v),
            (Integer::from(-3i128), Integer::from(-2i128))
        );
    }
}
