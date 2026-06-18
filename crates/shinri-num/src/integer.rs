use crate::limbs;
use core::cmp::Ordering;

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
}
