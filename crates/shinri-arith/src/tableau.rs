//! The simplex tableau: integer rows with a shared per-row denominator (spec §7.5).
//! Row i means `den_i · x_basic_i = Σ num_i[j] · x_j` over nonbasic j.

use crate::vars::ArithVar;
use rustc_hash::FxHashMap;
use shinri_num::{Integer, Rational};

#[derive(Clone, Debug)]
pub struct Row {
    pub num: FxHashMap<ArithVar, Integer>,
    pub den: Integer,
}

impl Default for Row {
    fn default() -> Self {
        Row {
            num: FxHashMap::default(),
            // den > 0 invariant: use one(), not zero()
            den: Integer::one(),
        }
    }
}

impl Row {
    /// Build `x_basic = Σ a_j x_j` as integer numerators over a shared denominator.
    pub fn from_rationals(coeffs: &[(ArithVar, Rational)]) -> Row {
        // Shared denominator = lcm of all a_j denominators.
        let mut den = Integer::one();
        for (_, a) in coeffs {
            den = lcm(&den, &a.denom());
        }
        let mut num = FxHashMap::default();
        for (v, a) in coeffs {
            // a_j = a.numer/a.denom ; numerator over shared den = a.numer * (den/a.denom)
            let scale = exact_div(&den, &a.denom());
            // Integer Mul is by-value: clone both operands
            let n = a.numer() * scale;
            if !n.is_zero() {
                num.insert(*v, n);
            }
        }
        let mut r = Row { num, den };
        r.reduce();
        r
    }

    #[inline]
    pub fn coeff(&self, v: ArithVar) -> Rational {
        match self.num.get(&v) {
            Some(n) => Rational::new(n.clone(), self.den.clone()),
            None => Rational::zero(),
        }
    }

    pub fn vars(&self) -> impl Iterator<Item = ArithVar> + '_ {
        self.num.keys().copied()
    }

    /// Divide through by gcd(all numerators, den); force den > 0.
    pub fn reduce(&mut self) {
        if self.den.is_zero() {
            self.den = Integer::one();
        }
        let mut g = self.den.abs();
        for n in self.num.values() {
            g = g.gcd(n);
            if g == Integer::one() {
                break;
            }
        }
        if g != Integer::one() {
            self.den = exact_div(&self.den, &g);
            for n in self.num.values_mut() {
                *n = exact_div(n, &g);
            }
        }
        if self.den.is_negative() {
            // Integer Neg is by-value: negate an owned clone
            self.den = -self.den.clone();
            for n in self.num.values_mut() {
                *n = -n.clone();
            }
        }
        self.num.retain(|_, n| !n.is_zero());
    }
}

fn exact_div(a: &Integer, b: &Integer) -> Integer {
    let (q, r) = a.div_rem(b);
    debug_assert!(r.is_zero(), "exact_div with remainder");
    q
}

fn lcm(a: &Integer, b: &Integer) -> Integer {
    if a.is_zero() || b.is_zero() {
        return Integer::zero();
    }
    let g = a.gcd(b);
    let q = exact_div(a, &g);
    // Integer Mul is by-value: q * b.clone(), then abs()
    (q * b.clone()).abs()
}

#[cfg(test)]
mod row_tests {
    use super::*;

    fn av(n: u32) -> ArithVar {
        ArithVar(n)
    }

    #[test]
    fn from_rationals_reduces_to_shared_denominator() {
        // x_basic = (1/2) a + (1/3) b  ==>  6 x = 3 a + 2 b
        let r = Row::from_rationals(&[
            (av(1), Rational::new(1i128.into(), 2i128.into())),
            (av(2), Rational::new(1i128.into(), 3i128.into())),
        ]);
        assert_eq!(r.den, Integer::from(6i128));
        assert_eq!(r.num[&av(1)], Integer::from(3i128));
        assert_eq!(r.num[&av(2)], Integer::from(2i128));
        // coeff recovers the rationals.
        assert_eq!(r.coeff(av(1)), Rational::new(1i128.into(), 2i128.into()));
        assert_eq!(r.coeff(av(2)), Rational::new(1i128.into(), 3i128.into()));
        assert_eq!(r.coeff(av(9)), Rational::zero());
    }

    #[test]
    fn reduce_strips_common_factor_and_normalizes_sign() {
        // 4 x = 2 a  (den could come in negative) -> 2 x = 1 a
        let mut r = Row {
            num: [(av(1), Integer::from(-2i128))].into_iter().collect(),
            den: Integer::from(-4i128),
        };
        r.reduce();
        assert_eq!(r.den, Integer::from(2i128));
        assert_eq!(r.num[&av(1)], Integer::from(1i128));
    }
}
