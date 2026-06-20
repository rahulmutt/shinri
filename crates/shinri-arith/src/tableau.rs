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

use crate::normalize::LinComb;
use rustc_hash::FxHashSet;

#[derive(Default)]
pub struct Tableau {
    pub rows: FxHashMap<ArithVar, Row>,
    pub basic: FxHashSet<ArithVar>,
}

impl Tableau {
    #[inline]
    pub fn is_basic(&self, v: ArithVar) -> bool {
        self.basic.contains(&v)
    }

    #[inline]
    pub fn row(&self, basic: ArithVar) -> &Row {
        &self.rows[&basic]
    }

    pub fn define_slack(&mut self, slack: ArithVar, comb: &LinComb) {
        if self.basic.contains(&slack) {
            return;
        }
        let row = Row::from_rationals(&comb.0);
        self.rows.insert(slack, row);
        self.basic.insert(slack);
    }

    /// Swap `entering` (nonbasic) into the basis; `basic` leaves. Gauss-Jordan
    /// over the rational coefficients, each row re-reduced to shared-denominator
    /// integer form afterward (spec §7.5).
    pub fn pivot(&mut self, basic: ArithVar, entering: ArithVar) {
        // Solve rows[basic]:  basic = Σ a_j x_j , with a_e = coeff(entering) ≠ 0.
        // => entering = (1/a_e) basic - Σ_{j≠e} (a_j/a_e) x_j
        let old = self.rows.remove(&basic).expect("pivot on non-basic row");
        let a_e = old.coeff(entering);
        debug_assert!(!a_e.is_zero(), "pivot on zero coefficient");
        let inv = a_e.recip();

        // Build entering_row: (basic, 1/a_e) and (j, -(a_j/a_e)) for each j≠entering.
        let mut solved: Vec<(ArithVar, Rational)> = Vec::new();
        solved.push((basic, inv.clone()));
        for v in old.vars() {
            if v == entering {
                continue;
            }
            let a_j = old.coeff(v);
            solved.push((v, -(a_j * inv.clone())));
        }
        let entering_row = Row::from_rationals(&solved);

        // Substitute `entering` out of every other row:
        //   row b: b = Σ c_k x_k + c_e * entering
        //   ->  b = Σ c_k x_k + c_e * entering_row   (drop the c_e·entering term)
        // new_b[v] = old_b.coeff(v) (for v≠entering) + c_e * entering_row.coeff(v)
        let other_basics: Vec<ArithVar> = self.rows.keys().copied().collect();
        for b in other_basics {
            let c_e = self.rows[&b].coeff(entering);
            if c_e.is_zero() {
                continue;
            }
            // Collect all vars from old row b (excluding entering) and entering_row.
            let mut merged: FxHashMap<ArithVar, Rational> = FxHashMap::default();
            // Contribution from old row b (without the entering term).
            for v in self.rows[&b].vars() {
                if v == entering {
                    continue;
                }
                let coeff = self.rows[&b].coeff(v);
                *merged.entry(v).or_insert_with(Rational::zero) =
                    merged.get(&v).cloned().unwrap_or_else(Rational::zero) + coeff;
            }
            // Contribution from c_e * entering_row.
            for v in entering_row.vars() {
                let add = c_e.clone() * entering_row.coeff(v);
                let e = merged.entry(v).or_insert_with(Rational::zero);
                *e = e.clone() + add;
            }
            let pairs: Vec<(ArithVar, Rational)> = merged.into_iter().collect();
            self.rows.insert(b, Row::from_rationals(&pairs));
        }

        self.rows.insert(entering, entering_row);
        self.basic.remove(&basic);
        self.basic.insert(entering);
    }
}

#[cfg(test)]
mod tableau_tests {
    use super::*;
    fn av(n: u32) -> ArithVar {
        ArithVar(n)
    }

    #[test]
    fn define_slack_creates_a_basic_row() {
        // s = 2x + 3y
        let mut t = Tableau::default();
        let comb = LinComb(vec![
            (av(1), Rational::from_int(2i128.into())),
            (av(2), Rational::from_int(3i128.into())),
        ]);
        t.define_slack(av(0), &comb);
        assert!(t.is_basic(av(0)));
        assert_eq!(t.row(av(0)).coeff(av(1)), Rational::from_int(2i128.into()));
        assert_eq!(t.row(av(0)).coeff(av(2)), Rational::from_int(3i128.into()));
    }

    #[test]
    fn pivot_swaps_basis_and_rewrites() {
        // s = 2x + 3y ; pivot x in, s out  =>  x = (1/2) s - (3/2) y
        let mut t = Tableau::default();
        let comb = LinComb(vec![
            (av(1), Rational::from_int(2i128.into())),
            (av(2), Rational::from_int(3i128.into())),
        ]);
        t.define_slack(av(0), &comb);
        t.pivot(av(0), av(1));
        assert!(t.is_basic(av(1)));
        assert!(!t.is_basic(av(0)));
        assert_eq!(
            t.row(av(1)).coeff(av(0)),
            Rational::new(1i128.into(), 2i128.into())
        );
        assert_eq!(
            t.row(av(1)).coeff(av(2)),
            Rational::new((-3i128).into(), 2i128.into())
        );
    }

    #[test]
    fn pivot_sums_shared_variable_across_rows() {
        // Two basic rows sharing nonbasic y:
        //   s1 = 2x + 3y   (av 3)
        //   s2 =  x + 4y   (av 4)
        // pivot(s1, x):  x = (1/2)s1 - (3/2)y, then substitute x out of s2:
        //   s2 = (s2 without x) + c_e * entering_row
        //      = 4y + 1*((1/2)s1 - (3/2)y) = (1/2)s1 + (5/2)y
        // y appears in BOTH old-s2 (4y) and entering_row (-3/2 y) -> coefficients SUM to 5/2.
        let mut t = Tableau::default();
        let comb1 = LinComb(vec![
            (av(1), Rational::from_int(2i128.into())),
            (av(2), Rational::from_int(3i128.into())),
        ]);
        let comb2 = LinComb(vec![
            (av(1), Rational::one()),
            (av(2), Rational::from_int(4i128.into())),
        ]);
        t.define_slack(av(3), &comb1); // s1
        t.define_slack(av(4), &comb2); // s2
        t.pivot(av(3), av(1)); // pivot x(av1) in, s1(av3) out
        assert!(t.is_basic(av(1))); // x now basic
        assert!(!t.is_basic(av(3))); // s1 now nonbasic
        assert!(t.is_basic(av(4))); // s2 still basic
                                    // x's row: x = (1/2)s1 - (3/2)y
        assert_eq!(
            t.row(av(1)).coeff(av(3)),
            Rational::new(1i128.into(), 2i128.into())
        );
        assert_eq!(
            t.row(av(1)).coeff(av(2)),
            Rational::new((-3i128).into(), 2i128.into())
        );
        // s2's REWRITTEN row: s2 = (1/2)s1 + (5/2)y  <-- the shared-y summation
        assert_eq!(
            t.row(av(4)).coeff(av(3)),
            Rational::new(1i128.into(), 2i128.into())
        );
        assert_eq!(
            t.row(av(4)).coeff(av(2)),
            Rational::new(5i128.into(), 2i128.into())
        );
        // s2 no longer references x directly.
        assert_eq!(t.row(av(4)).coeff(av(1)), Rational::zero());
    }
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
