//! Feasibility-based bound tightening (FBBT) over the tableau rows. Pure: reads
//! tableau + bounds, returns tighter INTEGER bounds for the caller to install.

use crate::bounds::{BoundKind, Bounds};
use crate::branch::round_int_bound;
use crate::tableau::Tableau;
use crate::vars::{ArithVar, VarStore};
use shinri_num::{DeltaRational, Rational};

/// A working copy of the bounds as plain rationals (delta dropped -- FBBT reasons
/// over the closed integer relaxation). `None` = unbounded on that side.
#[derive(Clone)]
struct Interval {
    lo: Option<Rational>,
    hi: Option<Rational>,
}

/// Derive tighter INTEGER bounds from the tableau rows by interval propagation
/// to a fixpoint (or `max_rounds`). Returns only bounds strictly tighter than
/// the input. Monotone: never widens, so always sound.
pub fn tighten_to_fixpoint(
    tableau: &Tableau,
    bounds: &Bounds,
    vars: &VarStore,
    max_rounds: usize,
) -> Vec<(ArithVar, BoundKind, DeltaRational)> {
    let n = vars.len();
    // Seed working intervals from the live bounds (drop delta: use the rational part).
    let mut iv: Vec<Interval> = (0..n)
        .map(|i| {
            let v = ArithVar(i as u32);
            Interval {
                lo: bounds.lower(v).map(|(d, _)| d.c().clone()),
                hi: bounds.upper(v).map(|(d, _)| d.c().clone()),
            }
        })
        .collect();

    for _ in 0..max_rounds {
        let mut changed = false;
        // Each basic row is  s = Sum a_j x_j. Treat it as the equality
        // s - Sum a_j x_j = 0 and propagate a bound onto each member, including s.
        let basics: Vec<ArithVar> = tableau.basic.iter().copied().collect();
        for s in basics {
            let row = tableau.row(s);
            // members: (var, coeff) for s (coeff -1) and each x_j (coeff +a_j),
            // expressing  Sum coeff*var = 0.
            let mut members: Vec<(ArithVar, Rational)> = vec![(s, -Rational::one())];
            for j in row.vars() {
                members.push((j, row.coeff(j)));
            }
            // For each target member k: coeff_k*x_k = -Sum_{i!=k} coeff_i*x_i.
            for k in 0..members.len() {
                let (vk, ck) = members[k].clone();
                if ck.is_zero() {
                    continue;
                }
                // Bound the RHS sum -Sum_{i!=k} coeff_i*x_i using the others' intervals.
                let (mut rhs_lo, mut rhs_hi) = (Some(Rational::zero()), Some(Rational::zero()));
                for (i, (vi, ci)) in members.iter().enumerate() {
                    if i == k {
                        continue;
                    }
                    // contribution = -ci*x_i ; its range from x_i's interval.
                    let neg = -ci.clone();
                    let (clo, chi) = term_range(&neg, &iv[vi.index()]);
                    rhs_lo = add_opt(rhs_lo, clo);
                    rhs_hi = add_opt(rhs_hi, chi);
                }
                // x_k = rhs / ck. Dividing by a negative flips the interval ends.
                let (mut nlo, mut nhi) = (
                    rhs_lo.map(|r| r / ck.clone()),
                    rhs_hi.map(|r| r / ck.clone()),
                );
                if ck.is_negative() {
                    std::mem::swap(&mut nlo, &mut nhi);
                }
                // Integer rounding for Int vars; tighten only if strictly better.
                let is_int = vars.is_int(vk);
                if let Some(hi) = nhi {
                    let cand = if is_int {
                        round_int_bound(&hi, BoundKind::Upper, false).c().clone()
                    } else {
                        hi
                    };
                    if iv[vk.index()].hi.as_ref().is_none_or(|cur| &cand < cur) {
                        iv[vk.index()].hi = Some(cand);
                        changed = true;
                    }
                }
                if let Some(lo) = nlo {
                    let cand = if is_int {
                        round_int_bound(&lo, BoundKind::Lower, false).c().clone()
                    } else {
                        lo
                    };
                    if iv[vk.index()].lo.as_ref().is_none_or(|cur| &cand > cur) {
                        iv[vk.index()].lo = Some(cand);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Emit only bounds strictly tighter than the original live bounds.
    let mut out = Vec::new();
    for (i, interval) in iv.iter().enumerate() {
        let v = ArithVar(i as u32);
        if let Some(hi) = &interval.hi {
            let tighter = bounds.upper(v).is_none_or(|(d, _)| hi < d.c());
            if tighter {
                out.push((
                    v,
                    BoundKind::Upper,
                    DeltaRational::from_rational(hi.clone()),
                ));
            }
        }
        if let Some(lo) = &interval.lo {
            let tighter = bounds.lower(v).is_none_or(|(d, _)| lo > d.c());
            if tighter {
                out.push((
                    v,
                    BoundKind::Lower,
                    DeltaRational::from_rational(lo.clone()),
                ));
            }
        }
    }
    out
}

/// Range of `coeff * x` over x's interval. `None` end = unbounded.
fn term_range(coeff: &Rational, iv: &Interval) -> (Option<Rational>, Option<Rational>) {
    if coeff.is_zero() {
        return (Some(Rational::zero()), Some(Rational::zero()));
    }
    let a = iv.lo.clone().map(|l| coeff.clone() * l);
    let b = iv.hi.clone().map(|h| coeff.clone() * h);
    if coeff.is_negative() {
        // negative coeff flips which end is the min/max
        (b, a)
    } else {
        (a, b)
    }
}

/// `a + b` where `None` is an unbounded (infinite) end -> result unbounded.
fn add_opt(a: Option<Rational>, b: Option<Rational>) -> Option<Rational> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x + y),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::tighten_to_fixpoint;
    use crate::bounds::{BoundKind, Bounds};
    use crate::normalize::LinComb;
    use crate::tableau::Tableau;
    use crate::vars::VarStore;
    use shinri_core::{Lit, Var};
    use shinri_num::{DeltaRational, Integer, Rational};

    fn dr(n: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::from_int(Integer::from(n)))
    }
    fn lit() -> Lit {
        Lit::new(Var::new(0), true)
    }

    // System: x, y integer in [0, 10]; slack s = x + y with s <= 1.
    // FBBT must derive x <= 1 and y <= 1 (since the other var >= 0).
    #[test]
    fn fbbt_tightens_from_a_sum_bound() {
        let mut vars = VarStore::default();
        let tx = shinri_core::TermId::new(1).unwrap();
        let ty = shinri_core::TermId::new(2).unwrap();
        let x = vars.problem_var_sorted(tx, true);
        let y = vars.problem_var_sorted(ty, true);
        let comb = LinComb(vec![(x, Rational::one()), (y, Rational::one())]);
        let s = vars.slack_var(&comb);

        let mut tab = Tableau::default();
        tab.define_slack(s, &comb);

        let mut b = Bounds::default();
        b.ensure(vars.len());
        // x, y in [0, 10]
        for v in [x, y] {
            b.tighten(v, BoundKind::Lower, dr(0), lit());
            b.tighten(v, BoundKind::Upper, dr(10), lit());
        }
        // s <= 1, s >= 0
        b.tighten(s, BoundKind::Lower, dr(0), lit());
        b.tighten(s, BoundKind::Upper, dr(1), lit());

        let out = tighten_to_fixpoint(&tab, &b, &vars, 8);
        // Expect x <= 1 and y <= 1 among the tightenings.
        assert!(out.contains(&(x, BoundKind::Upper, dr(1))), "got {out:?}");
        assert!(out.contains(&(y, BoundKind::Upper, dr(1))), "got {out:?}");
    }

    // Integer rounding: slack s = 3x with s <= 7  =>  x <= 2  (floor(7/3)), not 7/3.
    #[test]
    fn fbbt_rounds_to_integer() {
        let mut vars = VarStore::default();
        let tx = shinri_core::TermId::new(1).unwrap();
        let x = vars.problem_var_sorted(tx, true);
        let comb = LinComb(vec![(x, Rational::from_int(3i128.into()))]);
        let s = vars.slack_var(&comb);
        let mut tab = Tableau::default();
        tab.define_slack(s, &comb);
        let mut b = Bounds::default();
        b.ensure(vars.len());
        b.tighten(x, BoundKind::Lower, dr(0), lit());
        b.tighten(x, BoundKind::Upper, dr(100), lit());
        b.tighten(s, BoundKind::Lower, dr(0), lit());
        b.tighten(s, BoundKind::Upper, dr(7), lit());
        let out = tighten_to_fixpoint(&tab, &b, &vars, 8);
        assert!(out.contains(&(x, BoundKind::Upper, dr(2))), "got {out:?}");
    }
}
