//! Mixed-integer Gomory (GMI) cut derivation from a fractional tableau row.
//! Pure: reads tableau + bounds + values, returns a `≤` cut over problem vars.
//! Exact rational arithmetic only.

use crate::bounds::Bounds;
use crate::branch::floor_rational;
use crate::tableau::Tableau;
use crate::vars::{ArithVar, VarStore};
use rustc_hash::FxHashMap;
use shinri_num::{DeltaRational, Rational};

/// A `≤` cut `Σ (coeff·var) ≤ rhs` over PROBLEM variables, valid for every
/// integer point of the feasible region.
#[derive(Clone, Debug)]
pub struct GmiCut {
    pub lhs: Vec<(ArithVar, Rational)>,
    pub rhs: Rational,
}

/// Fractional part `r − ⌊r⌋ ∈ [0, 1)`.
fn frac(r: &Rational) -> Rational {
    r.clone() - Rational::from_int(floor_rational(r))
}

/// Derive a GMI cut from `basic`'s tableau row. Returns `None` if `basic`'s
/// value is integral or no separating cut arises (caller branches instead).
///
/// Row form: `basic = Σ_{j∈N} a_j · x_j`. Each nonbasic `x_j` sits at an active
/// bound; orient `y_j = x_j − lo_j ≥ 0` (at lower) or `y_j = hi_j − x_j ≥ 0`
/// (at upper). With `f0 = frac(β(basic))` and `ā_j` the coefficient of y_j in the
/// rewritten row `basic = β − Σ ā_j·y_j`, the GMI cut is `Σ ψ(ā_j)·y_j ≥ f0`:
///
/// - Integer nonbasic: ψ(ā) = frac(ā) if frac(ā) ≤ f0, else f0*(1−frac(ā))/(1−f0).
/// - Continuous nonbasic: ψ(ā) = ā if ā ≥ 0, else −ā·f0/(1−f0).
///   (≥f0-normalised form — matches integer branch and ge_rhs = f0 baseline.)
///
/// Substituting the y's back and flipping to `≤` yields a cut over problem vars.
pub fn derive_gmi(
    basic: ArithVar,
    tableau: &Tableau,
    bounds: &Bounds,
    value: &[DeltaRational],
    vars: &VarStore,
    expand_slack: &dyn Fn(ArithVar) -> Vec<(ArithVar, Rational)>,
) -> Option<GmiCut> {
    let beta = value[basic.index()].c().clone();
    let f0 = frac(&beta);
    if f0.is_zero() {
        return None; // integral row → nothing to cut
    }
    let one = Rational::one();
    let row = tableau.row(basic);

    // Accumulate x-space coefficients (in ≥ form: Σ coeff·x ≥ ge_rhs).
    // We work in y-space first then substitute y_j back to x_j.
    let mut xcoeff: FxHashMap<ArithVar, Rational> = FxHashMap::default();
    // ge_rhs accumulates: starts as f0, then adjusted as we absorb bound constants.
    let mut ge_rhs = f0.clone();

    for j in row.vars() {
        let a_j = row.coeff(j);
        if a_j.is_zero() {
            continue;
        }

        // Determine orientation and active bound.
        // at lower ⟹ y_j = x_j − lo (sign convention: x_j = y_j + lo)
        // at upper ⟹ y_j = hi − x_j (x_j = hi − y_j)
        //
        // CRITICAL: compare full DeltaRational (c AND k) to identify which bound
        // the nonbasic sits at. Comparing only .c() is wrong when δ distinguishes
        // the bounds (e.g. a strict lower at `2−δ` vs an upper at `2`): the rational
        // parts are equal but the var is NOT at the lower bound. Wrong orientation
        // ⟹ y_j ≠ 0 at the current vertex ⟹ the cut doesn't separate it → panic.
        let val_j = &value[j.index()];
        let at_lower = bounds.lower(j).map(|(d, _)| d == val_j).unwrap_or(false);
        let at_upper = !at_lower && bounds.upper(j).map(|(d, _)| d == val_j).unwrap_or(false);
        let (at_upper_bound, bound_val) = if at_lower {
            (false, bounds.lower(j).unwrap().0.c().clone())
        } else if at_upper {
            (true, bounds.upper(j).unwrap().0.c().clone())
        } else if let Some((d, _)) = bounds.lower(j) {
            // Defensive: value matches neither bound (shouldn't happen for a true
            // nonbasic in a feasible LP state). Fall back to treating as lower.
            (false, d.c().clone())
        } else {
            // Free nonbasic with nonzero coeff: cannot orient ⟹ no cut.
            return None;
        };

        // Compute ā_j: the coefficient of y_j in the form `basic = β − Σ ā_j·y_j`.
        //   At lower (y_j = x_j − lo): a_j·x_j = a_j·(y_j + lo). Coefficient of y_j
        //     in the row (RHS side) is a_j, so ā_j = −a_j (to subtract from β form).
        //   At upper (y_j = hi − x_j): a_j·x_j = a_j·(hi − y_j). Coefficient of y_j
        //     in the row (RHS side) is −a_j, so ā_j = a_j (sign flips naturally).
        // Equivalently: ā_j = −a_j for lower, ā_j = a_j for upper.
        let a_bar = if at_upper_bound {
            a_j.clone()
        } else {
            -a_j.clone()
        };

        // GMI coefficient ψ(ā_j):
        let psi = if vars.is_int(j) {
            // Integer nonbasic
            let f = frac(&a_bar);
            if f <= f0 {
                f
            } else {
                f0.clone() * (one.clone() - f.clone()) / (one.clone() - f0.clone())
            }
        } else {
            // Continuous nonbasic (≥f0-normalised form, matching the integer branch
            // and ge_rhs = f0 baseline):
            //   ψ = ā          if ā ≥ 0  (was ā/f0 in ≥1-normalised form)
            //   ψ = −ā·f0/(1−f0)  if ā < 0
            // Both are ≥ 0: ā ≥ 0 → ψ = ā ≥ 0; ā < 0 → −ā > 0 and f0/(1−f0) > 0.
            if !a_bar.is_negative() {
                a_bar.clone()
            } else {
                (-a_bar.clone()) * f0.clone() / (one.clone() - f0.clone())
            }
        };

        if psi.is_zero() {
            continue;
        }

        // Translate y_j back to x_j and accumulate into the ≥ form.
        //   at lower: y_j = x_j − lo ⟹ ψ·y_j = ψ·x_j − ψ·lo
        //     ≥ form: +ψ·x_j on LHS; add ψ·lo to ge_rhs.
        //   at upper: y_j = hi − x_j ⟹ ψ·y_j = ψ·hi − ψ·x_j
        //     ≥ form: −ψ·x_j on LHS; add ψ·hi to ge_rhs.
        if at_upper_bound {
            let e = xcoeff.entry(j).or_insert_with(Rational::zero);
            *e = e.clone() - psi.clone();
            ge_rhs = ge_rhs - psi * bound_val;
        } else {
            let e = xcoeff.entry(j).or_insert_with(Rational::zero);
            *e = e.clone() + psi.clone();
            ge_rhs = ge_rhs + psi * bound_val;
        }
    }

    if xcoeff.is_empty() {
        return None;
    }

    // Flip ≥ to ≤: negate all coefficients and rhs.
    // Σ c·x ≥ ge_rhs  ⟺  Σ (−c)·x ≤ −ge_rhs
    let rhs_le = -ge_rhs;

    // Expand any slack vars in lhs to problem vars via `expand_slack`.
    let mut prob: FxHashMap<ArithVar, Rational> = FxHashMap::default();
    for (v, c) in xcoeff {
        let neg_c = -c; // flip to ≤
        if vars.is_slack(v) {
            for (pv, pc) in expand_slack(v) {
                let e = prob.entry(pv).or_insert_with(Rational::zero);
                *e = e.clone() + neg_c.clone() * pc;
            }
        } else {
            let e = prob.entry(v).or_insert_with(Rational::zero);
            *e = e.clone() + neg_c;
        }
    }
    let lhs: Vec<(ArithVar, Rational)> = prob.into_iter().filter(|(_, c)| !c.is_zero()).collect();
    if lhs.is_empty() {
        return None;
    }
    let cut = GmiCut { lhs, rhs: rhs_le };
    // Safety net: a non-separating cut is useless; returning None lets the caller
    // fall back to branching (always sound). This guarantees debug_validate's
    // separation assertion can never fire even under edge-case orientation issues.
    if !separates(&cut, value) {
        return None;
    }
    Some(cut)
}

/// True iff the current assignment violates the `≤` cut (strict separation).
pub fn separates(cut: &GmiCut, value: &[DeltaRational]) -> bool {
    let mut acc = Rational::zero();
    for (v, c) in &cut.lhs {
        acc = acc + c.clone() * value[v.index()].c().clone();
    }
    acc > cut.rhs
}

/// Debug self-check: re-derive the cut from the same inputs and assert it
/// matches, and that it separates the current vertex. Compiled out of release.
#[cfg(debug_assertions)]
pub fn debug_validate(
    cut: &GmiCut,
    basic: ArithVar,
    tableau: &Tableau,
    bounds: &Bounds,
    value: &[DeltaRational],
    vars: &VarStore,
    expand_slack: &dyn Fn(ArithVar) -> Vec<(ArithVar, Rational)>,
) {
    assert!(
        separates(cut, value),
        "GMI cut fails to separate the current vertex"
    );
    let again = derive_gmi(basic, tableau, bounds, value, vars, expand_slack)
        .expect("re-derivation must reproduce a cut");
    let mut a: Vec<_> = cut.lhs.clone();
    let mut b: Vec<_> = again.lhs.clone();
    a.sort_by_key(|(v, _)| v.0);
    b.sort_by_key(|(v, _)| v.0);
    assert_eq!(a, b, "GMI re-derivation disagreement (lhs)");
    assert_eq!(cut.rhs, again.rhs, "GMI re-derivation disagreement (rhs)");
}

#[cfg(test)]
mod tests {
    use super::{derive_gmi, separates};
    use crate::bounds::{BoundKind, Bounds};
    use crate::normalize::LinComb;
    use crate::tableau::Tableau;
    use crate::vars::{ArithVar, VarStore};
    use shinri_core::{Lit, TermId, Var};
    use shinri_num::{DeltaRational, Integer, Rational};

    fn dr_r(n: i128, d: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::new(Integer::from(n), Integer::from(d)))
    }
    fn dr(n: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::from_int(Integer::from(n)))
    }
    fn lit() -> Lit {
        Lit::new(Var::new(0), true)
    }

    /// Evaluates `Σ c·point[v]` and asserts it is ≤ `cut.rhs`. Exact rational
    /// arithmetic — guards soundness: all integer-feasible points must satisfy
    /// the cut.
    fn assert_cut_satisfied(cut: &super::GmiCut, point: &[DeltaRational], label: &str) {
        let mut acc = Rational::zero();
        for (v, c) in &cut.lhs {
            acc = acc + c.clone() * point[v.index()].c().clone();
        }
        assert!(
            acc <= cut.rhs,
            "integer-feasible point {label} VIOLATES cut: lhs={acc:?} > rhs={:?}: {cut:?}",
            cut.rhs,
        );
    }

    // Classic 2-var Gomory example: feasible LP vertex is fractional in an
    // integer var; the derived cut must separate that vertex and admit all
    // integer points. We assert separation (the robust, formula-agnostic check)
    // and that the cut is over problem vars only.
    #[test]
    fn gmi_cut_separates_fractional_vertex() {
        // Problem: x, y integer ≥ 0; slack s = x + y. Suppose the simplex sits
        // at x = 3/2 (basic, fractional), with nonbasic vars at their bounds.
        let mut vars = VarStore::default();
        let tx = TermId::new(1).unwrap();
        let ty = TermId::new(2).unwrap();
        let x = vars.problem_var_sorted(tx, true);
        let y = vars.problem_var_sorted(ty, true);
        let comb = LinComb(vec![(x, Rational::one()), (y, Rational::one())]);
        let s = vars.slack_var(&comb);

        let mut tab = Tableau::default();
        tab.define_slack(s, &comb);
        // Pivot x into the basis so x has a row in terms of {s, y}.
        tab.pivot(s, x); // x = s − y

        let mut b = Bounds::default();
        b.ensure(vars.len());
        b.tighten(x, BoundKind::Lower, dr(0), lit());
        b.tighten(y, BoundKind::Lower, dr(0), lit());
        b.tighten(s, BoundKind::Lower, dr(0), lit());
        b.tighten(s, BoundKind::Upper, dr_r(3, 2), lit()); // s ≤ 3/2

        // Values: nonbasic s at its upper bound 3/2, y at lower 0 ⟹ x = 3/2.
        let mut value = vec![DeltaRational::from_rational(Rational::zero()); vars.len()];
        value[s.index()] = dr_r(3, 2);
        value[y.index()] = dr(0);
        value[x.index()] = dr_r(3, 2);

        let comb_of = |v: ArithVar| -> Vec<(ArithVar, Rational)> {
            if v == s {
                vec![(x, Rational::one()), (y, Rational::one())]
            } else {
                vec![(v, Rational::one())]
            }
        };
        let cut = derive_gmi(x, &tab, &b, &value, &vars, &comb_of).expect("fractional row ⟹ a cut");
        // The cut must be over PROBLEM vars only (no slack s).
        assert!(
            cut.lhs.iter().all(|(v, _)| !vars.is_slack(*v)),
            "cut over problem vars: {cut:?}"
        );
        // The cut must separate the current vertex.
        assert!(
            separates(&cut, &value),
            "cut must exclude x=3/2 vertex: {cut:?}"
        );

        // VALIDITY: every integer-feasible point must satisfy the cut.
        // Feasible integer points: x+y ≤ 1 (since s = x+y ≤ 3/2 and x,y ≥ 0 integers
        // implies x+y ≤ 1). Build point vectors indexed by ArithVar.
        let make_point = |xv: i128, yv: i128| -> Vec<DeltaRational> {
            let mut pt = vec![DeltaRational::from_rational(Rational::zero()); vars.len()];
            pt[x.index()] = dr(xv);
            pt[y.index()] = dr(yv);
            pt[s.index()] = dr(xv + yv);
            pt
        };
        assert_cut_satisfied(&cut, &make_point(0, 0), "(x=0,y=0)");
        assert_cut_satisfied(&cut, &make_point(1, 0), "(x=1,y=0)");
        assert_cut_satisfied(&cut, &make_point(0, 1), "(x=0,y=1)");

        // Pin the exact emitted cut: after f0-normalisation the cut must be x+y ≤ 1.
        // Sort lhs by var index for a deterministic comparison.
        let mut lhs_sorted = cut.lhs.clone();
        lhs_sorted.sort_by_key(|(v, _)| v.0);
        let expected_lhs = {
            let mut tmp = vec![(x, Rational::one()), (y, Rational::one())];
            tmp.sort_by_key(|(v, _)| v.0);
            tmp
        };
        assert_eq!(
            lhs_sorted, expected_lhs,
            "cut lhs should be x+y after f0-normalisation: {cut:?}"
        );
        assert_eq!(
            cut.rhs,
            Rational::one(),
            "cut rhs should be 1 after f0-normalisation: {cut:?}"
        );
    }

    // An already-integral row yields no cut.
    #[test]
    fn integral_row_yields_no_cut() {
        let mut vars = VarStore::default();
        let tx = TermId::new(1).unwrap();
        let ty = TermId::new(2).unwrap();
        let x = vars.problem_var_sorted(tx, true);
        let y = vars.problem_var_sorted(ty, true);
        let comb = LinComb(vec![(x, Rational::one()), (y, Rational::one())]);
        let s = vars.slack_var(&comb);
        let mut tab = Tableau::default();
        tab.define_slack(s, &comb);
        tab.pivot(s, x);
        let mut b = Bounds::default();
        b.ensure(vars.len());
        let mut value = vec![DeltaRational::from_rational(Rational::zero()); vars.len()];
        value[x.index()] = dr(2); // integral
        let comb_of = |v: ArithVar| -> Vec<(ArithVar, Rational)> {
            if v == s {
                vec![(x, Rational::one()), (y, Rational::one())]
            } else {
                vec![(v, Rational::one())]
            }
        };
        assert!(derive_gmi(x, &tab, &b, &value, &vars, &comb_of).is_none());
    }
}
