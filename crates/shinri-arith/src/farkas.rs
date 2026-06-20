//! Build the conflict from an infeasible basic row: the basic's violated bound
//! plus the bound pinning each nonbasic that blocks its repair (spec §7).

use crate::bounds::Bounds;
use crate::simplex::Below;
use crate::tableau::Tableau;
use crate::vars::ArithVar;
use shinri_core::Lit;

/// Collect the literals of the Farkas core for infeasible `basic` (direction `dir`).
pub fn conflict_lits(tableau: &Tableau, bounds: &Bounds, basic: ArithVar, dir: Below) -> Vec<Lit> {
    let mut out = Vec::new();
    // The basic var's own violated bound.
    let basic_lit = match dir {
        Below::Lower => bounds.lower(basic),
        Below::Upper => bounds.upper(basic),
    };
    if let Some((_, l)) = basic_lit {
        out.push(*l);
    }
    // For each nonbasic in the row, the bound that pins it (blocking repair).
    // increase basic? then a>0 nonbasics are pinned at UPPER, a<0 at LOWER; the
    // opposite when decreasing.
    let increase = dir == Below::Lower;
    let row = tableau.row(basic);
    for j in row.vars() {
        let a = row.coeff(j);
        if a.is_zero() {
            continue;
        }
        let a_pos = !a.is_negative();
        // pinned-at-upper when (want basic to rise) and the nonbasic would have to
        // rise to help (a_pos == increase) but it's already at its upper bound.
        let want_rise = increase == a_pos;
        let pin = if want_rise {
            bounds.upper(j)
        } else {
            bounds.lower(j)
        };
        if let Some((_, l)) = pin {
            out.push(*l);
        }
    }
    out.sort_unstable_by_key(|l| l.code());
    out.dedup();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bounds::{BoundKind, Bounds};
    use crate::normalize::LinComb;
    use crate::tableau::Tableau;
    use crate::vars::ArithVar;
    use shinri_core::Var;
    use shinri_num::{DeltaRational, Rational};

    fn av(n: u32) -> ArithVar {
        ArithVar(n)
    }
    fn dr(n: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::from_int(n.into()))
    }
    fn lit(n: u32) -> shinri_core::Lit {
        shinri_core::Lit::new(Var::new(n), true)
    }

    #[test]
    fn conflict_cites_the_pinning_bound_side_not_the_opposite() {
        // Basic row: s = 2x - 3y  (coeff x=+2>0, y=-3<0).
        let x = av(0);
        let y = av(1);
        let s = av(2);
        let mut t = Tableau::default();
        t.define_slack(
            s,
            &LinComb(vec![
                (x, Rational::from_int(2i128.into())),
                (y, Rational::from_int((-3i128).into())),
            ]),
        );
        // Each var gets BOTH bounds, with DISTINCT lits, so the wrong pin side is detectable.
        let mut b = Bounds::default();
        b.ensure(3);
        // s lower bound (the basic's violated side for Below::Lower).
        b.tighten(s, BoundKind::Lower, dr(10), lit(100));
        // x: lower=lit(101), upper=lit(102). Keep lower <= upper: 0 <= 5.
        b.tighten(x, BoundKind::Lower, dr(0), lit(101));
        b.tighten(x, BoundKind::Upper, dr(5), lit(102));
        // y: lower=lit(103), upper=lit(104). Keep lower <= upper: 0 <= 5.
        b.tighten(y, BoundKind::Lower, dr(0), lit(103));
        b.tighten(y, BoundKind::Upper, dr(5), lit(104));

        // dir = Below::Lower => increase basic s.
        // For x (a=+2>0): want_rise=true => cite UPPER(x)=lit(102).
        // For y (a=-3<0): want_rise=false => cite LOWER(y)=lit(103).
        // Basic s: cite LOWER(s)=lit(100).
        let lits = conflict_lits(&t, &b, s, Below::Lower);
        assert!(
            lits.contains(&lit(100)),
            "must cite the basic's violated lower bound"
        );
        assert!(
            lits.contains(&lit(102)),
            "must cite x's UPPER (the pinning side), not its lower"
        );
        assert!(
            lits.contains(&lit(103)),
            "must cite y's LOWER (the pinning side), not its upper"
        );
        // Discrimination: the OPPOSITE sides must NOT be cited.
        assert!(
            !lits.contains(&lit(101)),
            "must NOT cite x's lower (wrong pin side)"
        );
        assert!(
            !lits.contains(&lit(104)),
            "must NOT cite y's upper (wrong pin side)"
        );
    }
}
