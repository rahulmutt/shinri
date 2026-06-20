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
