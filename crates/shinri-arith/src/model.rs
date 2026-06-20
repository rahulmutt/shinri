//! Eliminate the δ-infinitesimal: pick δ* > 0 small enough that every variable's
//! (c, k) value respects all active strict bounds, then emit concrete rationals.

use crate::bounds::Bounds;
use crate::vars::ArithVar;
use shinri_num::{DeltaRational, Rational};

/// A positive δ* no larger than every finite positive gap between an assignment
/// and a strict bound it must respect. Returns 1 when no strict bound binds.
pub fn choose_delta(value: &[DeltaRational], bounds: &Bounds, n: usize) -> Rational {
    let mut delta = Rational::one();
    for i in 0..n {
        let v = ArithVar(i as u32);
        let val = &value[v.index()];
        // For each bound, if it differs only in the δ component, the real gap in
        // c must stay positive: require δ* * |k_gap| < |c_gap| when c_gap != 0.
        for (bound, _) in [bounds.lower(v), bounds.upper(v)].into_iter().flatten() {
            let c_gap = val.c().clone() - bound.c().clone();
            let k_gap = val.k().clone() - bound.k().clone();
            if !c_gap.is_zero() && !k_gap.is_zero() {
                // need delta < |c_gap| / |k_gap|
                let ratio = c_gap.clone() / k_gap.clone();
                let cand = if ratio.is_negative() { -ratio } else { ratio };
                if cand < delta {
                    delta = cand;
                }
            }
        }
    }
    // Halve to stay strictly inside every gap.
    delta / Rational::from_int(2i128.into())
}
