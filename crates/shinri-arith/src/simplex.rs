//! The Dutertre–de Moura check loop: find a violated basic, pivot in an entering
//! nonbasic that can repair it (Bland's rule), update, repeat. No candidate ⇒
//! the row is a Farkas witness of infeasibility.

use crate::bounds::Bounds;
use crate::tableau::Tableau;
use crate::vars::ArithVar;
use shinri_num::DeltaRational;

/// The smallest-index basic var whose value is outside its bounds, with the
/// direction it must move. `None` ⇒ all basics feasible.
pub fn first_violated_basic(
    tableau: &Tableau,
    bounds: &Bounds,
    value: &[DeltaRational],
) -> Option<(ArithVar, Below)> {
    let mut best: Option<(ArithVar, Below)> = None;
    for &b in &tableau.basic {
        let v = &value[b.index()];
        if let Some((lo, _)) = bounds.lower(b) {
            if v < lo {
                best = pick(best, b, Below::Lower);
                continue;
            }
        }
        if let Some((hi, _)) = bounds.upper(b) {
            if v > hi {
                best = pick(best, b, Below::Upper);
            }
        }
    }
    best
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Below {
    Lower, // value < lower: must INCREASE basic
    Upper, // value > upper: must DECREASE basic
}

fn pick(cur: Option<(ArithVar, Below)>, b: ArithVar, dir: Below) -> Option<(ArithVar, Below)> {
    match cur {
        Some((c, _)) if c <= b => cur,
        _ => Some((b, dir)),
    }
}

/// A nonbasic var that can move `basic` in the needed direction, by Bland's rule
/// (smallest index). `increase` = basic must increase.
pub fn entering_for(
    tableau: &Tableau,
    bounds: &Bounds,
    value: &[DeltaRational],
    basic: ArithVar,
    increase: bool,
) -> Option<ArithVar> {
    let row = tableau.row(basic);
    let mut vars: Vec<ArithVar> = row.vars().collect();
    vars.sort();
    for j in vars {
        let a = row.coeff(j); // basic = ... + a * j + ...
        if a.is_zero() {
            continue;
        }
        // To increase basic: either a>0 and j can rise, or a<0 and j can fall.
        let a_pos = !a.is_negative();
        let want_rise = increase == a_pos;
        if want_rise && can_rise(bounds, value, j) {
            return Some(j);
        }
        if !want_rise && can_fall(bounds, value, j) {
            return Some(j);
        }
    }
    None
}

fn can_rise(bounds: &Bounds, value: &[DeltaRational], j: ArithVar) -> bool {
    match bounds.upper(j) {
        Some((hi, _)) => &value[j.index()] < hi,
        None => true,
    }
}
fn can_fall(bounds: &Bounds, value: &[DeltaRational], j: ArithVar) -> bool {
    match bounds.lower(j) {
        Some((lo, _)) => &value[j.index()] > lo,
        None => true,
    }
}
