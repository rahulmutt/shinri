//! Per-variable lower/upper bounds (as DeltaRational) with a trail for backtrack.

use crate::vars::ArithVar;
use shinri_core::Lit;
use shinri_num::DeltaRational;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BoundKind {
    Lower,
    Upper,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TightenResult {
    Redundant,
    Tightened,
    Conflict { other: Lit },
}

#[derive(Clone, Default)]
struct VarBounds {
    lower: Option<(DeltaRational, Lit)>,
    upper: Option<(DeltaRational, Lit)>,
}

type TrailEntry = (ArithVar, BoundKind, Option<(DeltaRational, Lit)>);

#[derive(Default)]
pub struct Bounds {
    vars: Vec<VarBounds>,
    // Undo trail: (var, kind, previous value). Checkpoints index into this.
    trail: Vec<TrailEntry>,
    marks: Vec<usize>,
}

impl Bounds {
    pub fn ensure(&mut self, n: usize) {
        if self.vars.len() < n {
            self.vars.resize(n, VarBounds::default());
        }
    }

    pub fn lower(&self, v: ArithVar) -> Option<&(DeltaRational, Lit)> {
        self.vars[v.index()].lower.as_ref()
    }
    pub fn upper(&self, v: ArithVar) -> Option<&(DeltaRational, Lit)> {
        self.vars[v.index()].upper.as_ref()
    }

    pub fn mark(&mut self) {
        self.marks.push(self.trail.len());
    }

    /// Number of live marks (so a caller can `undo_to` this exact depth later).
    pub fn marks_len(&self) -> usize {
        self.marks.len()
    }

    /// Undo down to `checkpoints` remaining marks (absolute count of marks kept).
    pub fn undo_to(&mut self, checkpoints: usize) {
        while self.marks.len() > checkpoints {
            let target = self.marks.pop().unwrap();
            while self.trail.len() > target {
                let (v, kind, prev) = self.trail.pop().unwrap();
                match kind {
                    BoundKind::Lower => self.vars[v.index()].lower = prev,
                    BoundKind::Upper => self.vars[v.index()].upper = prev,
                }
            }
        }
    }

    pub fn tighten(
        &mut self,
        v: ArithVar,
        kind: BoundKind,
        val: DeltaRational,
        lit: Lit,
    ) -> TightenResult {
        self.ensure(v.index() + 1);
        // Read needed values first to avoid simultaneous borrow + mutable borrow.
        let cur_lower = self.vars[v.index()].lower.clone();
        let cur_upper = self.vars[v.index()].upper.clone();
        match kind {
            BoundKind::Lower => {
                if let Some((ref cur, _)) = cur_lower {
                    if &val <= cur {
                        return TightenResult::Redundant;
                    }
                }
                if let Some((ref ub, ulit)) = cur_upper {
                    if &val > ub {
                        return TightenResult::Conflict { other: ulit };
                    }
                }
                let prev = self.vars[v.index()].lower.take();
                self.trail.push((v, BoundKind::Lower, prev));
                self.vars[v.index()].lower = Some((val, lit));
                TightenResult::Tightened
            }
            BoundKind::Upper => {
                if let Some((ref cur, _)) = cur_upper {
                    if &val >= cur {
                        return TightenResult::Redundant;
                    }
                }
                if let Some((ref lb, llit)) = cur_lower {
                    if &val < lb {
                        return TightenResult::Conflict { other: llit };
                    }
                }
                let prev = self.vars[v.index()].upper.take();
                self.trail.push((v, BoundKind::Upper, prev));
                self.vars[v.index()].upper = Some((val, lit));
                TightenResult::Tightened
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_num::Rational;

    fn dr(n: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::from_int(n.into()))
    }
    fn lit(n: u32) -> Lit {
        Lit::new(shinri_core::Var::new(n), true)
    }
    fn av(n: u32) -> ArithVar {
        ArithVar(n)
    }

    #[test]
    fn tighten_detects_crossing_conflict() {
        let mut b = Bounds::default();
        b.ensure(1);
        assert_eq!(
            b.tighten(av(0), BoundKind::Lower, dr(5), lit(1)),
            TightenResult::Tightened
        );
        // upper 3 < lower 5 -> conflict citing the lower's lit.
        assert_eq!(
            b.tighten(av(0), BoundKind::Upper, dr(3), lit(2)),
            TightenResult::Conflict { other: lit(1) }
        );
    }

    #[test]
    fn redundant_bound_is_ignored() {
        let mut b = Bounds::default();
        b.ensure(1);
        b.tighten(av(0), BoundKind::Upper, dr(10), lit(1));
        assert_eq!(
            b.tighten(av(0), BoundKind::Upper, dr(20), lit(2)),
            TightenResult::Redundant
        );
    }

    #[test]
    fn undo_restores_previous_bounds() {
        let mut b = Bounds::default();
        b.ensure(1);
        b.tighten(av(0), BoundKind::Upper, dr(10), lit(1));
        b.mark();
        b.tighten(av(0), BoundKind::Upper, dr(4), lit(2));
        assert_eq!(b.upper(av(0)).unwrap().0, dr(4));
        b.undo_to(0);
        assert_eq!(b.upper(av(0)).unwrap().0, dr(10));
    }

    #[test]
    fn undo_removes_a_freshly_installed_bound() {
        let mut b = Bounds::default();
        b.ensure(1);
        // No prior bound on av(0).
        b.mark();
        assert_eq!(
            b.tighten(av(0), BoundKind::Lower, dr(7), lit(1)),
            TightenResult::Tightened
        );
        assert!(b.lower(av(0)).is_some());
        b.undo_to(0);
        // The bound was installed with prev=None, so undo must restore it to None.
        assert!(b.lower(av(0)).is_none());
    }

    #[test]
    fn tighten_detects_crossing_conflict_other_direction() {
        let mut b = Bounds::default();
        b.ensure(1);
        assert_eq!(
            b.tighten(av(0), BoundKind::Upper, dr(3), lit(1)),
            TightenResult::Tightened
        );
        // lower 5 > upper 3 -> conflict citing the upper's lit.
        assert_eq!(
            b.tighten(av(0), BoundKind::Lower, dr(5), lit(2)),
            TightenResult::Conflict { other: lit(1) }
        );
    }
}
