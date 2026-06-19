use crate::types::{LBool, Reason};
use shinri_core::{Lit, Var};

/// Per-variable solver state, struct-of-arrays, indexed by `Var::index()`.
pub struct Assignment {
    value: Vec<LBool>,
    level: Vec<u32>,
    reason: Vec<Reason>,
    phase: Vec<bool>,
}

impl Default for Assignment {
    fn default() -> Self {
        Assignment::new()
    }
}

impl Assignment {
    pub fn new() -> Assignment {
        Assignment {
            value: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            phase: Vec::new(),
        }
    }

    #[inline]
    pub fn num_vars(&self) -> usize {
        self.value.len()
    }

    /// Allocate the next variable, defaulting to Unset / phase false.
    pub fn new_var(&mut self) -> Var {
        let v = Var::new(self.value.len() as u32);
        self.value.push(LBool::Unset);
        self.level.push(0);
        self.reason.push(Reason::Decision);
        self.phase.push(false);
        v
    }

    #[inline]
    pub fn value(&self, v: Var) -> LBool {
        self.value[v.index()]
    }

    /// The value of a literal: the var's value flipped if the literal is negative.
    #[inline]
    pub fn lit_value(&self, l: Lit) -> LBool {
        let v = self.value[l.var().index()];
        if l.is_positive() {
            v
        } else {
            v.negate()
        }
    }

    #[inline]
    pub fn level(&self, v: Var) -> u32 {
        self.level[v.index()]
    }

    #[inline]
    pub fn reason(&self, v: Var) -> Reason {
        self.reason[v.index()]
    }

    #[inline]
    pub fn phase(&self, v: Var) -> bool {
        self.phase[v.index()]
    }

    /// Record an assignment making `l` true at `level` with antecedent `reason`.
    #[inline]
    pub fn assign(&mut self, l: Lit, level: u32, reason: Reason) {
        let v = l.var();
        debug_assert_eq!(self.value[v.index()], LBool::Unset, "double-assign");
        self.value[v.index()] = LBool::from_bool(l.is_positive());
        self.level[v.index()] = level;
        self.reason[v.index()] = reason;
        self.phase[v.index()] = l.is_positive();
    }

    /// Clear a variable's value on backtrack, preserving its saved phase.
    #[inline]
    pub fn unassign(&mut self, v: Var) {
        self.value[v.index()] = LBool::Unset;
    }

    /// Clear every variable to Unset / level 0, preserving the variable count
    /// and saved phases (used by the conservative push/pop rebuild).
    pub fn reset(&mut self) {
        for v in &mut self.value {
            *v = LBool::Unset;
        }
        for l in &mut self.level {
            *l = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assign_sets_value_level_phase_then_unassign_clears_value_keeps_phase() {
        let mut a = Assignment::new();
        let v = a.new_var();
        assert_eq!(a.value(v), LBool::Unset);

        let l = Lit::new(v, false); // negative literal
        a.assign(l, 3, Reason::Decision);
        assert_eq!(a.value(v), LBool::False);
        assert_eq!(a.lit_value(l), LBool::True); // the literal itself is satisfied
        assert_eq!(a.level(v), 3);
        assert_eq!(a.reason(v), Reason::Decision);
        assert!(!a.phase(v));

        a.unassign(v);
        assert_eq!(a.value(v), LBool::Unset);
        assert!(!a.phase(v)); // phase is remembered for phase-saving

        // Phase saving must persist a TRUE phase across unassign (not reset to default).
        let l_pos = Lit::new(v, true);
        a.assign(l_pos, 1, Reason::Unit);
        assert!(a.phase(v));
        a.unassign(v);
        assert!(a.phase(v)); // saved phase persists across unassign
    }
}
