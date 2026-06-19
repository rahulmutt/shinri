use shinri_core::Lit;

/// A three-valued Boolean: the value of a variable on the current trail.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LBool {
    True,
    False,
    Unset,
}

impl LBool {
    #[inline]
    pub fn from_bool(b: bool) -> LBool {
        if b {
            LBool::True
        } else {
            LBool::False
        }
    }
    /// Flip True<->False; Unset stays Unset.
    #[inline]
    pub fn negate(self) -> LBool {
        match self {
            LBool::True => LBool::False,
            LBool::False => LBool::True,
            LBool::Unset => LBool::Unset,
        }
    }
}

/// The effort a theory `check` is asked for (spec §8.1).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Effort {
    Standard,
    Full,
}

/// The result of a theory consistency `check` (spec §8.1). `Conflict`/`Lemma`
/// carry literal sets the solver folds into conflict analysis.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TheoryResult {
    Sat,
    Conflict(Vec<Lit>),
    Lemma(Vec<Lit>),
}

/// The outcome of a solve. `Unsat.core` is the failed-assumption set
/// (empty for an unconditional UNSAT) — spec §7.2.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SolveResult {
    Sat,
    Unsat { core: Vec<Lit> },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lbool_negate_and_from_bool() {
        assert_eq!(LBool::from_bool(true), LBool::True);
        assert_eq!(LBool::True.negate(), LBool::False);
        assert_eq!(LBool::Unset.negate(), LBool::Unset);
    }
}
