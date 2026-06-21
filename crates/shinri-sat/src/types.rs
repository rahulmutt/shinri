use crate::clause::ClauseRef;
use shinri_core::Lit;
use shinri_core::TermId;
use shinri_core::TheoryJust;

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
/// carry literal sets the solver folds into conflict analysis. `SplitAtoms`
/// carries a clause of *positive atoms* (as `TermId`s) the solver must mint
/// fresh vars for, bind into the theory, then learn + case-split (splitting on
/// demand — QF_LIA Plan A).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TheoryResult {
    Sat,
    Conflict(Vec<Lit>),
    Lemma(Vec<Lit>),
    SplitAtoms(Vec<TermId>),
}

/// The outcome of a solve. `Unsat.core` is the failed-assumption set
/// (empty for an unconditional UNSAT) — spec §7.2.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SolveResult {
    Sat,
    Unsat { core: Vec<Lit> },
}

/// The antecedent of a trail assignment: why a variable holds its value.
/// The resolution backbone for both conflict analysis and the proof chain.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Reason {
    /// A branching decision or an assumption.
    Decision,
    /// A top-level unit clause (asserted at level 0).
    Unit,
    /// A longer clause became unit under the current trail.
    Clause(ClauseRef),
    /// Implied by an implicit binary clause; the literal is the *other* literal.
    Binary(Lit),
    /// A theory propagation; the explanation is recomputed lazily (spec §8.1).
    Theory(TheoryJust),
}

/// A detected inconsistency: a stored clause, or a virtual clause (an implicit
/// binary, or — later — a theory conflict) given by its literal set.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Conflict {
    Clause(ClauseRef),
    Lits(Vec<Lit>),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lbool_negate_and_from_bool() {
        assert_eq!(LBool::from_bool(true), LBool::True);
        assert_eq!(LBool::True.negate(), LBool::False);
        assert_eq!(LBool::False.negate(), LBool::True);
        assert_eq!(LBool::Unset.negate(), LBool::Unset);
    }

    #[test]
    fn split_atoms_holds_term_ids() {
        let t = shinri_core::TermId::new(7).unwrap();
        let r = TheoryResult::SplitAtoms(vec![t]);
        match r {
            TheoryResult::SplitAtoms(atoms) => assert_eq!(atoms, vec![t]),
            _ => panic!("expected SplitAtoms"),
        }
    }
}
