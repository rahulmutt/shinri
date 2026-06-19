//! Combination-lemma certificate content (spec §8). The in-memory record of
//! every theory lemma this crate emits; serialization (Alethe/LRAT) and the
//! stitch with the SAT resolution proof are downstream in shinri-solver.

use shinri_core::Lit;

/// One emitted theory lemma: the conflict `clause` and the input `antecedents`
/// whose conjunction it negates.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CertStep {
    pub clause: Vec<Lit>,
    pub antecedents: Vec<Lit>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CertError {
    /// `clause` is not the negation of `antecedents`.
    NotNegation(usize),
    /// A real conflict cited no antecedents.
    Empty(usize),
}

#[derive(Default)]
pub struct CertLog {
    steps: Vec<CertStep>,
}

impl CertLog {
    pub fn record(&mut self, clause: &[Lit], antecedents: &[Lit]) {
        self.steps.push(CertStep {
            clause: clause.to_vec(),
            antecedents: antecedents.to_vec(),
        });
    }
    pub fn steps(&self) -> &[CertStep] {
        &self.steps
    }

    /// Structural soundness: each clause is exactly the negation of its
    /// antecedents (deeper EUF/Farkas T-validity is re-checked in those crates).
    pub fn recheck(&self) -> Result<(), CertError> {
        for (i, s) in self.steps.iter().enumerate() {
            if s.antecedents.is_empty() {
                return Err(CertError::Empty(i));
            }
            let mut expect: Vec<Lit> = s.antecedents.iter().map(|l| l.negate()).collect();
            expect.sort_unstable_by_key(|l| l.code());
            expect.dedup();
            let mut got = s.clause.clone();
            got.sort_unstable_by_key(|l| l.code());
            got.dedup();
            if expect != got {
                return Err(CertError::NotNegation(i));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Var;

    #[test]
    fn well_formed_lemma_rechecks() {
        let a = Lit::new(Var::new(1), true);
        let b = Lit::new(Var::new(2), true);
        let mut log = CertLog::default();
        log.record(&[a.negate(), b.negate()], &[a, b]);
        assert_eq!(log.recheck(), Ok(()));
    }

    #[test]
    fn empty_antecedents_are_rejected() {
        let a = Lit::new(Var::new(1), true);
        let mut log = CertLog::default();
        log.record(&[a.negate()], &[]);
        assert_eq!(log.recheck(), Err(CertError::Empty(0)));
    }
}
