use rustc_hash::FxHashMap;
use shinri_core::TermId;
use shinri_theory::types::ModelVal;

/// The outcome of `check_sat`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SolveOutcome {
    Sat,
    Unsat,
    Unknown,
}

/// A satisfying assignment, keyed by term.
#[derive(Default, Debug)]
pub struct Model {
    pub(crate) values: FxHashMap<TermId, ModelVal>,
}

impl Model {
    pub fn get(&self, t: TermId) -> Option<&ModelVal> {
        self.values.get(&t)
    }
}
