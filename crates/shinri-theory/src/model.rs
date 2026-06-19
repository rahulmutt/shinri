//! Combined model assembly (spec §7.3). The skeleton (this task) is the storage
//! map; the cross-theory assembly + self-check live in the Combiner (Task 14).

use crate::types::ModelVal;
use rustc_hash::FxHashMap;
use shinri_core::TermId;

/// Each theory writes its term values here; the Combiner reconciles them.
#[derive(Default)]
pub struct ModelBuilder {
    values: FxHashMap<TermId, ModelVal>,
}

impl ModelBuilder {
    #[inline]
    pub fn assign(&mut self, t: TermId, v: ModelVal) {
        self.values.insert(t, v);
    }
    #[inline]
    pub fn get(&self, t: TermId) -> Option<&ModelVal> {
        self.values.get(&t)
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
}
