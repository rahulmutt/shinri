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

    /// First term that `self` and `other` assign different values to, if any.
    pub fn merge_check(&self, other: &ModelBuilder) -> Option<TermId> {
        for (t, v) in self.values.iter() {
            if let Some(ov) = other.values.get(t) {
                if v != ov {
                    return Some(*t);
                }
            }
        }
        None
    }

    /// Fold another builder's assignments into this one (other wins ties; the
    /// caller has already verified agreement via `merge_check`).
    pub fn absorb(&mut self, other: ModelBuilder) {
        for (t, v) in other.values {
            self.values.insert(t, v);
        }
    }

    /// Iterate all assigned `(TermId, ModelVal)` pairs.
    pub fn iter(&self) -> impl Iterator<Item = (shinri_core::TermId, crate::types::ModelVal)> + '_ {
        self.values.iter().map(|(t, v)| (*t, v.clone()))
    }
}
