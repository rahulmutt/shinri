use shinri_core::Var;

/// Reusable scratch for 1-UIP analysis, sized to the variable count so the
/// hot path allocates nothing per conflict.
#[derive(Default)]
pub struct Analyzer {
    /// Per-variable "seen in this analysis" marks.
    pub seen: Vec<bool>,
    /// The learnt clause being built.
    pub learnt: Vec<shinri_core::Lit>,
}

impl Analyzer {
    pub fn ensure_vars(&mut self, n: usize) {
        if self.seen.len() < n {
            self.seen.resize(n, false);
        }
    }

    #[inline]
    pub fn clear_seen(&mut self, v: Var) {
        self.seen[v.index()] = false;
    }
}
