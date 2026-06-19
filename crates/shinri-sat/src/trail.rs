use shinri_core::Lit;

/// The stack of assigned literals in assignment order, plus decision-level
/// markers and the BCP cursor `qhead`. The SAT-specific undo (theories unwind
/// through their own `pop`, driven in lockstep with these levels).
pub struct Trail {
    lits: Vec<Lit>,
    level_starts: Vec<usize>, // level_starts[i] = index where level i+1 began
    qhead: usize,
}

impl Default for Trail {
    fn default() -> Self {
        Trail::new()
    }
}

impl Trail {
    pub fn new() -> Trail {
        Trail { lits: Vec::new(), level_starts: Vec::new(), qhead: 0 }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    #[inline]
    pub fn decision_level(&self) -> u32 {
        self.level_starts.len() as u32
    }

    /// Open a new decision level at the current trail height.
    #[inline]
    pub fn new_level(&mut self) {
        self.level_starts.push(self.lits.len());
    }

    #[inline]
    pub fn push(&mut self, l: Lit) {
        self.lits.push(l);
    }

    #[inline]
    pub fn lit_at(&self, i: usize) -> Lit {
        self.lits[i]
    }

    #[inline]
    pub fn qhead(&self) -> usize {
        self.qhead
    }

    #[inline]
    pub fn set_qhead(&mut self, q: usize) {
        self.qhead = q;
    }

    /// The next literal awaiting propagation, advancing the cursor.
    #[inline]
    pub fn next_unpropagated(&mut self) -> Option<Lit> {
        if self.qhead < self.lits.len() {
            let l = self.lits[self.qhead];
            self.qhead += 1;
            Some(l)
        } else {
            None
        }
    }

    /// The trail index where decision `level` (1-based) began. Panics if
    /// `level == 0` (level 0 has no marker — it starts at index 0).
    #[inline]
    pub fn level_start(&self, level: u32) -> usize {
        self.level_starts[(level - 1) as usize]
    }

    /// Unwind every literal assigned above decision `level`, newest-first,
    /// passing each to `f` (the caller un-assigns it). `qhead` is clamped so
    /// propagation resumes from the truncated end.
    pub fn backtrack_to(&mut self, level: u32, mut f: impl FnMut(Lit)) {
        debug_assert!(level <= self.decision_level(), "backtrack above current level");
        let target_len = if (level as usize) < self.level_starts.len() {
            self.level_starts[level as usize]
        } else {
            self.lits.len()
        };
        while self.lits.len() > target_len {
            f(self.lits.pop().unwrap());
        }
        self.level_starts.truncate(level as usize);
        if self.qhead > self.lits.len() {
            self.qhead = self.lits.len();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Var;

    fn lit(n: u32) -> Lit {
        Lit::new(Var::new(n), true)
    }

    #[test]
    fn levels_push_and_backtrack_replays_newest_first() {
        let mut t = Trail::new();
        t.push(lit(0)); // level 0
        assert_eq!(t.decision_level(), 0);

        t.new_level();
        t.push(lit(1));
        t.push(lit(2)); // level 1: [1,2]
        t.new_level();
        t.push(lit(3)); // level 2: [3]
        assert_eq!(t.decision_level(), 2);
        assert_eq!(t.len(), 4);

        let mut undone = Vec::new();
        t.backtrack_to(1, |l| undone.push(l));
        assert_eq!(undone, vec![lit(3)]); // only level 2 unwound
        assert_eq!(t.decision_level(), 1);

        undone.clear();
        t.backtrack_to(0, |l| undone.push(l));
        assert_eq!(undone, vec![lit(2), lit(1)]); // LIFO
        assert_eq!(t.decision_level(), 0);
        assert_eq!(t.len(), 1); // level-0 lit(0) survives
    }

    #[test]
    fn qhead_walks_then_stops() {
        let mut t = Trail::new();
        t.push(lit(5));
        t.push(lit(6));
        assert_eq!(t.next_unpropagated(), Some(lit(5)));
        assert_eq!(t.next_unpropagated(), Some(lit(6)));
        assert_eq!(t.next_unpropagated(), None);
    }
}
