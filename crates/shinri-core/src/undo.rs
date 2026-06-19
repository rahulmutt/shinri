/// A generic, monomorphized typed undo log. The core backtracking primitive
/// (spec §6): each component instantiates it with its own POD entry type `E`
/// and supplies how to undo one entry via the `pop_to` closure. Flat `Vec`,
/// no dyn dispatch, zero overhead on normal (non-backtrack) component access.
pub struct UndoLog<E> {
    entries: Vec<E>,
    /// `level_starts[i]` = number of entries present when level `i+1` began.
    level_starts: Vec<usize>,
}

impl<E> Default for UndoLog<E> {
    fn default() -> Self {
        UndoLog {
            entries: Vec::new(),
            level_starts: Vec::new(),
        }
    }
}

impl<E> UndoLog<E> {
    #[inline]
    pub fn record(&mut self, e: E) {
        self.entries.push(e);
    }

    #[inline]
    pub fn push_level(&mut self) {
        self.level_starts.push(self.entries.len());
    }

    #[inline]
    pub fn level(&self) -> usize {
        self.level_starts.len()
    }

    /// Pop back to `level`, replaying each undone entry through `f` in reverse
    /// (LIFO) order. Panics in debug if `level` exceeds the current level.
    pub fn pop_to(&mut self, level: usize, mut f: impl FnMut(E)) {
        debug_assert!(level <= self.level(), "pop_to: target level above current");
        while self.level_starts.len() > level {
            let start = self.level_starts.pop().unwrap();
            while self.entries.len() > start {
                let e = self.entries.pop().unwrap();
                f(e);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn levels_and_lifo_replay() {
        let mut log: UndoLog<i32> = UndoLog::default();
        assert_eq!(log.level(), 0);
        log.record(1);
        log.push_level(); // level 1 starts
        assert_eq!(log.level(), 1);
        log.record(2);
        log.record(3);
        log.push_level(); // level 2 starts
        assert_eq!(log.level(), 2);
        log.record(4);

        let mut undone = Vec::new();
        log.pop_to(1, |e| undone.push(e)); // undo level 2's entries only
        assert_eq!(undone, vec![4]);
        assert_eq!(log.level(), 1);

        undone.clear();
        log.pop_to(0, |e| undone.push(e)); // undo level 1's entries, LIFO
        assert_eq!(undone, vec![3, 2]);
        assert_eq!(log.level(), 0);
    }

    #[test]
    fn pop_to_current_level_is_noop() {
        let mut log: UndoLog<i32> = UndoLog::default();
        log.push_level();
        log.record(9);
        let mut count = 0;
        log.pop_to(1, |_| count += 1);
        assert_eq!(count, 0);
        assert_eq!(log.level(), 1);
    }
}
