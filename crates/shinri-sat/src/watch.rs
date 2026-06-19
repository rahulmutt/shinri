use crate::clause::ClauseRef;
use shinri_core::Lit;

/// What a watch points at. `Binary` means the clause IS `(blocker ∨ index-lit)`
/// and lives entirely in this entry — propagation never touches the arena.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WatchTarget {
    Clause(ClauseRef),
    Binary,
}

/// One watch-list entry: 8 bytes (a tagged `u32` plus the blocking literal).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Watch {
    pub target: WatchTarget,
    pub blocker: Lit,
}

/// Per-literal watch lists, indexed by `Lit::code()`. There are `2*num_vars`
/// lists. A watch on literal `l` fires when `l` becomes false.
pub struct Watches {
    lists: Vec<Vec<Watch>>,
}

impl Default for Watches {
    fn default() -> Self {
        Watches::new()
    }
}

impl Watches {
    pub fn new() -> Watches {
        Watches { lists: Vec::new() }
    }

    /// Grow to hold `2*num_vars` lists.
    pub fn ensure_vars(&mut self, num_vars: usize) {
        let needed = num_vars * 2;
        if self.lists.len() < needed {
            self.lists.resize_with(needed, Vec::new);
        }
    }

    #[inline]
    fn idx(l: Lit) -> usize {
        l.code() as usize
    }

    pub fn watch_clause(&mut self, r: ClauseRef, w0: Lit, w1: Lit) {
        self.lists[Self::idx(w0.negate())].push(Watch {
            target: WatchTarget::Clause(r),
            blocker: w1,
        });
        self.lists[Self::idx(w1.negate())].push(Watch {
            target: WatchTarget::Clause(r),
            blocker: w0,
        });
    }

    pub fn watch_binary(&mut self, a: Lit, b: Lit) {
        self.lists[Self::idx(a.negate())].push(Watch {
            target: WatchTarget::Binary,
            blocker: b,
        });
        self.lists[Self::idx(b.negate())].push(Watch {
            target: WatchTarget::Binary,
            blocker: a,
        });
    }

    #[inline]
    pub fn list(&self, l: Lit) -> &[Watch] {
        &self.lists[Self::idx(l)]
    }

    #[inline]
    pub fn list_mut(&mut self, l: Lit) -> &mut Vec<Watch> {
        &mut self.lists[Self::idx(l)]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Var;

    fn lit(n: u32, pos: bool) -> Lit {
        Lit::new(Var::new(n), pos)
    }

    #[test]
    fn binary_registers_on_negations_with_other_as_blocker() {
        let mut w = Watches::new();
        w.ensure_vars(2);
        let a = lit(0, true);
        let b = lit(1, true);
        w.watch_binary(a, b);
        // (a ∨ b): on ¬a we watch with blocker b; on ¬b blocker a.
        let la = w.list(a.negate());
        assert_eq!(la.len(), 1);
        assert_eq!(la[0].target, WatchTarget::Binary);
        assert_eq!(la[0].blocker, b);
        assert_eq!(w.list(b.negate())[0].blocker, a);
    }

    #[test]
    fn clause_watch_blocker_is_the_other_watched_lit() {
        let mut w = Watches::new();
        w.ensure_vars(3);
        let r = ClauseRef(0);
        let w0 = lit(0, true);
        let w1 = lit(1, true);
        w.watch_clause(r, w0, w1);
        let l = w.list(w0.negate());
        assert_eq!(l[0].target, WatchTarget::Clause(r));
        assert_eq!(l[0].blocker, w1);
        assert_eq!(w.list(w1.negate())[0].blocker, w0);
    }
}
