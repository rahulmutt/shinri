use crate::assignment::Assignment;
use crate::heuristic::BranchHeuristic;
use crate::types::LBool;
use shinri_core::Var;

const NIL: u32 = u32::MAX;

/// Variable Move-To-Front: a doubly-linked priority list over variables. The
/// most-recently-bumped variable is at the head; `next` walks from a `search`
/// pointer (kept at-or-before the highest-priority unassigned var). Integer
/// stamps only — fully deterministic.
///
/// `stamp` totally orders every variable by "closeness to head": a bumped
/// variable is moved to the actual head and stamped with an increasing
/// non-negative `counter` value (so the most recently bumped variable has the
/// highest stamp of all). A variable that has NEVER been bumped keeps its
/// original tail-appended list position, so it must compare as "further from
/// head" than every bumped variable AND be ordered against other never-bumped
/// variables by creation order (earlier-created = closer to head). We get
/// both properties from ONE comparable field by giving never-bumped variables
/// strictly NEGATIVE, decreasing-with-creation-order stamps (`creation_seq`):
/// they always lose to any non-negative bump stamp, and among themselves the
/// earlier-created variable (less negative) wins, matching its head-ward
/// position in the tail-append order.
pub struct Vmtf {
    next: Vec<u32>,
    prev: Vec<u32>,
    stamp: Vec<i64>,
    head: u32,
    tail: u32,
    search: u32,
    counter: i64,
    /// Next stamp to hand to a newly created (never-bumped) variable;
    /// strictly negative and decremented on every `new_var` call so earlier
    /// creations keep a higher (less negative) stamp than later ones.
    creation_seq: i64,
}

impl Default for Vmtf {
    fn default() -> Self {
        Vmtf {
            next: Vec::new(),
            prev: Vec::new(),
            stamp: Vec::new(),
            head: NIL,
            tail: NIL,
            search: NIL,
            counter: 0,
            creation_seq: -1,
        }
    }
}

impl Vmtf {
    fn unlink(&mut self, i: u32) {
        let p = self.prev[i as usize];
        let n = self.next[i as usize];
        if p != NIL {
            self.next[p as usize] = n;
        } else {
            self.head = n;
        }
        if n != NIL {
            self.prev[n as usize] = p;
        } else {
            self.tail = p;
        }
    }
}

impl BranchHeuristic for Vmtf {
    fn new_var(&mut self, v: Var) {
        let i = v.index() as u32;
        debug_assert_eq!(i as usize, self.next.len(), "vars added in order");
        self.next.push(NIL);
        self.prev.push(NIL);
        // Strictly-negative, strictly-decreasing creation stamp — see the
        // struct doc comment. Always compares below any bump stamp (which
        // starts at/above 1), and preserves creation order among
        // never-bumped variables.
        self.stamp.push(self.creation_seq);
        self.creation_seq -= 1;
        if self.head == NIL {
            self.head = i;
            self.tail = i;
            self.search = i;
        } else {
            self.next[self.tail as usize] = i;
            self.prev[i as usize] = self.tail;
            self.tail = i;
        }
    }

    fn bump(&mut self, v: Var) {
        let i = v.index() as u32;
        self.counter += 1;
        self.stamp[i as usize] = self.counter;
        if self.head != i {
            self.unlink(i);
            self.next[i as usize] = self.head;
            self.prev[i as usize] = NIL;
            if self.head != NIL {
                self.prev[self.head as usize] = i;
            }
            self.head = i;
            if self.tail == NIL {
                self.tail = i;
            }
        }
        // After bump, this var is at the head with the highest stamp.
        // Reset search to head so next() finds it first.
        self.search = self.head;
    }

    fn decay(&mut self) {
        // VMTF has no decay (move-to-front is the aging mechanism).
    }

    fn on_unassign(&mut self, v: Var) {
        let i = v.index();
        if self.search == NIL || self.stamp[i] > self.stamp[self.search as usize] {
            self.search = i as u32;
        }
    }

    fn next(&mut self, assign: &Assignment) -> Option<Var> {
        let mut i = self.search;
        while i != NIL {
            let v = Var::new(i);
            if assign.value(v) == LBool::Unset {
                self.search = i;
                return Some(v);
            }
            i = self.next[i as usize];
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assignment::Assignment;
    use crate::types::Reason;
    use shinri_core::Lit;

    #[test]
    fn most_recently_bumped_unassigned_var_is_chosen() {
        let mut a = Assignment::new();
        for _ in 0..3 {
            a.new_var();
        }
        let mut h = Vmtf::default();
        for i in 0..3 {
            h.new_var(Var::new(i));
        }
        h.bump(Var::new(2)); // var 2 now highest priority
        assert_eq!(h.next(&a), Some(Var::new(2)));

        // Assign var 2; next() must skip it and fall to the next candidate.
        a.assign(Lit::new(Var::new(2), true), 1, Reason::Decision);
        let n = h.next(&a).unwrap();
        assert!(n == Var::new(0) || n == Var::new(1));

        // Unassigning var 2 makes it the top candidate again.
        a.unassign(Var::new(2));
        h.on_unassign(Var::new(2));
        assert_eq!(h.next(&a), Some(Var::new(2)));
    }

    /// I2 (slice 7) root cause: a NEVER-bumped variable that becomes
    /// unassigned via backtrack must still be found by a later `next()`,
    /// even when `search` currently sits on another never-bumped variable
    /// that was appended AFTER it (and so is closer to head). Before the
    /// fix, every never-bumped variable shared `stamp == 0`, so
    /// `on_unassign`'s `stamp[i] > stamp[search]` comparison never rewound
    /// `search` back over it — the freed, still-unassigned variable became
    /// permanently invisible to `next()`. This silently dropped a variable
    /// from CDCL branching, letting the SAT core report "no more decisions"
    /// (and the theory conclude Sat) while a raw input clause referencing
    /// that variable was still unassigned — the exact shape of the
    /// premature-SAT debug panic at `shinri-sat/src/solver.rs` ("returned
    /// SAT but a clause is unsatisfied").
    #[test]
    fn unassigning_an_earlier_never_bumped_var_is_found_again() {
        let mut a = Assignment::new();
        for _ in 0..3 {
            a.new_var();
        }
        let mut h = Vmtf::default();
        for i in 0..3 {
            h.new_var(Var::new(i)); // tail-appended in order: 0, 1, 2 — none ever bumped.
        }
        // Decide 0 then 1 (in list order); search advances past both to 2.
        a.assign(Lit::new(Var::new(0), true), 1, Reason::Decision);
        assert_eq!(h.next(&a), Some(Var::new(1)));
        a.assign(Lit::new(Var::new(1), true), 1, Reason::Decision);
        assert_eq!(h.next(&a), Some(Var::new(2)));

        // Backtrack unassigns var 0 (a decision made earlier in list order),
        // while `search` sits at 2. Var 0 must be rediscoverable.
        a.unassign(Var::new(0));
        h.on_unassign(Var::new(0));
        let found = h.next(&a);
        assert_eq!(
            found,
            Some(Var::new(0)),
            "a freed never-bumped variable positioned before `search` must not be lost"
        );
    }
}
