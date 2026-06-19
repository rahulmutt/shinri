use crate::assignment::Assignment;
use crate::heuristic::BranchHeuristic;
use crate::types::LBool;
use shinri_core::Var;

const NIL: u32 = u32::MAX;

/// Variable Move-To-Front: a doubly-linked priority list over variables. The
/// most-recently-bumped variable is at the head; `next` walks from a `search`
/// pointer (kept at-or-before the highest-priority unassigned var). Integer
/// stamps only — fully deterministic.
pub struct Vmtf {
    next: Vec<u32>,
    prev: Vec<u32>,
    stamp: Vec<u64>,
    head: u32,
    tail: u32,
    search: u32,
    counter: u64,
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
        self.stamp.push(0);
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
}
