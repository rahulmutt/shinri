use crate::assignment::Assignment;
use crate::types::LBool;
use shinri_core::Var;

use super::BranchHeuristic;

/// Exponential VSIDS: float activities with an indexed binary max-heap of
/// unassigned candidates. `var_inc` grows each conflict (the "exponential"
/// trick that avoids decaying every variable); rescale keeps it finite.
pub struct Evsids {
    activity: Vec<f64>,
    heap: Vec<u32>,    // binary max-heap of var indices
    pos: Vec<i32>,     // pos[v] = index in `heap`, or -1 if absent
    var_inc: f64,
    var_decay: f64,
}

impl Default for Evsids {
    fn default() -> Self {
        Evsids {
            activity: Vec::new(),
            heap: Vec::new(),
            pos: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.95,
        }
    }
}

impl Evsids {
    #[inline]
    fn higher(&self, a: u32, b: u32) -> bool {
        self.activity[a as usize] > self.activity[b as usize]
    }

    fn sift_up(&mut self, mut i: usize) {
        let x = self.heap[i];
        while i > 0 {
            let parent = (i - 1) / 2;
            if self.higher(x, self.heap[parent]) {
                self.heap[i] = self.heap[parent];
                self.pos[self.heap[i] as usize] = i as i32;
                i = parent;
            } else {
                break;
            }
        }
        self.heap[i] = x;
        self.pos[x as usize] = i as i32;
    }

    fn sift_down(&mut self, mut i: usize) {
        let x = self.heap[i];
        let n = self.heap.len();
        loop {
            let l = 2 * i + 1;
            if l >= n {
                break;
            }
            let r = l + 1;
            let child = if r < n && self.higher(self.heap[r], self.heap[l]) { r } else { l };
            if self.higher(self.heap[child], x) {
                self.heap[i] = self.heap[child];
                self.pos[self.heap[i] as usize] = i as i32;
                i = child;
            } else {
                break;
            }
        }
        self.heap[i] = x;
        self.pos[x as usize] = i as i32;
    }

    fn heap_insert(&mut self, v: u32) {
        if self.pos[v as usize] >= 0 {
            return;
        }
        self.heap.push(v);
        let i = self.heap.len() - 1;
        self.pos[v as usize] = i as i32;
        self.sift_up(i);
    }

    fn heap_pop(&mut self) -> Option<u32> {
        if self.heap.is_empty() {
            return None;
        }
        let top = self.heap[0];
        let last = *self.heap.last().unwrap();
        self.heap[0] = last;
        self.pos[last as usize] = 0;
        self.heap.pop();
        self.pos[top as usize] = -1;
        if !self.heap.is_empty() {
            self.sift_down(0);
        }
        Some(top)
    }
}

impl BranchHeuristic for Evsids {
    fn new_var(&mut self, v: Var) {
        debug_assert_eq!(v.index(), self.activity.len(), "vars added in order");
        self.activity.push(0.0);
        self.pos.push(-1);
        self.heap_insert(v.index() as u32);
    }

    fn bump(&mut self, v: Var) {
        let i = v.index();
        self.activity[i] += self.var_inc;
        if self.activity[i] > 1e100 {
            for a in &mut self.activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        if self.pos[i] >= 0 {
            self.sift_up(self.pos[i] as usize);
        }
    }

    fn decay(&mut self) {
        self.var_inc /= self.var_decay;
    }

    fn on_unassign(&mut self, v: Var) {
        self.heap_insert(v.index() as u32);
    }

    fn next(&mut self, assign: &Assignment) -> Option<Var> {
        while let Some(top) = self.heap_pop() {
            let v = Var::new(top);
            if assign.value(v) == LBool::Unset {
                // Re-insert so it can be chosen again after backtrack.
                self.heap_insert(top);
                return Some(v);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assignment::Assignment;
    use crate::heuristic::BranchHeuristic;
    use crate::types::Reason;
    use shinri_core::{Lit, Var};

    #[test]
    fn highest_activity_unassigned_var_chosen_and_reinserted() {
        let mut a = Assignment::new();
        for _ in 0..3 {
            a.new_var();
        }
        let mut h = Evsids::default();
        for i in 0..3 {
            h.new_var(Var::new(i));
        }
        h.bump(Var::new(1));
        h.bump(Var::new(1)); // var 1 most active
        assert_eq!(h.next(&a), Some(Var::new(1)));

        a.assign(Lit::new(Var::new(1), true), 1, Reason::Decision);
        let n = h.next(&a).unwrap();
        assert!(n != Var::new(1));

        a.unassign(Var::new(1));
        h.on_unassign(Var::new(1));
        assert_eq!(h.next(&a), Some(Var::new(1)));
    }
}
