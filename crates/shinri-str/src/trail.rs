#[derive(Default)]
pub struct Trail {
    marks: Vec<(usize, usize)>, // (eq_true_len, diseq_true_len) at each push
}

impl Trail {
    pub fn push(&mut self, eq_len: usize, diseq_len: usize) {
        self.marks.push((eq_len, diseq_len));
    }

    /// Current absolute decision level = number of open scopes. `push` is called
    /// once per SAT decision level, so this mirrors the SAT trail's decision level.
    /// A (dis)equality asserted while this returns 0 is UNCONDITIONALLY entailed
    /// (a top-level fact); one asserted at level > 0 is only CONDITIONALLY active
    /// (selected inside some disjunction at a decision).
    pub fn level(&self) -> u32 {
        self.marks.len() as u32
    }

    /// Returns the (eq_true_len, diseq_true_len) to truncate to for absolute `target` level.
    pub fn pop_to(&mut self, target: usize) -> Option<(usize, usize)> {
        let mut last = None;
        while self.marks.len() > target {
            last = self.marks.pop();
        }
        last
    }
}
