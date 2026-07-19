#[derive(Default)]
pub struct Trail {
    // (eq_true_len, diseq_true_len, memb_true_len, order_true_len)
    marks: Vec<(usize, usize, usize, usize)>,
}

impl Trail {
    pub fn push(&mut self, eq_len: usize, diseq_len: usize, memb_len: usize, order_len: usize) {
        self.marks.push((eq_len, diseq_len, memb_len, order_len));
    }

    /// Current absolute decision level = number of open scopes. (Unchanged
    /// semantics — see the original doc comment.)
    pub fn level(&self) -> u32 {
        self.marks.len() as u32
    }

    /// Returns the (eq, diseq, memb, order) lengths to truncate to for absolute
    /// `target`.
    pub fn pop_to(&mut self, target: usize) -> Option<(usize, usize, usize, usize)> {
        let mut last = None;
        while self.marks.len() > target {
            last = self.marks.pop();
        }
        last
    }
}
