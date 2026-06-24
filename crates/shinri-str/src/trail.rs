#[derive(Default)]
pub struct Trail {
    marks: Vec<(usize, usize)>, // (eq_true_len, diseq_true_len) at each push
}

impl Trail {
    pub fn push(&mut self, eq_len: usize, diseq_len: usize) {
        self.marks.push((eq_len, diseq_len));
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
