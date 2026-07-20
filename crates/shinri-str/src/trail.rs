#[derive(Default)]
pub struct Trail {
    // (eq_true_len, diseq_true_len, memb_true_len, order_true_len, prop_tags_len)
    marks: Vec<(usize, usize, usize, usize, usize)>,
}

impl Trail {
    pub fn push(
        &mut self,
        eq_len: usize,
        diseq_len: usize,
        memb_len: usize,
        order_len: usize,
        prop_len: usize,
    ) {
        self.marks
            .push((eq_len, diseq_len, memb_len, order_len, prop_len));
    }

    /// Current absolute decision level = number of open scopes. (Unchanged
    /// semantics — see the original doc comment.)
    pub fn level(&self) -> u32 {
        self.marks.len() as u32
    }

    /// Returns the (eq, diseq, memb, order, prop) lengths to truncate to for
    /// absolute `target`.
    pub fn pop_to(&mut self, target: usize) -> Option<(usize, usize, usize, usize, usize)> {
        let mut last = None;
        while self.marks.len() > target {
            last = self.marks.pop();
        }
        last
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The propagation-tag length is scoped like every other store: a mark taken
    /// at level N must restore the tag count on pop to N. A leaked tag is a
    /// stale-antecedent wrong-UNSAT (spec §9.1).
    #[test]
    fn pop_restores_prop_tag_length() {
        let mut t = Trail::default();
        t.push(0, 0, 0, 0, 0); // level 1 mark: 0 tags live
        t.push(1, 0, 0, 0, 3); // level 2 mark: 3 tags live
        let restored = t.pop_to(1).expect("popped at least one scope");
        assert_eq!(
            restored.4, 3,
            "pop must report the prop-tag truncation length"
        );
        assert_eq!(t.level(), 1, "one scope remains open");
    }
}
