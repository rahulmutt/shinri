//! Dense interning of arithmetic variables: problem variables (by TermId) and
//! slack variables (by canonical LinComb). Append-only across a solve.

use crate::normalize::LinComb;
use rustc_hash::FxHashMap;
use shinri_core::TermId;

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ArithVar(pub u32);

impl ArithVar {
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Default, Debug)]
pub struct VarStore {
    by_term: FxHashMap<TermId, ArithVar>,
    by_comb: FxHashMap<LinComb, ArithVar>,
    term_of: Vec<Option<TermId>>,
    is_slack: Vec<bool>,
    is_int: Vec<bool>,
}

impl VarStore {
    fn fresh(&mut self, term: Option<TermId>, slack: bool, is_int: bool) -> ArithVar {
        let v = ArithVar(self.term_of.len() as u32);
        self.term_of.push(term);
        self.is_slack.push(slack);
        self.is_int.push(is_int);
        v
    }

    pub fn problem_var(&mut self, t: TermId) -> ArithVar {
        if let Some(&v) = self.by_term.get(&t) {
            return v;
        }
        let v = self.fresh(Some(t), false, false);
        self.by_term.insert(t, v);
        v
    }

    pub fn problem_var_sorted(&mut self, t: TermId, is_int: bool) -> ArithVar {
        if let Some(&v) = self.by_term.get(&t) {
            return v;
        }
        let v = self.fresh(Some(t), false, is_int);
        self.by_term.insert(t, v);
        v
    }

    pub fn slack_var(&mut self, comb: &LinComb) -> ArithVar {
        if let Some(&v) = self.by_comb.get(comb) {
            return v;
        }
        let v = self.fresh(None, true, false);
        self.by_comb.insert(comb.clone(), v);
        v
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.term_of.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.term_of.is_empty()
    }

    #[inline]
    pub fn is_slack(&self, v: ArithVar) -> bool {
        self.is_slack[v.index()]
    }

    #[inline]
    pub fn is_int(&self, v: ArithVar) -> bool {
        self.is_int[v.index()]
    }

    pub fn mark_int(&mut self, v: ArithVar) {
        self.is_int[v.index()] = true;
    }

    #[inline]
    pub fn term_of(&self, v: ArithVar) -> Option<TermId> {
        self.term_of[v.index()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::normalize::LinComb;
    use shinri_num::Rational;

    #[test]
    fn problem_var_records_int_sortedness() {
        let mut s = VarStore::default();
        let ti = TermId::new(1).unwrap();
        let tr = TermId::new(2).unwrap();
        let xi = s.problem_var_sorted(ti, true);
        let xr = s.problem_var_sorted(tr, false);
        assert!(s.is_int(xi));
        assert!(!s.is_int(xr));
        // Re-interning the same term returns the same var, keeps its flag.
        assert_eq!(s.problem_var_sorted(ti, true), xi);
        assert!(s.is_int(xi));
        // Slacks are never int.
        let comb = LinComb(vec![(xi, Rational::one()), (xr, Rational::one())]);
        let sl = s.slack_var(&comb);
        assert!(!s.is_int(sl));
    }

    #[test]
    fn problem_and_slack_vars_intern_by_identity() {
        let mut s = VarStore::default();
        // TermId is 1-based (NonZeroU32): new(0) returns None.
        let t0 = TermId::new(1).unwrap();
        let t1 = TermId::new(2).unwrap();
        let a = s.problem_var(t0);
        let b = s.problem_var(t0); // same term → same var
        let c = s.problem_var(t1);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert!(!s.is_slack(a));

        let comb = LinComb(vec![(a, Rational::one()), (c, Rational::one())]);
        let s1 = s.slack_var(&comb);
        let s2 = s.slack_var(&comb); // same comb → same slack
        assert_eq!(s1, s2);
        assert!(s.is_slack(s1));
        assert_eq!(s.term_of(s1), None);
    }
}
