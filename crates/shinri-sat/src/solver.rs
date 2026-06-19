use crate::assignment::Assignment;
use crate::clause::ClauseDb;
use crate::config::SolverConfig;
use crate::trail::Trail;
use crate::types::{Conflict, LBool, Reason};
use crate::watch::{Watch, WatchTarget, Watches};
use shinri_core::{Lit, Var};

/// The CDCL search engine (concrete for now; generic params for theory, proof,
/// and heuristic are introduced in Tasks 13/17/18).
#[allow(dead_code)]
pub struct Solver {
    pub(crate) assign: Assignment,
    pub(crate) trail: Trail,
    pub(crate) db: ClauseDb,
    pub(crate) watches: Watches,
    pub(crate) config: SolverConfig,
    pub(crate) unsat: bool,
}

impl Solver {
    pub fn new(config: SolverConfig) -> Solver {
        Solver {
            assign: Assignment::new(),
            trail: Trail::new(),
            db: ClauseDb::new(),
            watches: Watches::new(),
            config,
            unsat: false,
        }
    }

    pub fn new_var(&mut self) -> Var {
        let v = self.assign.new_var();
        self.watches.ensure_vars(self.assign.num_vars());
        v
    }

    #[inline]
    pub fn is_unsat(&self) -> bool {
        self.unsat
    }

    /// Add an input clause at decision level 0. Returns false iff the formula
    /// is now trivially UNSAT (empty clause or a conflicting unit).
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        debug_assert_eq!(self.trail.decision_level(), 0, "add_clause only at level 0");
        match lits.len() {
            0 => {
                self.unsat = true;
                false
            }
            1 => {
                if self.enqueue(lits[0], Reason::Unit) {
                    true
                } else {
                    self.unsat = true;
                    false
                }
            }
            2 => {
                self.watches.watch_binary(lits[0], lits[1]);
                true
            }
            _ => {
                let (_id, r) = self.db.add_clause(lits, false);
                self.watches.watch_clause(r, lits[0], lits[1]);
                true
            }
        }
    }

    /// Try to make `l` true. Returns false if `l` is already false (a conflict).
    #[inline]
    pub fn enqueue(&mut self, l: Lit, reason: Reason) -> bool {
        match self.assign.lit_value(l) {
            LBool::True => true,
            LBool::False => false,
            LBool::Unset => {
                let level = self.trail.decision_level();
                self.assign.assign(l, level, reason);
                self.trail.push(l);
                true
            }
        }
    }

    /// Boolean constraint propagation to fixpoint. Returns the first conflict,
    /// or `None` if a fixpoint with no conflict is reached.
    pub fn propagate(&mut self) -> Option<Conflict> {
        while self.trail.qhead() < self.trail.len() {
            let p = self.trail.lit_at(self.trail.qhead());
            self.trail.set_qhead(self.trail.qhead() + 1);
            let false_lit = p.negate();

            // Inspect clauses watching `false_lit` (filed under `p`). Take the
            // list out so we can re-file moved watches into other lists.
            let watchers = std::mem::take(self.watches.list_mut(p));
            let mut keep: Vec<Watch> = Vec::with_capacity(watchers.len());
            let mut conflict: Option<Conflict> = None;
            let mut idx = 0;

            'watch: while idx < watchers.len() {
                let w = watchers[idx];
                idx += 1;

                // Blocker already satisfied => clause is true, keep untouched.
                if self.assign.lit_value(w.blocker) == LBool::True {
                    keep.push(w);
                    continue;
                }

                match w.target {
                    WatchTarget::Binary => {
                        keep.push(w);
                        match self.assign.lit_value(w.blocker) {
                            LBool::Unset => {
                                self.enqueue(w.blocker, Reason::Binary(false_lit));
                            }
                            LBool::False => {
                                conflict = Some(Conflict::Lits(vec![false_lit, w.blocker]));
                                break 'watch;
                            }
                            LBool::True => {}
                        }
                    }
                    WatchTarget::Clause(r) => {
                        // Keep watched lits at slots 0,1; put the false lit at 1.
                        if self.db.lit_at(r, 0) == false_lit {
                            self.db.swap_lits(r, 0, 1);
                        }
                        let other = self.db.lit_at(r, 0);
                        if other != w.blocker && self.assign.lit_value(other) == LBool::True {
                            keep.push(Watch { target: WatchTarget::Clause(r), blocker: other });
                            continue;
                        }
                        // Look for a replacement watch among slots 2..len.
                        let len = self.db.len_of(r);
                        let mut found = false;
                        for k in 2..len {
                            let lk = self.db.lit_at(r, k);
                            if self.assign.lit_value(lk) != LBool::False {
                                self.db.swap_lits(r, 1, k);
                                self.watches.list_mut(lk.negate()).push(Watch {
                                    target: WatchTarget::Clause(r),
                                    blocker: other,
                                });
                                found = true;
                                break;
                            }
                        }
                        if found {
                            continue; // clause leaves p's list
                        }
                        // No replacement: clause is unit (or conflicting) on `other`.
                        keep.push(Watch { target: WatchTarget::Clause(r), blocker: other });
                        match self.assign.lit_value(other) {
                            LBool::Unset => {
                                self.enqueue(other, Reason::Clause(r));
                            }
                            LBool::False => {
                                conflict = Some(Conflict::Clause(r));
                                break 'watch;
                            }
                            LBool::True => {}
                        }
                    }
                }
            }

            // Preserve any watchers not yet visited (after a conflict break).
            while idx < watchers.len() {
                keep.push(watchers[idx]);
                idx += 1;
            }
            *self.watches.list_mut(p) = keep;

            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(n: u32, pos: bool) -> Lit {
        Lit::new(Var::new(n), pos)
    }

    fn mk(n_vars: u32) -> Solver {
        let mut s = Solver::new(SolverConfig::default());
        for _ in 0..n_vars {
            s.new_var();
        }
        s
    }

    #[test]
    fn unit_then_binary_chain_propagates() {
        // (x0) , (¬x0 ∨ x1) , (¬x1 ∨ x2)  =>  x0,x1,x2 all true.
        let mut s = mk(3);
        assert!(s.add_clause(&[lit(0, true)]));
        assert!(s.add_clause(&[lit(0, false), lit(1, true)]));
        assert!(s.add_clause(&[lit(1, false), lit(2, true)]));
        assert!(s.propagate().is_none());
        assert_eq!(s.assign.value(Var::new(0)), LBool::True);
        assert_eq!(s.assign.value(Var::new(1)), LBool::True);
        assert_eq!(s.assign.value(Var::new(2)), LBool::True);
    }

    #[test]
    fn long_clause_becomes_unit_and_conflicts() {
        // Force all but one literal false in a ternary clause, then falsify it.
        // Clauses: (x0), (x1), (¬x0 ∨ ¬x1 ∨ x2), (¬x2)
        let mut s = mk(3);
        s.add_clause(&[lit(0, true)]);
        s.add_clause(&[lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, false), lit(2, true)]);
        s.add_clause(&[lit(2, false)]);
        // x0,x1 true => ternary forces x2 true; (¬x2) unit forces x2 false => conflict.
        let c = s.propagate();
        assert!(c.is_some(), "expected a conflict");
    }
}
