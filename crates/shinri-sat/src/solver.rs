use crate::analyze::Analyzer;
use crate::assignment::Assignment;
use crate::clause::{ClauseDb, ClauseRef};
use crate::config::SolverConfig;
use crate::trail::Trail;
use crate::types::{Conflict, LBool, Reason, SolveResult};
use crate::watch::{Watch, WatchTarget, Watches};
use shinri_core::{Lit, Var};

/// The CDCL search engine (concrete for now; generic params for theory, proof,
/// and heuristic are introduced in Tasks 13/17/18).
pub struct Solver {
    pub(crate) assign: Assignment,
    pub(crate) trail: Trail,
    pub(crate) db: ClauseDb,
    pub(crate) watches: Watches,
    #[allow(dead_code)]
    pub(crate) config: SolverConfig,
    pub(crate) unsat: bool,
    pub(crate) analyzer: Analyzer,
    pub(crate) stats_minimized: u64,
    pub(crate) learnts: Vec<ClauseRef>,
    pub(crate) conflicts: u64,
    pub(crate) stats_deleted: u64,
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
            analyzer: Analyzer::default(),
            stats_minimized: 0,
            learnts: Vec::new(),
            conflicts: 0,
            stats_deleted: 0,
        }
    }

    pub fn new_var(&mut self) -> Var {
        let v = self.assign.new_var();
        self.watches.ensure_vars(self.assign.num_vars());
        self.analyzer.ensure_vars(self.assign.num_vars());
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

    /// Pick an unassigned variable, branching on its saved phase (phase saving).
    /// Task 13 replaces this body with the `BranchHeuristic`.
    fn pick_branch(&self) -> Option<Lit> {
        for i in 0..self.assign.num_vars() {
            let v = Var::new(i as u32);
            if self.assign.value(v) == LBool::Unset {
                return Some(Lit::new(v, self.assign.phase(v)));
            }
        }
        None
    }

    /// Unwind the trail to `level`, un-assigning every popped literal.
    pub(crate) fn backtrack_to(&mut self, level: u32) {
        let assign = &mut self.assign;
        self.trail.backtrack_to(level, |l| assign.unassign(l.var()));
    }

    /// The literal set of a conflict — read from the arena for a stored clause,
    /// or returned directly for a virtual (binary/theory) conflict.
    fn conflict_lits(&self, c: &Conflict) -> Vec<Lit> {
        match c {
            Conflict::Clause(r) => self.db.lits(*r).to_vec(),
            Conflict::Lits(ls) => ls.clone(),
        }
    }

    /// 1-UIP conflict analysis. Returns (learnt clause with the asserting
    /// literal at index 0, backjump level). Assumes the conflict is at the
    /// current decision level > 0.
    pub(crate) fn analyze(&mut self, conflict: Conflict) -> (Vec<Lit>, u32) {
        let level = self.trail.decision_level();
        self.analyzer.learnt.clear();
        self.analyzer.learnt.push(Lit::from_code(0)); // placeholder for asserting lit
        let mut counter = 0u32; // literals at `level` still to resolve
        let mut trail_idx = self.trail.len();
        let mut seen_vars: Vec<Var> = Vec::new();

        // Seed with the conflict clause's literals.
        let mut reason_lits = self.conflict_lits(&conflict);
        loop {
            for &q in &reason_lits {
                let v = q.var();
                if !self.analyzer.seen[v.index()] && self.assign.level(v) > 0 {
                    self.analyzer.seen[v.index()] = true;
                    seen_vars.push(v);
                    if self.assign.level(v) == level {
                        counter += 1;
                    } else {
                        self.analyzer.learnt.push(q);
                    }
                }
            }
            // Find the next trail literal at `level` that we've marked seen.
            loop {
                trail_idx -= 1;
                let p = self.trail.lit_at(trail_idx);
                if self.analyzer.seen[p.var().index()] {
                    break;
                }
            }
            let p = self.trail.lit_at(trail_idx);
            let pv = p.var();
            self.analyzer.seen[pv.index()] = false;
            counter -= 1;
            if counter == 0 {
                // `p` is the first UIP; the asserting literal is its negation.
                self.analyzer.learnt[0] = p.negate();
                break;
            }
            // Resolve on p's reason.
            reason_lits = self.reason_lits_of(p);
        }

        self.minimize();

        // Clear remaining seen marks.
        for v in seen_vars {
            self.analyzer.seen[v.index()] = false;
        }

        // Backjump level = second-highest decision level in the learnt clause.
        let learnt = std::mem::take(&mut self.analyzer.learnt);
        let bt = learnt
            .iter()
            .skip(1)
            .map(|l| self.assign.level(l.var()))
            .max()
            .unwrap_or(0);
        (learnt, bt)
    }

    /// The literals (other than `p` itself) of `p`'s antecedent clause —
    /// i.e. the literals to resolve against when walking the implication graph.
    fn reason_lits_of(&self, p: Lit) -> Vec<Lit> {
        match self.assign.reason(p.var()) {
            Reason::Decision => Vec::new(), // a decision has no antecedent
            Reason::Unit => Vec::new(),
            Reason::Binary(other) => vec![other],
            Reason::Clause(r) => {
                // All literals except `p` (which is satisfied by this clause).
                self.db.lits(r).iter().copied().filter(|&l| l != p).collect()
            }
            Reason::Theory(_just) => Vec::new(), // expanded lazily in Task 17
        }
    }

    /// Install a learnt clause and return its ref (None if it is a unit, which
    /// is asserted at level 0). The asserting literal is `learnt[0]`.
    pub(crate) fn add_learnt(&mut self, learnt: &[Lit]) -> Option<ClauseRef> {
        match learnt.len() {
            0 => None, // empty learnt clause => top-level UNSAT (handled by caller)
            1 => None,
            2 => {
                self.watches.watch_binary(learnt[0], learnt[1]);
                None
            }
            _ => {
                let (_id, r) = self.db.add_clause(learnt, true);
                self.watches.watch_clause(r, learnt[0], learnt[1]);
                self.learnts.push(r);
                Some(r)
            }
        }
    }

    /// Literal Block Distance: the number of distinct decision levels in `lits`.
    fn compute_lbd(&self, lits: &[Lit]) -> u32 {
        let mut levels: Vec<u32> = lits.iter().map(|l| self.assign.level(l.var())).collect();
        levels.sort_unstable();
        levels.dedup();
        levels.len() as u32
    }

    /// A learnt clause is locked iff it is currently the reason of its asserting
    /// literal (`lits[0]`), so deleting it would orphan a trail assignment.
    fn is_locked(&self, r: ClauseRef) -> bool {
        let l0 = self.db.lit_at(r, 0);
        self.assign.value(l0.var()) != LBool::Unset
            && matches!(self.assign.reason(l0.var()), Reason::Clause(rr) if rr == r)
    }

    /// Delete the high-LBD half of the learnt database (lazy deletion), keeping
    /// every clause with glue <= threshold and every locked clause.
    pub(crate) fn reduce(&mut self) {
        let keep_glue = self.config.lbd_keep_threshold;
        let mut refs: Vec<ClauseRef> =
            self.learnts.iter().copied().filter(|&r| !self.db.is_deleted(r)).collect();
        refs.sort_by_key(|&r| self.db.lbd(r));
        let n = refs.len();
        let half = n / 2;
        let mut survivors = Vec::with_capacity(n);
        for (i, r) in refs.iter().copied().enumerate() {
            let in_worst_half = i >= n - half;
            if in_worst_half && self.db.lbd(r) > keep_glue && !self.is_locked(r) {
                self.db.mark_deleted(r);
                self.stats_deleted += 1;
            } else {
                survivors.push(r);
            }
        }
        self.learnts = survivors;
    }

    /// CDCL search with 1-UIP conflict analysis, clause learning, and
    /// non-chronological backjumping.
    pub fn solve(&mut self) -> SolveResult {
        if self.unsat {
            return SolveResult::Unsat { core: vec![] };
        }
        loop {
            match self.propagate() {
                Some(conflict) => {
                    if self.trail.decision_level() == 0 {
                        self.unsat = true;
                        return SolveResult::Unsat { core: vec![] };
                    }
                    let (learnt, bt) = self.analyze(conflict);
                    self.backtrack_to(bt);
                    let asserting = learnt[0];
                    let reason = match self.add_learnt(&learnt) {
                        Some(r) => Reason::Clause(r),
                        None if learnt.len() == 2 => Reason::Binary(learnt[1]),
                        None => Reason::Unit,
                    };
                    self.enqueue(asserting, reason);
                    self.conflicts += 1;
                    let lbd = self.compute_lbd(&learnt);
                    if let Reason::Clause(r) = reason {
                        self.db.set_lbd(r, lbd);
                    }
                    if self.conflicts % self.config.reduce_interval as u64 == 0 {
                        self.reduce();
                    }
                }
                None => match self.pick_branch() {
                    Some(l) => {
                        self.trail.new_level();
                        self.enqueue(l, Reason::Decision);
                    }
                    None => return SolveResult::Sat,
                },
            }
        }
    }

    /// Drop redundant literals from the learnt clause in place. Runs after the
    /// UIP loop, while `seen` still marks the clause's non-asserting literals.
    fn minimize(&mut self) {
        let mut learnt = std::mem::take(&mut self.analyzer.learnt);
        let mut newly_seen: Vec<Var> = Vec::new();
        let mut j = 1;
        for i in 1..learnt.len() {
            let l = learnt[i];
            if !self.lit_redundant(l, &mut newly_seen) {
                learnt[j] = l;
                j += 1;
            }
        }
        self.stats_minimized += (learnt.len() - j) as u64;
        learnt.truncate(j);
        for v in newly_seen {
            self.analyzer.seen[v.index()] = false;
        }
        self.analyzer.learnt = learnt;
    }

    /// True if `l` can be removed: every literal of its reason is already in the
    /// clause (`seen`), at level 0, or itself recursively redundant.
    fn lit_redundant(&mut self, l: Lit, newly_seen: &mut Vec<Var>) -> bool {
        match self.assign.reason(l.var()) {
            Reason::Decision => false,
            Reason::Unit => true,
            Reason::Binary(other) => self.redundant_step(other, newly_seen),
            Reason::Clause(r) => {
                let lits: Vec<Lit> =
                    self.db.lits(r).iter().copied().filter(|&x| x != l).collect();
                for x in lits {
                    if !self.redundant_step(x, newly_seen) {
                        return false;
                    }
                }
                true
            }
            Reason::Theory(_) => false, // don't minimize across theory reasons (Phase 1)
        }
    }

    fn redundant_step(&mut self, x: Lit, newly_seen: &mut Vec<Var>) -> bool {
        let v = x.var();
        if self.analyzer.seen[v.index()] || self.assign.level(v) == 0 {
            return true;
        }
        if matches!(self.assign.reason(v), Reason::Decision) {
            return false;
        }
        if self.lit_redundant(x, newly_seen) {
            self.analyzer.seen[v.index()] = true;
            newly_seen.push(v);
            true
        } else {
            false
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
                        if self.db.is_deleted(r) {
                            continue; // garbage-collect this watch entry
                        }
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

    use crate::types::SolveResult;

    #[test]
    fn cdcl_solves_unsat_pigeon_like() {
        // Same UNSAT 2-SAT as before, now via CDCL: must still be UNSAT.
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        s.add_clause(&[lit(0, true), lit(1, false)]);
        s.add_clause(&[lit(0, false), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, false)]);
        assert_eq!(s.solve(), SolveResult::Unsat { core: vec![] });
    }

    #[test]
    fn cdcl_solves_sat_and_assignment_satisfies() {
        // (x0 ∨ x1 ∨ x2) ∧ (¬x0 ∨ ¬x1) ∧ (¬x1 ∨ ¬x2) ∧ (x1) -> forces a chain.
        let mut s = mk(3);
        s.add_clause(&[lit(0, true), lit(1, true), lit(2, true)]);
        s.add_clause(&[lit(0, false), lit(1, false)]);
        s.add_clause(&[lit(1, false), lit(2, false)]);
        s.add_clause(&[lit(1, true)]);
        assert_eq!(s.solve(), SolveResult::Sat);
        // x1 true => x0 false, x2 false => clause1 needs x0|x1|x2: x1 true ok.
        assert_eq!(s.assign.value(Var::new(1)), LBool::True);
        assert_eq!(s.assign.value(Var::new(0)), LBool::False);
        assert_eq!(s.assign.value(Var::new(2)), LBool::False);
    }

    #[test]
    fn solves_satisfiable_2sat() {
        // (x0 ∨ x1) ∧ (¬x0 ∨ x1)  =>  SAT (x1 = true works).
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, true)]);
        assert_eq!(s.solve(), SolveResult::Sat);
    }

    #[test]
    fn detects_unsatisfiable_2sat() {
        // All four clauses over {x0,x1} => UNSAT.
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        s.add_clause(&[lit(0, true), lit(1, false)]);
        s.add_clause(&[lit(0, false), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, false)]);
        assert_eq!(s.solve(), SolveResult::Unsat { core: vec![] });
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
    fn minimization_field_tracks_removals_and_result_correct() {
        // 4-variable UNSAT core; correctness must hold with minimization on.
        let mut s = mk(4);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(2, true)]);
        s.add_clause(&[lit(1, false), lit(2, true)]);
        s.add_clause(&[lit(2, false), lit(3, true)]);
        s.add_clause(&[lit(2, false), lit(3, false)]);
        let r = s.solve();
        // This instance is UNSAT (x2 is forced true, then x3 must be both true
        // and false); correctness must hold with minimization on.
        assert_eq!(r, SolveResult::Unsat { core: vec![] });
        let _ = s.stats_minimized; // field must exist
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

    #[test]
    fn reduce_deletes_high_lbd_unlocked_learnts() {
        let mut s = mk(6);
        // Install three "learnt" clauses directly with controlled LBD.
        let r_lo = s.add_learnt(&[lit(0, true), lit(1, true), lit(2, true)]).unwrap();
        let r_hi = s.add_learnt(&[lit(3, true), lit(4, true), lit(5, true)]).unwrap();
        s.learnts.push(r_lo);
        s.learnts.push(r_hi);
        s.db.set_lbd(r_lo, 2); // glue, protected (<= threshold 2)
        s.db.set_lbd(r_hi, 9); // high glue, deletable
        s.reduce();
        assert!(!s.db.is_deleted(r_lo), "low-LBD clause kept");
        assert!(s.db.is_deleted(r_hi), "high-LBD clause deleted");
        assert!(s.stats_deleted >= 1);
    }
}
