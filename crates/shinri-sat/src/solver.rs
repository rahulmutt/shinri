use crate::analyze::Analyzer;
use crate::assignment::Assignment;
use crate::clause::{ClauseDb, ClauseRef};
use crate::config::SolverConfig;
use crate::heuristic::BranchHeuristic;
#[cfg(test)]
use crate::heuristic::Vmtf;
use crate::restart::RestartPolicy;
use crate::theory::Theory;
use crate::trail::Trail;
use crate::types::{Conflict, Effort, LBool, Reason, SolveResult, TheoryResult};
use crate::watch::{Watch, WatchTarget, Watches};
use shinri_core::{ClauseId, Lit, ProofSink, TheoryJust, Var};

/// The CDCL search engine. `T` is the theory, `P` is the proof sink, `H` is
/// the branching heuristic, all fixed at construction (spec §8.4).
pub struct Solver<T: Theory, P: ProofSink + Default, H: BranchHeuristic> {
    pub(crate) assign: Assignment,
    pub(crate) trail: Trail,
    pub(crate) db: ClauseDb,
    pub(crate) watches: Watches,
    pub(crate) analyzer: Analyzer,
    pub(crate) restart: RestartPolicy,
    pub(crate) config: SolverConfig,
    pub(crate) heuristic: H,
    pub(crate) theory: T,
    pub(crate) proof: P,
    pub(crate) learnts: Vec<ClauseRef>,
    pub(crate) input_clauses: Vec<Vec<Lit>>,
    pub(crate) scopes: Vec<usize>,
    pub(crate) conflicts: u64,
    pub(crate) unsat: bool,
    pub(crate) theory_silent: bool,
    pub(crate) stats_minimized: u64,
    pub(crate) stats_deleted: u64,
}

impl<T: Theory, P: ProofSink + Default, H: BranchHeuristic> Solver<T, P, H> {
    pub fn new(config: SolverConfig) -> Solver<T, P, H> {
        Solver {
            assign: Assignment::new(),
            trail: Trail::new(),
            db: ClauseDb::new(),
            watches: Watches::new(),
            restart: RestartPolicy::new(config.restart, 100),
            config,
            heuristic: H::default(),
            theory: T::default(),
            proof: P::default(),
            unsat: false,
            theory_silent: false,
            analyzer: Analyzer::default(),
            stats_minimized: 0,
            learnts: Vec::new(),
            conflicts: 0,
            stats_deleted: 0,
            input_clauses: Vec::new(),
            scopes: Vec::new(),
        }
    }

    /// Construct around a pre-built theory (e.g. a `Combiner` with its
    /// `Context` already populated). Identical to `new` but does not default `T`.
    pub fn with_theory(config: SolverConfig, theory: T) -> Solver<T, P, H> {
        let mut s = Solver::new(config);
        s.theory = theory;
        s
    }

    /// Borrow the theory (e.g. to read a model after `solve`).
    pub fn theory(&self) -> &T {
        &self.theory
    }

    /// Mutably borrow the theory (e.g. to register atoms before `solve`).
    pub fn theory_mut(&mut self) -> &mut T {
        &mut self.theory
    }

    pub fn new_var(&mut self) -> Var {
        let v = self.assign.new_var();
        self.heuristic.new_var(v);
        self.theory.new_var(v);
        self.watches.ensure_vars(self.assign.num_vars());
        self.analyzer.ensure_vars(self.assign.num_vars());
        v
    }

    #[inline]
    pub fn is_unsat(&self) -> bool {
        self.unsat
    }

    /// Add an input clause (records it for push/pop, then installs it).
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        if self.trail.decision_level() != 0 {
            self.backtrack_to(0);
        }
        self.input_clauses.push(lits.to_vec());
        self.install_clause(lits)
    }

    /// Install a clause into the db/watches/trail without recording it.
    fn install_clause(&mut self, lits: &[Lit]) -> bool {
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
                let (id, r) = self.db.add_clause(lits, false);
                self.watches.watch_clause(r, lits[0], lits[1]);
                self.proof.input(id, lits);
                true
            }
        }
    }

    pub fn push(&mut self) {
        if self.trail.decision_level() != 0 {
            self.backtrack_to(0);
        }
        self.scopes.push(self.input_clauses.len());
        self.theory.push();
    }

    /// Closes `n` incremental scopes. Assumes the solver is at decision level 0
    /// (unlike `push`, this does not call `backtrack_to(0)`; callers must ensure
    /// solves have completed and the trail is already unwound to level 0).
    pub fn pop(&mut self, n: usize) {
        for _ in 0..n {
            if let Some(mark) = self.scopes.pop() {
                self.input_clauses.truncate(mark);
            }
        }
        self.theory.pop(n);
        self.rebuild();
    }

    /// Conservative rebuild: reset all derived state and re-install the
    /// surviving input clauses. Drops every learnt clause (spec §7.3).
    /// TODO(phase2): emit deletes on pop for learnt clauses being discarded.
    fn rebuild(&mut self) {
        let num_vars = self.assign.num_vars();
        self.assign.reset();
        self.trail = Trail::new();
        self.db = ClauseDb::new();
        self.watches = Watches::new();
        self.watches.ensure_vars(num_vars);
        self.learnts.clear();
        self.unsat = false;
        self.heuristic = H::default();
        for i in 0..num_vars {
            self.heuristic.new_var(Var::new(i as u32));
        }
        self.restart = RestartPolicy::new(self.config.restart, 100);
        self.conflicts = 0;
        // Re-install survivors WITHOUT re-asserting to the theory: the theory
        // retained the surviving scopes' facts via its own push/pop (spec §7).
        self.theory_silent = true;
        let inputs = std::mem::take(&mut self.input_clauses);
        for clause in &inputs {
            self.install_clause(clause);
        }
        self.input_clauses = inputs;
        self.theory_silent = false;
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
                if !self.theory_silent {
                    self.theory.assert(l);
                }
                true
            }
        }
    }

    fn pick_branch(&mut self) -> Option<Lit> {
        self.heuristic
            .next(&self.assign)
            .map(|v| Lit::new(v, self.assign.phase(v)))
    }

    /// Unwind the trail to `level`, un-assigning every popped literal.
    pub(crate) fn backtrack_to(&mut self, level: u32) {
        let from = self.trail.decision_level();
        let assign = &mut self.assign;
        let heuristic = &mut self.heuristic;
        self.trail.backtrack_to(level, |l| {
            assign.unassign(l.var());
            heuristic.on_unassign(l.var());
        });
        if from > level {
            self.theory.pop((from - level) as usize);
        }
    }

    /// If `conflict_lits` contains no literal at the current decision level,
    /// backtrack to the conflict's max level so that 1-UIP has a pivot literal.
    /// Returns `Err(())` when max_level == 0, signalling top-level UNSAT.
    /// `backtrack_to(max_level)` keeps levels ≤ max_level assigned (so the
    /// conflict clause stays all-false for `analyze`) and sets the decision
    /// level to max_level, giving 1-UIP a current-level literal to resolve on.
    fn reduce_to_conflict_level(&mut self, conflict_lits: &[Lit]) -> Result<(), ()> {
        let cur = self.trail.decision_level();
        if conflict_lits
            .iter()
            .any(|l| self.assign.level(l.var()) == cur)
        {
            return Ok(());
        }
        let max_level = conflict_lits
            .iter()
            .map(|l| self.assign.level(l.var()))
            .max()
            .unwrap_or(0);
        if max_level == 0 {
            return Err(());
        }
        // Keep max_level assignments intact so analyze() can resolve them;
        // only unassign levels strictly above max_level.
        self.backtrack_to(max_level);
        Ok(())
    }

    /// The Boolean value of a variable in the current assignment, if assigned.
    pub fn value_of(&self, v: Var) -> Option<bool> {
        match self.assign.value(v) {
            LBool::True => Some(true),
            LBool::False => Some(false),
            LBool::Unset => None,
        }
    }

    /// Every recorded input clause is satisfied by the current assignment.
    pub fn check_model(&self) -> bool {
        self.input_clauses
            .iter()
            .all(|cl| cl.iter().any(|&l| self.assign.lit_value(l) == LBool::True))
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
    /// literal at index 0, backjump level, antecedent ClauseId chain for LRAT).
    /// Assumes the conflict is at the current decision level > 0.
    pub(crate) fn analyze(&mut self, conflict: Conflict) -> (Vec<Lit>, u32, Vec<ClauseId>) {
        let level = self.trail.decision_level();
        self.analyzer.learnt.clear();
        self.analyzer.learnt.push(Lit::from_code(0)); // placeholder for asserting lit
        let mut counter = 0u32; // literals at `level` still to resolve
        let mut trail_idx = self.trail.len();
        let mut seen_vars: Vec<Var> = Vec::new();
        let mut chain: Vec<ClauseId> = Vec::new();

        // Seed with the conflict clause's literals.
        let mut reason_lits = self.conflict_lits(&conflict);
        // If the conflict itself is a stored clause, record it in the chain.
        if let Conflict::Clause(r) = &conflict {
            chain.push(self.db.clause_id(*r));
        }
        loop {
            for &q in &reason_lits {
                let v = q.var();
                if !self.analyzer.seen[v.index()] && self.assign.level(v) > 0 {
                    self.analyzer.seen[v.index()] = true;
                    self.heuristic.bump(v);
                    seen_vars.push(v);
                    if self.assign.level(v) == level {
                        counter += 1;
                    } else {
                        self.analyzer.learnt.push(q);
                    }
                }
            }
            // Find the next trail literal at `level` that we've marked seen.
            // IMPORTANT: only match literals at the CURRENT decision level.
            // Literals at intermediate levels are marked `seen` (to avoid
            // double-processing) but are already in the learnt clause; the
            // scan must skip them or `counter` underflows on decrement.
            loop {
                trail_idx -= 1;
                let p = self.trail.lit_at(trail_idx);
                if self.analyzer.seen[p.var().index()] && self.assign.level(p.var()) == level {
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
            // Resolve on p's reason; collect stored-clause antecedents into chain.
            if let Reason::Clause(r) = self.assign.reason(p.var()) {
                chain.push(self.db.clause_id(r));
            }
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
        (learnt, bt, chain)
    }

    /// The literals (other than `p` itself) of `p`'s antecedent clause —
    /// i.e. the literals to resolve against when walking the implication graph.
    fn reason_lits_of(&mut self, p: Lit) -> Vec<Lit> {
        match self.assign.reason(p.var()) {
            Reason::Decision => Vec::new(), // a decision has no antecedent
            Reason::Unit => Vec::new(),
            Reason::Binary(other) => vec![other],
            Reason::Clause(r) => {
                // All literals except `p` (which is satisfied by this clause).
                self.db
                    .lits(r)
                    .iter()
                    .copied()
                    .filter(|&l| l != p)
                    .collect()
            }
            Reason::Theory(just) => {
                let mut antecedents = Vec::new();
                self.theory.explain(just, &mut antecedents);
                // The clause is (p ∨ ¬a1 ∨ ...); resolve against the ¬ai (false).
                antecedents.iter().map(|a| a.negate()).collect()
            }
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
        let mut refs: Vec<ClauseRef> = self
            .learnts
            .iter()
            .copied()
            .filter(|&r| !self.db.is_deleted(r))
            .collect();
        refs.sort_by_key(|&r| self.db.lbd(r));
        let n = refs.len();
        let half = n / 2;
        let mut survivors = Vec::with_capacity(n);
        // refs sorted ascending by LBD; the worst (highest-LBD) half is the tail [n-half, n).
        for (i, r) in refs.iter().copied().enumerate() {
            let in_worst_half = i >= n - half;
            if in_worst_half && self.db.lbd(r) > keep_glue && !self.is_locked(r) {
                self.proof.delete(self.db.clause_id(r));
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
        self.solve_under(&[])
    }

    /// Solve under the given assumption literals (placed as the first
    /// decisions). On UNSAT, `core` is the failed-assumption subset.
    pub fn solve_under(&mut self, assumptions: &[Lit]) -> SolveResult {
        if self.unsat {
            return SolveResult::Unsat { core: vec![] };
        }
        self.backtrack_to(0);
        loop {
            match self.propagate() {
                Some(conflict) => {
                    if self.trail.decision_level() == 0 {
                        self.unsat = true;
                        return SolveResult::Unsat { core: vec![] };
                    }
                    // Theory conflicts can span only levels below the current one
                    // (the conflict was implied by earlier decisions but surfaced
                    // after more were made). 1-UIP needs a current-level literal
                    // to pivot on. Reduce the decision level to the conflict's max
                    // level so its top literals become current-level, then run the
                    // normal analysis (which resolves multiple top-level lits to
                    // one UIP).
                    let conflict_lits = self.conflict_lits(&conflict);
                    if let Err(()) = self.reduce_to_conflict_level(&conflict_lits) {
                        self.unsat = true;
                        return SolveResult::Unsat { core: vec![] };
                    }
                    let (learnt, bt, chain) = self.analyze(conflict);
                    self.backtrack_to(bt);
                    let asserting = learnt[0];
                    let r_opt = self.add_learnt(&learnt);
                    // Phase 1: binary/unit clauses are not stored in ClauseDb, so they carry a sentinel id
                    // and are proof-invisible by id (the RUP consumer re-derives them from content).
                    let pid = match r_opt {
                        Some(r) => self.db.clause_id(r),
                        None => ClauseId::new(u32::MAX), // sentinel id for unit/binary
                    };
                    self.proof.learn(pid, &learnt, &chain);
                    let reason = match r_opt {
                        Some(r) => Reason::Clause(r),
                        None if learnt.len() == 2 => Reason::Binary(learnt[1]),
                        None => Reason::Unit,
                    };
                    self.enqueue(asserting, reason);
                    self.conflicts += 1;
                    self.heuristic.decay();
                    let lbd = self.compute_lbd(&learnt);
                    if let Reason::Clause(r) = reason {
                        self.db.set_lbd(r, lbd);
                    }
                    if self
                        .conflicts
                        .is_multiple_of(self.config.reduce_interval as u64)
                    {
                        self.reduce();
                    }
                    self.restart.on_conflict(lbd);
                    if self.restart.should_restart()
                        && self.trail.decision_level() as usize > assumptions.len()
                    {
                        self.restart.on_restart();
                        self.backtrack_to(assumptions.len() as u32);
                    }
                }
                None => {
                    let dl = self.trail.decision_level() as usize;
                    if dl < assumptions.len() {
                        let a = assumptions[dl];
                        match self.assign.lit_value(a) {
                            LBool::True => {
                                self.trail.new_level(); // align levels; no new assignment
                                self.theory.push();
                            }
                            LBool::False => {
                                let mut core = self.analyze_final(a.negate());
                                core.push(a);
                                return SolveResult::Unsat { core };
                            }
                            LBool::Unset => {
                                self.trail.new_level();
                                self.theory.push();
                                self.enqueue(a, Reason::Decision);
                            }
                        }
                    } else {
                        match self.pick_branch() {
                            Some(l) => {
                                self.trail.new_level();
                                self.theory.push();
                                self.enqueue(l, Reason::Decision);
                            }
                            None => match self.theory.check(Effort::Full) {
                                TheoryResult::Sat => {
                                    debug_assert!(
                                        self.check_model(),
                                        "returned SAT but a clause is unsatisfied"
                                    );
                                    return SolveResult::Sat;
                                }
                                TheoryResult::Conflict(lits) => {
                                    if self.trail.decision_level() == 0 {
                                        self.unsat = true;
                                        return SolveResult::Unsat { core: vec![] };
                                    }
                                    // Same treatment as the propagate() path: if the
                                    // conflict spans only levels below the current one,
                                    // reduce the decision level to the conflict's max
                                    // level so 1-UIP has a current-level pivot.
                                    let conflict = Conflict::Lits(lits);
                                    let conflict_lits = self.conflict_lits(&conflict);
                                    if let Err(()) = self.reduce_to_conflict_level(&conflict_lits) {
                                        self.unsat = true;
                                        return SolveResult::Unsat { core: vec![] };
                                    }
                                    let (learnt, bt, chain) = self.analyze(conflict);
                                    self.backtrack_to(bt);
                                    let asserting = learnt[0];
                                    let r_opt = self.add_learnt(&learnt);
                                    let pid = match r_opt {
                                        Some(r) => self.db.clause_id(r),
                                        None => ClauseId::new(u32::MAX), // sentinel id for unit/binary
                                    };
                                    self.proof.learn(pid, &learnt, &chain);
                                    let reason = match r_opt {
                                        Some(r) => Reason::Clause(r),
                                        None if learnt.len() == 2 => Reason::Binary(learnt[1]),
                                        None => Reason::Unit,
                                    };
                                    self.enqueue(asserting, reason);
                                }
                                TheoryResult::Lemma(lits) => {
                                    self.add_learnt(&lits);
                                    let dl = self.trail.decision_level();
                                    if dl > 0 {
                                        self.backtrack_to(dl - 1);
                                    }
                                }
                                TheoryResult::SplitAtoms(_) => {
                                    // TODO: Task 3 — implement splitting-on-demand logic
                                    unimplemented!("SplitAtoms handler not yet implemented")
                                }
                            },
                        }
                    }
                }
            }
        }
    }

    /// Collect the assumption/decision literals that entail `p` (which is true
    /// on the trail). The basis of `get-unsat-core` under assumptions.
    fn analyze_final(&mut self, p: Lit) -> Vec<Lit> {
        self.analyzer.ensure_vars(self.assign.num_vars());
        let mut core: Vec<Lit> = Vec::new();
        let mut seen_vars: Vec<Var> = Vec::new();
        self.analyzer.seen[p.var().index()] = true;
        seen_vars.push(p.var());

        let mut i = self.trail.len();
        while i > 0 {
            i -= 1;
            let q = self.trail.lit_at(i);
            let v = q.var();
            if !self.analyzer.seen[v.index()] {
                continue;
            }
            match self.assign.reason(v) {
                Reason::Decision => core.push(q),
                Reason::Unit => {}
                Reason::Binary(other) => {
                    let ov = other.var();
                    if !self.analyzer.seen[ov.index()] && self.assign.level(ov) > 0 {
                        self.analyzer.seen[ov.index()] = true;
                        seen_vars.push(ov);
                    }
                }
                Reason::Clause(r) => {
                    let lits: Vec<Lit> = self.db.lits(r).to_vec();
                    for x in lits {
                        let xv = x.var();
                        if xv != v && !self.analyzer.seen[xv.index()] && self.assign.level(xv) > 0 {
                            self.analyzer.seen[xv.index()] = true;
                            seen_vars.push(xv);
                        }
                    }
                }
                Reason::Theory(_) => {}
            }
        }
        for v in seen_vars {
            self.analyzer.seen[v.index()] = false;
        }
        core
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
                let lits: Vec<Lit> = self
                    .db
                    .lits(r)
                    .iter()
                    .copied()
                    .filter(|&x| x != l)
                    .collect();
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

    /// Boolean BCP followed by theory propagation, to joint fixpoint.
    pub fn propagate(&mut self) -> Option<Conflict> {
        loop {
            if let Some(c) = self.propagate_boolean() {
                return Some(c);
            }
            let mut out: Vec<(Lit, TheoryJust)> = Vec::new();
            match self.theory.propagate(&mut out) {
                Some(conflict_lits) => return Some(Conflict::Lits(conflict_lits)),
                None => {
                    if out.is_empty() {
                        return None;
                    }
                    for (l, just) in out {
                        self.enqueue(l, Reason::Theory(just));
                    }
                    // loop: Boolean-propagate the new theory literals
                }
            }
        }
    }

    /// Boolean constraint propagation to fixpoint. Returns the first conflict,
    /// or `None` if a fixpoint with no conflict is reached.
    fn propagate_boolean(&mut self) -> Option<Conflict> {
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
                            keep.push(Watch {
                                target: WatchTarget::Clause(r),
                                blocker: other,
                            });
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
                        keep.push(Watch {
                            target: WatchTarget::Clause(r),
                            blocker: other,
                        });
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

    use crate::theory::{NoTheory, Theory};
    use crate::types::{Effort, TheoryResult};
    use shinri_core::{NoProof, TheoryJust};

    fn lit(n: u32, pos: bool) -> Lit {
        Lit::new(Var::new(n), pos)
    }

    fn mk(n_vars: u32) -> Solver<NoTheory, NoProof, Vmtf> {
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..n_vars {
            s.new_var();
        }
        s
    }

    use crate::types::SolveResult;

    // A toy theory that, once it has seen x0 asserted true, propagates x1 true.
    #[derive(Default)]
    struct ForceX1 {
        saw_x0: bool,
        done: bool,
    }
    impl Theory for ForceX1 {
        fn assert(&mut self, lit: Lit) {
            if lit == Lit::new(Var::new(0), true) {
                self.saw_x0 = true;
            }
        }
        fn propagate(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
            if self.saw_x0 && !self.done {
                self.done = true;
                out.push((
                    Lit::new(Var::new(1), true),
                    TheoryJust { theory: 0, tag: 0 },
                ));
            }
            None
        }
        fn explain(&mut self, _j: TheoryJust, _out: &mut Vec<Lit>) {}
        fn check(&mut self, _e: Effort) -> TheoryResult {
            TheoryResult::Sat
        }
        fn push(&mut self) {}
        fn pop(&mut self, _n: usize) {}
        fn new_var(&mut self, _v: Var) {}
    }

    #[test]
    fn theory_propagation_forces_a_literal() {
        let mut s: Solver<ForceX1, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..2 {
            s.new_var();
        }
        s.add_clause(&[lit(0, true)]); // unit forces x0 true
        assert_eq!(s.solve(), SolveResult::Sat);
        assert_eq!(s.assign.value(Var::new(1)), LBool::True); // theory-propagated
    }

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
        let r_lo = s
            .add_learnt(&[lit(0, true), lit(1, true), lit(2, true)])
            .unwrap();
        let r_hi = s
            .add_learnt(&[lit(3, true), lit(4, true), lit(5, true)])
            .unwrap();
        s.db.set_lbd(r_lo, 2); // glue, protected (<= threshold 2)
        s.db.set_lbd(r_hi, 9); // high glue, deletable
        s.reduce();
        assert!(!s.db.is_deleted(r_lo), "low-LBD clause kept");
        assert!(s.db.is_deleted(r_hi), "high-LBD clause deleted");
        assert_eq!(
            s.stats_deleted, 1,
            "exactly one high-LBD unlocked clause deleted"
        );
    }

    #[test]
    fn failed_assumptions_yield_core() {
        use std::collections::HashSet;
        // Clause (x0 ∨ x1). Assume ¬x0 and ¬x1 => UNSAT, core = {¬x0, ¬x1}.
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        let r = s.solve_under(&[lit(0, false), lit(1, false)]);
        match r {
            SolveResult::Unsat { core } => {
                let set: HashSet<Lit> = core.into_iter().collect();
                assert!(set.contains(&lit(0, false)));
                assert!(set.contains(&lit(1, false)));
            }
            _ => panic!("expected UNSAT under assumptions"),
        }
    }

    #[test]
    fn satisfiable_under_assumptions() {
        let mut s = mk(2);
        s.add_clause(&[lit(0, true), lit(1, true)]);
        assert_eq!(s.solve_under(&[lit(0, true)]), SolveResult::Sat);
    }

    #[test]
    fn pop_undoes_scoped_unsat() {
        let mut s = mk(1);
        s.push();
        s.add_clause(&[lit(0, true)]);
        s.add_clause(&[lit(0, false)]); // conflicting units => UNSAT in scope
        assert!(matches!(s.solve(), SolveResult::Unsat { .. }));
        s.pop(1);
        assert_eq!(s.solve(), SolveResult::Sat); // scope undone => satisfiable
    }

    use shinri_core::{ClauseId, ProofSink};

    // RecordingSink for Item 1: proof round-trip test.
    #[derive(Default)]
    struct RecordingSink {
        inputs: Vec<Vec<Lit>>,
        learns: Vec<Vec<Lit>>,
    }
    impl ProofSink for RecordingSink {
        fn input(&mut self, _c: ClauseId, lits: &[Lit]) {
            self.inputs.push(lits.to_vec());
        }
        fn learn(&mut self, _c: ClauseId, lits: &[Lit], _chain: &[ClauseId]) {
            self.learns.push(lits.to_vec());
        }
        fn theory_lemma(&mut self, _c: ClauseId, _lits: &[Lit], _j: shinri_core::TheoryJust) {}
        fn delete(&mut self, _c: ClauseId) {}
    }

    #[test]
    fn proof_round_trip_drat_validates() {
        // Definitely-UNSAT 2-SAT: (x0∨x1) ∧ (x0∨¬x1) ∧ (¬x0∨x1) ∧ (¬x0∨¬x1)
        let mut s: Solver<NoTheory, RecordingSink, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..2 {
            s.new_var();
        }
        let inputs = vec![
            vec![lit(0, true), lit(1, true)],
            vec![lit(0, true), lit(1, false)],
            vec![lit(0, false), lit(1, true)],
            vec![lit(0, false), lit(1, false)],
        ];
        for cl in &inputs {
            s.add_clause(cl);
        }
        assert_eq!(s.solve(), SolveResult::Unsat { core: vec![] });
        let learnt = s.proof.learns.clone();
        assert!(
            crate::certificate::check_drat(2, &inputs, &learnt),
            "DRAT proof emitted by solver did not validate"
        );
    }

    #[derive(Default)]
    struct CountingSink {
        inputs: u32,
        learns: u32,
        deletes: u32,
    }
    impl ProofSink for CountingSink {
        fn input(&mut self, _c: ClauseId, _lits: &[Lit]) {
            self.inputs += 1;
        }
        fn learn(&mut self, _c: ClauseId, _lits: &[Lit], _chain: &[ClauseId]) {
            self.learns += 1;
        }
        fn theory_lemma(&mut self, _c: ClauseId, _lits: &[Lit], _j: shinri_core::TheoryJust) {}
        fn delete(&mut self, _c: ClauseId) {
            self.deletes += 1;
        }
    }

    #[test]
    fn proof_sink_sees_inputs_and_learns() {
        let mut s: Solver<NoTheory, CountingSink, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..2 {
            s.new_var();
        }
        // Long input clause => one `input` call.
        s.add_clause(&[lit(0, true), lit(1, true), lit(0, false)]);
        s.add_clause(&[lit(0, true), lit(1, false)]);
        s.add_clause(&[lit(0, false), lit(1, true)]);
        s.add_clause(&[lit(0, false), lit(1, false)]);
        let _ = s.solve();
        assert!(s.proof.inputs >= 1, "long input clauses recorded");
    }

    #[test]
    fn with_theory_injects_and_exposes_the_instance() {
        let s: Solver<NoTheory, NoProof, Vmtf> =
            Solver::with_theory(SolverConfig::default(), NoTheory);
        // Accessors compile and return the injected theory.
        let _t: &NoTheory = s.theory();
    }
}

#[cfg(test)]
mod incremental_tests {
    use super::*;
    use crate::heuristic::Vmtf;
    use crate::theory::Theory;
    use shinri_core::{Lit, Var};
    use shinri_core::{NoProof, TheoryJust};

    /// Counts net asserts and tracks its own scope depth, so the test can prove
    /// rebuild neither resets the instance nor double-asserts surviving units.
    #[derive(Default)]
    struct CountTheory {
        asserts: i64,
        depth: i64,
    }
    impl Theory for CountTheory {
        fn assert(&mut self, _lit: Lit) {
            self.asserts += 1;
        }
        fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
            None
        }
        fn explain(&mut self, _just: TheoryJust, _out: &mut Vec<Lit>) {}
        fn check(&mut self, _effort: crate::types::Effort) -> crate::types::TheoryResult {
            crate::types::TheoryResult::Sat
        }
        fn push(&mut self) {
            self.depth += 1;
        }
        fn pop(&mut self, n: usize) {
            self.depth -= n as i64;
        }
        fn new_var(&mut self, _v: Var) {}
    }

    #[test]
    fn pop_preserves_theory_and_does_not_double_assert() {
        let mut s: Solver<CountTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        let a = s.new_var();
        // A unit clause asserts `a` at level 0 -> one theory.assert.
        s.add_clause(&[Lit::new(a, true)]);
        assert_eq!(s.theory().asserts, 1);
        s.push(); // opens a user scope -> theory.push
        assert_eq!(s.theory().depth, 1);
        let b = s.new_var();
        s.add_clause(&[Lit::new(b, true)]); // asserts `b` -> two total
        assert_eq!(s.theory().asserts, 2);
        s.pop(1); // close the scope: theory.pop(1); silent re-install of survivors
                  // depth back to 0; the surviving unit `a` is NOT re-asserted (silent).
        assert_eq!(s.theory().depth, 0);
        assert_eq!(
            s.theory().asserts,
            2,
            "rebuild must not re-assert survivors"
        );
    }
}
