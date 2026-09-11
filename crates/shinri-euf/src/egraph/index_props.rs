//! Slice 49, spec §6.2: `EGraph` against a from-scratch congruence closure,
//! over random push/pop/merge/diseq/register traces, with the index
//! invariants (spec §4.1) checked after every step.

use super::test_rig::Rig;
use proptest::prelude::*;
use rustc_hash::FxHashMap;
use shinri_core::{Op, TermId, TermNode};

#[derive(Clone, Debug)]
enum Step {
    Push,
    Pop(u8),
    Merge(u8, u8),
    Diseq(u8, u8),
    Register(u8),
    /// A merge immediately followed by a registration: spec §1.2 step 1, the
    /// defect's shape, which independent steps reach too rarely.
    MergeThenRegister(u8, u8, u8),
    Drain,
}

fn step() -> impl Strategy<Value = Step> {
    prop_oneof![
        2 => Just(Step::Push),
        1 => any::<u8>().prop_map(Step::Pop),
        2 => (any::<u8>(), any::<u8>()).prop_map(|(a, b)| Step::Merge(a, b)),
        1 => (any::<u8>(), any::<u8>()).prop_map(|(a, b)| Step::Diseq(a, b)),
        2 => any::<u8>().prop_map(Step::Register),
        3 => (any::<u8>(), any::<u8>(), any::<u8>())
            .prop_map(|(a, b, p)| Step::MergeThenRegister(a, b, p)),
        2 => Just(Step::Drain),
    ]
}

const MAX_LEVEL: usize = 5;

struct World {
    r: Rig,
    /// Candidate terms: constants c0..c3, f(ci), g(ci,cj), f(f(ci)), g(f(ci),cj).
    pool: Vec<TermId>,
    /// `levels[k]`: equalities (`true`) and disequalities (`false`) asserted at level k.
    levels: Vec<Vec<(TermId, TermId, bool)>>,
    /// A level-0 constant whose no-op merge drains `pending`.
    anchor: TermId,
}

impl World {
    fn new() -> World {
        let mut r = Rig::new();
        let consts: Vec<TermId> = (0..4).map(|i| r.konst(&format!("c{i}"))).collect();
        let f = r.fun("f", 1);
        let g = r.fun("g", 2);
        let mut pool = consts.clone();
        for &c in &consts {
            pool.push(r.app(f, &[c]));
        }
        for &x in &consts {
            for &y in &consts {
                pool.push(r.app(g, &[x, y]));
            }
        }
        for &c in &consts {
            let fc = r.app(f, &[c]);
            pool.push(r.app(f, &[fc]));
        }
        for &x in &consts {
            let fx = r.app(f, &[x]);
            for &y in &consts {
                pool.push(r.app(g, &[fx, y]));
            }
        }
        for &c in &consts {
            r.add(c);
        }
        World {
            r,
            pool,
            levels: vec![Vec::new()],
            anchor: consts[0],
        }
    }

    fn level(&self) -> usize {
        self.levels.len() - 1
    }

    fn registered(&self) -> Vec<TermId> {
        self.r
            .g
            .registered_terms()
            .iter()
            .map(|&(t, _)| t)
            .collect()
    }

    fn pick(&self, i: u8) -> TermId {
        let reg = self.registered();
        reg[i as usize % reg.len()]
    }

    fn pop_to(&mut self, k: usize) {
        self.r.pop(k);
        self.levels.truncate(k + 1);
    }

    /// A theory conflict: backtrack one level, as the SAT solver would.
    /// Returns `false` when the conflict is at level 0 (the trace is over).
    fn on_conflict(&mut self) -> bool {
        match self.level() {
            0 => false,
            l => {
                self.pop_to(l - 1);
                true
            }
        }
    }

    fn merge(&mut self, a: u8, b: u8) -> bool {
        let (ta, tb) = (self.pick(a), self.pick(b));
        self.levels.last_mut().unwrap().push((ta, tb, true));
        if self.r.merge(ta, tb).is_some() {
            self.on_conflict()
        } else {
            true
        }
    }

    fn register(&mut self, p: u8) {
        let t = self.pool[p as usize % self.pool.len()];
        self.r.add(t);
    }

    /// Run one step. `Ok(false)` ends the trace.
    fn run(&mut self, s: &Step) -> Result<bool, TestCaseError> {
        let alive = match *s {
            Step::Push => {
                if self.level() >= MAX_LEVEL {
                    true
                } else if self.r.drain(self.anchor).is_some() {
                    // Spec §3.4's drain-before-push contract: the SAT loop
                    // propagates (and EUF closes) before every decision push.
                    self.on_conflict()
                } else {
                    self.compare()?;
                    self.r.push();
                    self.levels.push(Vec::new());
                    true
                }
            }
            Step::Pop(k) => {
                if self.level() > 0 {
                    let k = k as usize % self.level();
                    self.pop_to(k);
                }
                true
            }
            Step::Merge(a, b) => self.merge(a, b),
            Step::Diseq(a, b) => {
                let (ta, tb) = (self.pick(a), self.pick(b));
                if self.level() == 0 || ta == tb {
                    true
                } else {
                    self.levels.last_mut().unwrap().push((ta, tb, false));
                    if self.r.diseq(ta, tb).is_some() {
                        self.on_conflict()
                    } else {
                        true
                    }
                }
            }
            Step::Register(p) => {
                self.register(p);
                true
            }
            Step::MergeThenRegister(a, b, p) => {
                let alive = self.merge(a, b);
                if alive {
                    self.register(p);
                }
                alive
            }
            Step::Drain => {
                if self.r.drain(self.anchor).is_some() {
                    self.on_conflict()
                } else {
                    self.compare()?;
                    true
                }
            }
        };
        if alive {
            self.r
                .g
                .check_index(&self.r.eq)
                .map_err(TestCaseError::fail)?;
        }
        Ok(alive)
    }

    /// Only valid right after a drain that returned no conflict: the engine's
    /// equivalence over registered terms must equal a from-scratch congruence
    /// closure of the live equalities.
    fn compare(&mut self) -> Result<(), TestCaseError> {
        fn find(uf: &mut [usize], mut x: usize) -> usize {
            while uf[x] != x {
                uf[x] = uf[uf[x]];
                x = uf[x];
            }
            x
        }
        let reg = self.registered();
        let idx: FxHashMap<TermId, usize> = reg.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        let mut uf: Vec<usize> = (0..reg.len()).collect();
        for &(a, b, pos) in self.levels.iter().flatten() {
            if pos {
                let (ra, rb) = (find(&mut uf, idx[&a]), find(&mut uf, idx[&b]));
                uf[ra] = rb;
            }
        }
        let shapes: Vec<Option<(Op, Vec<usize>)>> = reg
            .iter()
            .map(|&t| match self.r.ctx.term_node(t) {
                TermNode::App { op, args, .. } => Some((
                    *op,
                    self.r.ctx.children(*args).iter().map(|k| idx[k]).collect(),
                )),
                TermNode::Const { .. } => None,
            })
            .collect();
        loop {
            let mut changed = false;
            let mut table: FxHashMap<(Op, Vec<usize>), usize> = FxHashMap::default();
            for (i, shape) in shapes.iter().enumerate() {
                let Some((op, kids)) = shape else { continue };
                let key = (
                    *op,
                    kids.iter().map(|&k| find(&mut uf, k)).collect::<Vec<_>>(),
                );
                match table.get(&key) {
                    Some(&j) => {
                        let (ri, rj) = (find(&mut uf, i), find(&mut uf, j));
                        if ri != rj {
                            uf[ri] = rj;
                            changed = true;
                        }
                    }
                    None => {
                        table.insert(key, i);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for &(a, b, pos) in self.levels.iter().flatten() {
            if !pos && find(&mut uf, idx[&a]) == find(&mut uf, idx[&b]) {
                return Err(TestCaseError::fail(format!(
                    "reference: live disequality {a:?} != {b:?} is violated, but the engine reported no conflict"
                )));
            }
        }
        for (i, &ti) in reg.iter().enumerate() {
            for (j, &tj) in reg.iter().enumerate().skip(i + 1) {
                let want = find(&mut uf, i) == find(&mut uf, j);
                let got = self.r.equal(ti, tj);
                if want != got {
                    return Err(TestCaseError::fail(format!(
                        "engine: {ti:?} {} {tj:?}; reference: {}",
                        if got { "==" } else { "!=" },
                        if want { "equal" } else { "distinct" }
                    )));
                }
            }
        }
        Ok(())
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 512,
        failure_persistence: None,
        ..ProptestConfig::default()
    })]

    #[test]
    fn egraph_matches_reference_closure(steps in prop::collection::vec(step(), 1..80)) {
        let mut w = World::new();
        for s in &steps {
            if !w.run(s)? {
                return Ok(());
            }
        }
        if w.r.drain(w.anchor).is_none() {
            w.compare()?;
        }
    }
}
