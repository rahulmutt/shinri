//! Property tests for the EqualityEngine: a brute-force union-find oracle must
//! agree on `are_equal`, and `pop` must restore state exactly (spec §10).

use proptest::prelude::*;
use shinri_core::{Lit, TermId, Var};
use shinri_theory::{ENodeId, EqJust, EqualityEngine, MergeEvent};

/// A naive backtracking union-find oracle (Vec-of-sets), no proof forest.
#[derive(Clone, Default)]
struct Oracle {
    parent: Vec<usize>,
    snapshots: Vec<Vec<usize>>,
}
impl Oracle {
    fn intern(&mut self, n: usize) {
        while self.parent.len() <= n {
            let k = self.parent.len();
            self.parent.push(k);
        }
    }
    fn find(&self, mut n: usize) -> usize {
        while self.parent[n] != n {
            n = self.parent[n];
        }
        n
    }
    fn merge(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
    fn equal(&self, a: usize, b: usize) -> bool {
        self.find(a) == self.find(b)
    }
    fn push(&mut self) {
        self.snapshots.push(self.parent.clone());
    }
    fn pop(&mut self) {
        self.parent = self.snapshots.pop().unwrap();
    }
}

#[derive(Clone, Debug)]
enum Cmd {
    Merge(u8, u8),
    Push,
    Pop,
}

fn cmd_strategy() -> impl Strategy<Value = Cmd> {
    prop_oneof![
        (0u8..8, 0u8..8).prop_map(|(a, b)| Cmd::Merge(a, b)),
        Just(Cmd::Push),
        Just(Cmd::Pop),
    ]
}

proptest! {
    #[test]
    fn engine_matches_oracle(cmds in proptest::collection::vec(cmd_strategy(), 0..200)) {
        let mut eng = EqualityEngine::default();
        let mut orc = Oracle::default();
        let nodes: Vec<ENodeId> = (0..8).map(|i| eng.intern(TermId::new(i + 1).unwrap())).collect();
        for i in 0..8 { orc.intern(i); }
        let mut depth = 0usize;
        for cmd in cmds {
            match cmd {
                Cmd::Merge(a, b) => {
                    let (a, b) = (a as usize, b as usize);
                    let j = EqJust::Asserted(Lit::new(Var::new((a * 8 + b) as u32), true));
                    let _ = eng.merge(nodes[a], nodes[b], j);
                    // Drain merge events so pop's debug_assert (merges.is_empty()) never fires.
                    let mut drained: Vec<MergeEvent> = Vec::new();
                    eng.drain_merges(&mut drained);
                    orc.merge(a, b);
                }
                Cmd::Push => { eng.push(); orc.push(); depth += 1; }
                Cmd::Pop => {
                    if depth > 0 {
                        depth -= 1;
                        eng.pop(depth);
                        orc.pop();
                    }
                }
            }
            // Invariant: are_equal agrees with the oracle for every pair.
            for a in 0..8 {
                for b in 0..8 {
                    prop_assert_eq!(eng.are_equal(nodes[a], nodes[b]), orc.equal(a, b));
                }
            }
        }
    }
}
