//! End-to-end split-and-converge integration test (QF_LIA Plan A, Task 6).
//!
//! Drives a real `Solver<Combiner<NullTheory, OneShotSplitter>, NoProof, Vmtf>`
//! through the full splitting-on-demand loop:
//!   sub-theory `TCheck::Split` → Combiner `TheoryResult::SplitAtoms`
//!   → Solver mints+binds+learns+backtracks → search assigns split literals → Sat.

use std::cell::RefCell;

use shinri_core::{Lit, NoProof, TermId, Var};
use shinri_sat::{SolveResult, Solver, SolverConfig, Vmtf};
use shinri_theory::{Combiner, Effort, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

// Thread-local storage for observing `OneShotSplitter::new_var` calls from
// outside the Combiner (the `#[cfg(test)] pub(crate)` accessors are invisible
// to integration tests, which link the non-test lib build).
thread_local! {
    static BOUND: RefCell<Vec<(Var, TermId)>> = RefCell::new(Vec::new());
}

// ── NullTheory ────────────────────────────────────────────────────────────────
// Do-nothing EUF slot: every method is a no-op, check always returns Sat.

#[derive(Default)]
struct NullTheory;

impl TheorySolver for NullTheory {
    const THEORY_ID: u16 = 99;

    fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}

    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<shinri_theory::EqLeaf>> {
        None
    }

    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, shinri_core::TheoryJust)>,
    ) -> Option<Vec<shinri_theory::EqLeaf>> {
        None
    }

    fn check(&mut self, _cx: &mut TheoryCtx, _effort: Effort) -> TCheck {
        TCheck::Sat
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut shinri_theory::Explainer) {}

    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}

    fn push(&mut self) {}

    fn pop(&mut self, _level: usize) {}
}

// ── OneShotSplitter ───────────────────────────────────────────────────────────
// Arith slot: on the FIRST Full check returns `TCheck::Split([a1, a2])`, then
// always returns `TCheck::Sat`. Records each `new_var` call in `BOUND`.

#[derive(Default)]
struct OneShotSplitter {
    fired: bool,
}

impl TheorySolver for OneShotSplitter {
    const THEORY_ID: u16 = 7;

    fn new_var(&mut self, _cx: &mut TheoryCtx, v: Var, atom: TermId) {
        BOUND.with(|b| b.borrow_mut().push((v, atom)));
    }

    fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<shinri_theory::EqLeaf>> {
        None
    }

    fn propagate(
        &mut self,
        _cx: &mut TheoryCtx,
        _out: &mut Vec<(Lit, shinri_core::TheoryJust)>,
    ) -> Option<Vec<shinri_theory::EqLeaf>> {
        None
    }

    fn check(&mut self, _cx: &mut TheoryCtx, _effort: Effort) -> TCheck {
        if !self.fired {
            self.fired = true;
            TCheck::Split(vec![TermId::new(100).unwrap(), TermId::new(101).unwrap()])
        } else {
            TCheck::Sat
        }
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut shinri_theory::Explainer) {}

    fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}

    fn push(&mut self) {}

    fn pop(&mut self, _level: usize) {}
}

// ── Integration test ──────────────────────────────────────────────────────────

#[test]
fn split_once_then_sat_end_to_end() {
    // Reset the thread-local so a re-run in the same thread starts clean.
    BOUND.with(|b| b.borrow_mut().clear());

    // Build a Solver whose theory is a real Combiner<NullTheory, OneShotSplitter>.
    // Combiner::default() uses Context::new() internally; no atoms are registered
    // here, so assert/propagate are no-ops for the single real var `a`.
    let mut s: Solver<Combiner<NullTheory, OneShotSplitter>, NoProof, Vmtf> =
        Solver::new(SolverConfig::default());

    // Mint one real var and force it true with a unit clause. This ensures the
    // solver reaches `pick_branch() == None` (all vars assigned) and enters the
    // `theory.check(Effort::Full)` branch.
    let a = s.new_var();
    s.add_clause(&[Lit::new(a, true)]);

    // ── Run the full solve loop ──
    let res = s.solve();

    // ── Assertion 1: result is Sat ──
    assert!(
        matches!(res, SolveResult::Sat),
        "expected SolveResult::Sat, got {:?}",
        res
    );

    // ── Assertion 2: exactly two fresh vars were created and bound ──
    // The Combiner's bind_fresh calls OneShotSplitter::new_var for each split
    // atom. The solver mints vars in order after `a` (index 0), so the fresh
    // vars are at indices 1 and 2.
    let bound = BOUND.with(|b| b.borrow().clone());
    assert_eq!(
        bound.len(),
        2,
        "expected exactly 2 bind_fresh calls, got {}",
        bound.len()
    );
    // Both fresh vars must have higher indices than `a`.
    for (v, _atom) in &bound {
        assert!(
            v.index() > a.index(),
            "fresh var {:?} must have index > a.index() ({})",
            v,
            a.index()
        );
    }
    // The exact fresh var indices are 1 and 2.
    let indices: Vec<usize> = bound.iter().map(|(v, _)| v.index()).collect();
    assert!(
        indices.contains(&1),
        "expected fresh var at index 1, got {:?}",
        indices
    );
    assert!(
        indices.contains(&2),
        "expected fresh var at index 2, got {:?}",
        indices
    );

    // The bound.len() == 2 check above already pins "exactly two fresh vars were
    // minted": the OneShotSplitter records every bind_fresh call, so its count
    // is the authoritative count of fresh vars the Solver created for split atoms.

    // ── Assertion 3: the learnt split clause [v1, v2] is satisfied ──
    // The split clause is [Lit::new(fresh1, true), Lit::new(fresh2, true)].
    // After search converges, at least one of the two fresh vars must be true.
    let fresh_v1 = Var::new(1);
    let fresh_v2 = Var::new(2);
    let v1_true = s.value_of(fresh_v1) == Some(true);
    let v2_true = s.value_of(fresh_v2) == Some(true);
    assert!(
        v1_true || v2_true,
        "split clause [v1, v2] must be satisfied: v1={:?}, v2={:?}",
        s.value_of(fresh_v1),
        s.value_of(fresh_v2)
    );
}
