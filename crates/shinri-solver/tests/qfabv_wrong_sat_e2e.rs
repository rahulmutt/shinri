//! Slice 47: regression pins for the QF_ABV wrong-`sat` cluster. Each fixture
//! is a hand-reduced form of a named reproducer from
//! `docs/superpowers/specs/2026-09-09-shinri-slice47-qfabv-wrong-sat-design.md` §8.
//! The first two are UNSAT. A `sat` on either is a soundness regression; an
//! `unknown` means the post-solve gate caught the model but the engine still
//! cannot decide the shape (spec §7 criterion 4 — sound, and reportable).
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

fn run(src: &str) -> Option<CommandResponse> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut last = None;
    while let Some(r) = parser.next_command(solver.ctx_mut()) {
        let cmd = r.expect("fixture parses");
        let resp = solver.execute(cmd);
        if !matches!(resp, CommandResponse::None) {
            last = Some(resp);
        }
    }
    last
}

/// `wchains002ue` reduced: two chains over the same base writing the same two
/// indices in opposite orders. The writes commute when i != j, so asserting
/// the chains differ is UNSAT.
#[test]
fn commuting_store_chains_are_not_distinct() {
    let r = run("(set-logic QF_ABV)\
         (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-fun i () (_ BitVec 8))(declare-fun j () (_ BitVec 8))\
         (declare-fun e () (_ BitVec 8))(declare-fun f () (_ BitVec 8))\
         (assert (distinct i j))\
         (assert (distinct (store (store a i e) j f) (store (store a j f) i e)))\
         (check-sat)");
    assert_eq!(r, Some(CommandResponse::Unsat));
}

/// `bubsort002un` reduced: a read of a doubly-stored array at the first store's
/// index, where the second store writes a different index, must equal the first
/// store's element.
#[test]
fn read_through_two_stores_is_pinned() {
    let r = run("(set-logic QF_ABV)\
         (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-fun i () (_ BitVec 8))(declare-fun j () (_ BitVec 8))\
         (declare-fun e () (_ BitVec 8))(declare-fun f () (_ BitVec 8))\
         (assert (distinct i j))\
         (assert (distinct (select (store (store a i e) j f) i) e))\
         (check-sat)");
    assert_eq!(r, Some(CommandResponse::Unsat));
}

/// A store chain equated to itself under a different write order, positively
/// asserted — the shape Task 5's `accessed_indices` fix serves. The chains ARE
/// equal, so the asserted equality holds and this must stay SAT: the pin that
/// catches an over-rejecting gate (spec §7 criterion 2).
#[test]
fn commuting_store_chains_are_equal() {
    let r = run("(set-logic QF_ABV)\
         (declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-fun i () (_ BitVec 8))(declare-fun j () (_ BitVec 8))\
         (declare-fun e () (_ BitVec 8))(declare-fun f () (_ BitVec 8))\
         (assert (distinct i j))\
         (assert (= (store (store a i e) j f) (store (store a j f) i e)))\
         (check-sat)");
    assert_eq!(r, Some(CommandResponse::Sat));
}

/// The spec's minimal store-chain-equality reproducer, verbatim: two chains
/// over one base writing the SAME two indices with the elements swapped. With
/// `i0 != i1` the writes are independent, so the chains agree only where
/// `e0 == e1` — which the second assertion forbids. z3: `unsat`.
///
/// This is the shape whose `sat` the slice-47 bisect traced to a corrupted
/// model read (`abv_stage::RealBridge::model`), not to a missing axiom.
#[test]
fn swapped_elements_over_shared_indices_are_distinct() {
    let r = run("(set-logic QF_ABV)\
         (declare-const a0 (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const i0 (_ BitVec 8))(declare-const i1 (_ BitVec 8))\
         (declare-const e0 (_ BitVec 8))(declare-const e1 (_ BitVec 8))\
         (assert (distinct i0 i1))(assert (distinct e0 e1))\
         (assert (= (store (store a0 i0 e0) i1 e1) (store (store a0 i0 e1) i1 e0)))\
         (check-sat)");
    assert_eq!(r, Some(CommandResponse::Unsat));
}
