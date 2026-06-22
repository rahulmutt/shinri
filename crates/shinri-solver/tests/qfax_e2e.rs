//! End-to-end QF_AX (array) witnesses. Tests verify the ROW-1 and ROW-2 axioms
//! produce UNSAT, a free arrangement is SAT, and array equality is Unknown
//! (extensionality fence).

use shinri_core::{BuiltinOp, Op};
use shinri_solver::{SolveOutcome, Solver};

fn arr_setup(s: &mut Solver) -> (shinri_core::SortId, shinri_core::SortId, shinri_core::SortId) {
    let i = s.declare_sort("I");
    let e = s.declare_sort("E");
    let a = s.array_sort(i, e);
    (i, e, a)
}

#[test]
fn row1_select_over_store_same_index_unsat() {
    // select(store(a,i,e), i) != e  is UNSAT
    let mut s = Solver::new();
    let (i_s, e_s, arr_s) = arr_setup(&mut s);
    let a = s.declare_const("a", arr_s);
    let i = s.declare_const("i", i_s);
    let e = s.declare_const("e", e_s);
    let st = s.app(Op::Builtin(BuiltinOp::Store), &[a, i, e]);
    let sel = s.app(Op::Builtin(BuiltinOp::Select), &[st, i]);
    let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[sel, e]);
    s.assert(dist);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn row2_select_over_store_diff_index_unsat() {
    // i != j  ∧  select(store(a,i,e), j) != select(a, j)  is UNSAT
    let mut s = Solver::new();
    let (i_s, e_s, arr_s) = arr_setup(&mut s);
    let a = s.declare_const("a", arr_s);
    let i = s.declare_const("i", i_s);
    let j = s.declare_const("j", i_s);
    let e = s.declare_const("e", e_s);
    let st = s.app(Op::Builtin(BuiltinOp::Store), &[a, i, e]);
    let sel1 = s.app(Op::Builtin(BuiltinOp::Select), &[st, j]);
    let sel2 = s.app(Op::Builtin(BuiltinOp::Select), &[a, j]);
    let dij = s.app(Op::Builtin(BuiltinOp::Distinct), &[i, j]);
    let dsel = s.app(Op::Builtin(BuiltinOp::Distinct), &[sel1, sel2]);
    s.assert(dij);
    s.assert(dsel);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn free_arrangement_sat() {
    // select(store(a,i,e), j) = v  with i,j free  is SAT
    let mut s = Solver::new();
    let (i_s, e_s, arr_s) = arr_setup(&mut s);
    let a = s.declare_const("a", arr_s);
    let i = s.declare_const("i", i_s);
    let j = s.declare_const("j", i_s);
    let e = s.declare_const("e", e_s);
    let v = s.declare_const("v", e_s);
    let st = s.app(Op::Builtin(BuiltinOp::Store), &[a, i, e]);
    let sel = s.app(Op::Builtin(BuiltinOp::Select), &[st, j]);
    let eq = s.eq(sel, v);
    s.assert(eq);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

#[test]
fn array_equality_is_unknown() {
    // extensionality fence: array-to-array equality → Unknown
    let mut s = Solver::new();
    let (_i, _e, arr_s) = arr_setup(&mut s);
    let a = s.declare_const("a", arr_s);
    let b = s.declare_const("b", arr_s);
    let eq = s.eq(a, b);
    s.assert(eq);
    assert_eq!(s.check_sat(), SolveOutcome::Unknown);
}
