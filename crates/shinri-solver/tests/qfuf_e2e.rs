use shinri_core::{BuiltinOp, Op};
use shinri_solver::{SolveOutcome, Solver};

fn uconst(s: &mut Solver, name: &str, sort: shinri_core::SortId) -> shinri_core::TermId {
    let f = s.declare_fun(name, &[], sort);
    s.app(Op::Uninterpreted(f), &[])
}

#[test]
fn push_pop_scopes_assertions() {
    let mut s = Solver::new();
    let u = s.declare_sort("U");
    let a = uconst(&mut s, "a", u);
    let b = uconst(&mut s, "b", u);
    let ab = s.eq(a, b);
    let nab = s.app(Op::Builtin(BuiltinOp::Not), &[ab]);

    s.assert(ab); // a = b
    assert_eq!(s.check_sat(), SolveOutcome::Sat);

    s.push();
    s.assert(nab); // a = b  ∧  a != b  -> unsat in this scope
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
    s.pop(1);

    // Back to just a = b -> sat again.
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

#[test]
fn predicate_congruence_e2e() {
    let mut s = Solver::new();
    let u = s.declare_sort("U");
    let boolsort = s.bool_sort();
    let a = uconst(&mut s, "a", u);
    let b = uconst(&mut s, "b", u);
    let p = s.declare_fun("p", &[u], boolsort);
    let pa = s.app(Op::Uninterpreted(p), &[a]);
    let pb = s.app(Op::Uninterpreted(p), &[b]);
    let npb = s.app(Op::Builtin(BuiltinOp::Not), &[pb]);
    let ab = s.eq(a, b);
    s.assert(pa);
    s.assert(npb);
    s.assert(ab);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}
