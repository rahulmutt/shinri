use shinri_core::{BuiltinOp, Op};
use shinri_num::Rational;
use shinri_solver::{SolveOutcome, Solver};

fn int_const(s: &mut Solver, name: &str) -> shinri_core::TermId {
    let int = s.int_sort();
    s.declare_const(name, int)
}
fn int_num(s: &mut Solver, n: i128) -> shinri_core::TermId {
    let int = s.int_sort();
    s.numeral(Rational::from_int(n.into()), int)
}

#[test]
fn int_unsat_2x_eq_1() {
    // 2x = 1 has no integer solution.
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let two = int_num(&mut s, 2);
    let one = int_num(&mut s, 1);
    let twox = s.app(Op::Builtin(BuiltinOp::Mul), &[two, x]);
    let atom = s.eq(twox, one);
    s.assert(atom);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn int_sat_with_branching() {
    // 2x = 4 ∧ x ≥ 1 → x = 2 (sat, requires integer feasibility).
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let two = int_num(&mut s, 2);
    let four = int_num(&mut s, 4);
    let onec = int_num(&mut s, 1);
    let twox = s.app(Op::Builtin(BuiltinOp::Mul), &[two, x]);
    let eq = s.eq(twox, four);
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[x, onec]);
    s.assert(eq);
    s.assert(ge);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

#[test]
fn int_diseq_is_a_split() {
    // x ≠ 0 ∧ -1 ≤ x ≤ 1 → x = 1 or x = -1 (sat).
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let zero = int_num(&mut s, 0);
    let lo = int_num(&mut s, -1);
    let hi = int_num(&mut s, 1);
    let ne = {
        let eq = s.eq(x, zero);
        s.app(Op::Builtin(BuiltinOp::Not), &[eq])
    };
    let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[x, lo]);
    let le = s.app(Op::Builtin(BuiltinOp::Le), &[x, hi]);
    s.assert(ne);
    s.assert(ge);
    s.assert(le);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);
}

#[test]
fn unbounded_infeasible_terminates() {
    // 3x − 3y = 1 has no integer solution; the a-priori box makes the search
    // terminate (unsat) instead of branching forever.
    let mut s = Solver::new();
    let x = int_const(&mut s, "x");
    let y = int_const(&mut s, "y");
    let three = int_num(&mut s, 3);
    let one = int_num(&mut s, 1);
    let tx = s.app(Op::Builtin(BuiltinOp::Mul), &[three, x]);
    let ty = s.app(Op::Builtin(BuiltinOp::Mul), &[three, y]);
    let lhs = s.app(Op::Builtin(BuiltinOp::Sub), &[tx, ty]);
    let atom = s.eq(lhs, one);
    s.assert(atom);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn mixed_int_real_query_is_unknown() {
    // An Int atom and a Real atom in one query → fenced to Unknown (QF_LIRA).
    let mut s = Solver::new();
    let xi = int_const(&mut s, "xi");
    let zi = int_num(&mut s, 0);
    let gei = s.app(Op::Builtin(BuiltinOp::Ge), &[xi, zi]);
    let real = s.real_sort();
    let xr = s.declare_const("xr", real);
    let zr = s.numeral(Rational::from_int(0i128.into()), real);
    let ger = s.app(Op::Builtin(BuiltinOp::Ge), &[xr, zr]);
    s.assert(gei);
    s.assert(ger);
    assert_eq!(s.check_sat(), SolveOutcome::Unknown);
}
