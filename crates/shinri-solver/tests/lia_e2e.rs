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
#[ignore = "terminates and is sound, but baseline B&B (cuts OFF) explores O(M) diagonal nodes \
            on 3x−3y=1 with the sound a-priori bound (~85k), taking minutes; \
            re-enable after Plan B2 adds Gomory cuts"]
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

/// Regression test for Bug 2 (GMI orientation via full DeltaRational match).
///
/// iter=22 repro from the Task-8 differential oracle: constraints over x0,x1,x2 ∈ ℤ:
///   -x2 ≠ -3  (x2 ≠ 3)
///   -2x0 -2x1 -2x2 ≠ 3
///   -x0 ≠ -2  (x0 ≠ 2)
///   x0 - 2x2 < 0
///
/// Before the fix, `derive_gmi` picked the wrong bound orientation for a nonbasic
/// whose value matched the bound only on .c() but NOT on the δ component; this
/// produced a non-separating cut → `debug_validate` SIGABRT (in debug mode).
/// After the fix the solver must return Sat or Unsat (no panic).
#[test]
fn gmi_orientation_bug_repro_iter22() {
    let mut s = Solver::new();
    s.set_stage_b(true);
    let int = s.int_sort();
    let x0 = s.declare_const("x0", int);
    let x1 = s.declare_const("x1", int);
    let x2 = s.declare_const("x2", int);

    let n = |s: &mut Solver, v: i64| s.numeral(Rational::from_int((v as i128).into()), int);
    let mul = |s: &mut Solver, c: i64, v: _| {
        let cn = n(s, c);
        s.app(Op::Builtin(BuiltinOp::Mul), &[cn, v])
    };
    let ne = |s: &mut Solver, lhs: _, rhs: _| {
        let eq = s.eq(lhs, rhs);
        s.app(Op::Builtin(BuiltinOp::Not), &[eq])
    };

    // -x2 ≠ -3
    let neg_x2 = mul(&mut s, -1, x2);
    let neg3 = n(&mut s, -3);
    let c0 = ne(&mut s, neg_x2, neg3);
    // -2x0 - 2x1 - 2x2 ≠ 3
    let t0 = mul(&mut s, -2, x0);
    let t1 = mul(&mut s, -2, x1);
    let t2 = mul(&mut s, -2, x2);
    let sum01 = s.app(Op::Builtin(BuiltinOp::Add), &[t0, t1]);
    let sum012 = s.app(Op::Builtin(BuiltinOp::Add), &[sum01, t2]);
    let three = n(&mut s, 3);
    let c1 = ne(&mut s, sum012, three);
    // -x0 ≠ -2
    let neg_x0 = mul(&mut s, -1, x0);
    let neg2 = n(&mut s, -2);
    let c2 = ne(&mut s, neg_x0, neg2);
    // x0 - 2x2 < 0
    let pos_x0 = mul(&mut s, 1, x0);
    let neg2x2 = mul(&mut s, -2, x2);
    let lhs4 = s.app(Op::Builtin(BuiltinOp::Add), &[pos_x0, neg2x2]);
    let zero = n(&mut s, 0);
    let c3 = s.app(Op::Builtin(BuiltinOp::Lt), &[lhs4, zero]);

    s.assert(c0);
    s.assert(c1);
    s.assert(c2);
    s.assert(c3);
    // Must not panic (SIGABRT from debug_validate or OOB from sentinel leak).
    // The exact outcome (Sat/Unsat) is whatever is correct; we just guard no crash.
    let outcome = s.check_sat();
    assert!(
        matches!(outcome, SolveOutcome::Sat | SolveOutcome::Unsat),
        "expected Sat or Unsat, got {outcome:?}"
    );
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
