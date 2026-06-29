//! End-to-end QF_FP tests: SMT-LIB text -> parser -> solver, asserting SAT outcomes
//! and model rendering for pure floating-point queries.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Drive a script; return (last outcome, model string after the last check-sat).
fn run(src: &str) -> (SolveOutcome, String) {
    let mut s = Solver::new();
    let mut p = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(result) = p.next_command(s.ctx_mut()) {
        let cmd = result.expect("parse");
        match s.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    let model = s.get_model_string();
    (outcome, model)
}

#[test]
fn isnan_sat_model_is_a_nan() {
    let (o, model) = run("(declare-fun x () Float32) (assert (fp.isNaN x)) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
    // The model must define x as an (fp ...) triple whose exponent is all ones
    // and significand non-zero. We assert the rendering shape only.
    assert!(model.contains("(fp #b"), "model must render x as an fp triple: {model}");
}

#[test]
fn isnegative_and_isinfinite_sat() {
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (fp.isNegative x)) (assert (fp.isInfinite x)) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat); // x = -inf
}

#[test]
fn fp_eq_pos_neg_zero_is_sat() {
    // +0 fp.eq -0 holds, so this is SAT (any x works since both consts are concrete).
    let (o, _) = run("(assert (fp.eq (_ +zero 8 24) (_ -zero 8 24))) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

// ── Slice-2a end-to-end: fp.add / fp.sub SAT/UNSAT + symbolic-RM + get-model ───
//
// ENCODING NOTE: The SMT-LIB literal form `(fp #b0 #x7f ...)` is parsed as
// `FpFromBits` (an App node with BV children). `is_supported_fp_word` does not
// handle `FpFromBits`, so such scripts trip the soundness fence and return
// `Unknown` rather than SAT/UNSAT. The indexed special forms `(_ +oo 8 24)`,
// `(_ -oo 8 24)`, `(_ +zero 8 24)` etc. are parsed as `ConstVal::Float` nodes
// (via `mk_fp_const`), which ARE in `is_supported_fp_word`, so they pass the
// fence. All four tests below use these forms instead of `(fp ...)` literals.

#[test]
fn fp_add_inf_plus_inf_is_inf_sat() {
    // SAT: fp.add(RNE, +inf, +inf) = +inf. Uses (_ +oo 8 24) (ConstVal::Float)
    // because (fp #b...) literals route through FpFromBits (App w/ BV children),
    // which is not in is_supported_fp_word → soundness fence → Unknown.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.add RNE (_ +oo 8 24) (_ +oo 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat); // +inf + +inf = +inf
}

#[test]
fn fp_add_inf_plus_inf_not_neg_inf_unsat() {
    // UNSAT: fp.add(RNE, +inf, +inf) ≠ -inf. Uses (_ +oo 8 24) / (_ -oo 8 24)
    // (ConstVal::Float) for the same reason as the SAT sibling above.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.add RNE (_ +oo 8 24) (_ +oo 8 24))))
(assert (fp.eq x (_ -oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat); // +inf + +inf ≠ -inf
}

#[test]
fn fp_sub_is_add_neg_sat() {
    // SAT: fp.sub(RNE, +inf, +zero) = +inf. Analogous to 2 - 1 = 1.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.sub RNE (_ +oo 8 24) (_ +zero 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat); // +inf - +zero = +inf
}

#[test]
fn fp_add_symbolic_rm_sat() {
    // SAT: ∃ rounding mode rm. fp.eq x (fp.add rm +inf +zero).
    // Any concrete RM works: +inf + +zero = +inf regardless of rounding.
    let src = "\
(set-logic QF_FP)
(declare-fun rm () RoundingMode)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.add rm (_ +oo 8 24) (_ +zero 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_add_sat_get_model_round_trip() {
    // After SAT, get_model_string() must render the FP variable x.
    // x is constrained to +inf = 0x7F800000: sign 0, exp 11111111, sig 0*23.
    // The model renderer always uses binary (#b) for all three fields.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.add RNE (_ +oo 8 24) (_ +oo 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
    // +inf = (fp #b0 #b11111111 #b00000000000000000000000)
    assert!(
        model.contains("(fp #b0 #b11111111 #b00000000000000000000000)"),
        "model must render x as +inf: {model}"
    );
}

// ── Slice-2b end-to-end: fp.mul SAT/UNSAT + symbolic-RM + get-model ───────────

#[test]
fn fp_mul_inf_times_two_is_inf_sat() {
    // SAT: fp.mul(RNE, +inf, +inf) = +inf (inf * inf = inf, exact).
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.mul RNE (_ +oo 8 24) (_ +oo 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_mul_inf_times_zero_is_nan_sat() {
    // SAT: fp.mul(RNE, +inf, +zero) = NaN; x asserted isNaN.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (_ +zero 8 24)))
(assert (fp.isNaN (fp.mul RNE (_ +oo 8 24) x)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat); // +inf * +0 = NaN
}

#[test]
fn fp_mul_inf_times_zero_not_inf_unsat() {
    // UNSAT: (+inf * +0) is NaN, never +inf, so isInfinite of it cannot hold.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (_ +zero 8 24)))
(assert (fp.isInfinite (fp.mul RNE (_ +oo 8 24) x)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_mul_symbolic_rm_sat() {
    // SAT: ∃ rounding mode rm. fp.eq x (fp.mul rm +inf +inf).
    // inf * inf = +inf regardless of rounding.
    let src = "\
(set-logic QF_FP)
(declare-fun rm () RoundingMode)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.mul rm (_ +oo 8 24) (_ +oo 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_mul_sat_get_model_round_trip() {
    // After SAT, the model must render x = +inf. (+inf * +inf = +inf, exact.)
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.mul RNE (_ +oo 8 24) (_ +oo 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
    assert!(
        model.contains("(fp #b0 #b11111111 #b00000000000000000000000)"),
        "model must render x as +inf: {model}"
    );
}

// ── Slice-2c end-to-end: fp.div SAT/UNSAT + symbolic-RM + divByZero + get-model ──

#[test]
fn fp_div_inf_by_zero_is_inf_sat() {
    // SAT: fp.div(RNE, +inf, +zero) = +inf, and x asserted = +inf.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.div RNE (_ +oo 8 24) (_ +zero 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_div_zero_by_zero_is_nan_sat() {
    // SAT: fp.div(RNE, +zero, +zero) = NaN.
    let src = "\
(set-logic QF_FP)
(assert (fp.isNaN (fp.div RNE (_ +zero 8 24) (_ +zero 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_div_zero_by_zero_not_zero_unsat() {
    // UNSAT: 0/0 is NaN, and NaN is never fp.eq to +zero.
    let src = "\
(set-logic QF_FP)
(assert (fp.eq (fp.div RNE (_ +zero 8 24) (_ +zero 8 24)) (_ +zero 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_div_by_zero_symbolic_finite_sat() {
    // SAT: a normal y divided by +zero is ±inf (divByZero). Solver picks y normal.
    let src = "\
(set-logic QF_FP)
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isNormal y))
(assert (fp.isInfinite (fp.div RNE y (_ +zero 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_div_symbolic_rm_sat() {
    // SAT: ∃ rounding mode rm. fp.eq x (fp.div rm +inf +zero); +inf/+0 = +inf for any rm.
    let src = "\
(set-logic QF_FP)
(declare-fun rm () RoundingMode)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.div rm (_ +oo 8 24) (_ +zero 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_div_sat_get_model_round_trip() {
    // After SAT, the model must render x = +inf. (+inf / +zero = +inf, exact.)
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.div RNE (_ +oo 8 24) (_ +zero 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
    assert!(
        model.contains("(fp #b0 #b11111111 #b00000000000000000000000)"),
        "model must render x as +inf: {model}"
    );
}

// ── Slice-2c′ end-to-end: fp.sqrt SAT/UNSAT + get-model ──────────────────────

#[test]
fn fp_sqrt_inf_is_inf_sat() {
    // SAT: fp.sqrt(RNE, +inf) = +inf; x asserted fp.eq to +inf.
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.sqrt RNE (_ +oo 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat); // sqrt(+inf) = +inf
}

#[test]
fn fp_sqrt_neg_inf_is_nan_sat() {
    // SAT: fp.sqrt(RNE, -inf) = NaN.
    let src = "\
(set-logic QF_FP)
(assert (fp.isNaN (fp.sqrt RNE (_ -oo 8 24))))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat); // sqrt(-inf) = NaN
}

#[test]
fn fp_sqrt_neg_inf_is_not_zero_unsat() {
    // UNSAT: sqrt(-inf) = NaN, and NaN is never fp.eq to any non-NaN value.
    let src = "\
(set-logic QF_FP)
(assert (fp.eq (fp.sqrt RNE (_ -oo 8 24)) (_ +zero 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat); // NaN ≠ +zero under fp.eq
}

#[test]
fn fp_sqrt_sat_get_model_round_trip() {
    // After SAT, the model must render x = +inf. (sqrt(+inf) = +inf, exact.)
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.sqrt RNE (_ +oo 8 24))))
(assert (fp.eq x (_ +oo 8 24)))
(check-sat)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat);
    assert!(
        model.contains("(fp #b0 #b11111111 #b00000000000000000000000)"),
        "model must render x as +inf: {model}"
    );
}
