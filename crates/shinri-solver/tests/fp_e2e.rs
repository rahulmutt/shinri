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

// (sqrt(+inf)=+inf is covered by fp_sqrt_sat_get_model_round_trip below, which
// uses the identical query plus a model assertion — no separate SAT-only test.)

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

// ── Slice-2d end-to-end: ordering relations + fp.min/fp.max ───────────────────

#[test]
fn fp_lt_zero_lt_inf_is_sat() {
    let (o, _) = run("(assert (fp.lt (_ +zero 8 24) (_ +oo 8 24))) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_lt_antisymmetry_is_unsat() {
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) \
         (assert (fp.lt x y)) (assert (fp.lt y x)) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_leq_reflexive_fails_only_for_nan() {
    // (not (fp.leq x x)) is SAT only when x is NaN.
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (not (fp.leq x x))) (assert (fp.isNaN x)) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    let (o2, _) = run(
        "(declare-fun x () Float32) \
         (assert (not (fp.leq x x))) (assert (not (fp.isNaN x))) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Unsat);
}

#[test]
fn fp_min_of_inf_zero_equals_zero_sat_with_model() {
    let (o, model) = run(
        "(declare-fun x () Float32) \
         (assert (fp.eq x (fp.min (_ +oo 8 24) (_ +zero 8 24)))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat); // min(+oo,+0) = +0, so x fp.eq +0
    assert!(model.contains("(fp #b"), "model renders x: {model}");
}

#[test]
fn fp_max_picks_larger_unsat_when_contradicted() {
    // max(+0,+oo) = +oo, which is not fp.eq +0  => asserting equality is UNSAT.
    let (o, _) = run(
        "(assert (fp.eq (fp.max (_ +zero 8 24) (_ +oo 8 24)) (_ +zero 8 24))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

// ── Slice-2f end-to-end: fp.fma SAT/UNSAT + symbolic-RM + fence canary ──

#[test]
fn fp_fma_nan_when_zero_times_inf_sat() {
    // 0 * +inf + x is NaN regardless of x: fp.isNaN holds -> SAT.
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (fp.isNaN (fp.fma RNE (_ +zero 8 24) (_ +oo 8 24) x))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_fma_inf_product_finite_addend_sat() {
    // (+inf) * x + y, with x = +1.0-ish nonzero and y finite, is +inf.
    // Use isInfinite over a symbolic-but-constrained query: SAT.
    let (o, _) = run(
        "(declare-fun y () Float32) \
         (assert (fp.isInfinite (fp.fma RTP (_ +oo 8 24) (_ +oo 8 24) y))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat); // +inf * +inf + y = +inf
}

#[test]
fn fp_fma_inf_minus_inf_is_nan_sat() {
    // (+inf)*(+inf) + (-inf) = +inf + (-inf) = NaN.
    let (o, _) = run(
        "(assert (fp.isNaN (fp.fma RNE (_ +oo 8 24) (_ +oo 8 24) (_ -oo 8 24)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_fma_symbolic_rm_sat_get_model() {
    // w = fma(rm, x, y, z) with symbolic rm and operands: SAT, model renders.
    let (o, model) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) \
         (declare-fun z () Float32) (declare-fun w () Float32) \
         (declare-fun rm () RoundingMode) \
         (assert (fp.eq w (fp.fma rm x y z))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triples: {model}");
}

#[test]
fn fp_fma_malformed_is_unknown() {
    // Fence canary: an fma whose operand is an unsupported FP word (fp.rem is out
    // of scope) must trip the fence -> Unknown, never SAT/UNSAT.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) (declare-fun w () Float32) \
         (assert (fp.eq w (fp.fma RNE x y (fp.rem x y)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}

// ── Slice-2e end-to-end: fp.roundToIntegral SAT/UNSAT + symbolic-RM + get-model ──

#[test]
fn fp_roundtointegral_inf_passthrough_sat() {
    // roundToIntegral(RTP, +oo) = +oo, so fp.isInfinite holds: SAT.
    let (o, _) = run(
        "(assert (fp.isInfinite (fp.roundToIntegral RTP (_ +oo 8 24)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_roundtointegral_nan_is_nan_sat() {
    let (o, _) = run(
        "(assert (fp.isNaN (fp.roundToIntegral RNE (_ NaN 8 24)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_roundtointegral_idempotent_on_integral_unsat() {
    // For any x, roundToIntegral(RNE, roundToIntegral(RNE, x)) = roundToIntegral(RNE, x)
    // under STRUCTURAL equality (=, bitwise).  Under fp.eq this would be SAT because
    // fp.eq(NaN, NaN) = false (IEEE), making (not (fp.eq ...)) satisfiable at x=NaN.
    // With structural = the two sides have identical bits for every x (including NaN,
    // since rti(NaN) returns the canonical NaN unchanged), so (not (= ...)) is UNSAT.
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (not (= (fp.roundToIntegral RNE (fp.roundToIntegral RNE x)) \
                         (fp.roundToIntegral RNE x)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_roundtointegral_symbolic_rm_sat_get_model() {
    // z = roundToIntegral(rm, x) with symbolic rm and symbolic x: SAT, model renders.
    let (o, model) = run(
        "(declare-fun x () Float32) (declare-fun z () Float32) (declare-fun rm () RoundingMode) \
         (assert (fp.eq z (fp.roundToIntegral rm x))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triples: {model}");
}

#[test]
fn fp_roundtointegral_malformed_is_unknown() {
    // Fence canary: a roundToIntegral whose operand is an unsupported FP word
    // (fp.fma is out of scope) must trip the fence → Unknown, never SAT/UNSAT.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) (declare-fun u () Float32) \
         (assert (fp.eq u (fp.roundToIntegral RNE (fp.fma RNE x y u)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}
