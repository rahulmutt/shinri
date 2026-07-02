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
// ENCODING NOTE (historical, slice-2a): at the time these tests were written,
// the SMT-LIB literal form `(fp #b0 #x7f ...)` parsed as `FpFromBits` (an App
// node with BV children), which `is_supported_fp_word` did not handle, so such
// scripts tripped the soundness fence and returned `Unknown` rather than
// SAT/UNSAT. As of slice 4c, `FpFromBits` (and the 1-arg `to_fp` bitcast) IS
// admitted and solves end-to-end — see the slice-4c end-to-end block below.
// The indexed special forms `(_ +oo 8 24)`, `(_ -oo 8 24)`, `(_ +zero 8 24)`
// etc. are parsed as `ConstVal::Float` nodes (via `mk_fp_const`), which were
// (and remain) in `is_supported_fp_word`. All four tests below still use
// these forms instead of `(fp ...)` literals, for consistency with the rest
// of this slice-2a block.

#[test]
fn fp_add_inf_plus_inf_is_inf_sat() {
    // SAT: fp.add(RNE, +inf, +inf) = +inf. Uses (_ +oo 8 24) (ConstVal::Float);
    // (fp #b...) literals (FpFromBits) also solve as of slice 4c, but this test
    // predates that and keeps the special-value form for consistency.
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
    // Fence canary: an fma whose operand is an unsupported FP word must trip the
    // fence -> Unknown. Trigger = to_fp from a symbolic Real (durably out of scope
    // for all of v1: the symbolic-Real bridge is deferred past Plan 3). Float-sorted,
    // so it nests where the 4th fma operand must be a Float.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) (declare-fun w () Float32) \
         (declare-fun r () Real) \
         (assert (fp.eq w (fp.fma RNE x y ((_ to_fp 8 24) RNE r)))) (check-sat)",
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
    // (to_fp from a symbolic Real, durably out of scope) must trip the fence -> Unknown.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun u () Float32) (declare-fun r () Real) \
         (assert (fp.eq u (fp.roundToIntegral RNE ((_ to_fp 8 24) RNE r)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}

// ── Slice-2g end-to-end: fp.rem SAT/UNSAT + get-model + fence canary ──

#[test]
fn fp_rem_known_value_sat() {
    // rem(+0, +oo) = +0: rule "rem(x, ±inf) = x" for finite x (here x = +0), per
    // shinri-fp/src/reference.rs ref_rem. Ground/constant-only query.
    //
    // DEVIATION FROM BRIEF (historical, slice-2g): at the time this test was
    // written, the brief's literal form `(fp #b0 #x82 #b...)` for "5.0 rem 3.0
    // = -1.0" did NOT pass this codebase's soundness fence -- the
    // `(fp #b sign #x exp #b sig)` triple parses as `FpFromBits` (an App node),
    // which `is_supported_fp_word` did not recognize at the time (only
    // `ConstVal::Float` literals and nullary FP vars were base cases; see the
    // pre-existing slice-2a ENCODING NOTE earlier in this file). Confirmed
    // empirically: that form yielded Unknown, not Sat. As of slice 4c,
    // `FpFromBits` IS admitted and solves end-to-end (see the slice-4c
    // end-to-end block below), but this test predates that and keeps the
    // special-value-form workaround for consistency: the "known value" here
    // is expressed via the five special forms
    // `(_ +oo/-oo/+zero/-zero/NaN eb sb)` instead of 5.0/3.0.
    let (o, _) = run(
        "(assert (fp.eq (fp.rem (_ +zero 8 24) (_ +oo 8 24)) (_ +zero 8 24))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_rem_inf_dividend_is_nan_unsat() {
    // DEVIATION FROM BRIEF (two levels): the brief's primary symbolic-x form
    // (`(fp.gt (fp.abs (fp.rem x 2.0)) 2.0)` -> UNSAT) risks the known fp.rem
    // deep-circuit grind under symbolic UNSAT (~276-stage circuit; see brief
    // NOTE and memory: bit-blasted fp.div/fp.rem-class circuits can run for
    // minutes to hours). The brief's authorized concrete-x fallback
    // (`rem(7.0,2.0) = -1.0`, assert `= +1.0` -> Unsat) is ALSO unreachable: it
    // depends on the same `(fp #b...)` literal-triple encoding used (and
    // rejected, see fp_rem_known_value_sat above) for the SAT test, which trips
    // the fence -> Unknown rather than Unsat. Confirmed empirically.
    //
    // Resolution: build a ground UNSAT entirely from the five fence-admitted
    // special-value literals. Per shinri-fp/src/reference.rs ref_rem, rule order
    // is NaN -> rem(±inf, _) = NaN -> rem(_, ±0) = NaN -> rem(x, ±inf) = x ->
    // rem(±0, finite-nonzero) = ±0 -> exact remainder. rem(+oo, +0) hits the
    // `rem(±inf, _) = NaN` rule (checked before y is even examined), so the true
    // result is NaN, never +0. fp.eq(NaN, _) is always false (IEEE), so
    // asserting the result equals +0 is UNSAT. Ground/constant-only: folds
    // instantly, no symbolic search at all -- strictly faster and safer than
    // either of the brief's two proposed forms.
    let (o, _) = run(
        "(assert (fp.eq (fp.rem (_ +oo 8 24) (_ +zero 8 24)) (_ +zero 8 24))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_rem_sat_get_model() {
    // w = rem(x, y): SAT, model renders fp triples.
    let (o, model) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) (declare-fun w () Float32) \
         (assert (fp.eq w (fp.rem x y))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triples: {model}");
}

#[test]
fn fp_rem_malformed_is_unknown() {
    // Slice-2g fence canary: a fp.rem nesting an unsupported FP word (to_fp from a
    // symbolic Real, durably out of scope) must trip the fence -> Unknown.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun u () Float32) (declare-fun r () Real) \
         (assert (fp.eq u (fp.rem x ((_ to_fp 8 24) RNE r)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}

// ── Slice-3a end-to-end: non-BV to_fp (FP→FP + const-Real) + fence canaries ──

#[test]
fn to_fp_fp_widen_sat_get_model() {
    // y (Float64) = widen(x : Float32). SAT; model renders fp triples.
    let (o, model) = run(
        "(declare-fun x () Float32) (declare-fun y () Float64) \
         (assert (fp.eq y ((_ to_fp 11 53) RNE x))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triples: {model}");
}

#[test]
fn to_fp_fp_widen_reflexive_unsat() {
    // Widening a symbolic Float32 x to Float64 and asserting the result differs
    // from itself (core = — bitwise, well-defined even when x is NaN, unlike
    // fp.eq) is UNSAT. This drives the real FP→FP widen circuit for a symbolic
    // source and pins the pipeline to a decidable UNSAT verdict.
    // (This test predates slice 4c: at the time it was written, the intended
    //  "widen(1.0f32) == 1.0f64" literal test was not expressible, since
    //  `(fp #b..)` literal triples parsed to the then-unsupported FpFromBits
    //  node — a documented slice-2a encoding limitation — so a literal-source
    //  to_fp fenced to Unknown. As of slice 4c, FpFromBits IS admitted, but a
    //  symbolic source remains a valid — and arguably stronger — way to
    //  exercise the widen circuit, so this test is kept as-is.)
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (not (= ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) RNE x)))) \
         (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn to_fp_const_real_known_value_sat() {
    // to_fp of 1/3 into Float32 (RNE) = 0x3EAA_AAAB; assert fp.eq with z and read model.
    let (o, model) = run(
        "(declare-fun z () Float32) \
         (assert (fp.eq z ((_ to_fp 8 24) RNE (/ 1.0 3.0)))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triple for z: {model}");
}

#[test]
fn to_fp_const_real_reflexive_unsat() {
    // to_fp(1/3) equals itself under fp.eq (non-NaN); asserting the negation is UNSAT.
    let (o, _) = run(
        "(assert (not (fp.eq ((_ to_fp 8 24) RNE (/ 1.0 3.0)) \
                             ((_ to_fp 8 24) RNE (/ 1.0 3.0))))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn to_fp_bv_crossing_and_symbolic_real_are_unknown() {
    // Remaining still-fenced conversions → Unknown (soundness: BV→FP bitcast
    // (FpFromBits / 1-arg to_fp) is admitted as of slice 4c, int→FP
    // (2-arg to_fp + to_fp_unsigned) is admitted as of slice 4d, and FP→BV
    // (fp.to_sbv/fp.to_ubv) is admitted as of slice 4e — see the slice-4c,
    // slice-4d, and slice-4e end-to-end blocks above; the remaining fence is
    // only the deferred Real bridge (symbolic-Real to_fp / fp.to_real).
    let scripts = [
        // symbolic-Real to_fp
        "(declare-fun r () Real) (declare-fun z () Float32) \
         (assert (fp.eq z ((_ to_fp 8 24) RNE r))) (check-sat)",
        // fp.to_real
        "(declare-fun x () Float32) \
         (assert (= (fp.to_real x) 0.0)) (check-sat)",
    ];
    for s in scripts {
        let (o, _) = run(s);
        assert_eq!(o, SolveOutcome::Unknown, "must fence to Unknown: {s}");
    }
}

// ── Slice-4b: mixed BV+FP (no crossing op) now solves ──────────────────────
#[test]
fn mixed_bv_and_fp_sat_with_model() {
    // A pure-BV constraint AND a pure-FP constraint, no crossing conversion.
    // x = #x05 (BV8) and y is a NaN (FP32). Independent, jointly satisfiable.
    let src = "\
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= x #x05))
(assert (fp.isNaN y))
(check-sat)
(get-model)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "mixed BV+FP (no crossing) is SAT");
    assert!(model.contains("x"), "model surfaces the BV var");
    assert!(model.contains("y"), "model surfaces the FP var");
}

#[test]
fn mixed_bv_and_fp_unsat() {
    // BV side is self-contradictory; the whole conjunction is UNSAT regardless
    // of the (satisfiable) FP side — proves the two blast into one instance.
    let src = "\
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= x #x05))
(assert (= x #x06))
(assert (fp.isNaN y))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat, "contradictory BV side makes the mixed query UNSAT");
}

// ── Slice-4c end-to-end: BV→FP bitcast (FpFromBits + 1-arg to_fp) ───────────
#[test]
fn fp_from_bits_known_value_sat() {
    // (fp #b0 #b11111111 #b0…0) is +oo. Pins the field layout semantically:
    // sign=0 (MSB), exp=all-ones, sig=0. A wrong concat order would break this.
    let src = "\
(declare-fun z () (_ FloatingPoint 8 24))
(assert (fp.eq z (fp #b0 #b11111111 #b00000000000000000000000)))
(assert (fp.isInfinite z))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "(fp 0 all-ones 0) is +oo");
}

#[test]
fn fp_from_bits_sign_bit_is_msb_unsat() {
    // Same pattern but sign=1 → -oo, which is fp.eq-distinct from +oo → UNSAT.
    let src = "\
(assert (fp.eq (fp #b1 #b11111111 #b00000000000000000000000) (_ +oo 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat, "sign bit is the MSB: (fp 1 …) is -oo, not +oo");
}

#[test]
fn fp_from_bits_symbolic_child_sat_with_model() {
    // Symbolic BV sign feeding an FP atom; get-model surfaces both the BV child
    // and the resulting FP var.
    let src = "\
(declare-fun s () (_ BitVec 1))
(declare-fun z () (_ FloatingPoint 8 24))
(assert (fp.eq z (fp s #b11111111 #b00000000000000000000000)))
(assert (fp.isInfinite z))
(check-sat)
(get-model)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "∃ sign bit making (fp s all-ones 0) infinite");
    assert!(model.contains("s"), "model surfaces the symbolic BV child");
    assert!(model.contains("z"), "model surfaces the FP var");
}

#[test]
fn to_fp_1arg_bitcast_known_value_sat() {
    // 0x7f800000 is the IEEE-754 bit pattern for +oo (float32). The 1-arg
    // to_fp reinterprets it; isInfinite must hold.
    let src = "\
(declare-fun b () (_ BitVec 32))
(assert (= b #x7f800000))
(assert (fp.isInfinite ((_ to_fp 8 24) b)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "0x7f800000 bitcasts to +oo");
}

// ── Slice-4d end-to-end: int→FP (to_fp 2-arg BV + to_fp_unsigned) ───────────
#[test]
fn to_fp_signed_bv_sat_with_model() {
    // The only 8-bit signed b with value -1 is 0xFF; -1.0f32 is
    // (fp #b1 #b01111111 #b0…0). Pins the signed read end-to-end.
    let src = "\
(declare-fun b () (_ BitVec 8))
(assert (fp.eq ((_ to_fp 8 24) RNE b) (fp #b1 #b01111111 #b00000000000000000000000)))
(check-sat)
(get-model)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "b = 0xFF reads as -1 signed");
    assert!(model.contains("b"), "model surfaces the BV source var");
}

#[test]
fn to_fp_unsigned_never_negative_unsat() {
    // An unsigned read is ≥ 0, and fp.lt equates ±0 — so strictly-below -0 is
    // impossible. Distinguishes the unsigned face from the signed one.
    let src = "\
(declare-fun b () (_ BitVec 8))
(assert (fp.lt ((_ to_fp_unsigned 8 24) RNE b) (_ -zero 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat, "unsigned int→FP is never negative");
}

#[test]
fn to_fp_signed_bv_negative_sat() {
    // The signed counterpart of the test above IS satisfiable (any b ≥ 0x80).
    let src = "\
(declare-fun b () (_ BitVec 8))
(assert (fp.lt ((_ to_fp 8 24) RNE b) (_ -zero 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "signed int→FP can be negative");
}

#[test]
fn to_fp_unsigned_rounding_pin_sat() {
    // u32::MAX = 4294967295 is not f32-representable; RNE rounds up to 2^32.
    // The right-hand side goes through the (independent) const-Real face.
    let src = "\
(declare-fun b () (_ BitVec 32))
(assert (= b #xffffffff))
(assert (fp.eq ((_ to_fp_unsigned 8 24) RNE b) ((_ to_fp 8 24) RNE 4294967296.0)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "u32::MAX rounds to 2^32 under RNE");
}

#[test]
fn to_fp_zero_is_plus_zero_sat() {
    // Core = distinguishes ±0: the conversion of integer 0 must be exactly +0.
    let src = "\
(declare-fun b () (_ BitVec 8))
(assert (= b #x00))
(assert (= ((_ to_fp 8 24) RTN b) (_ +zero 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "int 0 → +0 even under RTN");
}

// ── Slice-4e: FP→BV (fp.to_ubv / fp.to_sbv) now solves ──────────────────────

#[test]
fn fp_to_ubv_sat_unsat_with_model() {
    // 42.0 → ubv8 is specified: equals #x2A (any mode; exact integer).
    let (o, model) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) (declare-fun a () (_ BitVec 8)) \
         (assert (fp.eq x (fp #b0 #b10100 #b0101000000))) \
         (assert (= a ((_ fp.to_ubv 8) RTZ x))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("x") && model.contains("a"), "model surfaces both vars");
    let (o2, _) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) \
         (assert (fp.eq x (fp #b0 #b10100 #b0101000000))) \
         (assert (distinct ((_ fp.to_ubv 8) RTZ x) #x2A)) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Unsat, "42.0 → ubv8 must be exactly #x2A");
}

#[test]
fn fp_to_bv_round_then_range_boundary_trio() {
    // The z3-probed spec-§2 boundary semantics, pinned end-to-end.
    let cases = [
        // -0.5 RNE rounds to 0 → in range → specified 0.
        ("(assert (distinct ((_ fp.to_ubv 8) RNE (fp #b1 #b01110 #b0000000000)) #x00)) (check-sat)",
         SolveOutcome::Unsat),
        // 255.5 RTZ → 255 → specified #xFF.
        ("(assert (distinct ((_ fp.to_ubv 8) RTZ (fp #b0 #b10110 #b1111111100)) #xFF)) (check-sat)",
         SolveOutcome::Unsat),
        // 255.5 RNE → 256 → OUT of range → unspecified: may equal #x07.
        ("(assert (= ((_ fp.to_ubv 8) RNE (fp #b0 #b10110 #b1111111100)) #x07)) (check-sat)",
         SolveOutcome::Sat),
    ];
    for (s, want) in cases {
        let (o, _) = run(s);
        assert_eq!(o, want, "boundary pin: {s}");
    }
}

#[test]
fn fp_to_sbv_int_min_and_unspecified() {
    // -128.0 → sbv8 = #x80 (INT_MIN in range); NaN → sbv8 unconstrained.
    let (o, _) = run(
        "(assert (distinct ((_ fp.to_sbv 8) RTZ (fp #b1 #b10110 #b0000000000)) #x80)) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat, "-128.0 → sbv8 is exactly #x80");
    let (o2, _) = run(
        "(assert (= ((_ fp.to_sbv 8) RNE (_ NaN 5 11)) #x11)) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Sat, "unspecified sbv value is unconstrained (can be 0x11)");
}

#[test]
fn fp_to_bv_congruence_e2e() {
    // Probe-2 shape: equal args force equal results even when unspecified.
    let (o, _) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) (declare-fun y () (_ FloatingPoint 5 11)) \
         (assert (= x y)) (assert (fp.isNaN x)) \
         (assert (distinct ((_ fp.to_ubv 8) RNE x) ((_ fp.to_ubv 8) RNE y))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat, "congruence: equal (rm, x) → equal results");
    // Probe-1 shape: different unspecified inputs may differ.
    let (o2, _) = run(
        "(declare-fun a () (_ BitVec 8)) (declare-fun b () (_ BitVec 8)) \
         (assert (= a ((_ fp.to_ubv 8) RNE (_ NaN 5 11)))) \
         (assert (= b ((_ fp.to_ubv 8) RNE (_ +oo 5 11)))) \
         (assert (distinct a b)) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Sat, "NaN and +oo results are independent");
}

#[test]
fn fp_to_bv_under_bv_atom() {
    // First legal FP subterm under a BV atom: (bvult (fp.to_ubv …) k).
    let (o, _) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) \
         (assert (fp.eq x (fp #b0 #b10100 #b0101000000))) \
         (assert (bvult ((_ fp.to_ubv 8) RTZ x) #x10)) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat, "42 < 16 is false");
    let (o2, _) = run(
        "(declare-fun x () (_ FloatingPoint 5 11)) \
         (assert (fp.eq x (fp #b0 #b10100 #b0101000000))) \
         (assert (bvult ((_ fp.to_ubv 8) RTZ x) #x30)) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Sat, "42 < 48");
}

// ── Slice 5: FP-sorted ite + the FP n-ary =/distinct wrong-SAT family ───────

#[test]
fn fp_ite_isnan_of_non_nans_unsat() {
    let (o, _) = run(
        "(declare-const c Bool)(declare-const x Float32)(declare-const y Float32)\
         (assert (not (fp.isNaN x)))(assert (not (fp.isNaN y)))\
         (assert (fp.isNaN (ite c x y)))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_ite_isnan_sat_twin() {
    // Drop the y pin: c=false, y=NaN works.
    let (o, _) = run(
        "(declare-const c Bool)(declare-const x Float32)(declare-const y Float32)\
         (assert (not (fp.isNaN x)))\
         (assert (fp.isNaN (ite c x y)))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_ite_condition_with_fp_atom_unsat() {
    // Condition is itself an FP atom: (ite (fp.lt a b) a b) is min(a,b);
    // pinning a<b and result=b contradicts (a,b distinct non-NaN handled via lt).
    let (o, _) = run(
        "(declare-const a Float32)(declare-const b Float32)\
         (assert (fp.lt a b))\
         (assert (fp.eq (ite (fp.lt a b) a b) b))\
         (assert (not (fp.eq a b)))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_nary_distinct_three_zeros_unsat() {
    // R3 — answered sat before slice 5 (wrong-SAT): only ±0 are zero values.
    let (o, _) = run(
        "(declare-const a (_ FloatingPoint 2 2))(declare-const b (_ FloatingPoint 2 2))\
         (declare-const c (_ FloatingPoint 2 2))\
         (assert (distinct a b c))\
         (assert (fp.isZero a))(assert (fp.isZero b))(assert (fp.isZero c))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_nary_distinct_two_zeros_sat_twin() {
    let (o, _) = run(
        "(declare-const a (_ FloatingPoint 2 2))(declare-const b (_ FloatingPoint 2 2))\
         (assert (distinct a b))\
         (assert (fp.isZero a))(assert (fp.isZero b))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_nary_eq_chain_unsat() {
    // R5 — answered sat before slice 5 (wrong-SAT).
    let (o, _) = run(
        "(declare-const a Float32)(declare-const b Float32)(declare-const c Float32)\
         (assert (= a b c))(assert (distinct a c))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

// ── Slice 5: RM equality atoms + RM-sorted ite ───────────────────────────────

#[test]
fn rm_pigeonhole_six_distinct_unsat() {
    // R6 — answered sat before slice 5: RM equalities leaked to EUF, which
    // treats RoundingMode as an unbounded uninterpreted sort.
    let (o, _) = run(
        "(declare-const r RoundingMode)\
         (assert (distinct r RNE RNA RTP RTN RTZ))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn rm_pigeonhole_five_distinct_sat_twin() {
    let (o, _) = run(
        "(declare-const r RoundingMode)\
         (assert (distinct r RNE RNA RTP RTN))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat); // r = RTZ
}

#[test]
fn rm_eq_two_modes_unsat() {
    let (o, _) = run(
        "(declare-const r RoundingMode)\
         (assert (= r RNE))(assert (= r RTZ))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

// NOTE: the parser's `define-fun` macro expansion only fires for parenthesized
// calls `(name args...)`, not bare-symbol 0-ary references `name` (SMT-LIB's
// usual convention for 0-ary functions) — `resolve_leaf` never consults
// `lookup_macro`. That's a pre-existing parser gap outside this task's scope
// (fp_stage.rs + this file's RM tests only), so per the brief's fallback we
// inline the two Float32 `(fp ...)` literals at their use sites: `one` = 1.0
// (`#b0 #b01111111 #b0…0`) and `tiny` = 2^-24 (`#b0 #b01100111 #b0…0`).

#[test]
fn rm_ite_steers_rounding_unsat() {
    // (ite c RNE RTP) over 1.0 + 2^-24 (exact halfway): RNE ties-to-even →
    // exactly 1.0; RTP → 1.0 + 2^-23 ≠ 1.0. Pinning the sum to 1.0 with
    // (not c) forces RTP → contradiction. z3-confirmed both verdicts on the
    // equivalent script before pinning.
    let (o, _) = run(
        "(declare-const c Bool)\
         (assert (fp.eq (fp.add (ite c RNE RTP) \
             (fp #b0 #b01111111 #b00000000000000000000000) \
             (fp #b0 #b01100111 #b00000000000000000000000)) \
             (fp #b0 #b01111111 #b00000000000000000000000)))\
         (assert (not c))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn rm_ite_steers_rounding_sat_twin() {
    let (o, _) = run(
        "(declare-const c Bool)\
         (assert (fp.eq (fp.add (ite c RNE RTP) \
             (fp #b0 #b01111111 #b00000000000000000000000) \
             (fp #b0 #b01100111 #b00000000000000000000000)) \
             (fp #b0 #b01111111 #b00000000000000000000000)))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat); // c = true → RNE → exact 1.0
}

#[test]
fn model_never_leaks_ite_internals() {
    let (o, model) = run(
        "(declare-const c Bool)(declare-const x Float32)(declare-const y Float32)\
         (assert (fp.isNaN (ite c x y)))(check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(!model.contains("ite!"), "internal ite symbols leaked into get-model: {model}");
    // The user constants still get values.
    assert!(model.contains("(x "), "user constant x missing from model: {model}");
}
