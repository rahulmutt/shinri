//! Fixed e2e QF_BV witnesses with known results.
//!
//! Each test asserts a specific SMT-LIB 2 formula via the text parser and
//! checks that shinri's verdict matches the known result.
//!
//! Uses the same `run_script` helper as tests/script_e2e.rs.

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

/// Run an SMT-LIB 2 script through the parser+solver and collect output lines.
fn run_script(src: &str) -> Vec<String> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut out = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match result {
            Ok(cmd) => match solver.execute(cmd) {
                CommandResponse::None => {}
                CommandResponse::Sat => out.push("sat".into()),
                CommandResponse::Unsat => out.push("unsat".into()),
                CommandResponse::Unknown => out.push("unknown".into()),
                CommandResponse::Model(s) | CommandResponse::Values(s) => out.push(s),
                CommandResponse::Error(e) => out.push(format!("(error \"{e}\")")),
            },
            Err(diag) => out.push(format!("(error \"{}\")", diag.message)),
        }
    }
    out
}

// ────────────────────────────────────────────────────────────────────────────
// 1. bvadd wrap identity (overflow)
//    (bvadd x #xff) = x  iff  x + 255 ≡ x (mod 256)  iff  255 ≡ 0 (mod 256).
//    This is FALSE for all x, so asserting equality is UNSAT.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvadd_overflow_wrap_identity_unsat() {
    // Adding 255 (= 0xff) to x in 8-bit arithmetic should never produce x
    // (that would require 255 ≡ 0 mod 256). UNSAT.
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (= (bvadd x #xff) x))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvadd by #xff cannot equal identity");
}

// ────────────────────────────────────────────────────────────────────────────
// 2. bvadd wrap: x + 1 = 0 is satisfiable (x = 0xff wraps to 0)
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvadd_wrap_sat() {
    // x + 1 = 0 in 8-bit: satisfied by x = 0xff = 255. SAT.
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (= (bvadd x #x01) #x00))\
         (check-sat)",
    );
    assert_eq!(
        out,
        vec!["sat"],
        "x + 1 = 0 mod 256 is satisfiable (x = 0xff)"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// 3. bvudiv by zero = all-ones (SMT-LIB semantics)
//    bvudiv(x, 0) is defined to be all-ones (2^n - 1) in QF_BV.
//    So (= (bvudiv x #x00) #xff) must be SAT.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvudiv_by_zero_is_all_ones_sat() {
    // QF_BV semantics: bvudiv(x, 0) = all-ones. SAT (witness: any x, e.g. x=0).
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (= (bvudiv x #x00) #xff))\
         (check-sat)",
    );
    assert_eq!(
        out,
        vec!["sat"],
        "bvudiv by zero must equal all-ones (QF_BV semantics)"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// 4. bvudiv by zero ≠ all-ones is UNSAT
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvudiv_by_zero_not_all_ones_unsat() {
    // Asserting the negation of the above: UNSAT.
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (not (= (bvudiv x #x00) #xff)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvudiv by zero must always be all-ones");
}

// ────────────────────────────────────────────────────────────────────────────
// 5. bvsdiv sign cases
//    bvsdiv(-1, 1) = -1 (signed division, -1 / 1 = -1).
//    In 8-bit: -1 = 0xff; 1 = 0x01; result = 0xff.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvsdiv_negative_dividend_sat() {
    // Asserting (= (bvsdiv #xff #x01) #xff):
    // -1 / 1 = -1 in signed 8-bit arithmetic. SAT (closed formula, no variables).
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (= (bvsdiv #xff #x01) #xff))\
         (check-sat)",
    );
    assert_eq!(
        out,
        vec!["sat"],
        "bvsdiv(-1, 1) = -1 in 8-bit signed arithmetic"
    );
}

#[test]
fn bvsdiv_positive_dividend_positive_divisor_sat() {
    // 6 / 2 = 3 in signed 8-bit. SAT.
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (= (bvsdiv #x06 #x02) #x03))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"], "bvsdiv(6, 2) = 3");
}

#[test]
fn bvsdiv_negative_negative_sat() {
    // (-6) / (-2) = 3 in signed 8-bit arithmetic.
    // -6 = 0xfa, -2 = 0xfe, result = 3 = 0x03. SAT.
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (= (bvsdiv #xfa #xfe) #x03))\
         (check-sat)",
    );
    assert_eq!(
        out,
        vec!["sat"],
        "bvsdiv(-6, -2) = 3 in 8-bit signed arithmetic"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// 6. concat / extract round-trip
//    concat(hi, lo) then extract recovers original pieces.
//    concat(#x0f, #x3c) = #x0f3c (16-bit).
//    extract[15:8](#x0f3c) = #x0f,  extract[7:0](#x0f3c) = #x3c.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn concat_produces_correct_16bit_value_sat() {
    // Concat 0x0f (hi 8 bits) and 0x3c (lo 8 bits) → 0x0f3c. SAT.
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (= (concat #x0f #x3c) #x0f3c))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"], "concat(#x0f, #x3c) = #x0f3c");
}

#[test]
fn extract_hi_bytes_sat() {
    // extract[15:8](#x0f3c) = #x0f. SAT.
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (= ((_ extract 15 8) #x0f3c) #x0f))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"], "extract[15:8](#x0f3c) = #x0f");
}

#[test]
fn extract_lo_bytes_sat() {
    // extract[7:0](#x0f3c) = #x3c. SAT.
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (= ((_ extract 7 0) #x0f3c) #x3c))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"], "extract[7:0](#x0f3c) = #x3c");
}

#[test]
fn concat_extract_round_trip_unsat() {
    // concat(extract[15:8](x), extract[7:0](x)) ≠ x is UNSAT for all 16-bit x.
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 16))\
         (assert (not (= (concat ((_ extract 15 8) x) ((_ extract 7 0) x)) x)))\
         (check-sat)",
    );
    assert_eq!(
        out,
        vec!["unsat"],
        "concat(hi(x), lo(x)) = x for all x (round-trip)"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// 7. Shift by width = 0
//    bvshl(x, n) where n >= width gives 0 (all bits shifted out).
//    For 8-bit: bvshl(x, #x08) = #x00. UNSAT to assert it's ≠ 0.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvshl_by_width_is_zero_sat() {
    // bvshl(x, 8) = 0 for all 8-bit x. SAT (for some x, e.g. x=1, result is 0).
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (= (bvshl x #x08) #x00))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"], "bvshl(x, 8) = 0 is satisfiable");
}

#[test]
fn bvshl_by_width_always_zero_unsat() {
    // (not (= (bvshl x #x08) #x00)) is UNSAT: shifting by width always produces 0.
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (not (= (bvshl x #x08) #x00)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvshl by width must always be 0");
}

#[test]
fn bvlshr_by_width_always_zero_unsat() {
    // Logical right shift by width: same result, all bits shifted out.
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (not (= (bvlshr x #x08) #x00)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvlshr by width must always be 0");
}

// ────────────────────────────────────────────────────────────────────────────
// 8. Get-model check: after SAT, model should include a value for x
//    We use the script_e2e run_script approach and check that the model
//    response is non-empty and starts with '('.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn get_model_after_sat_bv() {
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (= x #x2a))\
         (check-sat)\
         (get-model)",
    );
    // First line: "sat"
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("sat"),
        "should be sat"
    );
    // Second line: the model — should start with '(' and contain a BV value.
    assert!(
        out.len() >= 2,
        "get-model should produce a second line, got: {out:?}"
    );
    let model = &out[1];
    assert!(
        model.starts_with('('),
        "model output should start with '(', got: {model}"
    );
    // The model should contain something referencing #x2a (42 in hex = 0x2a).
    // Accept either the exact hex value or the decimal representation.
    let contains_val = model.contains("#x2a") || model.contains("42");
    assert!(
        contains_val,
        "model should contain x=0x2a (42), got: {model}"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// 9. bvnot double-negation identity
//    bvnot(bvnot(x)) = x for all x. UNSAT to assert the negation.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvnot_double_negation_unsat() {
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (not (= (bvnot (bvnot x)) x)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvnot(bvnot(x)) = x for all x");
}

// ────────────────────────────────────────────────────────────────────────────
// 10. bvand with all-ones is identity
//     bvand(x, #xff) = x for all 8-bit x. UNSAT to assert the negation.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvand_all_ones_identity_unsat() {
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (not (= (bvand x #xff) x)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvand(x, 0xff) = x for all x");
}

// ────────────────────────────────────────────────────────────────────────────
// 11. bvor with zero is identity
//     bvor(x, #x00) = x for all 8-bit x. UNSAT to assert the negation.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvor_zero_identity_unsat() {
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (not (= (bvor x #x00) x)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvor(x, 0x00) = x for all x");
}

// ────────────────────────────────────────────────────────────────────────────
// 12. bvxor self-inverse
//     bvxor(x, x) = 0 for all x. UNSAT to assert the negation.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvxor_self_is_zero_unsat() {
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (not (= (bvxor x x) #x00)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvxor(x, x) = 0 for all x");
}

// ────────────────────────────────────────────────────────────────────────────
// 13. Unsigned comparisons: #x00 bvult #x01 is a tautology
//     (not (bvult #x00 #x01)) is UNSAT.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvult_zero_lt_one_unsat() {
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (not (bvult #x00 #x01)))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvult(0, 1) is always true");
}

// ────────────────────────────────────────────────────────────────────────────
// 14. Signed comparison: #x80 (= -128) bvslt #x00 (= 0) is a tautology
//     (not (bvslt #x80 #x00)) is UNSAT.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvslt_min_lt_zero_unsat() {
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (not (bvslt #x80 #x00)))\
         (check-sat)",
    );
    assert_eq!(
        out,
        vec!["unsat"],
        "bvslt(-128, 0) is always true in 8-bit signed"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// 15. zero_extend then extract round-trip
//     zero_extend(4, x) produces a 12-bit value; extract[7:0] recovers x.
//     (not (= ((_ extract 7 0) ((_ zero_extend 4) x)) x)) is UNSAT.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn zero_extend_extract_round_trip_unsat() {
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (assert (not (= ((_ extract 7 0) ((_ zero_extend 4) x)) x)))\
         (check-sat)",
    );
    assert_eq!(
        out,
        vec!["unsat"],
        "extract[7:0](zero_extend(4, x)) = x for all 8-bit x"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// 16. bvmul commutativity: bvmul(x,y) = bvmul(y,x). UNSAT to assert negation.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvmul_commutativity_unsat() {
    let out = run_script(
        "(set-logic QF_BV)\
         (declare-fun x () (_ BitVec 8))\
         (declare-fun y () (_ BitVec 8))\
         (assert (not (= (bvmul x y) (bvmul y x))))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"], "bvmul is commutative");
}

// ────────────────────────────────────────────────────────────────────────────
// 17. bvurem: x = bvadd(bvmul(bvudiv(x,y), y), bvurem(x,y)) when y ≠ 0
//     This is the Euclidean identity for unsigned remainder.
//     We test it as a specific numeric case: 13 / 5 = 2 remainder 3.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn bvurem_euclidean_identity_sat() {
    // 13 / 5 = 2 (unsigned), 5 * 2 + 3 = 13. SAT.
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (= (bvurem #x0d #x05) #x03))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"], "bvurem(13, 5) = 3");
}

// ────────────────────────────────────────────────────────────────────────────
// 18. sign_extend: sign_extend(8, #xf0) = #xfff0 (sign bit 1 → extend with 1s)
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn sign_extend_negative_sat() {
    // #xf0 in 8 bits has MSB=1. sign_extend(8, #xf0) = #xfff0.
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (= ((_ sign_extend 8) #xf0) #xfff0))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"], "sign_extend(8, 0xf0) = 0xfff0");
}

#[test]
fn sign_extend_positive_sat() {
    // #x0f in 8 bits has MSB=0. sign_extend(8, #x0f) = #x000f.
    let out = run_script(
        "(set-logic QF_BV)\
         (assert (= ((_ sign_extend 8) #x0f) #x000f))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"], "sign_extend(8, 0x0f) = 0x000f");
}
