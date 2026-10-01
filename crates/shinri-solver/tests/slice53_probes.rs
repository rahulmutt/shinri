//! Slice 53 probes (spec §6.2). An Int/Real `(= a b)` atom used to be lowered
//! to `(and E Le Ge)`, which is only equivalent in positive positions; under
//! `not (or …)`, `=>`, Bool `=` or a negated `ite` the SAT solver could falsify
//! `E` alone (wrong `sat`). Every `*_unsat` case here was `sat` at `2ceef06`
//! unless marked "regression pin". Each has a `sat` sibling so the fix cannot
//! pass by over-refuting.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

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

const INT: &str = "(set-logic QF_LIA)(declare-fun p () Bool)\
    (declare-fun x () Int)(declare-fun y () Int)";
const REAL: &str = "(set-logic QF_LRA)(declare-fun p () Bool)\
    (declare-fun x () Real)(declare-fun y () Real)";

fn verdict(header: &str, body: &str) -> String {
    let out = run_script(&format!("{header}{body}(check-sat)"));
    out.first().cloned().unwrap_or_default()
}

/// Asserts `body` is unsat and `sibling` (one constraint relaxed) is sat,
/// under both the Int and the Real header.
fn both_sorts(body: &str, sibling: &str) {
    for h in [INT, REAL] {
        assert_eq!(verdict(h, body), "unsat", "{h}{body}");
        assert_eq!(verdict(h, sibling), "sat", "{h}{sibling}");
    }
}

#[test]
fn demorgan_negated_or() {
    both_sorts(
        "(assert (not (or (= x 1) p)))(assert (>= x 1))(assert (<= x 1))",
        "(assert (not (or (= x 1) p)))(assert (>= x 1))(assert (<= x 2))",
    );
}

#[test]
fn negated_implication() {
    both_sorts(
        "(assert (not (=> (= x 1) (= (- x 1) 0))))",
        "(assert (not (=> (= x 1) (= (- x 1) 1))))",
    );
}

#[test]
fn bool_iff_over_arith_eq() {
    both_sorts(
        "(assert (= x 1))(assert (= p (= x 2)))(assert p)",
        "(assert (= x 1))(assert (= p (= x 2)))(assert (not p))",
    );
}

#[test]
fn negated_ite_branches() {
    both_sorts(
        "(assert (>= x 1))(assert (<= x 1))(assert (not (ite p (= x 1) (= x 1))))",
        "(assert (>= x 1))(assert (<= x 2))(assert (not (ite p (= x 1) (= x 1))))",
    );
}

/// Regression pin: already unsat at `2ceef06`.
#[test]
fn xor_over_arith_eq() {
    both_sorts(
        "(assert (= x 1))(assert (xor p (= x 1)))(assert p)",
        "(assert (= x 1))(assert (xor p (= x 1)))(assert (not p))",
    );
}

/// Regression pin: term-level `ite` conditions are lifted by `word_norm`.
/// The Real case spells the branches `1.0`/`0.0`: an Int-literal `ite` in
/// QF_LRA is `unknown` independently of this slice (pre-existing, see report).
#[test]
fn term_ite_condition() {
    for (h, one, zero) in [(INT, "1", "0"), (REAL, "1.0", "0.0")] {
        let body = |x: &str| {
            format!("(assert (= x {x}))(assert (< (ite (= x {one}) {one} {zero}) {one}))")
        };
        assert_eq!(verdict(h, &body(one)), "unsat", "{h}");
        assert_eq!(
            verdict(h, &body(if one == "1" { "2" } else { "2.0" })),
            "sat",
            "{h}"
        );
    }
}

/// Review Focus 5: n-ary `=` under `=>` (collector must match `lower`'s pairs).
/// Regression pin: already correct at `2ceef06` (the old shape happened to be sound here).
#[test]
fn nary_eq_under_implication() {
    both_sorts(
        "(assert (= x 1))(assert (= y 1))(assert (not (=> p (= x y 1))))(assert p)",
        "(assert (= x 1))(assert (= y 2))(assert (not (=> p (= x y 1))))(assert p)",
    );
}

/// Review Focus 4: a fractional Real solution under De Morgan.
#[test]
fn real_fractional_eq_under_demorgan() {
    let body = "(assert (not (or (= (* 2 x) 1) p)))(assert (>= x 0.5))(assert (<= x 0.5))";
    let sib = "(assert (not (or (= (* 2 x) 1) p)))(assert (>= x 0.5))(assert (<= x 1.0))";
    assert_eq!(verdict(REAL, body), "unsat");
    assert_eq!(verdict(REAL, sib), "sat");
}

/// EUF must still see `x = y` (it is an argument of `f`) under `=>`.
/// Regression pin: already correct at `2ceef06` (the old shape happened to be sound here).
#[test]
fn uflia_congruence_under_implication() {
    let h = "(set-logic QF_UFLIA)(declare-fun f (Int) Int)\
        (declare-fun x () Int)(declare-fun y () Int)(declare-fun p () Bool)";
    assert_eq!(
        verdict(
            h,
            "(assert p)(assert (=> p (= x y)))(assert (distinct (f x) (f y)))"
        ),
        "unsat"
    );
    assert_eq!(
        verdict(
            h,
            "(assert (not p))(assert (=> p (= x y)))(assert (distinct (f x) (f y)))"
        ),
        "sat"
    );
}

/// Review Focus 3: `str.len` equality under De Morgan; the string model gate
/// must not see the axiom clauses.
/// Regression pin: already correct at `2ceef06` (the old shape happened to be sound here).
#[test]
fn slia_len_eq_under_demorgan() {
    let h = "(set-logic QF_SLIA)(declare-fun s () String)(declare-fun p () Bool)";
    assert_eq!(
        verdict(
            h,
            "(assert (= s \"ab\"))(assert (not (or (= (str.len s) 2) p)))"
        ),
        "unsat"
    );
    assert_eq!(
        verdict(
            h,
            "(assert (= s \"abc\"))(assert (not (or (= (str.len s) 2) p)))"
        ),
        "sat"
    );
}

/// Review Focus 1: the popped scope's negated equality must not leak.
#[test]
fn push_pop_negated_eq_does_not_leak() {
    let out = run_script(&format!(
        "{INT}(push 1)(assert (not (or (= x 1) p)))(check-sat)(pop 1)\
         (assert (= x 1))(check-sat)"
    ));
    assert_eq!(out, vec!["sat".to_string(), "sat".to_string()]);
}

/// Review Focus 2: the model must satisfy `x = 1` and `y ≠ 2`.
#[test]
fn implication_sat_model_respects_negated_eq() {
    let out = run_script(&format!(
        "(set-option :produce-models true){INT}\
         (assert (not (=> (= x 1) (= y 2))))(check-sat)(get-value (x y))"
    ));
    assert_eq!(out[0], "sat");
    let v = out[1].replace(char::is_whitespace, "");
    assert!(v.contains("(x1)"), "x must be 1: {}", out[1]);
    assert!(!v.contains("(y2)"), "y must not be 2: {}", out[1]);
}

const KEYMAERA_2074: &str = r#"(set-logic QF_LRA)
(declare-fun e () Real)
(declare-fun buscore2dollarskuscore0 () Real)
(declare-fun auscore2dollarskuscore0 () Real)
(declare-fun cuscore2dollarskuscore0 () Real)
(assert (let ((?v_0 (* 5 auscore2dollarskuscore0)) (?v_1 (* 3 buscore2dollarskuscore0))) (not (=> (and (= e 0) (= (+ (+ ?v_0 ?v_1) cuscore2dollarskuscore0) 10)) (= (+ (+ (- ?v_0 5) (+ ?v_1 6)) (- cuscore2dollarskuscore0 1)) 10)))))"#;
const KEYMAERA_2406: &str = r#"(set-logic QF_LRA)
(declare-fun e () Real)
(declare-fun buscore2dollarskuscore1 () Real)
(declare-fun cuscore2dollarskuscore1 () Real)
(declare-fun auscore2dollarskuscore1 () Real)
(assert (let ((?v_0 (* 5 auscore2dollarskuscore1)) (?v_1 (* 3 buscore2dollarskuscore1))) (not (=> (= (+ (+ ?v_0 ?v_1) cuscore2dollarskuscore1) 10) (or (= e 0) (= (+ (+ (+ ?v_0 5) (- ?v_1 3)) (- cuscore2dollarskuscore1 2)) 10))))))"#;

/// Corpus rows `QF_LRA/keymaera/simple_example_2-node{2074,2406}.smt2`
/// (`:status unsat`, z3 unsat; shinri `sat` at `2ceef06`).
#[test]
fn keymaera_rows() {
    for src in [KEYMAERA_2074, KEYMAERA_2406] {
        assert_eq!(
            run_script(&format!("{src}(check-sat)")),
            vec!["unsat".to_string()]
        );
    }
}

/// Corpus row `QF_BVFP/ramalho/esbmc/Float-no-simp9-main.smt2` (z3 unsat;
/// shinri `sat` at `2ceef06`), minimized. Cause: `fp.add` gave `(+0)+(+0) = -0`
/// under roundTowardNegative (IEEE 754 §6.3: a same-sign zero sum keeps its
/// sign; only an opposite-sign exact-zero sum is -0 under RTN), so ESBMC's
/// `signbit(+0.0 + +0.0)` could be 1 when the rounding mode was RTN.
#[test]
fn ramalho_min_core() {
    const SRC: &str = r#"(set-logic QF_BVFP)
(declare-fun v0 () (_ BitVec 32))
(declare-fun v1 () (_ FloatingPoint 11 53))
(declare-fun v2 () Bool)
(declare-fun v3 () (_ BitVec 32))
(declare-fun v4 () Bool)
(declare-fun v5 () Bool)
(declare-fun v6 () (_ FloatingPoint 11 53))
(declare-fun v7 () (_ BitVec 32))
(declare-fun v8 () (_ BitVec 32))
(declare-fun v9 () (_ BitVec 32))
(declare-fun v10 () Bool)
(declare-fun v11 () (_ FloatingPoint 11 53))
(declare-fun v12 () (_ BitVec 32))
(declare-fun v13 () (_ BitVec 32))
(declare-fun v14 () (_ BitVec 32))
(declare-fun v15 () Bool)
(declare-fun v16 () (_ BitVec 32))
(assert (let ((a!1 (ite (= v0 #x00000000) roundNearestTiesToEven (ite (= v0 #x00000001) roundTowardNegative (ite (= v0 #x00000002) roundTowardPositive roundTowardZero))))) (= (fp.add a!1 (fp #b0 #b00000000000 #x0000000000000) (fp #b0 #b00000000000 #x0000000000000)) v1)))
(assert (= (= #x00000008 #x00000004) v2))
(assert (let ((a!1 (not (not v4)))) (= a!1 v5)))
(assert (= v1 v6))
(assert (= (ite (fp.isNegative v6) #x00000001 #x00000000) v7))
(assert (= (ite (not v5) v9 v7) v8))
(assert (let ((a!1 (not (not (not v4))))) (= a!1 v10)))
(assert (= v1 v11))
(assert (= (ite (fp.isNegative v11) #x00000001 #x00000000) v12))
(assert (= (ite (not v10) v14 v12) v13))
(assert (= (= (ite v2 v3 (ite v4 v8 v13)) #x00000000) v15))
(assert (not (=> (not v15) false)))"#;
    assert_eq!(
        run_script(&format!("{SRC}(check-sat)")),
        vec!["unsat".to_string()]
    );
    // sat sibling: the same core without the negated claim stays satisfiable.
    let sat_src = SRC.replace("(assert (not (=> (not v15) false)))", "");
    assert_ne!(sat_src, SRC);
    assert_eq!(
        run_script(&format!("{sat_src}(check-sat)")),
        vec!["sat".to_string()]
    );
}
