//! Slice 52 probes (spec §8). They pin the Noetzli wrong-`sat` pair and its
//! reduced reproducers.
//!
//! Written BEFORE the implementation. On `main` (`7bd2279`) every `unsat` pin
//! fails: `sat` for the Bool-`=`/`distinct`/proxy forms, and `unknown`
//! (`str-model-rejected`) for R1, R2 and `xor`. The SAT controls pass, and
//! each control's model is re-checked here by hand. z3 4.16.0 confirms
//! `noetzli_370`, `noetzli_458`, `r1_unit_diseq`, `distinct_form`, `xor_form`,
//! `not_distinct_form`, and `bool_proxy` are unsat. `ab_prefix_h2` is sat in z3
//! with a bogus model (H2 queued hole); shinri today produces the same bogus sat;
//! after Task 2 the gate turns that into a sound `unknown`.
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

const XY: &str = "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)";

fn verdict(body: &str) -> String {
    let out = run_script(&format!("{XY}{body}(check-sat)"));
    out.first().cloned().unwrap_or_default()
}

/// The value of String variable `name` in a `(get-model)` response. The
/// controls only use `A`, `B` and the empty string, so no escape handling.
fn model_str(model: &str, name: &str) -> String {
    let key = format!("(define-fun {name} () String \"");
    let start = model
        .find(&key)
        .unwrap_or_else(|| panic!("{name} missing: {model}"))
        + key.len();
    let end = start + model[start..].find('"').expect("closing quote");
    model[start..end].to_owned()
}

fn sat_model(body: &str) -> (String, String) {
    let out = run_script(&format!(
        "(set-option :produce-models true){XY}{body}(check-sat)(get-model)"
    ));
    assert_eq!(out[0], "sat", "control must be sat: {out:?}");
    (model_str(&out[1], "x"), model_str(&out[1], "y"))
}

/// Corpus row `str-pred-small-rw_370.smt2`. z3: unsat.
#[test]
fn noetzli_370() {
    assert_eq!(
        verdict(r#"(assert (not (= (= "A" (str.++ y x)) (= "A" (str.++ x y)))))"#),
        "unsat"
    );
}

/// Corpus row `str-pred-small-rw_458.smt2`. z3: unsat.
#[test]
fn noetzli_458() {
    assert_eq!(
        verdict(r#"(assert (not (= (= "B" (str.++ y x)) (= "B" (str.++ x y)))))"#),
        "unsat"
    );
}

/// R1 (spec §1.2): H1 shape, top-level literals only. z3: unsat.
#[test]
fn r1_unit_diseq() {
    assert_eq!(
        verdict(r#"(assert (= "A" (str.++ y x)))(assert (not (= "A" (str.++ x y))))"#),
        "unsat"
    );
}

/// R2 (spec §1.2): the char-peel leaves `[] = [!strk0, x]`. z3: unsat.
#[test]
fn r2_both_vars_diseq() {
    assert_eq!(
        verdict(r#"(assert (= "A" (str.++ y x)))(assert (not (= "A" x)))(assert (not (= "A" y)))"#),
        "unsat"
    );
}

#[test]
fn distinct_form() {
    assert_eq!(
        verdict(r#"(assert (distinct (= "A" (str.++ y x)) (= "A" (str.++ x y))))"#),
        "unsat"
    );
}

#[test]
fn xor_form() {
    assert_eq!(
        verdict(r#"(assert (xor (= "A" (str.++ y x)) (= "A" (str.++ x y))))"#),
        "unsat"
    );
}

/// Stays red (returns `sat`) through Tasks 2 and 3: the gate cannot evaluate the
/// Bool constant `p` (spec §9 audit). It turns green (unsat) at Task 4 (H3).
#[test]
fn bool_proxy() {
    assert_eq!(
        verdict(
            r#"(declare-fun p () Bool)(assert (= p (= "A" (str.++ y x))))
               (assert (not (= p (= "A" (str.++ x y)))))"#
        ),
        "unsat"
    );
}

/// Review Focus 5: a `distinct` atom asserted false (`¬distinct ≡ =`) lands in
/// `eq_true` and must get the same own-literal exemption. z3: unsat.
#[test]
fn not_distinct_form() {
    assert_eq!(
        verdict(r#"(assert (not (= (not (distinct "A" (str.++ y x))) (= "A" (str.++ x y)))))"#),
        "unsat"
    );
}

/// Soundness check for H2 (constant-prefix residual, queued per spec §9). z3 says
/// sat with a valid model (x="B", y="A"). shinri today produces a bogus sat with an
/// invalid model. After Task 2 the gate turns that into a sound `unknown`. If a later
/// slice solves H2, it will produce a correct `sat` or `unsat`.
#[test]
fn ab_prefix_h2() {
    let out = run_script(&format!(
        "(set-option :produce-models true){XY}(assert (not (= (= \"AB\" (str.++ y x)) (= \"AB\" (str.++ x y)))))(check-sat)(get-model)"
    ));
    let verdict = out.first().cloned().unwrap_or_default();
    assert_ne!(verdict, "unsat");
    if verdict == "sat" {
        let model = &out[1];
        let x = model_str(model, "x");
        let y = model_str(model, "y");
        // With z3's model (x="B", y="A"): y++x="AB", x++y="BA".
        // Assertion: ¬((y++x="AB") = (x++y="AB"))
        // ≡ ¬(true = false) ≡ ¬false ≡ true ✓
        assert_ne!(
            format!("{y}{x}") == "AB",
            format!("{x}{y}") == "AB",
            "model must satisfy the assertion: y={y}, x={x}"
        );
    }
}

#[test]
fn ctrl_single_eq() {
    let (x, y) = sat_model(r#"(assert (= "A" (str.++ y x)))"#);
    assert_eq!(format!("{y}{x}"), "A");
}

#[test]
fn ctrl_both_empty_ok() {
    let (x, y) = sat_model(r#"(assert (= "" (str.++ y x)))(assert (= "" (str.++ x y)))"#);
    assert_eq!((x.as_str(), y.as_str()), ("", ""));
}

/// Review Focus 1: a genuine `sat` whose Bool `=` the gate now evaluates.
#[test]
fn ctrl_iff_true() {
    let (x, y) = sat_model(r#"(assert (= (= "A" (str.++ y x)) (= "A" (str.++ x y))))"#);
    assert_eq!(format!("{y}{x}") == "A", format!("{x}{y}") == "A");
}

/// Review Focus 3 end to end: `"" = x ++ x` forces `x = ""`.
#[test]
fn ctrl_repeated_var() {
    let (x, _y) = sat_model(r#"(assert (= "" (str.++ x x y)))"#);
    assert_eq!(x, "");
}
