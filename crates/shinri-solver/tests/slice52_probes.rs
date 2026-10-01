//! Slice 52 probes (spec §8). They pin the Noetzli wrong-`sat` pair and its
//! reduced reproducers.
//!
//! Final state under the agreed fallback (Ruling R15): H3 (the word-equation
//! gate own-literal/diseq exemption) was dropped because it cost 309 correct
//! `sat` rows (now `unknown:sat-budget`) on the bench; it is queued. So the
//! Bool-`=`/`distinct`/`xor` forms (`noetzli_370`, `noetzli_458`,
//! `not_distinct_form`, `distinct_form`, `xor_form`) are pinned "not sat": z3
//! says unsat and the T2 gate turns the bogus model into a sound
//! `unknown:str-model-rejected`. R1, R2, the H1 length-link probes and every
//! `ctrl_*` hold. `bool_proxy` is a known wrong `sat` (the gate cannot
//! evaluate the Bool constant `p`), pinned as a passing known-bug marker
//! (asserts the wrong `sat`; flip it to `unsat` when the fix lands).
//! `ab_prefix_h2` is sat in z3 (valid model x="B", y="A"); shinri's bogus
//! model is turned into a sound `unknown` by the T2 gate; it is a soundness
//! check (H2 queued).
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

/// Corpus row `str-pred-small-rw_370.smt2`. z3: unsat. The T2 gate turns the bogus model into a sound
/// `unknown:str-model-rejected`; H3 (the word-equation gate own-literal/diseq
/// exemption) was dropped under the agreed fallback because it cost 309
/// correct `sat` rows (unknown:sat-budget) on the bench; it is queued.
#[test]
fn noetzli_370() {
    assert_ne!(
        verdict(r#"(assert (not (= (= "A" (str.++ y x)) (= "A" (str.++ x y)))))"#),
        "sat"
    );
}

/// Corpus row `str-pred-small-rw_458.smt2`. z3: unsat. The T2 gate turns the bogus model into a sound
/// `unknown:str-model-rejected`; H3 (the word-equation gate own-literal/diseq
/// exemption) was dropped under the agreed fallback because it cost 309
/// correct `sat` rows (unknown:sat-budget) on the bench; it is queued.
#[test]
fn noetzli_458() {
    assert_ne!(
        verdict(r#"(assert (not (= (= "B" (str.++ y x)) (= "B" (str.++ x y)))))"#),
        "sat"
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

/// `distinct` form of the pair. z3: unsat. The T2 gate turns the bogus model into a sound
/// `unknown:str-model-rejected`; H3 (the word-equation gate own-literal/diseq
/// exemption) was dropped under the agreed fallback because it cost 309
/// correct `sat` rows (unknown:sat-budget) on the bench; it is queued.
#[test]
fn distinct_form() {
    assert_ne!(
        verdict(r#"(assert (distinct (= "A" (str.++ y x)) (= "A" (str.++ x y))))"#),
        "sat"
    );
}

/// `xor` form of the pair. z3: unsat. The T2 gate turns the bogus model into a sound
/// `unknown:str-model-rejected`; H3 (the word-equation gate own-literal/diseq
/// exemption) was dropped under the agreed fallback because it cost 309
/// correct `sat` rows (unknown:sat-budget) on the bench; it is queued.
#[test]
fn xor_form() {
    assert_ne!(
        verdict(r#"(assert (xor (= "A" (str.++ y x)) (= "A" (str.++ x y))))"#),
        "sat"
    );
}

/// KNOWN WRONG SAT (z3: unsat), pinned as a passing marker (R16): the gate
/// cannot evaluate the Bool constant `p` (the `eval_bool` audit, spec §9), and
/// H3 was dropped under the agreed fallback. Flip this pin to `unsat` when the
/// audit or a narrowed H3 + the deep-nf propagate (R11) lands. Not `#[ignore]`d:
/// the nightly tier runs ignored tests and AGENTS.md reserves `#[ignore]` for
/// slow tests.
#[test]
fn bool_proxy() {
    assert_eq!(
        verdict(
            r#"(declare-fun p () Bool)(assert (= p (= "A" (str.++ y x))))
               (assert (not (= p (= "A" (str.++ x y)))))"#
        ),
        "sat",
        "KNOWN WRONG SAT (z3: unsat): flip this pin to unsat when the eval_bool Bool-constant audit or a narrowed H3 + deep-nf propagate lands"
    );
}

/// Review Focus 5: a `distinct` atom asserted false (`¬distinct ≡ =`) lands in
/// `eq_true`. z3: unsat. Pinned "not sat": the T2 gate turns the bogus model
/// into a sound `unknown:str-model-rejected`. The own-literal exemption that
/// would give `unsat` was H3, which was reverted (it cost 309 correct `sat`
/// rows on the bench) and is queued.
#[test]
fn not_distinct_form() {
    assert_ne!(
        verdict(r#"(assert (not (= (not (distinct "A" (str.++ y x))) (= "A" (str.++ x y)))))"#),
        "sat"
    );
}

/// Soundness check for H2 (constant-prefix residual, queued per spec §9). z3 says
/// sat with a valid model (x="B", y="A"). shinri's bogus model is invalid; since Task 2 the
/// gate turns it into a sound `unknown`. If a later
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
        // Check if shinri's model satisfies the assertion.
        // z3's valid model (x="B", y="A"): y++x="AB", x++y="BA",
        // ¬((y++x="AB") = (x++y="AB")) ≡ ¬(true = false) ≡ true ✓
        // shinri's bogus model today does not satisfy this check.
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

/// H1 must not hide a string/arith length conflict. z3: unsat (`len y = 0`
/// forces `x = "A"`, contradicting `x != "A"`). Must never be `sat`.
#[test]
fn h1_len_linked_not_sat() {
    let v = verdict(
        r#"(assert (= "A" (str.++ y x)))(assert (= (+ (str.len y) 1) 1))(assert (not (= x "A")))"#,
    );
    assert_ne!(v, "sat", "wrong sat: len y = 0 is violated by any model");
}

/// Satisfiable variant: the only model is y = "" and x = "A". H1 links
/// len(v) = 0 to arith after each merge into "", so this stays sat.
#[test]
fn ctrl_h1_len_linked() {
    let (x, y) = sat_model(r#"(assert (= "A" (str.++ y x)))(assert (= (+ (str.len y) 1) 1))"#);
    assert_eq!((x.as_str(), y.as_str()), ("A", ""));
}
