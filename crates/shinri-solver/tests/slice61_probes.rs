//! Slice 61 probes (spec §7.2). The free leaves of a concat-subject
//! membership were never seeded jointly, so both reproducers answered
//! `unknown` (`str-model-rejected`, `violated:memb@not-needed`) at the branch
//! point. Each `sat` case re-checks its witness by pinning the `get-value`
//! answers and re-solving: the pinned memberships are ground and fold through
//! the slice-19 evaluator, independent of the seeding path. Each case that
//! must not be `sat` has a `sat` sibling, so the fix cannot pass by
//! refusing everything.
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

/// `QF_SLIA/2015-Norn/HammingDistance/norn-benchmark-531.smt2`, assertions
/// verbatim (z3 `sat`: `var_8 = "a"`, `var_9 = "aa"`).
const NORN_531: &str = r#"(set-logic QF_SLIA)
(declare-fun var_8 () String)
(declare-fun var_9 () String)
(assert (str.in_re (str.++ var_8 "z" var_9 ) (re.++ (re.* (re.++ (str.to_re "a") (re.++ (re.* (re.union (str.to_re "b") (str.to_re "a"))) (str.to_re "z")))) (re.++ (str.to_re "a") (re.* (re.union (str.to_re "b") (str.to_re "a")))))))
(assert (str.in_re (str.++ var_8 "z" var_9 ) (re.++ (re.* (re.union (str.to_re "z") (re.++ (str.to_re "a") (re.++ (re.* (str.to_re "a")) (str.to_re "z"))))) (re.++ (str.to_re "a") (re.* (str.to_re "a"))))))
(assert (str.in_re var_9 (re.* (re.range "a" "u"))))
(assert (str.in_re var_8 (re.* (re.range "a" "u"))))
(assert (not (str.in_re (str.++ "b" var_8 "z" "b" var_9 ) (re.++ (re.* (re.union (re.union (str.to_re "z") (str.to_re "b")) (re.++ (str.to_re "a") (re.union (str.to_re "z") (str.to_re "a"))))) (str.to_re "a")))))
"#;

/// `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-035-reverse-fuzz.smt2`
/// (z3 `sat`).
const REGEX_035: &str = r#"(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (str.in_re (str.++ y x) (re.* (str.to_re "b"))))
"#;

/// Jointly empty (z3 `unsat`); concat-subject emptiness is queued, so
/// `unknown` is expected, but never `sat`.
const JOINT_EMPTY: &str = r#"(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))
(assert (str.in_re x (re.+ (str.to_re "b"))))
"#;

const JOINT_EMPTY_SAT: &str = r#"(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "a"))))
(assert (str.in_re x (re.+ (str.to_re "a"))))
"#;

/// z3 `sat` (e.g. x = "aba", y = "b"). Pass 2 may ignore the pin; the gate
/// must then reject, never print a bad witness.
const LEN_PIN: &str = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re (str.++ x y) (re.* (str.to_re "ab"))))
(assert (= (str.len x) 3))
"#;

/// Runs `body` with `(check-sat)(get-value (vars))`; on `sat`, pins every
/// value and re-solves, returning the first verdict.
fn verdict_with_witness_check(body: &str, vars: &[&str]) -> String {
    let out = run_script(&format!(
        "{body}(check-sat)\n(get-value ({}))\n",
        vars.join(" ")
    ));
    if out[0] == "sat" {
        let values = &out[1];
        let mut pinned = body.to_string();
        for v in vars {
            let at = values.find(&format!("({v} \"")).expect("get-value shape") + v.len() + 3;
            let end = at + values[at..].find("\")").expect("closing quote");
            pinned.push_str(&format!("(assert (= {v} \"{}\"))\n", &values[at..end]));
        }
        assert_eq!(
            run_script(&format!("{pinned}(check-sat)\n")),
            vec!["sat"],
            "witness rejected: {values}"
        );
    }
    out[0].clone()
}

#[test]
fn norn_531_sat_with_valid_witness() {
    assert_eq!(
        verdict_with_witness_check(NORN_531, &["var_8", "var_9"]),
        "sat"
    );
}

#[test]
fn regex_035_sat_with_valid_witness() {
    assert_eq!(verdict_with_witness_check(REGEX_035, &["x", "y"]), "sat");
}

#[test]
fn joint_empty_not_sat() {
    assert_ne!(verdict_with_witness_check(JOINT_EMPTY, &["x", "y"]), "sat");
}

#[test]
fn joint_empty_sat_sibling() {
    assert_eq!(
        verdict_with_witness_check(JOINT_EMPTY_SAT, &["x", "y"]),
        "sat"
    );
}

#[test]
fn length_pin_sound() {
    // Never unsat (z3 sat); a sat witness is re-checked inside the helper.
    assert_ne!(verdict_with_witness_check(LEN_PIN, &["x", "y"]), "unsat");
}
