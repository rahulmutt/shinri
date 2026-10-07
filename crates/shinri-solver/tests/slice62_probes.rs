//! Slice 62 probes (spec §7.2). Item 5: compound length arithmetic the
//! arith model never valued was skipped by the gate, so `x, y ∈ (ab)*` with
//! `len x + len y = 3` answered `sat` (z3 `unsat`). Item 3: Norn `ab` 135/138
//! need the leaf intersection's exact length bounds to reach a valid `sat`.
//! The backstop: a length used only under a UF answered `sat` with a model
//! violating it. Each `sat` witness is re-checked by pinning the `get-value`
//! answers and re-solving.
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

fn verdict(body: &str) -> String {
    run_script(&format!("{body}(check-sat)\n"))
        .into_iter()
        .find(|l| matches!(l.as_str(), "sat" | "unsat" | "unknown"))
        .expect("a verdict")
}

/// On `sat`, the `get-value` line for `vars`.
fn sat_values(body: &str, vars: &str) -> String {
    let out = run_script(&format!("{body}(check-sat)\n(get-value ({vars}))\n"));
    assert_eq!(
        out.first().map(String::as_str),
        Some("sat"),
        "{out:?}\n{body}"
    );
    out[1].clone()
}

const R11A_VARIANT: &str = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (and (<= (+ (str.len x) (str.len y)) 3) (>= (+ (str.len x) (str.len y)) 3)))
"#;

const R10: &str = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (= (+ (str.len x) (str.len y)) 3))
"#;

/// `QF_SLIA/2015-Norn/ab/norn-benchmark-135.smt2`, assertions verbatim
/// (z3 `sat`: `var_0 = "ab"`, `v = 2`).
const NORN_135: &str = r#"(set-logic QF_SLIA)
(declare-fun var_0 () String)
(declare-const v Int)
(assert (str.in_re var_0 (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(assert (str.in_re var_0 (re.++ (re.* (str.to_re "a")) (re.++ (str.to_re "b") (re.* (str.to_re "b"))))))
(assert (str.in_re var_0 (re.++ (str.to_re "a") (re.* (str.to_re "b")))))
(assert (str.in_re var_0 (re.* (re.range "a" "u"))))
(assert (and (<= 0  (str.len var_0)) (= (* v 2 ) (+ (str.len var_0) 2 ))))
"#;

/// `QF_SLIA/2015-Norn/ab/norn-benchmark-138.smt2`, assertions verbatim.
const NORN_138: &str = r#"(set-logic QF_SLIA)
(declare-fun var_4 () String)
(declare-const v Int)
(assert (str.in_re var_4 (re.++ (re.* (str.to_re "a")) (re.++ (str.to_re "b") (re.* (str.to_re "b"))))))
(assert (str.in_re var_4 (re.++ (str.to_re "a") (re.* (str.to_re "b")))))
(assert (str.in_re var_4 (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(assert (str.in_re var_4 (re.* (re.range "a" "u"))))
(assert (not (str.in_re (str.++ "a" var_4 "b" ) (str.to_re ""))))
(assert (and (<= 0  (str.len var_4)) (= (* v 2 ) (+ (str.len var_4) 2 ))))
"#;

/// The backstop's case: `len x` reaches only a UF argument (z3 `unsat`:
/// `len x` is even, ≤ 3, and `f` is 0 at 0 and 2). `main` printed
/// `sat ((x ""))`.
const UF_LEN: &str = r#"(set-logic ALL)
(declare-fun x () String)
(declare-fun f (Int) Int)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (= (f (str.len x)) 1))
(assert (= (f 0) 0))
(assert (= (f 2) 0))
(assert (<= (str.len x) 3))
"#;

/// Sibling: `f(2)` unconstrained, so `x = "ab"` is a model (z3 `sat`).
const UF_LEN_SAT: &str = r#"(set-logic ALL)
(declare-fun x () String)
(declare-fun f (Int) Int)
(assert (str.in_re x (re.* (str.to_re "ab"))))
(assert (= (f (str.len x)) 1))
(assert (= (f 0) 0))
(assert (<= (str.len x) 3))
"#;

#[test]
fn r11a_variant_not_sat() {
    assert_ne!(verdict(R11A_VARIANT), "sat");
}

#[test]
fn r10_not_sat() {
    assert_ne!(verdict(R10), "sat");
}

/// Parse `((s "w") (v k))` into (w, k).
fn word_and_int(vals: &str) -> (String, i64) {
    let w = vals.split('"').nth(1).expect("a quoted word").to_string();
    let k = vals
        .rsplit([' ', '('])
        .find_map(|t| t.trim_end_matches(')').parse::<i64>().ok())
        .expect("an Int value");
    (w, k)
}

fn norn_witness_holds(body: &str, s: &str) {
    let (w, v) = word_and_int(&sat_values(body, &format!("{s} v")));
    assert_eq!(w, "ab", "the intersection is {{ab}}");
    assert_eq!(v * 2, w.chars().count() as i64 + 2, "v·2 = len + 2");
    let pinned = format!("{body}(assert (= {s} \"{w}\"))\n(assert (= v {v}))\n");
    assert_eq!(verdict(&pinned), "sat", "pinned witness re-solves sat");
}

#[test]
fn norn_135_sat_with_valid_model() {
    norn_witness_holds(NORN_135, "var_0");
}

#[test]
fn norn_138_sat_with_valid_model() {
    norn_witness_holds(NORN_138, "var_4");
}

#[test]
fn uf_len_backstop_not_sat() {
    assert_ne!(verdict(UF_LEN), "sat");
}

#[test]
fn uf_len_backstop_sat_sibling() {
    let vals = sat_values(UF_LEN_SAT, "x");
    let w = vals.split('"').nth(1).expect("a quoted word");
    assert!(
        w == "ab",
        "the only even length ≤ 3 with f ≠ 0 is 2: {vals}"
    );
}

// Final review (Critical): the group lemma's bound atom can PRE-EXIST as a
// SAT var — here as an input atom — already false at final check, so the
// lemma `¬m₁ ∨ ¬m₂ ∨ bound` is born all-false. Pre-fix the multi-guard
// install never noticed it (`unknown`); z3 answers `unsat` on all four.

/// The R4 pin (`script_e2e::in_re_unfold_unsat_disjoint_stars`) with
/// `(>= (str.len x) 1)` spelled as the negated bound atom itself.
const R4_SIBLING: &str = r#"(set-logic QF_S)(declare-fun x () String)
(assert (str.in_re x (re.* (str.to_re "a"))))
(assert (str.in_re x (re.* (str.to_re "b"))))
(assert (not (<= (str.len x) 0)))
"#;

/// `a*b ∩ ab* = {ab}`: upper bound atom `(<= (str.len x) 2)` asserted false.
const AB_NOT_LE2: &str = r#"(set-logic QF_SLIA)(declare-fun x () String)
(assert (str.in_re x (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(assert (str.in_re x (re.++ (str.to_re "a") (re.* (str.to_re "b")))))
(assert (not (<= (str.len x) 2)))
"#;

/// Same group, lower bound atom `(>= (str.len x) 2)` asserted false.
const AB_NOT_GE2: &str = r#"(set-logic QF_SLIA)(declare-fun x () String)
(assert (str.in_re x (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(assert (str.in_re x (re.++ (str.to_re "a") (re.* (str.to_re "b")))))
(assert (not (>= (str.len x) 2)))
"#;

/// `a*(b|cc) ∩ [b-c]* = {b, cc}`: upper bound atom asserted false.
const BCC_NOT_LE2: &str = r#"(set-logic QF_S)(declare-fun x () String)
(assert (str.in_re x (re.++ (re.* (str.to_re "a")) (re.union (str.to_re "b") (str.to_re "cc")))))
(assert (str.in_re x (re.* (re.range "b" "c"))))
(assert (not (<= (str.len x) 2)))
"#;

#[test]
fn r4_sibling_negated_bound_atom_unsat() {
    assert_eq!(verdict(R4_SIBLING), "unsat");
}

#[test]
fn group_bound_atom_false_upper_unsat() {
    assert_eq!(verdict(AB_NOT_LE2), "unsat");
}

#[test]
fn group_bound_atom_false_lower_unsat() {
    assert_eq!(verdict(AB_NOT_GE2), "unsat");
}

#[test]
fn group_bound_atom_false_union_leaf_unsat() {
    assert_eq!(verdict(BCC_NOT_LE2), "unsat");
}
