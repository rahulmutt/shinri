//! Slice 60 probes (spec §7.2). `regex::next_classes` used to cut Σ at every
//! `Range` in the regex, so a long literal under `re.+` overflowed
//! `CLASS_SPLIT_CAP` on the first derivative step: the witness search and the
//! emptiness conflict both gave up, and every case here answered `unknown`
//! (`str-model-rejected`, `violated:memb@not-needed`) at the branch point.
//! The `unsat` case has `sat` siblings so the fix cannot pass by
//! over-refuting; the `sat` cases pin the exact witness.
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

/// 40 pairwise non-adjacent printable chars ('!' + 2i): 81 cuts under the
/// old all-ranges partition, 3 under the head-only one.
const L40: &str = "!#%')+-/13579;=?ACEGIKMOQSUWY[]_acegikmo";

/// `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-010-reverse-multiply-fuzz.smt2`
/// (assertions verbatim; z3 `unsat`). The three words start with 'b', 'a',
/// 'j', so the intersection is empty after one derivative step.
const REGEX_010: &str = r#"(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (str.in_re x (re.+ (str.to_re "bba"))))
(assert (str.in_re x (re.+ (str.to_re "aaps]0e4_b{a"))))
(assert (str.in_re x (re.+ (str.to_re "j.3F&AXI'\x0c';7lLbg8[c_P1ou^uNIM-(' '%+}q'\x0c''\r''\t''\n'(CW/"))))
(check-sat)
"#;

fn shared_member_script() -> String {
    format!(
        "(set-logic QF_S)(declare-fun x () String)\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}\"))))\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}{L40}\"))))\n\
         (assert (str.in_re x (re.* (re.range \"!\" \"~\"))))\n\
         (check-sat)\n(get-value (x))\n"
    )
}

fn len_pin_script() -> String {
    format!(
        "(set-logic QF_S)(declare-fun x () String)\n\
         (assert (str.in_re x (re.+ (str.to_re \"{L40}\"))))\n\
         (assert (= (str.len x) 80))\n\
         (check-sat)\n(get-value (x))\n"
    )
}

#[test]
fn regex_010_distinct_heads_unsat() {
    assert_eq!(run_script(REGEX_010), vec!["unsat"]);
}

#[test]
fn shared_member_sat_with_witness() {
    let out = run_script(&shared_member_script());
    assert_eq!(
        out,
        vec!["sat".to_string(), format!("((x \"{L40}{L40}\"))")]
    );
}

#[test]
fn long_literal_len_pin_sat_with_witness() {
    let out = run_script(&len_pin_script());
    assert_eq!(
        out,
        vec!["sat".to_string(), format!("((x \"{L40}{L40}\"))")]
    );
}
