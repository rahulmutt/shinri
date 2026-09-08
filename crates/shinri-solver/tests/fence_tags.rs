//! Slice 46: every `unknown` from `check_sat` carries a fence tag naming the
//! guard that produced it; decided answers carry none.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

/// Run a script; return (last check-sat response, last fence tag).
fn run(src: &str) -> (Option<CommandResponse>, Option<&'static str>) {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut last = None;
    while let Some(r) = parser.next_command(solver.ctx_mut()) {
        let cmd = r.expect("fixture parses");
        let resp = solver.execute(cmd);
        if !matches!(resp, CommandResponse::None) {
            last = Some(resp);
        }
    }
    let tag = solver.last_fence();
    (last, tag)
}

#[test]
fn decided_sat_has_no_fence() {
    let (r, tag) = run("(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 0.0))(check-sat)");
    assert!(matches!(r, Some(CommandResponse::Sat)));
    assert_eq!(tag, None);
}

#[test]
fn decided_unsat_has_no_fence() {
    let (r, tag) = run(
        "(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 0.0))(assert (< x 0.0))(check-sat)",
    );
    assert!(matches!(r, Some(CommandResponse::Unsat)));
    assert_eq!(tag, None);
}

#[test]
fn reglan_declaration_is_tagged() {
    let (r, tag) = run("(set-logic QF_S)(declare-fun r () RegLan)(check-sat)");
    assert!(matches!(r, Some(CommandResponse::Unknown)));
    assert_eq!(tag, Some("reglan-decl"));
}

#[test]
fn symbolic_str_order_is_tagged() {
    // Slice 31: two-free-variable str.< is deliberately fenced.
    let (r, tag) = run(
        "(set-logic QF_S)(declare-fun a () String)(declare-fun b () String)\
         (assert (str.< a b))(check-sat)",
    );
    assert!(matches!(r, Some(CommandResponse::Unknown)));
    assert_eq!(tag, Some("str-order"));
}

#[test]
fn bv_mixed_with_int_is_tagged() {
    let (r, tag) = run(
        "(set-logic QF_BV)(declare-fun x () (_ BitVec 8))(declare-fun i () Int)\
         (assert (= x #x01))(assert (> i 0))(check-sat)",
    );
    assert!(matches!(r, Some(CommandResponse::Unknown)));
    assert_eq!(tag, Some("bv-non-bv-atom"));
}

#[test]
fn fence_is_cleared_by_the_next_check_sat() {
    let mut solver = Solver::new();
    let mut parser = Parser::new(
        "(set-logic QF_S)(declare-fun a () String)(declare-fun b () String)\
         (push 1)(assert (str.< a b))(check-sat)(pop 1)\
         (assert (= a \"x\"))(check-sat)",
    );
    let mut answers = Vec::new();
    while let Some(r) = parser.next_command(solver.ctx_mut()) {
        match solver.execute(r.unwrap()) {
            CommandResponse::None => {}
            other => answers.push((other, solver.last_fence())),
        }
    }
    assert!(matches!(answers[0].0, CommandResponse::Unknown));
    assert_eq!(answers[0].1, Some("str-order"));
    assert!(matches!(answers[1].0, CommandResponse::Sat));
    assert_eq!(answers[1].1, None);
}
