//! End-to-end verdict pins for non-word ite elimination (slice 10).
//!
//! Before slice 10, `(ite c x y)` over Int/Real/uninterpreted/Array sorts fell
//! through word_norm untouched and reached EUF as an OPAQUE application: the
//! condition was never linked to the branches, so e.g. pure QF_LRA
//! `(= (ite b 2.5 0.25) 1.0)` answered SAT (wrong — z3: unsat; the model even
//! valued `b` as an uninterpreted-sort element `@elem0`). word_norm now
//! eliminates those ites (slice-10 design §1/§2); these tests pin the correct
//! verdicts. Word-sorted ites (slice 5) and Bool/String ites are pinned
//! unchanged.
use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Like `run`, but returns (outcome, get-model string, get-value responses).
fn run_full(src: &str) -> (SolveOutcome, String, Vec<String>) {
    let mut s = Solver::new();
    let mut p = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    let mut values = Vec::new();
    while let Some(result) = p.next_command(s.ctx_mut()) {
        let cmd = result.expect("parse");
        match s.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            CommandResponse::Values(v) => values.push(v),
            _ => {}
        }
    }
    let model = s.get_model_string();
    (outcome, model, values)
}

/// Drive a full SMT-LIB script; return the last check-sat outcome.
fn run(src: &str) -> SolveOutcome {
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
    outcome
}

/// Pure QF_LRA: the ite can only be 2.5 or 0.25, never 1.0.
#[test]
fn lra_ite_neither_branch_unsat() {
    let o = run("(declare-fun b () Bool)\
                 (assert (= (ite b 2.5 0.25) 1.0))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// SAT twin: picking the then-branch is consistent.
#[test]
fn lra_ite_then_branch_sat() {
    let o = run("(declare-fun b () Bool)\
                 (assert (= (ite b 2.5 0.25) 2.5))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

/// Pure QF_LIA twin of the LRA pin.
#[test]
fn lia_ite_neither_branch_unsat() {
    let o = run("(declare-fun b () Bool)\
                 (assert (= (ite b 2 0) 1))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// ite nested inside arithmetic: (+ (ite b 2 0) 1) ∈ {3, 1}, never 2.
#[test]
fn lia_ite_nested_in_plus_unsat() {
    let o = run("(declare-fun b () Bool)(declare-fun y () Int)\
                 (assert (= (+ (ite b 2 0) 1) y))\
                 (assert (= y 2))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// Uninterpreted sort: ite over U with pairwise-distinct u1,u2,u3.
#[test]
fn usort_ite_neither_branch_unsat() {
    let o = run("(declare-sort U 0)\
                 (declare-fun b () Bool)\
                 (declare-fun u1 () U)(declare-fun u2 () U)(declare-fun u3 () U)\
                 (assert (distinct u1 u2 u3))\
                 (assert (= (ite b u1 u2) u3))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// SAT twin over U: the then-branch is consistent.
#[test]
fn usort_ite_then_branch_sat() {
    let o = run("(declare-sort U 0)\
                 (declare-fun b () Bool)\
                 (declare-fun u1 () U)(declare-fun u2 () U)\
                 (assert (distinct u1 u2))\
                 (assert (= (ite b u1 u2) u1))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

/// Array-sorted ite on the QF_ABV path: (ite b a1 a2) selects 1 or 2 at i,
/// never 3. Pre-slice-10 this was wrong-SAT on the VALIDATED ABV path.
#[test]
fn abv_array_ite_neither_branch_unsat() {
    let o = run("(declare-fun b () Bool)\
                 (declare-fun a1 () (Array (_ BitVec 8) (_ BitVec 8)))\
                 (declare-fun a2 () (Array (_ BitVec 8) (_ BitVec 8)))\
                 (declare-fun i () (_ BitVec 8))\
                 (assert (= (select a1 i) #x01))\
                 (assert (= (select a2 i) #x02))\
                 (assert (= (select (ite b a1 a2) i) #x03))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// SAT twin on ABV.
#[test]
fn abv_array_ite_then_branch_sat() {
    let o = run("(declare-fun b () Bool)\
                 (declare-fun a1 () (Array (_ BitVec 8) (_ BitVec 8)))\
                 (declare-fun a2 () (Array (_ BitVec 8) (_ BitVec 8)))\
                 (declare-fun i () (_ BitVec 8))\
                 (assert (= (select a1 i) #x01))\
                 (assert (= (select a2 i) #x02))\
                 (assert (= (select (ite b a1 a2) i) #x01))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

/// REGRESSION PIN (correct before slice 10 too): the string path already
/// self-eliminates arith ites in shinri-str reduce_assertions (design §1.1
/// item 2). word_norm now does it first; the verdict must stay correct.
#[test]
fn string_path_arith_ite_stays_unsat() {
    let o = run("(declare-fun s () String)\
                 (assert (= (ite (= s \"a\") 2.5 0.25) 1.0))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// REGRESSION PIN: Bool-sorted ite is plain Boolean structure (Tseitin) and
/// must NOT be eliminated — b false forces the else-branch q, but q is false.
#[test]
fn bool_ite_stays_correct_unsat() {
    let o = run(
        "(declare-fun b () Bool)(declare-fun p () Bool)(declare-fun q () Bool)\
                 (assert p)(assert (not q))\
                 (assert (ite b p q))\
                 (assert (not b))\
                 (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

/// REGRESSION PIN: String-sorted ite (excluded from the broadened gate) keeps
/// its correct verdict via the existing path.
#[test]
fn string_sorted_ite_stays_unsat() {
    let o = run("(declare-fun b () Bool)\
                 (assert (= (ite b \"aa\" \"bb\") \"cc\"))\
                 (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

/// Slice 10 model channel: get-value on an eliminated Int-sorted ite must
/// answer from the EUF/arith model. b is forced true, so the ite is 2.
#[test]
fn get_value_on_eliminated_int_ite_returns_branch_value() {
    let (o, _model, values) = run_full(
        "(declare-fun b () Bool)(declare-fun y () Int)\
         (assert b)\
         (assert (= y (ite b 2 0)))\
         (check-sat)(get-value ((ite b 2 0)))",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert_eq!(values.len(), 1);
    assert!(!values[0].contains("ite!"), "internal name leaked: {}", values[0]);
    assert!(!values[0].contains('?'), "no value produced: {}", values[0]);
    assert!(values[0].contains('2'), "expected branch value 2: {}", values[0]);
}

/// Slice 10 model channel: get-model must NOT leak internal ite! symbols
/// even though they now live in the EUF/arith model.
#[test]
fn get_model_does_not_leak_arith_ite_symbols() {
    let (o, model, _values) = run_full(
        "(declare-fun b () Bool)(declare-fun y () Int)\
         (assert b)\
         (assert (= y (ite b 2 0)))\
         (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(
        !model.contains("ite!"),
        "internal symbol leaked into get-model: {model}"
    );
}
