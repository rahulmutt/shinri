//! End-to-end QF_DT witnesses: SMT-LIB text -> parser -> solver.
//! Covers selector-collapse, injectivity (a dedicated selector-instantiation
//! rule plants the field selectors, and collapse + EUF congruence close over
//! them), constructor disjointness, tester consistency, and the slice-39
//! completeness fence.

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

const LIST: &str = "(declare-datatype List ((nil) (cons (head Int) (tail List))))";

#[test]
fn selector_over_constructor_unsat() {
    // head(cons(1, nil)) != 1  is UNSAT
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (assert (distinct (head (cons 1 nil)) 1))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn constructor_disjointness_unsat() {
    // x = nil  and  x = cons(1, nil)  is UNSAT
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (= x nil))(assert (= x (cons 1 nil)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn injectivity_unsat() {
    // cons(a, nil) = cons(b, nil)  and  a != b  is UNSAT.
    // The dedicated injectivity rule (`instantiate_injectivity_selectors`)
    // plants the head/tail selector applications on both constructor apps;
    // collapse lemmas + EUF congruence over cons(a,nil) = cons(b,nil) then
    // close over them to derive a = b, contradicting a != b.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (declare-fun a () Int)(declare-fun b () Int)\
         (assert (= (cons a nil) (cons b nil)))(assert (distinct a b))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn injectivity_branch_local_stays_sat() {
    // Wrong-UNSAT regression for the injectivity rule. The injective
    // consequence `a = b` is CONDITIONAL on `cons(a,nil) ≡ cons(b,nil)`, which
    // here holds only if the SAT layer picks the equality disjunct. Taking
    // `p = true` with the equality false leaves `a ≠ b` satisfiable, so the
    // query is SAT. If the injectivity rule pinned `a = b` (or the collapse
    // consequence chain) at level 0 rather than deriving it inside EUF's
    // congruence — retracted when the `cons ≡ cons` merge is backtracked — this
    // would wrongly report unsat.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (declare-fun a () Int)(declare-fun b () Int)(declare-fun p () Bool)\
         (assert (or (= (cons a nil) (cons b nil)) p))(assert (distinct a b))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn injectivity_transitive_diseq_unsat() {
    // Injectivity composed with EUF transitivity: cons(a,nil) = cons(b,nil)
    // forces a = b; with b = c and a ≠ c that is a contradiction. The a = b
    // consequence emerges via selector-collapse + congruence, and EUF supplies
    // the transitive a = b = c ≠ a conflict.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (declare-fun a () Int)(declare-fun b () Int)(declare-fun c () Int)\
         (assert (= (cons a nil) (cons b nil)))(assert (= b c))(assert (distinct a c))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn tester_contradicting_constructor_unsat() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (= x (cons 1 nil)))(assert ((_ is nil) x))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn tester_agreeing_with_constructor_sat() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (= x (cons 1 nil)))(assert ((_ is cons) x))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn uf_over_datatype_congruence_unsat() {
    // f(x) != f(y) with x = y  is UNSAT — datatype sorts under a UF.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (declare-fun x () List)(declare-fun y () List)\
         (declare-fun f (List) Int)\
         (assert (= x y))(assert (distinct (f x) (f y)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn undetermined_constructor_fences_to_unknown() {
    // The slice-39 completeness fence (spec §5.2). Exhaustiveness — that x must
    // be SOME constructor — needs the case split landing in slice 40, so this
    // UNSAT query is reported `unknown` rather than wrongly `sat`.
    // SLICE 40 WILL FLIP THIS PIN TO `unsat`.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (not ((_ is nil) x)))(assert (not ((_ is cons) x)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unknown"], "slice-39 fence: see spec §5.2");
}

#[test]
fn mixed_datatype_and_arith_unsat() {
    // Regression for the Task 9 review MUST-FIX: datatype atoms must be routed
    // through the same mixed-theory bookkeeping (saw_euf / saw_euf_nonreal) as
    // Owner::Arrays, since datatype constructor/selector/tester applications
    // are EUF-adjacent. This query is genuinely cross-theory, not trivially
    // unsat from arithmetic alone: `head(cons(x, nil)) = 5` only yields `x = 5`
    // via the DT selector-collapse lemma (`head(cons(x,nil)) = x`) plus EUF
    // transitivity, and it takes plain Int arithmetic (`x < 5`) combined with
    // that DT-derived equality to reach UNSAT. Before DtSolver is wired, no
    // collapse lemma is ever emitted, x is unconstrained by the first assert,
    // and `x < 5` alone is satisfiable.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () Int)\
         (assert (= (head (cons x nil)) 5))(assert (< x 5))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}
