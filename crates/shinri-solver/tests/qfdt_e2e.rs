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

// NOTE: the slice-39 pin that used to live here (`undetermined_constructor_
// fences_to_unknown`, asserting `unknown` on this exact query per spec §5.2)
// was removed in slice 40 T4: it ran the byte-for-byte identical query as
// `negated_all_testers_is_unsat` below, which now supersedes it with the
// slice-40-correct `unsat` assertion. See task-4-report.md for the
// reconciliation record (an adjudicated, z3-confirmed completeness gain, not
// a regression).

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

// ─────────────────────────────────────────────────────────────────────────────
// slice-39 soundness fix: an arith RELATION whose operand IS the selector term.
// Before the fix `classify`'s blanket `contains_dt_op → Owner::Datatypes`
// deep-walk stole these atoms from the simplex (Datatypes dispatches to EUF+DT
// only, never Arith), so the inequality went unevaluated and shinri returned a
// confident WRONG `sat`. The selector is now an ordinary Int UF-app: the
// relation is Arith-owned, DT-collapse merges `head(cons(10,nil)) = 10` into
// EUF, N-O exchanges it to Arith, and the simplex derives the conflict.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn arith_lt_over_selector_unsat() {
    // head(cons(10, nil)) = 10, so 10 < 5 is FALSE → unsat.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (assert (< (head (cons 10 nil)) 5))(check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn arith_le_over_selector_unsat() {
    // 10 <= 5 is FALSE → unsat.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (assert (<= (head (cons 10 nil)) 5))(check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn arith_gt_over_selector_sat() {
    // 10 > 5 is TRUE → sat (a satisfiable relation over a selector still routes
    // through Arith and is decided, not fenced).
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (assert (> (head (cons 10 nil)) 5))(check-sat)"
    ));
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn arith_ge_over_selector_unsat() {
    // 10 >= 20 is FALSE → unsat.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (assert (>= (head (cons 10 nil)) 20))(check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn arith_wrapped_selector_unsat() {
    // (+ head(cons(10,nil)) 1) = 11, so 11 < 5 is FALSE → unsat. Confirms the
    // selector rides the arith path even when nested under an arithmetic op.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}\
         (assert (< (+ (head (cons 10 nil)) 1) 5))(check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

// ─────────────────────────────────────────────────────────────────────────────
// Slice 40 — datatype tester case-splitting (the completeness-fence lift).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn negated_all_testers_is_unsat() {
    // Exhaustiveness: x is a List, so it must be nil or cons, but both testers
    // are negated. Slice 39 answered `unknown` (the coarse completeness
    // fence); slice 40's exhaustiveness split decides `unsat`.
    //
    // This query originally surfaced a SAT-layer wiring gap while this test
    // was being written (see task-4-report.md's original diagnosis): the
    // exhaustiveness split's `TCheck::Split { guard: None, atoms: [is-nil(x),
    // is-cons(x)] }` reuses the SAME atom terms as the already-asserted
    // `¬is-nil(x)` / `¬is-cons(x)` unit facts, and `shinri-sat`'s
    // `TheoryResult::SplitAtoms` handler (`lits.len() != 1` branch) installed
    // the resulting binary clause via `add_learnt`/`watch_binary` without
    // checking whether both literals were already false on the trail, so the
    // conflict was silently accepted instead of discovered. That gap is now
    // FIXED (`fix(sat): conflict/propagate SplitAtoms clauses already
    // (un)assigned on the trail`, commit 16efa9fb, pinned in
    // shinri-sat::solver tests, commit 8bce8a54) — this query now correctly
    // decides `unsat`. This test supersedes the removed slice-39 pin
    // `undetermined_constructor_fences_to_unknown`, which ran the identical
    // query and asserted `unknown`.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert (not ((_ is nil) x)))(assert (not ((_ is cons) x)))\
         (check-sat)"
    ));
    assert_eq!(
        out,
        vec!["unsat"],
        "slice-40 exhaustiveness split decides unsat (SAT-layer SplitAtoms fix, commit 16efa9fb)"
    );
}

#[test]
fn instantiation_yields_sat_model() {
    // Sat requires instantiating cons to satisfy head(x) = 5. Exercises the
    // guarded constructor-instantiation rule (Rule 2) plus the nullary-first
    // phase bias steering the lazy descent to terminate.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)\
         (assert ((_ is cons) x))(assert (= (head x) 5))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn mutually_recursive_group_is_sat() {
    // Mutually recursive datatypes: a Tree is a leaf or a node holding a
    // Forest, and a Forest is fnil or an fcons of a Tree and a Forest. Confirms
    // the split/instantiation rules generalize across a mutually recursive
    // sort group, not just single-sort List.
    let out = run_script(
        "(set-logic QF_UFDTLIA)\
         (declare-datatypes ((Tree 0) (Forest 0))\
           (((leaf (val Int)) (node (kids Forest)))\
            ((fnil) (fcons (fhd Tree) (ftl Forest)))))\
         (declare-fun t () Tree)\
         (assert ((_ is node) t))\
         (check-sat)",
    );
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn cyclic_self_reference_is_unsat() {
    // x = cons(h, x) has no finite ground model and, by datatype acyclicity, no
    // model at all. Slice 40 fenced this to `unknown`; slice 41 proves `unsat`
    // via the cycle-explanation conflict. Adjudicated completeness flip
    // (z3/cvc5 agree unsat), not a regression.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)(declare-fun h () Int)\
         (assert (= x (cons h x)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

#[test]
fn mutual_cycle_is_unsat() {
    // x = cons(1, y) ∧ y = cons(2, x): a two-node datatype cycle → unsat.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun x () List)(declare-fun y () List)\
         (assert (= x (cons 1 y)))(assert (= y (cons 2 x)))\
         (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

/// Slice 42 performance gate. A datatype with an `Int` field makes every
/// DT-minted `head(t)` selector application an Int-sorted UF app, so the
/// sort-only filter in `Euf::shared_arith_terms` sweeps all of them into the
/// Nelson-Oppen shared set. Pre-slice-42 every pair sat at β = 0 and was probed
/// with two simplex solves: 24.7 s at n = 24 (release), against 10 ms for the
/// same n = 24 query with an uninterpreted field sort — the control pinned by
/// `uninterpreted_field_chain_is_fast` below. Post-fix the Int-field query
/// matches that control exactly at 10 ms, a ≈2470× improvement. (The spec's
/// ≈1600× headline is the n = 20 pair, 9.4 s vs 6 ms; do not mix the two.)
///
/// The bound is deliberately loose (5 s against a 24.7 s baseline). Wall-clock
/// assertions are normally a flakiness smell; a fault of this size leaves enough
/// margin to be worth one, and without it a regression silently consumes the
/// blocking tier's 10-15 min budget. The tier that actually runs this is the
/// DEBUG profile, where the query takes ≈90 ms against a ~5 ms process-startup
/// floor — ~55× of margin under the 5 s bound, so the bound is not tight even
/// unoptimized.
#[test]
fn int_field_chain_does_not_blow_up() {
    let n = 24;
    let mut src = String::from(
        "(set-logic QF_DT)\
         (declare-datatype List ((nil) (cons (head Int) (tail List))))\
         (declare-const x List)",
    );
    let mut t = String::from("x");
    for _ in 0..n {
        src.push_str(&format!("(assert (not ((_ is nil) {t})))"));
        t = format!("(tail {t})");
    }
    src.push_str("(check-sat)");

    let start = std::time::Instant::now();
    let out = run_script(&src);
    let elapsed = start.elapsed();

    // Exact, not `last()`: a script that errored on every `assert` and then
    // trivially `sat`-ed on an empty problem would be fast AND green under the
    // weaker form.
    assert_eq!(out, vec!["sat"]);
    assert!(
        elapsed.as_secs() < 5,
        "n={n} Int-field chain took {elapsed:?}; pre-slice-42 baseline was 24.7s \
         and the post-fix target is milliseconds"
    );
}

/// Companion control: the same query shape with an uninterpreted field sort
/// never entered the shared set and was always fast. Pinning it here makes a
/// future regression attributable — if BOTH tests slow down the cause is not
/// the arith seam.
#[test]
fn uninterpreted_field_chain_is_fast() {
    let n = 24;
    let mut src = String::from(
        "(set-logic ALL)\
         (declare-sort U 0)\
         (declare-datatype List ((nil) (cons (head U) (tail List))))\
         (declare-const x List)",
    );
    let mut t = String::from("x");
    for _ in 0..n {
        src.push_str(&format!("(assert (not ((_ is nil) {t})))"));
        t = format!("(tail {t})");
    }
    src.push_str("(check-sat)");

    let start = std::time::Instant::now();
    let out = run_script(&src);
    let elapsed = start.elapsed();

    // Exact, for the same reason as the gate above.
    assert_eq!(out, vec!["sat"]);
    assert!(elapsed.as_secs() < 5, "control query took {elapsed:?}");
}
