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

/// Slice 47: a bare `sat` must never survive on the commuting-store shape.
/// `wchains002ue`-shaped: two store chains over the same base writing the
/// same index set in opposite orders, asserted DISTINCT. The writes commute,
/// so the assertion is unsat and any `sat` is spurious.
///
/// NOTE: this fixture is decided `Unsat` by `refine`'s pre-existing
/// congruence/extensionality lemmas before `solve_qfabv_with_models` ever
/// reaches the `validate` gate, so it does NOT exercise the gate call added
/// in this task — it is a regression guard on the commuting-store shape
/// only. See `qfabv_gate_fences_store_chain_equality_spurious_sat` below for
/// a fixture that actually reaches the gate.
#[test]
fn qfabv_commuting_store_disequality_is_never_sat() {
    let (r, tag) = run("(set-logic QF_ABV)\
         (declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))\
         (declare-fun i () (_ BitVec 4))(declare-fun j () (_ BitVec 4))\
         (declare-fun e () (_ BitVec 4))(declare-fun f () (_ BitVec 4))\
         (assert (distinct i j))\
         (assert (distinct (store (store a i e) j f) (store (store a j f) i e)))\
         (check-sat)");
    // The writes commute when i != j, so this is UNSAT. Either the engine
    // decides it (best) or the gate downgrades it (sound). What must NEVER
    // happen is a bare `sat`.
    match r {
        Some(CommandResponse::Unsat) => assert_eq!(tag, None),
        Some(CommandResponse::Unknown) => assert_eq!(tag, Some("abv-model-rejected")),
        other => panic!("QF_ABV commuting-store disequality must not be sat: {other:?}"),
    }
}

/// Slice 47: this fixture DOES reach the `validate` gate today — `refine`
/// reports `Sat` on a model no array realises (Task 1's minimal
/// store-chain-equality reproducer), and the gate downgrades it to a fenced
/// `Unknown` before it can surface as a wrong `sat`. Without the gate call
/// in `solve_qfabv_with_models`, this test FAILS with `Some(Sat)` — that is
/// the property `qfabv_commuting_store_disequality_is_never_sat` cannot
/// provide, since that fixture never reaches the gate at all.
#[test]
fn qfabv_gate_fences_store_chain_equality_spurious_sat() {
    let (r, tag) = run("(set-logic QF_ABV)\
         (declare-const a0 (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const i0 (_ BitVec 8))(declare-const i1 (_ BitVec 8))\
         (declare-const e0 (_ BitVec 8))(declare-const e1 (_ BitVec 8))\
         (assert (distinct i0 i1))(assert (distinct e0 e1))\
         (assert (= (store (store a0 i0 e0) i1 e1) (store (store a0 i0 e1) i1 e0)))\
         (check-sat)");
    // Either the engine decides this outright as Unsat (best, and this test
    // stays valid if a later task teaches it to), or the gate downgrades a
    // spurious Sat to a fenced Unknown (sound). What must NEVER happen is a
    // bare `sat`.
    match r {
        Some(CommandResponse::Unsat) => assert_eq!(tag, None),
        Some(CommandResponse::Unknown) => assert_eq!(tag, Some("abv-model-rejected")),
        other => panic!("QF_ABV store-chain equality must not be sat: {other:?}"),
    }
}

/// The §4.1 grammar: `<mode>:<kind>@<rebuild>`, no whitespace.
fn well_formed_detail(tag: &str) -> bool {
    let Some((head, rebuild)) = tag.rsplit_once('@') else {
        return false;
    };
    let Some((mode, kind)) = head.split_once(':') else {
        return false;
    };
    matches!(mode, "violated" | "unevaluable")
        && !kind.is_empty()
        && matches!(rebuild, "not-needed" | "adopted" | "rejected" | "budget")
        && !tag.contains(char::is_whitespace)
}

/// Slice 59: a `str-model-rejected` carries a well-formed detail, and the
/// next `check-sat` clears it (Review Focus 1). The first query is the
/// slice-58 `g1` guard shape, `unknown fence=str-model-rejected` at `de96d28`.
#[test]
fn str_model_rejected_detail_clears_on_next_check() {
    let src = "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)\
        (assert (str.prefixof \"a\" x))(assert (= x y))\
        (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))(check-sat)\
        (assert false)(check-sat)";
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut seen = Vec::new();
    while let Some(r) = parser.next_command(solver.ctx_mut()) {
        let resp = solver.execute(r.expect("fixture parses"));
        if matches!(
            resp,
            CommandResponse::Sat | CommandResponse::Unsat | CommandResponse::Unknown
        ) {
            seen.push((
                resp,
                solver.last_fence(),
                solver.last_fence_detail().map(str::to_owned),
            ));
        }
    }
    assert_eq!(seen.len(), 2);
    assert!(matches!(seen[0].0, CommandResponse::Unknown));
    assert_eq!(seen[0].1, Some("str-model-rejected"));
    let detail = seen[0]
        .2
        .as_deref()
        .expect("a detail on str-model-rejected");
    assert!(well_formed_detail(detail), "{detail:?}");
    assert!(matches!(seen[1].0, CommandResponse::Unsat));
    assert_eq!((seen[1].1, seen[1].2.as_deref()), (None, None));
}

#[test]
fn other_fences_carry_no_detail() {
    let mut solver = Solver::new();
    let mut parser = Parser::new(
        "(set-logic QF_S)(declare-fun a () String)(declare-fun b () String)\
         (assert (str.< a b))(check-sat)",
    );
    while let Some(r) = parser.next_command(solver.ctx_mut()) {
        solver.execute(r.expect("fixture parses"));
    }
    assert_eq!(solver.last_fence(), Some("str-order"));
    assert_eq!(solver.last_fence_detail(), None);
}
