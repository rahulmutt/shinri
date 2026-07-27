//! Slice 43 — the model channel. Datatype field values must come from the
//! theory that owns them, not render as `?`.
//!
//! Task 2 asserted with `contains` because model output was not yet
//! deterministic (entries came from an FxHashMap). Task 5 made `get-model`
//! enumerate the declared-symbol registry in declaration order, so every
//! assertion here is now an exact whole-line pin.

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

/// Probe C3 of the spec: arith pins the selector's value, so the field must
/// render 42 — not `?`. THE PREMISE GATE: the value is already in `arith_m`
/// (Arith::build_model assigns every var it knows); this asserts it is now
/// reachable from DtSolver's renderer.
#[test]
fn int_field_renders_arith_assigned_value() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert ((_ is cons) l))(assert (= (head l) 42))\
         (check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun l () List (cons 42 nil)))");
}

/// Probe C2: a LITERAL field. Independent of any theory — readable straight off
/// the term via Context::numeral_value, so this passes even with an empty
/// builder. Pins spec §3.C branch 2.
#[test]
fn literal_int_field_renders_from_the_term() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert (= l (cons 1 nil)))(check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun l () List (cons 1 nil)))");
}

/// Probe C1: the field is entirely UNCONSTRAINED and its selector application
/// was minted in-search, so it is not in the Solver's own ctx. Arith still holds
/// it at its current beta, and inside the Combiner the TermId is valid — which is
/// the whole reason rendering moved there.
#[test]
fn unconstrained_minted_int_field_still_renders_a_value() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert ((_ is cons) l))(check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    // MEASURED, not predicted: the tail is unconstrained, so the value is
    // whichever beta arith is sitting on and whichever constructor DT picked.
    assert_eq!(out[1], "((define-fun l () List (cons 0 nil)))");
}

/// Spec §5 left the Bool-field question open; this pins the MEASURED answer.
/// It RESOLVES to `(mk true)`: `Euf::model`'s truth-node branch runs before the
/// sort-ownership skip, so a Bool field merged with EUF's ⊤ node gets a
/// `ModelVal::Bool(true)` in the shared builder and `render_field`'s branch 3
/// reads it. No `?` survives here.
#[test]
fn bool_field_resolves_from_the_euf_truth_node() {
    let out = run_script(
        "(set-logic QF_UFDT)(declare-datatype B ((mk (b Bool))))(declare-fun z () B)\
         (assert (b z))(check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun z () B (mk true)))");
}

/// A String-sorted field is a SURVIVING `?` (spec §5's fenced-gap list — Task 7
/// owns pinning that list). `(s w)` is minted in-search by DT, so it never
/// enters `StrSolver`'s `str_terms` and the string model never assigns it
/// (`shinri-str/src/model.rs:116-126`). EUF treats String as uninterpreted and
/// leaves a `ModelVal::Elem` behind, which is an opaque CLASS TOKEN, not a
/// String value. `render_field` must therefore refuse it and fall through to
/// `?`: printing `@elem0` in a String position would be a sort-mismatched value
/// — a wrong model, which is strictly worse than a visible placeholder.
#[test]
fn string_field_stays_a_placeholder_rather_than_an_elem_token() {
    let out = run_script(
        "(set-logic ALL)(declare-datatype S ((mk (s String))))(declare-fun w () S)\
         (assert ((_ is mk) w))(check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun w () S (mk ?)))");
}

/// The other side of that guard: for a genuinely UNINTERPRETED-sorted field an
/// `@elemN` token IS the faithful SMT-LIB rendering of an anonymous domain
/// element, so the guard must not over-fire and degrade it to `?`.
#[test]
fn uninterpreted_sorted_field_still_renders_its_elem_token() {
    let out = run_script(
        "(set-logic ALL)(declare-sort U 0)(declare-datatype P ((mk (u U))))\
         (declare-fun p () P)(assert ((_ is mk) p))(check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun p () P (mk @elem0)))");
}

/// Probe C4: two levels of tester-driven instantiation.
#[test]
fn nested_int_fields_both_render() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert ((_ is cons) l))(assert ((_ is cons) (tail l)))\
         (assert (= (head l) 7))(check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    // MEASURED, not predicted: only the outer field is pinned (7); the inner
    // one is whatever arith's beta and DT's constructor choice landed on.
    assert_eq!(out[1], "((define-fun l () List (cons 7 (cons 0 nil))))");
}

// ── Slice 43 Task 5: conformant, deterministic `define-fun` output ───────────

/// Spec §4.B: conformant define-fun, single line, declaration order.
#[test]
fn model_emits_define_fun_in_declaration_order() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)(declare-fun x () Int)\
         (assert ((_ is cons) l))(assert (= (head l) 42))(assert (= x 5))\
         (check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(
        out[1],
        "((define-fun l () List (cons 42 nil))(define-fun x () Int 5))"
    );
}

/// Determinism: the same query must produce byte-identical model output every
/// run. Before slice 43 entries came out in FxHashMap order.
#[test]
fn model_output_is_deterministic() {
    let q = format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)(declare-fun x () Int)\
         (assert ((_ is cons) l))(assert (= x 5))(check-sat)(get-model)"
    );
    let first = run_script(&q);
    for _ in 0..8 {
        assert_eq!(run_script(&q), first, "model output must be deterministic");
    }
}

/// Spec §1 probes M4/M4c: a declared symbol occurring in NO assertion. It is in
/// no registered atom, so no theory assigns it and there is nothing in the value
/// map to iterate — it used to vanish entirely, returning `()`. M4c is the
/// non-datatype control: a fix that only handles the datatype path fails it.
#[test]
fn unasserted_int_symbol_gets_a_default() {
    let out = run_script("(set-logic QF_LIA)(declare-fun x () Int)(check-sat)(get-model)");
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun x () Int 0))");
}

#[test]
fn unasserted_datatype_symbol_gets_a_structural_default() {
    // `List` has a nullary constructor, so the default is `nil`.
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)(check-sat)(get-model)"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun l () List nil))");
}

#[test]
fn unasserted_datatype_without_nullary_ctor_recurses_into_field_defaults() {
    // `Box` has NO nullary constructor, so the default must be built by
    // recursing into the field's own default (spec §4.B).
    let out = run_script(
        "(set-logic QF_UFDTLIA)(declare-datatype Box ((mk (unbox Int))))\
         (declare-fun b () Box)(check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun b () Box (mk 0)))");
}

/// Slice 43 §2: `get-model` is only meaningful after `sat`. Registry
/// enumeration would otherwise answer an UNSAT query with a complete,
/// well-formed `define-fun` list of sort defaults — a model-shaped lie, and
/// strictly worse than the old `()`, which no caller can misread. A harness
/// that reads `out[1]` without checking `out[0]` must not be handed one.
#[test]
fn get_model_after_unsat_is_empty_not_a_fabricated_model() {
    let out = run_script(
        "(set-logic QF_LIA)(declare-fun x () Int)\
         (assert (= x 5))(assert (= x 6))(check-sat)(get-model)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unsat"),
        "got {out:?}"
    );
    assert_eq!(out[1], "()");
}

/// The `unknown` half of the same guard: a fenced query has no model either.
/// This is the case the old `if !has_bv_euf && !has_abv` guard would also have
/// caught — but that guard cannot be restored, because it equally suppresses a
/// declared symbol that occurs in no assertion (§1 defect 3). The gate must be
/// "was the last solve sat", not "is there any model data".
#[test]
fn get_model_after_unknown_is_empty_not_a_fabricated_model() {
    let out = run_script(
        "(set-logic QF_ALIA)(declare-fun a () (Array Int Int))(declare-fun i () Int)\
         (assert (= (select a i) 9))(check-sat)(get-model)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
    assert_eq!(out[1], "()");
}

/// A new assertion invalidates the recorded outcome: the previous `sat`
/// described a different assertion set, so a `get-model` before the next
/// `check-sat` must not report the stale model as if it were current.
#[test]
fn get_model_after_a_new_assert_is_empty_until_resolved() {
    let out = run_script(
        "(set-logic QF_LIA)(declare-fun x () Int)(assert (= x 5))(check-sat)(get-model)\
         (assert (= x 6))(get-model)(check-sat)(get-model)",
    );
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "((define-fun x () Int 5))");
    assert_eq!(out[2], "()", "stale model after a new assert: {out:?}");
    assert_eq!(out[3], "unsat");
    assert_eq!(out[4], "()");
}

/// Task 5 found and fixed the identical defect in `format_model` (gated on
/// `last_outcome`); `GetValue` had the same defect — the query changing
/// underneath an unresolved `check-sat` must not answer with a value from
/// the PREVIOUS, unrelated solve. SMT-LIB treats `get-value` after a
/// non-`sat` check as an error, so this must produce `CommandResponse::Error`
/// (the established pattern: `GetUnsatCore` does the same), not a
/// model-shaped-but-stale response.
#[test]
fn get_value_after_unsat_is_an_error_not_a_stale_value() {
    let out = run_script(
        "(set-logic QF_LIA)(declare-fun x () Int)\
         (assert (= x 5))(check-sat)(get-value (x))\
         (assert (= x 6))(check-sat)(get-value (x))",
    );
    assert_eq!(out[0], "sat");
    assert_eq!(out[1], "((x 5))");
    assert_eq!(out[2], "unsat");
    assert_eq!(
        out[3], "(error \"model is not available\")",
        "stale value after unsat: {out:?}"
    );
}

/// Spec §4.C: get-value must label each response with the term the user asked
/// for, not an internal id.
#[test]
fn get_value_labels_responses_with_the_requested_term() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert ((_ is cons) l))(assert (= (head l) 7))\
         (check-sat)(get-value ((head l) l))"
    ));
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "(((head l) 7) (l (cons 7 nil)))");
}

/// Spec §1 defect 2: no internal name and no undeclared symbol may appear.
#[test]
fn model_names_only_declared_symbols() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert (= l (cons 1 nil)))(check-sat)(get-model)"
    ));
    let model = &out[1];
    assert!(
        !model.contains("(define-fun nil"),
        "a constructor constant is not a declared symbol: {model}"
    );
    for tn in ["t3", "t4", "t5", "t6", "t7"] {
        assert!(
            !model.contains(&format!("(define-fun {tn} ")),
            "internal term id {tn} leaked into the model: {model}"
        );
    }
}
