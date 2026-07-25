//! Slice 43 — the model channel. Datatype field values must come from the
//! theory that owns them, not render as `?`.
//!
//! Task 2 asserts with `contains` because model output is not yet deterministic
//! (entries come from an FxHashMap). Task 5 makes it deterministic and converts
//! these to exact-string assertions.

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
    let model = &out[1];
    assert!(
        model.contains("(cons 42 nil)"),
        "Int field must render its arith value, got: {model}"
    );
    assert!(
        !model.contains('?'),
        "no `?` placeholder may survive for an Int field, got: {model}"
    );
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
    assert!(
        out[1].contains("(cons 1 nil)"),
        "literal field must render as 1, got: {}",
        out[1]
    );
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
    assert!(
        !out[1].contains('?'),
        "an unconstrained Int field must still get a value, got: {}",
        out[1]
    );
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
    assert!(
        out[1].contains("(mk true)"),
        "Bool field must render true, got: {}",
        out[1]
    );
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
    assert!(
        !out[1].contains("@elem"),
        "an EUF class token must never render in a String field, got: {}",
        out[1]
    );
    assert!(
        out[1].contains("(mk ?)"),
        "an unassigned String field stays a visible placeholder, got: {}",
        out[1]
    );
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
    assert!(
        out[1].contains("(mk @elem0)"),
        "an uninterpreted-sorted field keeps its domain-element token, got: {}",
        out[1]
    );
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
    assert!(
        out[1].contains("(cons 7 (cons "),
        "outer field must render 7 with a nested cons, got: {}",
        out[1]
    );
}
