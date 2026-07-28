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

/// T6 review finding 1 (security-relevant, exponential output amplification):
/// the term DAG is hash-consed and the parser supports `let`
/// (`shinri-parser/src/parser.rs:772`), which binds a name to a TermId
/// without duplicating it. `display_term` has no memoization, so before the
/// node-visit budget it re-walked a shared child once per occurrence in its
/// parent — a chain of `x_i := (g x_{i-1} x_{i-1})` cost `2^N` node-visits
/// for `N` levels, not `N`. Measured pre-fix: a 22-level chain (612-byte
/// script) rendered a 29 MB `get-value` response in ~4.3s; the review's own
/// measurement found 25 MB/4.1s at N=22 and 100 MB/16.5s at N=24 — i.e. it
/// roughly doubles per level. This pins a 40-level chain, which would be
/// `2^40` node-visits unbounded, completing fast with a budget-capped,
/// bounded-size response instead.
#[test]
fn get_value_on_exponentially_shared_term_stays_bounded() {
    // N is deliberately in the 22-25 band, NOT 40: if the budget is ever
    // weakened this test must FAIL, and it can only fail by COMPLETING. At
    // N=40 an unbudgeted render is 2^40 node-visits — the test would hang
    // until CI's 20-minute cap killed the job, which reads as an
    // infrastructure timeout rather than as a regression. At N=25 the
    // unbudgeted render is only three doublings past the measured 25-29 MB /
    // ~4s at N=22 (see the doc comment above), so it blows the size assertion
    // below within seconds.
    const N: usize = 25;
    let mut src = String::from(
        "(set-logic QF_UFLIA)(declare-fun g (Int Int) Int)(check-sat)(get-value ((let ((x0 0))",
    );
    for i in 1..=N {
        let prev = i - 1;
        src.push_str(&format!("(let ((x{i} (g x{prev} x{prev})))"));
    }
    src.push_str(&format!("x{N}"));
    src.push_str(&")".repeat(N + 1));
    src.push_str("))");

    let out = run_script(&src);
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    // Unbounded this would be exponential in N (25-29 MB already at N=22,
    // measured, roughly doubling per level). DISPLAY_TERM_BUDGET caps total
    // node-visits regardless of N, so the response stays small.
    assert!(
        out[1].len() < 2_000_000,
        "get-value response not bounded: {} bytes",
        out[1].len()
    );
}

/// Spec §1 defect 2: no internal name and no undeclared symbol may appear.
#[test]
fn model_names_only_declared_symbols() {
    let out = run_script(&format!(
        "(set-logic QF_UFDTLIA){LIST}(declare-fun l () List)\
         (assert (= l (cons 1 nil)))(check-sat)(get-model)"
    ));
    // Absence assertions alone are near-unfalsifiable — an empty model `()`,
    // or an error response, satisfies every one of them. Gate on the verdict
    // and pin a positive entry first, so the absences below are absences from
    // a model that actually says something.
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    let model = &out[1];
    assert!(
        model.contains("(define-fun l () List "),
        "the declared symbol `l` must be present: {model}"
    );
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

// ── Task 7: pin the three fenced gaps (spec §5) ───────────────────────────
//
// Each test below records CURRENT behaviour of a gap the spec leaves open on
// purpose, so a successor slice can find it and a future change to it is a
// deliberate decision rather than an accident. Every assertion here was
// measured against the real release binary (`./target/release/shinri`)
// before being written — none is a value predicted from the spec text.

/// Spec §5 predicted a BV-sorted datatype field "still renders `?`", reasoning
/// that BV values are extracted solver-side from SAT vars and never enter the
/// Combiner's ModelBuilder, so DT cannot see them.
///
/// PRE-slice-44 history (superseded below, kept for the record — this is the
/// same class of bug slice 44 fences): `(w v)` is a non-nullary uninterpreted
/// application with a BV result sort whose one argument, `v`, is
/// Datatype-sorted — not BV/FP-sorted, so it has no blastable word. Before
/// slice 44 Task 2's fence existed, behaviour differed per build profile:
///
/// * RELEASE (no debug assertions): `blast_bv_word`'s `Op::Uninterpreted` arm
///   minted FRESH unconstrained bits for `(w v)` with no congruence, decided
///   `sat`, and the model rendered `v`'s field as the placeholder `?` (the
///   final review's finding 1 fix, itself now moot for this query).
/// * DEV/TEST (debug assertions ON): the same code path hit
///   `debug_assert!(child_ids.is_empty(), "non-nullary uninterpreted BV fn
///   out of scope")` in `crates/shinri-bv/src/blast/mod.rs:282` and PANICKED
///   before `check-sat` ever returned.
///
/// Slice 44 Task 2's `uf_args_supported` fence (`bv_stage.rs`) now catches
/// this BEFORE lowering starts, in EVERY build profile: `v`'s Datatype sort
/// has no blastable word, so the query fences to a SOUND `unknown`. This is
/// the spec §2.1 named decided → unknown exception (an uninterpreted-sorted
/// argument to a BV-result uninterpreted function), and it also means the
/// debug-mode panic and the release-mode unsound `sat` are BOTH gone — the
/// debug_assert! is no longer reachable from this query at all.
const BV_FIELD: &str = "(set-logic QF_UFDTBV)(declare-datatype W ((mk (w (_ BitVec 8)))))\
                        (declare-fun v () W)(assert (= (w v) #x2a))(check-sat)(get-model)";

/// MEASURED (slice 44 Task 2): both build profiles now agree — the fence
/// fires before the bit-blaster is ever invoked, so there is no longer a
/// debug/release split to pin separately.
#[test]
fn fenced_bv_field_is_unknown() {
    let out = run_script(BV_FIELD);
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}

/// `get-model` omits functions of arity > 0 (spec §5): a function graph needs
/// EUF congruence-class enumeration plus a default point, which is a later
/// slice, so `get-model` is knowingly NOT a complete model for UF queries.
///
/// MEASURED, matches the spec's prediction: `f` never appears in the output;
/// `x` — the arity-0 symbol in the same query — is present, so an empty or
/// errored model cannot make this test pass vacuously.
#[test]
fn fenced_arity_gt_zero_function_is_omitted() {
    let out = run_script(
        "(set-logic QF_UFLIA)(declare-fun x () Int)(declare-fun f (Int) Int)\
         (assert (> (f x) 3))(check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    // MEASURED: `((define-fun x () Int 0))` — `f` is entirely absent; `x` is
    // present (the beta arith settled on to satisfy `(f x) > 3` with `f`
    // free).
    assert_eq!(out[1], "((define-fun x () Int 0))");
}

/// Uninterpreted-sort field VALUES resolve (via EUF's `Elem`), but render as
/// `@elem0` rather than SMT-LIB's `(as @U!val!0 U)` (spec §5) — pre-existing
/// and out of scope to fix here.
/// `uninterpreted_sorted_field_still_renders_its_elem_token` above already
/// pins the single-symbol shape of that token; this test pins the OTHER half
/// the brief calls for and that the single-symbol test cannot exercise: two
/// symbols FORCED into the same EUF equivalence class must render the SAME
/// field value, not two different opaque tokens for what is provably one
/// value. Not a duplicate of the existing test — it exercises class-merge
/// consistency, not just token shape.
#[test]
fn fenced_uninterpreted_field_agrees_across_a_merged_class() {
    let out = run_script(
        "(set-logic QF_UFDT)(declare-sort U 0)(declare-datatype P ((mk (f U))))\
         (declare-fun p () P)(declare-fun q () P)(assert (= p q))\
         (check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    // MEASURED: both fields resolve to the SAME @elemN token, not `?` and not
    // two distinct tokens for a class the solver proved is one value.
    assert_eq!(
        out[1],
        "((define-fun p () P (mk @elem0))(define-fun q () P (mk @elem0)))"
    );
}

// ── Final review, finding 1: a sort default must not answer for a symbol the
//    solve actually constrained ────────────────────────────────────────────

/// `value_of_declared` returns `None` for two conditions that are not
/// interchangeable: the symbol was never interned (occurs in no assertion — a
/// sort default is then CORRECT, since its constraint set is empty), or it was
/// interned and constrained but no value channel holds a value for it (a sort
/// default is then a LIE).
///
/// The QF_ABV path (`crates/shinri-solver/src/lib.rs`, the
/// `uses_arrays_over_bv` early return) is the general case of the second
/// condition: it populates ONLY `abv_array_models`, so every non-array
/// declared symbol on that path has no channel. Before the fix, `i` and `j`
/// below — both pinned by an assertion to a nonzero value — printed
/// `#b0000`, a model contradicting the very assertions that made the query
/// `sat`. Pre-slice-43 `format_model` iterated the value map and they were
/// merely ABSENT; changing the enumeration axis to declarations is what turned
/// that silent incompleteness into a confident falsehood. The array entry,
/// which DOES have a channel, must keep its real value — an over-broad fix
/// that degraded everything to `?` fails this test too.
#[test]
fn abv_unvalued_symbol_is_a_placeholder_not_a_fabricated_default() {
    let out = run_script(
        "(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))\
         (declare-fun i () (_ BitVec 4))(declare-fun j () (_ BitVec 4))\
         (assert (= i #x3))(assert (= j #x5))(assert (= (select a i) #x2a))\
         (check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(
        out[1],
        "((define-fun a () (Array (_ BitVec 4) (_ BitVec 8)) \
          (store ((as const (Array (_ BitVec 4) (_ BitVec 8))) #x00) #x3 #x2a))\
          (define-fun i () (_ BitVec 4) ?)(define-fun j () (_ BitVec 4) ?))"
    );
}

/// The Bool half of the same condition, and the sharper demonstration: a
/// defaulted `Bool` prints `false` for a symbol the query ASSERTED, so the
/// falsehood is not a matter of an unlucky bit pattern.
#[test]
fn abv_unvalued_bool_is_a_placeholder_not_false() {
    let out = run_script(
        "(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))\
         (declare-fun b () Bool)(assert b)(assert (= (select a #x0) #x2a))\
         (check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert!(
        out[1].contains("(define-fun b () Bool ?)"),
        "an asserted Bool must not be defaulted to `false`: {}",
        out[1]
    );
}

/// The control for the fix: a symbol in NO assertion is never interned, so the
/// sort default still applies and `get-model` still answers for it. This is
/// what keeps the finding-1 fix from being "degrade everything to `?`".
/// (`unasserted_int_symbol_gets_a_default` above pins the same property on the
/// arith path; this pins that the two `None` sources are distinguished within
/// ONE model, side by side.)
#[test]
fn unasserted_and_unvalued_symbols_are_told_apart_in_one_model() {
    let out = run_script(
        "(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))\
         (declare-fun i () (_ BitVec 4))(declare-fun k () (_ BitVec 4))\
         (assert (= (select a i) #x2a))(check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    // `i` occurs in the select (interned, unvalued → `?`); `k` occurs nowhere
    // (never interned → default). Same model, same sort, different answers.
    assert!(
        out[1].contains("(define-fun i () (_ BitVec 4) ?)"),
        "constrained-but-unvalued must be `?`: {}",
        out[1]
    );
    assert!(
        out[1].contains("(define-fun k () (_ BitVec 4) #x0)"),
        "unasserted must keep its sort default: {}",
        out[1]
    );
}

/// Duplicate declarations must not produce duplicate model entries. The parser
/// accepts redeclaration and hash-cons maps both to one symbol; pre-slice-43
/// the term-keyed value map collapsed the repeat implicitly, the declaration
/// registry has to do it explicitly.
#[test]
fn redeclared_symbol_appears_once_in_the_model() {
    let out = run_script(
        "(set-logic QF_LIA)(declare-fun x () Int)(declare-fun x () Int)\
         (check-sat)(get-model)",
    );
    assert_eq!(out.first().map(|s| s.as_str()), Some("sat"), "got {out:?}");
    assert_eq!(out[1], "((define-fun x () Int 0))");
}
