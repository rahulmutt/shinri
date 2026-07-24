//! Differential oracle: shinri-solver vs z3 on QF_DT (datatypes + LIA).
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(qfdt_oracle)'
//!
//! Requires `z3` on PATH at runtime. Guarded by `#[cfg(feature = "oracle")]` —
//! WITHOUT the feature flag this file compiles to ZERO tests, which must never
//! be reported as passing coverage. Filter by **binary** (`binary(qfdt_oracle)`),
//! not `test(qfdt_oracle)` — the latter matches test *names*, not the test
//! functions defined here, and silently finds 0 tests.
//!
//! SOUNDNESS contract: when shinri returns Sat or Unsat it MUST agree with z3.
//! Shinri `Unknown` (the slice-39 completeness fence, spec §5.2) is a
//! non-disagreement and is skipped. z3 `Unknown` means there is no ground
//! truth for that query and is also skipped.
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

// ─────────────────────────────────────────────────────────────────────────────
// shinri-side harness
// ─────────────────────────────────────────────────────────────────────────────

fn shinri_answer(src: &str) -> String {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut last = String::from("none");
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        if let Ok(cmd) = result {
            match solver.execute(cmd) {
                CommandResponse::Sat => last = "sat".into(),
                CommandResponse::Unsat => last = "unsat".into(),
                CommandResponse::Unknown => last = "unknown".into(),
                _ => {}
            }
        }
    }
    last
}

// ─────────────────────────────────────────────────────────────────────────────
// z3-side harness — copied verbatim from tests/qfs_differential.rs
// (z3_verdict / z3_run, lines 118-155) so the two oracle suites stay
// consistent. Renamed `Verdict::to_str`-style comparisons to plain strings to
// match `shinri_answer`'s return type; the subprocess invocation itself
// (args, timeout, memory cap) is untouched.
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

/// Run `z3 -smt2 -in` on `script` and return its first-line verdict.
fn z3_verdict(script: &str) -> Verdict {
    let out = z3_run(script);
    match out
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("unknown")
    {
        "sat" => Verdict::Sat,
        "unsat" => Verdict::Unsat,
        _ => Verdict::Unknown,
    }
}

fn z3_run(script: &str) -> String {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let mut child = Command::new("z3")
        // Hard caps: a divergent query must degrade to `timeout` /
        // `(error "out of memory")` — both parsed as Unknown — instead of
        // filling the container's cgroup limit. Verified against z3 4.16.0.
        .args(["-smt2", "-in", "-T:120", "-memory:4096"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("z3 not on PATH — required for #[cfg(feature = \"oracle\")]");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(script.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn z3_answer(src: &str) -> String {
    match z3_verdict(src) {
        Verdict::Sat => "sat".into(),
        Verdict::Unsat => "unsat".into(),
        Verdict::Unknown => "unknown".into(),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Cases
// ─────────────────────────────────────────────────────────────────────────────

const LIST: &str = "(declare-datatype List ((nil) (cons (head Int) (tail List))))";

fn agree(body: &str) {
    let src = format!("(set-logic QF_UFDTLIA){LIST}{body}(check-sat)");
    let ours = shinri_answer(&src);
    if ours == "unknown" {
        return; // slice-39 fence — not a disagreement
    }
    let theirs = z3_answer(&src);
    if theirs == "unknown" {
        return; // no ground truth
    }
    assert_eq!(ours, theirs, "disagreement on:\n{src}");
}

/// Like `agree`, but for cases where the slice-40 fence lift means shinri
/// MUST reach a decided verdict — asserts `ours != "unknown"` before
/// cross-checking against z3, so a regression that reintroduces the
/// completeness fence for these shapes fails loudly instead of silently
/// passing as a non-mismatch.
fn agree_decided(body: &str) {
    let src = format!("(set-logic QF_UFDTLIA){LIST}{body}(check-sat)");
    let ours = shinri_answer(&src);
    assert_ne!(
        ours, "unknown",
        "slice-40 fence must be lifted for this query, got unknown:\n{src}"
    );
    let theirs = z3_answer(&src);
    if theirs == "unknown" {
        return; // no ground truth
    }
    assert_eq!(ours, theirs, "shinri {ours} vs z3 {theirs}:\n{src}");
}

#[test]
fn qfdt_oracle_selector_collapse() {
    agree("(assert (distinct (head (cons 1 nil)) 1))");
}

#[test]
fn qfdt_oracle_injectivity() {
    agree(
        "(declare-fun a () Int)(declare-fun b () Int)\
         (assert (= (cons a nil) (cons b nil)))(assert (distinct a b))",
    );
}

#[test]
fn qfdt_oracle_disjointness() {
    agree("(declare-fun x () List)(assert (= x nil))(assert (= x (cons 1 nil)))");
}

#[test]
fn qfdt_oracle_tester_agreement() {
    agree("(declare-fun x () List)(assert (= x (cons 1 nil)))(assert ((_ is cons) x))");
}

#[test]
fn qfdt_oracle_nested_constructors() {
    agree("(assert (distinct (head (tail (cons 1 (cons 2 nil)))) 2))");
}

#[test]
fn qfdt_oracle_uf_over_datatype() {
    agree(
        "(declare-fun x () List)(declare-fun y () List)(declare-fun f (List) Int)\
         (assert (= x y))(assert (distinct (f x) (f y)))",
    );
}

// slice-39 soundness fix: an arith relation directly over a selector term.
// These are the shapes that previously returned a confident wrong `sat`.
#[test]
fn qfdt_oracle_lt_over_selector() {
    agree("(assert (< (head (cons 10 nil)) 5))");
}

#[test]
fn qfdt_oracle_le_over_selector() {
    agree("(assert (<= (head (cons 10 nil)) 5))");
}

#[test]
fn qfdt_oracle_gt_over_selector() {
    agree("(assert (> (head (cons 10 nil)) 5))");
}

#[test]
fn qfdt_oracle_ge_over_selector() {
    agree("(assert (>= (head (cons 10 nil)) 20))");
}

#[test]
fn qfdt_oracle_arith_wrapped_selector() {
    agree("(assert (< (+ (head (cons 10 nil)) 1) 5))");
}

// ─────────────────────────────────────────────────────────────────────────────
// slice-40: exhaustiveness case-splitting + Sat-side PARTIAL propagation.
// These queries exercise the tester-exhaustiveness fence lift (spec
// docs/superpowers/specs/2026-07-24-shinri-slice40-tester-case-split-design.md
// §5) and must land on a definite shinri verdict (sat/unsat), not the
// completeness-fence `unknown`. They route through `agree_decided`, which
// asserts `ours != "unknown"` before cross-checking z3 — a regression back
// to the fence WOULD fail these tests, unlike `agree()`.
// ─────────────────────────────────────────────────────────────────────────────

// Two-constructor exhaustiveness: ¬is-nil(x) ∧ ¬is-cons(x) is UNSAT — every
// List value is exactly one of nil/cons. Pre-slice-40 this fenced to unknown.
#[test]
fn qfdt_oracle_exhaustiveness_two_ctor_unsat() {
    agree_decided(
        "(declare-fun x () List)(assert (not ((_ is nil) x)))(assert (not ((_ is cons) x)))",
    );
}

// Instantiation over a fresh (non-List) datatype: constructor-argument
// equalities must instantiate selectors on a Pair, not just List.
#[test]
fn qfdt_oracle_pair_instantiation_sat() {
    agree_decided(
        "(declare-datatype Pair ((mk (fst Int) (snd Bool))))\
         (declare-fun p () Pair)\
         (assert (= (fst p) 7))(assert (snd p))",
    );
}

// Three-constructor exhaustiveness: ¬is-red(c) ∧ ¬is-green(c) forces
// is-blue(c) via PARTIAL propagation (the slice-40 SAT-side fix) — must
// decide sat (c = blue), not fence to unknown.
#[test]
fn qfdt_oracle_color_three_ctor_partial_propagation_sat() {
    agree_decided(
        "(declare-datatype Color ((red) (green) (blue)))\
         (declare-fun c () Color)\
         (assert (not ((_ is red) c)))(assert (not ((_ is green) c)))",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// slice-41: datatype acyclicity. Cyclic equations over the (infinite,
// well-founded) List datatype are UNSAT — no finite/infinite term satisfies
// the occurs-check violation. Pre-slice-41 these fenced to unknown; now they
// must decide unsat. Routed through `agree_decided`, so a regression back to
// the fence fails loudly instead of silently passing as a non-mismatch.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn qfdt_oracle_cyclic_self_reference() {
    // x = cons(h, x): z3/cvc5 return unsat by acyclicity; slice 41 must too.
    agree_decided("(declare-fun x () List)(declare-fun h () Int)(assert (= x (cons h x)))");
}

#[test]
fn qfdt_oracle_cyclic_mutual() {
    // x = cons(1, y) ∧ y = cons(2, x): mutual datatype cycle → unsat.
    agree_decided(
        "(declare-fun x () List)(declare-fun y () List)\
         (assert (= x (cons 1 y)))(assert (= y (cons 2 x)))",
    );
}
