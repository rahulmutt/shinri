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
