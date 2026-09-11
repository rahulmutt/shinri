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

// ─────────────────────────────────────────────────────────────────────────────
// Slice 48: randomized generator.
//
// The fixed shapes above cannot find the slice-48 defect, because tester
// disjointness was order-dependent: the SAME formula answered `sat` or `unsat`
// depending on which conjunct SAT asserted first, and every hand-written shape
// here happens to use the order that worked. The generator's load-bearing
// dimension is therefore CONJUNCT ORDER — it shuffles, and it alternates
// between separate `(assert ..)` commands and one `(and ..)`.
// ─────────────────────────────────────────────────────────────────────────────

/// A tiny deterministic LCG so the corpus is reproducible without `rand`.
/// Copied verbatim from tests/qfabv_oracle.rs to match the existing convention.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0 >> 16
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

const N_ITERS: usize = 300;

/// The Barrett family, names copied verbatim from
/// `QF_DT/20172804-Barrett/barrett-jsat/tests/v1/v1l30072.cvc.smt2`, plus a
/// flat enum standing in for the blocksworld-style enums.
const BARRETT: &str = "(declare-datatypes ((nat 0)(list 0)(tree 0)) (\
((succ (pred nat)) (zero))\
((cons (car tree) (cdr list)) (null))\
((node (children list)) (leaf (data nat)))))\
(declare-datatype Color ((red) (green) (blue)))\
(declare-fun n1 () nat)(declare-fun l1 () list)(declare-fun l2 () list)\
(declare-fun t1 () tree)(declare-fun c1 () Color)";

fn nat_term(rng: &mut Lcg, depth: u32) -> String {
    match rng.below(if depth == 0 { 3 } else { 4 }) {
        0 => "zero".into(),
        1 => "n1".into(),
        2 => format!("(data {})", tree_term(rng, depth.saturating_sub(1))),
        _ => format!("(succ {})", nat_term(rng, depth - 1)),
    }
}

fn list_term(rng: &mut Lcg, depth: u32) -> String {
    match rng.below(if depth == 0 { 4 } else { 6 }) {
        0 => "null".into(),
        1 => "l1".into(),
        2 => "l2".into(),
        // A selector applied to a possibly-WRONG constructor: where the corpus
        // reproducer v1l30072 lives.
        3 => format!("(children {})", tree_term(rng, depth.saturating_sub(1))),
        4 => format!("(cdr {})", list_term(rng, depth - 1)),
        _ => format!(
            "(cons {} {})",
            tree_term(rng, depth - 1),
            list_term(rng, depth - 1)
        ),
    }
}

fn tree_term(rng: &mut Lcg, depth: u32) -> String {
    match rng.below(if depth == 0 { 2 } else { 4 }) {
        0 => "t1".into(),
        1 => format!(
            "(leaf {})",
            if depth == 0 {
                "zero".into()
            } else {
                nat_term(rng, depth - 1)
            }
        ),
        2 => format!("(car {})", list_term(rng, depth - 1)),
        _ => format!("(node {})", list_term(rng, depth - 1)),
    }
}

/// One conjunct. Testers and equalities are drawn from the same pool so a
/// generated instance mixes both — the mix is what the defect needs.
fn conjunct(rng: &mut Lcg) -> String {
    let d = 2;
    let body = match rng.below(9) {
        0 => format!("(= {} {})", list_term(rng, d), list_term(rng, d)),
        1 => format!("(= {} {})", tree_term(rng, d), tree_term(rng, d)),
        2 => format!("(= {} {})", nat_term(rng, d), nat_term(rng, d)),
        3 => format!("((_ is cons) {})", list_term(rng, d)),
        4 => format!("((_ is null) {})", list_term(rng, d)),
        5 => format!("((_ is node) {})", tree_term(rng, d)),
        6 => format!("((_ is leaf) {})", tree_term(rng, d)),
        7 => format!("((_ is succ) {})", nat_term(rng, d)),
        _ => {
            let k = ["red", "green", "blue"][rng.below(3) as usize];
            format!("(= c1 {k})")
        }
    };
    if rng.below(4) == 0 {
        format!("(not {body})")
    } else {
        body
    }
}

fn gen_instance(rng: &mut Lcg) -> String {
    let n = 2 + rng.below(4) as usize;
    let mut cs: Vec<String> = (0..n).map(|_| conjunct(rng)).collect();
    // Fisher-Yates over the LCG: the order dimension the fixed shapes lack.
    for i in (1..cs.len()).rev() {
        let j = rng.below((i + 1) as u64) as usize;
        cs.swap(i, j);
    }
    let asserts = if rng.below(2) == 0 {
        // Separate commands: SAT sees them in file order.
        cs.iter()
            .map(|c| format!("(assert {c})"))
            .collect::<String>()
    } else {
        // One conjunction: the assert order is SAT's to choose. This is the
        // encoding the minimal reproducer uses.
        format!("(assert (and {}))", cs.join(""))
    };
    format!("(set-logic QF_DT){BARRETT}{asserts}(check-sat)")
}

#[test]
fn qfdt_random_matches_z3() {
    let mut rng = Lcg(0xD7_0000_0048u64);
    let (mut n_sat, mut n_unsat, mut n_skipped) = (0usize, 0usize, 0usize);

    for it in 0..N_ITERS {
        let src = gen_instance(&mut rng);
        let ours = shinri_answer(&src);
        if ours == "unknown" {
            n_skipped += 1; // our incompleteness fence — not a disagreement
            continue;
        }
        let theirs = z3_answer(&src);
        if theirs == "unknown" {
            n_skipped += 1; // no ground truth
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_DT SOUNDNESS DISAGREEMENT (iter {it}): shinri={ours} z3={theirs}\n\
             Reproduce with this instance:\n{src}"
        );
        if ours == "sat" {
            n_sat += 1;
        } else {
            n_unsat += 1;
        }
    }

    println!(
        "qfdt_random_matches_z3: {N_ITERS} iters, {n_sat} sat / {n_unsat} unsat / \
         {n_skipped} skipped, 0 mismatches"
    );
    // Both directions must be exercised, or the oracle proves nothing.
    assert!(n_sat > 0, "generator produced no sat instances");
    assert!(n_unsat > 0, "generator produced no unsat instances");
}

// ─────────────────────────────────────────────────────────────────────────────
// Slice 49: guarded-record generator.
//
// `gen_instance` above emits only top-level ground conjuncts, so every literal
// lands at decision level 0 and EUF never registers a term mid-search. The
// slice-49 defect (spec §1.2) needs exactly that: a selector application
// minted by DT's injectivity rule while a same-constructor merge holds only
// inside a case split. This generator wraps equalities over a record of a
// constructor-bearing datatype in `ite`/`or` guards, including the degenerate
// both-branches-equal guard the reduced repro uses.
// ─────────────────────────────────────────────────────────────────────────────

const GUARDED_RECORD: &str = "(declare-datatypes ((E 0)) (((A) (C) (H))))\
(declare-datatypes ((T 0)) (((stack (top E) (rest T)) (empty))))\
(declare-datatypes ((R 0)) (((R (right T)))))\
(declare-fun p () R)(declare-fun q () R)(declare-fun u () R)\
(declare-fun c () E)(declare-fun e1 () E)(declare-fun t1 () T)";

const RECS: [&str; 3] = ["p", "q", "u"];
const ENUMS: [&str; 3] = ["A", "C", "H"];

fn gr_rec(rng: &mut Lcg) -> &'static str {
    RECS[rng.below(3) as usize]
}

fn gr_enum(rng: &mut Lcg) -> &'static str {
    ["A", "C", "H", "e1", "c"][rng.below(5) as usize]
}

fn gr_stack(rng: &mut Lcg) -> String {
    match rng.below(5) {
        0 => format!("(stack {} empty)", gr_enum(rng)),
        1 => format!("(right {})", gr_rec(rng)),
        2 => "empty".into(),
        3 => "t1".into(),
        _ => format!("(stack {} t1)", gr_enum(rng)),
    }
}

fn gr_atom(rng: &mut Lcg) -> String {
    match rng.below(5) {
        0 => {
            let (x, y) = (gr_rec(rng), gr_rec(rng));
            format!("(= {x} {y})")
        }
        1 => {
            let (x, e) = (gr_rec(rng), gr_enum(rng));
            format!("(= (top (right {x})) {e})")
        }
        _ => {
            let x = gr_rec(rng);
            format!("(= (right {x}) {})", gr_stack(rng))
        }
    }
}

fn gr_guarded(rng: &mut Lcg) -> String {
    let b1 = gr_atom(rng);
    let b2 = if rng.below(2) == 0 {
        b1.clone()
    } else {
        gr_atom(rng)
    };
    if rng.below(2) == 0 {
        let k = ENUMS[rng.below(3) as usize];
        format!("(ite (= c {k}) {b1} {b2})")
    } else {
        format!("(or {b1} {b2})")
    }
}

fn gen_guarded_record(rng: &mut Lcg) -> String {
    let n = 3 + rng.below(4) as usize;
    let mut asserts = String::new();
    for _ in 0..n {
        let c = if rng.below(2) == 0 {
            gr_guarded(rng)
        } else {
            gr_atom(rng)
        };
        asserts.push_str(&format!("(assert {c})"));
    }
    format!("(set-logic QF_DT){GUARDED_RECORD}{asserts}(check-sat)")
}

#[test]
fn qfdt_random_guarded_records_match_z3() {
    let mut rng = Lcg(0xD7_0000_0049u64);
    let (mut n_sat, mut n_unsat, mut n_skipped) = (0usize, 0usize, 0usize);

    for it in 0..N_ITERS {
        let src = gen_guarded_record(&mut rng);
        let ours = shinri_answer(&src);
        if ours == "unknown" {
            n_skipped += 1; // our incompleteness fence — not a disagreement
            continue;
        }
        let theirs = z3_answer(&src);
        if theirs == "unknown" {
            n_skipped += 1; // no ground truth
            continue;
        }
        assert_eq!(
            ours, theirs,
            "QF_DT SOUNDNESS DISAGREEMENT (guarded records, iter {it}): shinri={ours} z3={theirs}\n\
             Reproduce with this instance:\n{src}"
        );
        if ours == "sat" {
            n_sat += 1;
        } else {
            n_unsat += 1;
        }
    }

    println!(
        "qfdt_random_guarded_records_match_z3: {N_ITERS} iters, {n_sat} sat / {n_unsat} unsat / \
         {n_skipped} skipped, 0 mismatches"
    );
    assert!(n_sat > 0, "generator produced no sat instances");
    assert!(n_unsat > 0, "generator produced no unsat instances");
}
