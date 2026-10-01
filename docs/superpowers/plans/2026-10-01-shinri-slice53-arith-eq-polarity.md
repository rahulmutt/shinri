# Slice 53 — Arithmetic `=` under non-positive polarity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make every Int/Real `(= a b)` atom mean `a = b` to arithmetic in every Boolean position. This takes the 4 keymaera/calypto rows from `wrong` to `correct`. Then minimize, and within a time box fix, the ramalho QF_BVFP wrong `sat`.

**Architecture:** A new pre-encoding pass in `shinri-solver` collects every arithmetic-sorted binary `Eq` atom reachable through Boolean structure. It emits three theory-valid clauses per atom (`E→Le`, `E→Ge`, `Le∧Ge→E`), which the encoder asserts next to the lowered assertions. They are kept out of the string model gate's input. `lower`'s positive arithmetic `Eq` arm now returns the bare `E`.

**Tech Stack:** Rust (workspace pinned via `mise`), cargo-nextest 0.9.140, z3 4.16.0 and cvc5 from mise for oracles, `easy_smt` in oracle tests, `shinri-bench` for corpus runs.

**Spec:** `docs/superpowers/specs/2026-10-01-shinri-slice53-arith-eq-polarity-design.md`

## Global Constraints

- Branch: `slice53-arith-eq-polarity` off `main`. PR to `main`, merged with a merge commit when CI is green; then delete the branch (remote and local).
- Pure Rust: no new dependencies (`deny.toml` bans native-link crates).
- No change to the parser, the SAT core, the Combiner or the arithmetic theory (spec §4).
- The `Not(Eq) → (or Lt Gt)` arm and the arithmetic `distinct` arms stay unchanged (spec §3.3).
- Never remove `#[ignore]` from the exhaustive `shinri-fp` suites (`fp_div/fp_mul/fp_add` `_tiny_exhaustive_all_modes`, `to_fp_fp_tiny_exhaustive_both_directions`, `rem_tiny_exhaustive`).
- Oracle tests run only with `--features oracle`. Always confirm a non-zero discovered count; a 0-test run is not green.
- nextest filters use `-E 'test(<name>)'` or `-E 'binary(<name>)'`, never a positional filter.
- No new test may take > 5 min. The target for the new oracle binary is < 30 s.
- `cargo fmt --all` before every commit; `cargo clippy --workspace --all-targets -- -D warnings` clean (`mise run lint`).
- Bench limits: 20 s, 3072 MB, 6 jobs, `taskset -c 12-23`. Logics: QF_LIA, QF_LRA, QF_BVFP, QF_UFLIA, QF_UFLRA, QF_S, QF_SLIA.
- Stop for a ruling (do not ship) on any `* → wrong` row, or on a net `correct` loss in any logic (spec §7, criteria 3–4).

## Review Focus

Inputs the spec implies but its listed tests don't exercise. Each has a test in Task 2:

1. **`push`/`pop` across a negated arithmetic `=`.** The axioms are rebuilt per `check_sat` from live assertions, so a popped scope must leave no stale constraint. Test: `push_pop_negated_eq_does_not_leak`.
2. **Models after `sat` under negated equalities.** `get-value` must honour `x = 1`, `y ≠ 2` from `(not (=> (= x 1) (= y 2)))`. Test: `implication_sat_model_respects_negated_eq`.
3. **Strings: `str.len` equalities under negation.** They now go through the axioms, and the string model gate must not see the axiom clauses. Test: `slia_len_eq_under_demorgan` (+ sat sibling).
4. **Real equalities with fractional solutions under negation** (`(= (* 2 a) 1)` with `a` pinned to `1/2`). Test: `real_fractional_eq_under_demorgan`.
5. **N-ary arithmetic `=` under negation.** The collector must yield the same adjacent-pair atoms that `lower` builds. Test: unit `arith_eq_atoms_splits_nary_like_lower` and e2e `nary_eq_under_implication`.

---

## File Structure

| file | change | responsibility |
| --- | --- | --- |
| `crates/shinri-solver/src/lib.rs` | modify | new `arith_eq_atoms` + `arith_eq_axioms` (next to `is_arith_sorted`, ~1825); `check_sat` call site (~1167) and encode site (~1275); `lower`'s positive `Eq` arm (~2272–2320); unit tests in `mod tests` (~2575) |
| `crates/shinri-solver/tests/slice53_probes.rs` | create | blocking-tier e2e probes: §1.3 shapes, keymaera inlined, Review Focus 1–5, ramalho repro |
| `crates/shinri-solver/tests/arith_polarity_oracle.rs` | create | `oracle`-feature differential family vs z3. **Deviation from spec §6.3:** its own binary instead of `oracle.rs` (1,800+ lines), following the `nary_arith_oracle.rs` precedent; the test name `differential_qf_lia_lra_polarity` is unchanged |
| `crates/shinri-fp/src/…` or `crates/shinri-bv/src/…` | maybe modify | ramalho fix, only on the Task 3 "local fix" branch |
| `docs/superpowers/research/2026-10-0X-smtlib-2024-slice53-arith-eq-polarity-report.md` | create | measurement report (date = day the after-run finishes) |
| `docs/superpowers/specs/2026-10-01-shinri-slice53-arith-eq-polarity-design.md` | modify | §12 Measured outcomes |

---

### Task 1: Branch and base bench run

**Files:** none committed (bench output lives in git-ignored `bench/results/`).

**Interfaces:**
- Produces: `bench/results/slice53-base/{results.jsonl,report.md}`, which Task 4 compares against; and the frozen binary `target/slice53-base/shinri`.

The base run uses a **copied** binary, so later rebuilds of `target/release/shinri` in Tasks 2–3 cannot swap it mid-run. Expected wall-clock: about 5–6 h. The baseline had about 4,100 timeouts across LIA/LRA/BVFP/UFLIA, and the strings logics took about 1.5 h in slice 52. Start it, then continue with Task 2 in parallel. **Do not run anything else pinned to cores 12–23 while it runs.**

- [ ] **Step 1: Create the branch**

```bash
git checkout -b slice53-arith-eq-polarity main
```

- [ ] **Step 2: Confirm the corpus is present** (QF_LIA/LRA/BVFP were fetched on 2026-10-01)

```bash
for l in QF_LIA QF_LRA QF_BVFP QF_UFLIA QF_UFLRA QF_S QF_SLIA; do printf '%s ' $l; find bench/corpus/$l -name '*.smt2' | wc -l; done
```

Expected: 13306, 1753, 17249, 659, 1284, 18940, 84395. If a logic is missing: `BENCH_LOGICS=<logic> mise run bench-fetch`.

- [ ] **Step 3: Build and freeze the base binary at `2ceef06`**

The branch has only the spec and plan commits on top of `2ceef06`, so the sources are identical.

```bash
git diff --stat 2ceef06 HEAD -- crates   # expected: empty
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice53-base && cp target/release/shinri target/slice53-base/shinri
md5sum target/slice53-base/shinri | tee target/slice53-base/md5.txt
```

- [ ] **Step 4: Start the base run in the background**

```bash
taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_LIA,QF_LRA,QF_BVFP,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice53-base/shinri --run-id slice53-base \
  > target/slice53-base/run.log 2>&1
```

(Run with the Bash tool's `run_in_background`; it re-invokes you when it exits.) The fixture header records the checkout HEAD, not the binary's commit; this is a known harness nit. The report must state that the binary is `2ceef06` sources, citing the md5 from Step 3.

- [ ] **Step 5: When it finishes, render the report and record the wrong rows**

```bash
target/release/shinri-bench report bench/results/slice53-base
tail -1 target/slice53-base/run.log
python3 - <<'EOF'
import json
for l in open("bench/results/slice53-base/results.jsonl"):
    r = json.loads(l)
    if r.get("verdict") == "wrong": print(r["path"], r["answers"], r["status"])
EOF
```

Expected: at least the 5 rows of spec §1.1. Copy the list into the scratchpad note `slice53-notes.md`. Task 4 checks any extra row against the fix.

---

### Task 2: Arithmetic `=` equivalence axioms (tests first)

**Files:**
- Create: `crates/shinri-solver/tests/slice53_probes.rs`
- Create: `crates/shinri-solver/tests/arith_polarity_oracle.rs`
- Modify: `crates/shinri-solver/src/lib.rs` (~1167, ~1275, ~1825, ~2272–2320, `mod tests`)

**Interfaces:**
- Produces (private, on `impl Solver` in `lib.rs`):
  - `fn arith_eq_atoms(&mut self, roots: &[TermId]) -> Vec<TermId>`: every binary Int/Real `(= a b)` reachable through Boolean positions of `roots`, in first-visit order, deduplicated. An n-ary `(= a b c)` yields `(= a b)`, `(= b c)`, the same hash-consed terms `lower` builds.
  - `fn arith_eq_axioms(&mut self, roots: &[TermId]) -> Vec<TermId>`: for each atom `E = (= a b)` from `arith_eq_atoms`, three Bool terms in this order: `(or (not E) (<= a b))`, `(or (not E) (>= a b))`, `(or (not (<= a b)) (not (>= a b)) E)`.
- Changes: `lower` on a binary arithmetic `(= a b)` returns the term itself. On an n-ary one it returns `(and (= a b) (= b c) …)`.

- [ ] **Step 1: Write the e2e probes**

Create `crates/shinri-solver/tests/slice53_probes.rs`. The two keymaera constants are the corpus files' `set-logic`, `declare-fun` and `assert` lines, copied verbatim (comments, `set-info`, `check-sat` and `exit` dropped):

```rust
//! Slice 53 probes (spec §6.2). An Int/Real `(= a b)` atom used to be lowered
//! to `(and E Le Ge)`, which is only equivalent in positive positions; under
//! `not (or …)`, `=>`, Bool `=` or a negated `ite` the SAT solver could falsify
//! `E` alone (wrong `sat`). Every `*_unsat` case here was `sat` at `2ceef06`
//! unless marked "regression pin". Each has a `sat` sibling so the fix cannot
//! pass by over-refuting.
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

const INT: &str = "(set-logic QF_LIA)(declare-fun p () Bool)\
    (declare-fun x () Int)(declare-fun y () Int)";
const REAL: &str = "(set-logic QF_LRA)(declare-fun p () Bool)\
    (declare-fun x () Real)(declare-fun y () Real)";

fn verdict(header: &str, body: &str) -> String {
    let out = run_script(&format!("{header}{body}(check-sat)"));
    out.first().cloned().unwrap_or_default()
}

/// Asserts `body` is unsat and `sibling` (one constraint relaxed) is sat,
/// under both the Int and the Real header.
fn both_sorts(body: &str, sibling: &str) {
    for h in [INT, REAL] {
        assert_eq!(verdict(h, body), "unsat", "{h}{body}");
        assert_eq!(verdict(h, sibling), "sat", "{h}{sibling}");
    }
}

#[test]
fn demorgan_negated_or() {
    both_sorts(
        "(assert (not (or (= x 1) p)))(assert (>= x 1))(assert (<= x 1))",
        "(assert (not (or (= x 1) p)))(assert (>= x 1))(assert (<= x 2))",
    );
}

#[test]
fn negated_implication() {
    both_sorts(
        "(assert (not (=> (= x 1) (= (- x 1) 0))))",
        "(assert (not (=> (= x 1) (= (- x 1) 1))))",
    );
}

#[test]
fn bool_iff_over_arith_eq() {
    both_sorts(
        "(assert (= x 1))(assert (= p (= x 2)))(assert p)",
        "(assert (= x 1))(assert (= p (= x 2)))(assert (not p))",
    );
}

#[test]
fn negated_ite_branches() {
    both_sorts(
        "(assert (>= x 1))(assert (<= x 1))(assert (not (ite p (= x 1) (= x 1))))",
        "(assert (>= x 1))(assert (<= x 2))(assert (not (ite p (= x 1) (= x 1))))",
    );
}

/// Regression pin: already unsat at `2ceef06`.
#[test]
fn xor_over_arith_eq() {
    both_sorts(
        "(assert (= x 1))(assert (xor p (= x 1)))(assert p)",
        "(assert (= x 1))(assert (xor p (= x 1)))(assert (not p))",
    );
}

/// Regression pin: term-level `ite` conditions are lifted by `word_norm`.
#[test]
fn term_ite_condition() {
    both_sorts(
        "(assert (= x 1))(assert (< (ite (= x 1) 1 0) 1))",
        "(assert (= x 2))(assert (< (ite (= x 1) 1 0) 1))",
    );
}

/// Review Focus 5: n-ary `=` under `=>` (collector must match `lower`'s pairs).
#[test]
fn nary_eq_under_implication() {
    both_sorts(
        "(assert (= x 1))(assert (= y 1))(assert (not (=> p (= x y 1))))(assert p)",
        "(assert (= x 1))(assert (= y 2))(assert (not (=> p (= x y 1))))(assert p)",
    );
}

/// Review Focus 4: a fractional Real solution under De Morgan.
#[test]
fn real_fractional_eq_under_demorgan() {
    let body = "(assert (not (or (= (* 2 x) 1) p)))(assert (>= x 0.5))(assert (<= x 0.5))";
    let sib = "(assert (not (or (= (* 2 x) 1) p)))(assert (>= x 0.5))(assert (<= x 1.0))";
    assert_eq!(verdict(REAL, body), "unsat");
    assert_eq!(verdict(REAL, sib), "sat");
}

/// EUF must still see `x = y` (it is an argument of `f`) under `=>`.
#[test]
fn uflia_congruence_under_implication() {
    let h = "(set-logic QF_UFLIA)(declare-fun f (Int) Int)\
        (declare-fun x () Int)(declare-fun y () Int)(declare-fun p () Bool)";
    assert_eq!(
        verdict(h, "(assert p)(assert (=> p (= x y)))(assert (distinct (f x) (f y)))"),
        "unsat"
    );
    assert_eq!(
        verdict(h, "(assert (not p))(assert (=> p (= x y)))(assert (distinct (f x) (f y)))"),
        "sat"
    );
}

/// Review Focus 3: `str.len` equality under De Morgan; the string model gate
/// must not see the axiom clauses.
#[test]
fn slia_len_eq_under_demorgan() {
    let h = "(set-logic QF_SLIA)(declare-fun s () String)(declare-fun p () Bool)";
    assert_eq!(
        verdict(h, "(assert (= s \"ab\"))(assert (not (or (= (str.len s) 2) p)))"),
        "unsat"
    );
    assert_eq!(
        verdict(h, "(assert (= s \"abc\"))(assert (not (or (= (str.len s) 2) p)))"),
        "sat"
    );
}

/// Review Focus 1: the popped scope's negated equality must not leak.
#[test]
fn push_pop_negated_eq_does_not_leak() {
    let out = run_script(&format!(
        "{INT}(push 1)(assert (not (or (= x 1) p)))(check-sat)(pop 1)\
         (assert (= x 1))(check-sat)"
    ));
    assert_eq!(out, vec!["sat".to_string(), "sat".to_string()]);
}

/// Review Focus 2: the model must satisfy `x = 1` and `y ≠ 2`.
#[test]
fn implication_sat_model_respects_negated_eq() {
    let out = run_script(&format!(
        "(set-option :produce-models true){INT}\
         (assert (not (=> (= x 1) (= y 2))))(check-sat)(get-value (x y))"
    ));
    assert_eq!(out[0], "sat");
    let v = out[1].replace(char::is_whitespace, "");
    assert!(v.contains("(x1)"), "x must be 1: {}", out[1]);
    assert!(!v.contains("(y2)"), "y must not be 2: {}", out[1]);
}

const KEYMAERA_2074: &str = r#"(set-logic QF_LRA)
(declare-fun e () Real)
(declare-fun buscore2dollarskuscore0 () Real)
(declare-fun auscore2dollarskuscore0 () Real)
(declare-fun cuscore2dollarskuscore0 () Real)
(assert (let ((?v_0 (* 5 auscore2dollarskuscore0)) (?v_1 (* 3 buscore2dollarskuscore0))) (not (=> (and (= e 0) (= (+ (+ ?v_0 ?v_1) cuscore2dollarskuscore0) 10)) (= (+ (+ (- ?v_0 5) (+ ?v_1 6)) (- cuscore2dollarskuscore0 1)) 10)))))"#;
const KEYMAERA_2406: &str = r#"(set-logic QF_LRA)
(declare-fun e () Real)
(declare-fun buscore2dollarskuscore1 () Real)
(declare-fun cuscore2dollarskuscore1 () Real)
(declare-fun auscore2dollarskuscore1 () Real)
(assert (let ((?v_0 (* 5 auscore2dollarskuscore1)) (?v_1 (* 3 buscore2dollarskuscore1))) (not (=> (= (+ (+ ?v_0 ?v_1) cuscore2dollarskuscore1) 10) (or (= e 0) (= (+ (+ (+ ?v_0 5) (- ?v_1 3)) (- cuscore2dollarskuscore1 2)) 10))))))"#;

/// Corpus rows `QF_LRA/keymaera/simple_example_2-node{2074,2406}.smt2`
/// (`:status unsat`, z3 unsat; shinri `sat` at `2ceef06`).
#[test]
fn keymaera_rows() {
    for src in [KEYMAERA_2074, KEYMAERA_2406] {
        assert_eq!(run_script(&format!("{src}(check-sat)")), vec!["unsat".to_string()]);
    }
}
```

`run_script` returns only `sat`/`unsat`/… lines because `print-success` is off by default in `Solver`. If a `set-logic` echo appears, filter `"success"` in `keymaera_rows`.

- [ ] **Step 2: Run the probes; confirm they fail at HEAD**

Run: `cargo nextest run -p shinri-solver -E 'binary(slice53_probes)'`

Expected: 13 tests discovered. These FAIL (`sat` where `unsat` is expected): `demorgan_negated_or`, `negated_implication`, `bool_iff_over_arith_eq`, `negated_ite_branches`, `nary_eq_under_implication`, `real_fractional_eq_under_demorgan`, `keymaera_rows`, and probably `uflia_congruence_under_implication` and `slia_len_eq_under_demorgan`. These pass: `xor_over_arith_eq`, `term_ite_condition`, `push_pop_negated_eq_does_not_leak`. Record the exact pass/fail list in `slice53-notes.md`. A test that passes but was expected to fail is a finding: note it, keep it as a regression pin, and fix its doc comment.

- [ ] **Step 3: Write the oracle family**

Create `crates/shinri-solver/tests/arith_polarity_oracle.rs`:

```rust
//! Differential oracle (slice 53, spec §6.3): Int/Real `=`/`distinct`/`<=`
//! atoms nested under random `not`/`or`/`and`/`=>`/`xor`/`ite`/Bool-`=` shapes,
//! conjoined with bound pins, checked against z3. The pre-existing arithmetic
//! oracles generate conjunctions, so they never put an arithmetic `=` under
//! non-positive polarity, which is how the slice-53 wrong `sat` survived.
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(arith_polarity_oracle)'
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// Copied from tests/nary_arith_oracle.rs (the per-binary convention).
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

const N_ITERS: usize = 200;
const VARS: &[&str] = &["x", "y", "z"];

#[derive(Clone, Copy)]
enum Sort {
    Int,
    Real,
}

impl Sort {
    fn name(self) -> &'static str {
        match self {
            Sort::Int => "Int",
            Sort::Real => "Real",
        }
    }
    fn logic(self) -> &'static str {
        match self {
            Sort::Int => "QF_LIA",
            Sort::Real => "QF_LRA",
        }
    }
    /// A literal in -2..=2: `(- 1)` / `(- 1.0)` for negatives.
    fn lit(self, k: i64) -> String {
        let mag = match self {
            Sort::Int => format!("{}", k.abs()),
            Sort::Real => format!("{}.0", k.abs()),
        };
        if k < 0 { format!("(- {mag})") } else { mag }
    }
}

fn var(rng: &mut Lcg) -> &'static str {
    VARS[rng.below(VARS.len() as u64) as usize]
}

/// Small constants (-2..=2) so atoms collide with the pinned values often.
fn small(rng: &mut Lcg) -> i64 {
    rng.below(5) as i64 - 2
}

/// An arithmetic term: a variable, `(+ v k)`, `(- v w)` or `(* c v)`.
fn term(rng: &mut Lcg, s: Sort) -> String {
    match rng.below(4) {
        0 => var(rng).to_string(),
        1 => format!("(+ {} {})", var(rng), s.lit(small(rng))),
        2 => format!("(- {} {})", var(rng), var(rng)),
        _ => format!("(* {} {})", s.lit(1 + rng.below(2) as i64), var(rng)),
    }
}

fn atom(rng: &mut Lcg, s: Sort) -> String {
    let rhs = if rng.below(2) == 0 { var(rng).to_string() } else { s.lit(small(rng)) };
    let op = match rng.below(6) {
        0..=3 => "=", // bias towards the atom under test
        4 => "distinct",
        _ => "<=",
    };
    format!("({op} {} {rhs})", term(rng, s))
}

fn formula(rng: &mut Lcg, s: Sort, depth: u32) -> String {
    if depth == 0 || rng.below(4) == 0 {
        return if rng.below(6) == 0 { "p".to_string() } else { atom(rng, s) };
    }
    let mut f = || formula(rng, s, depth - 1);
    match rng.below(7) {
        0 => format!("(not {})", f()),
        1 => format!("(or {} {})", f(), f()),
        2 => format!("(and {} {})", f(), f()),
        3 => format!("(=> {} {})", f(), f()),
        4 => format!("(xor {} {})", f(), f()),
        5 => format!("(ite {} {} {})", f(), f(), f()),
        _ => format!("(= {} {})", f(), f()),
    }
}

fn gen_script(rng: &mut Lcg, s: Sort) -> String {
    let mut src = String::from("(declare-const p Bool)\n");
    for v in VARS {
        src.push_str(&format!("(declare-const {v} {})\n", s.name()));
    }
    // A negated root makes non-positive polarity the common case.
    let root = formula(rng, s, 3);
    let root = if rng.below(2) == 0 { format!("(not {root})") } else { root };
    src.push_str(&format!("(assert {root})\n"));
    // 0..=2 pins, each squeezing a variable to a small value via <= and >=.
    for _ in 0..rng.below(3) {
        let (v, k) = (var(rng), s.lit(small(rng)));
        src.push_str(&format!("(assert (<= {v} {k}))\n(assert (>= {v} {k}))\n"));
    }
    src.push_str("(check-sat)\n");
    src
}

fn shinri_outcome(logic: &str, src: &str) -> SolveOutcome {
    let full = format!("(set-logic {logic})\n{src}");
    let mut solver = Solver::new();
    let mut parser = Parser::new(&full);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.expect("parse error in generated script");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    outcome
}

fn z3_outcome(logic: &str, src: &str) -> easy_smt::Response {
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()
        .expect("failed to launch z3 — run `mise install`");
    ctx.set_logic(logic).expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-const ") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

fn run_family(s: Sort, seed: u64) {
    let mut rng = Lcg(seed);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut disagreements: Vec<String> = Vec::new();
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng, s);
        let ours = shinri_outcome(s.logic(), &src);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => {
                n_unknown += 1;
                continue;
            }
        }
        match (ours, z3_outcome(s.logic(), &src)) {
            (SolveOutcome::Sat, easy_smt::Response::Sat)
            | (SolveOutcome::Unsat, easy_smt::Response::Unsat)
            | (_, easy_smt::Response::Unknown) => {}
            (o, t) => disagreements.push(format!(
                "iter {iter}: shinri={o:?} z3={t:?}\n{src}"
            )),
        }
    }
    println!(
        "{}: sat={n_sat} unsat={n_unsat} unknown={n_unknown} disagreements={}",
        s.logic(),
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "{} disagreements; first three:\n{}",
        disagreements.len(),
        disagreements.iter().take(3).cloned().collect::<Vec<_>>().join("\n")
    );
    assert!(n_sat > 0 && n_unsat > 0, "need both sat ({n_sat}) and unsat ({n_unsat})");
    assert_eq!(n_unknown, 0, "QF_LIA/QF_LRA are total in shinri");
}

#[test]
fn differential_qf_lia_lra_polarity() {
    run_family(Sort::Int, 0x51CE_0053_0001);
    run_family(Sort::Real, 0x51CE_0053_0002);
}
```

- [ ] **Step 4: Run the oracle at HEAD; confirm it catches the defect**

Run: `cargo nextest run -p shinri-solver --features oracle -E 'binary(arith_polarity_oracle)' --no-capture`

Expected: 1 test discovered, FAIL with `N disagreements` (N ≥ 1, `shinri=Sat z3=Unsat`) on the QF_LIA family. Record N and the first script in `slice53-notes.md` as the "before" evidence for the report. To get the QF_LRA count too, temporarily swap the two `run_family` lines, re-run, record, and swap back. If N = 0 for both, raise the negated-root share (`rng.below(2)` → always negate) and the `=` bias until the family catches it. A family that misses the known bug is not evidence.

- [ ] **Step 5: Write the unit tests**

Add to `mod tests` in `crates/shinri-solver/src/lib.rs` (next to `lower_rewrites_int_distinct_to_or_lt_gt`):

```rust
    /// Slice 53: `arith_eq_atoms` finds Int/Real `=` atoms in every Boolean
    /// position (not / => / xor / ite / Bool `=` / Bool `distinct`).
    #[test]
    fn arith_eq_atoms_finds_every_boolean_position() {
        use shinri_core::{BuiltinOp, Op, Rational};
        let mut s = Solver::new();
        let (int, bool_) = (s.int_sort(), s.bool_sort());
        let x = s.declare_const("x", int);
        let y = s.declare_const("y", int);
        let p = s.declare_const("p", bool_);
        let n: Vec<TermId> = (1..=6)
            .map(|k| s.numeral(Rational::from_int((k as i128).into()), int))
            .collect();
        let e: Vec<TermId> = n.iter().map(|&k| s.eq(x, k)).collect();
        let e_y = s.eq(y, x);
        let or = s.app(Op::Builtin(BuiltinOp::Or), &[e[0], p]);
        let r1 = s.app(Op::Builtin(BuiltinOp::Not), &[or]);
        let r2 = s.app(Op::Builtin(BuiltinOp::Implies), &[p, e[1]]);
        let r3 = s.app(Op::Builtin(BuiltinOp::Xor), &[p, e_y]);
        let r4 = s.app(Op::Builtin(BuiltinOp::Ite), &[p, e[2], e[3]]);
        let r5 = s.eq(p, e[4]);
        let r6 = s.app(Op::Builtin(BuiltinOp::Distinct), &[p, e[5]]);
        let got = s.arith_eq_atoms(&[r1, r2, r3, r4, r5, r6]);
        assert_eq!(got, vec![e[0], e[1], e_y, e[2], e[3], e[4], e[5]]);
    }

    /// Slice 53: shared atoms are reported once; Bool- and uninterpreted-sorted
    /// `=` are not arithmetic atoms.
    #[test]
    fn arith_eq_atoms_dedups_and_ignores_non_arith_eq() {
        let mut s = Solver::new();
        let (int, bool_) = (s.int_sort(), s.bool_sort());
        let u = s.ctx_mut().declare_sort("U");
        let x = s.declare_const("x", int);
        let y = s.declare_const("y", int);
        let p = s.declare_const("p", bool_);
        let q = s.declare_const("q", bool_);
        let a = s.declare_const("a", u);
        let b = s.declare_const("b", u);
        let exy = s.eq(x, y);
        let pq = s.eq(p, q);
        let ab = s.eq(a, b);
        let got = s.arith_eq_atoms(&[exy, exy, pq, ab]);
        assert_eq!(got, vec![exy]);
    }

    /// Slice 53 (Review Focus 5): an n-ary `(= x y z)` yields the adjacent
    /// pairs, the same hash-consed terms `lower` conjoins.
    #[test]
    fn arith_eq_atoms_splits_nary_like_lower() {
        use shinri_core::{BuiltinOp, Op};
        let mut s = Solver::new();
        let int = s.int_sort();
        let x = s.declare_const("x", int);
        let y = s.declare_const("y", int);
        let z = s.declare_const("z", int);
        let nary = s.app(Op::Builtin(BuiltinOp::Eq), &[x, y, z]);
        let neg = s.app(Op::Builtin(BuiltinOp::Not), &[nary]);
        let xy = s.eq(x, y);
        let yz = s.eq(y, z);
        assert_eq!(s.arith_eq_atoms(&[neg]), vec![xy, yz]);
        let lowered = s.lower(nary);
        let want = s.app(Op::Builtin(BuiltinOp::And), &[xy, yz]);
        assert_eq!(lowered, want);
    }

    /// Slice 53: a binary arithmetic `=` lowers to itself; its three axioms
    /// are emitted in the documented order.
    #[test]
    fn binary_arith_eq_lowers_bare_with_three_axioms() {
        use shinri_core::{BuiltinOp, Op};
        let mut s = Solver::new();
        let int = s.int_sort();
        let x = s.declare_const("x", int);
        let y = s.declare_const("y", int);
        let e = s.eq(x, y);
        assert_eq!(s.lower(e), e);
        let le = s.app(Op::Builtin(BuiltinOp::Le), &[x, y]);
        let ge = s.app(Op::Builtin(BuiltinOp::Ge), &[x, y]);
        let ne = s.app(Op::Builtin(BuiltinOp::Not), &[e]);
        let nle = s.app(Op::Builtin(BuiltinOp::Not), &[le]);
        let nge = s.app(Op::Builtin(BuiltinOp::Not), &[ge]);
        let want = vec![
            s.app(Op::Builtin(BuiltinOp::Or), &[ne, le]),
            s.app(Op::Builtin(BuiltinOp::Or), &[ne, ge]),
            s.app(Op::Builtin(BuiltinOp::Or), &[nle, nge, e]),
        ];
        assert_eq!(s.arith_eq_axioms(&[e]), want);
    }
```

If `TermId` is not in scope in `mod tests`, add `use shinri_core::TermId;` at the top of the module.

- [ ] **Step 6: Run the unit tests; confirm they fail to compile**

Run: `cargo nextest run -p shinri-solver -E 'test(arith_eq_atoms) | test(binary_arith_eq_lowers_bare)'`
Expected: compile error, `no method named arith_eq_atoms` / `arith_eq_axioms`.

- [ ] **Step 7: Implement the collector and axioms**

In `crates/shinri-solver/src/lib.rs`, directly after `fn is_arith_sorted` (~1825):

```rust
    /// Slice 53: every Int/Real binary `(= a b)` reachable through a Boolean
    /// position of `roots` (`and`/`or`/`not`/`=>`/`xor`/`ite`, Bool `=` and
    /// Bool `distinct`), in first-visit order, without duplicates. An n-ary
    /// arithmetic `=` contributes its adjacent pairs, the same hash-consed
    /// terms `lower` conjoins. Non-Bool terms are not entered (term-level
    /// `ite` is already lifted by `word_norm`). Iterative: deep BMC formulas.
    fn arith_eq_atoms(&mut self, roots: &[TermId]) -> Vec<TermId> {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let bool_sort = self.ctx.bool_sort();
        let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        let mut emitted: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
        let mut out = Vec::new();
        let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let TermNode::App {
                op: Op::Builtin(op),
                args,
                ..
            } = self.ctx.term_node(t).clone()
            else {
                continue;
            };
            let kids: Vec<TermId> = self.ctx.children(args).to_vec();
            match op {
                BuiltinOp::Eq if kids.len() >= 2 && self.is_arith_sorted(kids[0]) => {
                    for w in kids.windows(2) {
                        let e = self
                            .ctx
                            .mk_app(Op::Builtin(BuiltinOp::Eq), &[w[0], w[1]])
                            .expect("Eq well-sorted");
                        if emitted.insert(e) {
                            out.push(e);
                        }
                    }
                }
                // `ite` is entered only when Bool-sorted (a term ite never
                // reaches here: `word_norm` lifts it).
                BuiltinOp::Ite if self.ctx.sort_of(t) == bool_sort => {
                    stack.extend(kids.iter().rev());
                }
                // Bool connectives; `Eq`/`Distinct` over Bool children are
                // iff/xor-like. Over any other sort they are leaves (the
                // arithmetic `Eq` arm above already matched first).
                BuiltinOp::And
                | BuiltinOp::Or
                | BuiltinOp::Not
                | BuiltinOp::Implies
                | BuiltinOp::Xor
                | BuiltinOp::Eq
                | BuiltinOp::Distinct
                    if kids.iter().all(|&k| self.ctx.sort_of(k) == bool_sort) =>
                {
                    stack.extend(kids.iter().rev());
                }
                _ => {}
            }
        }
        out
    }

    /// Slice 53 (spec §3.2): for each atom `E = (= a b)` of `arith_eq_atoms`,
    /// the theory-valid clauses `E → a≤b`, `E → a≥b`, `a≤b ∧ a≥b → E`. They
    /// make `E` mean `a = b` to arithmetic in every polarity; `lower` keeps
    /// only the bare `E`. Not fed to the string model gate (it evaluates the
    /// user's assertions, not solver axioms).
    fn arith_eq_axioms(&mut self, roots: &[TermId]) -> Vec<TermId> {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let atoms = self.arith_eq_atoms(roots);
        let mut out = Vec::with_capacity(atoms.len() * 3);
        for e in atoms {
            let TermNode::App { args, .. } = self.ctx.term_node(e).clone() else {
                unreachable!("arith_eq_atoms returns Eq applications")
            };
            let (a, b) = {
                let k = self.ctx.children(args);
                (k[0], k[1])
            };
            let mut mk = |op: BuiltinOp, xs: &[TermId]| {
                self.ctx.mk_app(Op::Builtin(op), xs).expect("well-sorted")
            };
            let le = mk(BuiltinOp::Le, &[a, b]);
            let ge = mk(BuiltinOp::Ge, &[a, b]);
            let ne = mk(BuiltinOp::Not, &[e]);
            let nle = mk(BuiltinOp::Not, &[le]);
            let nge = mk(BuiltinOp::Not, &[ge]);
            out.push(mk(BuiltinOp::Or, &[ne, le]));
            out.push(mk(BuiltinOp::Or, &[ne, ge]));
            out.push(mk(BuiltinOp::Or, &[nle, nge, e]));
        }
        out
    }
```

- [ ] **Step 8: Wire the axioms into `check_sat`**

At ~1167 replace:

```rust
        let lowered: Vec<TermId> = assertions.into_iter().map(|a| self.lower(a)).collect();
```

with:

```rust
        // Slice 53: theory axioms tying every arithmetic `=` atom to its Le/Ge
        // in all polarities. Minted here, before the ctx is cloned into the
        // Combiner. Kept apart from `lowered`: the string model gate below
        // evaluates `lowered` as the user's assertions.
        let eq_axioms = self.arith_eq_axioms(&assertions);
        let lowered: Vec<TermId> = assertions.into_iter().map(|a| self.lower(a)).collect();
```

At ~1275 replace:

```rust
            let top_lits: Vec<shinri_core::Lit> = lowered.iter().map(|&a| enc.encode(a)).collect();
```

with:

```rust
            let top_lits: Vec<shinri_core::Lit> = lowered
                .iter()
                .chain(eq_axioms.iter())
                .map(|&a| enc.encode(a))
                .collect();
```

- [ ] **Step 9: Make the positive `Eq` arm return the bare atom**

In `lower` (~2272), replace the arm's doc comment and body. Keep the `kids.len() >= 2 && self.is_arith_sorted(kids[0])` guard; the `else { t }` branch is unchanged.

```rust
            // ── Arithmetic equality: (= a b) → (= a b) ──────────────────────
            //
            // The bare Eq atom, so EUF sees x=y for congruence (QF_UFLRA/UFLIA).
            // Arith learns a=b through `arith_eq_axioms` (slice 53), which ties
            // E to (Le a b)/(Ge a b) in every polarity. The old
            // `(and E Le Ge)` was only sound in positive positions.
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Eq),
                args,
                ..
            } => {
                let kids: Vec<TermId> = self.ctx.children(args).to_vec();
                if kids.len() >= 2 && self.is_arith_sorted(kids[0]) {
                    if kids.len() == 2 {
                        return t;
                    }
                    // N-ary chain: the adjacent binary atoms, matching
                    // `arith_eq_atoms`.
                    let conj: Vec<TermId> = kids
                        .windows(2)
                        .map(|w| {
                            self.ctx
                                .mk_app(Op::Builtin(BuiltinOp::Eq), &[w[0], w[1]])
                                .expect("Eq well-sorted")
                        })
                        .collect();
                    self.ctx
                        .mk_app(Op::Builtin(BuiltinOp::And), &conj)
                        .expect("and well-sorted")
                } else {
                    t
                }
            }
```

Delete the old body's `Le`/`Ge` minting and the 3-per-pair `conj` vector.

- [ ] **Step 10: Run unit tests, probes and the oracle; all pass**

```bash
cargo nextest run -p shinri-solver -E 'test(arith_eq_atoms) | test(binary_arith_eq_lowers_bare)'
cargo nextest run -p shinri-solver -E 'binary(slice53_probes)'
cargo nextest run -p shinri-solver --features oracle -E 'binary(arith_polarity_oracle)' --no-capture
```

Expected: 4, 13 and 1 discovered, all PASS. The oracle prints non-zero `sat` and `unsat`, `unknown=0` and `disagreements=0` for both logics; record the counts and wall time in `slice53-notes.md`. If a probe still fails, debug with superpowers:systematic-debugging; do not loosen the assertion.

- [ ] **Step 11: Run the whole solver crate and the full blocking suite**

```bash
cargo nextest run -p shinri-solver
mise run test
```

Expected: all pass. A failure in an existing test that pins the old `(and E Le Ge)` shape or old counts (e.g. clause/atom counts) gets updated, with the reason in its comment. Any other failure is a real regression: stop and debug.

- [ ] **Step 12: Spot-check the 4 corpus rows with the new binary**

```bash
cargo build --release -p shinri-cli
for f in QF_LIA/calypto/problem-001542.cvc.1.smt2 QF_LIA/calypto/problem-001553.cvc.1.smt2 \
         QF_LRA/keymaera/simple_example_2-node2074.smt2 QF_LRA/keymaera/simple_example_2-node2406.smt2; do
  p=$(find bench/corpus -path "*$f"); echo "$f $(timeout 20 target/release/shinri $p | grep -v '^success$')"
done
```

Expected: `unsat` for all four. If a calypto row is still `sat`, it has a second cause: minimize it (same method as Task 3 Step 2), record it, and stop for a ruling (spec §7 criterion 1 is hard).

**Do not run this while the Task 1 base run is still going** if it would compete for cores 12–23. The release build itself is safe: the base run uses the copied binary.

- [ ] **Step 13: Lint, format, commit**

```bash
cargo fmt --all
mise run lint
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/slice53_probes.rs \
        crates/shinri-solver/tests/arith_polarity_oracle.rs
git commit -m "fix(solver): slice53 - tie every arithmetic = atom to Le/Ge in all polarities (wrong-sat under not/=>/iff/ite)"
```

---

### Task 3: Ramalho BVFP row (time-boxed)

**Files:**
- Modify: `crates/shinri-solver/tests/slice53_probes.rs` (append one test)
- Maybe modify: one encoding function in `crates/shinri-fp/src/` or `crates/shinri-bv/src/`, plus its unit test module

**Interfaces:**
- Consumes: the release binary from Task 2.
- Produces: either a fixed row (an `unsat` probe), or a known-bug marker probe plus a queued cause in `slice53-notes.md` for Task 4's report.

**Time box:** Steps 1–3 (minimize + root-cause). If, when Step 3 ends, the cause is not localized to one encoding function with an obvious fix, take the marker branch (Step 4b). Do not extend the box.

- [ ] **Step 1: Confirm the row is untouched by Task 2**

```bash
R=$(find bench/corpus -path '*ramalho/esbmc/Float-no-simp9-main.smt2')
timeout 20 target/release/shinri $R | grep -v '^success$'   # expected: sat
timeout 60 z3 $R                                             # expected: unsat
```

- [ ] **Step 2: Minimize (throwaway script, scratchpad only)**

Write `$SCRATCH/ddmin.py` (`$SCRATCH` = this session's scratchpad directory; never commit it). It:

1. parses the file into top-level commands with a parenthesis-depth counter that respects `|…|` quoted symbols and `"…"` strings;
2. keeps every `set-logic`/`declare-*`/`define-*` command and runs ddmin over the `assert` commands;
3. defines a candidate as interesting when `target/release/shinri` prints `sat` and `z3 -T:30` prints `unsat`;
4. then, for each surviving `assert`, tries replacing each `(=> A B)` subterm with `B`, and each `(and …)` conjunct list with a shorter one, keeping the change when it stays interesting;
5. finally drops `declare-fun`s whose symbol no longer occurs.

```bash
python3 $SCRATCH/ddmin.py $R > $SCRATCH/ramalho-min.smt2
wc -c $SCRATCH/ramalho-min.smt2
target/release/shinri $SCRATCH/ramalho-min.smt2; z3 $SCRATCH/ramalho-min.smt2
```

Expected: a core of at most a few KB that is still shinri `sat` / z3 `unsat`.

- [ ] **Step 3: Root-cause**

```bash
( cat $SCRATCH/ramalho-min.smt2 | sed 's/(check-sat)/(set-option :produce-models true)(check-sat)(get-model)/' ) > $SCRATCH/m.smt2
target/release/shinri $SCRATCH/m.smt2 > $SCRATCH/model.txt
```

Substitute shinri's model into the core as `define-fun`s, assert each original assertion separately in z3, and find the one z3 evaluates to `false`. Reduce that assertion to the smallest FP predicate that disagrees (expected suspects: `fp.isNegative` on `-0.0`/NaN, `fp.eq` vs `=` on ±0). Then locate its encoding:

```bash
grep -rn "IsNegative\|FpIsNeg\|fn .*is_negative\|FpEq" crates/shinri-fp/src crates/shinri-bv/src | head
```

Write the cause (predicate, inputs, shinri's value vs the IEEE value, the file:line of the encoding) into `slice53-notes.md`.

- [ ] **Step 4a (local fix): Pin, fix, verify**

Append to `slice53_probes.rs` (paste the minimized core in place of `PASTE:`; the core comes from Step 2's file):

```rust
/// Corpus row `QF_BVFP/ramalho/esbmc/Float-no-simp9-main.smt2` (z3 unsat;
/// shinri `sat` at `2ceef06`), minimized. Cause: <one line from Step 3>.
#[test]
fn ramalho_min_core() {
    const SRC: &str = r#"PASTE: contents of ramalho-min.smt2 without (check-sat)/(exit)"#;
    assert_eq!(run_script(&format!("{SRC}(check-sat)")), vec!["unsat".to_string()]);
}
```

Run `cargo nextest run -p shinri-solver -E 'test(ramalho_min_core)'` and confirm it FAILS. Add a unit test in the encoding's crate that checks the fixed predicate on the disagreeing input, and confirm it fails too. Fix the encoding, then re-run both (PASS) plus:

```bash
cargo nextest run -p shinri-fp
cargo nextest run -p shinri-solver --features oracle -E 'binary(fp_oracle)' --no-capture
timeout 20 target/release/shinri $R | grep -v '^success$'   # expected after rebuild: unsat
```

`fp_oracle` contains `differential_qf_fp_rem` (~25 min, pre-existing). Run it once, at the end of this task, and record its time. If the touched encoding is covered by an exhaustive `#[ignore]`d `shinri-fp` suite, run only that suite once with `--run-ignored only -E 'test(<name>)'` and record the result. Never remove the `#[ignore]`.

Commit:

```bash
cargo fmt --all && mise run lint
git add crates/shinri-solver/tests/slice53_probes.rs crates/shinri-fp crates/shinri-bv
git commit -m "fix(fp): slice53 - <predicate> on <input> (ramalho wrong-sat)"
```

- [ ] **Step 4b (marker branch): Pin the known bug and queue it**

Append to `slice53_probes.rs`:

```rust
/// KNOWN BUG (slice 53, queued): corpus row
/// `QF_BVFP/ramalho/esbmc/Float-no-simp9-main.smt2`, minimized; z3 unsat,
/// shinri `sat`. Cause hypothesis: <one line from Step 3>. This is a passing
/// marker asserting today's wrong `sat` (slice-52 R16 style); flip it to
/// `unsat` when the fix lands.
#[test]
fn ramalho_min_core_known_wrong_sat() {
    const SRC: &str = r#"PASTE: contents of ramalho-min.smt2 without (check-sat)/(exit)"#;
    assert_eq!(run_script(&format!("{SRC}(check-sat)")), vec!["sat".to_string()]);
}
```

Run it (PASS), then commit:

```bash
cargo fmt --all
git add crates/shinri-solver/tests/slice53_probes.rs
git commit -m "test(fp): slice53 - pin ramalho minimized wrong-sat as a known-bug marker (queued)"
```

---

### Task 4: Gates, after-run, report

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice53-arith-eq-polarity-report.md`
- Modify: `docs/superpowers/specs/2026-10-01-shinri-slice53-arith-eq-polarity-design.md` (§12)

**Interfaces:**
- Consumes: `bench/results/slice53-base` (Task 1), `slice53-notes.md` (Tasks 1–3).

- [ ] **Step 1: Gates** (before the bench, so they don't share cores with it)

```bash
cargo fmt --all -- --check
mise run lint
mise run test
cargo nextest run -p shinri-solver --features oracle 2>&1 | tee target/slice53-oracle.log | tail -5
```

Expected: all green. The oracle log shows a non-zero "N tests run" (701 discovered at slice 52, plus 1 new), with every test passed or skipped. Record the counts.

- [ ] **Step 2: After-run** (the base run must be finished)

```bash
cargo build --release -p shinri-cli -p shinri-bench
md5sum target/release/shinri
BENCH_LOGICS=QF_LIA,QF_LRA,QF_BVFP,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA BENCH_RUN_ID=slice53 \
  taskset -c 12-23 mise run bench-run
BENCH_RUN_ID=slice53 mise run bench-report
```

- [ ] **Step 3: Transitions** (scratch script, not committed)

```python
# $SCRATCH/transitions.py
import json, collections, sys
def load(p):
    rows = {}
    for l in open(p):
        r = json.loads(l)
        if "path" in r: rows[r["path"]] = r
    return rows
a = load("bench/results/slice53-base/results.jsonl")
b = load("bench/results/slice53/results.jsonl")
assert a.keys() == b.keys(), (len(a.keys() - b.keys()), len(b.keys() - a.keys()))
print("common paths:", len(a))
t = collections.Counter(); fam = collections.defaultdict(collections.Counter)
for p in a:
    x, y = a[p]["verdict"], b[p]["verdict"]
    if x != y:
        k = (a[p]["logic"], x, y); t[k] += 1
        fam[k][p.split("/")[1]] += 1
        if y == "wrong": print("ESCALATE", p, x, "->", y)
        if x == "correct" and (y.startswith("unknown") or y == "timeout"): print("LOSS", p, y)
for k, n in sorted(t.items()):
    print(*k, n, dict(fam[k]))
net = collections.Counter()
for (lg, x, y), n in t.items():
    net[lg] += n * ((y == "correct") - (x == "correct"))
print("net correct per logic:", dict(net))
```

Expected: no `ESCALATE` line. `net correct` is ≥ 0 for every logic, and the 4 arithmetic rows show `wrong → correct`. **Any `ESCALATE`, or a negative net for any logic: stop and ask for a ruling before writing the report as final** (spec §7 criteria 3–4). Every `LOSS` line goes into the report with a triage (cause or noise, with evidence: re-run the row 3× at 20 s with both binaries).

- [ ] **Step 4: Write the report**

Follow the structure of `docs/superpowers/research/2026-10-01-smtlib-2024-slice52-str-bool-eq-report.md`:

- title line with run-id and fixture sha;
- commands; run table (run, solver, md5, started, finished, wall-clock), using the Step 3 md5 from Task 1 for `slice53-base` and stating that the fixture sha records the checkout, not the binary;
- load disclosure;
- how the transitions were computed;
- Headline;
- Success criteria (spec §7 table with results);
- per-logic matrix for both runs, copied from each `report.md`;
- transition matrices (changed cells only);
- every formerly `wrong` row: before/after/z3, plus any extra `wrong` rows from Task 1 Step 5 with their disposition;
- every `correct → unknown/timeout` row, triaged;
- timing: median/p90 per logic, base vs after (criterion 6);
- oracle and probe evidence: the before counts from Task 2 Step 4, the after counts from Step 10, discovered/passed/skipped totals;
- Ramalho: minimized core size, cause, and the fix or marker;
- Gates;
- Queued for the next slice: the `Not(Eq)` arm removal (if timing allows), ramalho if on the marker branch, and every slice-52 queue item carried forward verbatim;
- References.

- [ ] **Step 5: Fill spec §12 Measured outcomes**

Replace `To be filled in from the `slice53` report.` with the criteria table (result per row), the credited gain (solver-attributable, separated from z3-oracle noise as in slice 52), the run ids and fixture, and any deviations from the spec text. The deviations include `arith_polarity_oracle.rs` instead of `oracle.rs`.

- [ ] **Step 6: Commit, push, PR**

```bash
git add docs/superpowers/research/*slice53* docs/superpowers/specs/2026-10-01-shinri-slice53-arith-eq-polarity-design.md
git commit -m "docs(bench+spec): slice53 - re-run report and measured outcomes"
git push -u origin slice53-arith-eq-polarity
gh pr create --base main --title "slice53: arithmetic = under non-positive polarity (+ ramalho)" \
  --body "Spec: docs/superpowers/specs/2026-10-01-shinri-slice53-arith-eq-polarity-design.md
Report: docs/superpowers/research/<file>. Criteria table: see spec §12."
```

Then wait for CI to go green, merge with a merge commit, and delete the branch on the remote and locally (AGENTS.md conventions).
