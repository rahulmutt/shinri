# Slice 54 — Purify compound Bool arguments Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove the wrong `sat` on every compound Bool-sorted argument of a non-connective parent (UF, datatype constructor/selector, `select`/`store`) by replacing the argument with a fresh internal Bool proxy plus a defining iff.

**Architecture:** A new item 3 in `WordNorm::walk` (`crates/shinri-solver/src/word_norm.rs`). After a node's children are rewritten, if the node is not a Boolean connective, each Bool-sorted child that is not a Bool constant or a nullary symbol is replaced by a memoized proxy `bool!<n>`, and `(= b t)` is appended to the definitions. `word_norm` runs first in `check_sat` (`lib.rs:772`), so every solve path sees purified terms. No other file in `src/` changes.

**Tech Stack:** Rust (toolchain pinned via `mise`, Rust 1.99.0 after Task 1), cargo-nextest, z3 4.16.0 from mise for the oracle (`easy_smt` in oracle tests), `shinri-bench` for corpus runs.

**Spec:** `docs/superpowers/specs/2026-10-02-shinri-slice54-uf-bool-arg-purify-design.md`

## Global Constraints

- Branch: `slice54-uf-bool-arg-purify` off `main`. PR to `main`, merged with a merge commit when CI is green; then delete the branch (remote and local).
- Pure Rust: no new dependencies (`deny.toml` bans native-link crates).
- No change to the parser, `lower`, Tseitin, EUF, the Combiner, any fence predicate, the theory crates or the string model gate (spec §4). The only `src/` file that changes is `crates/shinri-solver/src/word_norm.rs`.
- Proxy names are `bool!<n>`; ite names stay `ite!<n>`. Both are minted through `fresh_var` (collision probe + `reserve_symbol` + `internal`).
- Never remove `#[ignore]` from the exhaustive `shinri-fp` suites (`fp_div/fp_mul/fp_add` `_tiny_exhaustive_all_modes`, `to_fp_fp_tiny_exhaustive_both_directions`, `rem_tiny_exhaustive`).
- Oracle tests run only with `--features oracle`. Always confirm a non-zero discovered count; a 0-test run is not green.
- nextest filters use `-E 'test(<name>)'` or `-E 'binary(<name>)'`, never a positional filter.
- No new test may take > 5 min; the new oracle binary's target is < 30 s.
- `cargo fmt --all` before every commit; `cargo clippy --workspace --all-targets -- -D warnings` clean (`mise run lint`).
- Bench limits: 20 s, 3072 MB, 6 jobs, `taskset -c 12-23`. Logics: QF_UF, QF_DT, QF_UFLIA, QF_UFLRA.
- Stop for a ruling (do not ship) on any `* → wrong` row, any `decided → unknown` flip caused by the fix, or a net `correct` loss in any logic (spec §3.5, §7 criteria 3–4).

## Review Focus

Inputs the spec implies but its listed tests don't exercise. Each has a test in Task 3's `slice54_probes.rs`:

1. **`push`/`pop` around a purified argument.** The proxy map outlives scopes, but definitions are re-emitted per `check-sat` from the live assertions, so a popped scope must not leave a stale constraint, and a re-pushed one must reuse the proxy correctly. Test: `push_pop_reuses_proxy_soundly` (HEAD answers `sat sat sat`; z3 answers `unsat sat unsat`).
2. **Incremental `check-sat` after the pinning assertion arrives.** Test: `incremental_pin_after_first_check` (HEAD `sat sat`; z3 `sat unsat`).
3. **A Bool-argument UF over a string predicate (string path).** `(P (= (str.len s) 1))` is wrong `sat` on HEAD. After the fix it must not be `sat`. `unknown` is acceptable because the string model gate evaluates the user's original assertions. Test: `string_path_bool_arg_is_not_sat`.
4. **A user declaring `bool!0` after a `check-sat` minted it.** It must be rejected as reserved, as `ite!0` is (`script_e2e.rs::post_mint_declaration_of_internal_name_is_rejected`). Test: `post_mint_declaration_of_bool_proxy_is_rejected`.
5. **A purified argument inside an eliminated term-level `ite` branch.** `(= (ite p (f (= x 1)) 0) 7)`: both the ite elimination and the purification act on the same term. Test: `proxy_inside_eliminated_term_ite` (HEAD `sat`; z3 `unsat`).

---

## File Structure

| file | change | responsibility |
| --- | --- | --- |
| `crates/shinri-solver/src/word_norm.rs` | modify | module doc item 3; `bool_arg_var` map; `fresh_var` prefix parameter; `is_bool_connective`, `needs_bool_proxy`, `bool_proxy`; the purification loop in `walk`; unit tests |
| `crates/shinri-solver/tests/slice54_probes.rs` | create | blocking-tier e2e probes: spec §1.2 shapes, §6.2 list, fence pins, model hygiene, Review Focus 1–5 |
| `crates/shinri-solver/tests/bool_arg_oracle.rs` | create | `oracle`-feature differential families vs z3: QF_UFLIA, QF_UFLRA, QF_DT |
| `mise.toml` | modify | Rust 1.98.1 → 1.99.0 (already in the working tree) |
| `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice54-uf-bool-arg-report.md` | create | measurement report (date = day the after-run finishes) |
| `docs/superpowers/specs/2026-10-02-shinri-slice54-uf-bool-arg-purify-design.md` | modify | §11 Measured outcomes |

**Deviation from spec §6.3, recorded in §11:** the oracle family is three tests (`differential_bool_arg_uflia`, `differential_bool_arg_uflra`, `differential_bool_arg_dt`) in one binary, not a single `differential_bool_arg`, so that each sub-family can be filtered and reported on its own.

---

### Task 1: Branch, toolchain commit, base bench run

**Files:**
- Modify: `mise.toml` (already changed in the working tree: `rust = { version = "1.99.0", … }`)

**Interfaces:**
- Produces: `bench/results/slice54-base/{results.jsonl,report.md}` and the frozen binary `target/slice54-base/shinri`, both consumed by Task 4.

The base run uses a **copied** binary, so later rebuilds of `target/release/shinri` cannot swap it mid-run. Start it, then go on to Task 2 in parallel. **Do not run anything else pinned to cores 12–23 while it runs.**

- [ ] **Step 1: Commit this plan to `main`, then branch**

The spec is already on `main` (`03dd750`). Spec+plan pairs live on `main` (AGENTS.md).

```bash
git checkout main
git add docs/superpowers/plans/2026-10-02-shinri-slice54-uf-bool-arg-purify.md
git commit -m "docs(plan): slice54 - purify compound Bool arguments"
git checkout -b slice54-uf-bool-arg-purify
git status --short   # expected: " M mise.toml" only
```

- [ ] **Step 2: Toolchain commit**

```bash
mise install
rustc --version                      # expected: rustc 1.99.0
cargo fmt --all --check && cargo clippy --workspace --all-targets -- -D warnings
git add mise.toml
git commit -m "chore(toolchain): rust 1.99.0"
```

Expected: fmt and clippy are clean, as measured during brainstorming. If a 1.99 lint fires, fix it in this commit.

- [ ] **Step 3: Confirm the corpus is present**

```bash
for l in QF_UF QF_DT QF_UFLIA QF_UFLRA; do printf '%s ' $l; find bench/corpus/$l -name '*.smt2' | wc -l; done
```

Expected: 7503, 8700, 659, 1284. If a logic is missing: `BENCH_LOGICS=<logic> mise run bench-fetch`.

- [ ] **Step 4: Build and freeze the base binary**

The branch carries only docs and `mise.toml` on top of `61be117`, so the crate sources are identical. The base binary is built with Rust 1.99.0, the same toolchain as the after-run, which keeps the comparison toolchain-neutral.

```bash
git diff --stat 61be117 HEAD -- crates   # expected: empty
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice54-base && cp target/release/shinri target/slice54-base/shinri
md5sum target/slice54-base/shinri | tee target/slice54-base/md5.txt
```

- [ ] **Step 5: Start the base run in the background**

```bash
taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_UF,QF_DT,QF_UFLIA,QF_UFLRA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice54-base/shinri --run-id slice54-base \
  > target/slice54-base/run.log 2>&1
```

Run it with the Bash tool's `run_in_background`; it re-invokes you when it exits. Record the start and finish time for the report's run table. The fixture header records the checkout HEAD, not the binary's commit (known harness nit). The report must state that the binary is built from `61be117` sources, citing the md5 from Step 4.

- [ ] **Step 6: When it finishes, render the report and record the wrong rows**

```bash
target/release/shinri-bench report bench/results/slice54-base
tail -1 target/slice54-base/run.log
python3 - <<'EOF'
import json
for l in open("bench/results/slice54-base/results.jsonl"):
    r = json.loads(l)
    if r.get("verdict") == "wrong": print(r["path"], r["answers"], r["status"])
EOF
```

Copy the list (possibly empty) into the scratchpad note `slice54-notes.md`. Task 4 checks each row against the fix.

---

### Task 2: Oracle family (written first; must disagree at HEAD)

**Files:**
- Create: `crates/shinri-solver/tests/bool_arg_oracle.rs`

**Interfaces:**
- Consumes: the public `shinri_solver::{Solver, CommandResponse, SolveOutcome}` and `shinri_parser::Parser`, unchanged.
- Produces: tests `differential_bool_arg_uflia`, `differential_bool_arg_uflra`, `differential_bool_arg_dt`, binary `bool_arg_oracle`. Task 3 re-runs them after the fix; Task 4 records the counts.

This task changes no `src/` code. It is committed before the fix and fails on purpose under `--features oracle`. CI runs the oracle job only on the PR, whose head includes Task 3. `mise run test` stays green because the binary is `#![cfg(feature = "oracle")]`.

- [ ] **Step 1: Write the oracle binary**

```rust
//! Differential oracle (slice 54, spec §6.3): uninterpreted functions and a
//! datatype constructor applied to compound Bool arguments, checked against
//! z3. Arguments are drawn from a small shared atom pool so that two
//! applications often receive equivalent arguments — congruence then has to
//! see through the argument's truth value, which is exactly what the slice-54
//! wrong `sat` broke (a compound Bool argument was an opaque e-graph node).
//!
//! Run with:
//!   cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle)'
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

#[derive(Clone, Copy, PartialEq)]
enum Family {
    UfLia,
    UfLra,
    Dt,
}

impl Family {
    fn logic(self) -> &'static str {
        match self {
            Family::UfLia => "QF_UFLIA",
            Family::UfLra => "QF_UFLRA",
            Family::Dt => "QF_DT",
        }
    }
    fn decls(self) -> &'static str {
        match self {
            Family::UfLia => {
                "(declare-const p Bool)\n(declare-const q Bool)\n\
                 (declare-const x Int)\n(declare-const y Int)\n\
                 (declare-fun P (Bool) Bool)\n(declare-fun f (Bool Int) Int)\n"
            }
            Family::UfLra => {
                "(declare-const p Bool)\n(declare-const q Bool)\n\
                 (declare-const x Real)\n(declare-const y Real)\n\
                 (declare-fun P (Bool) Bool)\n(declare-fun f (Bool Real) Real)\n"
            }
            Family::Dt => {
                "(declare-datatypes ((B 0)) (((mk (fa Bool) (fb Bool)) (nil))))\n\
                 (declare-const p Bool)\n(declare-const q Bool)\n\
                 (declare-const u B)\n(declare-const v B)\n"
            }
        }
    }
    /// The shared atom pool: Bool variables plus theory atoms.
    fn leaves(self) -> &'static [&'static str] {
        match self {
            Family::UfLia => &["p", "q", "(= x 1)", "(<= y 0)", "(= x y)"],
            Family::UfLra => &["p", "q", "(= x 1.0)", "(<= y 0.0)", "(= x y)"],
            Family::Dt => &["p", "q", "(fa u)", "((_ is mk) v)", "(= u v)"],
        }
    }
    fn lit(self, k: u64) -> String {
        match self {
            Family::UfLra => format!("{k}.0"),
            _ => format!("{k}"),
        }
    }
}

fn leaf(rng: &mut Lcg, fam: Family) -> String {
    let ls = fam.leaves();
    ls[rng.below(ls.len() as u64) as usize].to_string()
}

fn formula(rng: &mut Lcg, fam: Family, depth: u32) -> String {
    if depth == 0 || rng.below(3) == 0 {
        return leaf(rng, fam);
    }
    let k = rng.below(5);
    let mut f = || formula(rng, fam, depth - 1);
    match k {
        0 => format!("(not {})", f()),
        1 => format!("(and {} {})", f(), f()),
        2 => format!("(or {} {})", f(), f()),
        3 => format!("(=> {} {})", f(), f()),
        _ => format!("(xor {} {})", f(), f()),
    }
}

/// A Bool argument: `true`/`false` (so congruence with a constant matters)
/// or a depth-≤1 formula (a leaf or one connective over leaves).
fn arg(rng: &mut Lcg, fam: Family) -> String {
    match rng.below(5) {
        0 => "true".to_string(),
        1 => "false".to_string(),
        _ => formula(rng, fam, 1),
    }
}

fn assertion(rng: &mut Lcg, fam: Family) -> String {
    let k = rng.below(6);
    if k >= 4 {
        // Pins on the atom pool, so the arguments' truth values are forced.
        return if k == 4 {
            formula(rng, fam, 2)
        } else {
            format!("(not {})", formula(rng, fam, 1))
        };
    }
    match fam {
        Family::Dt => match k {
            0 => format!("(= u (mk {} {}))", arg(rng, fam), arg(rng, fam)),
            1 => format!("(= v (mk {} {}))", arg(rng, fam), arg(rng, fam)),
            2 => format!(
                "(distinct (mk {} {}) (mk {} {}))",
                arg(rng, fam),
                arg(rng, fam),
                arg(rng, fam),
                arg(rng, fam)
            ),
            _ => {
                if rng.below(2) == 0 {
                    "(= u v)".to_string()
                } else {
                    "(not (= u v))".to_string()
                }
            }
        },
        _ => match k {
            0 => format!("(P {})", arg(rng, fam)),
            1 => format!("(not (P {}))", arg(rng, fam)),
            2 => format!("(= (f {} x) {})", arg(rng, fam), fam.lit(rng.below(3))),
            _ => format!("(distinct (f {} y) (f {} y))", arg(rng, fam), arg(rng, fam)),
        },
    }
}

fn gen_script(rng: &mut Lcg, fam: Family) -> String {
    let mut src = String::from(fam.decls());
    for _ in 0..3 + rng.below(3) {
        src.push_str(&format!("(assert {})\n", assertion(rng, fam)));
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
        if t.starts_with("(declare-") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

fn run_family(fam: Family, seed: u64) {
    let mut rng = Lcg(seed);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut disagreements: Vec<String> = Vec::new();
    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng, fam);
        let ours = shinri_outcome(fam.logic(), &src);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => {
                n_unknown += 1;
                continue;
            }
        }
        match (ours, z3_outcome(fam.logic(), &src)) {
            (SolveOutcome::Sat, easy_smt::Response::Sat)
            | (SolveOutcome::Unsat, easy_smt::Response::Unsat)
            | (_, easy_smt::Response::Unknown) => {}
            (o, t) => disagreements.push(format!("iter {iter}: shinri={o:?} z3={t:?}\n{src}")),
        }
    }
    println!(
        "{}: sat={n_sat} unsat={n_unsat} unknown={n_unknown} disagreements={}",
        fam.logic(),
        disagreements.len()
    );
    assert!(
        disagreements.is_empty(),
        "{} disagreements; first three:\n{}",
        disagreements.len(),
        disagreements
            .iter()
            .take(3)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "need both sat ({n_sat}) and unsat ({n_unsat})"
    );
}

#[test]
fn differential_bool_arg_uflia() {
    run_family(Family::UfLia, 0x51CE_0054_0001);
}

#[test]
fn differential_bool_arg_uflra() {
    run_family(Family::UfLra, 0x51CE_0054_0002);
}

#[test]
fn differential_bool_arg_dt() {
    run_family(Family::Dt, 0x51CE_0054_0003);
}
```

- [ ] **Step 2: Run it at HEAD (before the fix) and record the "before" evidence**

```bash
cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle)' --no-capture 2>&1 \
  | tee target/slice54-oracle-before.log | grep -E "QF_|tests? run|FAIL|PASS"
```

Expected: 3 tests discovered. Each family **FAILS** with `disagreements > 0`, and each line `QF_…: sat=… unsat=… unknown=… disagreements=N` shows N > 0. Copy the three lines into `slice54-notes.md`.

If a family shows `disagreements=0` at HEAD, the generator does not reach the defect. Strengthen it before going on. In order: raise the `(P …)`/`(not (P …))` share in `assertion` (e.g. `k` in `0..=1` for 4 of 8 draws), then add `true`/`false` to `leaves`. Re-run until N > 0, and record the change in the notes.

Also record the wall-clock from nextest's summary. It must be < 30 s; if not, lower `N_ITERS` to 120 and re-run.

- [ ] **Step 3: Commit**

```bash
cargo fmt --all
cargo clippy -p shinri-solver --all-targets --features oracle -- -D warnings
git add crates/shinri-solver/tests/bool_arg_oracle.rs
git commit -m "test(oracle): slice54 - bool-argument differential families (fail at HEAD)"
```

---

### Task 3: Purification in `word_norm` (tests first)

**Files:**
- Modify: `crates/shinri-solver/src/word_norm.rs` (module doc lines 1–23; struct `WordNorm` lines 27–56; `fresh_var` lines 99–118; `walk` lines 120–262; `mod tests` from line 265)
- Create: `crates/shinri-solver/tests/slice54_probes.rs`

**Interfaces:**
- Consumes: `shinri_core::{Context, Op, BuiltinOp, TermNode, TermId, SortId}`; `Context::{bool_sort, sort_of, term_node, children, mk_app, declare_fun, reserve_symbol, lookup_symbol, mk_const_bool}`.
- Produces (all private to `word_norm.rs`):
  - field `bool_arg_var: FxHashMap<TermId, TermId>`
  - `fn fresh_var(&mut self, ctx: &mut Context, sort: SortId, prefix: &str) -> TermId` (was `(ctx, sort)`)
  - `fn is_bool_connective(op: Op) -> bool` (free function)
  - `fn needs_bool_proxy(ctx: &Context, t: TermId) -> bool` (free function)
  - `fn bool_proxy(&mut self, ctx: &mut Context, t: TermId, defs: &mut Vec<TermId>, seen_defs: &mut FxHashSet<TermId>) -> TermId`
  - The public surface (`WordNorm::normalize`, `pub internal`) is unchanged.

- [ ] **Step 1: Write the e2e probes**

Create `crates/shinri-solver/tests/slice54_probes.rs`. Every script below was run on HEAD `61be117` against z3 4.16.0 during planning. Each `*_unsat` body answers `sat` on HEAD, and each sibling is `sat` per z3.

```rust
//! Slice 54 probes (spec §6.2). A compound Bool term used as an argument of a
//! non-connective parent (UF, datatype constructor/selector) was an opaque
//! e-graph node, never tied to its truth value, so `(P t)` and `(P true)`
//! could differ while `t` held (wrong `sat`). `word_norm` now replaces such an
//! argument with an internal proxy `bool!<n>` plus `(= b t)`. Every `unsat`
//! case here answered `sat` at `61be117` unless marked "regression pin"; each
//! has a `sat` sibling so the fix cannot pass by over-refuting.
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

const UFLIA: &str = "(set-logic QF_UFLIA)(declare-fun p () Bool)(declare-fun q () Bool)\
    (declare-fun x () Int)(declare-fun y () Int)(declare-fun P (Bool) Bool)\
    (declare-fun f (Bool) Int)(declare-fun F (Bool Int Bool) Int)";
const UFLRA: &str = "(set-logic QF_UFLRA)(declare-fun x () Real)(declare-fun P (Bool) Bool)";
const UF: &str = "(set-logic QF_UF)(declare-sort U 0)(declare-fun a () U)(declare-fun b () U)\
    (declare-fun q () Bool)(declare-fun P (Bool) Bool)";
const DT: &str = "(set-logic QF_DT)(declare-datatypes ((B 0)) (((mk (fld Bool)))))\
    (declare-fun y () B)(declare-fun q () Bool)(declare-fun r () Bool)";

fn verdict(header: &str, body: &str) -> String {
    let out = run_script(&format!("{header}{body}(check-sat)"));
    out.first().cloned().unwrap_or_default()
}

/// Asserts `body` is unsat and `sibling` (one constraint relaxed) is sat.
fn pair(header: &str, body: &str, sibling: &str) {
    assert_eq!(verdict(header, body), "unsat", "{header}{body}");
    assert_eq!(verdict(header, sibling), "sat", "{header}{sibling}");
}

// ── spec §1.2 ──────────────────────────────────────────────────────────────

#[test]
fn r1_int_eq_argument() {
    pair(
        UFLIA,
        "(assert (P (= x 1)))(assert (not (P true)))(assert (= x 1))",
        "(assert (P (= x 1)))(assert (not (P true)))(assert (= x 2))",
    );
}

#[test]
fn r2_distinct_over_int_valued_uf() {
    pair(
        UFLIA,
        "(assert (distinct (f (= x 1)) (f true)))(assert (= x 1))",
        "(assert (distinct (f (= x 1)) (f true)))(assert (= x 2))",
    );
}

#[test]
fn r3_int_le_argument() {
    pair(
        UFLIA,
        "(assert (P (<= x 1)))(assert (not (P true)))(assert (= x 0))",
        "(assert (P (<= x 1)))(assert (not (P true)))(assert (= x 2))",
    );
}

#[test]
fn r4_uninterpreted_sort_eq_argument() {
    pair(
        UF,
        "(assert (P (= a b)))(assert (not (P true)))(assert (= a b))",
        "(assert (P (= a b)))(assert (not (P true)))(assert (distinct a b))",
    );
}

#[test]
fn r5_pure_boolean_argument() {
    pair(
        UF,
        "(assert (P (and q q)))(assert (not (P true)))(assert q)",
        "(assert (P (and q q)))(assert (not (P true)))(assert (not q))",
    );
}

/// Regression pin: a bare Bool constant argument was already linked.
#[test]
fn r6_bare_bool_constant_argument() {
    pair(
        UF,
        "(assert (P q))(assert (not (P true)))(assert q)",
        "(assert (P q))(assert (not (P true)))(assert (not q))",
    );
}

#[test]
fn r7_false_side() {
    pair(
        UFLIA,
        "(assert (P (= x 1)))(assert (not (P false)))(assert (not (= x 1)))",
        "(assert (P (= x 1)))(assert (not (P false)))(assert (= x 1))",
    );
}

#[test]
fn uflra_eq_argument() {
    pair(
        UFLRA,
        "(assert (P (= x 1.0)))(assert (not (P true)))(assert (= x 1.0))",
        "(assert (P (= x 1.0)))(assert (not (P true)))(assert (= x 2.0))",
    );
}

#[test]
fn uflra_le_argument() {
    pair(
        UFLRA,
        "(assert (P (<= x 1.0)))(assert (not (P true)))(assert (= x 0.5))",
        "(assert (P (<= x 1.0)))(assert (not (P true)))(assert (= x 1.5))",
    );
}

#[test]
fn s5_datatype_constructor_argument() {
    pair(
        DT,
        "(assert (= (mk (and q r)) (mk true)))(assert (not q))",
        "(assert (= (mk (and q r)) (mk true)))(assert q)",
    );
}

#[test]
fn datatype_selector_over_purified_field() {
    pair(
        DT,
        "(assert (= y (mk (and q r))))(assert (fld y))(assert (not q))",
        "(assert (= y (mk (and q r))))(assert (fld y))(assert r)",
    );
}

#[test]
fn multi_argument_uf() {
    pair(
        UFLIA,
        "(assert (distinct (F (= x 1) y (and p q)) (F true y false)))(assert (= x 1))(assert (not p))",
        "(assert (distinct (F (= x 1) y (and p q)) (F true y false)))(assert (= x 1))(assert p)(assert q)",
    );
}

#[test]
fn bool_argument_uf_under_arithmetic() {
    pair(
        UFLIA,
        "(assert (= (f true) 5))(assert (< (f (= x 1)) 3))(assert (= x 1))",
        "(assert (= (f true) 5))(assert (< (f (= x 1)) 3))(assert (= x 2))",
    );
}

#[test]
fn nested_purification() {
    pair(
        UFLIA,
        "(assert (P (P (and p q))))(assert (not (P (P true))))(assert p)(assert q)",
        "(assert (P (P (and p q))))(assert p)(assert q)",
    );
}

// ── Fence pins: sound `unknown` today, must stay so (spec §3.5) ────────────

#[test]
fn fence_pin_ufbv_bool_argument_stays_unknown() {
    let h = "(set-logic QF_UFBV)(declare-fun x () (_ BitVec 4))(declare-fun P (Bool) Bool)";
    assert_eq!(
        verdict(h, "(assert (P (= x #x1)))(assert (not (P true)))(assert (= x #x1))"),
        "unknown"
    );
}

#[test]
fn fence_pin_bool_array_select_stays_unknown() {
    let h = "(set-logic QF_AUFLIA)(declare-fun a () (Array Int Bool))(declare-fun P (Bool) Bool)";
    assert_eq!(
        verdict(h, "(assert (P (select a 0)))(assert (not (P true)))(assert (select a 0))"),
        "unknown"
    );
}

#[test]
fn fence_pin_bool_array_store_stays_unknown() {
    let h = "(set-logic QF_AUFLIA)(declare-fun x () Int)(declare-fun a () (Array Int Bool))";
    assert_eq!(
        verdict(h, "(assert (= a (store a 0 (= x 1))))(assert (= x 1))(assert (not (select a 0)))"),
        "unknown"
    );
}

// ── Model hygiene ──────────────────────────────────────────────────────────

#[test]
fn get_model_has_no_proxy_symbols() {
    let out = run_script(
        "(set-logic QF_UFLIA)(set-option :produce-models true)(declare-fun x () Int)\
         (declare-fun P (Bool) Bool)(assert (P (= x 1)))(assert (not (P true)))\
         (assert (= x 2))(check-sat)(get-model)",
    );
    assert_eq!(out[0], "sat");
    assert!(out[1].contains("(define-fun x () Int 2)"), "{:?}", out[1]);
    assert!(!out[1].contains("bool!"), "proxy leaked into get-model: {:?}", out[1]);
}

// ── Review Focus ───────────────────────────────────────────────────────────

/// Review Focus 1. HEAD: sat sat sat; z3: unsat sat unsat.
#[test]
fn push_pop_reuses_proxy_soundly() {
    let out = run_script(&format!(
        "{UFLIA}(push 1)(assert (P (= x 1)))(assert (not (P true)))(assert (= x 1))(check-sat)(pop 1)\
         (assert (not (P true)))(assert (= x 1))(check-sat)\
         (push 1)(assert (P (= x 1)))(check-sat)(pop 1)"
    ));
    assert_eq!(out, vec!["unsat", "sat", "unsat"]);
}

/// Review Focus 2. HEAD: sat sat; z3: sat unsat.
#[test]
fn incremental_pin_after_first_check() {
    let out = run_script(&format!(
        "{UFLIA}(assert (P (= x 1)))(assert (not (P true)))(check-sat)(assert (= x 1))(check-sat)"
    ));
    assert_eq!(out, vec!["sat", "unsat"]);
}

/// Review Focus 3. HEAD: sat; z3: unsat. `unknown` is acceptable: the string
/// model gate evaluates the user's original assertions, which contain the UF.
#[test]
fn string_path_bool_arg_is_not_sat() {
    let v = verdict(
        "(set-logic QF_SLIA)(declare-fun s () String)(declare-fun P (Bool) Bool)",
        "(assert (P (= (str.len s) 1)))(assert (not (P true)))(assert (= s \"a\"))",
    );
    assert_ne!(v, "sat", "wrong sat on the string path");
}

/// Review Focus 4: mirrors script_e2e::post_mint_declaration_of_internal_name_is_rejected.
#[test]
fn post_mint_declaration_of_bool_proxy_is_rejected() {
    let out = run_script(&format!(
        "{UFLIA}(assert (P (= x 1)))(check-sat)\
         (declare-fun bool!0 () Bool)(assert bool!0)(check-sat)"
    ));
    assert_eq!(out.len(), 4, "sat / declare-error / use-error / sat: {out:?}");
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("reserved for solver-internal use"),
        "declaration of the minted name must be rejected, got {:?}",
        out[1]
    );
    assert!(out[2].starts_with("(error"), "use is undeclared, got {:?}", out[2]);
    assert_eq!(out[3], "sat");
}

/// Review Focus 5. HEAD: sat; z3: unsat.
#[test]
fn proxy_inside_eliminated_term_ite() {
    pair(
        UFLIA,
        "(assert (= (ite p (f (= x 1)) 0) 7))(assert p)(assert (= x 1))(assert (= (f true) 5))",
        "(assert (= (ite p (f (= x 1)) 0) 7))(assert p)(assert (= x 1))(assert (= (f true) 7))",
    );
}
```

- [ ] **Step 2: Run the probes at HEAD and record which fail**

```bash
cargo nextest run -p shinri-solver -E 'binary(slice54_probes)' 2>&1 | tee target/slice54-probes-before.log | tail -30
```

Expected: 23 tests discovered. **Pass** (pins): `r6_bare_bool_constant_argument`, the three `fence_pin_*`, and `get_model_has_no_proxy_symbols` (5 tests). **Fail** (wrong `sat`): the other 18. One caveat for `post_mint_declaration_of_bool_proxy_is_rejected`: at HEAD nothing is minted, so `bool!0` is a legal declaration, the output is `["sat", "sat"]`, and the test fails on the length assertion. If any count differs, stop and read the failing script before going on. Record the pass/fail list in `slice54-notes.md`.

- [ ] **Step 3: Write the failing unit tests in `word_norm.rs`**

Append to `mod tests` (after the last existing test). The helpers `bool_var`/`bv_var` already exist there.

```rust
    // ── Slice 54: compound Bool arguments → proxy + (= b t) ─────────────────

    fn int_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let s = ctx.int_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }
    /// Declares `name : Bool -> Bool` and returns the symbol.
    fn bool_pred(ctx: &mut Context, name: &str) -> shinri_core::SymbolId {
        let b = ctx.bool_sort();
        ctx.declare_fun(name, &[b], b)
    }

    #[test]
    fn compound_bool_argument_becomes_proxy_plus_definition() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let p = bool_pred(&mut ctx, "P");
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let pe = ctx.mk_app(Op::Uninterpreted(p), &[eq]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[pe]);
        assert_eq!(wn.internal.len(), 1);
        let b = *wn.internal.iter().next().unwrap();
        let pb = ctx.mk_app(Op::Uninterpreted(p), &[b]).unwrap();
        let def = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[b, eq]).unwrap();
        assert_eq!(out, vec![pb, def]);
        // The proxy is named bool!<n>.
        let TermNode::App { op: Op::Uninterpreted(sym), .. } = ctx.term_node(b).clone() else {
            panic!("proxy must be a nullary uninterpreted app");
        };
        assert_eq!(ctx.lookup_symbol("bool!0"), Some(sym));
    }

    #[test]
    fn bare_constants_and_connective_children_are_not_purified() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let q = bool_var(&mut ctx, "q");
        let p = bool_pred(&mut ctx, "P");
        let t = ctx.mk_const_bool(true);
        let pq = ctx.mk_app(Op::Uninterpreted(p), &[q]).unwrap();
        let pt = ctx.mk_app(Op::Uninterpreted(p), &[t]).unwrap();
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let conj = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[eq, q]).unwrap();
        let iff = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[q, eq]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[pq, pt, conj, iff]);
        assert_eq!(out, vec![pq, pt, conj, iff], "same TermIds, nothing appended");
        assert!(wn.internal.is_empty());
    }

    #[test]
    fn one_proxy_per_argument_term_across_parents_and_calls() {
        let mut ctx = Context::new();
        let q = bool_var(&mut ctx, "q");
        let r = bool_var(&mut ctx, "r");
        let p = bool_pred(&mut ctx, "P");
        let g = bool_pred(&mut ctx, "G");
        let qr = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[q, r]).unwrap();
        let pqr = ctx.mk_app(Op::Uninterpreted(p), &[qr]).unwrap();
        let gqr = ctx.mk_app(Op::Uninterpreted(g), &[qr]).unwrap();
        let mut wn = WordNorm::default();
        let out1 = wn.normalize(&mut ctx, &[pqr, gqr]);
        assert_eq!(wn.internal.len(), 1, "P and G share one proxy for (and q r)");
        assert_eq!(out1.len(), 3, "two rewritten atoms + ONE deduped definition");
        // Second check-sat: same proxy, definition re-emitted.
        let out2 = wn.normalize(&mut ctx, &[pqr]);
        assert_eq!(wn.internal.len(), 1);
        assert_eq!(out2.len(), 2);
        assert_eq!(out2[1], out1[2], "same hash-consed definition");
    }

    #[test]
    fn nested_bool_arguments_purify_bottom_up() {
        // (P (P (and q r))): inner (and q r) → b0, then (P b0) → b1.
        let mut ctx = Context::new();
        let q = bool_var(&mut ctx, "q");
        let r = bool_var(&mut ctx, "r");
        let p = bool_pred(&mut ctx, "P");
        let qr = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[q, r]).unwrap();
        let inner = ctx.mk_app(Op::Uninterpreted(p), &[qr]).unwrap();
        let outer = ctx.mk_app(Op::Uninterpreted(p), &[inner]).unwrap();
        let mut wn = WordNorm::default();
        let out = wn.normalize(&mut ctx, &[outer]);
        assert_eq!(wn.internal.len(), 2);
        let b0 = ctx.mk_app(Op::Uninterpreted(ctx.lookup_symbol("bool!0").unwrap()), &[]).unwrap();
        let b1 = ctx.mk_app(Op::Uninterpreted(ctx.lookup_symbol("bool!1").unwrap()), &[]).unwrap();
        let pb0 = ctx.mk_app(Op::Uninterpreted(p), &[b0]).unwrap();
        let pb1 = ctx.mk_app(Op::Uninterpreted(p), &[b1]).unwrap();
        let def0 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[b0, qr]).unwrap();
        let def1 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[b1, pb0]).unwrap();
        assert_eq!(out, vec![pb1, def0, def1]);
    }

    #[test]
    fn bool_ite_argument_is_purified_but_term_ite_condition_is_not() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let c = bool_var(&mut ctx, "c");
        let p = bool_pred(&mut ctx, "P");
        let f = ctx.declare_fun("f", &[ctx.bool_sort()], ctx.bool_sort());
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let fls = ctx.mk_const_bool(false);
        // (f (ite c (P (= x y)) false)): (= x y) → b0 as P's argument; the Bool
        // ite is Boolean structure (not eliminated) and is itself f's argument → b1.
        let pe = ctx.mk_app(Op::Uninterpreted(p), &[eq]).unwrap();
        let bite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[c, pe, fls]).unwrap();
        let fb = ctx.mk_app(Op::Uninterpreted(f), &[bite]).unwrap();
        let mut wn = WordNorm::default();
        wn.normalize(&mut ctx, &[fb]);
        assert_eq!(wn.internal.len(), 2, "one proxy for (= x y), one for the Bool ite");

        // (= (ite (= x y) x y) x): Int term ite → ite!; its condition is NOT purified.
        let tite = ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[eq, x, y]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[tite, x]).unwrap();
        let mut wn2 = WordNorm::default();
        wn2.normalize(&mut ctx, &[atom]);
        assert_eq!(wn2.internal.len(), 1, "only the ite! symbol");
        assert!(ctx.lookup_symbol("ite!0").is_some());
    }

    #[test]
    fn bool_proxy_name_skips_user_declared_collision() {
        let mut ctx = Context::new();
        let bs = ctx.bool_sort();
        ctx.declare_fun("bool!0", &[], bs);
        let q = bool_var(&mut ctx, "q");
        let r = bool_var(&mut ctx, "r");
        let p = bool_pred(&mut ctx, "P");
        let qr = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[q, r]).unwrap();
        let pqr = ctx.mk_app(Op::Uninterpreted(p), &[qr]).unwrap();
        let mut wn = WordNorm::default();
        wn.normalize(&mut ctx, &[pqr]);
        let b = *wn.internal.iter().next().unwrap();
        let user = ctx.mk_app(Op::Uninterpreted(ctx.lookup_symbol("bool!0").unwrap()), &[]).unwrap();
        assert_ne!(b, user, "proxy must not alias a user symbol");
    }
```

If the borrow checker rejects `ctx.declare_fun("f", &[ctx.bool_sort()], ctx.bool_sort())` or `ctx.mk_app(Op::Uninterpreted(ctx.lookup_symbol(..).unwrap()), &[])`, bind the inner value to a `let` first. The behaviour under test does not change.

- [ ] **Step 4: Run the unit tests to see them fail**

```bash
cargo nextest run -p shinri-solver -E 'test(compound_bool_argument_becomes_proxy_plus_definition) + test(bare_constants_and_connective_children_are_not_purified) + test(one_proxy_per_argument_term_across_parents_and_calls) + test(nested_bool_arguments_purify_bottom_up) + test(bool_ite_argument_is_purified_but_term_ite_condition_is_not) + test(bool_proxy_name_skips_user_declared_collision)'
```

Expected: 6 tests discovered. `bare_constants_and_connective_children_are_not_purified` passes (nothing is purified yet). The other 5 fail on `internal.len()` or the output vector.

- [ ] **Step 5: Implement**

(a) Module doc: after item 2 (line 14), add:

```rust
//! 3. **Bool-argument purification** (slice 54): a Bool-sorted child of a
//!    parent that is NOT a Boolean connective (UF and datatype applications,
//!    `select`/`store`) — other than `true`/`false` or a nullary symbol —
//!    becomes a fresh nullary Bool symbol `b` (`bool!<n>`) plus one appended
//!    definition `(= b t)` (Bool `=` is iff for Tseitin). Without it the
//!    argument was an opaque e-graph node, never tied to its truth value:
//!    `(P (= x 1))`, `(not (P true))`, `(= x 1)` was a wrong `sat`. `b` takes
//!    the same path as a user Bool constant (an EUF atom merged with ⊤/⊥), and
//!    the definition puts `t` in a Boolean position (so slice 53's arithmetic
//!    `=` axioms reach it).
```

and in the INVARIANTS list change the fresh-name bullet to:

```rust
//! - Fresh names `ite!<n>` / `bool!<n>` are probed against the symbol table so
//!   they can never alias a user symbol; model filtering keys on the
//!   `internal` TermId set, never on the name.
```

(b) Struct: add after `orig_ite`:

```rust
    /// Slice 54: compound Bool argument (post-child-rewrite) → its proxy
    /// symbol. Solver-lifetime, like `ite_var`: a shared argument and repeated
    /// check-sats reuse one proxy.
    bool_arg_var: FxHashMap<TermId, TermId>,
```

(c) `fresh_var`: add the prefix parameter.

```rust
    fn fresh_var(&mut self, ctx: &mut Context, sort: SortId, prefix: &str) -> TermId {
        loop {
            let name = format!("{prefix}{}", self.ctr);
```

(the rest of the body is unchanged). Update the ite call site in `walk`:

```rust
                    let w = self.fresh_var(ctx, ctx.sort_of(rebuilt), "ite!");
```

(d) Free functions next to `eliminates_ite_sort`:

```rust
/// Slice 54: parents whose Bool-sorted children sit in a Boolean position
/// (Tseitin encodes them as structure). Every other parent's Bool child is a
/// term-position argument and is purified. `Ite` is listed for both shapes:
/// a Bool ite is structure, and a term ite's condition stays Boolean in its
/// elimination definition `(ite c (= w x) (= w y))`.
fn is_bool_connective(op: Op) -> bool {
    matches!(
        op,
        Op::Builtin(
            BuiltinOp::Not
                | BuiltinOp::And
                | BuiltinOp::Or
                | BuiltinOp::Implies
                | BuiltinOp::Xor
                | BuiltinOp::Eq
                | BuiltinOp::Distinct
                | BuiltinOp::Ite
        )
    )
}

/// Slice 54: a Bool-sorted argument needs a proxy unless it is already a
/// single atom EUF links to ⊤/⊥: a Bool constant (`true`/`false`) or a
/// nullary symbol (a user Bool constant, or an earlier proxy).
fn needs_bool_proxy(ctx: &Context, t: TermId) -> bool {
    if ctx.sort_of(t) != ctx.bool_sort() {
        return false;
    }
    match ctx.term_node(t) {
        TermNode::Const { .. } => false,
        TermNode::App {
            op: Op::Uninterpreted(_),
            args,
            ..
        } => !ctx.children(*args).is_empty(),
        TermNode::App { .. } => true,
    }
}
```

(e) `bool_proxy` method, in `impl WordNorm` after `fresh_var`:

```rust
    /// Slice 54: the proxy for argument `t`, appending `(= b t)` once per call.
    fn bool_proxy(
        &mut self,
        ctx: &mut Context,
        t: TermId,
        defs: &mut Vec<TermId>,
        seen_defs: &mut FxHashSet<TermId>,
    ) -> TermId {
        let b = if let Some(&b) = self.bool_arg_var.get(&t) {
            b
        } else {
            let b = self.fresh_var(ctx, ctx.bool_sort(), "bool!");
            self.bool_arg_var.insert(t, b);
            b
        };
        let def = ctx
            .mk_app(Op::Builtin(BuiltinOp::Eq), &[b, t])
            .expect("(= b t) over Bool is well-sorted");
        if seen_defs.insert(def) {
            defs.push(def);
        }
        b
    }
```

(f) In `walk`, make `new_kids` mutable and purify before the rebuild:

```rust
        let mut new_kids: Vec<TermId> = kids
            .iter()
            .map(|&k| self.walk(ctx, k, memo, defs, seen_defs))
            .collect();
        // Slice 54 (item 3): purify compound Bool arguments of non-connectives.
        if !is_bool_connective(op) {
            for k in new_kids.iter_mut() {
                if needs_bool_proxy(ctx, *k) {
                    *k = self.bool_proxy(ctx, *k, defs, seen_defs);
                }
            }
        }
        // No-change ⇒ SAME TermId (hard requirement); otherwise rebuild.
```

The rest of `walk` is unchanged. The `Ite` arm reads `new_kids[0..3]`, and `Ite` is a connective, so its kids are never purified. The `Not` arm reads `kids[0]`/`new_kids[0]`, and `Not` is a connective too.

- [ ] **Step 6: Run unit tests and probes**

```bash
cargo nextest run -p shinri-solver -E 'binary(slice54_probes)' 2>&1 | tail -5
cargo nextest run -p shinri-solver --lib -E 'test(/word_norm/)' 2>&1 | tail -5
```

Expected: `slice54_probes` 23 passed. All `word_norm` unit tests pass: the old ones plus the 6 new ones, so the count is non-zero and at least 6 higher than before.

If `string_path_bool_arg_is_not_sat` gives `unknown`, that is accepted (see the test's doc). Record it in the notes for the report.

- [ ] **Step 7: Fence audit (spec §3.5 risk 2)**

Read each predicate and confirm that a nullary Bool symbol and a Bool-operand `(= b t)` are treated as Boolean structure, not as a fence trigger:

```bash
grep -n "nullary\|Bool-operand\|Pure Boolean" crates/shinri-solver/src/bv_stage.rs crates/shinri-solver/src/abv_stage.rs
sed -n 204,260p crates/shinri-solver/src/string_stage.rs
```

- `bv_stage::has_non_bv_theory_atom`: exempts "a bare declared Bool constant (0-ary uninterpreted symbol)" and Bool-operand `Eq`/`Distinct`. ✔ when both are present.
- `abv_stage::fenced` / `walk_fence`: "Bool-operand (dis)equality is iff/xor — Boolean structure". ✔ when present.
- `string_stage::fenced`: fences an `Op::Uninterpreted` application only when its result or an argument is String-sorted; `bool!` is Bool-sorted. ✔.

Write one line per predicate into `slice54-notes.md`. If any predicate does treat these shapes as a trigger, stop: that is a `decided → unknown` risk, which needs a ruling (Global Constraints).

- [ ] **Step 8: Oracle after the fix**

```bash
cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle)' --no-capture 2>&1 \
  | tee target/slice54-oracle-after.log | grep -E "QF_|tests? run|FAIL|PASS"
```

Expected: 3 discovered, 3 passed. Every family shows `disagreements=0`, with `sat` and `unsat` both > 0. Copy the three lines into `slice54-notes.md`. If a disagreement remains, debug it before going on (superpowers:systematic-debugging), starting from the printed script.

- [ ] **Step 9: Commit**

```bash
cargo fmt --all
mise run lint
git add crates/shinri-solver/src/word_norm.rs crates/shinri-solver/tests/slice54_probes.rs
git commit -m "fix(solver): slice54 - purify compound Bool arguments into proxies (UF/DT wrong-sat)"
```

---

### Task 4: Gates, after-run, report

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice54-uf-bool-arg-report.md`
- Modify: `docs/superpowers/specs/2026-10-02-shinri-slice54-uf-bool-arg-purify-design.md` (§11)

**Interfaces:**
- Consumes: `bench/results/slice54-base` and `target/slice54-base/md5.txt` (Task 1); `slice54-notes.md` and the oracle/probe logs (Tasks 1–3).

- [ ] **Step 1: Gates** (before the after-run, so they don't share cores with it; the base run must be finished)

```bash
mise run lint
mise run test 2>&1 | tail -3
mise run deny && mise run secrets
cargo nextest run -p shinri-solver --features oracle 2>&1 | tee target/slice54-oracle.log | tail -5
```

Expected: all green. The oracle log shows a non-zero discovered count: slice 53's 720, plus 3 new. Every test passes or is skipped, and `differential_qf_uflia_compound_args` and the `qfdt_oracle_*` tests pass. Record the counts. The unfiltered oracle suite takes ~25–33 min because of `fp_oracle differential_qf_fp_rem` (pre-existing; see the slice-53 report).

- [ ] **Step 2: After-run**

```bash
cargo build --release -p shinri-cli -p shinri-bench
md5sum target/release/shinri
BENCH_LOGICS=QF_UF,QF_DT,QF_UFLIA,QF_UFLRA BENCH_RUN_ID=slice54 \
  taskset -c 12-23 mise run bench-run
BENCH_RUN_ID=slice54 mise run bench-report
```

- [ ] **Step 3: Transitions** (scratch script, not committed)

```python
# $SCRATCH/transitions.py
import json, collections
def load(p):
    rows = {}
    for l in open(p):
        r = json.loads(l)
        if "path" in r: rows[r["path"]] = r
    return rows
a = load("bench/results/slice54-base/results.jsonl")
b = load("bench/results/slice54/results.jsonl")
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

Expected: no `ESCALATE` line and `net correct` ≥ 0 for every logic. **Any `ESCALATE`, or a negative net in any logic: stop and ask for a ruling before writing the report as final** (spec §7 criteria 3–4). Triage every `LOSS` line: re-run the row 3× at 20 s with both binaries. Call it noise if both binaries fluctuate, and attributable if only the after binary loses. Check the attributable ones for whether the file mints a proxy at all (Step 4). A loss on a file with no Bool argument is noise by construction, because its encoding is byte-identical.

- [ ] **Step 4: Proxy-minting count (criterion 7)**

```bash
grep -rlE '\(declare-fun [^ ]+ \([^)]*Bool' bench/corpus/QF_UF | wc -l
grep -rlE '\(declare-datatypes' bench/corpus/QF_DT | xargs grep -lE '\([a-zA-Z_][^ ()]* Bool\)' | wc -l
```

These are upper bounds for the files that can mint a proxy. Report both counts, and cross-tabulate the changed rows from Step 3 against these file lists.

- [ ] **Step 5: Write the report**

Follow the structure of `docs/superpowers/research/2026-10-02-smtlib-2024-slice53-arith-eq-polarity-report.md`:

- title line with run-id and fixture sha;
- commands; run table (run, solver, md5, started, finished, wall-clock), using `target/slice54-base/md5.txt` for `slice54-base` and stating that the fixture sha records the checkout, not the binary;
- load disclosure;
- how the transitions were computed;
- Headline;
- Success criteria (spec §7 table, with results);
- per-logic matrix for both runs, copied from each `report.md`;
- transition matrices (changed cells only);
- every `wrong` row from Task 1 Step 6 with its after verdict and disposition;
- every `correct → unknown/timeout` row, triaged;
- timing: median/p90 per logic, base vs after; proxy-minting counts (Step 4);
- oracle and probe evidence: before (Task 2 Step 2, Task 3 Step 2) and after (Task 3 Steps 6 and 8, Task 4 Step 1) counts, discovered/passed/skipped;
- fence audit (Task 3 Step 7);
- the five lines skipped from the bench (QF_LIA, QF_LRA, QF_S, QF_SLIA, QF_BVFP) and why (spec §7), labelled as a reasoned omission;
- Gates;
- Queued for the next slice: spec §9, plus every item carried in the slice-53 report's queue, verbatim, minus the "theory atom used as an argument of an uninterpreted function" item (closed here; note that the shape was broader than described);
- References.

- [ ] **Step 6: Fill spec §11 Measured outcomes**

Replace the §11 placeholder sentence with the criteria table (result and evidence per row), the run ids and fixture, and these deviations:

- the oracle is three tests in `bool_arg_oracle.rs`, not one `differential_bool_arg`;
- any generator strengthening from Task 2 Step 2;
- whether `string_path_bool_arg_is_not_sat` came out `unsat` or `unknown`.

- [ ] **Step 7: Commit, push, PR**

```bash
git add docs/superpowers/research/*slice54* docs/superpowers/specs/2026-10-02-shinri-slice54-uf-bool-arg-purify-design.md
git commit -m "docs(bench+spec): slice54 - re-run report and measured outcomes"
git push -u origin slice54-uf-bool-arg-purify
gh pr create --base main --title "slice54: purify compound Bool arguments (UF/DT wrong-sat) + rust 1.99.0" \
  --body "Spec: docs/superpowers/specs/2026-10-02-shinri-slice54-uf-bool-arg-purify-design.md
Plan: docs/superpowers/plans/2026-10-02-shinri-slice54-uf-bool-arg-purify.md
Report: docs/superpowers/research/<file>. Criteria table: see spec §11.
Also bumps the toolchain to Rust 1.99.0 (fmt/clippy clean, no code changes needed)."
```

Then wait for CI to go green (including the `oracle` job), merge with a merge commit, and delete the branch on the remote and locally (AGENTS.md conventions).
