# Slice 57 — String model reconciliation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn `unknown fence=str-model-rejected` into a correct `sat` when the string model builder fails on a class holding several concats (or a cycle through an engine-minted concat) although a witness exists, without adding any wrong `sat`.

**Architecture:** `StrSolver::model_with` keeps today's default build, now computed as a value list (`model::string_values`) and self-checked against the input string equations. Only when that check fails does a new rebuild (`model_reconcile::reconciled_values`) run: input concats first, every candidate length-checked against arith, rejected candidates rolled back. An adopted rebuild sets a new `ModelBuilder` flag, and the solver's gate then demands that every assertion evaluates to `Some(true)` (strict mode).

**Tech Stack:** Rust workspace (toolchain pinned in `mise.toml`, Rust 1.99), cargo-nextest 0.9.140, z3 from mise for the oracle, `shinri-bench` for the SMT-LIB 2024 run.

**Spec:** `docs/superpowers/specs/2026-10-03-shinri-slice57-str-model-reconcile-design.md`

## Global Constraints

- Code changes only in: `crates/shinri-str/src/model.rs`, new `crates/shinri-str/src/model_reconcile.rs`, `crates/shinri-str/src/lib.rs` (`model_with`, `mod` line, tests), `crates/shinri-theory/src/model.rs` (`ModelBuilder` flag), `crates/shinri-solver/src/lib.rs` (gate). No parser, SAT, Combiner search, `wordeq.rs`, string `check` or `lower` change (spec §5).
- The default build is bit-identical to HEAD: a model whose default build satisfies every input string equation is assigned unchanged and the flag stays unset (spec §4.1).
- Without the flag the gate is 3-valued exactly as today; with it, `None` rejects (spec §4.3).
- The only verdict the slice may add is `sat` (spec §4.3). Any `* → wrong` row stops the slice for a ruling (spec §8, criterion 1).
- Bench: logics QF_S, QF_SLIA, QF_LIA; `--timeout 20 --mem-mb 3072 --jobs 6`; detached with `setsid` under `taskset -c 12-23`; base run `slice57-base` built from `46d5fd9` sources (spec §6, §8).
- Oracle tests only run with `--features oracle`; without it they silently run 0 tests. Always confirm a non-zero discovered count (AGENTS.md).
- nextest filters use the expression form `-E 'test(<name>)'` / `-E 'binary(<name>)'` (AGENTS.md).
- While the base bench run is live, run builds and tests on cores 0–11 (`taskset -c 0-11 …`) so they do not perturb the bench (slice-53 R9).
- `cargo fmt --all` before every commit; `mise run lint` (clippy `-D warnings`) must be clean.
- Branch `slice57-str-model-reconcile` off `main`; PR to `main`, merge commit when CI is green, then delete the branch (AGENTS.md).

## Review Focus

1. **Default model violates an input equation the gate never sees, while the 3-valued gate would pass** (e.g. a decided input disjunct). The rebuild is then adopted and the strict gate may turn a `sat` that is correct today into `unknown`. Expected: rows that are `sat` today stay `sat`. Pinned in Task 1 (`rf1_input_disjunction_stays_sat`); bench criterion 4 triages any real occurrence.
2. **The strict flag leaking across `check-sat` calls** in one script (push/pop). Expected: a later default-path query whose assertion the gate cannot evaluate (`str.<`) stays `sat`. Pinned in Task 1 (`rf2_strict_flag_does_not_leak_across_checks`).
3. **Constants needing escapes in a rebuilt value** (`"\\"`, two backslashes in SMT-LIB 2.6). Expected: the value prints with `\u{5c}` and keeps the prefix. Pinned in Task 1 (`p2_len_eq_prefix_backslashes`).
4. **Zero-length classes** (`x = y ++ ""`, `len x = 0`). Expected: `sat` with `x = y = ""`, unchanged. Pinned in Task 1 (`rf4_zero_length_class_stays_sat`).
5. **A rebuilt model next to an assertion the gate cannot evaluate** (`str.<`). Expected: `unknown`, never an unconfirmed `sat`. Pinned in Task 1 (`strict_gate_keeps_unevaluable_unknown`) and Task 2's unit tests.

---

## File Structure

| File | Change | Responsibility |
| --- | --- | --- |
| `crates/shinri-theory/src/model.rs` | Modify | `ModelBuilder` gains `strict_check` with `require_strict_check` / `strict_check_required`; `absorb` ORs it |
| `crates/shinri-solver/src/lib.rs` | Modify | Read the flag after `build_model`; `string_model_satisfies(.., strict)`; unit tests |
| `crates/shinri-str/src/model.rs` | Modify | `assign` becomes `string_values` (returns values, no write); helpers made `pub(crate)` |
| `crates/shinri-str/src/model_reconcile.rs` | Create | `reconciled_values`, `input_eqs_hold`, `ReconcileInput`; unit tests |
| `crates/shinri-str/src/lib.rs` | Modify | `mod model_reconcile;`; `model_with` runs default → self-check → rebuild → flag; unit tests |
| `crates/shinri-solver/tests/slice57_probes.rs` | Create | End-to-end probes (spec §7.3) and Review Focus 1–5 |
| `crates/shinri-solver/tests/qfs_differential.rs` | Modify | `differential_qfs_model_reconcile` family (spec §7.4) |
| `docs/superpowers/research/<date>-smtlib-2024-slice57-str-model-reconcile-report.md` | Create | Bench report and carried queue |
| `docs/superpowers/specs/2026-10-03-shinri-slice57-str-model-reconcile-design.md` | Modify | Append *Measured outcomes* |

---

### Task 0: Branch, base binary, base run

**Files:** none in the repo (artifacts under `target/slice57-base/`, `bench/results/slice57-base/`).

- [ ] **Step 1: Create the slice branch**

```bash
cd /workspace && git checkout main && git pull --ff-only && git checkout -b slice57-str-model-reconcile
```

- [ ] **Step 2: Confirm the crates are unchanged from `46d5fd9`**

Run: `git diff --stat 46d5fd9 HEAD -- crates`
Expected: empty (only the spec and plan commits sit on top of `46d5fd9`).

- [ ] **Step 3: Build and freeze the base binary**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice57-base && cp target/release/shinri target/slice57-base/shinri
cp target/release/shinri-bench target/slice57-base/shinri-bench
md5sum target/slice57-base/shinri | tee target/slice57-base/md5.txt
echo 46d5fd9 > target/slice57-base/commit.txt
```

- [ ] **Step 4: Confirm the corpus is present**

Run: `ls bench/corpus/QF_S bench/corpus/QF_SLIA bench/corpus/QF_LIA | head -3`
Expected: family directories listed. If a logic is missing, run `BENCH_LOGICS=QF_S,QF_SLIA,QF_LIA mise run bench-fetch` first.

- [ ] **Step 5: Launch the base run detached**

```bash
date -u +%FT%TZ > target/slice57-base/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/slice57-base/shinri-bench run \
  --logics QF_S,QF_SLIA,QF_LIA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice57-base/shinri --run-id slice57-base \
  > target/slice57-base/run.log 2>&1; date -u +%FT%TZ > target/slice57-base/finished.txt' \
  > /dev/null 2>&1 &
```

About 116,600 rows (QF_SLIA 84,395, QF_S 18,940, QF_LIA 13,306), so expect several hours. Do not wait: Tasks 1–4 proceed meanwhile on cores 0–11. Task 5 waits for `target/slice57-base/finished.txt`.

---

### Task 1: Failing probes and the oracle family (before evidence)

**Files:**
- Create: `crates/shinri-solver/tests/slice57_probes.rs`
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (new family, appended after `qfs_str_order_const_word_matches_z3`, before the targeted cases)

**Interfaces:**
- Consumes: nothing new.
- Produces: the probe file that Task 3 turns green, and `MR_BEFORE_UNKNOWN_Z3_SAT`, which Task 3 sets from this task's measurement (recorded in `target/slice57-before.txt`).

- [ ] **Step 1: Write the probe file**

Create `crates/shinri-solver/tests/slice57_probes.rs`:

```rust
//! Slice 57 probes (spec §7.3). When the word-equation search leaves a
//! string class holding several concats (an input equation's side and a
//! minted char-peel/F-split side) or a cycle through a minted concat, the
//! default model builder picked the wrong concat and the gate rejected the
//! model (`unknown fence=str-model-rejected`). At `46d5fd9` every `sat` case
//! below answered `unknown`; the slice-53 base binary answered the `len`
//! cases `sat`. A model produced by the reconciliation rebuild must pass the
//! strict gate, so `strict_gate_keeps_unevaluable_unknown` stays `unknown`.
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

const H: &str = "(set-logic QF_SLIA)(declare-fun x () String)(declare-fun y () String)";

fn verdict(body: &str) -> String {
    run_script(&format!("{H}{body}(check-sat)"))
        .first()
        .cloned()
        .unwrap_or_default()
}

/// Decode the first SMT-LIB 2.6 string literal in `resp` (`""` and `\u{..}`).
fn decode(resp: &str) -> String {
    let start = resp.find('"').expect("a string literal");
    let cs: Vec<char> = resp[start + 1..].chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < cs.len() {
        match cs[i] {
            '"' if cs.get(i + 1) == Some(&'"') => {
                out.push('"');
                i += 2;
            }
            '"' => break,
            '\\' if cs.get(i + 1) == Some(&'u') && cs.get(i + 2) == Some(&'{') => {
                let close = i + cs[i..].iter().position(|&c| c == '}').expect("closing brace");
                let hex: String = cs[i + 3..close].iter().collect();
                let code = u32::from_str_radix(&hex, 16).expect("hex escape");
                out.push(char::from_u32(code).expect("valid code point"));
                i = close + 1;
            }
            c => {
                out.push(c);
                i += 1;
            }
        }
    }
    out
}

/// `body` must be `sat`; returns the model value of `x`.
fn sat_x(body: &str) -> String {
    let out = run_script(&format!("{H}{body}(check-sat)(get-value (x))"));
    assert_eq!(out.first().map(String::as_str), Some("sat"), "{H}{body}");
    decode(&out[1])
}

// ── spec §1.1: the slice-53 regressions ─────────────────────────────────────

#[test]
fn p1_len_eq_prefix_cd() {
    let x = sat_x("(assert (= (str.len x) 3))(assert (str.prefixof \"cd\" x))");
    assert!(x.starts_with("cd") && x.chars().count() == 3, "x = {x:?}");
}

#[test]
fn p1_len_bounds_prefix_cd() {
    let x = sat_x(
        "(assert (>= (str.len x) 3))(assert (<= (str.len x) 3))(assert (str.prefixof \"cd\" x))",
    );
    assert!(x.starts_with("cd") && x.chars().count() == 3, "x = {x:?}");
}

/// `"\\"` is two backslashes in SMT-LIB 2.6 (Review Focus 3).
#[test]
fn p2_len_eq_prefix_backslashes() {
    let x = sat_x("(assert (= (str.len x) 3))(assert (str.prefixof \"\\\\\" x))");
    assert!(x.starts_with("\\\\") && x.chars().count() == 3, "x = {x:?}");
}

#[test]
fn p2_len_bounds_prefix_backslashes() {
    let x = sat_x(
        "(assert (>= (str.len x) 3))(assert (<= (str.len x) 3))(assert (str.prefixof \"\\\\\" x))",
    );
    assert!(x.starts_with("\\\\") && x.chars().count() == 3, "x = {x:?}");
}

#[test]
fn p3_len_eq_suffix_c() {
    let x = sat_x("(assert (= (str.len x) 3))(assert (str.suffixof \"c\" x))");
    assert!(x.ends_with('c') && x.chars().count() == 3, "x = {x:?}");
}

#[test]
fn p3_len_bounds_suffix_c() {
    let x = sat_x(
        "(assert (>= (str.len x) 3))(assert (<= (str.len x) 3))(assert (str.suffixof \"c\" x))",
    );
    assert!(x.ends_with('c') && x.chars().count() == 3, "x = {x:?}");
}

/// `QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-multiply-reverse-fuzz.smt2`,
/// assertions inlined. z3: sat.
#[test]
fn p4_stringfuzz_multiply_reverse() {
    let x = sat_x(
        "(assert (= (str.len x) 5))(assert (= x y))\
         (assert (str.in_re y (re.* (re.range \"!\" \"`\"))))(assert (str.prefixof \"1\" x))",
    );
    assert!(x.starts_with('1') && x.chars().count() == 5, "x = {x:?}");
    assert!(x.chars().all(|c| ('!'..='`').contains(&c)), "x = {x:?}");
}

// ── unsat siblings: the rebuild must not over-accept ────────────────────────

#[test]
fn u1_prefix_longer_than_len_unsat() {
    assert_eq!(
        verdict("(assert (= (str.len x) 1))(assert (str.prefixof \"cd\" x))"),
        "unsat"
    );
}

#[test]
fn u2_suffix_with_zero_len_unsat() {
    assert_eq!(
        verdict("(assert (= (str.len x) 0))(assert (str.suffixof \"c\" x))"),
        "unsat"
    );
}

// ── known-unknown pins (queued engine-side reconciliation, spec §9 item 1) ──

/// `regex-050-translate-rotate-fuzz.smt2`; z3: unsat. Needs the engine to
/// derive the conflict between `x`'s constant prefix and the membership
/// (spec §9 item 1); the model-side rebuild cannot produce `unsat`.
#[test]
fn k1_stringfuzz_translate_rotate_stays_unknown() {
    assert_eq!(
        verdict(
            "(assert (= (str.len x) 3))(assert (= x y))\
             (assert (str.in_re y (re.+ (re.range \"a\" \"b\"))))(assert (str.prefixof \"\\\\\" x))"
        ),
        "unknown",
        "queued: engine-side reconciliation (slice-57 spec §9 item 1)"
    );
}

/// `regex-050-translate-graft-translate.smt2`; z3: unsat. Same queue item.
#[test]
fn k2_stringfuzz_translate_graft_stays_unknown() {
    assert_eq!(
        verdict(
            "(assert (= 2 (str.len x)))(assert (= x y))\
             (assert (str.in_re y (re.* (re.range \"a\" \"b\"))))(assert (str.prefixof \"1\" x))"
        ),
        "unknown",
        "queued: engine-side reconciliation (slice-57 spec §9 item 1)"
    );
}

// ── strict gate (spec §4.3, Review Focus 5) ─────────────────────────────────

/// At `46d5fd9` this answers `unknown fence=str-model-rejected` (default
/// build rejected), so the rebuild runs. The gate cannot evaluate `str.<`,
/// so the strict gate must keep it `unknown` (z3: sat).
#[test]
fn strict_gate_keeps_unevaluable_unknown() {
    assert_eq!(
        verdict(
            "(assert (= (str.len x) 3))(assert (str.prefixof \"cd\" x))(assert (str.< x \"zzz\"))"
        ),
        "unknown"
    );
}

// ── Review Focus ────────────────────────────────────────────────────────────

/// Review Focus 1: a decided input disjunct; `sat` today, must stay `sat`.
#[test]
fn rf1_input_disjunction_stays_sat() {
    let x = sat_x(
        "(assert (or (= x \"ab\") (= x \"cd\")))(assert (= (str.len x) 2))\
         (assert (str.prefixof \"c\" x))",
    );
    assert_eq!(x, "cd");
}

/// Review Focus 2: the strict flag belongs to one model build only.
#[test]
fn rf2_strict_flag_does_not_leak_across_checks() {
    let out = run_script(&format!(
        "{H}(push 1)(assert (= (str.len x) 3))(assert (str.prefixof \"cd\" x))(check-sat)(pop 1)\
         (push 1)(assert (= (str.len x) 1))(assert (str.< x \"b\"))(check-sat)(pop 1)"
    ));
    assert_eq!(out, vec!["sat".to_string(), "sat".to_string()]);
}

/// Review Focus 4: zero-length class; `sat` today, must stay `sat`.
#[test]
fn rf4_zero_length_class_stays_sat() {
    let x = sat_x("(assert (= x (str.++ y \"\")))(assert (= (str.len x) 0))");
    assert_eq!(x, "");
}
```

- [ ] **Step 2: Run the probes and record which fail at the branch base**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice57_probes)' 2>&1 | tee target/slice57-probes-before.log | tail -25`
Expected: 15 tests discovered. FAIL: `p1_len_eq_prefix_cd`, `p2_len_eq_prefix_backslashes`, `p3_len_eq_suffix_c`, `p4_stringfuzz_multiply_reverse`, `rf2_strict_flag_does_not_leak_across_checks` (its first check is `unknown` today). PASS: the rest (the `len`-bounds variants, the unsat siblings, k1/k2, the strict pin, rf1, rf4). If the outcome differs, record the difference in `target/slice57-before.txt` and report it; do not edit expectations.

- [ ] **Step 3: Add the oracle generator and family**

In `crates/shinri-solver/tests/qfs_differential.rs`, append this section after the `qfs_str_order_const_word_matches_z3` test (before the targeted cases):

```rust
// ─────────────────────────────────────────────────────────────────────────────
// Model-reconciliation differential oracle (slice 57): prefixof / suffixof /
// concat equations with constants, a length pin written as `=`, as `<=`+`>=`,
// or absent, and an optional membership. These reach string classes holding
// several concats, where the default model builder failed
// (`str-model-rejected`). Verdicts must agree with z3; Sat models are
// z3-verified. Fresh seed — never perturb existing families' seeds.
// ─────────────────────────────────────────────────────────────────────────────

const MR_N_ITERS: usize = 300;

fn gen_model_reconcile_body(seed: u64) -> (String, usize) {
    let mut rng = Lcg(seed);
    let nv = 1 + rng.below(2) as usize;
    let mut b = String::from("(set-logic QF_SLIA)\n");
    for k in 0..nv {
        b.push_str(&format!("(declare-fun s{k} () String)\n"));
    }
    let var = |rng: &mut Lcg| format!("s{}", rng.below(nv as u64));
    const LITS: [&str; 6] = ["a", "b", "ab", "ba", "cd", "c"];
    let lit = |rng: &mut Lcg| format!("\"{}\"", LITS[rng.below(LITS.len() as u64) as usize]);
    for _ in 0..1 + rng.below(3) {
        let x = var(&mut rng);
        let l = lit(&mut rng);
        let a = match rng.below(4) {
            0 => format!("(str.prefixof {l} {x})"),
            1 => format!("(str.suffixof {l} {x})"),
            2 => {
                let y = var(&mut rng);
                format!("(= {x} (str.++ {l} {y}))")
            }
            _ => {
                let y = var(&mut rng);
                format!("(= {x} (str.++ {y} {l}))")
            }
        };
        b.push_str(&format!("(assert {a})\n"));
    }
    let x = var(&mut rng);
    let n = rng.below(5);
    match rng.below(3) {
        0 => b.push_str(&format!("(assert (= (str.len {x}) {n}))\n")),
        1 => b.push_str(&format!(
            "(assert (>= (str.len {x}) {n}))\n(assert (<= (str.len {x}) {n}))\n"
        )),
        _ => {}
    }
    if rng.below(3) == 0 {
        let x = var(&mut rng);
        b.push_str(&format!(
            "(assert (str.in_re {x} (re.+ (re.range \"a\" \"d\"))))\n"
        ));
    }
    (b, nv)
}

#[test]
fn differential_qfs_model_reconcile() {
    let mut rng = Lcg(0x57_0000_0001u64);
    let (mut n_sat, mut n_unsat, mut n_unknown, mut n_unknown_z3_sat, mut n_z3skip, mut n_witness) =
        (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);

    for it in 0..MR_N_ITERS {
        let seed = rng.next();
        let (body, nv) = gen_model_reconcile_body(seed);
        let script = format!("{body}(check-sat)\n");
        let ours = shinri_verdict(&script);
        let theirs = z3_verdict(&script);
        if ours == Verdict::Unknown {
            n_unknown += 1;
            if theirs == Verdict::Sat {
                n_unknown_z3_sat += 1;
            }
            continue;
        }
        if theirs == Verdict::Unknown {
            n_z3skip += 1;
            continue;
        }
        assert_eq!(
            ours, theirs,
            "MODEL-RECONCILE SOUNDNESS DISAGREEMENT (iter {it}, seed {seed}): \
             shinri={ours:?} z3={theirs:?}\nReproduce:\n{script}"
        );
        match ours {
            Verdict::Sat => {
                n_sat += 1;
                let names: Vec<String> = (0..nv).map(|k| format!("s{k}")).collect();
                let get = format!("{script}(get-value ({}))\n", names.join(" "));
                let lines = shinri_lines(&get);
                if let Some(resp) = lines.get(1) {
                    let model = parse_string_values(resp);
                    if !model.is_empty() {
                        let w = z3_with_model(&body, &model);
                        assert_eq!(
                            w,
                            Verdict::Sat,
                            "WITNESS FAILURE (iter {it}, seed {seed}): model {model:?}\n{body}"
                        );
                        n_witness += 1;
                    }
                }
            }
            Verdict::Unsat => n_unsat += 1,
            Verdict::Unknown => unreachable!(),
        }
    }

    println!(
        "differential_qfs_model_reconcile: {MR_N_ITERS} iters — {n_sat} sat / {n_unsat} unsat / \
         {n_unknown} shinri-unknown ({n_unknown_z3_sat} with z3 sat) / {n_z3skip} z3-unknown; \
         {n_witness} witnesses; 0 disagreements"
    );
    assert!(n_sat > 0, "model-reconcile family produced zero SAT instances");
    assert!(n_unsat > 0, "model-reconcile family produced zero UNSAT instances");
    assert!(n_witness > 0, "no witnesses checked — model path not exercised");
}
```

- [ ] **Step 4: Run the family and record the before count**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle --no-capture -E 'test(differential_qfs_model_reconcile)' 2>&1 | tee target/slice57-oracle-before.log | grep -E 'differential_qfs_model_reconcile:|tests run|PASS|FAIL'`
Expected: 1 test discovered and passing, plus the summary line. Write the summary line to `target/slice57-before.txt`. The `with z3 sat` count must be non-zero (spec §7.4). If it is zero, strengthen the generator (for example add `"cd"` prefixes with a length pin of 3 more often, or more `=`-written length pins) and re-run until it is non-zero. Record every generator change for the report.

- [ ] **Step 5: Format, lint, commit**

```bash
cargo fmt --all
taskset -c 0-11 cargo clippy -p shinri-solver --all-targets -- -D warnings
taskset -c 0-11 cargo clippy -p shinri-solver --all-targets --features oracle 2>&1 | grep -B2 -A8 'differential_qfs_model_reconcile\|gen_model_reconcile_body\|MR_N_ITERS' || true
git add crates/shinri-solver/tests/slice57_probes.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(slice57): model-reconciliation probes and oracle family (5 probes fail at HEAD)"
```

The first clippy run covers the probes and must be clean. `qfs_differential.rs` only compiles with `--features oracle` and already has pre-existing clippy errors there (queued since slice 54). The second command shows only diagnostics that point into the new code, and it must print nothing.

---

### Task 2: `ModelBuilder` strict flag and the strict gate

**Files:**
- Modify: `crates/shinri-theory/src/model.rs:9-50` (struct, methods, `absorb`, new test module)
- Modify: `crates/shinri-solver/src/lib.rs` (`build_model` call site ~1356, gate ~1490, `string_model_satisfies` ~1520, test module `slice52_gate_tests` ~3686)

**Interfaces:**
- Consumes: nothing new.
- Produces: `ModelBuilder::require_strict_check(&mut self)`, `ModelBuilder::strict_check_required(&self) -> bool`; `Solver::string_model_satisfies(&self, assertions: &[TermId], model: &Model, strict: bool) -> bool`.

- [ ] **Step 1: Write the failing `ModelBuilder` test**

Append to `crates/shinri-theory/src/model.rs`:

```rust
#[cfg(test)]
mod strict_check_tests {
    use super::*;

    #[test]
    fn strict_check_defaults_off_and_survives_absorb() {
        let mut a = ModelBuilder::default();
        assert!(!a.strict_check_required());
        let mut b = ModelBuilder::default();
        b.require_strict_check();
        assert!(b.strict_check_required());
        a.absorb(b);
        assert!(a.strict_check_required(), "absorb must keep the flag");
    }
}
```

- [ ] **Step 2: Run it to verify it fails**

Run: `taskset -c 0-11 cargo nextest run -p shinri-theory -E 'test(strict_check_defaults_off_and_survives_absorb)'`
Expected: compile error, `no method named strict_check_required`.

- [ ] **Step 3: Add the flag**

In `crates/shinri-theory/src/model.rs`, replace the struct and `absorb`, and add the two methods:

```rust
/// Each theory writes its term values here; the Combiner reconciles them.
#[derive(Default)]
pub struct ModelBuilder {
    values: FxHashMap<TermId, ModelVal>,
    /// Slice 57: set by a theory whose values the solver must confirm with
    /// the strict model gate (every assertion definitely true).
    strict_check: bool,
}
```

```rust
    /// Slice 57: ask the solver to confirm this model with the strict gate.
    #[inline]
    pub fn require_strict_check(&mut self) {
        self.strict_check = true;
    }
    /// Slice 57: whether some theory asked for the strict gate.
    #[inline]
    pub fn strict_check_required(&self) -> bool {
        self.strict_check
    }
```

```rust
    /// Fold another builder's assignments into this one (other wins ties; the
    /// caller has already verified agreement via `merge_check`). The strict
    /// flag is kept if either builder set it.
    pub fn absorb(&mut self, other: ModelBuilder) {
        let ModelBuilder {
            values,
            strict_check,
        } = other;
        for (t, v) in values {
            self.values.insert(t, v);
        }
        self.strict_check |= strict_check;
    }
```

- [ ] **Step 4: Run it to verify it passes**

Run: `taskset -c 0-11 cargo nextest run -p shinri-theory -E 'test(strict_check_defaults_off_and_survives_absorb)'`
Expected: 1 passed.

- [ ] **Step 5: Write the failing gate tests**

Append inside `mod slice52_gate_tests` in `crates/shinri-solver/src/lib.rs` (it already has `noetzli_atoms` and `model`):

```rust
    /// Slice 57: an assertion the gate cannot evaluate (`str.<`) passes the
    /// 3-valued gate but fails the strict one.
    #[test]
    fn strict_gate_rejects_unevaluable_assertion() {
        let mut s = Solver::new();
        let (x, y, _e1, _e2) = noetzli_atoms(&mut s);
        let lt = s.app(Op::Builtin(BuiltinOp::StrLt), &[x, y]);
        let m = model(&[(x, "a"), (y, "b")]);
        assert_eq!(s.eval_bool(lt, &m), None);
        assert!(s.string_model_satisfies(&[lt], &m, false));
        assert!(!s.string_model_satisfies(&[lt], &m, true));
    }

    /// Slice 57: the strict gate accepts a set that evaluates to all-true.
    #[test]
    fn strict_gate_accepts_all_true() {
        let mut s = Solver::new();
        let (x, y, e1, e2) = noetzli_atoms(&mut s);
        // e1 = ("A" = y ++ x), e2 = ("A" = x ++ y): both true for x="", y="A".
        let m = model(&[(x, ""), (y, "A")]);
        assert!(s.string_model_satisfies(&[e1, e2], &m, true));
        let not_e1 = s.app(Op::Builtin(BuiltinOp::Not), &[e1]);
        assert!(!s.string_model_satisfies(&[not_e1], &m, true));
    }
```

Change the existing call in `gate_rejects_noetzli_bogus_model` to pass `false`:

```rust
        assert!(!s.string_model_satisfies(&[assertion], &m, false));
```

- [ ] **Step 6: Run them to verify they fail**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --lib -E 'test(strict_gate_)'`
Expected: compile error, `string_model_satisfies` takes 2 arguments but 3 were supplied.

- [ ] **Step 7: Implement the strict gate**

In `crates/shinri-solver/src/lib.rs`, right after `let mb = sat.theory_mut().build_model();` (~line 1356) add:

```rust
                // Slice 57: a string model from the reconciliation rebuild must
                // pass the strict gate (every assertion definitely true).
                let strict_gate = mb.strict_check_required();
```

Change the gate call (~line 1490):

```rust
                if on_string_path && !self.string_model_satisfies(&lowered, &model, strict_gate) {
```

Replace `string_model_satisfies` (~line 1520) and append to its doc comment:

```rust
    ///
    /// Slice 57: with `strict` set (the string theory adopted its
    /// reconciliation rebuild, `ModelBuilder::strict_check_required`), `None`
    /// also rejects. The rebuild changes string contents the engine did not
    /// derive, so an assertion the gate cannot evaluate (`str.<`, compound
    /// arithmetic, a UF application) could be violated unseen; a rebuilt model
    /// yields `sat` only when every assertion is positively confirmed.
    fn string_model_satisfies(&self, assertions: &[TermId], model: &Model, strict: bool) -> bool {
        for &a in assertions {
            match self.eval_bool(a, model) {
                Some(true) => {}
                Some(false) => return false,
                None if strict => return false,
                None => {}
            }
        }
        true
    }
```

Run `grep -n "string_model_satisfies(" crates/shinri-solver/src/lib.rs` and confirm every call passes three arguments.

- [ ] **Step 8: Run the tests to verify they pass**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --lib -E 'test(strict_gate_) | test(gate_rejects_noetzli_bogus_model)'`
Expected: 3 passed.

- [ ] **Step 9: Format, lint, commit**

```bash
cargo fmt --all
taskset -c 0-11 cargo clippy -p shinri-theory -p shinri-solver --all-targets -- -D warnings
git add crates/shinri-theory/src/model.rs crates/shinri-solver/src/lib.rs
git commit -m "feat(gate): slice57 - ModelBuilder strict flag and strict string model gate"
```

---

### Task 3: Self-check and reconciliation rebuild

**Files:**
- Modify: `crates/shinri-str/src/model.rs` (`assign` → `string_values` at lines 80–122; `pub(crate)` on `free_fill` :228, `class_member` :358, `const_word_of` :383, `is_concat` :405, `concat_arity` :416)
- Create: `crates/shinri-str/src/model_reconcile.rs`
- Modify: `crates/shinri-str/src/lib.rs` (`mod model_reconcile;` after `pub mod model;` at line 8; `model_with` at 1562–1579; a new test in `mod tests`)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (before-count constant and assertion)

**Interfaces:**
- Consumes: `ModelBuilder::require_strict_check` (Task 2).
- Produces: `pub fn model::string_values(terms: &mut Context, eq: &mut EqualityEngine, known: &[TermId], str_terms: &[TermId], m: &ModelBuilder, seed: &FxHashMap<TermId, String>) -> Vec<(TermId, String)>`; `pub(crate) fn model_reconcile::reconciled_values(terms: &mut Context, eq: &mut EqualityEngine, m: &ModelBuilder, inp: &ReconcileInput<'_>) -> Vec<(TermId, String)>`; `pub(crate) fn model_reconcile::input_eqs_hold(terms: &Context, input_eqs: &[TermId], vals: &[(TermId, String)], m: &ModelBuilder) -> bool`; `pub(crate) struct ReconcileInput<'a> { known, str_terms, seeds, input_sides, minted_sides }`.

- [ ] **Step 1: Refactor `assign` into `string_values` (no behaviour change)**

In `crates/shinri-str/src/model.rs`, replace `pub fn assign(...)` (its doc comment stays, reworded as below) with:

```rust
/// The default string valuation, without writing it: `(term, value)` for every
/// term of `str_terms` that `m` does not already hold a string for, in
/// `str_terms` order. Compound (concat) terms are assembled from their
/// operands, and constant characters pinned by the equality-engine normal
/// forms are overlaid.
///
/// `known` must contain every string-sorted term visible to the solver (so that
/// `deep_normal_form` can reflect merges with terms not syntactically inside
/// `t`, e.g. `x = "ab"` pins `x`'s value to "ab").
pub fn string_values(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    str_terms: &[TermId],
    m: &ModelBuilder,
    seed: &FxHashMap<TermId, String>,
) -> Vec<(TermId, String)> {
    let mut memo: FxHashMap<TermId, String> = seed.clone();
    let mut in_progress: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();

    // (keep the existing "Value concat terms FIRST" comment and loop verbatim)
    let mut concats: Vec<TermId> = known
        .iter()
        .copied()
        .filter(|&t| is_concat(terms, t))
        .collect();
    concats.sort_by_key(|&t| std::cmp::Reverse(concat_arity(terms, t)));
    for t in concats {
        let _ = value_of(terms, eq, known, t, m, &mut memo, &mut in_progress);
    }

    let mut out = Vec::new();
    for &t in str_terms {
        // (keep the existing "Respect an existing *string* assignment" comment)
        if matches!(m.get(t), Some(ModelVal::String(_))) {
            continue;
        }
        let v = value_of(terms, eq, known, t, m, &mut memo, &mut in_progress);
        out.push((t, v));
    }
    out
}
```

Change the module doc line 1 from `//! Model construction for the string theory (Task 17 + Task 19 overlay).` to `//! Default model construction for the string theory (Task 17 + Task 19 overlay; the slice-57 rebuild is in `model_reconcile`).`

Mark `free_fill`, `class_member`, `const_word_of`, `is_concat`, `concat_arity` as `pub(crate) fn`.

In `crates/shinri-str/src/lib.rs` `model_with`, replace the last line `model::assign(cx.terms, cx.eq, &known, &str_terms, m, &seeds);` with:

```rust
        for (t, v) in model::string_values(cx.terms, cx.eq, &known, &str_terms, m, &seeds) {
            m.assign(t, ModelVal::String(v));
        }
```

(`ModelVal` is `shinri_theory::types::ModelVal`; add it to the `use` lines at the top of `lib.rs` if it is not already imported.)

Run: `taskset -c 0-11 cargo nextest run -p shinri-str`
Expected: all pass (same count as before the refactor; record it).

- [ ] **Step 2: Write the `model_reconcile` file with failing tests**

Create `crates/shinri-str/src/model_reconcile.rs` with only the test module and stub signatures, so the tests compile and fail:

```rust
//! Slice 57: reconciliation rebuild of the string model.
//!
//! The default builder (`model::string_values`) values a variable from the
//! FIRST concat in its class. When the word-equation search leaves a class
//! holding several concats (an input equation's side next to a minted
//! char-peel/F-split side), or a cycle through a minted concat, that choice can
//! violate an input equation, and the solver's model gate rejects the model
//! (`str-model-rejected`). This rebuild prefers input concats, length-checks
//! every candidate against the arith model, and rolls back a rejected
//! candidate's values. `StrSolver::model_with` adopts its result only if every
//! input equation holds, and then sets `ModelBuilder::require_strict_check`.

use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::types::ModelVal;
use shinri_theory::{EqualityEngine, ModelBuilder};

use crate::model::{class_member, concat_arity, const_word_of, free_fill, is_concat};

/// What the rebuild reads besides the term context, EUF and the arith model.
pub(crate) struct ReconcileInput<'a> {
    /// Every string term visible to the solver (as for `model::string_values`).
    pub known: &'a [TermId],
    /// The terms to value, in output order.
    pub str_terms: &'a [TermId],
    /// Membership seeds for free leaves (`model::memb_seeds`).
    pub seeds: &'a FxHashMap<TermId, String>,
    /// Both sides of every asserted input (non-minted) string equality.
    pub input_sides: &'a FxHashSet<TermId>,
    /// Both sides of every asserted minted string equality.
    pub minted_sides: &'a FxHashSet<TermId>,
}

pub(crate) fn reconciled_values(
    _terms: &mut Context,
    _eq: &mut EqualityEngine,
    _m: &ModelBuilder,
    _inp: &ReconcileInput<'_>,
) -> Vec<(TermId, String)> {
    Vec::new()
}

pub(crate) fn input_eqs_hold(
    _terms: &Context,
    _input_eqs: &[TermId],
    _vals: &[(TermId, String)],
    _m: &ModelBuilder,
) -> bool {
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_theory::types::EqJust;

    fn var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn cat(ctx: &mut Context, a: TermId, b: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[a, b]).unwrap()
    }

    fn set_len(ctx: &mut Context, m: &mut ModelBuilder, t: TermId, n: i128) {
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[t]).unwrap();
        m.assign(l, ModelVal::Num(shinri_core::Rational::from_int(n.into())));
    }

    fn merge(eq: &mut EqualityEngine, a: TermId, b: TermId) {
        let an = eq.intern(a);
        let bn = eq.intern(b);
        let _ = eq.merge(an, bn, EqJust::Definitional);
    }

    fn value_in(vals: &[(TermId, String)], t: TermId) -> String {
        vals.iter()
            .find(|(k, _)| *k == t)
            .map(|(_, v)| v.clone())
            .expect("term valued")
    }

    fn sides(ts: &[TermId]) -> FxHashSet<TermId> {
        ts.iter().copied().collect()
    }

    /// `x ≈ "cd" ++ p` (input) and `x ≈ "c" ++ k` (minted, listed first, as the
    /// search produces it), `len x = 3`, `len p = 1`. The default build takes
    /// the minted concat and free-fills `x`; the rebuild gives `"cd?"`.
    #[test]
    fn char_peel_class_prefers_input_concat() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let mut m = ModelBuilder::default();
        let (x, p, k) = (var(&mut ctx, "x"), var(&mut ctx, "p"), var(&mut ctx, "k"));
        let cd = ctx.mk_string_const("cd");
        let c = ctx.mk_string_const("c");
        let input = cat(&mut ctx, cd, p);
        let minted = cat(&mut ctx, c, k);
        merge(&mut eq, x, input);
        merge(&mut eq, x, minted);
        set_len(&mut ctx, &mut m, x, 3);
        set_len(&mut ctx, &mut m, p, 1);
        let known = vec![minted, x, cd, input, k, p, c];
        let input_eq = ctx.mk_eq(x, input).unwrap();
        let seeds = FxHashMap::default();

        let default =
            crate::model::string_values(&mut ctx, &mut eq, &known, &known, &m, &seeds);
        assert!(!value_in(&default, x).starts_with("cd"), "documents the defect");
        assert!(!input_eqs_hold(&ctx, &[input_eq], &default, &m));

        let inp = ReconcileInput {
            known: &known,
            str_terms: &known,
            seeds: &seeds,
            input_sides: &sides(&[x, input]),
            minted_sides: &sides(&[x, minted]),
        };
        let rebuilt = reconciled_values(&mut ctx, &mut eq, &m, &inp);
        let xv = value_in(&rebuilt, x);
        assert!(xv.starts_with("cd") && xv.chars().count() == 3, "x = {xv:?}");
        assert!(input_eqs_hold(&ctx, &[input_eq], &rebuilt, &m));
    }

    /// `x ≈ s ++ "c"` (input) and `s ≈ x ++ k` (minted, an infeasible cycle),
    /// `len x = 3`, `len s = 2`. The cycle must fall back to a free fill of
    /// `s`, and the rejected candidate must not poison `x`.
    #[test]
    fn minted_cycle_fills_freely_without_poisoning() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let mut m = ModelBuilder::default();
        let (x, s, k) = (var(&mut ctx, "x"), var(&mut ctx, "s"), var(&mut ctx, "k"));
        let c = ctx.mk_string_const("c");
        let input = cat(&mut ctx, s, c);
        let minted = cat(&mut ctx, x, k);
        merge(&mut eq, x, input);
        merge(&mut eq, s, minted);
        set_len(&mut ctx, &mut m, x, 3);
        set_len(&mut ctx, &mut m, s, 2);
        let known = vec![minted, x, input, s, k, c];
        let input_eq = ctx.mk_eq(x, input).unwrap();
        let seeds = FxHashMap::default();
        let inp = ReconcileInput {
            known: &known,
            str_terms: &known,
            seeds: &seeds,
            input_sides: &sides(&[x, input]),
            minted_sides: &sides(&[s, minted]),
        };
        let rebuilt = reconciled_values(&mut ctx, &mut eq, &m, &inp);
        let (xv, sv) = (value_in(&rebuilt, x), value_in(&rebuilt, s));
        assert_eq!(sv.chars().count(), 2, "s = {sv:?}");
        assert_eq!(xv, format!("{sv}c"));
        assert!(input_eqs_hold(&ctx, &[input_eq], &rebuilt, &m));
    }

    /// A side that cannot be evaluated counts as holding.
    #[test]
    fn unevaluable_side_counts_as_holding() {
        let mut ctx = Context::new();
        let m = ModelBuilder::default();
        let (x, y) = (var(&mut ctx, "x"), var(&mut ctx, "y"));
        let e = ctx.mk_eq(x, y).unwrap();
        assert!(input_eqs_hold(&ctx, &[e], &[(x, "a".to_owned())], &m));
        assert!(!input_eqs_hold(
            &ctx,
            &[e],
            &[(x, "a".to_owned()), (y, "b".to_owned())],
            &m
        ));
    }
}
```

Add `mod model_reconcile;` after `pub mod model;` in `crates/shinri-str/src/lib.rs`.

- [ ] **Step 3: Run the tests to verify they fail**

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(char_peel_class_prefers_input_concat) | test(minted_cycle_fills_freely_without_poisoning) | test(unevaluable_side_counts_as_holding)'`
Expected: 3 FAIL (the stubs return an empty list / always `true`). If `char_peel_class_prefers_input_concat` fails at the "documents the defect" assertion instead, the default builder already picks the input concat for this `known` order; reorder `known` until the default build reproduces the defect (the real run listed the minted concat first) and note it.

- [ ] **Step 4: Implement `input_eqs_hold`**

Replace the stub:

```rust
/// True iff every input equation's two sides denote the same word under
/// `vals` (falling back to `m`'s string values). A side is evaluated the way
/// the solver's gate (`Solver::eval_str_val`) does: a constant, else the
/// assigned value, else the concatenation of its operands. A side that cannot
/// be evaluated counts as holding, so this never fires on a term the gate
/// cannot see either. `eq_true` may hold a `Distinct` asserted false; its
/// sides must be equal too.
pub(crate) fn input_eqs_hold(
    terms: &Context,
    input_eqs: &[TermId],
    vals: &[(TermId, String)],
    m: &ModelBuilder,
) -> bool {
    let view: FxHashMap<TermId, &str> = vals.iter().map(|(t, v)| (*t, v.as_str())).collect();
    input_eqs.iter().all(|&atom| {
        let (l, r) = crate::wordeq::diseq_sides(terms, atom);
        match (eval_word(terms, &view, m, l), eval_word(terms, &view, m, r)) {
            (Some(a), Some(b)) => a == b,
            _ => true,
        }
    })
}

fn eval_word(
    terms: &Context,
    view: &FxHashMap<TermId, &str>,
    m: &ModelBuilder,
    t: TermId,
) -> Option<String> {
    if let Some(s) = terms.string_const_value(t) {
        return Some(s.to_owned());
    }
    if let Some(s) = view.get(&t) {
        return Some((*s).to_owned());
    }
    if let Some(ModelVal::String(s)) = m.get(t) {
        return Some(s.clone());
    }
    match terms.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            args,
            ..
        } => {
            let mut out = String::new();
            for &k in terms.children(*args) {
                out.push_str(&eval_word(terms, view, m, k)?);
            }
            Some(out)
        }
        _ => None,
    }
}
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(unevaluable_side_counts_as_holding)'`
Expected: PASS.

- [ ] **Step 5: Implement `reconciled_values`**

Replace the stub:

```rust
/// Rebuild the string valuation (spec §4.2): `(term, value)` for every term of
/// `str_terms` that `m` does not already hold a string for, in `str_terms`
/// order. Starts from a fresh memo seeded only with the membership seeds.
pub(crate) fn reconciled_values(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    m: &ModelBuilder,
    inp: &ReconcileInput<'_>,
) -> Vec<(TermId, String)> {
    let mut r = Reconciler {
        terms,
        eq,
        m,
        inp,
        memo: inp.seeds.clone(),
        in_progress: FxHashSet::default(),
    };
    // Input-equation concats first, longest first, so a top-level concat sets
    // its operands' values before they are valued on their own.
    let mut firsts: Vec<TermId> = inp
        .input_sides
        .iter()
        .copied()
        .filter(|&t| is_concat(r.terms, t))
        .collect();
    firsts.sort_by_key(|&t| (std::cmp::Reverse(concat_arity(r.terms, t)), t.index()));
    for t in firsts {
        let _ = r.value(t);
    }
    let mut out = Vec::new();
    for &t in inp.str_terms {
        if matches!(m.get(t), Some(ModelVal::String(_))) {
            continue;
        }
        let v = r.value(t);
        out.push((t, v));
    }
    out
}

struct Reconciler<'a, 'b> {
    terms: &'a mut Context,
    eq: &'a mut EqualityEngine,
    m: &'a ModelBuilder,
    inp: &'a ReconcileInput<'b>,
    memo: FxHashMap<TermId, String>,
    in_progress: FxHashSet<TermId>,
}

impl Reconciler<'_, '_> {
    fn value(&mut self, t: TermId) -> String {
        if let Some(v) = self.memo.get(&t) {
            return v.clone();
        }
        if let Some(v) = self.terms.string_const_value(t) {
            let v = v.to_owned();
            self.memo.insert(t, v.clone());
            return v;
        }
        if !self.in_progress.insert(t) {
            // Re-entry: a cycle such as `x ≈ s ++ "c"`, `s ≈ x ++ k` (minted).
            // A free fill of the class length, NOT memoised, so the enclosing
            // candidate is judged on its own length and rolled back if wrong.
            let n = self.class_len(t).unwrap_or(0);
            return free_fill(self.eq, t, n);
        }
        let out = if is_concat(self.terms, t) {
            self.value_concat(t)
        } else {
            self.value_var(t)
        };
        self.in_progress.remove(&t);
        self.memo.insert(t, out.clone());
        out
    }

    /// A class constant wins; otherwise the first candidate concat whose word
    /// has the class length (rule 2), with a rejected candidate's memo entries
    /// rolled back; otherwise a free fill of the class length.
    fn value_var(&mut self, t: TermId) -> String {
        let known = self.inp.known;
        if let Some(c) = class_member(self.terms, self.eq, known, t, |terms, mm| {
            terms.string_const_value(mm).is_some() && mm != t
        }) {
            return self
                .terms
                .string_const_value(c)
                .expect("class constant")
                .to_owned();
        }
        let n = self.class_len(t);
        for k in self.candidates(t) {
            let saved = self.memo.clone();
            let v = self.value(k);
            if n.is_none_or(|n| v.chars().count() == n) {
                return v;
            }
            self.memo = saved;
        }
        free_fill(self.eq, t, n.unwrap_or(0))
    }

    /// Concats in `t`'s class other than `t` (rule 1): input-equation sides
    /// first, then other non-minted concats, then minted sides; longer first,
    /// then by term id for determinism.
    fn candidates(&mut self, t: TermId) -> Vec<TermId> {
        let known = self.inp.known;
        let tn = self.eq.intern(t);
        let root = self.eq.find(tn);
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut c: Vec<TermId> = Vec::new();
        for &k in known {
            if k == t || !is_concat(self.terms, k) || !seen.insert(k) {
                continue;
            }
            let kn = self.eq.intern(k);
            if self.eq.find(kn) == root {
                c.push(k);
            }
        }
        let (input, minted) = (self.inp.input_sides, self.inp.minted_sides);
        let rank = |k: TermId| {
            if input.contains(&k) {
                0
            } else if minted.contains(&k) {
                2
            } else {
                1
            }
        };
        let terms = &*self.terms;
        c.sort_by_key(|&k| (rank(k), std::cmp::Reverse(concat_arity(terms, k)), k.index()));
        c
    }

    /// A concat anchored to a fixed word in its class is sliced among its
    /// operands by length (as `model::value_concat` does); otherwise it is
    /// assembled from its operands' values.
    fn value_concat(&mut self, t: TermId) -> String {
        let kids: Vec<TermId> = match self.terms.term_node(t) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrConcat),
                args,
                ..
            } => self.terms.children(*args).to_vec(),
            _ => return String::new(),
        };
        let known = self.inp.known;
        let anchor = class_member(self.terms, self.eq, known, t, |terms, mm| {
            const_word_of(terms, mm).is_some()
        })
        .and_then(|c| const_word_of(self.terms, c));
        match anchor {
            Some(word) => self.slice_word(&kids, &word),
            None => kids.into_iter().map(|k| self.value(k)).collect(),
        }
    }

    /// Record each operand's slice of `word` (constants and already-valued
    /// operands keep their own length; the last operand takes the remainder;
    /// others take their arith length) and return `word`.
    fn slice_word(&mut self, kids: &[TermId], word: &str) -> String {
        let chars: Vec<char> = word.chars().collect();
        let mut off = 0usize;
        for (i, &k) in kids.iter().enumerate() {
            let len = if let Some(c) = self.terms.string_const_value(k) {
                c.chars().count()
            } else if let Some(v) = self.memo.get(&k) {
                v.chars().count()
            } else if i + 1 == kids.len() {
                chars.len().saturating_sub(off)
            } else {
                self.len_of(k).unwrap_or(0)
            };
            let start = off.min(chars.len());
            let end = (off + len).min(chars.len());
            if self.terms.string_const_value(k).is_none() {
                self.memo
                    .entry(k)
                    .or_insert_with(|| chars[start..end].iter().collect());
            }
            off = end;
        }
        word.to_owned()
    }

    /// `str.len k` in the arith model, if arith assigned it.
    fn len_of(&mut self, k: TermId) -> Option<usize> {
        let lt = self
            .terms
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[k])
            .expect("str.len of a string term");
        match self.m.get(lt) {
            Some(ModelVal::Num(r)) if !r.is_negative() => {
                r.numer().to_i128().map(|v| v as usize)
            }
            _ => None,
        }
    }

    /// `t`'s own arith length, else the largest arith length over its class
    /// members; `None` when arith assigned none (then no candidate is
    /// length-checked).
    fn class_len(&mut self, t: TermId) -> Option<usize> {
        if let Some(n) = self.len_of(t) {
            return Some(n);
        }
        let known = self.inp.known;
        let tn = self.eq.intern(t);
        let root = self.eq.find(tn);
        let mut best: Option<usize> = None;
        for &k in known {
            let kn = self.eq.intern(k);
            if self.eq.find(kn) == root {
                if let Some(n) = self.len_of(k) {
                    best = best.max(Some(n));
                }
            }
        }
        best
    }
}
```

If `TermId::index()` or `Rational::numer().to_i128()` has a different name, use the one `model.rs` uses (`len_of_in_model` and `free_fill` show both).

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(char_peel_class_prefers_input_concat) | test(minted_cycle_fills_freely_without_poisoning) | test(unevaluable_side_counts_as_holding)'`
Expected: 3 passed.

- [ ] **Step 6: Write the failing `model_with` tests**

Append inside `mod tests` in `crates/shinri-str/src/lib.rs` (next to `free_var_model_filled_with_default_char`, which shows the setup):

```rust
    /// Slice 57: build a StrSolver whose `eq_true` holds `input` (and
    /// optionally `minted`), with every term forced into `str_terms`.
    fn slice57_solver(
        input: &[TermId],
        minted: &[TermId],
        terms: &[TermId],
    ) -> StrSolver {
        let mut s = StrSolver::default();
        for (i, &a) in input.iter().chain(minted).enumerate() {
            s.eq_true
                .push((a, shinri_core::Lit::new(shinri_core::Var::new(i as u32), true)));
            s.eq_levels.push(0);
        }
        for &a in minted {
            s.minted_eqs.insert(a);
        }
        for &t in terms {
            s.test_force_str_term(t);
        }
        s
    }

    fn slice57_var(ctx: &mut Context, name: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    fn slice57_len(ctx: &mut Context, m: &mut ModelBuilder, t: TermId, n: i64) {
        let l = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[t]).unwrap();
        m.assign(l, ModelVal::Num(shinri_core::Rational::from_int(n.into())));
    }

    fn slice57_merge(eq: &mut EqualityEngine, a: TermId, b: TermId) {
        let an = eq.intern(a);
        let bn = eq.intern(b);
        let _ = eq.merge(an, bn, shinri_theory::types::EqJust::Definitional);
    }

    /// The char-peel class: the default build violates the input equation,
    /// the rebuild is adopted and the strict flag is set.
    #[test]
    fn slice57_model_with_adopts_rebuild_and_flags_strict() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut m = ModelBuilder::default();
        let x = slice57_var(&mut ctx, "x");
        let p = slice57_var(&mut ctx, "p");
        let k = slice57_var(&mut ctx, "k");
        let cd = ctx.mk_string_const("cd");
        let c = ctx.mk_string_const("c");
        let cdp = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[cd, p]).unwrap();
        let ck = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[c, k]).unwrap();
        let input_eq = ctx.mk_eq(x, cdp).unwrap();
        let minted_eq = ctx.mk_eq(x, ck).unwrap();
        slice57_merge(&mut eq, x, cdp);
        slice57_merge(&mut eq, x, ck);
        slice57_len(&mut ctx, &mut m, x, 3);
        slice57_len(&mut ctx, &mut m, p, 1);
        let mut s = slice57_solver(&[input_eq], &[minted_eq], &[ck, x, cd, cdp, k, p, c]);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.model_with(&mut cx, &mut m);
        match m.get(x) {
            Some(ModelVal::String(v)) => {
                assert!(v.starts_with("cd") && v.chars().count() == 3, "x = {v:?}")
            }
            other => panic!("expected a String for x, got {other:?}"),
        }
        assert!(m.strict_check_required());
    }

    /// Two conflicting input concats: no rebuild satisfies both, so the
    /// default model is kept and the flag stays unset.
    #[test]
    fn slice57_model_with_keeps_default_when_rebuild_fails() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut m = ModelBuilder::default();
        let x = slice57_var(&mut ctx, "x");
        let p = slice57_var(&mut ctx, "p");
        let q = slice57_var(&mut ctx, "q");
        let ab = ctx.mk_string_const("ab");
        let cd = ctx.mk_string_const("cd");
        let abp = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[ab, p]).unwrap();
        let cdq = ctx.mk_app(Op::Builtin(BuiltinOp::StrConcat), &[cd, q]).unwrap();
        let e1 = ctx.mk_eq(x, abp).unwrap();
        let e2 = ctx.mk_eq(x, cdq).unwrap();
        slice57_merge(&mut eq, x, abp);
        slice57_merge(&mut eq, x, cdq);
        slice57_len(&mut ctx, &mut m, x, 3);
        slice57_len(&mut ctx, &mut m, p, 1);
        slice57_len(&mut ctx, &mut m, q, 1);
        let mut s = slice57_solver(&[e1, e2], &[], &[x, abp, cdq, p, q, ab, cd]);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.model_with(&mut cx, &mut m);
        assert!(!m.strict_check_required());
        assert!(matches!(m.get(x), Some(ModelVal::String(_))));
    }

    /// The default path: a model that already satisfies its input equations
    /// is unchanged and the flag stays unset.
    #[test]
    fn slice57_model_with_default_path_unflagged() {
        let mut ctx = Context::new();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut m = ModelBuilder::default();
        let x = slice57_var(&mut ctx, "x");
        let ab = ctx.mk_string_const("ab");
        let e = ctx.mk_eq(x, ab).unwrap();
        slice57_merge(&mut eq, x, ab);
        let mut s = slice57_solver(&[e], &[], &[x, ab]);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.model_with(&mut cx, &mut m);
        assert_eq!(m.get(x), Some(&ModelVal::String("ab".into())));
        assert!(!m.strict_check_required());
    }
```

If `eq_true`/`eq_levels`/`minted_eqs` are not visible from `mod tests` (they are private fields of `StrSolver`, which a child module can read), or `Var::new` takes a different integer type, adjust the helper to match `free_var_model_filled_with_default_char` and the struct definition at `lib.rs:30-130`.

Run: `taskset -c 0-11 cargo nextest run -p shinri-str -E 'test(slice57_model_with_)'`
Expected: `slice57_model_with_adopts_rebuild_and_flags_strict` FAILS (no rebuild yet); the other two pass.

- [ ] **Step 7: Wire the rebuild into `model_with`**

In `crates/shinri-str/src/lib.rs`, replace the loop added in Step 1 at the end of `model_with` with:

```rust
        // Slice 57: default build, then self-check against the INPUT string
        // equations (non-minted `eq_true` atoms). Only a violated input
        // equation triggers the reconciliation rebuild, which is adopted if it
        // satisfies every input equation and then requires the strict gate.
        let vals = model::string_values(cx.terms, cx.eq, &known, &str_terms, m, &seeds);
        let input_eqs: Vec<TermId> = self
            .eq_true
            .iter()
            .map(|&(a, _)| a)
            .filter(|a| !self.minted_eqs.contains(a))
            .collect();
        let vals = if model_reconcile::input_eqs_hold(cx.terms, &input_eqs, &vals, m) {
            vals
        } else {
            let mut input_sides: FxHashSet<TermId> = FxHashSet::default();
            let mut minted_sides: FxHashSet<TermId> = FxHashSet::default();
            for &(atom, _) in &self.eq_true {
                let (l, r) = crate::wordeq::diseq_sides(cx.terms, atom);
                let set = if self.minted_eqs.contains(&atom) {
                    &mut minted_sides
                } else {
                    &mut input_sides
                };
                set.insert(l);
                set.insert(r);
            }
            let inp = model_reconcile::ReconcileInput {
                known: &known,
                str_terms: &str_terms,
                seeds: &seeds,
                input_sides: &input_sides,
                minted_sides: &minted_sides,
            };
            let rebuilt = model_reconcile::reconciled_values(cx.terms, cx.eq, m, &inp);
            if model_reconcile::input_eqs_hold(cx.terms, &input_eqs, &rebuilt, m) {
                m.require_strict_check();
                rebuilt
            } else {
                vals
            }
        };
        for (t, v) in vals {
            m.assign(t, ModelVal::String(v));
        }
```

Run: `taskset -c 0-11 cargo nextest run -p shinri-str`
Expected: all pass, including the three `slice57_model_with_*` tests.

- [ ] **Step 8: Run the probes**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver -E 'binary(slice57_probes)' 2>&1 | tee target/slice57-probes-after.log | tail -25`
Expected: 15 discovered, 15 passed. If `p3_*` (the suffix cycle) or `p4` still fail, trace `model_with` with a temporary `eprintln!` (removed before commit) and fix the rebuild, not the probe. If `strict_gate_keeps_unevaluable_unknown` answers `sat`, stop: either an unevaluable assertion passed the strict gate or the rebuild was not flagged. Investigate, and do not change the expectation without a ruling.

- [ ] **Step 9: Tighten the oracle family**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle --no-capture -E 'test(differential_qfs_model_reconcile)' 2>&1 | tee target/slice57-oracle-after.log | grep -E 'differential_qfs_model_reconcile:|PASS|FAIL'`
Expected: PASS, 0 disagreements, and a `with z3 sat` count strictly below the Task 1 count.

Then in `qfs_differential.rs`, under `const MR_N_ITERS`, add the before count from `target/slice57-before.txt` (replace `N` with that number):

```rust
/// `unknown`-where-z3-`sat` count at `46d5fd9` (slice-57 plan, Task 1 Step 4).
const MR_BEFORE_UNKNOWN_Z3_SAT: usize = N;
```

and at the end of `differential_qfs_model_reconcile`:

```rust
    assert!(
        n_unknown_z3_sat < MR_BEFORE_UNKNOWN_Z3_SAT,
        "unknown-where-z3-sat {n_unknown_z3_sat} not below the slice-57 base \
         {MR_BEFORE_UNKNOWN_Z3_SAT}"
    );
```

Re-run the Step 9 command; expected PASS.

- [ ] **Step 10: Format, lint, commit**

```bash
cargo fmt --all
taskset -c 0-11 cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-str/src/model.rs crates/shinri-str/src/model_reconcile.rs crates/shinri-str/src/lib.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "fix(str): slice57 - reconcile multi-concat string classes in the model builder"
```

---

### Task 4: Gates

**Files:** none (logs under `target/`).

- [ ] **Step 1: Full blocking tier**

Run: `taskset -c 0-11 mise run ci 2>&1 | tee target/slice57-ci.log | tail -30`
Expected: lint, deny, secrets and test green. Record the nextest totals (passed / skipped). Any failure in an existing string test (e.g. `qfs_fuzz_corpus`, `script_e2e`, `slice33_probes`) is investigated, not re-pinned: a model that changed for a currently-`sat` input means §4.1's default path was not bit-identical.

- [ ] **Step 2: Oracle suite**

Run: `taskset -c 0-11 cargo nextest run -p shinri-solver --features oracle 2>&1 | tee target/slice57-oracle-suite.log | tail -15`
Expected: non-zero discovered count (slice 56 recorded the suite's size; compare), 0 failures. Record discovered / passed / skipped.

- [ ] **Step 3: Commit nothing; note the totals for the report**

Copy the totals from Steps 1–2 into `target/slice57-before.txt` under a `gates:` heading.

---

### Task 5: Bench run, triage, report, measured outcomes, PR

**Files:**
- Create: `docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice57-str-model-reconcile-report.md` (date = the day the after-run finishes)
- Modify: `docs/superpowers/specs/2026-10-03-shinri-slice57-str-model-reconcile-design.md` (append *Measured outcomes*)

**Interfaces:**
- Consumes: branch HEAD after Task 3; `bench/results/slice57-base/results.jsonl`; `target/slice57-base/shinri`.
- Produces: the report and spec section cited by the PR.

- [ ] **Step 1: Wait for the base run**

Wait for `target/slice57-base/finished.txt` (use a Monitor/until-loop, not a foreground sleep). Then confirm: `wc -l bench/results/slice57-base/results.jsonl` (rows + 1 fixture line) and `grep -c '"verdict"' bench/results/slice57-base/results.jsonl`.

- [ ] **Step 2: Build and launch the after-run detached**

```bash
cargo build --release -p shinri-cli -p shinri-bench
mkdir -p target/slice57-after && cp target/release/shinri target/slice57-after/shinri
md5sum target/slice57-after/shinri | tee target/slice57-after/md5.txt
git rev-parse --short HEAD | tee target/slice57-after/commit.txt
date -u +%FT%TZ > target/slice57-after/started.txt
setsid nohup sh -c 'taskset -c 12-23 target/release/shinri-bench run \
  --logics QF_S,QF_SLIA,QF_LIA \
  --timeout 20 --mem-mb 3072 --jobs 6 \
  --solver target/slice57-after/shinri --run-id slice57 \
  > target/slice57-after/run.log 2>&1; date -u +%FT%TZ > target/slice57-after/finished.txt' \
  > /dev/null 2>&1 &
```

Wait for `target/slice57-after/finished.txt` the same way.

- [ ] **Step 3: Render reports and join the runs**

```bash
BENCH_RUN_ID=slice57-base mise run bench-report
BENCH_RUN_ID=slice57 mise run bench-report
python3 - <<'EOF'
import json, collections
def load(p):
    out = {}
    for line in open(p):
        r = json.loads(line)
        if "path" in r:
            out[r["path"]] = r
    return out
a = load("bench/results/slice57-base/results.jsonl")
b = load("bench/results/slice57/results.jsonl")
assert a.keys() == b.keys(), "row sets differ"
c = collections.Counter()
changed = []
for p in sorted(a):
    va, vb = a[p]["verdict"], b[p]["verdict"]
    if va != vb:
        c[(a[p]["logic"], va, vb)] += 1
        changed.append((p, a[p]["logic"], va, vb))
for k, n in sorted(c.items()):
    print(*k, n)
print("total changed", len(changed))
for lg in ("QF_S", "QF_SLIA", "QF_LIA"):
    for run, d in (("base", a), ("after", b)):
        rej = sum(1 for r in d.values() if r["logic"] == lg and r["verdict"] == "unknown:str-model-rejected")
        cor = sum(1 for r in d.values() if r["logic"] == lg and r["verdict"] == "correct")
        print(lg, run, "correct", cor, "str-model-rejected", rej)
open("target/slice57-after/changed.tsv", "w").write(
    "\n".join("\t".join(x) for x in changed) + "\n")
EOF
```

- [ ] **Step 4: Check every new `sat` that has no ground truth**

For every changed row whose after verdict is `unverified` (shinri `sat`, no `:status`), run z3 (timeout 60 s). Any z3 `unsat` is a wrong answer: stop the slice for a ruling (criterion 1).

```bash
awk -F'\t' '$4=="unverified"{print $1}' target/slice57-after/changed.tsv > target/slice57-after/unverified.txt
while read -r p; do
  printf '%s\t%s\n' "$p" "$(timeout 60 z3 bench/corpus/$p 2>/dev/null | head -1)"
done < target/slice57-after/unverified.txt | tee target/slice57-after/unverified-z3.tsv
grep -c $'\tunsat$' target/slice57-after/unverified-z3.tsv || true
```

Expected: the last count is 0.

- [ ] **Step 5: Triage**

For every changed row that starts or ends in `correct`, and every row that ends in `wrong`: 3 runs per binary, interleaved, with the bench's command line, on cores 12–23 with nothing else running:

```bash
for p in $(awk -F'\t' '$3=="correct"||$4=="correct"||$4=="wrong"{print $1}' target/slice57-after/changed.tsv); do
  for i in 1 2 3; do
    for bin in target/slice57-base/shinri target/slice57-after/shinri; do
      r=$(taskset -c 12-23 prlimit --as=3221225472 timeout -s KILL 21 timeout 20 $bin bench/corpus/$p 2>/dev/null \
          | grep -m1 -E '^(sat|unsat|unknown)$' || echo none)
      printf '%s\t%s\t%s\t%s\n' "$p" "$(basename $(dirname $bin))" "$i" "$r"
    done
  done
done | tee target/slice57-after/triage.tsv
```

If a group has more than 200 rows, triage a stratified sample of at least 32 rows across its families instead, and state the sample size. Classify each row as in the slice-53 report: *attributable* if base and after each reproduce their bench verdict 3/3, *noise* otherwise. Any wrong answer from the after binary stops the slice (criterion 1). A net `correct` loss in any logic stops the slice for a ruling (criterion 4).

- [ ] **Step 6: Timing**

From the two `results.jsonl`, report median and p90 `wall_ms` per logic over rows that are `correct` in both runs (criterion 6).

- [ ] **Step 7: Write the report**

Follow the structure of `docs/superpowers/research/2026-10-03-smtlib-2024-slice56-uf-bool-const-report.md`:
- *Headline*
- *Commands* (the exact commands from Tasks 0, 4 and 5)
- *Runs*: both binaries with md5, started/finished, row counts
- *Success criteria*: spec §8 table, each PASS/FAIL with evidence
  - probes: `target/slice57-probes-before.log` / `-after.log`
  - oracle: before/after summary lines
  - gates: Task 4 totals
- *Per-logic matrix*, including `str-model-rejected` base vs after
- *Transition matrices* with closure arithmetic
- *Triage*: method, dispositions, the unverified-z3 check
- *Timing*
- *What changed versus the spec*: every deviation, including any generator change from Task 1 Step 4 and any `known` reordering from Task 3 Step 3
- *Gates*
- *Queued for the next slice*: spec §9 items 1–3, then the slice-56 report's queue items 3 onwards and its carried lists, copied verbatim, with a line saying the engine part of item 2 is split by slice 57 into §9 items 1–2

- [ ] **Step 8: Append *Measured outcomes* to the spec**

Append to `docs/superpowers/specs/2026-10-03-shinri-slice57-str-model-reconcile-design.md`:

```markdown
## 11. Measured outcomes

Full evidence:
`docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice57-str-model-reconcile-report.md`.

| # | criterion | result |
| --- | --- | --- |
| 1 | 0 `* → wrong`; 0 wrong answers in triage | <PASS/FAIL + counts, unverified-z3 check> |
| 2 | §1.1 shapes and `multiply-reverse-fuzz` answer `sat` | <PASS/FAIL> |
| 3 | `str-model-rejected` decreases in QF_S + QF_SLIA | <base → after per logic> |
| 4 | `correct → *` triaged; net `correct` ≥ 0 per logic | <PASS/FAIL + raw and credited net> |
| 5 | oracle before/after, 0 disagreements; `ci` green | <PASS/FAIL + counts> |
| 6 | median/p90 ms per logic | <numbers> |

### Deviations from this spec

- <each deviation, or "None.">
```

Replace every `<…>` with measured values before committing; none may remain.

- [ ] **Step 9: Commit, push, PR**

```bash
git add docs/superpowers/research/*slice57* docs/superpowers/specs/2026-10-03-shinri-slice57-str-model-reconcile-design.md
git commit -m "docs(bench+spec): slice57 - bench run and measured outcomes"
git push -u origin slice57-str-model-reconcile
gh pr create --base main --title "slice57: string model reconciliation for multi-concat classes" \
  --body "Spec: docs/superpowers/specs/2026-10-03-shinri-slice57-str-model-reconcile-design.md
Plan: docs/superpowers/plans/2026-10-03-shinri-slice57-str-model-reconcile.md
Report: docs/superpowers/research/<YYYY-MM-DD>-smtlib-2024-slice57-str-model-reconcile-report.md

<headline numbers from the report: wrong rows, str-model-rejected base → after, net correct per logic, oracle counts>"
```

Fill the body's placeholders from the report before running. Merge with a merge commit only after CI is green, then delete the branch locally and on the remote (AGENTS.md); ask the user before merging.
