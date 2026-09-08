# Slice 46 — SMT-LIB Benchmark Harness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `shinri-bench` (fetch / run / rerun / report over the SMT-LIB 2024 non-incremental corpus), add the `--stats` fence-tag hook to `shinri-cli`, and commit the first full-corpus baseline report.

**Architecture:** A new workspace binary crate orchestrates system tools (`curl`, `md5sum`, `timeout`, `prlimit`, `z3`, `cvc5`) via `std::process`, decodes the Zenodo `.tar.zst` archives in-process (pure-Rust `ruzstd` + a hand-rolled ustar reader), runs a 6-worker pool that writes one JSONL row per instance, and renders a Markdown report. The solver gains a `last_fence` tag so `unknown` answers are attributable; the CLI surfaces it on stderr under `--stats`.

**Tech Stack:** Rust 1.98 (workspace floor 1.96), `ruzstd 0.9.0` (pure Rust, MIT, `default-features = false, features = ["std"]`) as the ONLY new dependency (tooling crate only — the solver crates stay dependency-free), cargo-nextest, z3/cvc5 from mise.

**Spec:** `docs/superpowers/specs/2026-09-08-shinri-slice46-smtlib-bench-harness-design.md`. Two spec amendments are made in Task 1 (recorded there as as-built deltas): Zenodo publishes **md5**, not sha256, so the manifest stores md5 and verification shells out to `md5sum`; and there is no `zstd` binary the pod can get through mise (facebook/zstd ships no Linux release binaries), so extraction is in-process via `ruzstd` instead of `tar --zstd`.

## Global Constraints

- Blocking-tier test budget: every test added here must run in seconds; nothing in this plan touches the nightly tier.
- `cargo fmt --all` and `cargo clippy --workspace --all-targets -- -D warnings` clean before every commit (CI fails fast on fmt).
- Native-link dependencies are banned (`deny.toml`); `ruzstd` is pure Rust. No other new dependency anywhere. Solver crates (`shinri-solver`, `shinri-cli`) gain **zero** dependencies.
- `shinri-cli` stdout must be byte-identical with and without `--stats`.
- No solver behaviour change: `SolveOutcome` values are unchanged; only a side-channel tag is added.
- Paths: crate at `crates/shinri-bench`; committed manifest at `bench/manifest.toml`; git-ignored `bench/corpus/` and `bench/results/`.
- nextest filters use `-E 'test(<name>)'`; always confirm a non-zero discovered count.
- Budget defaults: timeout 20 s, memory 3072 MB address space, 6 jobs (pod cgroup: 8 CPU quota, 32 GiB).
- Zenodo record: `10.5281/zenodo.11061097` — "SMT-LIB release 2024 (non-incremental benchmarks)", version 2024.04.23. File URL pattern: `https://zenodo.org/api/records/11061097/files/<LOGIC>.tar.zst/content`.

---

## File map

| File | Responsibility |
|---|---|
| `crates/shinri-solver/src/lib.rs` | `last_fence: Option<&'static str>` on `Solver`; tag at every `Unknown` site; `pub fn last_fence()` |
| `crates/shinri-solver/tests/fence_tags.rs` | NEW — asserts tags for representative fences and `None` on decided |
| `crates/shinri-cli/src/args.rs` | `--stats` flag → `Invocation::Run { input, stats }` |
| `crates/shinri-cli/src/driver.rs` | wall-clock around `check-sat`, `stats:` line on stderr |
| `crates/shinri-cli/tests/cli.rs` | `--stats` black-box tests |
| `crates/shinri-bench/Cargo.toml` | binary crate, `ruzstd` dep |
| `crates/shinri-bench/src/main.rs` | arg parsing + subcommand dispatch only |
| `crates/shinri-bench/src/verdict.rs` | `Verdict`, `Answer`, `OracleAnswers`, `classify` (pure) |
| `crates/shinri-bench/src/instance.rs` | `Instance` (path, logic, bytes, `:status`), corpus walk |
| `crates/shinri-bench/src/json.rs` | minimal JSON string escape/unescape + flat-object reader |
| `crates/shinri-bench/src/results.rs` | `Row`, `Fixture`, JSONL append/read/resume |
| `crates/shinri-bench/src/archive.rs` | multi-frame zstd `Read` adapter + ustar extractor |
| `crates/shinri-bench/src/corpus.rs` | manifest parse, download, md5 verify, extract, `.verified` |
| `crates/shinri-bench/src/process.rs` | limited child process runner (`prlimit`+`timeout`), `Exec` result |
| `crates/shinri-bench/src/oracle.rs` | z3 → cvc5 on-demand adjudication |
| `crates/shinri-bench/src/runner.rs` | worker pool, per-instance pipeline, progress |
| `crates/shinri-bench/src/report.rs` | Markdown report from rows |
| `crates/shinri-bench/tests/runner_e2e.rs` | mini-corpus + stub solver end-to-end |
| `crates/shinri-bench/tests/corpus/*.smt2`, `stub-solver.sh` | fixtures |
| `crates/shinri-bench/tests/fixtures/report_rows.jsonl`, `report_golden.md` | report golden |
| `bench/manifest.toml` | pinned archives |
| `mise.toml`, `README.md`, `.gitignore`, `Cargo.toml` (workspace members) | wiring |

---

### Task 1: Fence tags in the solver

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (struct at ~`:100–126`, ctor at ~`:236–246`, `check_sat` at `:724`, every `SolveOutcome::Unknown` site listed below)
- Create: `crates/shinri-solver/tests/fence_tags.rs`
- Modify: `docs/superpowers/specs/2026-09-08-shinri-slice46-smtlib-bench-harness-design.md` (as-built note)

**Interfaces:**
- Produces: `Solver::last_fence(&self) -> Option<&'static str>`; `None` after `Sat`/`Unsat`, `Some(tag)` after `Unknown`. Tag vocabulary is the table below (Task 2 and Task 9 consume the strings verbatim).

Tag table — one per `return SolveOutcome::Unknown` / `=> SolveOutcome::Unknown` in `check_sat_inner` (line numbers as of `2932d20d`; re-grep with `grep -n "SolveOutcome::Unknown" crates/shinri-solver/src/lib.rs` before editing):

| Line | Guard | Tag |
|---|---|---|
| 766 | `any_fun_sig_mentions(reglan_sort())` | `reglan-decl` |
| 788 | `string_stage::fenced` | `str-fenced` |
| 813 | `has_unreduced_indexof_replace` | `str-indexof-replace` |
| 816 | `has_unrewritable_str_predicate` | `str-predicate-polarity` |
| 836 | `has_unreduced_int_conv` | `str-int-conv` |
| 848 | `has_unreduced_code_conv` | `str-code-conv` |
| 858 | `has_unreduced_str_order` | `str-order` |
| 870 | `has_unsupported_regex` | `str-regex` |
| 886 | `has_unfoldable_substr_or_at` | `str-substr-at` |
| 904 | `abv_stage::fenced` | `abv-fenced` |
| 911 | `uf_args_supported` (abv) | `abv-uf-args` |
| 918 | `uf_congruence_cost` (abv) | `abv-uf-budget` |
| 953 | `AbvOutcome::Unknown =>` | `abv-engine` |
| 1000 | `uses_crossing_conversion` | `fp-crossing-conversion` |
| 1010 | `has_non_bv_theory_atom` | `bv-non-bv-atom` |
| 1015 | `uf_args_supported` (bv) | `bv-uf-args` |
| 1023 | `uf_congruence_cost` (bv) | `bv-uf-budget` |
| 1066 | `has_non_bvfp_theory_atom` | `fp-non-bvfp-atom` |
| 1075 | `fp_atoms_fully_supported` | `fp-atoms-unsupported` |
| 1081 | `bv_atoms_fp_supported` | `fp-bv-atoms-unsupported` |
| 1096 | `uf_args_supported` (fp∪bv) | `fpbv-uf-args` |
| 1102 | `uf_congruence_cost` (fp∪bv) | `fpbv-uf-budget` |
| 1270 | `refused \|\| mixed \|\| lira` | `theory-refused` / `theory-mixed-sort` / `theory-lira` — split into three tags: `if refused { tag } else if mixed { tag } else { tag }` |
| 1276 | `SolveResult::Unknown =>` | `sat-budget` |
| 1427 | `!string_model_satisfies` | `str-model-rejected` |

Any site not in this table that the grep finds gets a tag named after its guard in the same style — never leave one untagged; the Task-1 reviewer greps for `SolveOutcome::Unknown` sites without a preceding `self.last_fence = Some(`.

- [ ] **Step 1: Write the failing test**

`crates/shinri-solver/tests/fence_tags.rs`:

```rust
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
    let (r, tag) = run("(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 0.0))(assert (< x 0.0))(check-sat)");
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
```

If `bv_mixed_with_int_is_tagged` turns out to hit a different fence first (e.g. `theory-mixed-sort`), keep the probe and change the expected tag to what the code actually does — the test pins the tag, it does not pick the fence. Record which in the commit message.

- [ ] **Step 2: Run it to verify it fails**

Run: `cargo nextest run -p shinri-solver -E 'binary(fence_tags)'`
Expected: compile error — `no method named last_fence`.

- [ ] **Step 3: Add the field, the accessor, the clear, and the tags**

In the `Solver` struct (after `last_outcome`):

```rust
    /// Slice 46: which fence produced the most recent `Unknown`, as a short
    /// stable tag (see the tag table in the slice-46 plan). `None` whenever
    /// the last `check_sat` decided, or nothing has been solved yet. Read by
    /// `shinri-cli --stats` so a benchmark run can attribute every `unknown`
    /// to the guard that raised it.
    last_fence: Option<&'static str>,
```

Ctor: `last_fence: None,`.

Accessor, next to `set_stage_b`:

```rust
    /// The fence tag behind the most recent `Unknown` (slice 46), or `None`.
    pub fn last_fence(&self) -> Option<&'static str> {
        self.last_fence
    }
```

`check_sat`:

```rust
    pub fn check_sat(&mut self) -> SolveOutcome {
        self.last_fence = None;
        let outcome = self.check_sat_inner();
        self.last_outcome = Some(outcome);
        outcome
    }
```

Then at every site in the tag table, insert the assignment on the line before the return, e.g.

```rust
        if self.ctx.any_fun_sig_mentions(self.ctx.reglan_sort()) {
            self.last_fence = Some("reglan-decl");
            return SolveOutcome::Unknown;
        }
```

Match arms (`:953`, `:1276`) become blocks:

```rust
            shinri_abv::AbvOutcome::Unknown => {
                self.last_fence = Some("abv-engine");
                SolveOutcome::Unknown
            }
```

Line 1270:

```rust
        if refused || mixed || lira {
            self.last_fence = Some(if refused {
                "theory-refused"
            } else if mixed {
                "theory-mixed-sort"
            } else {
                "theory-lira"
            });
            return SolveOutcome::Unknown;
        }
```

If a site is inside a closure or a helper that cannot see `self`, return the tag from the helper instead of assigning — do not skip it.

- [ ] **Step 4: Run the tests**

Run: `cargo nextest run -p shinri-solver -E 'binary(fence_tags)'` — expected: 6 tests, PASS.
Run: `cargo nextest run -p shinri-solver` — expected: all previously passing tests still pass (no behaviour change).
Run: `grep -n "SolveOutcome::Unknown" crates/shinri-solver/src/lib.rs` and confirm each hit inside `check_sat_inner` is preceded by a `self.last_fence = Some(` (the `CheckSatAssuming` arm in `execute` is NOT a `check_sat` site and stays untagged).

- [ ] **Step 5: Spec as-built note**

Append to spec §3.1: "As built: 25 sites, not twelve — the count in the design was the string-path range only. Tags are enumerated in the plan's Task 1 table."

- [ ] **Step 6: fmt, clippy, commit**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-solver docs/superpowers/specs/2026-09-08-shinri-slice46-smtlib-bench-harness-design.md
git commit -m "feat(solver): slice46 T1 - tag every check_sat Unknown with its fence"
```

---

### Task 2: `shinri --stats`

**Files:**
- Modify: `crates/shinri-cli/src/args.rs`
- Modify: `crates/shinri-cli/src/driver.rs` (`handle`, `:130–155`)
- Modify: `crates/shinri-cli/src/main.rs`
- Modify: `crates/shinri-cli/tests/cli.rs`

**Interfaces:**
- Consumes: `Solver::last_fence()` (Task 1).
- Produces: stderr line per `check-sat`: `stats: cmd=check-sat wall_ms=<u64> outcome=<sat|unsat|unknown> fence=<tag|->`. Task 7's runner parses exactly this.

- [ ] **Step 1: Failing tests**

Append to `crates/shinri-cli/tests/cli.rs`:

```rust
/// Run with extra args and stdin; return (stdout, stderr, code).
fn run_with(args: &[&str], stdin_text: &str) -> (String, String, Option<i32>) {
    let mut child = bin()
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(stdin_text.as_bytes()).unwrap();
    let out = child.wait_with_output().unwrap();
    (
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
        out.status.code(),
    )
}

const SAT_SCRIPT: &str = "(set-option :print-success false)\
(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 0.0))(check-sat)";

const FENCED_SCRIPT: &str = "(set-option :print-success false)\
(set-logic QF_S)(declare-fun a () String)(declare-fun b () String)\
(assert (str.< a b))(check-sat)";

#[test]
fn stats_line_shape_on_sat() {
    let (stdout, stderr, code) = run_with(&["--stats"], SAT_SCRIPT);
    assert_eq!(stdout, "sat\n");
    assert_eq!(code, Some(0));
    let lines: Vec<&str> = stderr.lines().filter(|l| l.starts_with("stats:")).collect();
    assert_eq!(lines.len(), 1, "stderr: {stderr:?}");
    let fields: Vec<&str> = lines[0].split(' ').collect();
    assert_eq!(fields[0], "stats:");
    assert_eq!(fields[1], "cmd=check-sat");
    assert!(fields[2].starts_with("wall_ms="));
    fields[2]["wall_ms=".len()..].parse::<u64>().unwrap();
    assert_eq!(fields[3], "outcome=sat");
    assert_eq!(fields[4], "fence=-");
    assert_eq!(fields.len(), 5);
}

#[test]
fn stats_line_names_the_fence_on_unknown() {
    let (stdout, stderr, _) = run_with(&["--stats"], FENCED_SCRIPT);
    assert_eq!(stdout, "unknown\n");
    assert!(stderr.contains("outcome=unknown fence=str-order"), "stderr: {stderr:?}");
}

#[test]
fn stats_does_not_change_stdout() {
    for script in [SAT_SCRIPT, FENCED_SCRIPT, UNSAT_SCRIPT] {
        let (plain, _, _) = run_with(&[], script);
        let (with, stderr, _) = run_with(&["--stats"], script);
        assert_eq!(plain, with);
        assert_eq!(stderr.lines().filter(|l| l.starts_with("stats:")).count(), 1);
    }
}

#[test]
fn no_stats_line_without_the_flag() {
    let (_, stderr, _) = run_with(&[], SAT_SCRIPT);
    assert!(!stderr.contains("stats:"));
}

#[test]
fn stats_one_line_per_check_sat() {
    let (_, stderr, _) = run_with(
        &["--stats"],
        "(set-option :print-success false)(set-logic QF_LRA)(declare-fun x () Real)\
         (push 1)(assert (> x 0.0))(check-sat)(pop 1)(assert (< x 0.0))(check-sat)",
    );
    assert_eq!(stderr.lines().filter(|l| l.starts_with("stats:")).count(), 2);
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo nextest run -p shinri-cli -E 'test(stats_)'`
Expected: 5 tests discovered, all FAIL (`--stats` is rejected as unknown, exit 2).

- [ ] **Step 3: Implement**

`args.rs`: `Invocation::Run { input: Input, stats: bool }`; in `parse_args` add `"--stats" => stats = true,` before the generic `-` arm; construct with `stats`. Update USAGE:

```
Options:
  -h, --help       Print this help and exit
  -V, --version    Print version and exit
      --stats      After each check-sat, print a `stats:` line on stderr
                   (wall_ms, outcome, and the fence tag behind an unknown)
```

Update the existing `args.rs` unit tests to the new struct shape (`stats: false`) and add:

```rust
    #[test]
    fn stats_flag_sets_stats() {
        assert_eq!(
            parse(&["--stats", "a.smt2"]),
            Ok(Invocation::Run { input: Input::File("a.smt2".into()), stats: true })
        );
    }
```

`driver.rs`: add `pub stats: bool` to `Presentation` (default `false`), `Driver::with_stats(stats: bool) -> Driver`, and in `handle`:

```rust
        let exiting = matches!(cmd, Command::Exit);
        let is_check_sat = matches!(cmd, Command::CheckSat);
        let started = std::time::Instant::now();
        let resp = self.solver.execute(cmd);
        if self.pres.stats && is_check_sat {
            let outcome = match &resp {
                CommandResponse::Sat => "sat",
                CommandResponse::Unsat => "unsat",
                _ => "unknown",
            };
            eprintln!(
                "stats: cmd=check-sat wall_ms={} outcome={} fence={}",
                started.elapsed().as_millis(),
                outcome,
                self.solver.last_fence().unwrap_or("-")
            );
        }
        match resp { /* unchanged arms */ }
```

`main.rs`: `Ok(args::Invocation::Run { input, stats }) => run(input, stats)`, and `run` builds `driver::Driver::with_stats(stats)`.

- [ ] **Step 4: Run tests**

Run: `cargo nextest run -p shinri-cli` — expected: all pass, the 5 new ones included.

- [ ] **Step 5: fmt, clippy, commit**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-cli
git commit -m "feat(cli): slice46 T2 - --stats prints wall time, outcome and fence tag per check-sat"
```

---

### Task 3: Crate scaffold, `json.rs`, and `verdict.rs`

**Files:**
- Create: `crates/shinri-bench/Cargo.toml`, `src/main.rs`, `src/json.rs`, `src/verdict.rs`
- Modify: `Cargo.toml` (workspace members), `.gitignore`

**Interfaces (produced):**

```rust
// verdict.rs
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Answer { Sat, Unsat, Unknown, Timeout }
impl Answer { pub fn parse(s: &str) -> Option<Answer>; pub fn as_str(self) -> &'static str; }

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct OracleAnswers { pub z3: Option<Answer>, pub cvc5: Option<Answer> }

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    Correct, Wrong, StatusSuspect, ParseError, Panic, Oom, Timeout,
    Unknown(String), Unverified, Malformed(String),
    /// Not final: the runner must consult the oracle and classify again.
    NeedsOracle,
}
impl Verdict { pub fn key(&self) -> String; pub fn parse(key: &str) -> Verdict; }

pub struct Observed<'a> {
    pub rc: Option<i32>,        // None = killed by signal
    pub killed_by_timeout: bool, // process.rs sets this from rc 124/137 + elapsed
    pub answers: &'a [Answer],  // stdout sat/unsat/unknown lines in order
    pub stderr: &'a str,
    pub fence: Option<&'a str>,
    pub status: Option<Answer>, // :status; None = absent
    pub oracle: Option<&'a OracleAnswers>,
}
pub fn classify(o: &Observed) -> Verdict;
```

```rust
// json.rs
pub fn escape(s: &str) -> String;                 // RFC 8259, wraps in quotes
pub fn parse_object(line: &str) -> Option<Vec<(String, JsonVal)>>;
pub enum JsonVal { Str(String), Num(i64), Bool(bool), Null, Arr(Vec<JsonVal>), Obj(Vec<(String, JsonVal)>) }
```

`Verdict::key` strings (stored in JSONL, used by report): `correct`, `wrong`, `status-suspect`, `parse-error`, `panic`, `oom`, `timeout`, `unknown:<tag>`, `unverified`, `malformed:<reason>`, `needs-oracle`.

- [ ] **Step 1: Scaffold**

`crates/shinri-bench/Cargo.toml`:

```toml
[package]
name = "shinri-bench"
version = "0.1.0"
edition.workspace = true
license.workspace = true
rust-version.workspace = true

[[bin]]
name = "shinri-bench"
path = "src/main.rs"

[dependencies]
# Tooling crate only — the solver crates stay dependency-free. Pure Rust,
# MIT; `hash` disabled (archive integrity is the manifest md5, not the frame
# checksum) so twox-hash is not pulled in.
ruzstd = { version = "0.9.0", default-features = false, features = ["std"] }
```

Add `"crates/shinri-bench"` to workspace `members`. Append to `.gitignore`:

```
# SMT-LIB corpus and benchmark results (slice 46) — fetched, never committed
bench/corpus/
bench/results/
```

`src/main.rs` for now:

```rust
//! shinri-bench: fetch / run / rerun / report over the SMT-LIB corpus.
mod json;
mod verdict;

fn main() {
    eprintln!("shinri-bench: not wired yet");
    std::process::exit(2);
}
```

- [ ] **Step 2: Failing tests for `json.rs`**

In `src/json.rs` `#[cfg(test)] mod tests`:

```rust
    #[test]
    fn escape_round_trips_control_and_unicode() {
        let s = "a\"b\\c\nd\te\u{1F600}\u{1}";
        let e = escape(s);
        assert_eq!(e, "\"a\\\"b\\\\c\\nd\\te\u{1F600}\\u0001\"");
        let obj = parse_object(&format!("{{\"k\":{e}}}")).unwrap();
        assert_eq!(obj[0].0, "k");
        assert!(matches!(&obj[0].1, JsonVal::Str(v) if v == s));
    }

    #[test]
    fn parse_flat_object_with_all_value_kinds() {
        let obj = parse_object(
            r#"{"s":"x","n":-42,"b":true,"z":null,"a":["sat","unsat"],"o":{"z3":"sat","cvc5":null}}"#,
        )
        .unwrap();
        assert_eq!(obj.len(), 6);
        assert!(matches!(&obj[1].1, JsonVal::Num(-42)));
        assert!(matches!(&obj[2].1, JsonVal::Bool(true)));
        assert!(matches!(&obj[3].1, JsonVal::Null));
        assert!(matches!(&obj[4].1, JsonVal::Arr(a) if a.len() == 2));
        assert!(matches!(&obj[5].1, JsonVal::Obj(o) if o.len() == 2));
    }

    #[test]
    fn parse_rejects_garbage() {
        assert!(parse_object("{\"k\":}").is_none());
        assert!(parse_object("not json").is_none());
        assert!(parse_object("{\"k\":\"unterminated}").is_none());
    }
```

- [ ] **Step 3: Implement `json.rs`**

`escape`: iterate chars; `"`→`\"`, `\\`→`\\\\`, `\n`/`\r`/`\t`→`\n`/`\r`/`\t`, other `< 0x20` → `\u00XX`, everything else verbatim (UTF-8 passes through). `parse_object`: a small recursive-descent over `&[u8]` with a cursor: `ws`, `expect(b)`, `string` (handles `\"` `\\` `\/` `\b` `\f` `\n` `\r` `\t` `\uXXXX` incl. surrogate pairs), `number` (optional `-`, digits only — the harness never writes fractions), `true`/`false`/`null`, `array`, `object`. Return `None` on any error or trailing non-whitespace. ~150 lines; no `unsafe`, no panics on malformed input (the report reads files that a killed run may have truncated).

- [ ] **Step 4: Failing tests for `verdict.rs`**

One test per spec §5 row plus the escalations:

```rust
    use super::*;
    use Answer::*;

    fn obs<'a>(rc: Option<i32>, answers: &'a [Answer], stderr: &'a str, status: Option<Answer>) -> Observed<'a> {
        Observed { rc, killed_by_timeout: false, answers, stderr, fence: None, status, oracle: None }
    }

    #[test] fn correct_matches_status() {
        assert_eq!(classify(&obs(Some(0), &[Unsat], "", Some(Unsat))), Verdict::Correct);
    }
    #[test] fn decided_without_status_needs_oracle() {
        assert_eq!(classify(&obs(Some(0), &[Sat], "", None)), Verdict::NeedsOracle);
        assert_eq!(classify(&obs(Some(0), &[Sat], "", Some(Unknown))), Verdict::NeedsOracle);
    }
    #[test] fn oracle_agreement_is_correct() {
        let o = OracleAnswers { z3: Some(Sat), cvc5: None };
        let mut ob = obs(Some(0), &[Sat], "", None); ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Correct);
    }
    #[test] fn oracle_disagreement_without_status_is_wrong() {
        let o = OracleAnswers { z3: Some(Unsat), cvc5: None };
        let mut ob = obs(Some(0), &[Sat], "", None); ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Wrong);
    }
    #[test] fn oracle_unknown_or_timeout_is_unverified() {
        for z in [Unknown, Timeout] {
            let o = OracleAnswers { z3: Some(z), cvc5: Some(Timeout) };
            let mut ob = obs(Some(0), &[Sat], "", None); ob.oracle = Some(&o);
            assert_eq!(classify(&ob), Verdict::Unverified);
        }
    }
    #[test] fn contradicting_status_needs_oracle_first() {
        assert_eq!(classify(&obs(Some(0), &[Sat], "", Some(Unsat))), Verdict::NeedsOracle);
    }
    #[test] fn contradicting_status_with_oracle_on_status_side_is_wrong() {
        let o = OracleAnswers { z3: Some(Unsat), cvc5: None };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat)); ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Wrong);
    }
    #[test] fn contradicting_status_z3_agrees_needs_cvc5() {
        let o = OracleAnswers { z3: Some(Sat), cvc5: None };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat)); ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::NeedsOracle);
    }
    #[test] fn both_oracles_agree_with_shinri_is_status_suspect() {
        let o = OracleAnswers { z3: Some(Sat), cvc5: Some(Sat) };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat)); ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::StatusSuspect);
    }
    #[test] fn cvc5_sides_with_status_is_wrong() {
        let o = OracleAnswers { z3: Some(Sat), cvc5: Some(Unsat) };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat)); ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Wrong);
    }
    #[test] fn oracle_timeout_on_contradiction_is_still_wrong() {
        // :status is an independent claim; an oracle that cannot decide does
        // not rescue a contradiction of it.
        let o = OracleAnswers { z3: Some(Timeout), cvc5: Some(Unknown) };
        let mut ob = obs(Some(0), &[Sat], "", Some(Unsat)); ob.oracle = Some(&o);
        assert_eq!(classify(&ob), Verdict::Wrong);
    }
    #[test] fn unknown_answer_keys_on_fence() {
        let mut ob = obs(Some(0), &[Unknown], "", Some(Sat)); ob.fence = Some("str-order");
        assert_eq!(classify(&ob), Verdict::Unknown("str-order".into()));
        let ob2 = obs(Some(0), &[Unknown], "", Some(Sat));
        assert_eq!(classify(&ob2), Verdict::Unknown("-".into()));
    }
    #[test] fn error_before_answer_is_parse_error() {
        assert_eq!(classify(&obs(Some(0), &[], "(error \"unknown symbol foo\")", None)), Verdict::ParseError);
    }
    #[test] fn panic_is_panic() {
        assert_eq!(classify(&obs(Some(101), &[], "thread 'main' panicked at ...", Some(Sat))), Verdict::Panic);
    }
    #[test] fn allocation_failure_is_oom() {
        assert_eq!(classify(&obs(Some(134), &[], "memory allocation of 4294967296 bytes failed", None)), Verdict::Oom);
        assert_eq!(classify(&obs(None, &[], "", None)), Verdict::Oom); // SIGKILL before the limit
    }
    #[test] fn timeout_is_timeout() {
        let mut ob = obs(Some(124), &[], "", Some(Sat)); ob.killed_by_timeout = true;
        assert_eq!(classify(&ob), Verdict::Timeout);
        let mut ob2 = obs(None, &[], "", None); ob2.killed_by_timeout = true;
        assert_eq!(classify(&ob2), Verdict::Timeout);
    }
    #[test] fn two_answers_is_malformed() {
        assert!(matches!(classify(&obs(Some(0), &[Sat, Sat], "", Some(Sat))), Verdict::Malformed(_)));
    }
    #[test] fn no_answer_clean_exit_is_malformed() {
        assert!(matches!(classify(&obs(Some(0), &[], "", Some(Sat))), Verdict::Malformed(_)));
    }
    #[test] fn keys_round_trip() {
        for v in [Verdict::Correct, Verdict::Wrong, Verdict::StatusSuspect, Verdict::ParseError,
                  Verdict::Panic, Verdict::Oom, Verdict::Timeout, Verdict::Unknown("x-y".into()),
                  Verdict::Unverified, Verdict::Malformed("spawn".into()), Verdict::NeedsOracle] {
            assert_eq!(Verdict::parse(&v.key()), v);
        }
    }
```

Note: the `ParseError` test passes the `(error …)` text via `stderr` for brevity; the real driver writes `(error …)` to **stdout**. `Observed` therefore also needs `pub stdout_errors: usize` — the count of `(error` lines on stdout seen before the first answer. Add that field (set to 0 in `obs`) and make the test set `stdout_errors: 1` with empty stderr instead. Rule: `ParseError` if `stdout_errors > 0 && answers.is_empty()`, or rc == 2 (the CLI's own usage/IO error exit).

- [ ] **Step 5: Implement `classify`** — precedence order, top to bottom:

1. `killed_by_timeout` → `Timeout`.
2. `rc == Some(101)` or stderr contains `panicked at` → `Panic`.
3. stderr contains `memory allocation of` and `failed`, or `rc == Some(134)`, or `rc == None` (signal, not timeout) → `Oom`.
4. `stdout_errors > 0 && answers.is_empty()`, or `rc == Some(2)` → `ParseError`.
5. `answers.len() != 1` → `Malformed("answers=<n>")`.
6. `answers[0] == Unknown` → `Unknown(fence.unwrap_or("-"))`.
7. decided `a`:
   - `status == Some(a)` → `Correct`.
   - `status` absent/`Unknown`: oracle `None` → `NeedsOracle`; `z3 == Some(a)` → `Correct`; `z3` decided ≠ `a` → `Wrong`; `z3` ∈ {Unknown, Timeout} → `Unverified`.
   - `status == Some(s)`, `s` decided ≠ `a`: oracle `None` → `NeedsOracle`; `z3` decided ≠ `a` → `Wrong`; `z3` ∈ {Unknown, Timeout} → `Wrong`; `z3 == Some(a)`: `cvc5 == None` → `NeedsOracle`; `cvc5 == Some(a)` → `StatusSuspect`; else → `Wrong`.

- [ ] **Step 6: Run, fmt, clippy, commit**

Run: `cargo nextest run -p shinri-bench` — expected: 3 json + 19 verdict tests PASS.

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add Cargo.toml Cargo.lock .gitignore crates/shinri-bench
git commit -m "feat(bench): slice46 T3 - shinri-bench crate, JSON codec, verdict classifier"
```

---

### Task 4: `instance.rs` and `results.rs`

**Files:**
- Create: `crates/shinri-bench/src/instance.rs`, `crates/shinri-bench/src/results.rs`
- Modify: `crates/shinri-bench/src/main.rs` (add `mod`s)

**Interfaces (produced):**

```rust
// instance.rs
pub struct Instance { pub rel_path: String, pub abs_path: PathBuf, pub logic: String, pub bytes: u64, pub status: Option<Answer> }
/// Scan the first 64 KiB for `(set-info :status <sat|unsat|unknown>)` outside comments.
pub fn scan_status(head: &str) -> Option<Answer>;
/// Walk `<corpus>/<LOGIC>/**/*.smt2` for each logic; sorted by rel_path.
pub fn walk(corpus: &Path, logics: &[String]) -> io::Result<Vec<Instance>>;

// results.rs
pub struct Fixture { pub sha: String, pub version: String, pub timeout_s: u64, pub mem_mb: u64, pub jobs: usize,
                     pub cpu_max: String, pub memory_max: String, pub corpus: String, pub started: String }
pub struct Row { pub path: String, pub logic: String, pub bytes: u64, pub status: Option<Answer>,
                 pub rc: Option<i32>, pub wall_ms: u64, pub answers: Vec<Answer>, pub fence: Option<String>,
                 pub stderr_head: String, pub verdict: Verdict, pub oracle: Option<OracleAnswers> }
impl Fixture { pub fn to_json(&self) -> String; pub fn from_json(line: &str) -> Option<Fixture>; pub fn same_run(&self, other: &Fixture) -> bool /* sha, timeout, mem, jobs */ }
impl Row { pub fn to_json(&self) -> String; pub fn from_json(line: &str) -> Option<Row>; }
pub struct ResultsFile { /* path, File */ }
impl ResultsFile {
    /// Open or create; returns the fixture on disk (if any) and the set of recorded paths.
    pub fn open(path: &Path, fixture: &Fixture) -> Result<(ResultsFile, HashSet<String>), String>;
    pub fn append(&mut self, row: &Row) -> io::Result<()>;   // write + flush
}
pub fn read_all(path: &Path) -> io::Result<(Option<Fixture>, Vec<Row>)>; // skips unparsable lines, counts them
```

- [ ] **Step 1: Failing tests (`instance.rs`)**

```rust
    #[test] fn status_present() {
        assert_eq!(scan_status("(set-logic QF_BV)\n(set-info :status unsat)\n"), Some(Answer::Unsat));
        assert_eq!(scan_status("(set-info   :status   sat )"), Some(Answer::Sat));
        assert_eq!(scan_status("(set-info :status unknown)"), Some(Answer::Unknown));
    }
    #[test] fn status_absent_or_in_comment() {
        assert_eq!(scan_status("(set-logic QF_BV)\n(check-sat)\n"), None);
        assert_eq!(scan_status("; (set-info :status sat)\n(set-logic QF_BV)"), None);
    }
    #[test] fn status_after_check_sat_still_counts_and_crlf() {
        assert_eq!(scan_status("(check-sat)\r\n(set-info :status sat)\r\n"), Some(Answer::Sat));
    }
    #[test] fn walk_sorts_and_derives_logic_from_top_dir() {
        let dir = std::env::temp_dir().join(format!("shinri-bench-walk-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("QF_BV/b")).unwrap();
        std::fs::create_dir_all(dir.join("QF_LRA")).unwrap();
        std::fs::write(dir.join("QF_BV/b/y.smt2"), "(set-info :status sat)").unwrap();
        std::fs::write(dir.join("QF_BV/a.smt2"), "").unwrap();
        std::fs::write(dir.join("QF_BV/README"), "").unwrap();
        std::fs::write(dir.join("QF_LRA/z.smt2"), "").unwrap();
        let v = walk(&dir, &["QF_BV".into()]).unwrap();
        assert_eq!(v.iter().map(|i| i.rel_path.as_str()).collect::<Vec<_>>(), ["QF_BV/a.smt2", "QF_BV/b/y.smt2"]);
        assert_eq!(v[1].logic, "QF_BV");
        assert_eq!(v[1].status, Some(Answer::Sat));
        assert_eq!(v[1].bytes, 22);
        std::fs::remove_dir_all(dir).unwrap();
    }
```

- [ ] **Step 2: Implement `instance.rs`**

`scan_status`: strip comments line-by-line (`;` to end of line), then find `(set-info`, skip whitespace, expect `:status`, skip whitespace, read a token, `Answer::parse` it. Only the first match counts. `walk`: recursive `read_dir`, collect `.smt2` files, `logic` = first path component, read the first 64 KiB with `File::read` into a `String::from_utf8_lossy` for the scan, `bytes` from metadata. Sort by `rel_path`. Missing logic directory → `Err` with a message naming it (`fetch` first).

- [ ] **Step 3: Failing tests (`results.rs`)**

```rust
    fn fixture() -> Fixture { Fixture { sha: "abc".into(), version: "shinri 0.1.0".into(), timeout_s: 20, mem_mb: 3072, jobs: 6,
        cpu_max: "800000 100000".into(), memory_max: "34359738368".into(), corpus: "zenodo.11061097".into(), started: "2026-09-08T00:00:00Z".into() } }
    fn row() -> Row { Row { path: "QF_S/a \"q\"\n.smt2".into(), logic: "QF_S".into(), bytes: 7, status: None, rc: Some(0),
        wall_ms: 12, answers: vec![Answer::Sat], fence: None, stderr_head: "line1\nline2\\".into(),
        verdict: Verdict::Unverified, oracle: Some(OracleAnswers { z3: Some(Answer::Timeout), cvc5: None }) } }

    #[test] fn row_round_trips() { let r = row(); let back = Row::from_json(&r.to_json()).unwrap(); assert_eq!(back.path, r.path); assert_eq!(back.stderr_head, r.stderr_head); assert_eq!(back.verdict, r.verdict); assert_eq!(back.oracle, r.oracle); assert_eq!(back.answers, r.answers); }
    #[test] fn fixture_round_trips() { let f = fixture(); let back = Fixture::from_json(&f.to_json()).unwrap(); assert!(f.same_run(&back)); assert_eq!(back.started, f.started); }
    #[test] fn open_resumes_and_refuses_mismatch() {
        let p = std::env::temp_dir().join(format!("shinri-bench-res-{}.jsonl", std::process::id()));
        let _ = std::fs::remove_file(&p);
        let (mut f, seen) = ResultsFile::open(&p, &fixture()).unwrap();
        assert!(seen.is_empty());
        f.append(&row()).unwrap();
        drop(f);
        let (_, seen) = ResultsFile::open(&p, &fixture()).unwrap();
        assert!(seen.contains(&row().path));
        let mut other = fixture(); other.timeout_s = 60;
        assert!(ResultsFile::open(&p, &other).is_err());
        std::fs::remove_file(&p).unwrap();
    }
    #[test] fn read_all_skips_truncated_last_line() {
        let p = std::env::temp_dir().join(format!("shinri-bench-trunc-{}.jsonl", std::process::id()));
        std::fs::write(&p, format!("{}\n{}\n{{\"path\":\"cut", fixture().to_json(), row().to_json())).unwrap();
        let (fx, rows) = read_all(&p).unwrap();
        assert!(fx.is_some()); assert_eq!(rows.len(), 1);
        std::fs::remove_file(&p).unwrap();
    }
```

- [ ] **Step 4: Implement `results.rs`**

Serialise by hand with `json::escape`; the fixture line is `{"fixture":{...}}`. `from_json` uses `json::parse_object` and pulls fields by name (missing field → `None`). `open`: if the file exists, read the first line as fixture (`same_run` must hold, else `Err("results file was produced by a different fixture (sha/timeout/mem/jobs); use a new --run-id")`), collect `path` of each parsable row; open in append mode. If the file does not exist, create it and write the fixture line. `append`: `writeln!` + `flush`.

- [ ] **Step 5: Run, fmt, clippy, commit**

Run: `cargo nextest run -p shinri-bench` — expected: previous 22 + 8 new PASS.

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-bench
git commit -m "feat(bench): slice46 T4 - instance scan/walk and resumable JSONL results"
```

---

### Task 5: `archive.rs` — zstd stream + ustar extractor

**Files:**
- Create: `crates/shinri-bench/src/archive.rs`
- Modify: `crates/shinri-bench/src/main.rs` (`mod archive;`)

**Interfaces (produced):**

```rust
/// `Read` over a concatenation of zstd frames (zstd files may hold several).
pub struct ZstdStream<R: BufRead> { /* src, decoder: ruzstd::decoding::FrameDecoder, started: bool */ }
impl<R: BufRead> ZstdStream<R> { pub fn new(src: R) -> ZstdStream<R>; }
impl<R: BufRead> Read for ZstdStream<R>;
/// Extract a (possibly GNU-longname) ustar stream into `dest`; returns the number of regular files written.
/// Entries whose normalised path escapes `dest` (`..`, absolute) are rejected with an error.
pub fn extract_tar(mut tar: impl Read, dest: &Path) -> io::Result<usize>;
```

- [ ] **Step 1: Failing tests**

```rust
    use ruzstd::encoding::{compress_to_vec, CompressionLevel};

    /// Build a ustar archive in memory: (path, contents) pairs; dirs get typeflag '5'.
    fn tar_bytes(entries: &[(&str, Option<&[u8]>)]) -> Vec<u8> {
        let mut out = Vec::new();
        for (name, data) in entries {
            let mut h = [0u8; 512];
            let (prefix, base) = if name.len() > 100 { name.split_at(name.len() - 100) } else { ("", *name) };
            h[..base.len()].copy_from_slice(base.as_bytes());
            h[345..345 + prefix.len()].copy_from_slice(prefix.as_bytes());
            h[100..108].copy_from_slice(b"0000644\0");
            let size = data.map_or(0, |d| d.len());
            h[124..136].copy_from_slice(format!("{size:011o}\0").as_bytes());
            h[156] = if data.is_some() { b'0' } else { b'5' };
            h[257..263].copy_from_slice(b"ustar\0");
            h[263..265].copy_from_slice(b"00");
            h[148..156].copy_from_slice(b"        ");
            let sum: u32 = h.iter().map(|&b| b as u32).sum();
            h[148..156].copy_from_slice(format!("{sum:06o}\0 ").as_bytes());
            out.extend_from_slice(&h);
            if let Some(d) = data { out.extend_from_slice(d); out.resize(out.len() + (512 - d.len() % 512) % 512, 0); }
        }
        out.extend_from_slice(&[0u8; 1024]);
        out
    }

    #[test] fn zstd_stream_decodes_two_concatenated_frames() {
        let a = compress_to_vec(&b"hello "[..], CompressionLevel::Fastest);
        let b = compress_to_vec(&b"world"[..], CompressionLevel::Uncompressed);
        let mut joined = a; joined.extend(b);
        let mut out = Vec::new();
        ZstdStream::new(std::io::Cursor::new(joined)).read_to_end(&mut out).unwrap();
        assert_eq!(out, b"hello world");
    }
    #[test] fn extract_regular_files_dirs_and_prefix_names() {
        let long = format!("{}/x.smt2", "d".repeat(120));
        let tar = tar_bytes(&[("QF_X/", None), ("QF_X/a.smt2", Some(b"(check-sat)")), (long.as_str(), Some(b"z"))]);
        let dest = std::env::temp_dir().join(format!("shinri-bench-tar-{}", std::process::id()));
        let n = extract_tar(std::io::Cursor::new(tar), &dest).unwrap();
        assert_eq!(n, 2);
        assert_eq!(std::fs::read(dest.join("QF_X/a.smt2")).unwrap(), b"(check-sat)");
        assert_eq!(std::fs::read(dest.join(&long)).unwrap(), b"z");
        std::fs::remove_dir_all(dest).unwrap();
    }
    #[test] fn extract_rejects_path_escape() {
        let tar = tar_bytes(&[("../evil", Some(b"x"))]);
        let dest = std::env::temp_dir().join(format!("shinri-bench-esc-{}", std::process::id()));
        assert!(extract_tar(std::io::Cursor::new(tar), &dest).is_err());
        let _ = std::fs::remove_dir_all(dest);
    }
    #[test] fn extract_through_zstd() {
        let tar = tar_bytes(&[("L/f.smt2", Some(b"(set-info :status sat)"))]);
        let z = compress_to_vec(&tar[..], CompressionLevel::Fastest);
        let dest = std::env::temp_dir().join(format!("shinri-bench-tz-{}", std::process::id()));
        assert_eq!(extract_tar(ZstdStream::new(std::io::Cursor::new(z)), &dest).unwrap(), 1);
        std::fs::remove_dir_all(dest).unwrap();
    }
```

- [ ] **Step 2: Implement**

`ZstdStream::read`: loop — if `!started || decoder.is_finished() && decoder.can_collect() == 0`: `let buf = src.fill_buf()?; if buf.is_empty() { return Ok(0) }`; `decoder.init(&mut src)` (map `FrameDecoderError` to `io::Error::other`), `started = true`. If `decoder.can_collect() == 0 && !decoder.is_finished()`: `decoder.decode_blocks(&mut src, BlockDecodingStrategy::UptoBytes(1 << 20))`. Then `let n = decoder.read(out)?; if n > 0 { return Ok(n) }` and loop. (`FrameDecoder` implements `Read` over its output buffer; `init`/`decode_blocks` take `impl Read`, and `&mut R` satisfies that.)

`extract_tar`: read 512-byte headers; two zero blocks end the stream. Fields: name `[0..100]`, size octal `[124..136]` (parse up to first NUL/space; also accept base-256 if byte 124 has the high bit — not expected, error out), typeflag `[156]`, prefix `[345..500]`, GNU long name: typeflag `L` → the entry body is the next header's name. Typeflag `0`/`\0` → regular file: `create_dir_all(parent)`, stream `size` bytes with a 64 KiB buffer, skip padding. `5` → `create_dir_all`. Everything else (symlinks `2`, hard links `1`, pax `x`/`g`) → skip body. Path safety: reject any component `..`, absolute names, or empty after trimming `./`.

- [ ] **Step 3: Run, fmt, clippy, commit**

Run: `cargo nextest run -p shinri-bench -E 'test(archive)'` — expected: 4 PASS.

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-bench
git commit -m "feat(bench): slice46 T5 - multi-frame zstd reader and ustar extractor"
```

---

### Task 6: `corpus.rs` — manifest, fetch, verify, extract

**Files:**
- Create: `crates/shinri-bench/src/corpus.rs`, `bench/manifest.toml`
- Modify: `crates/shinri-bench/src/main.rs` (`mod corpus;`)

**Interfaces (produced):**

```rust
pub struct ArchiveSpec { pub logic: String, pub url: String, pub md5: String, pub size: u64, pub smt2_count: Option<u64> }
pub struct Manifest { pub record: String, pub archives: Vec<ArchiveSpec> }
pub fn parse_manifest(text: &str) -> Result<Manifest, String>;
pub fn load_manifest(path: &Path) -> Result<Manifest, String>;
/// `curl` → md5sum → extract → `.verified`. `mirror`: replace the URL's `https://zenodo.org/api/records/<id>/files/` prefix with `<mirror>/`.
pub fn fetch(manifest: &Manifest, logics: &[String], corpus_dir: &Path, mirror: Option<&str>, dry_run: bool) -> Result<(), String>;
pub fn md5_of(path: &Path) -> io::Result<String>;   // shells out to `md5sum`
```

- [ ] **Step 1: Write `bench/manifest.toml`**

Values below are the Zenodo file metadata read on 2026-09-08 (`GET https://zenodo.org/api/records/11061097`, `files[].checksum`, `files[].size`). `smt2_count` is intentionally absent until Task 10 records the counts from the first extraction.

```toml
# SMT-LIB release 2024 (non-incremental benchmarks), version 2024.04.23
# https://doi.org/10.5281/zenodo.11061097
# md5 is what Zenodo publishes for each file; `shinri-bench fetch` verifies it
# after download and refuses to extract a mismatch.
record = "10.5281/zenodo.11061097"
base_url = "https://zenodo.org/api/records/11061097/files/"

[[archive]]
logic = "QF_BV"
file = "QF_BV.tar.zst"
size = 1734941977
md5 = "3104e6a73841bccab5a2b0960afa8576"

[[archive]]
logic = "QF_ABV"
file = "QF_ABV.tar.zst"
size = 139559467
md5 = "1522a83775e718596fc86d4fa6bf7551"

[[archive]]
logic = "QF_AUFBV"
file = "QF_AUFBV.tar.zst"
size = 1184909
md5 = "83c6c9bf34bd38a078c389cecf7ed0a3"

[[archive]]
logic = "QF_UFBV"
file = "QF_UFBV.tar.zst"
size = 87797101
md5 = "50d22090ac82e882761f0648f109485f"

[[archive]]
logic = "QF_FP"
file = "QF_FP.tar.zst"
size = 7534342
md5 = "d690d40fb847d889ed3b69e34ce82382"

[[archive]]
logic = "QF_BVFP"
file = "QF_BVFP.tar.zst"
size = 1033258
md5 = "c9aa57f04510048611ad0ad027c8ef76"

[[archive]]
logic = "QF_LRA"
file = "QF_LRA.tar.zst"
size = 182105257
md5 = "acded5157ed73f2672d1421f205b7209"

[[archive]]
logic = "QF_LIA"
file = "QF_LIA.tar.zst"
size = 688955075
md5 = "d71191111a0d80d6558a8784058d081c"

[[archive]]
logic = "QF_UF"
file = "QF_UF.tar.zst"
size = 54287659
md5 = "3ce26e05264581931a583bae96b87f34"

[[archive]]
logic = "QF_UFLIA"
file = "QF_UFLIA.tar.zst"
size = 18901126
md5 = "26d8d7e71c33b10c9767beebddb5da9e"

[[archive]]
logic = "QF_UFLRA"
file = "QF_UFLRA.tar.zst"
size = 162815543
md5 = "efcc423fd0f50e9b7942779d02e376ed"

[[archive]]
logic = "QF_AX"
file = "QF_AX.tar.zst"
size = 131549
md5 = "6d323ea02eb4d74e8ac77420bf94e3cb"

[[archive]]
logic = "QF_S"
file = "QF_S.tar.zst"
size = 2909837
md5 = "e7a201b1fff6c952f278154d6513a0c0"

[[archive]]
logic = "QF_SLIA"
file = "QF_SLIA.tar.zst"
size = 31834010
md5 = "277e586bf556ee33dc638348bc6de50a"

[[archive]]
logic = "QF_DT"
file = "QF_DT.tar.zst"
size = 43959596
md5 = "34701f2c49bf4669a550ac8124b8cad0"
```

The URL for each archive is `base_url + file + "/content"`.

- [ ] **Step 2: Failing tests**

```rust
    const MINI: &str = "record = \"10.5281/zenodo.1\"\nbase_url = \"https://h/f/\"\n\n[[archive]]\nlogic = \"QF_AX\"\nfile = \"QF_AX.tar.zst\"\nsize = 10\nmd5 = \"6d323ea02eb4d74e8ac77420bf94e3cb\"\nsmt2_count = 551\n";

    #[test] fn parses_manifest() {
        let m = parse_manifest(MINI).unwrap();
        assert_eq!(m.record, "10.5281/zenodo.1");
        assert_eq!(m.archives.len(), 1);
        assert_eq!(m.archives[0].url, "https://h/f/QF_AX.tar.zst/content");
        assert_eq!(m.archives[0].smt2_count, Some(551));
    }
    #[test] fn rejects_missing_md5_and_unknown_key() {
        assert!(parse_manifest(&MINI.replace("md5 = \"6d323ea02eb4d74e8ac77420bf94e3cb\"\n", "")).is_err());
        assert!(parse_manifest(&format!("{MINI}sha1 = \"x\"\n")).is_err());
    }
    #[test] fn committed_manifest_parses_and_lists_every_scoped_logic() {
        let m = load_manifest(Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../../bench/manifest.toml"))).unwrap();
        for l in ["QF_BV","QF_ABV","QF_AUFBV","QF_UFBV","QF_FP","QF_BVFP","QF_LRA","QF_LIA","QF_UF","QF_UFLIA","QF_UFLRA","QF_AX","QF_S","QF_SLIA","QF_DT"] {
            assert!(m.archives.iter().any(|a| a.logic == l), "missing {l}");
        }
        for a in &m.archives { assert_eq!(a.md5.len(), 32); assert!(a.md5.bytes().all(|b| b.is_ascii_hexdigit())); }
    }
    #[test] fn md5_of_matches_coreutils_vector() {
        let p = std::env::temp_dir().join(format!("shinri-bench-md5-{}", std::process::id()));
        std::fs::write(&p, b"abc").unwrap();
        assert_eq!(md5_of(&p).unwrap(), "900150983cd24fb0d6963f7d28e17f72");
        std::fs::remove_file(p).unwrap();
    }
    #[test] fn dry_run_prints_urls_and_touches_nothing() {
        let m = parse_manifest(MINI).unwrap();
        let dir = std::env::temp_dir().join(format!("shinri-bench-dry-{}", std::process::id()));
        fetch(&m, &["QF_AX".into()], &dir, None, true).unwrap();
        assert!(!dir.exists());
        fetch(&m, &["QF_NOPE".into()], &dir, None, true).unwrap_err();
    }
    #[test] fn mirror_rewrites_prefix() {
        assert_eq!(mirror_url("https://zenodo.org/api/records/11061097/files/QF_AX.tar.zst/content", "https://zenodo.org/api/records/11061097/files/", "/mnt/mirror"), "/mnt/mirror/QF_AX.tar.zst/content");
    }
```

- [ ] **Step 3: Implement**

Manifest reader: line-oriented — `key = "string"` / `key = 123`, `[[archive]]` starts a new table; top-level keys `record`, `base_url`; archive keys `logic`, `file`, `size`, `md5`, `smt2_count`; anything else → `Err`. Every archive needs `logic`, `file`, `size`, `md5`.

`fetch`, per selected archive (unknown logic → `Err`): 
1. `let verified = corpus_dir/<logic>/.verified`; if it exists and its content equals `md5`, skip with a "already verified" line.
2. Dry run: print the URL and continue.
3. `curl -L --fail --retry 5 --retry-all-errors -C - -o <corpus>/.dl/<file> <url>` (`-C -` resumes; a `curl` exit ≠ 0 → record the error, continue).
4. `md5_of` (`md5sum <path>`, first 32 chars of stdout). Mismatch → rename to `<file>.bad`, record error, continue.
5. Extract: `BufReader::new(File)` → `ZstdStream` → `extract_tar(…, corpus_dir)` (the archive's top-level directory is the logic name, matching `walk`). If the extracted top dir is not `<logic>`, error. Count `.smt2` files under `<corpus>/<logic>`; if `smt2_count` is `Some(n)` and differs → error; print the count either way (Task 10 records it).
6. Write `.verified` with the md5.
7. After all archives: if any error was recorded, print them and return `Err`.

Mirror: `mirror_url(url, base_url, mirror)` replaces the `base_url` prefix with `<mirror>/`; a `file://`-less local path is fine — `curl` accepts `file:///…`, so prefix `file://` when `mirror` starts with `/`.

- [ ] **Step 4: Run, fmt, clippy, commit**

Run: `cargo nextest run -p shinri-bench -E 'test(corpus)'` — expected: 6 PASS.

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-bench bench/manifest.toml
git commit -m "feat(bench): slice46 T6 - pinned Zenodo manifest, resumable checksummed fetch"
```

---

### Task 7: `process.rs`, `oracle.rs`, `runner.rs`

**Files:**
- Create: `crates/shinri-bench/src/process.rs`, `src/oracle.rs`, `src/runner.rs`
- Create: `crates/shinri-bench/tests/runner_e2e.rs`, `tests/corpus/stub-solver.sh`, `tests/corpus/QF_T/{sat,unsat,lies,slow,hog,crash}.smt2`
- Modify: `crates/shinri-bench/src/main.rs` (`mod`s)

**Interfaces (produced):**

```rust
// process.rs
pub struct Limits { pub timeout_s: u64, pub mem_mb: u64 }
pub struct Exec { pub rc: Option<i32>, pub stdout: String, pub stderr: String, pub wall_ms: u64, pub killed_by_timeout: bool, pub spawn_error: Option<String> }
/// `prlimit --as=<mem> timeout -s KILL <t+1> timeout <t> <program> <args…>`; stdin closed; both pipes drained on threads.
pub fn run_limited(program: &str, args: &[&str], limits: &Limits) -> Exec;
pub fn tools_available() -> Result<(), String>;   // prlimit, timeout on PATH

// oracle.rs
pub struct Oracle { pub z3: String, pub cvc5: String }   // program names, default "z3"/"cvc5"
impl Oracle { pub fn z3(&self, path: &Path, limits: &Limits) -> Answer; pub fn cvc5(&self, path: &Path, limits: &Limits) -> Answer; }
// cvc5 is invoked with `--lang smt2`; both parse the LAST sat/unsat/unknown line of stdout; timeout → Answer::Timeout.

// runner.rs
pub struct RunConfig { pub solver: String, pub solver_args: Vec<String>, pub limits: Limits, pub jobs: usize, pub oracle: Oracle }
pub fn run_one(inst: &Instance, cfg: &RunConfig) -> Row;
pub fn run_all(instances: Vec<Instance>, cfg: &RunConfig, results: &mut ResultsFile, skip: &HashSet<String>, progress: &mut dyn FnMut(usize, usize, &Verdict)) -> io::Result<()>;
pub fn parse_stats_fence(stderr: &str) -> Option<String>;     // last `stats:` line's `fence=` (None if `-`)
pub fn strip_stats(stderr: &str, max: usize) -> String;         // stderr_head: minus stats lines, first `max` bytes at a char boundary
pub fn parse_answers(stdout: &str) -> (Vec<Answer>, usize);      // (answers in order, `(error` lines before the first answer)
```

- [ ] **Step 1: Fixtures**

`tests/corpus/stub-solver.sh` (mode 755):

```sh
#!/bin/sh
# Stub solver for runner_e2e: behaviour is chosen by the input's basename.
f="$1"; shift
[ "$f" = "--stats" ] && { f="$1"; shift; }
case "$(basename "$f")" in
  sat.smt2)   echo sat;   echo "stats: cmd=check-sat wall_ms=1 outcome=sat fence=-" >&2 ;;
  unsat.smt2) echo unsat; echo "stats: cmd=check-sat wall_ms=1 outcome=unsat fence=-" >&2 ;;
  lies.smt2)  echo sat ;;
  slow.smt2)  sleep 30; echo sat ;;
  hog.smt2)   echo "memory allocation of 4000000000 bytes failed" >&2; kill -ABRT $$ ;;
  crash.smt2) echo "thread 'main' panicked at src/lib.rs:1:1:" >&2; exit 101 ;;
  *)          echo "(error \"unknown symbol zzz\")" ;;
esac
```

(`hog` fakes the abort rather than allocating — the classification path is what is under test; the real `prlimit` behaviour is exercised in Task 10.) Files under `tests/corpus/QF_T/`: `sat.smt2` = `(set-info :status sat)`, `unsat.smt2` = `(set-info :status unsat)`, `lies.smt2` = `(set-info :status unsat)`, `slow.smt2` = `(set-info :status sat)`, `hog.smt2` and `crash.smt2` = `(set-info :status sat)`.

- [ ] **Step 2: Failing unit tests (`runner.rs`)**

```rust
    #[test] fn answers_and_error_count() {
        assert_eq!(parse_answers("success\n(error \"x\")\nunsat\n"), (vec![Answer::Unsat], 1));
        assert_eq!(parse_answers("sat\n(error \"after\")\n"), (vec![Answer::Sat], 0));
        assert_eq!(parse_answers("(define-fun x () Int 3)\n"), (vec![], 0));
    }
    #[test] fn fence_from_last_stats_line() {
        assert_eq!(parse_stats_fence("stats: cmd=check-sat wall_ms=3 outcome=unknown fence=str-order\n"), Some("str-order".into()));
        assert_eq!(parse_stats_fence("stats: cmd=check-sat wall_ms=3 outcome=sat fence=-\n"), None);
        assert_eq!(parse_stats_fence("junk\n"), None);
    }
    #[test] fn stderr_head_drops_stats_and_truncates_on_char_boundary() {
        let s = "stats: cmd=check-sat wall_ms=1 outcome=sat fence=-\nerr é line\n";
        assert_eq!(strip_stats(s, 100), "err é line\n");
        assert_eq!(strip_stats(s, 5), "err \u{e9}");
    }
```

- [ ] **Step 3: Failing e2e test (`tests/runner_e2e.rs`)**

```rust
//! The runner end-to-end over a six-file mini-corpus and a stub solver.
use std::collections::HashSet;
use std::path::{Path, PathBuf};

fn fixture(name: &str) -> PathBuf { Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus").join(name) }

#[test]
fn six_verdicts_from_the_stub_solver() {
    if shinri_bench_test_support::tools_missing() { eprintln!("skipping: prlimit/timeout not on PATH"); return; }
    // ... see Step 4 for the support shim
}
```

Since the crate is a binary, integration tests cannot `use` its modules. Make it a lib+bin: move all `mod`s into `src/lib.rs` (`pub mod …`) and have `main.rs` do `use shinri_bench::*`. Then the test is:

```rust
use shinri_bench::instance::walk;
use shinri_bench::oracle::Oracle;
use shinri_bench::process::{tools_available, Limits};
use shinri_bench::results::{read_all, Fixture, ResultsFile};
use shinri_bench::runner::{run_all, RunConfig};
use shinri_bench::verdict::Verdict;

#[test]
fn six_verdicts_from_the_stub_solver() {
    if let Err(e) = tools_available() { eprintln!("skipping: {e}"); return; }
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let stub = corpus.join("stub-solver.sh");
    let insts = walk(&corpus, &["QF_T".into()]).unwrap();
    assert_eq!(insts.len(), 6);
    let out = std::env::temp_dir().join(format!("shinri-bench-e2e-{}.jsonl", std::process::id()));
    let _ = std::fs::remove_file(&out);
    let fx = Fixture { sha: "test".into(), version: "stub".into(), timeout_s: 2, mem_mb: 512, jobs: 3,
        cpu_max: "-".into(), memory_max: "-".into(), corpus: "mini".into(), started: "now".into() };
    let (mut rf, skip) = ResultsFile::open(&out, &fx).unwrap();
    let cfg = RunConfig {
        solver: stub.to_string_lossy().into_owned(), solver_args: vec!["--stats".into()],
        limits: Limits { timeout_s: 2, mem_mb: 512 }, jobs: 3,
        // The stub is also the oracle: `lies.smt2` gets `sat` from "z3" and "cvc5", so with :status unsat it lands on StatusSuspect.
        oracle: Oracle { z3: stub.to_string_lossy().into_owned(), cvc5: stub.to_string_lossy().into_owned() },
    };
    let t0 = std::time::Instant::now();
    run_all(insts, &cfg, &mut rf, &skip, &mut |_, _, _| {}).unwrap();
    assert!(t0.elapsed().as_secs() < 8, "pool did not overlap or kill: {:?}", t0.elapsed());
    let (_, rows) = read_all(&out).unwrap();
    let by: std::collections::HashMap<_, _> = rows.iter().map(|r| (r.path.clone(), r.verdict.clone())).collect();
    assert_eq!(by["QF_T/sat.smt2"], Verdict::Correct);
    assert_eq!(by["QF_T/unsat.smt2"], Verdict::Correct);
    assert_eq!(by["QF_T/lies.smt2"], Verdict::StatusSuspect);
    assert_eq!(by["QF_T/slow.smt2"], Verdict::Timeout);
    assert_eq!(by["QF_T/hog.smt2"], Verdict::Oom);
    assert_eq!(by["QF_T/crash.smt2"], Verdict::Panic);
    let lies = rows.iter().find(|r| r.path == "QF_T/lies.smt2").unwrap();
    assert_eq!(lies.oracle.as_ref().unwrap().z3, Some(shinri_bench::verdict::Answer::Sat));
    // Resume: a second open reports all six as done.
    let (_, seen) = ResultsFile::open(&out, &fx).unwrap();
    assert_eq!(seen.len(), 6);
    let _ = HashSet::<String>::new();
    std::fs::remove_file(out).unwrap();
}
```

- [ ] **Step 4: Implement**

`process::run_limited`: `Command::new("prlimit").arg(format!("--as={}", mem_mb * 1024 * 1024)).arg("timeout").arg("-s").arg("KILL").arg((t+1).to_string()).arg("timeout").arg(t.to_string()).arg(program).args(args)`, `stdin(Stdio::null())`, both pipes `piped()`; spawn two threads that `read_to_end` each pipe; `wait`; `String::from_utf8_lossy`. `rc = status.code()`; `killed_by_timeout = rc == Some(124) || (rc == Some(137) && wall >= t*1000) || (rc.is_none() && wall >= t*1000)`. `tools_available`: `Command::new("prlimit").arg("--version")` and `timeout --version` both succeed.

`oracle`: `run_limited(&self.z3, &[path], limits)`; if `killed_by_timeout` → `Timeout`; else last line of stdout that parses as an `Answer`, default `Unknown`. cvc5 args: `["--lang", "smt2", path]`.

`runner::run_one`: if the instance file cannot be opened, or `run_limited` cannot spawn (`prlimit`/solver missing — `Exec` carries `spawn_error: Option<String>`), return a `Row` with `verdict: Malformed("spawn: <reason>")` / `Malformed("unreadable: <reason>")`, `rc: None`, `wall_ms: 0` — a worker never aborts the run. Otherwise `run_limited(cfg.solver, [solver_args…, abs_path])` → `parse_answers`, `parse_stats_fence`, `strip_stats(…, 2048)` → `classify`; if `NeedsOracle`: `z3`, classify again; if still `NeedsOracle`: `cvc5`, classify again (never `NeedsOracle` after both). Build `Row`.

`runner::run_all`: filter `skip`; `total`; a `Mutex<VecDeque<Instance>>` work queue; `jobs` scoped threads (`std::thread::scope`) each popping and sending `Row`s over an `mpsc` channel; the main thread receives, appends, and calls `progress(done, total, &verdict)`. Errors from `append` abort the run with the error (rows already written stay valid).

- [ ] **Step 5: Run, fmt, clippy, commit**

Run: `cargo nextest run -p shinri-bench` — expected: previous + 3 unit + 1 e2e PASS, e2e under 8 s.

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-bench
git commit -m "feat(bench): slice46 T7 - limited process runner, on-demand oracle, worker pool"
```

---

### Task 8: `report.rs`

**Files:**
- Create: `crates/shinri-bench/src/report.rs`, `tests/fixtures/report_rows.jsonl`, `tests/fixtures/report_golden.md`, `tests/report_golden.rs`

**Interfaces (produced):**

```rust
pub fn normalise_diag(line: &str) -> String;   // digits runs → N, `"..."`/`|...|` → S, trailing whitespace trimmed
pub fn render(fixture: Option<&Fixture>, rows: &[Row]) -> String;   // the full Markdown report
```

- [ ] **Step 1: Failing unit tests**

```rust
    #[test] fn diag_normalisation_merges_symbol_and_number_variants() {
        assert_eq!(normalise_diag("(error \"unknown symbol foo\")"), normalise_diag("(error \"unknown symbol bar\")"));
        assert_eq!(normalise_diag("line 12: unexpected token |x|"), "line N: unexpected token S");
    }
    #[test] fn render_handles_no_correct_rows() {
        let r = Row { path: "QF_X/a.smt2".into(), logic: "QF_X".into(), bytes: 1, status: None, rc: Some(124), wall_ms: 20000,
            answers: vec![], fence: None, stderr_head: String::new(), verdict: Verdict::Timeout, oracle: None };
        let md = render(None, &[r]);
        assert!(md.contains("| QF_X |"));
        assert!(md.contains("n/a"));
    }
    #[test] fn ranking_is_stable_under_permutation() {
        let (_, mut rows) = read_all(Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/report_rows.jsonl"))).unwrap();
        let a = render(None, &rows);
        rows.reverse();
        assert_eq!(a, render(None, &rows));
    }
```

`tests/report_golden.rs`:

```rust
use shinri_bench::report::render;
use shinri_bench::results::read_all;
use std::path::Path;

#[test]
fn report_matches_golden() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let (fx, rows) = read_all(&dir.join("report_rows.jsonl")).unwrap();
    let got = render(fx.as_ref(), &rows);
    let want = std::fs::read_to_string(dir.join("report_golden.md")).unwrap();
    if std::env::var_os("UPDATE_GOLDEN").is_some() { std::fs::write(dir.join("report_golden.md"), &got).unwrap(); return; }
    assert_eq!(got, want, "run with UPDATE_GOLDEN=1 to regenerate after an intentional change");
}
```

- [ ] **Step 2: Write `report_rows.jsonl`**

A fixture line plus 30 rows written by hand with `Row::to_json` semantics: 3 logics (`QF_BV`, `QF_S`, `QF_LRA`); at least one row of every verdict (`correct` ×12 with varied `wall_ms`, `wrong` ×1 with oracle, `status-suspect` ×1, `parse-error` ×3 sharing a normalised diagnostic and 1 different, `panic` ×1, `oom` ×1, `timeout` ×4 across two size deciles, `unknown:str-order` ×3, `unknown:bv-uf-budget` ×1, `unverified` ×1, `malformed:answers=2` ×1). Easiest: write a throwaway `#[test] #[ignore]` that constructs the rows and prints them, run once, paste; delete the helper before committing.

- [ ] **Step 3: Implement `render`** — sections exactly as spec §6:

1. `# shinri-bench report` + fixture table (or "no fixture line").
2. `## Per-logic matrix`: header `| logic | total | correct | wrong | status-suspect | parse-error | panic | oom | timeout | unknown | unverified | malformed | decided% | median ms | p90 ms |`; logics sorted; `decided% = correct*100/(total-malformed)` with one decimal; median/p90 over `correct` rows (`n/a` if none). A final `all` row.
3. `## Ranked gaps`: buckets = `unknown:<tag>`, `parse-error:<normalised first line of stderr_head or the first `(error` line>`, `panic:<normalised first panicked-at line>`, `timeout`, `oom`, `unverified`; sort by count desc then key asc; each bucket: `### <key> — <count>`, per-logic counts on one line, then up to 3 example paths (smallest `bytes` first, ties by path).
4. `## Wrong answers`: table `| path | :status | shinri | z3 | cvc5 |` over `wrong` then `status-suspect` (sorted by path); "_none_" if empty.
5. `## Perf tail`: `timeout+oom` by logic; by size decile (deciles over ALL rows' `bytes`, 10 equal-count bins; print the byte range of each bin and its timeout+oom count); then per logic the 20 slowest `correct` rows `| path | wall_ms | bytes |`.

Everything deterministic: sort keys are explicit, no HashMap iteration reaches the output.

- [ ] **Step 4: Generate the golden, run, fmt, clippy, commit**

Run: `UPDATE_GOLDEN=1 cargo nextest run -p shinri-bench -E 'test(report_matches_golden)'`, read `report_golden.md` by eye (every section present, numbers sane, `n/a` where a logic has no correct rows), then `cargo nextest run -p shinri-bench` — expected: all PASS.

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/shinri-bench
git commit -m "feat(bench): slice46 T8 - Markdown report with ranked gaps and perf tail"
```

---

### Task 9: `main.rs` wiring, mise tasks, README

**Files:**
- Modify: `crates/shinri-bench/src/main.rs`, `mise.toml`, `README.md`, `AGENTS.md`

**Interfaces (consumed):** every `pub fn` above.

- [ ] **Step 1: Failing test** — in `main.rs` a `#[cfg(test)]` over the arg parser:

```rust
    #[test] fn run_args_have_documented_defaults() {
        let a = parse_run_args(&["--logics".into(), "QF_AX,QF_S".into()]).unwrap();
        assert_eq!((a.timeout_s, a.mem_mb, a.jobs), (20, 3072, 6));
        assert_eq!(a.logics, vec!["QF_AX", "QF_S"]);
        assert!(a.run_id.len() >= 15); // YYYYMMDDTHHMMSSZ
    }
    #[test] fn rerun_requires_verdicts() {
        assert!(parse_rerun_args(&["bench/results/x/results.jsonl".into()]).is_err());
    }
```

- [ ] **Step 2: Implement**

Subcommands and flags (hand-rolled parsing, mirror `shinri-cli/src/args.rs` style):

- `fetch [--logics A,B] [--mirror URL|DIR] [--dry-run] [--manifest PATH] [--corpus DIR]`
- `run [--logics A,B] [--timeout S] [--mem-mb M] [--jobs N] [--run-id ID] [--solver PATH] [--corpus DIR] [--results DIR]`
  - solver default: `target/release/shinri` if it exists, else `shinri` on PATH; always passes `--stats`.
  - fixture: `git rev-parse --short=12 HEAD` (fallback `-`), `<solver> --version`, `/sys/fs/cgroup/cpu.max` and `memory.max` (fallback `-`), `corpus = manifest.record`, `started` = UTC `YYYY-MM-DDTHH:MM:SSZ` computed from `SystemTime` (civil-from-days conversion, ~20 lines; no chrono).
  - default run-id `YYYYMMDDTHHMMSSZ`. Results at `<results>/<run-id>/results.jsonl`.
  - progress: every 50 rows and at the end, one line `done/total  correct=… wrong=… unknown=… timeout=… …` to stderr.
- `rerun <results.jsonl> --verdict v1,v2 [--timeout S] [--mem-mb M] [--jobs N] [--run-id ID]` — matches on `Verdict::key()` prefix (`unknown` matches every `unknown:*`), reconstructs `Instance`s from the row paths under the same corpus dir, runs into a new run-id.
- `report <run-dir>` → writes `<run-dir>/report.md` and prints its path.
- Every parse error prints usage and exits 2; every runtime error prints `error: …` and exits 1.

`mise.toml`:

```toml
[tasks.bench-fetch]
description = "Download + verify + extract the pinned SMT-LIB 2024 archives into bench/corpus (BENCH_LOGICS=A,B to subset; BENCH_MIRROR for a local mirror)"
run = "cargo run --release -p shinri-bench -- fetch ${BENCH_LOGICS:+--logics $BENCH_LOGICS} ${BENCH_MIRROR:+--mirror $BENCH_MIRROR}"

[tasks.bench-run]
description = "Run shinri over bench/corpus under limits (BENCH_LOGICS, BENCH_TIMEOUT=20, BENCH_MEM_MB=3072, BENCH_JOBS=6, BENCH_RUN_ID)"
run = [
  "cargo build --release -p shinri-cli -p shinri-bench",
  "target/release/shinri-bench run ${BENCH_LOGICS:+--logics $BENCH_LOGICS} --timeout ${BENCH_TIMEOUT:-20} --mem-mb ${BENCH_MEM_MB:-3072} --jobs ${BENCH_JOBS:-6} ${BENCH_RUN_ID:+--run-id $BENCH_RUN_ID}",
]

[tasks.bench-report]
description = "Render bench/results/$BENCH_RUN_ID/report.md"
run = "cargo run --release -p shinri-bench -- report bench/results/$BENCH_RUN_ID"
```

(`shell = "bash -c"` on each, as `fuzz-smoke` does, so `${VAR:+…}` expands.) README task table: three rows. AGENTS.md: one bullet under "Test-tier rules": "`bench-*` tasks are manual (never in `ci`); the corpus lives in git-ignored `bench/corpus/`; the baseline report is in `docs/superpowers/research/`."

- [ ] **Step 3: Smoke it by hand**

```bash
cargo build --release -p shinri-cli -p shinri-bench
target/release/shinri-bench fetch --dry-run
BENCH_LOGICS=QF_AX mise run bench-fetch          # 131 KB — real network
BENCH_LOGICS=QF_AX BENCH_RUN_ID=smoke mise run bench-run
BENCH_RUN_ID=smoke mise run bench-report && head -40 bench/results/smoke/report.md
```

Expected: fetch prints the md5 match and the `.smt2` count; run prints progress and finishes; the report has a `QF_AX` row. Fix whatever breaks before committing.

- [ ] **Step 4: Run, fmt, clippy, commit**

Run: `cargo nextest run -p shinri-bench` and `mise run lint`.

```bash
git add crates/shinri-bench mise.toml README.md AGENTS.md
git commit -m "feat(bench): slice46 T9 - subcommands, mise bench-* tasks, docs"
```

---

### Task 10: The baseline run and the research doc

**Files:**
- Modify: `bench/manifest.toml` (record `smt2_count` per logic)
- Create: `docs/superpowers/research/<run-date>-smtlib-2024-baseline.md`

This task is manual/operational; it runs in the background over days and is checked on between other work. The full corpus is ~3.1 GB compressed.

- [ ] **Step 1: Fetch everything**

`mise run bench-fetch` (resumable; re-run on any network failure). Record the printed `.smt2` count for every logic as `smt2_count = N` in `bench/manifest.toml`; commit: `git commit -am "chore(bench): slice46 T10 - record extracted .smt2 counts in the manifest"`.

- [ ] **Step 2: Run per logic, smallest first, in the background**

```bash
BENCH_RUN_ID=baseline-$(git rev-parse --short=12 HEAD) nohup mise run bench-run > bench/results/run.log 2>&1 &
```

Check with `tail -3 bench/results/run.log`. If the pod restarts, the same command resumes. Expected total: ~150k instances; at 6 workers and a 20 s cap the worst case is ~6 days, realistic 1–2 days since most decided instances take milliseconds.

- [ ] **Step 3: Verify the `Oom` path once for real**

Before trusting the perf numbers, confirm `prlimit --as` actually produces the `memory allocation of … failed` signature on this box: `prlimit --as=$((64*1024*1024)) target/release/shinri --stats bench/corpus/QF_BV/<a large file>.smt2; echo rc=$?` — expected stderr containing `memory allocation of` and rc 134. If instead the process is killed with rc 137 or the allocator behaves differently, adjust `classify`'s `Oom` rule and its unit test to match the observed signature and note it in the research doc.

- [ ] **Step 4: Report**

`BENCH_RUN_ID=<id> mise run bench-report`. Copy `report.md` to `docs/superpowers/research/<today>-smtlib-2024-baseline.md` and prepend:

```markdown
# SMT-LIB 2024 baseline — shinri @ <sha>

Run-id `<id>`, `mise run bench-run` with timeout 20 s / 3072 MB / 6 jobs on the
devpod (cgroup cpu.max 800000/100000, memory.max 32 GiB). Reproduce with the
same sha and `bench/manifest.toml`.

## Next slices (spec §5 priority order)

1. **<verdict/bucket>** — <count> instances in <logics>; cites `## Ranked gaps › <key>`; proposed slice: <one line>.
2. …
```

Every `Wrong` row must be reproduced by hand (`z3 <path>`; `cvc5 --lang smt2 <path>`; `target/release/shinri <path>`) and listed with its reproduction before the doc is committed. If there are none, say so under a `## Wrong answers` heading.

- [ ] **Step 5: Commit and open the PR**

```bash
git add docs/superpowers/research/ bench/manifest.toml
git commit -m "docs(bench): slice46 T10 - SMT-LIB 2024 baseline report and ranked next slices"
```

Then follow `superpowers:finishing-a-development-branch`: PR to `main`, merge on green with a merge commit, delete the branch.

---

## Self-review

**Spec coverage.** §3 layout → T3–T9 (`json.rs`, `process.rs`, `archive.rs` are finer splits than the spec's file list; same responsibilities). §3.1 → T1, T2. §4.1 fetch → T6 (md5/`ruzstd` amendments recorded in the header and T1 step 5 / T6). §4.2 run → T7, T9. §4.3 rerun → T9. §4.4 schema → T4. §5 → T3 (`classify`), T7 (oracle rule). §6 → T8; §6.1 → T10. §7 tests → T1 (`fence_tags`), T2 (`cli.rs`), T3–T8 unit + golden + e2e. §8 error handling → T6 (`.bad`, continue-then-fail), T4 (fixture refuse, truncated line), T7 (worker never aborts — `run_one` builds a `Malformed` row on spawn failure; add that branch), T8 (`n/a`). §9 → T10.

**Type consistency.** `Answer`/`Verdict`/`OracleAnswers`/`Observed` (T3) are used unchanged in T4 `Row`, T7 `run_one`, T8 `render`. `Instance` (T4) is consumed by T7 `run_one`/`run_all` and T9 `rerun`. `Limits`/`Exec` (T7) are used by `oracle.rs` in the same task. `Fixture::same_run` compares sha/timeout/mem/jobs, matching spec §4.2 step 2.

**Placeholders.** None: every step carries code or an exact command; the only deferred values are `smt2_count` (recorded from the first extraction, by design) and the baseline's findings (produced by the run).
