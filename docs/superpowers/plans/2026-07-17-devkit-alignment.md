# Devkit Alignment Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bring blocking CI from ~55 min to ~8–10 min by tiering five exhaustive `shinri-fp` tests to nightly, single-source the toolchain through mise, add a repo front door, and add proportionate security scanning.

**Architecture:** `#[ignore]` moves the slow tests to the nightly `differential` job (`--run-ignored all`); `mise.toml` becomes the single pinned source of tools **and** task definitions that both CI and local dev invoke (`mise run <task>`); README/AGENTS.md/CLAUDE.md form a single-sourced front door.

**Tech Stack:** Rust workspace (15 crates), cargo-nextest 0.9.140, mise (jdx/mise-action@v2 in CI), cargo-deny, gitleaks, cargo-fuzz.

**Spec:** `docs/superpowers/specs/2026-07-17-devkit-alignment-design.md`

## Global Constraints

- Blocking CI tier budget: 10–15 min wall-clock; job `timeout-minutes: 20`.
- Tiering threshold: any test measured >5 min goes to the nightly tier via `#[ignore = "..."]` with the measured time in the reason string.
- Exactly five tests move (listed in Task 1). Do not `#[ignore]` anything else.
- `mise.toml` is the only source of tool pins. After Task 3, `.github/workflows/ci.yml` must contain no `dtolnay/rust-toolchain` and no `taiki-e/install-action`.
- `Cargo.toml` `rust-version = "1.96.0"` (MSRV floor) is unchanged; the CI toolchain follows the mise pin (1.97.1).
- CI steps invoke `mise run <task>`; never duplicate a task's command line in ci.yml.
- All work on branch `devkit-alignment`, PR to `main`, merge commit on green (repo standing workflow).

---

### Task 1: Tier the five exhaustive shinri-fp tests to nightly via `#[ignore]`

**Files:**
- Modify: `crates/shinri-fp/src/blast/div.rs:183`
- Modify: `crates/shinri-fp/src/blast/mul.rs:196`
- Modify: `crates/shinri-fp/src/blast/add.rs:294`
- Modify: `crates/shinri-fp/src/convert.rs:478`
- Modify: `crates/shinri-fp/src/blast/rem.rs:222`

**Interfaces:**
- Produces: five `#[ignore]`d tests that Task 3's nightly `mise run test-full` step (i.e. `cargo nextest run --all --run-ignored all`) picks up.

- [ ] **Step 1: Create the working branch**

```bash
git checkout -b devkit-alignment
```

- [ ] **Step 2: Add the ignore attributes**

Each edit inserts one `#[ignore = ...]` line directly under the existing `#[test]` attribute of the named function. Reason strings carry the CI-measured runtime (run 29612760341).

`crates/shinri-fp/src/blast/div.rs` (fn `fp_div_tiny_exhaustive_all_modes`, line 183):

```rust
    #[test]
    #[ignore = "exhaustive: nightly tier (~54 min in CI)"]
    fn fp_div_tiny_exhaustive_all_modes() {
```

`crates/shinri-fp/src/blast/mul.rs` (fn `fp_mul_tiny_exhaustive_all_modes`, line 196):

```rust
    #[test]
    #[ignore = "exhaustive: nightly tier (~36 min in CI)"]
    fn fp_mul_tiny_exhaustive_all_modes() {
```

`crates/shinri-fp/src/blast/add.rs` (fn `fp_add_tiny_exhaustive_all_modes`, line 294):

```rust
    #[test]
    #[ignore = "exhaustive: nightly tier (~33 min in CI)"]
    fn fp_add_tiny_exhaustive_all_modes() {
```

`crates/shinri-fp/src/convert.rs` (fn `to_fp_fp_tiny_exhaustive_both_directions`, line 478):

```rust
    #[test]
    #[ignore = "exhaustive: nightly tier (~18 min in CI)"]
    fn to_fp_fp_tiny_exhaustive_both_directions() {
```

`crates/shinri-fp/src/blast/rem.rs` (fn `rem_tiny_exhaustive`, line 222):

```rust
    #[test]
    #[ignore = "exhaustive: nightly tier (~13 min in CI)"]
    fn rem_tiny_exhaustive() {
```

- [ ] **Step 3: Verify exactly those five tests are now skipped**

The substring `tiny_exhaustive` matches exactly the five tests (`rem_tiny_exhaustive` included; `to_fp_int_8bit_exhaustive_both_faces` and `fp_fma_tiny_sampled_all_modes` are not matched).

Run: `cargo nextest run -p shinri-fp -E 'test(tiny_exhaustive)'`
Expected: `0 tests run` ... `5 skipped` (completes in seconds — nothing executes).

- [ ] **Step 4: Verify the fast tier of shinri-fp still passes**

Run: `cargo nextest run -p shinri-fp`
Expected: PASS, summary ends `... passed, 5 skipped`; wall-clock ~6 min (longest remaining test `rem_float32_specials_and_random` ≈ 5.3 min).

- [ ] **Step 5: fmt check and commit**

```bash
cargo fmt --all --check
git add crates/shinri-fp/src/blast/div.rs crates/shinri-fp/src/blast/mul.rs \
        crates/shinri-fp/src/blast/add.rs crates/shinri-fp/src/convert.rs \
        crates/shinri-fp/src/blast/rem.rs
git commit -m "test(fp): tier the five >5min exhaustive suites to nightly via #[ignore]"
```

---

### Task 2: mise.toml — gitleaks pin + named tasks (lint/deny/secrets/test/test-full/fuzz-smoke/ci)

**Files:**
- Modify: `mise.toml` (full replacement below)

**Interfaces:**
- Consumes: the `#[ignore]`d tests from Task 1 (`test` skips them; `test-full` runs them).
- Produces: task names `lint`, `deny`, `secrets`, `test`, `test-full`, `fuzz-smoke`, `ci` — invoked verbatim by Task 3's ci.yml and referenced by Task 4's docs. `fuzz-smoke` honors env `FUZZ_SECONDS` (default 60).

- [ ] **Step 1: Replace mise.toml with:**

```toml
[tools]
rust = "1.97.1"
"cargo:cargo-nextest" = "0.9.140"
"cargo:cargo-deny" = "0.20.2"
"cargo:cargo-fuzz" = "0.13.2"
"cargo:cargo-mutants" = "27.1.0"
gitleaks = "8.30.1"
"github:Z3Prover/z3" = { version = "z3-4.16.0", exe = "z3", matching = "x64-glibc" }
"github:cvc5/cvc5" = { version = "cvc5-1.3.4", exe = "cvc5", matching = "x86_64-static.zip" }

[tasks.lint]
description = "rustfmt check + clippy (deny warnings)"
run = [
  "cargo fmt --all --check",
  "cargo clippy --workspace --all-targets -- -D warnings",
]

[tasks.deny]
description = "Dependency policy: bans, advisories, licenses (cargo-deny)"
run = "cargo deny check"

[tasks.secrets]
description = "Secret scan of the working tree (gitleaks)"
run = "gitleaks dir . --no-banner --redact"

[tasks.test]
description = "Fast test suite — skips #[ignore]d slow tests (blocking CI tier)"
run = "cargo nextest run --all"

[tasks.test-full]
description = "Full test suite — includes #[ignore]d exhaustive/slow tests (nightly tier)"
run = "cargo nextest run --all --run-ignored all"

[tasks.fuzz-smoke]
description = "Short libFuzzer budget per fuzz target (nightly rustc via mise); FUZZ_SECONDS overrides 60s"
shell = "bash -c"
run = """
set -euo pipefail
for spec in shinri-num:integer_ops shinri-theory:classify shinri-sat:dimacs_parse shinri-sat:cnf_vs_oracle; do
  crate="${spec%%:*}"; target="${spec##*:}"
  echo "== fuzz $crate/$target =="
  (cd "crates/$crate" && mise x rust@nightly -- cargo fuzz run "$target" -- -max_total_time="${FUZZ_SECONDS:-60}")
done
"""

[tasks.ci]
description = "Everything the blocking CI tier runs: lint, deny, secrets, test"
depends = ["lint", "deny", "secrets", "test"]
```

(The five task names `lint`/`deny`/`secrets`/`test`/`test-full` and the `test` description "skips #[ignore]d slow tests" — now actually true after Task 1 — are load-bearing: ci.yml and the docs reference them.)

- [ ] **Step 2: Install and verify the new tool pin**

Run: `mise install`
Expected: installs gitleaks 8.30.1 (other tools already present). Then `mise x -- gitleaks version` prints `8.30.1`.

- [ ] **Step 3: Run the fast blocking-tier tasks**

Run: `mise run lint && mise run deny && mise run secrets`
Expected: all pass; gitleaks reports `no leaks found`. (If gitleaks flags a false positive — e.g. a hex constant in test data — add a `.gitleaks.toml` with a targeted `[allowlist]` regex for that literal, commit it, and note it in the PR description. Do not disable the scan.)

- [ ] **Step 4: Run the fast test tier**

Run: `mise run test`
Expected: PASS, `1087 tests run` (1092 previously run − 5 newly skipped), `6 skipped` (5 new + 1 pre-existing), wall-clock ≤ ~8 min.

- [ ] **Step 5: Smoke the fuzz task with a tiny budget**

Run: `FUZZ_SECONDS=5 mise run fuzz-smoke`
Expected: installs rust nightly on first run, builds each of the 4 targets, runs each ~5 s, exits 0. (One-time local cost of a few minutes; CI nightly uses the 60 s default.)

- [ ] **Step 6: Commit**

```bash
git add mise.toml
git commit -m "build(mise): pin gitleaks; add lint/deny/secrets/test/test-full/fuzz-smoke/ci tasks"
```

If Step 3 required a `.gitleaks.toml`, include it in the same commit.

---

### Task 3: ci.yml — mise single-sourcing, budget enforcement, nightly full+fuzz

**Files:**
- Modify: `.github/workflows/ci.yml` (full replacement below; file is 49 lines today)

**Interfaces:**
- Consumes: mise tasks from Task 2 (`lint`, `deny`, `secrets`, `test`, `test-full`, `fuzz-smoke`).
- Produces: blocking job `test` (≤20 min hard cap) and nightly/dispatch job `differential`.

- [ ] **Step 1: Replace .github/workflows/ci.yml with:**

```yaml
name: ci
on:
  push:
  pull_request:
  schedule:
    - cron: '0 3 * * *' # nightly full/differential/fuzz budget
  workflow_dispatch: # on-demand run of the nightly-tier job
permissions:
  contents: read
jobs:
  # Blocking tier — budget 10–15 min wall-clock, hard-capped below.
  # Any test >5 min belongs in the nightly tier via #[ignore] (see AGENTS.md).
  test:
    runs-on: ubuntu-latest
    timeout-minutes: 20
    steps:
      - uses: actions/checkout@v4
      - uses: jdx/mise-action@v2 # single source of toolchain+tools: mise.toml
        env:
          GITHUB_TOKEN: ${{ github.token }} # mise github backend → avoid API rate limits resolving z3/cvc5 releases
      - uses: Swatinem/rust-cache@v2
      - name: Lint
        run: mise run lint
      - name: Dependency policy
        run: mise run deny
      - name: Secret scan
        run: mise run secrets
      - name: Tests (fast tier)
        run: mise run test

  # Nightly tier — exhaustive/#[ignore]d tests, extended differential, oracle, fuzz.
  differential:
    runs-on: ubuntu-latest
    if: github.event_name == 'schedule' || github.event_name == 'workflow_dispatch'
    steps:
      - uses: actions/checkout@v4
      - uses: jdx/mise-action@v2
        env:
          GITHUB_TOKEN: ${{ github.token }}
      - uses: Swatinem/rust-cache@v2
      - name: Full test suite (includes #[ignore]d exhaustive tier)
        run: mise run test-full
      - name: Extended differential (more cases)
        run: cargo nextest run -p shinri-sat --test oracle
        env:
          PROPTEST_CASES: '4000'
      - name: shinri-theory extended props (more cases)
        run: cargo nextest run -p shinri-theory --test props
        env:
          PROPTEST_CASES: '4000'
      - name: z3/cvc5 differential oracle suite
        run: cargo nextest run -p shinri-solver --features oracle
      - name: Fuzz smoke (60s per target)
        run: mise run fuzz-smoke
```

Notes locked in by the spec:
- `test-full` also runs the three pre-existing `#[ignore]`d tests (`lia_e2e::unbounded_infeasible_terminates`, `qfs_fuzz_corpus::e1_enumerate_wrong_verdicts`, and the oracle stub, which is additionally feature-gated so it stays absent). `e1_enumerate_wrong_verdicts` needs `z3` on PATH — mise-action provides it in this job.
- No `dtolnay/rust-toolchain`, no `taiki-e/install-action` anywhere in the file.

- [ ] **Step 2: Lint the workflow file**

Run: `mise x actionlint@1.7.7 -- actionlint .github/workflows/ci.yml`
Expected: no output, exit 0. (One-off tool run; actionlint is not added to mise.toml.)

- [ ] **Step 3: Commit**

```bash
git add .github/workflows/ci.yml
git commit -m "ci: single-source via mise; enforce 20min blocking cap; nightly full-suite + fuzz"
```

---

### Task 4: Front door — README.md, AGENTS.md, CLAUDE.md

**Files:**
- Modify: `README.md` (full replacement below; currently 2 lines)
- Create: `AGENTS.md`
- Create: `CLAUDE.md`

**Interfaces:**
- Consumes: task names from Task 2; tier semantics from Tasks 1/3.
- Produces: the repo's single-sourced discoverability surface. CLAUDE.md contains only a pointer/import — all agent content lives in AGENTS.md.

- [ ] **Step 1: Replace README.md with:**

````markdown
# shinri

A modern pure-Rust, high-performance SMT solver.

## Setup

Install [mise](https://mise.jdx.dev), then from the repo root:

```sh
mise install   # pinned toolchain + tools: rust, nextest, cargo-deny, gitleaks, z3, cvc5, …
mise run ci    # lint + dependency policy + secret scan + fast test suite
```

## Common tasks

Defined in `mise.toml` (CI runs these same tasks — they cannot drift):

| Task | What it does |
|---|---|
| `mise run lint` | rustfmt check + clippy (deny warnings) |
| `mise run deny` | dependency policy: bans, advisories, licenses |
| `mise run secrets` | gitleaks secret scan of the working tree |
| `mise run test` | fast test suite (skips `#[ignore]`d slow tests) |
| `mise run test-full` | full suite including exhaustive/slow tests (nightly tier) |
| `mise run fuzz-smoke` | short libFuzzer run per fuzz target (`FUZZ_SECONDS` overrides 60s) |
| `mise run ci` | everything the blocking CI tier runs |

## Test tiers

- **Blocking (every push/PR):** `mise run ci` — budget 10–15 min. Tests
  measured >5 min are `#[ignore]`d into the nightly tier and keep a fast
  smoke companion here.
- **Nightly / on-demand (`workflow_dispatch`):** full suite including
  `#[ignore]`d exhaustive tests, extended differential/property runs, the
  z3/cvc5 oracle suite, and a fuzz smoke budget.
- **Oracle differential:** `cargo nextest run -p shinri-solver --features
  oracle` — requires `z3`/`cvc5` on PATH (mise provides them). Without
  `--features oracle` the suite compiles to **zero tests**; a green run
  without the flag proves nothing.

## Crate map

Dependency-ordered, foundations first:

| Crate | Role |
|---|---|
| `shinri-num` | SMT-tuned exact big-integer and rational arithmetic |
| `shinri-core` | shared vocabulary: terms, sorts, interning |
| `shinri-sat` | CDCL(T)-ready SAT search engine |
| `shinri-euf` | EUF congruence-closure theory solver |
| `shinri-theory` | Nelson–Oppen theory-combination framework |
| `shinri-arith` | Dutertre–de Moura simplex for QF_LRA (+ LIA branch&bound) |
| `shinri-arrays` | QF_AX lazy read-over-write lemmas-on-demand |
| `shinri-bv` | eager bit-blasting of QF_BV to CNF |
| `shinri-abv` | QF_ABV via lemmas-on-demand abstraction–refinement |
| `shinri-fp` | eager bit-blasting of QF_FP, reusing the shinri-bv blaster |
| `shinri-str` | string/regex theory solver |
| `shinri-solver` | embeddable solver entry point; owns the term DAG |
| `shinri-parser` | SMT-LIB 2.6 frontend: lexer + recursive descent |
| `shinri-frontend` | neutral SMT-LIB command IR (parser → solver bridge) |
| `shinri-cli` | command-line binary |

Agent contributors: see [AGENTS.md](AGENTS.md).
````

- [ ] **Step 2: Create AGENTS.md with:**

```markdown
# Agent instructions — shinri

## Setup and tasks

`mise install` provisions everything (pinned in `mise.toml`). Workflows are
mise tasks — see the table in [README.md](README.md); CI invokes the same
tasks, so never duplicate their command lines elsewhere.

## Test-tier rules

- Blocking PR tier budget: **10–15 min wall-clock** (CI job hard cap 20 min).
  Any test measured **>5 min** must be
  `#[ignore = "exhaustive: nightly tier (~N min in CI)"]`d; make sure a fast
  smoke companion covers the same operation on the blocking tier.
- Never remove `#[ignore]` from the exhaustive `shinri-fp` suites
  (`fp_div/fp_mul/fp_add` `_tiny_exhaustive_all_modes`,
  `to_fp_fp_tiny_exhaustive_both_directions`, `rem_tiny_exhaustive`).
- Oracle differential tests are feature-gated: run with
  `cargo nextest run -p shinri-solver --features oracle` (z3/cvc5 come from
  mise). **Without `--features oracle` they silently run 0 tests** — never
  report that as green coverage.
- `mise run test-full` is the local equivalent of the nightly tier
  (~1 h: the div exhaustive alone is ~54 min).

## Hygiene

- Run `cargo fmt --all` before pushing — CI gates on `fmt --check` and fails
  fast.
- `cargo clippy --workspace --all-targets -- -D warnings` must be clean
  (`mise run lint` covers both).

## Conventions

- Specs: `docs/superpowers/specs/YYYY-MM-DD-<topic>-design.md`; plans:
  `docs/superpowers/plans/YYYY-MM-DD-<topic>.md`. Spec+plan pairs are
  committed to `main`.
- Feature work happens on a slice branch with a PR to `main`; merge with a
  merge commit when CI is green, then delete the branch (remote and local).
- Pure-Rust mandate: native-link dependencies are banned (`deny.toml` bans
  `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`).
```

- [ ] **Step 3: Create CLAUDE.md with:**

```markdown
All agent instructions live in [AGENTS.md](AGENTS.md).

@AGENTS.md
```

- [ ] **Step 4: Verify every task name referenced in the docs exists**

Run: `for t in lint deny secrets test test-full fuzz-smoke ci; do mise tasks | grep -q "^$t " || echo "MISSING: $t"; done`
Expected: no output.

- [ ] **Step 5: Commit**

```bash
git add README.md AGENTS.md CLAUDE.md
git commit -m "docs: README front door + crate map; AGENTS.md agent instructions; CLAUDE.md pointer"
```

---

### Task 5: End-to-end verification, PR, merge

**Files:** none (verification only).

**Interfaces:**
- Consumes: everything above.

- [ ] **Step 1: Fresh-clone onboarding check (spec acceptance #4)**

```bash
git clone /workspace /tmp/claude-1000/-workspace/0ee5a6c1-0bfe-4bd6-af75-aba16c320b96/scratchpad/shinri-onboard
cd /tmp/claude-1000/-workspace/0ee5a6c1-0bfe-4bd6-af75-aba16c320b96/scratchpad/shinri-onboard
git checkout devkit-alignment
mise install && mise run ci
```

Expected: exits 0 (cold build; allow ~15–20 min). Delete the clone afterwards.

- [ ] **Step 2: Push and open the PR**

```bash
git push -u origin devkit-alignment
gh pr create --title "Devkit alignment: CI speed tiering, mise single-sourcing, front door, security" \
  --body "Implements docs/superpowers/specs/2026-07-17-devkit-alignment-design.md. Blocking CI drops from ~55min to ~8-10min (five exhaustive shinri-fp tests tiered to nightly via #[ignore]; fast specials_and_random companions stay blocking). Toolchain single-sourced via mise. Nightly job now runs the full suite (--run-ignored all) + 60s/target fuzz. Adds gitleaks, README/AGENTS.md/CLAUDE.md front door."
```

- [ ] **Step 3: Watch the blocking job and check the budget (spec acceptance #1)**

Run: `gh pr checks --watch`
Expected: `test` job green. Then verify wall-clock ≤15 min:
`gh run list --workflow ci.yml --branch devkit-alignment --limit 1 --json createdAt,updatedAt`

- [ ] **Step 4: Dispatch and watch the nightly-tier job on the branch (spec acceptance #2)**

```bash
gh workflow run ci.yml --ref devkit-alignment
gh run watch $(gh run list --workflow ci.yml --branch devkit-alignment --event workflow_dispatch --limit 1 --json databaseId --jq '.[0].databaseId')
```

Expected: `differential` job green (~1.5–2 h: full suite incl. 54-min div exhaustive, oracle suites, 4×60 s fuzz). The five exhaustive tests and the pre-existing ignored tests all appear as **run**, not skipped, in the log.

- [ ] **Step 5: Merge on green (standing workflow)**

```bash
gh pr merge --merge
git checkout main && git pull
git branch -d devkit-alignment && git push origin --delete devkit-alignment 2>/dev/null; git remote prune origin
```
