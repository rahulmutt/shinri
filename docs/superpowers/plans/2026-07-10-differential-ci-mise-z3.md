# Wire z3/cvc5 into Nightly Differential CI Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the nightly `differential` CI job install z3 + cvc5 via mise and run the `shinri-solver` z3/cvc5 differential oracle suite that currently never runs in CI.

**Architecture:** Rewrite only the `differential` job in `.github/workflows/ci.yml` to obtain its toolchain from `jdx/mise-action@v2` (reading the existing `mise.toml`), keep the two existing proptest differential steps, and add one step: `cargo nextest run -p shinri-solver --features oracle`. The `test` job is untouched.

**Tech Stack:** GitHub Actions, mise (`jdx/mise-action@v2`), cargo-nextest, z3 4.16.0 + cvc5 1.3.4 (pinned in `mise.toml`), Rust workspace with a feature-gated `oracle` differential harness (`easy-smt`).

## Global Constraints

- Edit **only** the `differential` job in `.github/workflows/ci.yml`. Do not modify the `test` job, `mise.toml`, or any Rust source. (spec: Scope)
- The `differential` job stays gated on `if: github.event_name == 'schedule'` (nightly only). (existing `ci.yml`)
- Toolchain for the `differential` job comes from `jdx/mise-action@v2`, replacing `dtolnay/rust-toolchain` + `taiki-e/install-action` in that job only. (spec: Change §1)
- Keep the two existing steps verbatim, including `PROPTEST_CASES: '4000'`. (spec: Change §2)
- New oracle step command is exactly: `cargo nextest run -p shinri-solver --features oracle`. (spec: Change §3)
- Set `GITHUB_TOKEN: ${{ github.token }}` in the job `env` so mise's GitHub-release backend for z3/cvc5 is not rate-limited. (spec: Rationale)
- Retain `Swatinem/rust-cache@v2` for the workspace build cache. (spec: Rationale)

---

### Task 1: Pre-verify the new oracle command runs green locally

Prove the exact command the new CI step will run actually builds and passes in this environment (where mise already provides z3/cvc5), before touching CI. This is the "failing/passing test" for a workflow change — CI YAML can't be unit-tested, so we verify the command it invokes.

**Files:**
- Modify: none (verification only)

**Interfaces:**
- Consumes: `mise.toml` pins (`z3-4.16.0`, `cvc5-1.3.4`) already on this machine via mise.
- Produces: confidence that `cargo nextest run -p shinri-solver --features oracle` exits 0 — the command Task 2 wires into CI.

- [ ] **Step 1: Confirm z3 and cvc5 are resolvable via mise**

Run:
```bash
mise exec -- z3 --version && mise exec -- cvc5 --version
```
Expected: prints `Z3 version 4.16.0 ...` and `This is cvc5 version 1.3.4 ...` (non-zero exit means the tools aren't installed — run `mise install` first, then re-run).

- [ ] **Step 2: Confirm cargo-nextest is available**

Run:
```bash
mise exec -- cargo nextest --version
```
Expected: prints `cargo-nextest 0.9.140` (or the pinned version), exit 0.

- [ ] **Step 3: Run the exact oracle command CI will run**

Run:
```bash
mise exec -- cargo nextest run -p shinri-solver --features oracle
```
Expected: builds with the `oracle` feature, runs the ~17 non-`#[ignore]`d oracle suites (z3/cvc5 spawned by `easy-smt`), reports `0 failed`, exit 0. If any suite fails or z3/cvc5 is not found, STOP — the CI change would also fail; investigate before proceeding.

- [ ] **Step 4: No commit**

Verification only — nothing to commit in this task.

---

### Task 2: Rewrite the `differential` job to use mise + add the oracle suite step

**Files:**
- Modify: `.github/workflows/ci.yml` — the `differential` job (currently lines 28–46; the `test` job at lines 8–26 is unchanged).

**Interfaces:**
- Consumes: the green command validated in Task 1.
- Produces: a `differential` job that installs z3/cvc5 via mise and runs the oracle suite nightly.

- [ ] **Step 1: Replace the `differential` job block**

In `.github/workflows/ci.yml`, replace the entire existing `differential:` job (from the `  differential:` line through the end of the file) with:

```yaml
  differential:
    runs-on: ubuntu-latest
    if: github.event_name == 'schedule'
    env:
      GITHUB_TOKEN: ${{ github.token }} # mise github backend → avoid API rate limits resolving z3/cvc5 releases
    steps:
      - uses: actions/checkout@v4
      - uses: jdx/mise-action@v2 # installs mise.toml tools: rust, nextest, z3, cvc5 (also deny/fuzz/mutants)
      - uses: Swatinem/rust-cache@v2
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
```

Leave the `test` job (lines 8–26) and everything above it exactly as-is.

- [ ] **Step 2: Verify the workflow is valid YAML**

Run:
```bash
python3 -c "import yaml,sys; d=yaml.safe_load(open('.github/workflows/ci.yml')); j=d['jobs']['differential']; print('differential ok'); print('uses:', [s.get('uses') for s in j['steps'] if 'uses' in s]); print('runs:', [s.get('run') for s in j['steps'] if 'run' in s]); assert d['jobs']['test'], 'test job must still exist'"
```
Expected output (exit 0):
```
differential ok
uses: ['actions/checkout@v4', 'jdx/mise-action@v2', 'Swatinem/rust-cache@v2']
runs: ['cargo nextest run -p shinri-sat --test oracle', 'cargo nextest run -p shinri-theory --test props', 'cargo nextest run -p shinri-solver --features oracle']
```
If `yaml` is missing, install with `pip install pyyaml` or use `mise exec -- python3 ...`.

- [ ] **Step 3: Confirm the `test` job and toolchain-action removal are correct**

Run:
```bash
git diff .github/workflows/ci.yml
```
Expected: the diff touches **only** lines inside the `differential` job — adds `env.GITHUB_TOKEN`, swaps `dtolnay/rust-toolchain` + `taiki-e/install-action` for `jdx/mise-action@v2`, and appends the `z3/cvc5 differential oracle suite` step. The `test` job must appear nowhere in the diff.

- [ ] **Step 4: Commit**

```bash
git add .github/workflows/ci.yml
git commit -m "ci: run z3/cvc5 differential oracle suite nightly via mise

Install z3 4.16.0 + cvc5 1.3.4 (pinned in mise.toml) in the nightly
differential job via jdx/mise-action, and add a step running
'cargo nextest run -p shinri-solver --features oracle' — the real
differential coverage that previously never ran in CI."
```

---

## Self-Review

**1. Spec coverage:**
- Change §1 (mise-action toolchain) → Task 2 Step 1 (`jdx/mise-action@v2`). ✓
- Change §2 (keep two proptest steps with `PROPTEST_CASES=4000`) → Task 2 Step 1 (both steps retained verbatim). ✓
- Change §3 (add `-p shinri-solver --features oracle`) → Task 2 Step 1 (new step). ✓
- Rationale: `GITHUB_TOKEN` in env → Task 2 Step 1. ✓ nextest excludes `#[ignore]`d fuzz → inherent in command; noted in Task 1 Step 3. ✓ retain rust-cache → Task 2 Step 1. ✓
- Verification (valid YAML + local green command) → Task 1 + Task 2 Steps 2–3. ✓
- Out of scope (test job, ignored fuzz, theory stub) → Global Constraints + Task 2 Step 3 diff check. ✓

**2. Placeholder scan:** No TBD/TODO/"handle edge cases"/vague steps. Every code and command step shows exact content. ✓

**3. Type consistency:** No cross-task type/function references. The single command string `cargo nextest run -p shinri-solver --features oracle` is identical in Task 1 Step 3, Task 2 Step 1, and Task 2 Step 2 expected output. ✓
