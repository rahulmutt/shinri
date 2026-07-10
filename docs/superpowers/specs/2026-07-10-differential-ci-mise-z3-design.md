# Wire z3/cvc5 into the nightly `differential` CI job

**Date:** 2026-07-10
**Status:** Design approved; ready for implementation plan
**Scope:** `.github/workflows/ci.yml` — the `differential` job only

## Problem

The nightly `differential` job runs only two self-contained proptest differentials:

- `cargo nextest run -p shinri-sat --test oracle` (LCG-driven SAT checker vs. itself)
- `cargo nextest run -p shinri-theory --test props` (union-find brute-force oracle)

**Neither touches z3.** The real differential coverage — `shinri-solver` vs. the
**z3** and **cvc5** SMT solvers — lives in `crates/shinri-solver/tests/*_oracle.rs`
(~17 non-`#[ignore]`d suites), each gated behind `#![cfg(feature = "oracle")]` and
requiring `z3` (and, for QF_LIA cross-checks in `oracle.rs`, `cvc5`) on `PATH` at
runtime via the `easy-smt` harness.

That suite **never runs in CI**: CI installs its toolchain via
`dtolnay/rust-toolchain` + `taiki-e/install-action` (no z3/cvc5) and never passes
`--features oracle`. `mise.toml` already pins `github:Z3Prover/z3` `z3-4.16.0` and
`github:cvc5/cvc5` `cvc5-1.3.4`, so those tests run locally but never in CI. mise is
the vehicle to put z3/cvc5 on `PATH` in the workflow.

The current `differential` job is green — this change **adds** missing coverage; it
does not repair a red run.

## Change

Rewrite the `differential` job (and only that job — the `test` job is untouched) to:

1. Obtain its toolchain from `jdx/mise-action@v2`, which reads `mise.toml` and
   installs + activates the pinned tools (`rust`, `cargo-nextest`, `z3`, `cvc5`, and
   also `cargo-deny`/`cargo-fuzz`/`cargo-mutants`). Activation puts `cargo`, `z3`, and
   `cvc5` on `PATH`, including for the z3/cvc5 subprocesses `easy-smt` spawns.
2. Keep the two existing proptest differential steps unchanged
   (`PROPTEST_CASES=4000`).
3. Add a new step running the z3/cvc5 oracle suite:
   `cargo nextest run -p shinri-solver --features oracle`.

### Target job definition

```yaml
  differential:
    runs-on: ubuntu-latest
    if: github.event_name == 'schedule'
    env:
      GITHUB_TOKEN: ${{ github.token }}   # mise github backend → avoid API rate limits resolving z3/cvc5 releases
    steps:
      - uses: actions/checkout@v4
      - uses: jdx/mise-action@v2          # installs everything in mise.toml: rust, nextest, z3, cvc5 (also deny/fuzz/mutants)
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

## Rationale / key points

- **Toolchain source = mise.** `jdx/mise-action@v2` makes `mise.toml` the single
  source of truth for the differential job, matching the local dev environment
  exactly. It replaces `dtolnay/rust-toolchain` + `taiki-e/install-action` **in this
  job only**.
- **`GITHUB_TOKEN` in job env** prevents GitHub API rate-limiting when mise resolves
  the z3/cvc5 GitHub-release backends.
- **nextest** is used for the new step, consistent with the rest of CI. nextest does
  not run `#[ignore]`d tests, so the two long-fuzz suites (`qfs_fuzz_corpus`,
  `differential_qf_lia_small`) stay excluded and runtime stays bounded.
- **`-p shinri-solver --features oracle`** also re-runs the ordinary `shinri-solver`
  tests. This is harmless — they already pass in the `test` job — and keeps the
  command simple rather than enumerating each oracle test file.
- **Accepted cost:** mise-action also installs `cargo-fuzz` + `cargo-mutants` (unused
  in this job). They are cached by mise after the first nightly, amortizing to ~zero.
- `Swatinem/rust-cache@v2` is retained for the workspace build (`target/`) cache;
  mise's own cache covers the pinned tools.

## Verification

- Confirm the edited `.github/workflows/ci.yml` is valid YAML and the `differential`
  job structure is well-formed.
- Locally (mise provides z3/cvc5), confirm the exact new command builds and passes:
  `cargo nextest run -p shinri-solver --features oracle` — 0 disagreements, exit 0.
  Docs record this suite as "19 suites, 0 failed" under `cargo test`; nextest runs the
  ~17 non-ignored suites.

## Out of scope

- Converting the `test` job to mise (kept on `dtolnay`/`taiki-e`).
- Enabling the `#[ignore]`d long-fuzz suites (`qfs_fuzz_corpus`,
  `differential_qf_lia_small`) — would need `--run-ignored` and an `E1_ITERS`/
  `E1_MEM_GIB` budget.
- The `shinri-theory` oracle test, which is currently a stub (its z3 call is
  commented out) and exercises no solver.
