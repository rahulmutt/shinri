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
