# Devkit alignment: CI speed tiering, toolchain single-sourcing, front door, security

**Date:** 2026-07-17
**Status:** APPROVED (design reviewed section-by-section)

## Problem

Every push/PR CI run takes 40–55 minutes. Run 29612760341 (2026-07-17): the
`Tests` step alone was 54m26s; fmt, clippy, and deny together took under 10
seconds. The wall-clock is dominated by five exhaustive `shinri-fp` tests that
run on the blocking tier:

| Test | Measured time |
|---|---|
| `shinri-fp blast::div::tests::fp_div_tiny_exhaustive_all_modes` | 3252 s (~54 min) |
| `shinri-fp blast::mul::tests::fp_mul_tiny_exhaustive_all_modes` | 2184 s (~36 min) |
| `shinri-fp blast::add::tests::fp_add_tiny_exhaustive_all_modes` | 1960 s (~33 min) |
| `shinri-fp convert::tests::to_fp_fp_tiny_exhaustive_both_directions` | 1073 s (~18 min) |
| `shinri-fp blast::rem::tests::rem_tiny_exhaustive` | 795 s (~13 min) |

The remaining ~1087 tests complete in under 6 minutes of parallel wall-clock
(longest: `rem_float32_specials_and_random` at 319 s).

Beyond CI speed, an audit against the devkit skills found:

- **developer-environment:** the CI `test` job installs Rust via
  `dtolnay/rust-toolchain@1.96.0` while `mise.toml` pins `1.97.1` — the
  toolchain is double-sourced and has drifted. Tool installs are split between
  `taiki-e/install-action` (test job) and `mise-action` (differential job).
- **testing-practices:** no speed tiering on the blocking tier; the `mise run
  test` task description claims it "skips #[ignore]d slow tests" but none of
  the exhaustive tests are ignored, so local `cargo test --workspace` also
  takes ~50 min. The already-`#[ignore]`d baseline-B&B diophantine termination
  test runs nowhere in CI.
- **navigable-codebases:** README is two lines; no AGENTS.md/CLAUDE.md front
  door; no codebase map; only `test`/`test-full` exist as named tasks.
- **security-practices:** no secret scanning. Fuzz targets exist
  (`crates/{shinri-num,shinri-theory,shinri-sat}/fuzz`) and `cargo-fuzz` is
  pinned, but the nightly job runs no fuzz step despite its comment claiming a
  "nightly differential/fuzz budget".

## Goals

1. Blocking (push/PR) CI tier within a **10–15 minute wall-clock budget**,
   enforced.
2. Exhaustive/slow coverage preserved on the existing nightly/dispatch tier.
3. One pinned source of truth for toolchain and dev tools (`mise.toml`),
   shared by CI and local dev.
4. A discoverable front door (README + AGENTS.md) with a codebase map and
   named tasks, single-sourced.
5. Secret scanning on the blocking tier; a short fuzz budget on nightly.

## Non-goals

- No new fuzz targets (a `shinri-parser` fuzz target is a noted follow-up).
- No container/IaC scanning (nothing to scan; local CLI tool).
- No SCA changes (`cargo-deny` already covers advisories, bans, licenses).
- No test sharding/matrix builds — unnecessary once tiering lands.
- No changes to the oracle-feature differential suite semantics.

## Design

### 1. Test tiering (testing-practices)

Mechanism: **`#[ignore = "exhaustive: nightly tier (~54min)"]`** — the reason
string carries each test's measured time from the table above — on exactly the
five tests listed above (threshold: >5 min measured). Chosen over a nextest
`default-filter` (name-pattern fragile; plain `cargo test` would stay slow) and
over a feature gate (most plumbing; silent 0-tests-run hazard already seen with
the oracle feature).

- Each ignored exhaustive test keeps its fast companion on the blocking tier
  (`fp_div_float32_specials_and_random` 166 s, `fp_mul_…` 122 s, `fp_add_…`
  28 s, `to_fp_fp_f64_f32_…` 37 s, `rem_float32_…` 319 s) — these are the
  smoke variants; no new tests need writing.
- The blocking `test` job gets `timeout-minutes: 20` (budget 10–15 min plus
  cold-cache headroom) so budget creep fails loudly.
- The nightly/dispatch `differential` job gains a step:
  `cargo nextest run --all --run-ignored all`. This runs the five exhaustive
  tests plus the previously-orphaned diophantine termination test daily.

Expected blocking-tier wall-clock after the change: ~8–10 min (compile +
longest test ~5.3 min), within budget.

### 2. Toolchain single-sourcing + named tasks (developer-environment, navigable-codebases)

- The blocking `test` job replaces `dtolnay/rust-toolchain@1.96.0` +
  `taiki-e/install-action` with `jdx/mise-action@v2` (with
  `GITHUB_TOKEN` env, as the differential job already does). `mise.toml`
  becomes the single pinned source for rust, nextest, deny, z3, cvc5.
  `rustfmt`/`clippy` components come with the mise-installed toolchain.
- `Cargo.toml` `rust-version = "1.96.0"` stays as the MSRV floor; the CI
  toolchain follows the mise pin (currently 1.97.1).
- `mise.toml` tasks grow so CI and local dev run identical commands:
  - `lint` — `cargo fmt --all --check && cargo clippy --workspace
    --all-targets -- -D warnings`
  - `deny` — `cargo deny check`
  - `test` — switches to `cargo nextest run --all` (description "skips
    #[ignore]d slow tests" becomes true)
  - `test-full` — `cargo nextest run --all --run-ignored all`
  - `ci` — composite: lint, deny, test
- CI steps invoke `mise run lint`, `mise run deny`, `mise run test`, etc., so
  definitions cannot fork between CI and local.

### 3. Front door (navigable-codebases)

- **README.md** becomes the human front door: what shinri is, the crate map
  (one line per crate, dependency-ordered: num → core → sat/euf/theory →
  arith/arrays/bv/abv/fp/str → solver → parser/frontend → cli), setup via
  `mise install`, the named tasks, and the test-tier story (blocking vs
  nightly vs oracle-feature differential).
- **AGENTS.md** becomes the agent front door: build/test commands, tiering
  rules (never un-ignore exhaustive tests on the blocking tier; oracle tests
  require `--features oracle` or they silently run 0 tests), fmt-before-push,
  spec/plan conventions under `docs/superpowers/specs/`, and the standing
  merge-on-green workflow.
- **CLAUDE.md** is a one-line pointer to AGENTS.md — single-sourced, no
  drift. README and AGENTS.md link to each other; neither duplicates task
  definitions (both point at `mise.toml` task names).
- Onboarding is verified by running it: fresh-clone `mise install` +
  `mise run ci` must pass during implementation.

### 4. Security (security-practices)

Threat surface: local CLI tool; untrusted input is SMT-LIB text; no network,
no secrets at runtime. Proportionate additions:

- **gitleaks** pinned in `mise.toml`, run as a blocking-CI step (seconds),
  also exposed as `mise run secrets`.
- **Nightly fuzz budget:** the nightly job runs each existing fuzz target
  (`shinri-num`, `shinri-theory`, `shinri-sat`) for 60 s via
  `cargo fuzz run <target> -- -max_total_time=60`. cargo-fuzz needs a nightly
  rustc; that toolchain is pinned through mise (exact mechanism — a scoped
  mise env/version override for the fuzz step — is decided in the plan, not
  rustup's `+nightly`). Fuzz findings fail the nightly job (surfaced, not
  blocking merges).
- Explicit non-goals above; parser fuzz target recorded as follow-up.

## Error handling / failure modes

- **Budget creep:** `timeout-minutes: 20` fails the blocking job if the tier
  regresses; the AGENTS.md tiering rule tells contributors (human or agent) to
  `#[ignore]` any new >5 min test into the nightly tier.
- **Nightly-only breakage:** exhaustive/fuzz failures surface in the scheduled
  run and via `workflow_dispatch` for on-demand reproduction; they do not
  block merges. AGENTS.md documents how to run them locally
  (`mise run test-full`).
- **mise-action rate limits:** both jobs pass `GITHUB_TOKEN` to the mise
  github backend (the differential job already does).

## Testing / acceptance criteria

1. Blocking CI job on a PR completes in ≤15 min (target ~8–10 min) with all
   previously-passing non-exhaustive tests still run and green.
2. Nightly/dispatch job runs the five exhaustive tests + diophantine
   termination test + oracle suites + 3×60 s fuzz, green on dispatch.
3. `mise run test` locally completes without the five exhaustive tests;
   `mise run test-full` includes them.
4. Fresh-clone onboarding (`mise install && mise run ci`) passes.
5. gitleaks step green on the blocking tier.
6. No remaining reference to `dtolnay/rust-toolchain` or
   `taiki-e/install-action` in `.github/workflows/ci.yml`.

## Implementation slices (for the plan)

1. `#[ignore]` the five tests + nightly `--run-ignored all` step + job
   timeout (the CI-speed win, shippable alone).
2. mise-action single-sourcing + mise tasks + CI invoking `mise run`.
3. README + AGENTS.md + CLAUDE.md front door.
4. gitleaks + nightly fuzz budget.
