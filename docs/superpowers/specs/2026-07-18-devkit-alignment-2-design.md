# Devkit alignment 2: residual hygiene gaps

**Date:** 2026-07-18
**Status:** APPROVED (design reviewed with user)

Predecessor: devkit-alignment (2026-07-17, PR #22), which landed CI speed
tiering, mise single-sourcing, the README/AGENTS.md front door, gitleaks, and
the nightly fuzz budget. A fresh audit of the repo against the five devkit
skills (developer-environment, testing-practices, security-practices,
navigable-codebases, writing-clean-code) confirms that work is holding — and
finds six residual gaps, all hygiene-level. This slice cashes all six in one
PR. Semgrep SAST was considered and skipped on proportionality grounds
(clippy covers the lint side; the workspace has exactly one audited `unsafe`
block).

## Problem — the six gaps

1. **`devenv.nix` double-sources and un-pins the toolchain**
   (developer-environment). It enables `languages.rust` on the floating
   `"stable"` channel and adds `pkgs.cargo-nextest`; both tools are already
   exactly-pinned in `mise.toml`. The devkit rule: keep each tool in exactly
   one place; an unpinned entry is a reproducibility bug.
2. **No `shinri-parser` fuzz target** (testing-practices +
   security-practices). SMT-LIB text is the repo's only untrusted-input
   boundary, yet the fuzz targets cover `shinri-num`/`shinri-theory`/
   `shinri-sat` only. Recorded as a follow-up in the devkit-alignment spec;
   still open.
3. **No committed threat model** (security-practices). The threat reasoning
   exists only inside the dated devkit-alignment spec (§4), not as a durable,
   discoverable artifact pointed to from AGENTS.md.
4. **No dependency-update cadence** (developer-environment). No
   Dependabot/Renovate config; upgrades arrive as big-bang bumps instead of
   small CI-gated steps.
5. **Secret scan not in pre-commit** (security-practices calls
   secret-scan-in-pre-commit + CI "non-negotiable hygiene"). Currently CI +
   `mise run secrets` only.
6. **`cargo-mutants` is pinned but wired to nothing** — no task, no CI step,
   no README mention.

## Goals

1. Exactly one pinned source for every tool (mise.toml); no floating
   versions anywhere.
2. Fuzz coverage on the actual untrusted-input boundary (the parser).
3. A committed, discoverable threat model.
4. Automated, CI-gated dependency bumps on a weekly cadence.
5. Secrets blocked at commit time (opt-in per clone), not just in CI.
6. Mutation testing usable on demand and exercised on a nightly rotation.

## Non-goals

- No Semgrep/SAST addition (proportionality; revisit if `unsafe` count or
  attack surface grows).
- No auto-bumping of `mise.toml` pins — rust/z3/cvc5 versions are
  deliberate, adjudicated choices (the oracle pins in particular).
- No committed git hooks tooling (lefthook etc.); the hook is generated
  per-clone by mise.
- No change to blocking-tier CI content or budget.
- No solver-code changes of any kind; slice 29 (solver cadence) is
  unaffected.

## Design

### 1. Delete `devenv.nix` (developer-environment)

`git rm devenv.nix`. Everything it provided is mise-pinned; the devkit
fallback rule reserves devenv.nix for what mise cannot supply, which is
currently nothing. Git history preserves the template if a system-library
need ever appears. No other file references it.

### 2. Parser fuzz target (testing-practices, security-practices)

`crates/shinri-parser/fuzz` with one target, `parse_script`, following the
existing cargo-fuzz scaffold layout (`crates/shinri-num/fuzz` is the
pattern). Body: take arbitrary `&[u8]`; on valid UTF-8, build
`Parser::new(src)` with a fresh term context and drain `next_command` until
`None`, discarding `Ok` and `Err` alike. The property is crash-freedom on
arbitrary input — no panic, no OOM (input bounded by libFuzzer's default
`max_len`). Wire-up is one line: add `shinri-parser:parse_script` to the
`fuzz-smoke` rotation list in `mise.toml`; the nightly fuzz job inherits it
with zero `ci.yml` changes.

### 3. Threat model (security-practices)

`docs/threat-model.md`, per the devkit threat-model template:

- **Assets:** verdict soundness (a wrong sat/unsat is the worst failure);
  host-process integrity (no memory-unsafety escalation from input).
- **Adversary:** the author of a hostile SMT-LIB script fed to the CLI or
  library.
- **Trust boundary:** SMT-LIB text entering the lexer/parser — the only
  untrusted edge. No network, no runtime secrets, no elevated privileges.
- **Standing controls:** pure-Rust mandate (`deny.toml` bans native-link
  deps), a single audited `unsafe` block (`shinri-sat/src/clause.rs`),
  fuzzing (incl. the new parser target), cargo-deny SCA, gitleaks.
- **Out of scope:** resource-exhaustion DoS (SMT solving is inherently
  super-polynomial; callers impose external timeouts), side channels.

AGENTS.md gets a one-line pointer so agents load it before touching
parser/input-handling code.

### 4. Dependabot (developer-environment)

`.github/dependabot.yml`, weekly, two ecosystems:

- `cargo` — minor+patch bumps grouped into one PR to bound noise.
- `github-actions` — action version bumps.

`mise.toml` pins stay manual (non-goal above). Dependabot PRs gate on the
existing blocking CI tier.

### 5. Pre-commit secret scan (security-practices)

- New mise task `secrets-staged`:
  `gitleaks git --pre-commit --staged --no-banner --redact`
  (flags verified against the pinned gitleaks 8.30.1).
- Hook wired per-clone via
  `mise generate git-pre-commit --task=secrets-staged --write`; README's
  setup section gains that one line. Git hooks cannot be committed, so the
  hook is opt-in per clone; the blocking-CI gitleaks step remains the
  enforcing backstop.

### 6. cargo-mutants: on-demand task + nightly rotation (testing-practices)

- Task `mutants`: `cargo mutants --package "$MUTANTS_PACKAGE"` with a
  per-mutant timeout (exact flags pinned in the plan). Documented in the
  README task table alongside `secrets-staged`.
- New nightly-only `ci.yml` job `mutants` (same
  `schedule`/`workflow_dispatch` guard as the other nightly jobs): picks one
  crate deterministically by day-of-year modulo the workspace crate list
  (full 15-crate cycle ≈ every two weeks) and runs the task.
- **Report-only:** missed mutants are summarized in the log and uploaded as
  an artifact (`mutants.out`); they do not fail the job. A first run over an
  unaudited suite would otherwise pin the nightly red permanently. Revisit
  failing-on-regression once a baseline exists.
- Job hard cap (`timeout-minutes`) so a slow crate (`shinri-solver`,
  `shinri-fp` — minutes per test run, and mutants runs the suite per mutant)
  truncates loudly instead of eating the runner.

## Error handling / failure modes

- **Hook not installed:** per-clone opt-in means some clones won't run the
  staged scan; the blocking-CI gitleaks step catches anything that slips.
- **Mutants overrun:** the job timeout truncates the run; the artifact
  contains whatever completed. Truncation is visible in the log, not silent.
- **Dependabot PR breaks CI:** the PR simply stays red and unmerged; the
  blocking tier is the gate, as for any PR.
- **Parser fuzz finding:** a panic reproducer lands in
  `crates/shinri-parser/fuzz/artifacts` on the nightly job; findings fail
  the fuzz job (existing `fuzz-smoke` semantics — surfaced, not
  merge-blocking).

## Testing / acceptance criteria

1. Blocking CI unchanged: same steps, same budget, green.
2. Fresh-clone onboarding (`mise install && mise run ci`) passes with
   `devenv.nix` gone.
3. `workflow_dispatch` of the nightly tier shows (a) `parse_script` running
   in the fuzz job, (b) the `mutants` job completing with a `mutants.out`
   artifact for the day's crate.
4. The generated pre-commit hook blocks a staged dummy secret locally, and
   `mise run secrets-staged` passes on the clean tree.
5. Dependabot config is accepted by GitHub (visible under Insights →
   Dependency graph → Dependabot).
6. `docs/threat-model.md` committed; AGENTS.md points to it.

## Implementation slices (for the plan)

1. devenv.nix removal + Dependabot config + `secrets-staged` task/hook +
   README/AGENTS.md touches (pure config/docs).
2. Parser fuzz target + fuzz-smoke wire-up.
3. Threat model document.
4. mutants task + nightly rotation job.
5. End-to-end verification (fresh clone, nightly dispatch), PR, merge on
   green.

## Implementation notes (truth-up)

Landed 2026-07-18 as PR #26 (merge commit `3016bba5`, branch
`devkit-alignment-2`, 7 commits + 1 CI fix). Everything in this spec shipped
as designed except the deviations below.

**Acceptance results:**
1. Blocking tier green and unchanged: `test` job 14m33s cold at `4c15fc08`
   (nightly-only jobs correctly skipped on push/PR).
2. Fresh-clone onboard: `mise install && mise run ci` exit 0 with
   `devenv.nix` absent (1088 passed / 6 skipped, 342 s).
3. Nightly dispatch run 29644654228 at `4c15fc08`: ALL 10 jobs green,
   wall-clock 41m05s. (a) fuzz job ran all five targets incl.
   `== fuzz shinri-parser/parse_script ==` (1,717,461 runs / 61 s on the
   pre-fix dispatch; green again on the final run). (b) `mutants` job:
   `Tonight's crate: shinri-theory`, 245 mutants tested in 29 m —
   118 caught, 86 missed, 36 unviable, 5 timeouts — report-only exit 0 as
   designed (job 35 m, well under the 180-min cap). (c) artifact
   `mutants-shinri-theory` attached.
4. Hook verified locally (blocks a staged non-EXAMPLE dummy key, exit 1;
   clean tree exit 0) and live-validated: it ran on the branch's own
   commits after installation.
5. `dependabot.yml` accepted on main. CLI-side confirmation is limited:
   the Dependabot *alerts* feature is disabled for the repo (403 on the
   alerts API) but version updates from `dependabot.yml` are independent
   of it. Remaining human check: Insights → Dependency graph → Dependabot
   showing both ecosystems, and the first weekly PR wave.
6. `docs/threat-model.md` committed; AGENTS.md `## Security` points to it.

**Deviations from the spec/plan text:**
- Threat model's "exactly one audited `unsafe` block" was factually wrong:
  a second, `#[cfg(feature = "oracle")]`-gated `unsafe` (`libc::setrlimit`)
  lives in the differential test harness
  (`crates/shinri-solver/tests/qfs_fuzz_corpus.rs`). Claim scoped to
  shipping code in `0cf49349`.
- The plan's gitleaks drill key (`AKIA…EXAMPLE`) is allowlisted by gitleaks
  8.30.1's built-in `.+EXAMPLE$` stopword, so the drill as written
  false-negatives. Detection/blocking was proven with a non-EXAMPLE dummy
  key instead.
- The plan's `[tasks.mutants]` failed on a fresh CI checkout: cargo-mutants
  does not create the `--output` parent directory and CI has no `target/`.
  Fixed with `mkdir -p target/mutants &&` in the task (`4c15fc08`); the
  report-only exit-code guard correctly surfaced the failure as red (exit 1
  is not in the tolerated 0|2|3 set).
- Plumbing smoke on `shinri-frontend` legitimately found "0 mutants"
  (pure-enum IR crate); plumbing was verified via the artifact tree and the
  real CI run above.

**Banked:** first mutation baseline exists (shinri-theory: 86 missed
mutants in the artifact — future test-strengthening material); the
day-of-year rotation (`10#` radix guard) and report-only policy validated
in production.
