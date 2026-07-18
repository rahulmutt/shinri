# Devkit Alignment 2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Cash the six residual devkit-hygiene gaps from
`docs/superpowers/specs/2026-07-18-devkit-alignment-2-design.md` in one PR:
delete `devenv.nix`, add a `shinri-parser` fuzz target, commit a threat
model, add Dependabot, wire a pre-commit secret scan, and wire
`cargo-mutants` (on-demand task + nightly one-crate rotation).

**Architecture:** Pure config/docs/scaffold changes — zero solver-code
changes. Every new workflow is a named mise task that CI invokes, keeping
the single-sourcing invariant from devkit-alignment-1. The only new Rust
code is one libFuzzer target in its own standalone fuzz workspace
(mirroring `crates/shinri-num/fuzz`).

**Tech Stack:** mise tasks, GitHub Actions, gitleaks 8.30.1 (pinned),
cargo-mutants 27.1.0 (pinned), cargo-fuzz 0.13.2 (pinned, nightly rustc via
`mise x rust@nightly`).

## Global Constraints

- Blocking CI tier content and budget are untouched (10–15 min budget,
  `timeout-minutes: 20` hard cap stays).
- CI never spells a command a mise task already defines — CI calls
  `mise run <task>`.
- Pure-Rust mandate: no native-link deps (`deny.toml` bans stay).
- `cargo fmt --all` before every push (CI gates on `fmt --check`).
- `mise.toml` pins are never floated; Dependabot must NOT be configured to
  touch `mise.toml`.
- Branch: `devkit-alignment-2`, PR to `main`, merge commit on green, then
  delete branch remote+local (standing workflow).
- The plan file itself is committed to `main` before branching (house
  convention; the spec is already committed as `c7b5430e`).

---

### Task 1: Branch + delete devenv.nix

**Files:**
- Delete: `devenv.nix`

**Interfaces:**
- Consumes: nothing.
- Produces: the `devkit-alignment-2` branch all later tasks commit to.

- [ ] **Step 1: Create the branch**

```bash
cd /workspace
git checkout main && git pull
git checkout -b devkit-alignment-2
```

- [ ] **Step 2: Verify nothing references devenv.nix**

Run: `grep -rn "devenv" --include="*.md" --include="*.toml" --include="*.yml" --include="*.nix" . | grep -v docs/superpowers | grep -v "^./devenv.nix"`
Expected: no output (the only hits outside the file itself are historical
spec/plan docs, which are records and must not be edited).

- [ ] **Step 3: Delete the file**

```bash
git rm devenv.nix
```

- [ ] **Step 4: Verify the environment still provisions everything**

Run: `mise install && cargo nextest --version && gitleaks version && cargo mutants --version && z3 --version`
Expected: all five commands succeed (nextest 0.9.140, gitleaks 8.30.1,
cargo-mutants 27.1.0, z3 4.16.0) — proving mise alone provisions the
toolchain.

- [ ] **Step 5: Commit**

```bash
git commit -m "build: delete devenv.nix — every tool it provided is mise-pinned; it floated rust on \"stable\" (double-sourcing violation)"
```

---

### Task 2: Dependabot config

**Files:**
- Create: `.github/dependabot.yml`

**Interfaces:**
- Consumes: nothing.
- Produces: weekly CI-gated dependency-bump PRs (cargo grouped
  minor+patch; github-actions). No other task depends on it.

- [ ] **Step 1: Write the config**

Create `.github/dependabot.yml` with exactly:

```yaml
# Weekly CI-gated dependency bumps. Deliberately NOT configured for
# mise.toml: rust/z3/cvc5 pins are adjudicated choices (the differential
# oracle in particular must not drift under our feet).
version: 2
updates:
  - package-ecosystem: cargo
    directory: "/"
    schedule:
      interval: weekly
    groups:
      cargo-minor-patch:
        update-types:
          - minor
          - patch
  - package-ecosystem: github-actions
    directory: "/"
    schedule:
      interval: weekly
```

- [ ] **Step 2: Sanity-check the YAML parses**

Run: `python3 -c "import yaml,sys; yaml.safe_load(open('.github/dependabot.yml')); print('ok')"`
Expected: `ok`. (If PyYAML is unavailable, `ruby -ryaml -e "YAML.load_file('.github/dependabot.yml'); puts 'ok'"`; if neither exists, skip — GitHub validates on push and Task 7 checks the Dependabot tab.)

- [ ] **Step 3: Commit**

```bash
git add .github/dependabot.yml
git commit -m "build: dependabot — weekly grouped cargo minor+patch bumps and github-actions bumps, gated by blocking CI"
```

---

### Task 3: Pre-commit secret scan (`secrets-staged` task + hook)

**Files:**
- Modify: `mise.toml` (add one task after `[tasks.secrets]`)
- Modify: `README.md` (Setup section + Common tasks table)

**Interfaces:**
- Consumes: the pinned gitleaks 8.30.1 (already in `mise.toml`).
- Produces: mise task name `secrets-staged` (Task 7 does not re-test it;
  nothing else consumes it).

- [ ] **Step 1: Add the task to mise.toml**

In `mise.toml`, directly after the existing `[tasks.secrets]` block, add:

```toml
[tasks.secrets-staged]
description = "Secret scan of staged changes only (pre-commit hook body)"
run = "gitleaks git --pre-commit --staged --no-banner --redact"
```

- [ ] **Step 2: Verify the clean tree passes**

Run: `mise run secrets-staged`
Expected: exit 0, `no leaks found` (nothing staged, nothing to flag).

- [ ] **Step 3: Verify a staged secret is caught**

The dummy AWS key is assembled at runtime so the plan/repo never contain
the contiguous token (which would itself trip the tree scan):

```bash
printf 'aws_key = "AKIA%s"\n' 'IOSFODNN7EXAMPLE' > leak-test.txt
git add leak-test.txt
mise run secrets-staged; echo "exit: $?"
```

Expected: gitleaks reports 1 finding (aws-access-token, redacted), task
exits non-zero (`exit: 1`).

- [ ] **Step 4: Clean up the dummy**

```bash
git restore --staged leak-test.txt && rm leak-test.txt
mise run secrets-staged
```

Expected: exit 0 again.

- [ ] **Step 5: Generate the hook in this clone and verify it blocks**

```bash
mise generate git-pre-commit --task=secrets-staged --write
printf 'aws_key = "AKIA%s"\n' 'IOSFODNN7EXAMPLE' > leak-test.txt
git add leak-test.txt
git commit -m "should be blocked"; echo "commit exit: $?"
git restore --staged leak-test.txt && rm leak-test.txt
```

Expected: the commit is rejected by the pre-commit hook (`commit exit: 1`)
with the gitleaks finding in the output. The hook stays installed in this
clone (that's the point); it is per-clone and never committed.

- [ ] **Step 6: Document in README**

In `README.md` Setup section, extend the code block:

```sh
mise install   # pinned toolchain + tools: rust, nextest, cargo-deny, gitleaks, z3, cvc5, …
mise run ci    # lint + dependency policy + secret scan + fast test suite
mise generate git-pre-commit --task=secrets-staged --write   # optional: block staged secrets at commit time
```

In the Common tasks table, after the `mise run secrets` row, add:

```markdown
| `mise run secrets-staged` | gitleaks scan of staged changes only (pre-commit hook body) |
```

- [ ] **Step 7: Commit**

```bash
git add mise.toml README.md
git commit -m "sec: secrets-staged task + per-clone pre-commit hook via mise generate git-pre-commit"
```

---

### Task 4: shinri-parser fuzz target

**Files:**
- Create: `crates/shinri-parser/fuzz/Cargo.toml`
- Create: `crates/shinri-parser/fuzz/fuzz_targets/parse_script.rs`
- Modify: `mise.toml` (`fuzz-smoke` rotation list)

**Interfaces:**
- Consumes: `shinri_parser::{StreamingParser, StreamItem}` —
  `StreamingParser::new()`, `push_str(&mut self, &str)`,
  `next_command(&mut self, &mut Context) -> StreamItem`,
  `finish(&mut self, &mut Context) -> StreamItem` (call once at EOF);
  `shinri_core::Context::new()`.
- Produces: fuzz target `shinri-parser:parse_script` in the `fuzz-smoke`
  rotation (nightly `fuzz` CI job inherits it with zero ci.yml changes).

- [ ] **Step 1: Create the fuzz crate manifest**

Create `crates/shinri-parser/fuzz/Cargo.toml` (standalone workspace,
mirroring `crates/shinri-num/fuzz/Cargo.toml`):

```toml
[package]
name = "shinri-parser-fuzz"
version = "0.0.0"
edition = "2021"
publish = false

[package.metadata]
cargo-fuzz = true

[dependencies]
libfuzzer-sys = "0.4"
shinri-core = { path = "../../shinri-core" }
shinri-parser = { path = ".." }

[[bin]]
name = "parse_script"
path = "fuzz_targets/parse_script.rs"
test = false
doc = false

[workspace]
```

- [ ] **Step 2: Write the fuzz target**

Create `crates/shinri-parser/fuzz/fuzz_targets/parse_script.rs`:

```rust
#![no_main]
use libfuzzer_sys::fuzz_target;
use shinri_core::Context;
use shinri_parser::{StreamItem, StreamingParser};

// The repo's one untrusted-input boundary (docs/threat-model.md): arbitrary
// bytes fed through the same streaming path the CLI uses (driver.rs) must
// never panic. Ok/Err command results are both fine; only a crash is a bug.
fuzz_target!(|data: &[u8]| {
    if data.len() > 1 << 16 {
        return; // keep individual inputs bounded
    }
    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };
    let mut ctx = Context::new();
    let mut sp = StreamingParser::new();
    sp.push_str(src);
    loop {
        match sp.next_command(&mut ctx) {
            StreamItem::Command(_) => {}
            StreamItem::NeedMore | StreamItem::Done => break,
        }
    }
    // EOF flush: emits at most one trailing-partial-command diagnostic.
    let _ = sp.finish(&mut ctx);
});
```

- [ ] **Step 3: Build and smoke-run the target (30 s)**

```bash
cd /workspace/crates/shinri-parser
mise x rust@nightly -- cargo fuzz run parse_script -- -max_total_time=30
cd /workspace
```

Expected: compiles, libFuzzer runs for ~30 s (`Done ... runs in 31 second(s)`
or similar), exit 0, no crash artifact. First build takes a few minutes.

- [ ] **Step 4: Add the target to the fuzz-smoke rotation**

In `mise.toml` `[tasks.fuzz-smoke]`, change the `for spec in` list from:

```
for spec in shinri-num:integer_ops shinri-theory:classify shinri-sat:dimacs_parse shinri-sat:cnf_vs_oracle; do
```

to:

```
for spec in shinri-num:integer_ops shinri-theory:classify shinri-sat:dimacs_parse shinri-sat:cnf_vs_oracle shinri-parser:parse_script; do
```

- [ ] **Step 5: Verify the rotation picks it up (quick budget)**

Run: `FUZZ_SECONDS=5 mise run fuzz-smoke 2>&1 | grep "== fuzz"`
Expected output includes all five lines, ending with
`== fuzz shinri-parser/parse_script ==`, and the task exits 0.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-parser/fuzz mise.toml
git commit -m "test(parser): parse_script fuzz target — crash-freedom on the untrusted SMT-LIB boundary; joins the nightly fuzz-smoke rotation"
```

---

### Task 5: Threat model + AGENTS.md pointer

**Files:**
- Create: `docs/threat-model.md`
- Modify: `AGENTS.md` (new Security section)

**Interfaces:**
- Consumes: nothing.
- Produces: `docs/threat-model.md` (referenced by Task 4's code comment,
  already written to that path).

- [ ] **Step 1: Write docs/threat-model.md**

Create `docs/threat-model.md` with exactly:

```markdown
# Threat model — shinri

Last revisited: 2026-07-18 (devkit-alignment-2 slice). Revisit when a
trust boundary changes: a new input format, any network surface, or any
runtime privilege.

## What shinri is

A pure-Rust SMT solver, consumed as a CLI binary (`shinri-cli`) or an
embeddable library (`shinri-solver`). It reads SMT-LIB 2.6 text, decides
it, and prints verdicts/models. No network I/O, no runtime secrets, no
elevated privileges.

## Assets

1. **Verdict soundness.** A wrong `sat`/`unsat` is the worst failure mode:
   downstream users (verifiers, provers) build on the answer. Guarded by
   the test tiers, the z3/cvc5 differential oracle, and the dump-and-diff
   discipline (see [AGENTS.md](../AGENTS.md)) — named here, enforced there.
2. **Host-process integrity.** Hostile input must not corrupt memory or
   escalate beyond "the solver process misbehaved".

## Adversary

The author of a hostile SMT-LIB script fed to the CLI or library — a
malicious benchmark file, or a service embedding shinri and passing it
untrusted queries.

## Trust boundary

Exactly one untrusted edge: **SMT-LIB text entering the lexer/parser**
(`shinri-parser`, streamed through `StreamingParser` — the same path the
CLI driver uses). Everything past the parser operates on interned, typed
IR. There is no other input surface: no network listener, no config files,
no environment-controlled behavior beyond standard cargo/CI variables.

## Controls

| Risk | Control |
|---|---|
| Memory unsafety on hostile input | Pure-Rust mandate: `deny.toml` bans native-link deps (`rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`); exactly one audited `unsafe` block (`crates/shinri-sat/src/clause.rs`) |
| Parser crashes / panics | `parse_script` fuzz target (`crates/shinri-parser/fuzz`) on the nightly fuzz budget, alongside the num/theory/sat targets |
| Dependency CVEs | `cargo deny check` (advisories, bans, licenses) on the blocking tier; Dependabot weekly grouped bumps |
| Committed credentials | gitleaks: blocking-CI step + `mise run secrets`; opt-in per-clone pre-commit hook (`mise generate git-pre-commit --task=secrets-staged --write`) |

## Out of scope

- **Resource-exhaustion DoS.** SMT solving is inherently super-polynomial;
  a small input can legitimately consume unbounded CPU/memory. Callers
  must impose external timeouts and resource limits.
- **Side channels.** Solving is not a secret-bearing computation here;
  timing/cache behavior is not defended.
```

- [ ] **Step 2: Point to it from AGENTS.md**

In `AGENTS.md`, after the `## Hygiene` section and before `## Conventions`,
add:

```markdown
## Security

- Threat model: [docs/threat-model.md](docs/threat-model.md) — read it
  before touching `shinri-parser` or any input-handling code.
```

- [ ] **Step 3: Verify the links resolve**

Run: `test -f docs/threat-model.md && grep -q "threat-model.md" AGENTS.md && grep -q "AGENTS.md" docs/threat-model.md && echo ok`
Expected: `ok`

- [ ] **Step 4: Commit**

```bash
git add docs/threat-model.md AGENTS.md
git commit -m "docs: commit the threat model (one untrusted edge: SMT-LIB text into the parser); point to it from AGENTS.md"
```

---

### Task 6: cargo-mutants — on-demand task + nightly rotation

**Files:**
- Modify: `mise.toml` (add `[tasks.mutants]` before `[tasks.ci]`)
- Modify: `.github/workflows/ci.yml` (new `mutants` job after `fuzz`)
- Modify: `README.md` (Common tasks table + Test tiers nightly bullet)

**Interfaces:**
- Consumes: pinned cargo-mutants 27.1.0.
- Produces: mise task `mutants` (parameterized by env `MUTANTS_PACKAGE`);
  the CI job calls exactly `mise run mutants`.

- [ ] **Step 1: Add the mise task**

In `mise.toml`, directly before `[tasks.ci]`, add:

```toml
[tasks.mutants]
description = "Mutation-test one crate (cargo-mutants); pick it via MUTANTS_PACKAGE, e.g. MUTANTS_PACKAGE=shinri-num mise run mutants"
run = "cargo mutants --package \"$MUTANTS_PACKAGE\" --timeout 300 --output target/mutants"
```

(`--timeout 300` caps each cargo build/test invocation at 300 s so one
pathological mutant cannot eat the budget; `--output target/mutants` keeps
`mutants.out` under the already-gitignored `target/`.)

- [ ] **Step 2: Smoke-run locally on the smallest crate**

Run: `MUTANTS_PACKAGE=shinri-frontend mise run mutants; echo "exit: $?"`
Expected: cargo-mutants runs a baseline then the mutants for
`shinri-frontend` (a few minutes). Exit code 0 (all caught), 2 (missed
mutants found), or 3 (some timed out) are ALL acceptable here — this step
verifies the plumbing, not suite strength.

- [ ] **Step 3: Verify the artifact location**

Run: `ls target/mutants/mutants.out/ | head`
Expected: cargo-mutants output files (`outcomes.json`, `missed.txt`,
`caught.txt`, `mutants.json`, logs...).

- [ ] **Step 4: Add the nightly rotation job to ci.yml**

In `.github/workflows/ci.yml`, after the `fuzz` job, add:

```yaml
  # Mutation audit — one crate per night, rotated by day-of-year (full
  # 15-crate cycle ≈ every two weeks). Report-only for now: missed mutants
  # (exit 2) and timeouts (exit 3) surface via the mutants.out artifact,
  # not a red job — a first pass over an unaudited suite would pin the
  # nightly red permanently. Baseline/usage failures (other codes) still
  # fail. Revisit fail-on-regression once a baseline exists.
  mutants:
    runs-on: ubuntu-latest
    if: github.event_name == 'schedule' || github.event_name == 'workflow_dispatch'
    timeout-minutes: 180
    steps:
      - uses: actions/checkout@v4
      - uses: jdx/mise-action@v2
        env:
          GITHUB_TOKEN: ${{ github.token }}
      - uses: Swatinem/rust-cache@v2
      - name: Pick tonight's crate (day-of-year rotation)
        id: pick
        run: |
          crates=(shinri-num shinri-core shinri-frontend shinri-sat shinri-theory shinri-euf shinri-solver shinri-arith shinri-parser shinri-cli shinri-arrays shinri-bv shinri-abv shinri-str shinri-fp)
          idx=$(( 10#$(date -u +%j) % ${#crates[@]} ))
          echo "crate=${crates[$idx]}" >> "$GITHUB_OUTPUT"
          echo "Tonight's crate: ${crates[$idx]}"
      - name: Mutation-test ${{ steps.pick.outputs.crate }}
        run: |
          set +e
          MUTANTS_PACKAGE='${{ steps.pick.outputs.crate }}' mise run mutants
          code=$?
          case "$code" in
            0|2|3) exit 0 ;;  # clean / missed mutants / timeouts: report-only
            *) exit "$code" ;;
          esac
      - name: Upload mutants.out
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: mutants-${{ steps.pick.outputs.crate }}
          path: target/mutants/mutants.out
```

- [ ] **Step 5: Document in README**

In the Common tasks table, after the `mise run fuzz-smoke` row, add:

```markdown
| `mise run mutants` | mutation-test one crate (`MUTANTS_PACKAGE=shinri-num mise run mutants`) |
```

In the Test tiers section, extend the nightly bullet's list so it reads:

```markdown
- **Nightly / on-demand (`workflow_dispatch`):** full suite including
  `#[ignore]`d exhaustive tests, extended differential/property runs, the
  z3/cvc5 oracle suite, a fuzz smoke budget, and a one-crate
  mutation-audit rotation (report-only; results as a `mutants-<crate>`
  artifact).
```

- [ ] **Step 6: Commit**

```bash
git add mise.toml .github/workflows/ci.yml README.md
git commit -m "test: wire cargo-mutants — on-demand mutants task + report-only nightly one-crate rotation with mutants.out artifact"
```

---

### Task 7: End-to-end verification, PR, merge

**Files:** none (verification only).

**Interfaces:**
- Consumes: everything above.

- [ ] **Step 1: fmt + lint gate**

Run: `cargo fmt --all && mise run lint`
Expected: exit 0, no diffs, no clippy warnings. (The fuzz crate is a
standalone workspace, so also:
`cd crates/shinri-parser/fuzz && cargo fmt --check && cd /workspace` —
expected: clean.)

- [ ] **Step 2: Fresh-clone onboarding check (spec acceptance #2)**

```bash
git clone /workspace /tmp/claude-1000/-workspace/7bd540f7-10d8-49be-94ba-fc143b48bad5/scratchpad/shinri-onboard
cd /tmp/claude-1000/-workspace/7bd540f7-10d8-49be-94ba-fc143b48bad5/scratchpad/shinri-onboard
git checkout devkit-alignment-2
mise install && mise run ci
cd /workspace
rm -rf /tmp/claude-1000/-workspace/7bd540f7-10d8-49be-94ba-fc143b48bad5/scratchpad/shinri-onboard
```

Expected: exits 0 with `devenv.nix` absent (cold build; allow ~15 min).

- [ ] **Step 3: Push and open the PR**

```bash
git push -u origin devkit-alignment-2
gh pr create --title "Devkit alignment 2: residual hygiene gaps" \
  --body "Implements docs/superpowers/specs/2026-07-18-devkit-alignment-2-design.md. Deletes devenv.nix (double-sourced, floating rust channel); adds shinri-parser parse_script fuzz target to the nightly fuzz-smoke rotation; commits docs/threat-model.md (pointed from AGENTS.md); adds weekly grouped Dependabot (cargo + github-actions; mise.toml pins stay manual); adds secrets-staged task + per-clone pre-commit hook; wires cargo-mutants as an on-demand task plus a report-only nightly one-crate rotation with a mutants.out artifact. Blocking-tier content and budget unchanged."
```

- [ ] **Step 4: Watch the blocking job (spec acceptance #1)**

Run: `gh pr checks --watch`
Expected: `test` job green, wall-clock within the usual ~8–10 min (budget
unchanged — this PR adds nothing to the blocking tier).

- [ ] **Step 5: Dispatch the nightly tier on the branch (spec acceptance #3)**

```bash
gh workflow run ci.yml --ref devkit-alignment-2
sleep 30
gh run watch $(gh run list --workflow ci.yml --branch devkit-alignment-2 --event workflow_dispatch --limit 1 --json databaseId --jq '.[0].databaseId')
```

Expected: all nightly jobs green, and specifically:
(a) the `fuzz` job log contains `== fuzz shinri-parser/parse_script ==`;
(b) the `mutants` job log shows `Tonight's crate: <crate>` and completes
within its 180-min cap;
(c) a `mutants-<crate>` artifact is attached to the run
(`gh run view <id> --json artifacts --jq '.artifacts[].name'`).

- [ ] **Step 6: Check Dependabot accepted the config (spec acceptance #5)**

Run: `gh api repos/{owner}/{repo}/dependabot/alerts --silent 2>/dev/null; gh api "repos/{owner}/{repo}/contents/.github/dependabot.yml?ref=devkit-alignment-2" --jq .name`
Expected: `dependabot.yml`. (Full confirmation — the Dependency graph →
Dependabot tab showing both ecosystems — happens after merge; check it
post-merge and note the result in the truth-up.)

- [ ] **Step 7: Merge on green (standing workflow)**

```bash
gh pr merge --merge
git checkout main && git pull
git branch -d devkit-alignment-2 && git push origin --delete devkit-alignment-2 2>/dev/null; git remote prune origin
```

- [ ] **Step 8: Truth-up the spec**

Append an "Implementation notes (truth-up)" section to
`docs/superpowers/specs/2026-07-18-devkit-alignment-2-design.md` on `main`
(house convention): what landed as designed, any deviations, the nightly
dispatch results (fuzz line, mutants crate + exit code, artifact name), the
post-merge Dependabot tab check, and anything newly banked. Commit it:

```bash
git add docs/superpowers/specs/2026-07-18-devkit-alignment-2-design.md
git commit -m "docs: devkit-alignment-2 truth-up"
git push
```
