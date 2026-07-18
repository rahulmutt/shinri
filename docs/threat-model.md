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
