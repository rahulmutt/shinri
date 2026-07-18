# shinri

A modern pure-Rust, high-performance SMT solver.

## Setup

Install [mise](https://mise.jdx.dev), then from the repo root:

```sh
mise install   # pinned toolchain + tools: rust, nextest, cargo-deny, gitleaks, z3, cvc5, …
mise run ci    # lint + dependency policy + secret scan + fast test suite
mise generate git-pre-commit --task=secrets-staged --write   # optional: block staged secrets at commit time
```

## Common tasks

Defined in `mise.toml` (CI runs these same tasks — they cannot drift):

| Task | What it does |
|---|---|
| `mise run lint` | rustfmt check + clippy (deny warnings) |
| `mise run deny` | dependency policy: bans, advisories, licenses |
| `mise run secrets` | gitleaks secret scan of the working tree |
| `mise run secrets-staged` | gitleaks scan of staged changes only (pre-commit hook body) |
| `mise run test` | fast test suite (skips `#[ignore]`d slow tests) |
| `mise run test-full` | full suite including exhaustive/slow tests (nightly tier) |
| `mise run fuzz-smoke` | short libFuzzer run per fuzz target (`FUZZ_SECONDS` overrides 60s) |
| `mise run mutants` | mutation-test one crate (`MUTANTS_PACKAGE=shinri-num mise run mutants`) |
| `mise run ci` | everything the blocking CI tier runs |

## Test tiers

- **Blocking (every push/PR):** `mise run ci` — budget 10–15 min. Tests
  measured >5 min are `#[ignore]`d into the nightly tier and keep a fast
  smoke companion here.
- **Nightly / on-demand (`workflow_dispatch`):** full suite including
  `#[ignore]`d exhaustive tests, extended differential/property runs, the
  z3/cvc5 oracle suite, a fuzz smoke budget, and a one-crate
  mutation-audit rotation (report-only; results as a `mutants-<crate>`
  artifact).
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
