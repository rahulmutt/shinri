# Slice 63 — Constant coefficients in linear arithmetic

Status: design approved in chat 2026-10-07. First of four parallel tracks
agreed in chat (slice 63 LIA coefficients, slice 64 parser coverage,
slice 65 CEGAR length refinement, a re-baseline of the six un-benched
logics). Scope ruling (owner, in chat): approach B below (one shared
constant-value helper used by all three linearity sites); newly exposed
timeouts/ooms are reported, not gated.

**Area:** `shinri-core` (`Context::const_real_value` renamed
`const_arith_value`, alias kept), `shinri-theory` (`atom.rs`
`contains_nonlinear_mul`), `shinri-arith` (`lib.rs` `is_linear_arith`,
`normalize.rs` `linearize`'s `Mul` arm), a new oracle test in
`shinri-solver/tests/`. No parser, string, FP-semantics, SAT or bench-tool
change.

## 1. Summary

There are **4,874** `unknown:theory-refused` rows in `bench/results/slice53/`
(QF_LIA 4,764, QF_LRA 58, QF_SLIA 35, QF_UFLIA 17). **4,166**
contain `(* (- <numeral>)` by a literal grep over every file. The other 708
(`convert` 319, `rings_preprocessed` 294, `cut_lemmas` 93, Certora 2) were
sampled (6 files), and each sample showed the mirrored shape `(* x (- 4))`.
Criterion 2 (§8) is set below the total for that reason. Families: `nec-smt`
2,041, Bromberger 806, `CAV_2009_benchmarks` 591, `convert` 319, `rings_preprocessed`
294, `dillig` 233, `slacks` 232, and a tail.

Reproducer on `main` (`a287572`):

```smt2
(set-logic QF_LIA)(declare-fun x () Int)
(assert (<= (* (- 4) x) 3))
(check-sat)
```

shinri answers `unknown` with `fence=theory-refused`; z3 answers `sat`.

Root cause: `(- 4)` is interned as `App { Neg, [4] }`, not as a numeral.
Three sites decide "is this factor a constant" by matching a numeral only:

| site | test | effect |
| --- | --- | --- |
| `shinri-theory/src/atom.rs:223` `contains_nonlinear_mul` | `TermNode::Const` | counts `(- 4)` as a second non-constant factor → `Unsupported` → `refused` |
| `shinri-arith/src/lib.rs` `is_linear_arith` | `numeral_value` | same misjudgement |
| `shinri-arith/src/normalize.rs:141` `linearize` `Mul` arm | `numeral_value` | would hit its `"nonlinear reached normalize"` debug assertion |

`Context::const_real_value` (`shinri-core/src/context.rs:1023`) already
computes exactly the needed value — a numeral, or unary `(- c)` of a
constant — and is sort-agnostic in practice (`numeral_value` does not look
at the sort). It is today shared by the FP `to_fp` fence (`fp_stage.rs`).

## 2. Scope

In scope:
- recognise a numeral or (recursively) a unary `Neg` of one as a constant
  factor at all three sites, Int and Real alike, either argument position,
  n-ary `*`.

Out of scope:
- folding all-constant compound coefficients (`(* (+ 1 2) x)`,
  `(* (* 2 3) x)`): no refused row has one;
- QF_LIA timeouts (3,120) and ooms (566) at base, and any new ones this
  slice exposes: candidates for a later slice once the re-baseline ranks them;
- canonicalising `(- numeral)` in the term DAG (approach A, rejected below).

## 3. Approaches considered

- **A. Canonicalise in core.** `mk_app(Neg, [numeral])` interns a negative
  numeral. One change point, but the term DAG changes for every logic
  (string indices, the FP fence, the printer, slice 55's `get-value` echo),
  forcing a full-corpus neutrality run while three other tracks contend for
  bench cores. Rejected.
- **B. Shared helper at the three sites (chosen).** No DAG change;
  blast radius is the arithmetic path (LIA/LRA/UFLIA/UFLRA plus SLIA length
  arithmetic). The three sites must agree, which is enforced by a property
  test (§7.2).
- **C. Fold in the parser.** Literal syntax only, and collides with
  slice 64's `parser.rs` work. Rejected.

## 4. Design

### 4.1 `Context::const_arith_value`

Rename `const_real_value` to `const_arith_value`; keep
`pub fn const_real_value` as a one-line `#[inline]` alias so `fp_stage.rs`
is untouched. Doc comment states the shared admit set and names every
consumer: the FP `to_fp` fence (shinri-solver), arith classify
(shinri-theory), `is_linear_arith` and `linearize` (shinri-arith). The
coupling is deliberate: every consumer means "this term is a literal
constant", and one admit set cannot drift. Behaviour is unchanged
(numeral, or unary `Neg` of a constant, recursively; `None` otherwise).

### 4.2 `contains_nonlinear_mul`

A factor counts as non-constant iff `const_arith_value(factor).is_none()`.
The recursion into children is unchanged (a constant factor's subtree
contains no `*`, so descending into it is harmless).

### 4.3 `is_linear_arith`

The two `numeral_value(t).is_some()` tests (the early return and the `Mul`
factor filter) become `const_arith_value(t).is_some()`.

### 4.4 `linearize`, `Mul` arm

`coeff = coeff * r` takes `r` from `const_arith_value(k)`. The
`debug_assert!(nonconst.is_none(), …)` stays: after §4.2/§4.3 it is
reachable only if the three sites disagree, which §7.2 forbids. The
standalone `Neg` arm is unchanged (it already negates its child's form).

## 5. What this does not change

Term interning, printing, `get-value` echo, string and FP semantics, the
`lira` / `saw_shared` fences, simplex and branch-and-bound.

## 6. Tasks

0. Branch `slice63-lia-const-coefficients` in its own worktree off `main`;
   symlink `bench/corpus` from the main checkout.
1. Red unit tests (§7.1) in `shinri-theory`, `shinri-arith`, `shinri-core`.
2. §4.1 rename + alias; §4.2–§4.4 site changes; unit tests green.
3. Property test (§7.2).
4. Oracle test (§7.3); run with `--features oracle`, confirm non-zero count.
5. `mise run ci`; `cargo fmt --all`; clippy clean.
6. Measurement (§8) and report
   `docs/superpowers/research/2026-10-XX-smtlib-2024-slice63-lia-coefficients-report.md`.
7. PR to `main`, merge commit when green, delete branch.

## 7. Testing

### 7.1 Unit (blocking tier, written red first)

- `shinri-theory` `atom.rs`: `classify` returns `Ok(Owner::Arith)` for
  `(<= (* (- 4) x) 3)` and `(<= (* x (- 4)) 3)`, Int and Real; for
  `(* (- (- 2)) x)`; and still `Err(Unsupported)` for `(* (- x) y)` and
  `(* x y)`.
- `shinri-arith` `normalize.rs`: `linearize((* (- 4) x))` = `[(x, -4)], 0`;
  `(* x (- 4) 2)` = `[(x, -8)], 0`; `(* (- 3) (- 5))` = `[], 15`.
- `shinri-arith` `lib.rs`: `is_linear_arith` true for the above, false for
  `(* (- x) y)`.
- `shinri-core`: existing `const_real_value_*` tests keep passing through
  the alias; one new test calls `const_arith_value` on an Int numeral and
  `(- (- 7))`.
- `shinri-solver/tests/lia_e2e.rs`: the §1 reproducer answers `sat` with a
  model satisfying the assertion; `(and (>= (* (- 2) x) 1) (>= x 0))`
  answers `unsat`.

### 7.2 Lockstep property (blocking tier, `proptest`, `shinri-arith`)

Generate arith terms over 2–3 Int variables from `+ - * neg`, numerals and
`(- numeral)`, depth ≤ 4, both linear and nonlinear. Assert: classify
accepts the atom `(<= t 0)` ⇔ `is_linear_arith(t)` ⇔ `linearize(t)` returns
without panicking (debug build); and when accepted, the linear form
evaluates equal to `t` under a random integer assignment. Default case
count; must stay well under 5 s.

### 7.3 Oracle (`shinri-solver/tests/neg_coeff_oracle.rs`, `--features oracle`)

Same LCG/`easy_smt` conventions as `nary_arith_oracle.rs`. 200 random
QF_LIA scripts over 3 bounded Int variables, 2–5 linear atoms whose
coefficients are drawn from `k`, `(- k)` in either factor position, mixed
with `+`/`-`. Zero verdict disagreements with z3; `Unknown` is not
tolerated (QF_LIA, small bounded instances). A vacuity floor requires both
`sat > 0` and `unsat > 0`.

### 7.4 Unchanged suites

`mise run ci`, and the full oracle suite
(`cargo nextest run -p shinri-solver --features oracle`) green with a
discovered count ≥ the `main` count + this slice's new tests.

## 8. Measurement

Base: a fresh `mise run bench-run` of `main` over QF_LIA, QF_LRA, QF_UFLIA,
QF_UFLRA (the latest per-row arith verdicts are from slice 53, older than
`main`). After: the same logics at the PR head, plus the 2,000-row
neutrality sample (slice 59's seeded recipe) and a 2,000-row seeded QF_SLIA
sample (string length arithmetic goes through `linearize`).

Host sharing (cross-track rule): `--jobs 3` on cores 12–23 while other
tracks may be benching; no timing criterion in this slice, so no
serialized timing window is needed.

### Success criteria

1. `wrong = 0` in every after run.
2. `unknown:theory-refused` drops by ≥ 4,700 rows across the arith logics
   (of 4,874; the margin covers sampled-not-grepped rows in §1 that may
   carry a different refusal). Every row still refused is classified in the
   report.
3. Each row leaving `theory-refused` lands in `correct`, `unverified`
   (confirmed by z3 `-T:120` or cvc5 on a sample of ≥ 20, all agreeing), or
   `timeout`/`oom`. Counts per destination and per family are reported;
   new `timeout`/`oom` rows are **not** gated.
4. No `correct → non-correct` row reproduces on 3 re-runs of both binaries.
5. `mise run ci` and the oracle suite green (§7.4).
6. The neutrality and QF_SLIA samples change only at the timeout edge,
   reproduced 3/3 as noise.

## 9. Queued for the next slice

Filled in by the report.

## 10. References

- Latest per-row verdicts: `bench/results/slice53/` (arith logics),
  `bench/results/slice62*/` (strings).
- Baseline: `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`
  (§ Per-logic matrix, QF_LIA `unknown` 4,764).
- Shared-constant precedent: `Context::const_real_value` doc comment
  (FP fence/folder soundness invariant).
