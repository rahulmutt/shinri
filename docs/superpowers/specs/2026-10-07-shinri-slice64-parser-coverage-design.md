# Slice 64 — Parser coverage: Reals-logic numerals, named terms, `define-sort`

Status: design approved in chat 2026-10-07. Second of four parallel tracks
agreed in chat (slice 63 LIA coefficients, slice 64 parser coverage,
slice 65 CEGAR length refinement, a re-baseline of the six un-benched
logics). Scope rulings (owner, in chat):
- numerals become logic-aware (approach A, §3.1);
- `(! t :named n)` is stripped, and the name is bound as an alias (§3.2);
- `define-sort` is nullary only (§3.3);
- a sort error that drops an assertion while the script still answers
  `sat` stays out of scope and is queued (§9);
- new timeouts are reported, not gated.

**Area:** `shinri-parser` only (`parser.rs`, plus `env.rs` if a lookup
helper is needed). Tests in `shinri-parser` and `shinri-solver/tests/`. No
core, solver, theory, printer or bench-tool change.

## 1. Summary

Three parser gaps account for about 42,300 `parse-error` rows. The
per-logic counts below are the latest per-row verdicts (`bench/results/`;
QF_FP from the 2026-09-09 baseline, the only run of that logic):

| gap | rows | logic(s) | cause |
| --- | ---: | --- | --- |
| `define-sort` unsupported | 39,994 | QF_FP | `unsupported command: define-sort` |
| Int literal in Real context | ~2,290 | QF_LRA 1,064, QF_UFLRA 1,229 | `sort error: NotApplicable` / `Mismatch` |
| `!` annotation unsupported | 34 | QF_UF (`20170829-Rodin`) | `unknown operator !` |

**`define-sort`.** All 39,994 uses are nullary: `(define-sort NAME () S)`.
This was checked by grep over the full QF_FP corpus, fetched 2026-10-07;
no file has parameters. A throwaway probe inlined the aliases textually in
60 sampled QF_FP files. The existing FP engine then answered 55 of them in
agreement with `:status` (30 `sat`, 25 `unsat`). Of the rest, 2 were `sat`
on `:status unknown` rows and 3 timed out. None were wrong.

**Real numerals.** The parser does not track the logic, so every integer
literal is minted Int. `unify_arith` (`parser.rs:419`) re-mints a *bare*
Int numeral operand as Real when a sibling operand is Real. It does not
look through `(- k)`, and let-bound constants are already interned as Int
before the coercion runs. Reproducer
`QF_UFLRA/FFT/smtlib.624882.smt2` (`:status unsat`):

```smt2
(declare-fun f3 (Real) Real) (declare-fun f5 () Real)
(assert (= (f3 f5) (- 1)))   ; sort error: Mismatch {expected Real, found Int}
```

The failing assertion is dropped, and the script then answers `sat` (§9).
Rewriting `(- N)` to `(- N.0)` textually fixed 48 of 60 sampled LRA/UFLRA
rows. The 12 residuals I bisected are let-bound Int constants used in Real
contexts. Every QF_LRA and QF_UFLRA file declares only Real arithmetic:
none contains `Int`, `to_real`, `to_int` or `is_int`.

**`!`.** All 34 rows are `(assert (! (= …) :named hypN))`.

## 2. Scope

In scope:
- §3.1 Reals-only logics mint integer literals as Real; `unify_arith`
  also re-mints constant `(- k)` operands and folds a `(- k)` divisor;
- §3.2 `(! t attr*)` → `t`, binding `:named n` as an alias;
- §3.3 nullary `define-sort`.

Out of scope:
- parametric `define-sort` (0 corpus rows), which becomes a clean parse
  error;
- `get-assignment`, `get-unsat-core`, and `:pattern` semantics;
- printing `success` for `define-fun` / `define-sort`. Neither emits an IR
  command today; the existing behaviour is kept;
- the error-continuation behaviour (§9).

## 3. Design

### 3.1 Logic-aware numerals

`Parser` gains a field `numerals_are_real: bool`, initialised `false`.
`set-logic L` sets it to `reals_only_arith(L)`, which is true iff `L`
ends in `LRA`, `NRA` or `RDL` and the character before that suffix is not
`I`. That covers QF_LRA, QF_UFLRA, LRA, UFLRA, QF_NRA, QF_UFNRA, QF_RDL,
QF_FPLRA and QF_ABVFPLRA; it excludes QF_LIRA, AUFLIRA, QF_NIRA, QF_LIA,
ALL and every logic without arithmetic.

- `parse_atom_numeral` mints a non-decimal literal with sort Real when
  the field is true, and with sort Int otherwise. Decimals are always Real,
  unchanged. Indexed-operator numerals (`(_ bv5 32)`, `(_ extract …)`) and
  sort indices go through `expect_numeral_u32`, not through this path, so
  they are unaffected.
- This is the SMT-LIB 2.6 Reals-theory reading: in Reals logics a numeral
  denotes a real. It fixes `(- 1)`, let-bound constants, UF arguments and
  `ite` branches in one place.
- For logics where the field is false (ALL, LIRA), `unify_arith` is
  extended: an Int operand whose `ctx.const_real_value` is `Some(v)` is
  re-minted as the Real numeral `v` when the application is Real-typed. A
  `(/ x (- 2))` divisor folds through `const_real_value` as well, instead
  of being rejected as "non-linear division". (`const_real_value` exists
  on `main`. Slice 63 aliases it to `const_arith_value` without a
  behaviour change.)

### 3.2 Named terms `(! t attr*)`

In `parse_term`, an application whose head symbol is `!` parses the
inner term `t`, then zero or more attributes until `)`:

- `:named n`: `n` must be a symbol. If `n` is already bound as a
  function, macro or sort-free symbol in scope, the parse fails with
  `named term: name already in use: n`, per SMT-LIB 2.6 §3.6.5. Otherwise
  `env.add_macro(n, vec![], t)` binds it, so later uses of `n` resolve to
  `t`. That is the same mechanism a nullary `define-fun` uses.
- Any other keyword: its value, if present, is consumed by an
  **iterative** s-expression skip (a depth counter, as in
  `recover_to_command_end`), so a hostile, deeply nested attribute value
  cannot overflow the stack.
- The result is `t`. An annotation never changes a term's meaning.

### 3.3 Nullary `define-sort`

`(define-sort N () S)` parses `S` with `parse_sort`. It then registers
`env.add_sort(N, s)` with the resolved `SortId`, so an alias is never
re-expanded. This rules out alias-chain or alias-bomb blowups, and an alias
of an alias simply resolves to the stored `SortId`.

- If `N` is already a sort name (built-in or declared), the parse fails:
  `define-sort: sort already defined: N`.
- A non-empty parameter list fails: `parametric define-sort unsupported`.
- Like `define-fun`, it returns `Ok(None)` (no IR command), and the
  existing error-recovery path handles failures.

### 3.4 Security (threat model: the parser is the only trust boundary)

The new syntax adds no recursion beyond `parse_term`'s existing term
nesting. Attribute skipping is iterative, and sort aliases are resolved
once. Each error is a `Diagnostic`, never a panic. A local `parse_script`
fuzz run is a gate (§7.4).

## 4. What this does not change

Term interning, the IR command set, solver behaviour, numeral printing,
QF_LIA/ALL numeral sorts (still Int), and decimal handling.

## 5. Tasks (outline; the plan details them)

0. Worktree `slice64-parser-coverage` off `main`; base binary; base runs.
1. §3.1 logic-aware numerals and the `unify_arith` extension, with unit
   tests.
2. §3.2 named terms, with unit tests.
3. §3.3 `define-sort`, with unit tests.
4. E2E reproducers and the oracle generator extension.
5. Gates (ci, oracle, fuzz); after runs; report; PR.

## 6. Cross-track coordination

- Slice 63 also changes QF_LRA rows (its 58 refused rows). Whichever slice
  merges second rebases onto `main` and re-runs `mise run ci` and the
  oracle suite, without a new bench run.
- Bench host rule: `--jobs 3`, `taskset -c 12-23`, `setsid`; builds and
  tests on `taskset -c 0-11` while a bench is live.

## 7. Testing

### 7.1 Unit (`shinri-parser`, blocking tier, written red first)

- Under `QF_LRA` and `QF_UFLRA`, `1` and `(- 1)` parse to Real-sorted
  terms. Under `QF_LIA` and `ALL`, `1` is Int.
- `reals_only_arith` is checked for every logic name listed in §3.1,
  both included and excluded.
- The FFT reproducer's assertion `(= (f3 f5) (- 1))` parses.
- A let-bound `(let ((?v (- 1))) (= f4 ?v))` parses in QF_LRA.
- With logic `ALL`, `(+ x (- 1))` with `x : Real` parses as Real (the
  `unify_arith` extension), and `(/ x (- 2))` folds.
- `(! (= a b) :named h)` parses to the same `TermId` as `(= a b)`, and a
  later `h` resolves to it. A second `:named h` is an error, and so is
  `:named` on an already-declared function name. An unknown attribute
  with a nested value is skipped.
- `(define-sort FPN () (_ FloatingPoint 11 53))` followed by
  `(declare-fun x () FPN)` gives `x` the sort `fp_sort(11, 53)`. An alias
  of an alias works. A parametric `define-sort`, a redefinition of `Real`,
  and a redefinition of an earlier alias are each errors.

### 7.2 E2E (`shinri-solver/tests/`, blocking tier)

- The FFT reproducer, inlined, answers `unsat`.
- A Rodin-shaped script `(assert (! (= a b) :named hyp1))`
  `(assert (not (= a b)))` answers `unsat`.
- The wintersteiger reproducer `QF_FP/wintersteiger/abs/abs-has-solution-8522.smt2`
  is inlined as a string. It answers its `:status`, recorded while
  planning.

### 7.3 Oracle (`--features oracle`)

A QF_LRA generator emits `(- k)` constants, let-bound integer literals
and integer literals in Real contexts. It runs against z3 with zero
disagreements, allowing no shinri `Unknown` on small bounded instances, and
both the `sat` and `unsat` counts must be non-zero. Confirm a non-zero
discovered test count.

### 7.4 Gates

`mise run ci`; the full oracle suite, with a discovered count at least
`main`'s plus this slice's new tests; and
`FUZZ_SECONDS=600` on the `parse_script` target only
(`cd crates/shinri-parser && mise x rust@nightly -- cargo fuzz run parse_script -- -max_total_time=600`),
which must produce no crash.

## 8. Measurement

Base: a `main` binary. After: the PR head. Both run the same row sets:

- **fp**: all of QF_FP (40,407);
- **lra**: all of QF_LRA and QF_UFLRA (3,037);
- **uf-rodin**: the 34 QF_UF `parse-error` rows (hard-link corpus);
- **neutrality sample**: the 2,000-row slice-59 seeded recipe.

### Success criteria

1. `wrong = 0` in every after run.
2. QF_FP `parse-error` drops by ≥ 39,900.
3. QF_LRA plus QF_UFLRA `parse-error` drops by ≥ 2,000. Every remaining
   parse error is classified in the report.
4. All 34 Rodin rows parse (no `parse-error`).
5. No `correct → non-correct` row reproduces on 3 re-runs of both
   binaries.
6. The gates in §7.4 are green.
7. The neutrality sample changes only at the timeout edge, reproduced 3/3
   as noise.

Report only, not gated: the destination of rows that leave `parse-error`
(`correct`, `unverified`, `timeout`, `oom`, `unknown`), by logic and family.

## 9. Queued for the next slice

- **A sort error drops the assertion, and the script still answers.**
  Today the CLI prints `(error …)` for the failing command and continues.
  A later `check-sat` then decides a weaker problem, so a `:status unsat`
  script can print `sat`. The bench classifies these rows as
  `parse-error`, which hides it. Candidate fix: once any assertion fails
  to parse, the next `check-sat` answers `unknown` (or the CLI exits, per
  `:diagnostic-output-channel` conventions). Ranked by the report.
- Parametric `define-sort`, if the re-baseline finds any users.
- The report's own queue.

## 10. References

- Baseline: `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`
  (§ Next slices item 6, `define-sort`; § Per-logic matrix).
- Threat model: `docs/threat-model.md`.
- SMT-LIB 2.6 standard, §3.6.5 (term attributes), §4.2.3 (`define-sort`),
  and the Reals theory definition (numerals denote reals).
