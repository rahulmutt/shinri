# Slice 50 — QF_UFLIA: define compound shared arithmetic terms; eager ⊤≠⊥

Status: design approved in chat 2026-09-29. Picks up the post-slice-49 queue
(`docs/superpowers/research/2026-09-11-smtlib-2024-slice49-euf-report.md`,
`## Queued for the next slice`): the QF_UFLIA wrong-answer cluster (baseline
rank 3, 11 rows) and, as an independent task, the ⊤≠⊥ sentinel hazard.

## 1. Summary

### 1.1 The defect

All 11 remaining QF_UFLIA `wrong` rows (`mathsat/Wisa` 9, `wisas` 2) are
`:status unsat` answered `sat`. The cheapest,
`QF_UFLIA/mathsat/Wisa/xs-05-08-4-2-5-4.smt2` (3,627 bytes), answers `sat`
in about 4 s; z3 4.16.0 answers `unsat`. It has no Boolean-valued UF: every UF is
`Int → Int`, applied to compound arithmetic arguments such as
`(select_format (+ arg1 1))` and `(s_count (- (- fmt1 2) fmt0))`.

shinri's own model is inconsistent. With `get-value` appended: `arg1 = 0`,
`fmt1 = 3`, but `(+ arg1 1) ↦ 0` and `(+ fmt1 1) ↦ 0` (printed under
purification names `t250`, `t265`; see §10).

### 1.2 Minimal reproducer

```
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(assert (= a 0))
(assert (= (f 1) 5))
(assert (not (= (f (+ a 1)) 5)))
(check-sat)
```

shinri: `sat`, with `a ↦ 0`, `(+ a 1) ↦ 0`, `(f 1) ↦ 5`, `(f (+ a 1)) ↦ 6`.
z3: `unsat`. Variant probes (pre-slice `main` at `b94d4ce`):

| variant | shinri | z3 |
| --- | --- | --- |
| `a=0`, `f(0)=5`, `¬f(a)=5` (variable argument) | unsat | unsat |
| `a=1`, `f(1)=5`, `¬f((+ a 0))=5` | **sat** | unsat |
| `b=(+ a 1)`, `a=0`, `f(1)=5`, `¬f(b)=5` (indirection) | unsat | unsat |
| §1.2 as written | **sat** | unsat |
| §1.2 plus `(>= (+ a 1) 0)` (the term also in an arith atom) | **sat** | unsat |
| `a=0`, `f(0)=5`, `¬f((* 2 a))=5` | **sat** | unsat |

A variable argument and an indirection through a variable are correct. Every
compound linear argument is wrong, including when the same term appears in an
arithmetic atom.

### 1.3 Mechanism

The combiner's final check (`crates/shinri-theory/src/combiner.rs`,
`drive_final_check`) builds the shared set from
`Euf::shared_arith_terms` — every Int/Real-sorted term EUF has registered,
which includes a UF application's compound arguments — and calls
`Arith::ensure_shared_var(t)` on each (`crates/shinri-arith/src/lib.rs:648`).
That calls `self.vars.problem_var_sorted(t, is_int)`, which interns the
**TermId `(+ a 1)` as a fresh problem variable with no defining constraint**.
Only numerals are pinned (the slice-42 path).

Arithmetic atoms never reach that variable: `normalize::linearize` walks
`(+ a 1)` structurally to `a + 1` over `a`'s variable. So the simplex holds
two unrelated things — `a` (constrained) and `v_(+ a 1)` (free) — and
`entailed_equalities`, `model_equal_shared_pairs` (MBTC) and the model all
read the free one. Both of those also skip any variable whose interface class
is unconstrained (slice 42), which `v_(+ a 1)` always is, so the pair
`((+ a 1), 1)` is never even probed. In §1.2, `v_(+ a 1)` takes 0, MBTC never sees it equal to
`1`, EUF never merges `f(a+1)` with `f(1)`, and the answer is `sat`.

The indirection variant works because `b` is a leaf: the atom `b = a + 1`
constrains `b`'s problem variable, which *is* the shared variable.

### 1.4 Blast radius

Any logic whose final check runs the N-O exchange (the combiner skips it when
there is no UF application and no `str.len` term): QF_UFLIA, QF_UFLRA, and
the string logics wherever EUF registers a compound Int term. The QF_SLIA
baseline's 37 wrong `sat` rows (`20230329-denghang` 35, Noetzli 2) are a
candidate beneficiary; this spec claims nothing about them (§7).

### 1.5 The independent task: ⊤≠⊥ sentinel

Found by slice 49's whole-branch review and reproduced at the `Euf` level
only. `EGraph::truth_nodes` (`crates/shinri-euf/src/egraph.rs:367`) asserts
`⊤≠⊥` in the shared `EqualityEngine` at the **current** decision level but
caches `self.truth` permanently. Its only trigger is `Euf::new_var`'s
catch-all arm (`crates/shinri-euf/src/solver.rs:89–103`), which
`Combiner::bind_fresh` reaches mid-search for interned Boolean connectives
and DT tester atoms (`combiner.rs:374`ff). A pop below that level drops the
disequality and the cache prevents reinstalling it: `p(a)`, `¬p(b)`, `a=b`
is then accepted. The I1 comment's premise ("the combiner registers atoms at
level 0") is false under `bind_fresh`. No end-to-end wrong answer has been
demonstrated and no corpus row is attributed to it.

## 2. Scope

**In:**

* A definitional row for compound linear shared terms in
  `Arith::ensure_shared_var` (§3).
* Eager, base-level installation of the ⊤/⊥ sentinels (§4).
* Tests and oracle-generator coverage for both (§6); a measurement run and
  report (§7).

**Out** (queued in §10): the `get-value` printer, a post-hoc UFLIA model gate
(approach B), the `Owner::Shared` definitional merge, `pending` backtracking,
blocksworld re-index churn, the QF_S wrong rows, the `blast_word` panic
bucket.

## 3. The fix: definitional rows for compound shared terms

### 3.1 Change

In `Arith::ensure_shared_var(ctx, t)`, after interning `v_t`:

1. If `t` is a numeral: unchanged (slice-42 pin).
2. Else if `t`'s top symbol is `Add`, `Sub`, `Neg`, or a linear `Mul` (at
   most one non-numeral factor): `linearize(t)` to `(Σ qᵢ·xᵢ, c)`, build the
   canonical `LinComb` of `(v_t, 1)` and each `(xᵢ, −qᵢ)` (coalesced, sorted,
   zero coefficients dropped), take `s = vars.slack_var(comb)`, and
   `tableau.define_slack(s, comb)` if `s` is new. Pin `s` to `[c, c]` with a
   `fresh_sentinel()` literal, with the numeral path's "skip if already pinned
   to this value" idempotence. Mark `v_t` constrained (`mark_constrained`);
   see *Constrainedness* below.
3. Else (UF application, `str.len`, any other opaque leaf): unchanged.

**Constrainedness (slice 42 interaction).** `entailed_equalities` and
`model_equal_shared_pairs` skip every pair containing a variable whose
interface class is not constrained. Today `v_(+ a 1)` is never marked, so
both skip it. That is the second half of why §1.2 never connects `f(a+1)`
with `f(1)`. Once the row exists, `v_t` is no longer free to shift on its
own. `mark_constrained(v_t)` is the chosen treatment because it errs toward
*more* probing, which slice 42 documents as the sound direction: probing
still decides entailment exactly, and an MBTC split on a non-entailed pair is
a tautology. The alternative is to join `v_t` into its leaf's class, as
`union_interface_class` does, when the row is a pure unit difference
(`v_t − x = c`). That is more precise but only a performance refinement. It is
banked (§9), to be un-banked if criterion 6 attributes slowdowns to extra
probing.

The existing numeral path is kept as it is.

The linearization must reuse `normalize::linearize`, which interns leaves as
problem variables. The resulting comb is `v_t − (a + 1)`, so after coalescing
the row is `v_t − a = 1`.

**Degenerate combs.** If coalescing leaves `v_t` alone (`t` linearizes to a
constant, e.g. `(+ 0 1)` if the frontend has not folded it), the pin is on `v_t`
directly, as for a numeral. `v_t` never cancels against itself, because it is a
fresh variable distinct from every leaf of `t`.

**Int-ness.** `v_t` is Int-stamped by `problem_var_sorted` (unchanged). With
integral coefficients and constant the row keeps branch-and-bound sound. A
Real-sorted `t` (QF_UFLRA) gets the same row with no integrality.

### 3.2 Why this survives backtracking

Tableau rows and slack interning are permanent across a solve. Bounds are
trailed, so a pin installed at level *k* is undone by a pop below *k* — the
same "registration-created state scoped to the current level" class as
slice 49. It is still safe, for the same reason the existing numeral pins
are: `drive_final_check` recomputes the shared set and re-calls
`ensure_shared_var` for every member at **every** final check, before any
`Sat` is returned. Between final checks a missing pin can only make arith
weaker, never unsound, and the sentinel literal is dropped by `explain`, so
every conflict stays justified by input literals. This invariant goes in a
comment on `ensure_shared_var`.

### 3.3 What it does not change

`linearize`, atom encoding, `entailed_equalities` and MBTC are untouched.
They now read a variable whose value is `a + 1` in every simplex solution.

## 4. The fix: eager ⊤/⊥ sentinels

1. Add `Combiner::install_truth_terms(&mut self, t_true, t_false)`. It calls
   `euf.set_truth_terms(t_true, t_false)`, then builds a `TheoryCtx` and
   calls the EUF method that runs `EGraph::truth_nodes` (a new
   `Euf::install_truth(&mut self, cx)` wrapper). This is before solving, at
   the solve's base level.
2. Replace the `.euf_mut().set_truth_terms(...)` call at
   `crates/shinri-solver/src/lib.rs:1242` with `install_truth_terms`. That
   site is already required to run before any atom encoding.
3. Keep the lazy call in `Euf::new_var`'s catch-all arm. After step 2 it is a
   cache hit; it still serves standalone-EUF tests that only call
   `set_truth_terms`.
4. `debug_assert!` in `truth_nodes`' installing branch (cache miss) that the
   equality engine is at its base level, so a future mid-search install fails
   in tests rather than silently.
5. Rewrite the I1 comment in `new_var`: installation is eager in
   `install_truth_terms`, because `bind_fresh` can register atoms above
   level 0.

## 5. Tasks

Each task is test-first. Its new tests are run on pre-slice `main` and the
failure is recorded in the task report before the fix lands.

1. **Pin the Wisa mechanism.** Add the §1.2 repro and its `(+ a 0)` and
   `(* 2 a)` variants to `crates/shinri-solver/tests/uflia_e2e.rs`, and an
   arith unit test: `ensure_shared_var((+ a 1))`, assert `a = 0`,
   `check_full` → the shared variable's value is 1 (and `v ≠ 1` conflicts).
   Then confirm that `xs-05-08-4-2-5-4.smt2` reduces to §1.3, by delta
   debugging or by showing it answers `unsat` once Task 2 is in. **If the
   reduction exposes a second, independent mechanism, stop:** the slice steps
   up to approach B (§9), and the spec is amended before continuing.
2. **Definitional row** (§3), with a backtracking test: final check at
   level 1 installs the row and pin, pop to 0, re-enter at level 1 with the
   same constraints → still `unsat`.
3. **Eager ⊤/⊥** (§4). The slice-49 report's `Euf`-level repro becomes a
   permanent test, plus a combiner-level test: `bind_fresh` of a Boolean
   connective at level 1, pop to 0, assert `p(a)`, `¬p(b)`, `a=b` → conflict.
4. **Oracle coverage.** Check whether the QF_UFLIA/QF_UFLRA oracle generators
   (`crates/shinri-solver/tests/oracle.rs`,
   `crates/shinri-theory/tests/oracle.rs`) ever emit a UF application with a
   compound arithmetic argument. If none do, add that shape. This is the gap
   that let §1 through.
5. **Measurement run and report** (§7).

## 6. Testing

* `cargo nextest run -p shinri-solver --features oracle`, **unfiltered**,
  confirming a non-zero discovered count.
* `cargo nextest run -p shinri-solver -E 'binary(uflia_e2e)'`, non-zero
  count.
* `cargo nextest run -p shinri-arith` and `-p shinri-euf`.
* `mise run lint` (fmt + clippy `-D warnings`).
* No new test may exceed the blocking-tier budget in `AGENTS.md`.

## 7. Measurement

Run-id `slice50`, same limits as the baseline (20 s / 3072 MB / 6 jobs):

```
BENCH_LOGICS=QF_UF,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA,QF_DT BENCH_RUN_ID=slice50 mise run bench-run
```

Reported to `docs/superpowers/research/2026-09-29-smtlib-2024-slice50-uflia-report.md`,
with per-logic transition matrices against the most recent committed run
covering each logic.

### Comparison baselines

| logic | comparison run | total | correct | wrong | timeout | other |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| QF_DT | `slice49` | 8,700 | 8,105 | 0 | 584 | unknown 11 |
| QF_UF | `slice49` | 7,503 | 7,111 | 0 | 358 | parse-error 34 |
| QF_UFLIA | `slice49` | 659 | 104 | 11 | 522 | oom 5, unknown 17 |
| QF_UFLRA | `slice49` | 1,284 | 44 | 0 | 1 | parse-error 1,229, oom 10 |
| QF_S | `slice49` | 18,940 | 16,023 | 2 | 9 | unknown 2,809, unverified 97 |
| QF_SLIA | `baseline-8de004d44944` | 84,395 | 24,799 | 37 | 41 | parse-error 195, unknown 58,063, unverified 1,260 |

### Success criteria

| # | criterion | gate |
| --- | --- | --- |
| 1 | Tasks 1–3's tests each failed on pre-slice `main` (recorded) and pass now | **hard** |
| 2 | §1.2 repro and `xs-05-08-4-2-5-4.smt2` answer `unsat` | **hard** |
| 3 | `correct → wrong` transitions, all six logics | **0 — hard** |
| 4 | QF_UFLIA `wrong` | **≤ 11 — hard**; which rows moved, and to what, is reported per row |
| 5 | per-logic `correct` | **≥ comparison run — hard**, excluding only rows an A/B re-run shows flip identically on pre-slice `main`. QF_S excludes `instance10273` (oracle-boundary row); QF_UF expects ±5–10 `qg5` boundary rows. An oracle-side flip (verdict `correct ↔ unverified` with an identical shinri answer) counts as noise. Every excluded row is listed. |
| 6 | `correct → {timeout, unknown, oom}` transitions | **measured**; each row A/B-timed on pre-slice `main`, and those confirmed slower are reported as the slice's cost |
| 7 | `* → wrong` from a non-`correct` verdict | **measured**; each row checked for whether pre-slice `main` gives the same wrong answer with a longer timeout |
| 8 | QF_SLIA `wrong` delta; QF_S 2 wrong rows | **measured, not gated** |

**No causal claim without a trace.** Only `xs-05-08-4-2-5-4` is tied to §1.3,
and only by Task 1. Criterion 4 claims no number. Any row that moves is
reported, but none is attributed to this slice without a reduction or trace.
The sentinel task (§4) is expected to move no corpus row; if a row moves in
QF_DT or QF_UF, the report says so and does not attribute it.

## 8. Named reproducers

* §1.2 (3 assertions) — `uflia_e2e.rs`.
* `QF_UFLIA/mathsat/Wisa/xs-05-08-4-2-5-4.smt2` — corpus row.
* Slice-49 report's `Euf`-level sentinel repro — `shinri-euf` test.

## 9. Banked, not built

**Approach B — a `uflia-model-rejected` gate.** Evaluate every input
assertion under the built model and answer `unknown` on a violation,
mirroring `str-model-rejected` and `abv-model-rejected`. Banked because §1.3
is a single named mechanism with a local fix, and because today's model
output (`(+ a 1) ↦ 0`, purification names) suggests the evaluator a gate
would rely on is itself affected by §1.3. **Un-bank** if Task 1 finds a
second independent mechanism, or if criterion 4 leaves Wisa rows `wrong`
with no named cause.

**Unit-difference class join** (§3.1, *Constrainedness*). Join `v_t` into its
single leaf's interface class instead of marking it constrained when the row
is `v_t − x = c`, matching slice 42's treatment of interface equalities.
**Un-bank** if criterion 6's A/B timing attributes `correct → timeout` rows to
additional `entailed_equalities` or MBTC probing over compound shared terms.

**Approach C — the gate alone.** Rejected: it banks a known
combination-soundness hole and turns 11 rows into `unknown`, never `correct`.

## 10. Queued for the next slice

* **`get-value` echoes purification names.** `(get-value ((+ a 1)))` prints
  `(t9 0)` instead of `((+ a 1) 1)`. This is cosmetic, but it is wrong
  SMT-LIB output. Once §3 lands, the value is right and only the printed
  term is wrong.
* **Approach B's gate** (§9), if it is un-banked.
* Carried from slice 49 unchanged: the `Owner::Shared` definitional merge
  (`combiner.rs:185`, unverified); `pending` is not backtracked; the
  blocksworld re-index churn measurement; the QF_S wrong rows
  (`instance09174`, `instance10773`); the `blast_word` panic bucket.

## 11. References

* Slice 49 spec and report —
  `docs/superpowers/specs/2026-09-11-shinri-slice49-euf-midsearch-index-design.md`,
  `docs/superpowers/research/2026-09-11-smtlib-2024-slice49-euf-report.md`
  (`## Queued for the next slice`: the sentinel hazard and its `Euf`-level
  repro).
* Baseline — `docs/superpowers/research/2026-09-09-smtlib-2024-baseline.md`
  (§ Next slices, rank 3) and `2026-09-09-smtlib-2024-baseline-report.md`.
* Slice 42 — the numeral-pin path in `ensure_shared_var` that §3 extends.
* Code: `crates/shinri-arith/src/lib.rs:648` (`ensure_shared_var`),
  `crates/shinri-arith/src/normalize.rs:106` (`linearize`),
  `crates/shinri-arith/src/vars.rs` (`problem_var_sorted`, `slack_var`),
  `crates/shinri-theory/src/combiner.rs` (`drive_final_check`, `bind_fresh`),
  `crates/shinri-euf/src/egraph.rs:367` (`truth_nodes`),
  `crates/shinri-euf/src/solver.rs:18,89–103` (`set_truth_terms`, `new_var`),
  `crates/shinri-solver/src/lib.rs:1238–1243`.
