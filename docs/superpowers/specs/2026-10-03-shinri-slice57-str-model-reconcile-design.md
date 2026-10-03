# Slice 57 — String model reconciliation for multi-concat classes

Status: design approved in chat 2026-10-03. Picks up the engine part of the
slice-56 report's queue item 2 (`docs/superpowers/research/2026-10-03-smtlib-2024-slice56-uf-bool-const-report.md`,
§ Queued for the next slice): "the string engine accepts a premature SAT that
depends on the SAT decision order over its split atoms". Scope ruling
(owner, in chat): engine fix only; of the three approaches in §3, approach 1
now, approach 2 queued as its own spec. Bare-E, the `Not(Eq)` arm removal and
the axiom memory measurement are not in this slice.

**Area:** `shinri-str` (`model.rs`, `StrSolver::model_with` in `lib.rs`),
`shinri-theory` (one field on `ModelBuilder`), `shinri-solver` (the string
model gate). Tests in `shinri-str` (unit), `shinri-solver` (unit, new
`slice57_probes`, a new oracle family in `qfs_differential.rs`). No parser,
SAT, Combiner search, word-equation (`wordeq.rs`) or `lower` change.

## 1. Summary

### 1.1 The regression (measured at `46d5fd9`)

Slice 53's three arithmetic-`=` axiom clauses turned trivially satisfiable
string inputs into `unknown fence=str-model-rejected`. The slice-53 base
binary (`target/slice53-base/shinri`, built from `2ceef06`) answers them:

| input (QF_SLIA, `x` String) | slice53-base | HEAD | z3 |
| --- | --- | --- | --- |
| `(= (str.len x) 3)`, `(str.prefixof "cd" x)` | `sat` `"cdH"` | `unknown` | `sat` |
| `(= (str.len x) 3)`, `(str.suffixof "c" x)` | `sat` `"GGc"` | `unknown` | `sat` |
| `(= (str.len x) 3)`, `(str.prefixof "\\" x)` | `sat` | `unknown` | `sat` |
| `(>= (str.len x) 3)`, `(<= (str.len x) 3)`, `(str.prefixof "cd" x)` | `sat` | `sat` | `sat` |

The three stringfuzz-lu loss rows from the slice-53 report have the same
shape (`QF_SLIA/20230327-stringfuzz-lu/transformed/z3str2/regex-050-*.smt2`;
each is 4 assertions, `len`, `x = y`, a `str.in_re` and a `str.prefixof` —
the slice-53 report said 3 and omitted the `prefixof`):

| row | expected | HEAD |
| --- | --- | --- |
| `multiply-reverse-fuzz` | `sat` | `unknown` (`str-model-rejected`) |
| `translate-rotate-fuzz` | `unsat` | `unknown` (`str-model-rejected`) |
| `translate-graft-translate` | `unsat` | `unknown` (`str-model-rejected`) |

### 1.2 Mechanism (traced with throwaway debug output, not committed)

`len x = 3 ∧ prefixof "cd" x`:

1. The reduction gives the input equation `x = "cd" ++ !pfx0`. The axioms
   change the SAT search so that the word-equation loop char-peels it:
   `x = "" ∨ x = "c" ++ !strk0` (a minted equation), and the second disjunct
   is taken.
2. `x`'s EUF class now holds two concats. The input equation resolves as
   `["c", !strk0]` vs `["cd", !pfx0]`: both heads are constants, one a
   proper prefix of the other, so `resolve_inner` falls through to `Done`
   (`crates/shinri-str/src/wordeq.rs:1056`; pinned by
   `prefix_of_constant_is_done_not_conflict`).
3. Patching (2) to strip the common prefix only moves the stall: the next
   char-peel `!strk0 = "d" ++ !strk1` is emitted, but the single-level
   normal form never expands `!strk0` to its class concat (deep expansion
   is deliberately excluded on the conflict/split path for citation
   reasons), so the peel dedups to `Saturated`. `check` treats `Saturated`
   like `Done` (`crates/shinri-str/src/lib.rs:892`).
4. The model builder (`model.rs::value_of`) values `x` from the FIRST
   class concat `class_member` finds — here the minted `"c" ++ !strk0`.
   Arith has no length for the minted skolems (the per-concat length link
   is deliberately not emitted for minted equations, `lib.rs:457–489`), so
   the length guard discards it and `x` gets the free fill `"DDD"`. The
   gate rejects: `(= x (str.++ "cd" !pfx0))` evaluates to false.

`len x = 3 ∧ suffixof "c" x` differs at step 1: the F-split mints
`!sfx0 = x ++ !strk1` next to the input `x = !sfx0 ++ "c"`, an infeasible
cycle that arith cannot refute without minted length links. The builder
walks `x → !sfx0 ++ "c" → x ++ !strk1`, hits its cycle guard, and the
failed attempt's values poison the memo, so `x` again ends as `"DDD"`.

In both shapes a genuine witness exists that satisfies every INPUT
assertion (`"cdH"`, `"GGc"`), using only the arith lengths of the input
variables and treating the minted equations as non-binding. "Decision
order" decides whether the search reaches a multi-concat class at all; the
model builder's failure on such a class is what turns it into `unknown`.

### 1.3 Throwaway probes (not kept)

| change | `cd` / `\\` prefix | `suffixof "c"` | multiply-reverse | rotate, graft |
| --- | --- | --- | --- | --- |
| prefix strip in `resolve_inner` | unknown | unknown | unknown | unknown |
| builder tries every class concat, keeps a length-consistent one | **sat** | unknown | **sat** | unknown |

The suffix shape additionally needs memo hygiene and minted-cycle handling
(§4.2).

## 2. Scope

In scope:

- Make the string model builder produce a witness for a class with several
  concats, or a cycle through a minted concat, when one exists given the
  arith lengths (§4).
- A strict gate for any model the new path produced, so it cannot add a
  wrong `sat` (§4.3).

Out of scope (queued, §9):

- Any `unsat` gain: `translate-rotate-fuzz` and `translate-graft-translate`
  need the engine to derive a conflict (approach 2).
- `wordeq.rs`, the minted-equation length link, `Saturated` handling.
- Bare-E, removal of the `Not(Eq) → (or Lt Gt)` arm, the axiom memory
  measurement (slice-56 queue item 2's other parts).

## 3. Approaches considered

1. **Model-side reconciliation (chosen).** Rebuild the string model when
   the default build violates an input equation, preferring input concats,
   with length checks and memo hygiene. Small, confined to model
   construction, cannot change an `unsat`, and every adopted rebuild passes
   a strict gate. Gains only `sat`.
2. **Engine-side reconciliation (queued).** Partial constant-head strip, a
   cited deep normal form for the conflict/split path, and sound length
   links for minted equations, so `check` reaches a conflict or a genuine
   fixpoint instead of `Saturated`. The only route to the `unsat` rows, but
   it reopens two areas with wrong-UNSAT history (E1 ce1–ce8; the minted
   length-link conflict, `lib.rs:476–480`). Its own slice.
3. **Encoding-side:** emit the slice-53 axioms only for arithmetic `=` atoms
   in non-positive positions. Restores the base binary's behaviour on the
   regressed shapes but leaves the builder's multi-concat failure in place
   for every other route into that state. Rejected as masking.

## 4. Design

### 4.1 Default build, then self-check

`StrSolver::model_with` (`crates/shinri-str/src/lib.rs:1562`) builds the
model exactly as today (`model::assign`). It then evaluates every INPUT
string equation — each `eq_true` entry whose atom is not in `minted_eqs`,
including a `Distinct` asserted false — under the built values (both sides
assembled with the same concat evaluation `model.rs` already uses). If all
hold, it returns. This path is bit-identical to HEAD, so every row that is
`sat` today keeps its model.

A side that cannot be fully evaluated (a missing value) counts as holding
for this self-check, so the rebuild is never triggered by an unevaluable
equation; the solver gate stays the arbiter.

### 4.2 Reconciliation rebuild

Only when §4.1 finds a violated input equation, `model_with` calls a new
`model::assign_reconciled` with the same inputs (`known`, `str_terms`,
membership seeds) plus the set of input equations. It starts from a fresh
memo (the default build's values are discarded) and differs from `assign`
in three rules:

1. **Input concats are authoritative.** When valuing a non-constant term
   from its class, the candidate concats are ordered: sides of input
   equations first, then other non-minted concats, then sides of minted
   equations; ties by `concat_arity` descending, then `TermId` for
   determinism. A class constant still wins over any concat, as today.
2. **Transactional, length-checked candidates.** Each candidate is valued
   against a scratch copy of the memo. It is accepted only if its word's
   length equals the class length in the arith model
   (`class_len_in_model`); then the scratch memo is committed. A rejected
   candidate leaves no values behind (fixes the suffix-cycle poisoning).
   If no candidate is accepted, the term gets `free_fill` of the class
   length, as today.
3. **Minted cycles fill freely.** Re-entering a term that is in progress
   through a minted concat yields `free_fill` of that term's own class
   length and does not commit the enclosing candidate's partial values.

The concat-first pass of `assign` (top-level concats sliced before their
operands are valued) is kept, restricted to input-equation concats and
ordered as in rule 1.

The rebuild is adopted only if every input equation holds under it (the
§4.1 check). Otherwise the default model is kept unchanged and the solver
gate rejects it as today.

### 4.3 Strict gate for rebuilt models

`ModelBuilder` (`crates/shinri-theory/src/model.rs:11`) gains a boolean
field (working name `needs_strict_check`, default `false`) with a setter
and a getter. `model_with` sets it when it adopts a rebuild. The field must
survive `Combiner::build_model` (`combiner.rs:951`; strings build into the
shared builder last) and any `ModelBuilder` merge on that path.

In `Solver` (`crates/shinri-solver/src/lib.rs:1490`), when the flag is set,
`string_model_satisfies` runs in strict mode: every top-level assertion in
`lowered` must evaluate to `Some(true)`; `Some(false)` or `None` rejects
(fence `str-model-rejected`, unchanged). Without the flag the gate is
3-valued exactly as today.

Rationale: `eval_bool` (`lib.rs:1594`) returns `None` for terms it cannot
evaluate (`str.<`/`str.<=`, compound arithmetic, UF applications, among
others), and the 3-valued gate treats `None` as satisfied. A rebuilt model
changes string contents the engine's own reasoning did not produce, so it
could violate such a constraint unseen. Under the strict gate a rebuilt
model yields `sat` only when every assertion is positively confirmed; rows
it cannot confirm stay `unknown`, which they are today. The only verdict
this slice can add is `sat`, and only through that check.

The int-conv model repairs (`lib.rs:1469`) run before the gate, as today,
and are unaffected.

## 5. What this does not change

The SAT core, the Combiner's search and theory dispatch, `wordeq.rs`, the
string engine's `check`, `lower`, the parser, and every non-string path.
The default model build and the 3-valued gate are unchanged for any model
whose default build satisfies its input equations.

## 6. Tasks

1. **Base run.** `slice57-base` at `46d5fd9` over QF_S, QF_SLIA, QF_LIA
   (§8). Build the base binary first and run it detached (slice-53 ruling
   R1), so later commits do not block a resume.
2. **Failing tests first.** `slice57_probes.rs` (§7.3) and the oracle
   family (§7.4). Record that the probes fail and the oracle's
   `unknown`-where-z3-`sat` count at HEAD as "before" evidence.
3. **`ModelBuilder` flag and strict gate** (§4.3), with the §7.2 unit tests
   first.
4. **Self-check and reconciliation rebuild** (§4.1–4.2), with the §7.1 unit
   tests first.
5. **Gates and re-run.** `mise run ci`, the oracle suite, then `slice57`
   over the same logics, the report, and a *Measured outcomes* section
   appended to this spec.

## 7. Testing

### 7.1 Unit (`shinri-str`, `model.rs` tests)

- A model whose default build satisfies every input equation is returned
  unchanged, flag not set.
- Char-peel class: `x ≈ "cd" ++ !pfx0` (input), `x ≈ "c" ++ !strk0`
  (minted), `len x = 3` → rebuild values `x` as `"cd"` plus one character,
  flag set.
- Suffix cycle: `x ≈ !sfx0 ++ "c"` (input), `!sfx0 ≈ x ++ !strk1`
  (minted), `len x = 3`, `len !sfx0 = 2` → `x` ends in `"c"`, length 3;
  a rejected candidate leaves no memo entries.
- A rebuild that still violates an input equation → the default model is
  kept, flag not set.

### 7.2 Unit (`shinri-solver`)

- With the flag set, the strict gate rejects an assertion that evaluates to
  `None` (e.g. one containing `str.<`) and accepts an all-`Some(true)` set.
- Without the flag, a `None` assertion is still accepted (3-valued, as
  today).

### 7.3 End to end (`crates/shinri-solver/tests/slice57_probes.rs`, blocking tier)

- `sat`, with the printed model re-checked against the input assertions:
  `len x = 3` with `prefixof "cd"`, `prefixof "\\"`, `suffixof "c"`; each
  also with the length as `(>= …) (<= …)`; `multiply-reverse-fuzz`
  inlined.
- `unsat` siblings: `len x = 1 ∧ prefixof "cd" x`,
  `len x = 0 ∧ suffixof "c" x`.
- Known-`unknown` pins, each with a reason string naming the queued
  engine-side item: `translate-rotate-fuzz`, `translate-graft-translate`
  (inlined; z3 `unsat`).
- Strict-gate pin: a shape that task 2 confirms reaches the rebuild (its
  default build is rejected at HEAD), conjoined with an unevaluable
  constraint such as `(str.< x "zzz")`. Expected `unknown`: the rebuild is
  adopted but the strict gate cannot confirm `str.<`. The §7.2 unit tests
  pin the strict logic itself.

### 7.4 Oracle (feature `oracle`, `qfs_differential.rs`)

New test `differential_qfs_model_reconcile`, reusing the file's harness
(verdict comparison and the `get-value` witness re-check with z3). A
seeded LCG generator builds scripts over 1–2 String variables with 1–3
constraints from `str.prefixof` / `str.suffixof` / `=` against a concat
with a constant, a `str.len` pin written as `=`, as `<=`+`>=`, or absent,
and optionally a `str.in_re` over a small character range. 300 scripts.

- Before (task 2): record the number of scripts where shinri says
  `unknown` and z3 says `sat`; it must be non-zero (evidence the family
  reaches the defect). If it is zero, strengthen the generator until it is
  not.
- After: 0 verdict disagreements, 0 witness failures, and that count
  strictly lower than before. Record sat/unsat/unknown counts.
- Runtime target under 60 s.

Run with `cargo nextest run -p shinri-solver --features oracle`; a filtered
run uses `-E 'test(differential_qfs_model_reconcile)'`. Confirm a non-zero
discovered count. The existing `qfs_differential` and `qfs_fuzz_corpus`
tests stay green.

## 8. Measurement

Two `mise run bench-run` runs at default limits (20 s, 3072 MB, 6 jobs):
`slice57-base` at `46d5fd9` and `slice57` at the slice head, over QF_S and
QF_SLIA (the string path) and QF_LIA (shares the solver path; the change
cannot reach it, so it is a no-movement check).

Every changed row that starts or ends in `correct` is re-run 3× per binary,
interleaved, with the bench's command line (slice-53 triage method). Large
groups may use a stratified sample, stated with its size.

### Success criteria

| # | criterion | kind |
| --- | --- | --- |
| 1 | 0 rows `* → wrong` in all 3 logics; 0 wrong answers in triage re-runs | hard; any hit stops the slice for a ruling |
| 2 | the three §1.1 shapes and `multiply-reverse-fuzz` answer `sat` | hard |
| 3 | `unknown:str-model-rejected` decreases in QF_S + QF_SLIA; every `→ correct` group triaged | hard (direction), measured (size) |
| 4 | every `correct → *` row triaged; net `correct` ≥ 0 per logic. A net loss stops the slice for a ruling | hard |
| 5 | §7.4 shows the before/after movement with 0 disagreements and 0 witness failures; oracle discovered count non-zero; `mise run ci` green | hard |
| 6 | median/p90 ms per logic reported against `slice57-base` (the rebuild runs only on default-rejected models, so expected neutral) | measured |

## 9. Queued for the next slice

1. **Engine-side reconciliation (approach 2).** Partial constant-head strip
   in `resolve_inner` (`wordeq.rs:1056` returns `Done` for a
   constant-prefix residual), a cited deep normal form on the
   conflict/split path, and sound length links for minted equations.
   Reproducers: `translate-rotate-fuzz`, `translate-graft-translate`
   (`unsat`), and the §1.2 shapes reached without the model-side fix.
2. **Bare-E and `Not(Eq)` arm removal**, after (1): the R6 probes
   (`slice33_probes::probe_c_len_zero_var`,
   `script_e2e::user_pfx_name_declared_before_any_mint_still_works`) are
   the acceptance test.
3. **Axiom memory measurement** (slice-53 carry).
4. Every other item of the slice-56 report's queue, unchanged.

## 10. References

- Slice-56 report, § Queued for the next slice (item 2).
- Slice-53 spec `docs/superpowers/specs/2026-10-01-shinri-slice53-arith-eq-polarity-design.md`
  (§12, ruling R6) and report
  `docs/superpowers/research/2026-10-02-smtlib-2024-slice53-arith-eq-polarity-report.md`
  (*Attribution*, the stringfuzz trio).
- Code:
  - `crates/shinri-str/src/model.rs:88` (`assign`), `:136` (`value_of`),
    `:358` (`class_member`)
  - `crates/shinri-str/src/lib.rs:1562` (`model_with`), `:457–489`
    (length link, minted skip), `:884–892` (`Done`/`Saturated`)
  - `crates/shinri-str/src/wordeq.rs:1056` (fall-through `Done`)
  - `crates/shinri-theory/src/model.rs:11` (`ModelBuilder`),
    `combiner.rs:951` (`build_model`)
  - `crates/shinri-solver/src/lib.rs:1490` (gate call), `:1520`
    (`string_model_satisfies`), `:1594` (`eval_bool`)

## 11. Measured outcomes

Full evidence:
`docs/superpowers/research/2026-10-03-smtlib-2024-slice57-str-model-reconcile-report.md`.

| # | criterion | result |
| --- | --- | --- |
| 1 | 0 `* → wrong`; 0 wrong answers in triage | PASS. 0 `wrong` and 0 `* → wrong` in 116,641 rows, 0 wrong answers in 1,440 triage runs (240 rows × 3 × 2 binaries). Unverified-z3 check: 5 changed `unverified` rows, 0 z3 `unsat`. 3 are z3 `sat`. The other 2 are shinri `unsat` with no z3 answer in 60 s, and cvc5 gives `unsat` |
| 2 | §1.1 shapes and `multiply-reverse-fuzz` answer `sat` | PASS. `slice57_probes` 16/16 at `57743db` (before: 5 of 15 failing). The bench row `multiply-reverse-fuzz` is `correct`, `sat` 3/3 in triage |
| 3 | `str-model-rejected` decreases in QF_S + QF_SLIA | FAIL on raw counts, PASS credited (needs a ruling). Raw: QF_S 966 → 967, QF_SLIA 3,122 → 3,122 (combined +1). The +1 is two `timeout → str-model-rejected` rows. The base binary also rejects them 3/3 in isolation: it timed out on them only under bench load. Credited: QF_S 967 → 967, QF_SLIA 3,123 → 3,122 (−1, `multiply-reverse-fuzz`) |
| 4 | `correct → *` triaged; net `correct` ≥ 0 per logic | PASS. The 12 `correct → *` rows (QF_LIA) give the correct `sat` 3/3 on both binaries, so none is reproducible. Net `correct`, raw: QF_S +5, QF_SLIA +115, QF_LIA +84. Credited: QF_S 0, QF_SLIA +1, QF_LIA 0. The rest is noise: load timeouts, and z3-oracle timeouts in the base run |
| 5 | oracle before/after, 0 disagreements; `ci` green | PASS. `differential_qfs_model_reconcile`: before 48 sat / 179 unsat / 73 unknown (48 with z3 `sat`); after 61 / 179 / 60 (35 with z3 `sat`); 0 disagreements, 61 witnesses, 1 test discovered. `mise run ci` at `57743db`: 1,719/1,719 passed, 7 skipped |
| 6 | median/p90 ms per logic | Neutral. Bench, rows `correct` in both runs, base vs after (ms): QF_S median 19 vs 5, p90 49 vs 13; QF_SLIA 29 vs 5, p90 79 vs 15; QF_LIA 86 vs 63, p90 1,986 vs 1,618. The base run was slower throughout its run. A serial interleaved sample of 100 rows per logic is equal: QF_S median 4/4 ms, p90 8/9 ms; QF_SLIA 4/4, p90 17/16; QF_LIA 45/49, p90 622/635; summed times within 0.5% |

### Deviations from this spec

- §7.3 strict-gate pin: `(str.< x "zzz")` is gate-evaluable after lowering
  (answers `sat`, z3 `sat`). The pin now uses
  `(<= (- (str.len x) (str.len y)) 1)`, and the `str.<` script is kept as a
  positive `sat` probe.
- The rf2 leak probe was made gate-unevaluable the same way (final review),
  since its `str.<` query could not fail.
- Concat/operand consistency: rebuilt concat values join their operands,
  the adoption check composes concats, and a `concats_consistent` guard was
  added (not in §4.2).
- A candidate-trial budget (4 × |known| + 64) with an undo log bounds the
  rebuild. When it runs out, the rebuild is abandoned and the default model
  is kept. §4.2 does not mention cost.
- Two existing pins were moved in the sound direction:
  `script_e2e::str_input_var_concat_length_decides` changed from `unknown`
  to `sat` (z3 `sat`, witness checked), and `slice52_probes::bool_proxy`
  changed from a known wrong `sat` to `unknown`.
- The final whole-branch review ran before Task 5, while the base bench ran.
- The §7.4 generator is unchanged (before count 48). No `known` reordering
  was needed.
- Criterion 3 is met only on credited counts (above).
- Queued: the solver gate's `eval_str_val` reads a concat's stored value
  before composing its operands. Making the gate compose first is its own
  measured slice, because it changes default-path verdicts (§5).
