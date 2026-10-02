# Slice 56 — Atomic Bool constants as UF arguments: an excluded-middle definition in `word_norm`

Status: design approved in chat 2026-10-02. Picks up the first item of the
slice-55 report's queue
(`docs/superpowers/research/2026-10-02-smtlib-2024-slice55-get-value-report.md`,
`## Queued for the next slice`, item 1, "Wrong `sat`: a Bool constant as a
UF argument"). The slice-55 spec §9 named the `Not(Eq)` / bare-E /
string-order item "slice 56"; it stays queued, behind this soundness item
(the baseline priority rule puts `Wrong` first).

**Area:** `shinri-solver` (`word_norm.rs`: a second branch in item 3 of
`WordNorm::walk`'s non-connective loop, a new predicate, corrected doc
comments). Tests in `shinri-solver` (unit in `word_norm.rs`, new
`slice56_probes`, `bool_arg_oracle` loses its Ruling-8 exclusion). No
parser, `lower`, Tseitin, EUF, Combiner, fence, theory-crate, printer or
`get-value` change.

## 1. Summary

### 1.1 The defect

EUF ties a Bool-sorted e-node to ⊤/⊥ only when that node is also a SAT
atom: `Euf::assert` merges an asserted predicate atom with the sentinel.
Slice 54 purified *compound* Bool arguments into `bool!` proxies and left a
nullary user Bool constant `q` alone, on the premise (doc comment on
`needs_bool_proxy`) that it is "already a single atom EUF links to ⊤/⊥".
That premise holds only when `q` occurs somewhere as a Boolean atom
(slice-54 r6 asserts `q`). When `q` occurs **only** as an argument of a
non-connective parent, Tseitin never encodes it, SAT never decides it, and
EUF treats it as an opaque Bool-sorted node distinct from both `true` and
`false`. `(P q)`, `(P true)` and `(P false)` can then take three different
values. `get-model` shows the trace: `q` is bound to `@elem0`.

### 1.2 Reproducers (shinri: slice-55 binary built at `1a9db04`; z3 4.16.0)

| # | logic | assertions | shinri | z3 |
| --- | --- | --- | --- | --- |
| a1 | QF_UF | `(P q)`, `(not (P true))`, `(not (P false))` | `sat` ✗ | `unsat` |
| a2 | QF_UFLIA | `(distinct (f q) (f true) (f false))`, `f : Bool → Int` | `sat` ✗ | `unsat` |
| a3 | QF_UF | `(distinct (f q) (f true) (f false))`, `f : Bool → U` | `sat` ✗ | `unsat` |
| a4 | QF_UF | `(P q r)`, `(not (P true true))`, `(not (P false true))`, `r` | `sat` ✗ | `unsat` |
| a5 | QF_DT | `(distinct (mk q) (mk true) (mk false))`, `mk : Bool → B` | `sat` ✗ | `unsat` |
| a6 | QF_UFLRA | `(distinct (f q) (f true) (f false))`, `f : Bool → Real` | `sat` ✗ | `unsat` |
| a7 | QF_UF | `(P q)`, `(not (P true))`; `(get-value (q))` | `sat`, `((q @elem0))` ✗ | `sat`, `((q false))` |

The slice-55 report also records a1 answering `sat` under QF_UFLIA,
QF_UFBV and QF_AUFLIA headers.

Shapes already sound (same binary):

| shape as argument | shinri | status |
| --- | --- | --- |
| `(g x)`, a Bool selector over a datatype | `unsat` | linked |
| `(h r)`, a Bool-result UF application | `unsat` | linked |
| `q` when `q` also occurs as an atom (slice-54 r6) | `unsat` | linked |

### 1.3 The remedy, checked by hand

Adding `(assert (or q (not q)))` to a1 gives `unsat`, and to a5 gives
`unsat`; the slice-54 proxy by hand (`(P b)`, `(= b q)`) also gives `unsat`
on a1. Anything that makes `q` a SAT atom is enough: SAT decides it and
EUF's existing ⊤/⊥ merge does the rest. The tautology survives the whole
pipeline today (it is how the hand check works).

## 2. Scope

In scope:

- Every nullary user Bool constant that occurs as an argument of a
  non-connective parent (UF applications, datatype constructors, and any
  other non-connective `App`), in every logic that runs `word_norm`.
- Dropping the `bool_arg_oracle` Ruling-8 exclusion of `@`-valued pairs.

Out of scope:

- Bool-element arrays (`select`/`store` with Bool elements) and QF_UFBV
  Bool arguments: already fenced to a sound `unknown`, unchanged.
- Selector and UF-application Bool arguments: already sound.
- The `Not(Eq)` / bare-E / string-order item, the V2 evaluator and the rest
  of the slice-55 queue.

## 3. Design

### 3.1 The rule

In `walk`'s item 3, the loop over the rewritten arguments of a
non-connective parent gains a second branch:

```text
if needs_bool_proxy(k)            → proxy k            (slice 54, unchanged)
else if needs_excluded_middle(k)  → append (or k (not k)) via seen_defs;
                                    k stays in place
```

`needs_excluded_middle(t)` is true exactly when `t`:

1. is Bool-sorted,
2. is a nullary `Op::Uninterpreted` application, and
3. is not in `self.internal` (`bool!` proxies are already tied to their
   term by `(= b t)`; `ite!` symbols are never Bool-sorted).

`true`/`false` are `TermNode::Const` and fail condition 2. Because it reads
`self.internal`, the predicate is a `WordNorm` method (or takes the set).

The definition is built with `mk_app(Or, [k, mk_app(Not, [k])])` and pushed
through the same `seen_defs` as proxy definitions.

### 3.2 Invariants

- **No term rewrite.** The argument and its parent keep their `TermId`s; an
  assertion whose only change is this definition keeps its identical
  `TermId` (the slice-5 hard requirement). Nothing is added to
  `orig_rewrite`.
- **No new symbols.** Nothing is minted or reserved; `internal_vals`, the
  slice-55 `get-value` remap and the printer are untouched.
- **Dedupe.** Within one `normalize` call a constant gets one definition no
  matter how many argument positions it occupies. A later `check-sat`
  appends it again, as proxy definitions are; it is a tautology, so
  re-asserting it is harmless (also across `push`/`pop`).

### 3.3 Why it is sound and complete for this shape

`(or q (not q))` is valid, so appending it preserves satisfiability in both
directions: no `unsat` can be introduced, and every model of the original
is a model of the result. Its only effect is that Tseitin encodes `q` as an
atom; SAT then assigns it, and `Euf::assert` merges `q` with ⊤ or ⊥.
Congruence then forces `(P q)` to equal `(P true)` or `(P false)`, which
closes a1–a6. For a7 the model binds `q` to a real truth value, so
`get-model` / `get-value` print `true`/`false`.

### 3.4 Doc corrections

- `needs_bool_proxy`'s doc comment: drop the false "already a single atom
  EUF links to ⊤/⊥" claim for user constants and point to the new branch.
- The module doc (`//!` list, item 3): add the excluded-middle definition.

## 4. What this does not change

Parser, `lower`, Tseitin, EUF, Combiner, fences, theory crates, the
printer, `get-value`/`get-model` code. The slice-54 proxy rule is
unchanged.

## 5. Tasks

1. Probes `a1`–`a8` (§6.2) and the new unit test (§6.1), failing on `main`.
2. The rule (§3.1) and doc corrections (§3.4); update the slice-54 unit test
   `bare_constants_and_connective_children_are_not_purified`. Probes and
   unit tests pass; `mise run ci` green.
3. Oracle: drop the Ruling-8 exclusion, add the a7 family (§6.3).
4. Bench run and report (§7).

## 6. Testing

### 6.1 Unit (`word_norm.rs` test module)

- New `bare_bool_constant_argument_gets_excluded_middle_definition`:
  - `(P q)` keeps its `TermId`;
  - exactly one `(or q (not q))` is appended when `q` occurs in two
    parents (`(P q)`, `(f q)`);
  - none for `true`/`false`, for a `bool!` proxy argument, or for `q` under
    a connective (`(and q r)`).
- Updated `bare_constants_and_connective_children_are_not_purified`: still
  asserts no proxy is minted for `q`, and now expects its definition.

### 6.2 End to end (`crates/shinri-solver/tests/slice56_probes.rs`, blocking tier)

Same `verdict`/`pair` helpers as `slice54_probes`.

| # | script | expect |
| --- | --- | --- |
| a1–a6 | §1.2 | `unsat` |
| a7 | §1.2 | `sat`; `(get-value (q))` prints `((q false))`; `get-model` binds `q` to `false`, no `@` |
| a8 | a1 under `push`/`pop`, two `check-sat` | `unsat` both times |

a7 doubles as the pin that the tautology is not folded away anywhere: if it
were, `q` would print `@elem0` again.

### 6.3 Oracle (feature `oracle`, `tests/bool_arg_oracle.rs`)

- Remove the Ruling-8 exclusion: an `@`-valued pair is no longer skipped
  and counted as `n_abstract`; it is sent to z3 like any other, so an
  abstract value fails the test. Drop the `n_abstract` counter.
- Add a family whose UF arguments include bare Bool constants that occur
  nowhere else (the a1/a7 shapes).
- Gate:
  `cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle) | binary(qfdt_oracle) | test(differential_qf_uflia_compound_args)'`
  — non-zero discovered count, 0 disagreements, 0 z3 rejections.

## 7. Measurement

One after-run, compared against the existing slice-55 run
(`bench/results/slice55/`, binary `target/slice55-after/shinri`, md5
`6a753b2e1c088e0eefefc0a5ae4b1b38`). Same settings: logics QF_UF, QF_DT,
QF_UFLIA, QF_UFLRA; `--timeout 20 --mem-mb 3072 --jobs 6`; launched
detached under `taskset -c 12-23`. Report:
`docs/superpowers/research/<date>-smtlib-2024-slice56-uf-bool-const-report.md`,
with the carried queue minus this item.

Every `correct → *` row is re-run 3× on both binaries (slice-55 Ruling 3);
only reproducible differences count.

### Success criteria

| # | Criterion |
| --- | --- |
| 1 | a1–a8 pass; all eight fail on `main` |
| 2 | Bench: 0 `wrong`, 0 panic, and no reproducible `correct → *` loss |
| 3 | Oracle: non-zero test count, 0 disagreements, no `@` values |
| 4 | `mise run ci` green, `cargo fmt --all` clean |

## 8. Approaches not taken

- **A — proxy atomic constants too** (widen `needs_bool_proxy`). Same size
  of diff, but mints a `bool!` symbol and an equivalence for every argument
  occurrence of every Bool constant, including the common case where `q` is
  already an atom. More search perturbation across QF_UF (the
  QG-classification rows sit on the 20 s limit) and more proxies through
  the remap and model plumbing.
- **C — register the atom directly** (Tseitin `encode(q)` without a
  clause, after `word_norm`). Needs a new interface out of `word_norm` or a
  second term walk, and relies on the SAT heuristic deciding variables that
  occur in no clause — one more invariant to verify.

## 9. Queued for the next slice

- The slice-55 queue, items 2 onwards, carried unchanged (`Not(Eq)` /
  bare-E / string-order first).

## 10. References

- Slice-55 report:
  `docs/superpowers/research/2026-10-02-smtlib-2024-slice55-get-value-report.md`
  (*Defect found*; `## Queued for the next slice`, item 1).
- Slice-54 spec: `docs/superpowers/specs/2026-10-02-shinri-slice54-uf-bool-arg-purify-design.md`
  (§1.1, §3.1; r6).
- Slice-55 spec: `docs/superpowers/specs/2026-10-02-shinri-slice55-get-value-echo-remap-design.md`.
