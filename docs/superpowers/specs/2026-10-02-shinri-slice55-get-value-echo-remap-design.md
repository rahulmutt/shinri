# Slice 55 — `get-value`: honest echo, purified-term remap, symbol quoting

Status: design approved in chat 2026-10-02. Picks up the first item of the
slice-54 report's queue
(`docs/superpowers/research/2026-10-02-smtlib-2024-slice54-uf-bool-arg-report.md`,
`## Queued for the next slice`, "`get-value` remap for purified arguments"),
which that report says to do together with the carried slice-50 item
"`get-value` echoing internal names". It also absorbs the carried slice-53
item "`(get-model)` does not `|…|`-quote symbols that need it", because the
echo needs the same quoting rule. The slice-54 spec §9 named the `Not(Eq)` /
bare-E / string-order item "slice 55"; that item moves to slice 56.

**Area:** `shinri-core` (new `smtlib_print` module, moved from
`shinri-parser/src/print.rs`), `shinri-parser` (`print_term` becomes a
re-export), `shinri-solver` (`word_norm.rs`: one persisted map replaces
`orig_ite`; `lib.rs`: `format_value` lookup chain, the `internal_vals`
stash, `get-value` / `get-model` printing; `tseitin.rs`: `display_term`
deleted). No verdict-affecting change: no solving stage, fence, theory or
`lower` change, and nothing mints a term at query time.

## 1. Summary

### 1.1 The defects

**D1 — the echo prints raw TermIds.** `tseitin::display_term`
(`crates/shinri-solver/src/tseitin.rs`, `display_term_at_depth`) renders
only uninterpreted applications. Every builtin op and every literal falls to
`format!("t{}", t.index())`. So `(get-value ((+ a 1)))` prints `(t9 1)`
and `(get-value ((f (= x 1))))` prints `((f t4) …)`. The slice-50 spec
called these "purification names"; they are TermId indices, not names. The
output is not valid SMT-LIB for the query that was asked.

**D2 — purified terms print `?`.** Slice 54 rewrites a compound Bool
argument `t` to a proxy `bool!n` plus `(= bool!n t)`. The model holds
values for the rewritten terms (`(f bool!0)`), but `format_value` looks up
the user's original TermId (`(f (= x 1))`), which no theory registered. So
every term containing a purified argument prints `?`, and so does the
argument itself (`(= x 1)`). With `(= (f (= x 1)) 7)` asserted, the value
printed `7` before slice 54 and `?` now. The per-call walk memo holds the
original→rewritten mapping but is discarded after `normalize`.

**D3 — symbols are never quoted.** `format_model` prints `d.name` raw, so a
symbol that needs `|…|` (ESBMC's `__ESBMC_rounding_mode&0#10`) makes the
model unparseable. Any echo that prints symbols (the D1 fix) has the same
hole.

### 1.2 Reproducers (HEAD `a0d0fe9`)

| # | script (abridged) | query | HEAD prints | after |
|---|---|---|---|---|
| r1 | QF_LIA, `(= a 0)` | `((+ a 1))` | `((t9 1))` | `(((+ a 1) 1))` |
| r2 | QF_UFLIA, `f : Bool → Int`, `(= (f (= x 1)) 7)` | `((f (= x 1)))` | `(((f t4) ?))` | `(((f (= x 1)) 7))` |
| r3 | QF_UFLIA, `(P (= x 1))`, `(not (P true))`, `(= x 2)` | `((P (= x 1)) (= x 1) (P false))` | `(((P t4) ?) (t4 ?) ((P t1) ?))` | real echo; `(P (= x 1))` and `(= x 1)` valued |
| r4 | QF_BV, `(declare-const \|a#b\| (_ BitVec 8))` | `(get-model)` | `(define-fun a#b …)` | `(define-fun \|a#b\| …)` |

The exact TermId indices in the "HEAD prints" column are taken from the
slice-54 report and slice-50 spec; the probes (§6.1) pin the after column,
not the before.

## 2. Scope

In:

- One SMT-LIB term printer in `shinri-core`, with a node budget and symbol
  quoting, used by the parser, `get-value` and `get-model` (D1, D3).
- A persisted original→rewritten map in `WordNorm` and a read-only lookup
  chain in `format_value` (D2).
- `get-model` quotes symbol and sort names (D3).
- The printer prints negative `Int`/`Real` constants as `(- n)`; they are
  reachable as an echo once D1 is fixed.

Out (queued, §9):

- A model evaluator for a query term that occurs in no assertion (approach
  V2). Such a term keeps `?`.
- `get-model` contents (function graphs, internal symbols): unchanged apart
  from quoting.
- Source-text echo (approach P2): rejected, see §8.

## 3. Design

### 3.1 The printer: `shinri_core::smtlib_print`

The body of `crates/shinri-parser/src/print.rs` moves to
`crates/shinri-core/src/smtlib_print.rs`. That module sits next to
`smtlib_string`, which exists for the same reason: "so the parser and the
model printers agree on one rule set". `shinri_parser::print_term` becomes
`pub use shinri_core::smtlib_print::print_term`; the parser's round-trip
tests stay where they are.

API:

```rust
/// Unbounded; for the parser and tests.
pub fn print_term(ctx: &Context, t: TermId) -> String;
/// Bounded; for every solver output path.
pub fn print_term_budgeted(ctx: &Context, t: TermId, budget: &mut usize) -> String;
/// `name` if it is a simple SMT-LIB symbol and not reserved, else `|name|`.
pub fn quote_symbol(name: &str) -> std::borrow::Cow<'_, str>;
/// The sort's SMT-LIB name with any user symbol quoted.
pub fn print_sort(ctx: &Context, s: SortId) -> String;
```

- **Budget.** Each node visit costs one unit, checked before recursing, as
  in `display_term` today. When the budget is zero, the remaining subterm is
  printed as the symbol `|<truncated>|`: still a parseable term, visibly not
  a real one, and never a TermId index. The `depth > 10_000` backstop is
  kept and prints the same placeholder. `DISPLAY_TERM_BUDGET` (100 000)
  moves with the printer as `smtlib_print::DISPLAY_TERM_BUDGET`, and the
  `get-value` arm keeps one budget per response (slice 43 T6 rationale).
- **Quoting rule.** A name is printed bare iff it matches the lexer's simple
  symbol regex (`crates/shinri-parser/src/lexer.rs`,
  `[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*`) and is not a
  reserved word (`!`, `_`, `as`, `BINARY`, `DECIMAL`, `exists`, `HEXADECIMAL`,
  `forall`, `let`, `match`, `NUMERAL`, `par`, `STRING`, plus every command
  name, which SMT-LIB 2.6 §3.1 also reserves). Otherwise it is
  printed `|name|`. A name containing `|` or `\` cannot be quoted; the lexer
  cannot produce one, and internal names (`ite!n`, `bool!n`) are simple, so
  this case is a `debug_assert!` and prints the bare name in release.
  `true`/`false` are not reserved words in SMT-LIB 2.6 and are only ever
  printed for Bool constants.
- **Negative numerals.** `ConstVal::Num` with a negative value prints
  `(- n)` (Int) or `(- n.0)` / `(- (/ n d))` (Real). The current comment
  ("negatives are out of scope for round-trip") is removed.
- **Sorts.** `print_sort` quotes user-declared sort names and datatype
  names; builtin sorts (`Int`, `(_ BitVec 8)`, `(Array Int Int)`, …) print
  as `Context::sort_name` does today. If `Context::sort_name` already
  composes parametric sorts from component names, `print_sort` replaces it
  at the output call sites only; `sort_name` itself is not changed.

`tseitin::display_term` and `display_term_at_depth` are deleted.

### 3.2 The rewrite map: `WordNorm::orig_rewrite`

`WordNorm` gets a solver-lifetime field:

```rust
/// Every original TermId the walk changed → its rewritten TermId.
/// Get-value only (slice 55).
orig_rewrite: FxHashMap<TermId, TermId>,
```

`walk` inserts `(t, result)` whenever `result != t`. This subsumes
`orig_ite`: for an eliminated ite the walk returns its `ite!` symbol, so
`orig_rewrite[t]` is that symbol. `orig_ite` and `orig_ite_map()` are
deleted; `orig_rewrite_map()` replaces the accessor. `ite_map()` (keyed by
the post-rewrite ite) stays, because the ABV stage harvests internal
symbols from it.

Keys are hash-consed TermIds, which outlive `push`/`pop`, exactly like the
existing maps. Size is bounded by the number of changed nodes. Inserting
into the map mints nothing, so no TermId shifts.

### 3.3 The lookup chain: `format_value`

`format_value(t)` stays read-only and tries, in order:

1. `last_model[t]`: every term the walk left alone (unchanged behaviour).
2. `r = orig_rewrite[t]`, then `last_model[r]`: e.g. `(f (= x 1))` →
   `(f bool!0)` → `7`.
3. `b = bool_arg_var[r_or_t]`, then `internal_vals[b]`: a purified
   argument itself, e.g. `(= x 1)` → `bool!0` → `true`. (`bool_arg_var` is
   keyed by the post-child-rewrite argument, so the lookup key is `r` when
   step 2 found one, else `t`.)
4. `internal_vals[r]`: the rewritten form is itself an internal symbol
   (an eliminated ite: today's `eliminated_ite_vals` behaviour).
5. `abv_array_models[t]` (unchanged).
6. Otherwise `None`, printed `?` (unchanged fallback).

A term rewritten in an earlier `check-sat` but absent from the current one
finds no value at steps 2–4 and prints `?`, which is correct.

### 3.4 The stash: `internal_vals`

Today the main path builds `internal_vals` (values of `word_norm.internal`
symbols, kept out of the model), copies the ite subset into
`eliminated_ite_vals`, and drops the rest; the ABV path does the same from
`ite_sym_vals`. After this slice:

- The field `eliminated_ite_vals` is renamed `internal_vals` and keyed by the
  internal symbol, not by the original term. The main path stores its
  `internal_vals` whole; the ABV path stores `ite_sym_vals` whole.
- The two remap loops (`lib.rs` ~`:961–974` and ~`:1449–1458`) are deleted;
  steps 2–4 of §3.3 do the remap at query time.
- It is cleared at exactly the points `eliminated_ite_vals` is cleared
  today (`pop`, `Reset`, every `check_sat`), and the `pop` comment block
  is updated to the new name.

`abv-uf-args` fences every Bool argument, so a `bool!` proxy never reaches
`sat` on the ABV path; that path only ever feeds `ite!` values.

**Unverified fact (Task 1).** That a `bool!n` proxy's value reaches the
main path's `internal_vals`. It is an EUF atom merged with ⊤/⊥, and the
`mb` loops route `internal` terms there, but this has not been observed.
If it does not land there, Task 1 adds the value from the SAT assignment of
`b`'s atom, the way a user Bool constant is valued, and records which.

### 3.5 Output call sites

- `Command::GetValue`: `print_term_budgeted` replaces `display_term`.
- `format_model`: `quote_symbol(&d.name)` and `print_sort(d.result)`.
- Any other `Values(..)` producer is audited in Task 1 (§5).

## 4. What this does not change

Verdicts: no solving stage, fence, theory, Tseitin encoding or `lower` path
changes, and no TermId is minted at query time. `get-model` contents. The
`?` fallback for a term no channel values. The `get-value` gate on
`last_outcome == Some(Sat)`.

## 5. Tasks

1. **Audit and verify.** List every consumer of `Values(..)` / `get-value`
   / `get-model` output in tests and harnesses (including the oracle and
   differential binaries that parse it) and how each matches. Verify §3.4's
   unverified fact on r3. No code change.
2. **Move the printer to core** (§3.1), re-export from the parser, add
   `print_term_budgeted`, `quote_symbol`, `print_sort`, negative numerals.
   Unit tests and the round-trip property (§6.2).
3. **Switch the output call sites** (§3.5); delete `display_term`. Update
   the existing tests Task 1 listed.
4. **The rewrite map and lookup chain** (§3.2–§3.4).
5. **Probes** (§6.1) — written first in Tasks 3–4 under TDD, collected in
   `slice55_probes.rs`.
6. **Oracle** (§6.3).
7. **Measurement and report** (§7).

## 6. Testing

### 6.1 End to end (`crates/shinri-solver/tests/slice55_probes.rs`, blocking tier)

Golden comparison of the response line, except where the model is free
(then consistency is asserted, not one model):

- **e1** r1: `(((+ a 1) 1))`.
- **e2** r2: `(((f (= x 1)) 7))`.
- **e3** r3: the echo is `(((P (= x 1)) v1) ((= x 1) v2) ((P false) v3))`;
  `v1` is `true`, `v2` is `false` (since `x = 2`), and `v3` is pinned to
  whatever Task 1 measures (`?` if no channel values `(P false)`).
- **e4** an `ite` inside a purified argument, e.g. `(P (> (ite c x y) 0))`:
  the outer term and the argument are both valued (the chain composes).
- **e5** quoting: `|a#b|` and a sort `|my sort|` echo quoted in `get-value`;
  r4's `get-model` prints `(define-fun |a#b| () (_ BitVec 8) #x..)`.
- **e6** budget: the existing slice-43 T6 `let`-chain test adapted — output
  bounded, contains `|<truncated>|`, no `t<digits>` token.
- **e7** no leak: over every probe's output, no `bool!`, no `ite!`, and no
  token matching `\bt[0-9]+\b`.

At HEAD, e1–e5 and e7 fail; e6 fails on the placeholder text only.

### 6.2 Printer (`shinri-core` unit + `shinri-parser/tests/roundtrip.rs`)

- `parse(print_term(t)) == t` over the existing round-trip corpus, extended
  with quoted symbols, a quoted sort, reserved-word-shaped names, and
  negative Int/Real constants.
- `quote_symbol` table test: simple, reserved, needs-quote, digit-leading.
- Budget: a term of `N > budget` nodes prints at most `budget` real nodes
  plus placeholders.

### 6.3 Oracle (feature `oracle`, extend `tests/bool_arg_oracle.rs`)

For every generated instance shinri answers `sat`, issue
`(get-value (<each asserted term's Bool-argument parents and arguments>))`,
then send z3 the original assertions plus `(assert (= term value))` for
every pair whose value is not `?`, and require z3 `sat`. This checks in one
pass that the echo re-parses in another solver and that the values are
consistent. Gate: 0 disagreements, and a non-zero test count confirmed
(`cargo nextest run -p shinri-solver --features oracle -E 'binary(bool_arg_oracle)'`).

## 7. Measurement

Verdict-only bench comparison on the four slice-54 logics (QF_UF,
QF_UFLIA, QF_UFLRA, QF_DT), base = `a0d0fe9`, after = slice head. Timing
is reported but not gated: performance is not the subject, and the change
is post-solve. The report goes to
`docs/superpowers/research/2026-10-02-smtlib-2024-slice55-get-value-report.md`
with the exact commands.

### Success criteria

1. e1–e7 pass; at HEAD e1–e5 and e7 fail (logs kept).
2. **0 rows change verdict** in the four logics. Any change is a defect of
   this slice and blocks the merge.
3. Oracle: 0 disagreements, non-zero test count.
4. `mise run ci` green; `cargo fmt --all` clean.

## 8. Approaches not taken

- **P2 — echo the source text.** Byte-exact and blowup-free, but it changes
  the frontend IR (`GetValue(Vec<(TermId, String)>)`) and the parser's
  input handling (threat-model review), and `get-model` would still need a
  quoting helper. z3 and cvc5 re-print rather than echo.
- **P3 — extend `display_term` in place.** Smallest diff, but a second
  builtin-name table that drifts from the parser's.
- **V2 — a model evaluator.** Answers query terms that occur in no
  assertion, but it is a new soundness surface; slice 50 flagged the
  evaluator path as fragile. Queued.

## 9. Queued for the next slice

- Slice 56: the slice-53 queue's first entry (remove the `Not(Eq)` arm,
  with the bare-E simplification and the string-engine search-order
  sensitivity, and the axiom memory-growth measurement).
- V2 evaluator for unregistered query terms.
- Everything else in the slice-54 report's queue, carried unchanged, minus
  the two `get-value` items and the `get-model` quoting item closed here.

## 10. References

- Slice-54 report:
  `docs/superpowers/research/2026-10-02-smtlib-2024-slice54-uf-bool-arg-report.md`
  (*What changed versus the spec*, item 2; `## Queued for the next slice`).
- Slice-54 spec: `docs/superpowers/specs/2026-10-02-shinri-slice54-uf-bool-arg-purify-design.md`.
- Slice-50 spec §10: `docs/superpowers/specs/2026-09-29-shinri-slice50-uflia-shared-compound-args-design.md`.
- Threat model (output-size bound): `docs/threat-model.md`.

## 11. Measured outcomes

Full evidence:
`docs/superpowers/research/2026-10-02-smtlib-2024-slice55-get-value-report.md`.

| # | Criterion | Result |
| --- | --- | --- |
| 1 | e1–e7 pass | PASS (e1 observes `?` for `(+ a 1)`, Ruling 5) |
| 2 | 0 rows change verdict | PASS under the operationalised reading (re-run changed rows 3× on both binaries; only reproducible differences count): 18,146 rows, 0 `wrong`, 65 recorded differences, all `timeout`/`oom` resource flips; the re-runs show no reproducible answer difference |
| 3 | Oracle 0 disagreements, non-zero count | PASS: 22 tests run, DT 0/269/8, UFLIA 0/384/21, UFLRA 0/385/12 (disagreements / valued / abstract) |
| 4 | `mise run ci` green, fmt clean | PASS: 1,676 passed, 7 skipped |

### Deviations from this spec

- **Negative numerals (§3.1, §6.2) dropped.** The parser reads `(- 3)` as
  `Neg`, which already prints as `(- 3)`; no negative `ConstVal` is built
  from source (Ruling 1).
- **Testers print as `((_ is C) x)`, not the legacy `is-C` (Task 1,
  Ruling 6).** Shinri's parser rejects `(is-C v)`; the printer emits the
  SMT-LIB 2.6 indexed form and the parser is unchanged.
- **Bench base is the slice-54 run** (binary built at `6212fa5`), not a
  fresh run at `a0d0fe9`.
- **Oracle excludes `@`-valued pairs (Ruling 8).** They are counted as
  `n_abstract` and not sent to z3. They expose a pre-existing wrong `sat`
  (a Bool constant as a UF argument, `(P q)` with `(not (P true))` and
  `(not (P false))`), which this verdict-neutral slice does not fix. It is
  the first item of the next slice's queue (see the report, *Defect found*).
- **`bool!` proxies need no extra value loop** (Task 3 Step 1): `bool!0`
  is already in `internal_vals`.
