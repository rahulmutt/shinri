# Slice 12 design — string predicates (prefixof / suffixof / contains)

Date: 2026-07-07
Status: IMPLEMENTED (slice 12 landed 2026-07-09). Predicates parse / sort-check /
print, constant-fold at any polarity, fence negative/mixed/non-monotone to sound
Unknown, and decide positive occurrences via existential concat rewrite.
`qfs_predicates_matches_z3` = 33 sat / 68 unsat / 97 unknown @ 200 iters, 0
disagreements; `qfs_matches_z3` unchanged (90/136/74, 0 disagreements). The
predicate rewrite (predicates → word equations) surfaced a PRE-EXISTING
word-equation resolver unsoundness (present on `main`); implementation additionally
root-caused and fixed it — dl0-gated merge-derived length lemmas + a complete
3-valued model gate + antecedent-precise citation — verified across 3 independent
adversarial review rounds and ~24k differential fuzz iterations (0 wrong verdicts).
A permanent differential fuzzer (`tests/qfs_fuzz_corpus.rs`) and `script_e2e`
regression pins guard the fix. Residual (completeness, NOT soundness): sound
`unknown` on multi-variable disjunctive word-equation shapes the deliberately
incomplete word-equation+length theory cannot decide — deciding them needs a
complete procedure (out of slice-12 scope, follow-up).
Predecessor: slice 11 (PR #4, landed 2026-07-06, merge `d5a1599`)

## Goal

Admit `str.prefixof`, `str.suffixof`, `str.contains` — today parser
`unknown operator` errors, the exact coverage gap documented in slice-10
design §1.1 item 1 — with a **polarity-aware** posture:

- **Constant-fold** literal-literal cases to Boolean `true`/`false` at any
  polarity.
- **Decide** atoms whose every occurrence is positive, via existential
  concat decomposition into the existing word-equation machinery.
- **Fence** everything else (negative, mixed-polarity, or non-monotone
  occurrences) to sound `Unknown`, canary-pinned as flip-markers.

Approach chosen (over first-class `StrSolver` theory atoms, and over
fold-only): **assertion-level rewrite pre-pass**, the same house pattern as
the `str.at`/`str.substr` desugar in `shinri-str::reduce` — no new
theory-atom kind, no new assert/retract/justification state (deliberate,
after slices 8 and 11 spent two slices hardening exactly that machinery).

### SMT-LIB argument order (pinned here because it is a classic trap)

- `(str.prefixof p s)` — is `p` a prefix of `s`? **Needle first.**
- `(str.suffixof p s)` — is `p` a suffix of `s`? **Needle first.**
- `(str.contains s sub)` — does `s` contain `sub`? **Haystack first.**

Parser sort-checks, rewrite shapes, and tests all state this explicitly.

## Non-goals

- No `str.indexof` / `str.replace` / regex (scoped out; indexof needs
  first-occurrence minimality — a different, harder encoding).
- No negative-polarity decisiveness — fenced, with canaries as flip-markers
  for a future slice.
- No change to the existing string oracle family at seed `0xB000_9E38`
  (nary_oracle.rs) or to the fp-bridge str family
  (`differential_qf_fp_to_real_str`, supported-ops-only per slice-10 §1.1
  item 5); the new ops get their **own** oracle family.
- No substr/at fence change; `has_unfoldable_substr_or_at` semantics
  untouched.
- No word-equation completeness work — the slice-11 residue (cluster-B
  canonical input is a sound fuel-Unknown) stays a separate open follow-up.
- `get-value` on a predicate term stays unsupported (predicates are
  rewritten away pre-solve; consistent with substr today).

## 1. Surface changes

- `shinri-core`: three new `BuiltinOp` variants (`StrPrefixOf`,
  `StrSuffixOf`, `StrContains`); sort rule `String × String → Bool`.
- `shinri-parser`: parse the three ops with arity/sort checks; `print.rs`
  round-trips them.
- `shinri-str::reduce`: constant folder, polarity classifier, positive
  rewrite, and the fence predicate `has_unrewritable_str_predicate` (§2).
- `shinri-solver/lib.rs`: fence check + rewrite call at the existing
  string-path seam (`lib.rs:402-425`), sibling to
  `has_unfoldable_substr_or_at`.

## 2. Rewrite pre-pass & fence semantics

Ordering at the string-path seam: **fold → polarity check/fence → rewrite →
existing `reduce_assertions` (substr desugar) → Combiner.**

### Constant fold (first, any polarity)

Both args string literals → fold the atom to Boolean `true`/`false` in
place (concrete SMT-LIB semantics, char-based like `eval_substr_const`).
A folded atom is no longer a predicate occurrence, so e.g.
`(not (str.contains "abc" "d"))` decides without touching the fence.

### Polarity analysis

Walk each assertion's Boolean skeleton computing per-occurrence polarity by
standard descent: `and`/`or` preserve, `not` flips, `=>` flips the
antecedent. Any occurrence under a **non-monotone** context — `xor`,
`=`/`distinct` over Bool, or an `ite` in any position — is conservatively
both-polarity. An atom qualifies for rewriting only if **every** occurrence
across **all** assertions is positive. Unrecognized Boolean structure
defaults to both-polarity (fails sound: fence, never wrong-side rewrite).

### Rewrite (positive-only atoms)

Each qualifying atom is replaced in place by its existential decomposition
with fresh String vars (existing `FRESH_CTR` naming scheme):

- `(str.prefixof p s)` → `(= s (str.++ p k))`
- `(str.suffixof p s)` → `(= s (str.++ k p))`
- `(str.contains s sub)` → `(= s (str.++ k1 sub k2))`

Standard equisatisfiable positive-occurrence rewrite: a witness for the
equation implies the predicate; a model of the predicate extends to the
fresh vars. Fresh vars are per-atom with structural dedup — the same atom
TermId rewrites to the same equation reusing its fresh vars (word_norm's
dedup discipline).

### Fence (everything else)

`has_unrewritable_str_predicate` returns true iff any predicate occurrence
survives folding and fails the positive-only test → the query returns sound
`Unknown`. Same whole-query granularity as the substr fence at
`lib.rs:416`.

The rewrite emits only concat/eq shapes the wordeq engine already owns; the
string-path SAT fuel budget applies unchanged, so a heavy positive
`contains` (two fresh vars per atom) can still exhaust fuel to a sound
Unknown — tolerated and counted in the oracle.

## 3. Model & witness channel

Rewritten predicates leave only eq-over-concat atoms, which
`string_model_satisfies` (`lib.rs:904`) already evaluates — the witness
self-check covers the new shapes with zero changes. Fresh `k` vars get
model values from the wordeq engine like any other string var; they are
internal (reserved `FRESH_CTR` names, never user-named) and `get-model`
treats them exactly as substr's `pre`/`mid`/`post` fresh vars today —
matched, not changed.

## 4. Testing

- **Pre-flight canary hunt** (standing cross-slice lesson): grep the corpus
  for pins on `unknown operator`/parse-error behavior for these ops and for
  parser tests enumerating the `BuiltinOp` surface, before any code change.
  Design-time check found only the `fp_oracle.rs:1818` comment; the hunt is
  still front-loaded in the plan to net unit-level pins.
- **Unit (parser/core):** parse + sort-check + print round-trip for all
  three; arg-order pins (`contains` haystack-first); wrong-sort rejection.
- **Unit (reduce):** constant folds (true and false outcomes, all three
  ops, both polarities); positive rewrite shapes; dedup of a repeated atom;
  polarity classifier over `and`/`or`/`not`/`=>`/`xor`/Bool-eq/`ite`
  shapes; `has_unrewritable_str_predicate` fires exactly on the fence set.
- **E2e decisive pins** (z3-agreed): positive prefixof/suffixof/contains,
  SAT- and UNSAT-expected (e.g. `(str.prefixof "ab" s)` ∧
  `(= (str.len s) 1)` → unsat), mixed with concat/`str.len` arithmetic; a
  combined predicate + substr query (both fresh-var minters in one query).
- **E2e fence canaries** (flip-markers for a future negative-polarity
  slice): `(not (str.contains s "a"))` → Unknown; predicate under an `ite`
  condition → Unknown; same atom positive and negative → Unknown; predicate
  over a UF application `(g s)` → Unknown (upstream `string_stage::fenced`,
  unchanged).
- **New differential oracle family** `differential_qf_s_predicates`
  (own seed, `oracle` feature): fuzzed positive-polarity predicates over
  literal/var needles mixed with eq/concat/`str.len` atoms, z3-pinned —
  **0 disagreements**; Unknowns tolerated with counts reported (fuel
  exhaustion is legal); assert `sat>0 ∧ unsat>0` coverage.
- **Net:** full `cargo test --workspace` + full oracle sweep; clippy on a
  clean cache (warm-cache clippy false-passes here); long gates run in the
  background by the controller — no cargo subagents during live gate runs.

## 5. Risks

1. **Wordeq fuel blowup on `contains`** (two fresh vars per atom) —
   degrades to sound fuel-Unknown, counted in the oracle; if the decisive
   rate is embarrassingly low, document it as residue, don't force it.
2. **Polarity classifier bug → wrong-side rewrite would be unsound.**
   Owned by classifier unit tests + the z3 differential family; the
   conservative default (unrecognized structure → both-polarity → fence)
   fails sound.
3. **Fresh-var interaction with the substr desugar** (both mint fresh vars;
   predicate rewrite runs first): shared `FRESH_CTR` prevents collisions;
   the combined e2e pin owns it.
4. **String-stage fence interplay:** predicates over UF applications with
   String args still fence upstream — unchanged behavior, canary-pinned.

## 6. Acceptance summary

| Criterion | Bar |
|---|---|
| Coverage | all three ops parse, sort-check, print round-trip |
| Decisive | positive-polarity + folded cases decide, z3-agreed, e2e-pinned |
| Fence | negative/mixed/non-monotone → sound Unknown, canary-pinned |
| Oracle | new family 0 disagreements, sat>0 ∧ unsat>0, unknown counts reported |
| Net | full workspace + oracle sweep 0 regressions; clean-cache clippy 0 net-new |
| Ledger | slice-11 wordeq-completeness residue untouched, stays open |
