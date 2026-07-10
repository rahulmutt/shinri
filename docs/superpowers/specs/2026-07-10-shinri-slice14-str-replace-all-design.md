# Slice 14 design — `str.replace_all` (fold + partial-eval + fence)

Status: DESIGNED (2026-07-10). Follows slice 13 (`str.indexof` / `str.replace`,
PR #7, merged `568692f`).

## Scope

Add SMT-LIB `str.replace_all` as a value-sorted **function**
(`String × String × String → String`). This is a close cousin of slice-13
`str.replace`: same fold / partial-eval / fence structure, **minus** the
`indexof` half. Instead of one split around the leftmost occurrence, the
partial-eval performs an N-way split around every **non-overlapping**
occurrence.

Like slice 13 and unlike slice 12, both operands and result are values (not
predicates), so the rewrites are exact at any position and polarity — no
polarity analysis, and the pass introduces **zero fresh variables**. No new
model-filtering or get-value surface.

**Symbolic-`u` decision (full mirror of slice 13):** fold all-literal
applications; partial-eval literal-haystack + symbolic-`u` into the full N-way
concat (capped on occurrence count); fence only symbolic haystack/needle. A
symbolic `u` at ≥2 occurrences yields a concat with a **repeated** variable
(`… ++ u ++ … ++ u ++ …`) — new territory the slice-13 `replace` split never
hit (its `u` appeared exactly once). This lands in the semi-decidable
word-equation fragment: **sound** via the existing SAT step budget (Unknown on
exhaustion), with the 0-disagreement Z3 differential oracle as the guardrail.

Why not decide symbolic haystacks: `replace_all`'s general semantics hinge on
first-occurrence minimality and "no earlier occurrence" — negated containment at
scale, exactly the negative-polarity territory slice 12 fenced and the
deliberately incomplete word-equation engine's weakest area. Out of scope.

## Pinned SMT-LIB 2.6 semantics

`(str.replace_all s t u)` → String:

- Replaces **all non-overlapping** occurrences of `t` in `s` by `u`, scanning
  `s` **left-to-right**; after a match at position `p`, scanning resumes at
  `p + |t|` in the **original** haystack — `u` is never re-scanned, matches
  never overlap.
- If `t` **does not occur** in `s`: result is `s` unchanged (independent of
  `u`).
- If `t` is the **empty string**: result is `s` unchanged — **`u` is dropped**.
  ⚠️ This differs from slice-13 `str.replace`, where empty `t` gives `u ++ s`.
  This is the correctness trap for this slice.

All indices are **code points** (Unicode scalar values / `Vec<char>`), matching
`eval_substr_const` and slice 13 — never bytes (non-ASCII trap).

Argument order (pinned per the slice-12/13 convention): **haystack-first** —
`(str.replace_all s t u)` replaces `t` by `u` in `s`.

Worked examples (pin these in the unit tests):

- `(str.replace_all "aaa" "aa" "X")` = `"Xa"` — non-overlapping matches only
  (position {0}, then resume at 2; the overlap at position 1 is NOT matched).
- `(str.replace_all "abab" "ab" "Z")` = `"ZZ"` — adjacent matches.
- `(str.replace_all "abc" "z" "X")` = `"abc"` — not found, `u` dropped.
- `(str.replace_all "ab" "" "X")` = `"ab"` — empty needle, `u` dropped.
- `(str.replace_all "héllo" "l" "L")` = `"héLLo"` — code points, two matches.

## 1. Surface changes

- **`shinri-core`** (`term.rs`): one new `BuiltinOp` variant —
  `StrReplaceAll` with sort rule `String × String × String → String`,
  documented alongside `StrIndexOf` / `StrReplace`.
- **`shinri-core`** (`context.rs`): extend the existing `StrReplace`
  sort-rule arm to `StrReplace | StrReplaceAll` — the rule is identical
  (arity 3, `expect_all(String)`, → String).
- **`shinri-parser`** (`parser.rs`): map `"str.replace_all" => StrReplaceAll`
  and route it through the same `mk_app` sort-checking arm as `StrReplace`
  (delegates to `mk`, which sort-checks). Wrong-sort operands (e.g. an Int
  replacement) must be a parse diagnostic.
- **`shinri-parser`** (`print.rs`): `StrReplaceAll => "str.replace_all"`.

## 2. Pre-pass (extends `shinri-str/src/indexof_replace.rs`)

Reuses the existing `occurrences` helper. Adds:

- **`nonoverlapping_occurrences(hay, needle) -> Vec<usize>`** — greedy
  left-to-right scan, stepping `+|needle|` after each match. Empty needle
  returns an empty `Vec` (no positions), so the empty-needle case naturally
  drops `u` at both the fold and partial-eval paths.
- **`eval_replace_all(hay, t, u: &str) -> String`** — concrete fold. Empty `t`
  → return `hay` verbatim (`u` dropped). Else walk `nonoverlapping_occurrences`,
  emitting the literal gaps and `u` at each match position, then the trailing
  tail.
- **`rewrite_replace_all(ctx, kids)`** — mirrors `rewrite_replace`. `kids`
  already rewritten bottom-up. `Some(_)` iff a fold / partial-eval case applies;
  `None` leaves the app in place (→ fence):
  - **all-literal** (`hay`, `t`, `u` all String constants) → fold to one
    literal via `eval_replace_all`.
  - **literal haystack + needle, symbolic `u`**, occurrence count within cap →
    N-way concat `pre ++ u ++ mid₁ ++ u ++ … ++ u ++ post`, with empty literal
    flanks/separators elided (reuse the slice-13 flank-drop logic; if only a
    single non-empty part remains, collapse to it rather than a 1-ary concat).
  - **zero non-overlapping occurrences** (needle absent, or empty needle) →
    return the haystack `TermId` unchanged (drop `u`), exact.
  - **over-cap occurrence count** (symbolic-`u` path only) → return `None`
    (leave in place → fence).
- **New cap** `REPLACE_ALL_CONCAT_CAP: usize = 64` (mirrors
  `INDEXOF_CHAIN_CAP`) — bounds the **number of non-overlapping occurrences**
  spliced into the symbolic-`u` concat, capping term growth and the
  repeated-variable load on the wordeq engine. Folding (all-literal) is
  **uncapped** — it produces one literal, same as slice-13 folding.
- Wire `Op::Builtin(BuiltinOp::StrReplaceAll) => rewrite_replace_all(ctx, &new_children)`
  into `rewrite`'s `special` match, and add `StrReplaceAll` to the
  `has_unreduced_indexof_replace` fence walk's `matches!`.

Memoization, TermId preservation for untouched subtrees, and bottom-up ordering
are inherited unchanged from the slice-13 `rewrite` driver.

## 3. Fence / solver wiring

- **`string_stage.rs`**: add `BuiltinOp::StrReplaceAll` to `is_string_op` so
  `uses_strings` routes queries onto the string path.
- **`lib.rs`**: **no new stage**. `partial_eval_indexof_replace` already runs on
  the string path; the extended `has_unreduced_indexof_replace` now also fences
  any surviving `str.replace_all` application (symbolic haystack/needle, or
  over-cap literal) to a sound `Unknown` — canary-pinned flip-markers for a
  future symbolic-encoding slice.

Downstream: the folded literal is an ordinary constant; the symbolic-`u` concat
lands in the word-equation engine's decided concat fragment. Repeated-`u`
concats (≥2 occurrences) are the semi-decidable case — sound on the existing
step budget (Unknown on exhaustion), never a spurious verdict per the oracle
gate. `get-value` on a symbolic application is moot (it fences pre-solve),
consistent with substr and slice 13.

## 4. Testing

- **Unit** (`indexof_replace.rs` tests): the worked examples above, plus —
  empty-needle drops `u` (explicitly contrasted against `replace`'s `u ++ s`),
  non-overlapping vs overlapping (`"aaa"`/`"aa"` → `"Xa"`), adjacent matches
  (`"abab"`/`"ab"` → `"ZZ"`), needle at end, code-point (non-ASCII) matches,
  not-found drops `u`, all-literal fold, symbolic-`u` N-way concat shape +
  flank elision + single-part collapse (whole-haystack-is-needle), cap boundary
  (64 occurrences fold, 65 leave in place → fence), memo dedup (repeated app →
  same rewritten term), symbolic-haystack survives → fence classification.
- **e2e script pins** (`script_e2e`): decided **sat AND unsat** examples through
  both the fold and the symbolic-`u` concat paths; a symbolic-haystack
  `str.replace_all` → `unknown` fence canary as a flip-marker.
- **New differential oracle family** `qfs_replace_all_matches_z3` — own **fresh
  seed** (slice-12/13 convention: new op family = new oracle family, never
  perturb existing seeds), unknown-tolerant, **0-disagreement gate @ 200
  iters**. Generator mixes: all-literal (fold path), literal-haystack +
  symbolic `u` including ≥2 occurrences (partial-eval concat path), symbolic
  haystack (fence path), nested in `str.++` / `str.len` / `=` at both
  polarities.
- Existing oracle families (`qfs_matches_z3`, `qfs_predicates_matches_z3`,
  `qfs_indexof_replace_matches_z3`, the nary and fp-bridge str families)
  **untouched**.

## 5. Out of scope

- **Symbolic haystack / needle** `replace_all` — requires negated containment
  at scale (the fenced negative-polarity territory; the wordeq engine's weakest
  area). Fenced to sound `Unknown`.
- **`str.replace_re` / `str.replace_re_all`** — regex is a separate future
  plan; not this slice.
- Lifting the symbolic-`u` occurrence cap — later cleanup if a benchmark
  demands it.

## Risks

- **R1 — empty-needle trap.** `str.replace_all` drops `u` on empty needle;
  `str.replace` prepends it. A copy-paste from `rewrite_replace` that keeps the
  `u ++ s` empty-needle branch is unsound. Mitigation: the `eval_replace_all`
  empty-`t` branch and a dedicated unit test that asserts the contrast.
- **R2 — overlapping vs non-overlapping.** Reusing `occurrences` (which
  includes overlaps) for the split would be wrong; the split must use
  `nonoverlapping_occurrences`. Mitigation: the `"aaa"`/`"aa"` → `"Xa"` unit
  test and the oracle family.
- **R3 — repeated-variable concat completeness.** Symbolic `u` at ≥2
  occurrences may exhaust the wordeq step budget and return `Unknown` more often
  than `replace`. This is a completeness (not soundness) concession, bounded by
  `REPLACE_ALL_CONCAT_CAP` and tolerated by the unknown-tolerant oracle gate.
