# Slice 13 design — str.indexof / str.replace (fold + partial-eval + fence)

Date: 2026-07-10
Status: IMPLEMENTED (slice 13 landed 2026-07-10).
`qfs_indexof_replace_matches_z3` = 44 sat / 85 unsat / 71 shinri-unknown /
0 z3-unknown / 0 guard-bailout @ 200 iters, 34 witnesses, 0 disagreements;
existing families unchanged (`qfs_matches_z3` 90/136/74,
`qfs_predicates_matches_z3` 33/68/97, both 0 disagreements).
Predecessor: slice 12 (str predicates, landed 2026-07-09, PR #5); differential
CI item (PR #6, landed 2026-07-10)

## Goal

Admit `str.indexof` and `str.replace` — today parser `unknown operator`, the
two ops slice 12 explicitly scoped out — with approach B (user-selected over
fold-only and over symbolic first-occurrence encodings):

- **Constant-fold** fully-literal applications to their concrete value.
- **Partial-eval** applications whose haystack and needle are literal but
  whose remaining argument (replacement string / start index) is symbolic,
  via exact, polarity-free term rewrites into already-validated machinery
  (concat, length arithmetic, `elim_term_ite`).
- **Fence** every other occurrence (symbolic haystack or needle, or over-cap
  literal) to sound `Unknown`, canary-pinned as flip-markers.

Key structural property: both ops are value-sorted **functions** (Int-sorted
and String-sorted respectively), not predicates — the rewrites are exact at
any position and polarity, so unlike slice 12 there is no polarity analysis,
and the pass introduces **zero fresh variables** — no new model-filtering or
get-value surface.

Why not decide symbolic haystacks: both ops' general semantics hinge on
first-occurrence minimality ("no earlier occurrence"), which requires negated
containment at scale — exactly the negative-polarity territory slice 12
fenced, and the deliberately incomplete word-equation engine's weakest area
(the machinery slices 8/11/12 spent hardening). Out of scope.

## Pinned SMT-LIB 2.6 semantics

All indices are **code points** (Unicode scalar values), matching
`eval_substr_const`'s char-based convention — never bytes (non-ASCII trap).

Argument order (pinned per the slice-12 convention): both ops are
**haystack-first** — `(str.indexof s sub i)` searches for `sub` in `s`;
`(str.replace s t u)` replaces `t` by `u` in `s`. (Unlike
`str.prefixof`/`str.suffixof`, which are needle-first.)

- `(str.indexof s sub i)` → Int:
  - `-1` if `i < 0` or `i > |s|`. Note `i = |s|` is **in** range.
  - Else the smallest `j ≥ i` such that `sub` occurs in `s` at `j`.
    Occurrences may **overlap**: `"aa"` occurs in `"aaa"` at 0 AND 1 — the
    occurrence set enumerates every `j` with `s[j .. j+|sub|] = sub`.
  - `-1` if no such occurrence.
  - Empty needle occurs at every `0 ≤ j ≤ |s|`, so
    `(str.indexof s "" i) = i` whenever `0 ≤ i ≤ |s|` (including `i = |s|`).
- `(str.replace s t u)` → String:
  - If `t` occurs in `s`: replace the **leftmost** occurrence of `t` by `u`.
  - Else: `s` unchanged (the result does not depend on `u`).
  - Empty `t` occurs at position 0 → result `= u ++ s`.

## 1. Surface changes

- `shinri-core`: two new `BuiltinOp` variants — `StrIndexOf` with sort rule
  `String × String × Int → Int`, `StrReplace` with sort rule
  `String × String × String → String`.
- `shinri-parser`: parse both ops with arity/sort checks; `print.rs`
  round-trips them.
- `shinri-str::reduce::contains_string_op`: add both variants so pure
  indexof/replace queries route onto the string path (same wiring slice 12
  did for the predicates).

## 2. New pre-pass module `shinri-str/src/indexof_replace.rs`

One bottom-up, TermId-memoized rewrite:

```
pub fn partial_eval_indexof_replace(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>
```

Cases, applied after children are rewritten (nested occurrences compose):

### 2.1 Fold — all args literal/numeral

Compute the concrete result per the pinned semantics: an Int numeral for
`indexof` (including `-1`), a string literal for `replace`. Concrete
evaluation is done on `Vec<char>` (code points), reusing the
`int_numeral` / `string_const_value` helpers.

### 2.2 Partial-eval replace — `s`, `t` literal, `u` symbolic

- `t` found at leftmost occurrence position `p` (code-point index):
  rewrite to `(str.++ s[0..p] u s[p+|t|..])`, **dropping empty literal
  flanks** — the result is just `u` when both flanks are empty, `u ++ post`
  when only the prefix is empty (which subsumes the empty-`t` case:
  `u ++ s`), etc.
- `t` not found: rewrite to the literal `s`. Dropping the symbolic `u` from
  the term is exact — the replace value does not depend on `u`; `u`'s own
  constraints elsewhere in the query are unaffected.

### 2.3 Partial-eval indexof — `s`, `sub` literal, `i` symbolic

As a function of `i`, the result is a **step function** over the concrete
occurrence positions `o₁ < o₂ < … < oₖ` (overlaps enumerated):

```
ite(i < 0, -1,
  ite(i ≤ o₁, o₁,
    ite(i ≤ o₂, o₂,
      … ite(i ≤ oₖ, oₖ, -1))))
```

Empty needle emits `ite(0 ≤ i ∧ i ≤ |s|, i, -1)` directly.

The chain is Int-sorted ite. The existing `elim_term_ite` in
`reduce_assertions` — which runs later on the string path (lib.rs pipeline,
§3) — already eliminates non-Boolean ite soundly into fresh `!ite<n>` vars +
implications, with model filtering in place since slice 5/7. No new
machinery.

**Cap:** apply this case only when `|s| ≤ 64` code points (the chain length
is bounded by the occurrence count ≤ `|s|`). Over-cap applications are left
in place and fence (§3). Rationale: bounds term growth on adversarial
literals; oracle/e2e literals are far smaller. The cap applies only to the
symbolic-`i` chain — folding (§2.1) has no cap.

### 2.4 Everything else

Rebuild with rewritten children if changed, else keep the original `TermId`
(structural-sharing convention of `fold_str_predicates` / `rewrite`).

Fence predicate, same presence style as `has_unfoldable_substr_or_at`:

```
pub fn has_unreduced_indexof_replace(ctx: &Context, assertions: &[TermId]) -> bool
```

True iff any `StrIndexOf` / `StrReplace` application survives the rewrite —
symbolic haystack or needle, or over-cap literal.

## 3. Pipeline wiring (shinri-solver lib.rs string path)

Insert immediately after `fold_str_predicates` (currently lib.rs:414), before
the predicate polarity fence — ordering among the independent rewrites and
fences is immaterial, but the partial-eval must run before its own fence:

1. `assertions = shinri_str::indexof_replace::partial_eval_indexof_replace(…)`
   — unconditional (polarity-free, exact).
2. `if shinri_str::indexof_replace::has_unreduced_indexof_replace(…)` →
   `return SolveOutcome::Unknown` — sound fence, canary-pinned as
   flip-markers for a future symbolic-encoding slice.

Downstream stages (substr fence, predicate rewrite, `reduce_assertions`)
consume the rewrite's output: replace's concat lands in the word-equation
engine's decided concat fragment; indexof's ite chain is eliminated by
`elim_term_ite` into length-free LIA the Int seam already owns.

`get-value` on a symbolic application is moot — it fences pre-solve;
consistent with substr today. Folded results are ordinary literals.

## 4. Testing

- **Unit** (`indexof_replace.rs` tests): fold edge cases — empty needle at
  `i = |s|`, `i` out of range on both sides, overlapping occurrences
  (`"aa"` in `"aaa"`), needle at end, non-ASCII code-point indices (byte
  trap), replace not-found drops `u`, empty-`t` replace, empty-flank
  elision, memo dedup (repeated app → same rewritten term); chain-shape
  checks for symbolic-`i` indexof (threshold/value pairs, `-1` arms); cap
  boundary (64 folds/evals, 65 leaves in place); fence predicate
  classification.
- **e2e script pins** (`script_e2e`): decided sat AND unsat examples through
  both partial-eval rewrites; fence canaries (symbolic haystack →
  `unknown`) as flip-markers.
- **New differential oracle family** `qfs_indexof_replace_matches_z3`, own
  fresh seed (slice-12 convention: new op family = new oracle family, never
  perturb existing seeds), unknown-tolerant, **0-disagreement gate** @ 200
  iters. Generator mixes: all-literal (fold path), literal-haystack +
  symbolic `u` / symbolic `i` (partial-eval paths), symbolic haystack
  (fence path), nested in concat/len/eq at both polarities.
- Existing oracle families (`qfs_matches_z3`, `qfs_predicates_matches_z3`,
  seed `0xB000_9E38` nary family, fp-bridge str family) untouched.

## Non-goals

- `str.replace_all` and the regex variants (`str.indexof_re`,
  `str.replace_re`, `str.replace_re_all`) — replace_all shares no encoding
  with replace, regex variants need the RegLan sort. Scoped out
  (user-selected).
- Symbolic-haystack/needle decisiveness — needs negated-containment
  minimality; fenced, flip-markered.
- Negative-polarity string predicates — separate open backlog item
  (slice-12 residue).
- Word-equation completeness (slice-11 cluster-B residue) — untouched.
- No change to substr/at fences, predicate stages, or any existing oracle
  seed.

## Verification

- `cargo nextest run -p shinri-str -p shinri-solver -p shinri-parser` green.
- New oracle family: 0 disagreements @ 200 iters (mise-provided z3).
- e2e pins: decided examples return the pinned verdicts; canaries return
  `unknown`.
- `cargo fmt --all` / clippy clean, per house convention.
