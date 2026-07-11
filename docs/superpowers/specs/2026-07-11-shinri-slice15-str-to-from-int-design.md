# Slice 15 design — str.to_int / str.from_int (fold + exact rewrites + fence)

Date: 2026-07-11
Status: DESIGN APPROVED (not yet implemented).
Predecessor: slice 14 (str.replace_all, landed 2026-07-10, PR #8). Sibling
lineage: slice 13 (str.indexof / str.replace, PR #7) — this slice follows its
fold + exact-partial-eval + sound-fence template closely.

## Goal

Admit `str.to_int` and `str.from_int` — today parser `unknown operator` — via
the slice-13 shape (user-selected over a bounded digit-encoding bridge and over
fold-only):

- **Constant-fold** all-literal applications to their concrete value (exact,
  both directions).
- **Exact rewrite** the one shape where the two ops compose exactly: the
  roundtrip `str.to_int(str.from_int(n))` → `ite(n ≥ 0, n, -1)`, polarity-free,
  for any Int term `n`.
- **Fence** every other occurrence (symbolic string argument to `str.to_int`;
  symbolic, non-roundtrip Int argument to `str.from_int`) to sound `Unknown`,
  canary-pinned as flip-markers for a future digit-bridge slice.

Structural property (as in slice 13): both ops are value-sorted **functions**
(Int-sorted and String-sorted), not predicates. The fold is exact at any
position and polarity; the roundtrip rewrite is exact and polarity-free. The
pass introduces **zero fresh variables** of its own — the only fresh variable
is the `!ite` the existing `elim_term_ite` already mints for the roundtrip's
Int-sorted `ite`, with model filtering long in place (slices 5/7). No new
model-filtering or get-value surface.

Why not decide symbolic `str.to_int` / `str.from_int`: their general semantics
require per-character digit-classification and digit/length arithmetic — a
bounded completeness concession (like replace_all's symbolic-`u`), not an exact
rewrite. Deferred (see §5).

## Pinned SMT-LIB 2.6 semantics (the traps)

- **`str.to_int : String → Int`**:
  - Returns the numeric value **iff** the string is a **non-empty sequence of
    ASCII decimal digits** (code points U+0030–U+0039). Leading zeros are
    allowed: `str.to_int "007" = 7`, `str.to_int "0" = 0`.
  - **`-1`** for: the empty string; any string containing a non-digit; a sign
    char (`str.to_int "-5" = -1`, `str.to_int "+5" = -1`); whitespace; and — the
    **non-ASCII trap** — any Unicode character that is a "digit"/"numeric" by
    Unicode category but is **not** ASCII 0–9 (e.g. Arabic-Indic ٣ U+0663,
    fullwidth ３ U+FF13). A naive `char::is_numeric()` / `is_ascii_digit()`
    confusion here is unsound; classification must be exactly `('0'..='9')`.
  - **Arbitrary precision**: a 100-digit string yields a big integer;
    `shinri`'s `Rational` handles it (no i64/i128 overflow).
- **`str.from_int : Int → String`**:
  - For `n ≥ 0`: canonical decimal with **no leading zeros** (`str.from_int 0 =
    "0"`, `str.from_int 42 = "42"`).
  - For `n < 0`: the **empty string** `""` (not `"-1"`, not `"-5"` — it returns
    a String, and the defined result on negatives is empty).

Roundtrip facts (justify §2.2):
- `str.to_int(str.from_int(n)) = n` for `n ≥ 0` (canonical digits are recovered
  exactly), and `= str.to_int("") = -1` for `n < 0`. Hence the exact rewrite to
  `ite(n ≥ 0, n, -1)`.
- `str.from_int(str.to_int(s))` is **not** identity (e.g. `s = "007"` →
  `from_int(7) = "7" ≠ "007"`; `s = "x"` → `from_int(-1) = ""`), so there is no
  reverse rewrite.

## 1. Surface changes

- `shinri-core`: two new `BuiltinOp` variants — `StrToInt` with sort rule
  `String → Int`, `StrFromInt` with sort rule `Int → String` — arity/sort
  checked in `context.rs` alongside the other `Str*` ops.
- `shinri-parser`: parse both ops with arity/sort checks; `print.rs`
  round-trips them. Surface names are the SMT-LIB 2.6 standard `str.to_int` /
  `str.from_int` — the forms the oracle's z3 accepts, since the differential
  harness builds `shinri` terms and prints them for z3.
- `shinri-str::reduce::contains_string_op`: add both variants so a query that
  is pure arithmetic-plus-conversion (e.g. `str.to_int x = k`) still routes onto
  the string path where this pass runs (same wiring slices 12–14 used).

## 2. New pre-pass module `shinri-str/src/int_conv.rs`

One bottom-up, TermId-memoized rewrite:

```
pub fn partial_eval_int_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId>
```

Cases, applied after children are rewritten (nested occurrences compose):

### 2.1 Fold — literal argument

- `str.to_int(w)` where `w` is a string literal → Int numeral per the pinned
  semantics (including `-1`). Evaluated on `Vec<char>` (code points), classifying
  digits as exactly `('0'..='9')`. Value accumulated in `Rational` /
  arbitrary-precision integer — no fixed-width overflow.
- `str.from_int(k)` where `k` is an Int numeral → string literal per the pinned
  semantics (`""` when `k < 0`; no leading zeros otherwise).

(Literal-concat arguments like `str.to_int("1" ++ "2")` are folded to
`str.to_int("12")` by the existing concat normalization *before* this pass, so
no special concat case is needed here. A `str.from_int(3 + 4)` folds only if the
arithmetic simplifier has already reduced `3 + 4 → 7`; if not, it soundly fences
— acceptable incompleteness.)

### 2.2 Exact roundtrip rewrite — `str.to_int(str.from_int(n))`

For any Int term `n` (literal or symbolic), rewrite to:

```
ite(n ≥ 0, n, -1)
```

Exact and polarity-free per the roundtrip facts above. The chain is an
Int-sorted `ite`; the existing `elim_term_ite` in `reduce_assertions` (runs
later on the string path) eliminates non-Boolean `ite` soundly into a fresh
`!ite<n>` var + implications, with model filtering in place since slices 5/7 —
no new machinery. This is the **only** non-fold decision the slice makes.

### 2.3 Everything else

Rebuild with rewritten children if changed, else keep the original `TermId`
(structural-sharing convention of `partial_eval_indexof_replace` / `rewrite`).

Fence predicate, same presence style as `has_unreduced_indexof_replace`:

```
pub fn has_unreduced_int_conv(ctx: &Context, assertions: &[TermId]) -> bool
```

True iff any `StrToInt` / `StrFromInt` application survives the rewrite —
i.e. a symbolic string argument to `str.to_int`, or a symbolic/non-roundtrip
Int argument to `str.from_int`.

## 3. Pipeline wiring (shinri-solver string path)

Insert alongside the slice-13/14 rewrites (after `fold_str_predicates`, among
the independent rewrites/fences — ordering is immaterial, but the partial-eval
must run before its own fence):

1. `assertions = shinri_str::int_conv::partial_eval_int_conv(…)` —
   unconditional (polarity-free, exact).
2. `if shinri_str::int_conv::has_unreduced_int_conv(…)` →
   `return SolveOutcome::Unknown` — sound fence, canary-pinned as flip-markers
   for a future digit-bridge slice.

Downstream stages consume the rewrite's output: the roundtrip's `ite` chain is
eliminated by `elim_term_ite` into length-free LIA the Int seam already owns;
folded results are ordinary literals. `get-value` on a surviving symbolic
application is moot — it fences pre-solve, consistent with substr / slices
13–14.

## 4. Testing

- **Unit** (`int_conv.rs` tests): fold edges — leading zeros (`"007" = 7`,
  `"0" = 0`), empty → `-1`, embedded non-digit → `-1`, sign chars (`"-5"`,
  `"+5"`) → `-1`, **non-ASCII Unicode digit → `-1`** (the trap: ٣ U+0663,
  fullwidth ３ U+FF13), big-int (30+ digit) roundtrip both directions,
  `from_int(0) = "0"`, negative `from_int` → `""`; roundtrip rewrite shape
  (both `ite` arms, `n` symbolic); memo dedup (repeated app → same rewritten
  term); fence-predicate classification (symbolic survives, folded / roundtrip
  do not).
- **e2e script pins** (`script_e2e`): decided **sat AND unsat** examples through
  both the fold and the roundtrip paths; a symbolic `str.to_int` / `str.from_int`
  → `unknown` fence canary as a flip-marker.
- **New differential oracle family** `qfs_to_from_int_matches_z3` — own **fresh
  seed** (new op family = new oracle family, never perturb existing seeds),
  unknown-tolerant, **0-disagreement gate @ 200 iters**. Generator mixes:
  all-literal (fold path), `str.to_int(str.from_int(n))` roundtrip composition
  (decided path), symbolic string / Int arguments (fence path), nested in
  `str.++` / `str.len` / `=` / arithmetic at both polarities.
- Existing oracle families (`qfs_matches_z3`, `qfs_predicates_matches_z3`,
  `qfs_indexof_replace_matches_z3`, `qfs_replace_all_matches_z3`, the nary and
  fp-bridge str families) **untouched**.

## 5. Out of scope

- **Bounded digit bridge** for symbolic `str.from_int(n)` (digit-count `ite`
  chain + div/mod into LIA) and symbolic `str.to_int(u)` (per-character digit
  constraints) — a completeness concession deferred to a follow-up slice. This
  slice therefore leaves `str.to_int(x) = 5` and `str.from_int(x) = "5"` as
  `Unknown` by design.
- **One-sided range abstraction** — replacing a fenced `str.to_int(u)` by a
  fresh Int `v` with the sound relaxation `v ≥ -1` to decide out-of-range
  queries (`str.to_int(x) = -5` → unsat) while staying `Unknown` on sat. Sound
  but requires a one-sided abstraction/refinement mode `shinri` does not have
  today; future slice.
- `str.to_code` / `str.from_code`, `str.is_digit`, lexicographic `str.<` /
  `str.<=`, and all regex (`str.to_re` / `str.in_re` / `str.replace_re`).

## Risks

- **R1 — Unicode-digit trap.** `str.to_int` must classify digits as exactly
  ASCII `('0'..='9')`. Using `char::is_numeric()` (accepts Unicode numerics) or
  conflating it with a locale-aware parse is **unsound** (e.g. would fold
  `str.to_int "٣"` to `3` where z3 returns `-1`). Mitigation: explicit
  `('0'..='9')` classification and dedicated non-ASCII-digit → `-1` unit tests,
  plus the differential oracle generating non-ASCII code points.
- **R2 — negative `from_int` returns `""`, not a sign string.** A naive
  `format!("{n}")` yields `"-5"` for negative `n`; the defined result is the
  empty string. Mitigation: explicit `n < 0 → ""` branch and a dedicated unit
  test asserting the contrast against the positive canonical form.
- **R3 — reverse-roundtrip over-rewrite.** `str.from_int(str.to_int(s))` is
  **not** identity (leading zeros; non-digit → `""`). Only the
  `to_int(from_int(n))` direction may be rewritten. Mitigation: the rewrite
  matches that nesting order only; a unit test pins that the reverse nesting is
  left to fence (or fold, when `s` is literal).
- **R4 — fixed-width overflow on fold.** A long digit string / large `from_int`
  argument must not overflow i64/i128. Mitigation: accumulate in
  `Rational` / arbitrary-precision integers; a 30+ digit roundtrip test.

## Verification

- `cargo nextest run -p shinri-str -p shinri-solver -p shinri-parser` green.
- New oracle family: 0 disagreements @ 200 iters (mise-provided z3).
- e2e pins: decided examples return the pinned verdicts; canaries return
  `unknown`.
- `cargo fmt --all --check` clean (CI fmt gate) and clippy clean, per house
  convention.
