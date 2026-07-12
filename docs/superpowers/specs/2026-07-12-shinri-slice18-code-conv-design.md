# Slice 18 design — str.to_code / str.from_code / str.is_digit by exact rewriting

Date: 2026-07-12
Status: Approved design, pre-implementation.

Predecessor: slice 17 (constant-RHS `to_int`/`from_int` decision stage,
landed 2026-07-12). This slice adds the **last Spec-4 operators** —
`str.to_code`, `str.from_code` — plus `str.is_digit`, completing the
conversion spec's operator surface (`docs/superpowers/specs/
2026-06-24-shinri-qfs-core-design.md`, roadmap Spec 4 of 4).

User-selected envelope: fold + constant-RHS equivalences (symbolic linking
fences). User-selected approach: new `code_conv.rs` module with a **single
exact rewrite pass + presence fence** — the slice-15/17 three-stage split
collapses because every rewrite in this fragment is a full logical
equivalence (no model repair, no polarity restriction, no occurrence
counting, no length-pin expansion).

## Goal

Decide, with zero search and no new engine risk, both verdicts everywhere:

- `str.to_code(s) = k` for any numeral `k` — exact equivalence rewrites,
  any polarity, any occurrence count.
- `str.from_code(n) = "lit"` for any string literal — likewise.
- `str.is_digit(t)` for any string term — full expansion, decided
  everywhere.
- Literal folding and both roundtrip rewrites.

Everything outside the fragment fences to sound `Unknown` via a presence
fence — never a wrong verdict.

## Semantics (SMT-LIB 2.6)

- `str.to_code(s)`: the code point of `s`'s single character if `|s| = 1`,
  else `-1`.
- `str.from_code(n)`: the singleton string of code point `n` if
  `0 <= n <= 0x2FFFF` (the SMT-LIB alphabet), else `""`.
- `str.is_digit(s)`: true iff `|s| = 1` and the character is `'0'..='9'`
  (codes `0x30..=0x39`) — ASCII digits only, same discipline as
  `int_conv.rs`.

## Rewrite catalog

Every rule is a full equivalence — sound at any position, any polarity,
any occurrence count. No fresh variables are introduced by this module
(the only fresh symbol downstream is the `!ite` var that
`elim_term_ite` mints for the roundtrip ites, as established in slice 15).

| # | Shape | Rewrites to |
|---|-------|-------------|
| 1 | `to_code("lit")`, `from_code(k)`, `is_digit("lit")` (all-literal) | folded literal (value-level) |
| 2 | `to_code(from_code(n))` | `ite(0 <= n <= 0x2FFFF, n, -1)` |
| 3 | `from_code(to_code(s))` | `ite(len(s) = 1, s, "")` |
| 4 | `to_code(s) = k`, `k` in `0..=0x2FFFF`, non-surrogate | `s = "<char k>"` |
| 5 | `to_code(s) = -1` | `not (len(s) = 1)` |
| 6 | `to_code(s) = k`, `k <= -2` or `k > 0x2FFFF` | `false` |
| 7 | `from_code(n) = "c"` (single char, code `<= 0x2FFFF`) | `n = code(c)` |
| 8 | `from_code(n) = ""` | `n < 0 \/ n > 0x2FFFF` |
| 9 | `from_code(n) = "lit"` (multi-char, or char `> 0x2FFFF`) | `false` |
| 10 | `is_digit(t)` (any string term `t`) | `t = "0" \/ ... \/ t = "9"` |

Equality atoms match in **either orientation** (literal on the left or
right). Rules 4–9 apply wherever the atom sits (under `not` / `or` /
`ite`) — equivalences need no polarity tracking.

Rule 9's above-alphabet case: Rust `char` reaches `0x10FFFF`, so an input
literal can contain characters above the SMT-LIB alphabet cap `0x2FFFF`;
`from_code` never produces one, so equality with such a literal is `false`.

Note rule 5 decides `to_code(s) = -1` exactly — "not a single char" is a
plain LIA atom. The analogous open `to_int` case (`k = -1` under a length
pin) needed a "non-digit at some position" gadget and remains future work
there; it is free here.

### Representational fence: surrogates

`shinri-core` stores string literals as Rust `Box<str>`, which cannot hold
surrogate code points (`0xD800..=0xDFFF`) even though the SMT-LIB alphabet
includes them. Therefore:

- `from_code(k)` for surrogate `k` does **not** fold (rule 1 skips it);
- `to_code(s) = k` for surrogate `k` does **not** rewrite (rule 4 skips it);

both survive to the presence fence and the query returns a sound
`Unknown`. Input literals cannot contain surrogates (the parser does not
decode `\u{...}` escapes and Rust source text cannot encode lone
surrogates), so rules 7–9 need no surrogate case on the literal side.

## Non-goals (future work)

- Symbolic linking (`to_code(s) = n0`, `from_code(n) = t` with non-literal
  `t`) — needs a char/code seam or the lazy DPLL(T) propagator; fences.
- Inequality atoms (`to_code(s) >= k` etc.) — character-range constraints
  are not expressible as word equations without a range gadget; fences.
- Nested-arithmetic shapes (`to_code(s) + 1 = k`); fences.
- `str.<` / `str.<=` (lexicographic ordering) — still unparsed; separate
  future slice.
- Any change to the word-equation engine, arith seam, budgets, or fuel.

## Architecture

**shinri-core** (`term.rs`, `context.rs`): three new `BuiltinOp` variants —
`StrToCode` (String → Int), `StrFromCode` (Int → String), `StrIsDigit`
(String → Bool) — with `mk_app` sort checks mirroring
`StrToInt`/`StrFromInt`, plus context unit tests.

**shinri-parser**: recognize `str.to_code`, `str.from_code`,
`str.is_digit`.

**shinri-str** — new module `crates/shinri-str/src/code_conv.rs`:

1. `rewrite_code_conv(ctx, assertions) -> Vec<TermId>` — one bottom-up
   memoized pass applying the whole catalog: value-level folds, both
   roundtrip rewrites, constant-RHS atom equivalences, `is_digit`
   expansion. Untouched subtrees keep their TermIds. One subtlety:
   expansion can mint atoms that are themselves reducible
   (`is_digit(from_code(n))` expands to `from_code(n) = "0" \/ ...`, each
   of which is const-RHS rule 7) — minted equality atoms route back
   through the same atom-rewrite helper, so a single pass suffices; no
   fixpoint loop.
2. `has_unreduced_code_conv(ctx, assertions) -> bool` — presence fence:
   any surviving `StrToCode` / `StrFromCode` / `StrIsDigit` application
   ⇒ the solver returns `Unknown`.

**shinri-solver** (`lib.rs`, string path): call `rewrite_code_conv`
immediately after the int_conv stages (`lib.rs:447-452` as of slice 17),
then the fence alongside `has_unreduced_int_conv`. No repair list, no
outcome-match change, no new cross-component state. The string-valued ite
from rule 3 flows into the existing `elim_term_ite`, same as int_conv's
roundtrip ite.

**string_stage.rs**: add the three ops to the `is_string_op` inventory so
the mixed-theory fences (UF / BV / arrays) cover them; update the module
doc's operator list.

**No changes** to the word-equation engine, arith seam, budgets, fuel,
model construction, or printing — the fence guarantees no application
survives to model time, and folded literals print through the existing
string-literal path.

## Soundness

Every rewrite is a full logical equivalence introducing no fresh
variables; anything not rewritten fences to `Unknown`. Both verdicts
preserved everywhere — no demotion flag, no bound, no repair machinery
(slice 17's R2/R4 are not needed). Digit classification is exactly
`'0'..='9'`, never `char::is_numeric()`.

## Testing

- **Unit tests** (`code_conv.rs`): one test per catalog row plus the
  boundary lattice `k ∈ {-2, -1, 0, 0x39, 0xD7FF, 0xD800, 0xDFFF, 0xE000,
  0x2FFFF, 0x30000}` for both ops; `from_code(n) = ""` / single-char /
  multi-char / above-alphabet-char literals; `is_digit` on `"0"`, `"9"`,
  `"a"`, `""`, multi-char; both equality orientations; atoms under
  `not` / `or` / `ite`; the minted-atom chain (`is_digit(from_code(n))`
  reducing fully to a LIA disjunction); the surrogate fence; TermId
  stability of untouched subtrees.
- **E2e pins** (`shinri-solver` tests): small sat/unsat instances through
  the full solver with `get-value` checks. No canary flips this slice —
  these operators were previously unparseable, so no existing test can
  contain them.
- **Differential oracle**: new family `qfs_code_conv_matches_z3` under
  `--features oracle`, fresh seed, 200 iters — random constant-RHS shapes
  across the boundary values above, roundtrip nestings, `is_digit` over
  literals / vars / `from_code`, ~25% negation wrapping, occasional extra
  occurrences of the argument, unknown-tolerant, witness-checking
  (get-value models validated by z3), **0 disagreements required**. The
  five existing string families re-run unperturbed with existing seeds;
  `qfs_to_from_int_matches_z3` tallies must be identical (this slice does
  not touch int_conv).
- **Gates**: `cargo test -p shinri-str -p shinri-solver --features
  oracle`, `cargo fmt --check`, `cargo clippy --workspace --all-targets`
  clean; the ~50-min full workspace run stays CI-side.

## Future work

- Symbolic linking for `to_code` / `from_code` — a natural first customer
  for the lazy DPLL(T) propagator slice (single-character domain is far
  smaller than `to_int`'s); design constraints in
  `docs/superpowers/research/2026-07-11-eager-digit-bridge-infeasibility.md`
  apply.
- Inequality atoms over `to_code` (character ranges) — pairs naturally
  with a future regex/range gadget (Spec 2).
- `str.<` / `str.<=` lexicographic ordering.
