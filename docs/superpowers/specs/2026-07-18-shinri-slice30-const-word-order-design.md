# Slice 30 design — constant-word lexicographic order

Date: 2026-07-18
Status: DESIGN

Predecessor: slice 29 (enumeration↔length exact-length companion, landed
2026-07-18). Slice 29 cashed slice 22's enumeration-length seam gap. The
oldest **named** `_known_gap` pin still live is slice 23 §4's two-free-var
symbolic pair (`targeted_str_order_symbolic_pair_known_gap`,
`crates/shinri-solver/tests/qfs_differential.rs:3915`): `(str.< s u)` over
two free variables returns sound `Unknown`, z3 answers `Sat`. That case is
the acknowledged hard core — it needs the first-differing-position
*existential over a shared symbolic prefix*, i.e. word-equation-engine
work, which every string slice since 19 has held as a standing non-goal.

This slice does **not** cash that pin. It takes the bounded pure-rewrite
step adjacent to it: generalize slice 24's *single-character* constant
order arms to *any-length* constant words, shrinking the ordering fence
without touching the engine, and cashing slice 24 §5's inline
"multi-char constant ⇒ banked" item (`order.rs`, the two `None` arms). The
two-free-var pin stays banked and remains the oldest live gap — a
conscious, recorded deviation from the strict "cash the oldest pin"
convention, justified because the pure-rewrite ceiling cannot reach a
two-free-var comparison at all.

## 1. Problem — the constant side is capped at one character

`order.rs` (slice 23/24) rewrites `str.<`/`str.<=` to regex membership
when one side is a constant, but **only for a single-character constant**
(`single_char_code`, `order.rs:129`; the multi-char arms return `None` at
`order.rs:114` and `order.rs:120`, so a length-≥2 literal survives to the
fence and the query goes `Unknown`). Yet lexicographic comparison against
*any* fixed word is a regular language — the single-character rewrite is
just the k=1 case of a general construction. Everything above k=1 is
fenced today purely because the construction was never generalized, not
because it is undecidable in the pure-rewrite fragment.

Verified empirically (`multi_char_const_right_survives_to_fence`,
`order.rs:354`): `(str.< s "bc")` survives the rewrite and fences.

## 2. Fix — the general constant-word membership

For a constant word `w = c₀…c_{k-1}` (k ≥ 1, every `cᵢ ≤ MAX_CODE`) and a
symbolic `s`, replace the atom with `(str.in_re s R)`:

```
s <  w  ≡  s ∈  Eps ∪ { word(w[0..j]) : 1 ≤ j ≤ k-1 }        (proper prefixes of w)
                ∪ ⋃ᵢ  word(w[0..i]) · Range(0, cᵢ-1) · Σ*    (first differ at i, sᵢ < cᵢ)
s <= w  ≡  (above) ∪ word(w)                                 (… or s = w)

w <  s  ≡  s ∈  ⋃ᵢ  word(w[0..i]) · Range(cᵢ+1, MAX) · Σ*    (first differ at i, sᵢ > cᵢ)
                ∪ word(w) · Σ · Σ*                           (w a PROPER prefix of s)
w <= s  ≡  ⋃ᵢ (differ branches) ∪ word(w) · Σ*              (… or w a prefix incl. equality)
```

`word(w[0..i])` is the concat of singletons `Range(cⱼ, cⱼ)` for `j < i`
(`word(w[0..0]) = Eps`). Each interior class `Range(0, cᵢ-1)` /
`Range(cᵢ+1, MAX)` is built with the existing `range_rex`; empty intervals
(`cᵢ = 0` below, `cᵢ = MAX_CODE` above) fold away in `union`/`concat` as
they do for k=1.

**k=1 collapse (regression safety).** At k=1 the proper-prefix set is just
`{Eps}`, the single below-branch is `Range(0, c₀-1)·Σ*`, and the left
form is `Range(c₀+1, MAX)·Σ* ∪ word(c₀)·Σ·Σ*` — verbatim the current
`order_const_right` / `order_const_left`. The generalization is strict; the
existing single-char unit tests pass unchanged.

Details:

- **Refactor.** `single_char_code(&str) -> Option<i128>` becomes
  `word_codes(&str) -> Option<Vec<i128>>` (`None` if any char `> MAX_CODE`
  or the word length exceeds the cap below). `order_const_right` /
  `order_const_left` take `&[i128]` and emit the k-branch unions above.
  The three constant-matching arms of `try_order_atom` (empty-string is
  handled earlier; single-char; multi-char) collapse into one
  constant-word arm — the multi-char `None` returns are deleted.
- **Cap.** `const ORDER_CONST_LEN_CAP: usize = 256` (mirrors
  `ENUM_WORD_CAP`). A constant word longer than the cap ⇒ `word_codes`
  returns `None` ⇒ atom survives ⇒ fence to `Unknown`. Purely defensive:
  SMT-LIB literal text is untrusted input (threat model), and a length-k
  word builds an O(k)-branch regex; the cap bounds that. Skipping is
  always sound — it only ever weakens a would-be answer to `Unknown`.
- **Above-alphabet char.** Any `cᵢ > MAX_CODE` ⇒ fence, exactly as
  `single_char_code` fences today (guards the surrogate/`MAX_CODE` Range
  policy).
- **Both-constant / empty / reflexive cases unchanged.** Literal–literal
  fold, the empty-string boundary idioms, and syntactic reflexivity all
  fire before the constant-word arm (`order.rs:74`–`110`); this slice
  changes only the one-symbolic-side constant path.

## 3. Soundness

`{s : s <ₗₑₓ w}` (and the three sibling relations) is **exactly** the
regular language above — a standard fact of lexicographic order on a fixed
word: `s < w` iff either `s` is a proper prefix of `w`, or `s` and `w`
first differ at some position `i` with `sᵢ < cᵢ` (and then the suffix of
`s` is unconstrained). So each rewrite is a **two-way equivalence**, sound
at any polarity, nesting, or occurrence count — no polarity fence, the same
posture slice 23/24 established. Folding on Rust `&str` is code-point order
(UTF-8 is code-point-order-preserving byte-wise), so the `word`/`Range`
codes agree with SMT-LIB `str.<`/`str.<=`.

**No surrogate fence for in-alphabet words.** Every `cᵢ` is a valid Rust
`char`, so its neighbours `cᵢ-1` / `cᵢ+1` are at worst the surrogate block
**edges** (`0xDFFF` when `cᵢ = 0xE000`; `0xD800` when `cᵢ = 0xD7FF`), which
`range_rex` expresses. An interior surrogate endpoint therefore never
arises, and the whole construction reduces without fencing for any word
whose chars are all ≤ `MAX_CODE`. The rewrite itself decides nothing; the
downstream membership engine does, routed identically to the single-char
case.

## 4. Testing

**Unit (`order.rs`).**

- Flip `multi_char_const_right_survives_to_fence` → a *now-rewrites* test:
  assert the exact `s < "bc"` and `s <= "bc"` unions (both ops), plus the
  left forms `"bc" < s` / `"bc" <= s`.
- Astral / block-edge word (a `cᵢ` at a surrogate block edge — e.g.
  `\u{E000}` interior — must not fence).
- Cap fence: a 257-char constant word survives the rewrite (fences), a
  256-char word does not.
- k=1 single-char tests (`single_char_const_right_rewrites`,
  `single_char_const_left_rewrites`, the null-char and max-char and
  block-edge variants) pass **unchanged** — the strict-generalization
  regression guard.

**e2e pins (`qfs_differential.rs`, z3-cross-checked via `expect`).** One
per route:

- Right constant, `<`: `(str.< s "bc") ∧ (= s "bd")` → Unsat; a decided
  Sat witness (e.g. `(str.< s "bc") ∧ (= s "az")` → Sat).
- Left constant: `(str.< "bc" s) ∧ (= s "ba")` → Unsat;
  `(str.< "bc" s) ∧ (= s "bca")` → Sat (proper-prefix branch).
- `<=` boundary: `(str.<= s "bc") ∧ (= s "bc")` → Sat;
  `(str.< s "bc") ∧ (= s "bc")` → Unsat (strict excludes equality).
- **Non-regression:** `targeted_str_order_symbolic_pair_known_gap` stays
  `Unknown` (this slice does not cash the two-free-var gap) — asserted
  explicitly so a future reroute trips a test.

**Differential oracle** (house cadence: `--features oracle`, run
foreground with captured output — see AGENTS.md / oracle-gate memory).
Extend the `qfs_str_order_matches_z3` generator to emit **multi-char
ASCII-literal** comparisons (one side literal, one side free var), on top
of the existing literal–literal / empty-boundary / free-var mix. Expect:
**shinri-unknowns down** (the multi-char-literal shapes now decide),
**0 shinri-vs-z3 disagreements**. Non-ASCII literals stay excluded (the
pre-existing z3-CLI byte-comparison artifact slice 23 §5 documents). The
other string/regex families re-run with tallies **unchanged** — any
movement is a finding to adjudicate.

Per-iteration dump-and-diff (base vs fix): every flip `Unknown → decided`;
zero `decided → Unknown`, zero `sat ↔ unsat`.

**Gate list** (run locally pre-push): `shinri-str`,
`qfs_differential --features oracle`, `script_e2e` — a completeness-shifting
string change can flip string-side e2e pins; any z3-confirmed
`Unknown → decided` flip is an adjudicated flip, not a blocker
(slice-25/26/28/29 precedent). Plus
`cargo clippy --workspace --all-targets -- -D warnings` and
`cargo fmt --check`.

## 5. Alternatives considered

- **(B) Bounded first-differing-position unfold** (partial two-free-var):
  unfold the split to a bounded depth with fresh per-position `to_code`
  vars, fence the tail. Would make genuine progress on the `_known_gap`
  pin, but introduces fresh vars and touches the code/`str.at` seam —
  breaching the standing word-equation-engine non-goal and pulling in `Fuel`
  interaction. Rejected for this slice; the two-free-var decision stays a
  single, honest, larger future slice rather than a bounded half-measure.
- **(C) Shared-prefix peel:** peel syntactically-equal leading factors
  from `str.< (α·s) (α·u)` and recurse. Pure rewrite, but fires rarely on
  the bare `s < u` shape the pin targets — barely moves the fence. Best as
  a helper composed with the eventual engine slice; not a slice on its own.

## 6. Non-goals (banked)

- **Two-free-var symbolic lexicographic decision** — the
  first-differing-position existential over a shared symbolic prefix
  (slice 23 §4). The `_known_gap` hard core; explicitly requires
  word-equation-engine work. Remains the oldest live gap after this slice.
- **Constant words longer than `ORDER_CONST_LEN_CAP`** — fenced by design.
- **Chained / n-ary `str.<` / `str.<=`**, if the frontend ever admits them
  — binary only, matching the existing arms.
- Any change to the word-equation engine, the regex core, the arith seam,
  `Fuel`, or the SAT budgets.
- Slice-29 standing bank unchanged (approach-C fuel-free constant-length
  propagation, distinct-length sets > `LEN_FACT_DISTINCT_CAP`, co-finite
  memberships, slice-28 §8 conflict-core work, slice-27 typed-antecedent
  refactor).
