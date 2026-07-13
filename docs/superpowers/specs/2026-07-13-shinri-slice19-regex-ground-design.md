# Slice 19 design — RegLan plumbing + ground str.in_re by Brzozowski derivatives

Date: 2026-07-13
Status: IMPLEMENTED (slice 19 landed 2026-07-13).

Oracle (`qfs_regex_ground_matches_z3`, fresh seed `0x51_63_0000_0001`, 200
iters): 50 sat / 88 unsat / 62 shinri-unknown (tolerated) /
0 z3-unknown / 0 guard-bailout / 17 witnesses / **0
disagreements**. All pre-existing string families re-ran unperturbed with
tallies identical to their committed values.

**Deviations from the spec.**
None. (Production code matches the spec at every operator; the only
implementation-time adjustments were transient clippy `#[allow(dead_code)]`
attributes added in Task 2 and removed in Task 3, and cargo-fmt line
reflows — neither changes behavior or the spec's contract.)

Predecessor: slice 18 (`str.to_code`/`str.from_code`/`str.is_digit`, landed
2026-07-12), which completed roadmap **Spec 4** (conversions). This slice
kicks off the last remaining roadmap item, **Spec 2 — Regular expressions**
(`docs/superpowers/specs/2026-06-24-shinri-qfs-core-design.md`, Spec 2 of 4).
Spec 2 is too large for one slice; this slice establishes the full parse
surface and decides the ground fragment. Symbolic membership is a later
slice.

User-selected envelope: full `RegLan` operator plumbing + ground membership
(literal string × constant regex) at any polarity; everything else fences.
User-selected mechanism: **Brzozowski derivatives** — evaluation by
derivative + nullability over a small regex AST, chosen over NFA compilation
(needs determinization/product for `comp`/`inter`/`diff`; more code and
blowup risk for no ground-fragment benefit) and backtracking matching
(cannot handle `comp`/`inter` structurally).

## Goal

Decide, with zero search and no engine changes, `str.in_re(s, R)` at **any
polarity, any position, any occurrence count**, whenever:

- `s` is a string literal, and
- `R` is a **constant regex**: a `RegLan` term built from the operator
  surface below whose every `str.to_re` argument is a string literal and
  whose every `re.range` endpoint is a string literal.

The atom folds to `true`/`false` — a full logical equivalence (it is
evaluation), so no polarity tracking, no model repair, no fresh variables.
Everything else — symbolic string side, symbolic regex side, `RegLan`
equality, any other `RegLan`-sorted context — survives to a **presence
fence** and returns sound `Unknown`, never a wrong verdict.

## Operator surface (all of SMT-LIB RegLan — everything parses this slice)

| Operator | Arity/kind | Semantics note |
|---|---|---|
| `str.to_re` | String → RegLan | `{s}` — constant only when the arg is a literal |
| `re.none` | const | ∅ |
| `re.all` | const | Σ* |
| `re.allchar` | const | Σ (single char; alphabet `0x0..=0x2FFFF` incl. surrogates) |
| `re.++` | n-ary (≥2) | concatenation |
| `re.union` | n-ary (≥2) | union |
| `re.inter` | n-ary (≥2) | intersection |
| `re.*` | unary | Kleene star |
| `re.+` | unary | Kleene plus |
| `re.opt` | unary | option (`R ∪ {ε}`) |
| `re.comp` | unary | complement w.r.t. Σ* |
| `re.diff` | n-ary (≥2, left-assoc) | difference |
| `re.range` | String × String → RegLan | char range; **empty** if either endpoint is not a single char, or `lo > hi` |
| `(_ re.loop lo hi)` | indexed unary | `lo > hi` ⇒ empty; bounds are lazy (no expansion) |
| `(_ re.^ n)` | indexed unary | ≡ `(_ re.loop n n)` |

This completes the parseable `RegLan` operator surface in one slice, the
way slice 18 completed the conversion surface — but only ground membership
*decides*.

## Evaluation mechanism

`mem(s, R) = nullable(deriv(cₙ, … deriv(c₁, R)))` where `c₁…cₙ` are the
characters of `s` — exactly `|s|` derivative steps.

- `re.loop`/`re.^` counters decrement lazily per consumed character; huge
  bounds cost nothing (no expansion ever happens).
- `comp`, `inter`, `diff` have native derivative rules
  (`deriv(c, comp R) = comp(deriv(c, R))`, etc.) and native nullability
  (`nullable(comp R) = ¬nullable(R)`); no automaton is built.
- Smart constructors keep derivatives canonical and small (∅-absorption,
  ε-collapsing, n-ary flattening, idempotent-duplicate removal where
  cheap).
- A defensive **fuel cap** bounds derivative AST node count: if any
  intermediate derivative exceeds **10,000 nodes**, the atom simply does
  not fold and the presence fence returns a sound `Unknown` — same
  posture as the wordeq fuel. The constant lives in `regex.rs`; only
  pathological inputs reach it.

## Architecture

**shinri-core** (`sort.rs`, `term.rs`, `context.rs`):

- New `SortNode::RegLan` + a `reglan_sort()` accessor (mirrors
  `string_sort()`).
- New `BuiltinOp` variants: `StrInRe` (String × RegLan → Bool), `StrToRe`
  (String → RegLan), `ReNone`, `ReAll`, `ReAllChar` (RegLan consts),
  `ReConcat`, `ReUnion`, `ReInter`, `ReDiff` (n-ary ≥2), `ReStar`,
  `RePlus`, `ReOpt`, `ReComp` (unary), `ReRange` (String × String →
  RegLan), and indexed `ReLoop { lo: u32, hi: u32 }`, `RePow(u32)` —
  payload-carrying like `BvExtract`/`BvRepeat`.
- `mk_app` sort checks mirror the existing string-op checks; context unit
  tests per variant.
- Loop/power indices above `u32::MAX` → parse-time diagnostic, same
  discipline as the existing `BvIndex`/`FpIndex` range errors (an error is
  not a verdict; soundness unaffected).

**shinri-parser**: recognize the `"RegLan"` sort name; the non-indexed
`re.*` symbols and `str.in_re`/`str.to_re`; extend `parse_indexed_op` for
`(_ re.loop lo hi)` and `(_ re.^ n)` (it already returns payload-carrying
`BuiltinOp`s).

**shinri-str** — new module `crates/shinri-str/src/regex.rs`:

1. A small **private** `Rex` AST with smart constructors enforcing the
   canonical forms above — this is what keeps derivative growth tame.
2. `extract_const_regex(ctx, tid) -> Option<Rex>` — structural
   translation; `None` on any non-constant leaf (symbolic `str.to_re`
   argument, non-literal `re.range` endpoint, `RegLan` variable or any
   non-builtin `RegLan` application).
3. `nullable(&Rex) -> bool` and fuel-capped `deriv(c, &Rex)`.
4. `rewrite_ground_in_re(ctx, assertions) -> Vec<TermId>` — one bottom-up
   memoized pass folding ground `StrInRe` atoms to `true`/`false`.
   Untouched subtrees keep their TermIds.
5. `has_unreduced_regex(ctx, assertions) -> bool` — presence fence: any
   surviving `StrInRe` application or `RegLan`-sorted subterm ⇒ the solver
   returns `Unknown`.

**shinri-solver** (`lib.rs`, string path): call `rewrite_ground_in_re`
immediately after the code_conv stage (`lib.rs:467` region as of slice
18), then the fence alongside the other `has_unreduced_*` checks.
Additionally, a query that **declares** a `RegLan`-sorted uninterpreted
symbol fences to `Unknown` — `RegLan` can never reach model construction,
so no model-printer changes.

**string_stage.rs**: add the regex ops to the `is_string_op` inventory so
the mixed-theory fences (UF / BV / arrays) cover them; update the module
doc's operator list.

**No changes** to the word-equation engine, arith seam, budgets, existing
fuel, model construction, or printing — same posture as slice 18.

## Soundness

- The fold is evaluation — a full logical equivalence at any polarity,
  introducing no fresh variables. Anything not folded fences to `Unknown`.
  Both verdicts preserved everywhere; no repair machinery, no demotion, no
  bound.
- **Fuel**: exhaustion means no fold → fence → sound `Unknown`, never a
  wrong verdict.
- **Surrogates need no fence here** — unlike slice 18. Ground evaluation
  only takes derivatives w.r.t. characters of a Rust literal (which cannot
  encode surrogates) and never enumerates the alphabet or instantiates
  witness characters; `re.range` endpoints are literals too.
  `re.allchar`/`re.comp`'s inclusion of surrogates in Σ is respected
  vacuously: nullability is syntactic and derivatives are only taken at
  concrete non-surrogate characters.
- **Above-alphabet fence**: Rust literals *can* contain characters in
  `0x30000..=0x10FFFF`, outside the SMT-LIB alphabet (slice-18
  precedent). If the ground string or any `re.range` endpoint contains
  such a character, the fold is skipped → fence → `Unknown`, rather than
  guessing semantics solvers may disagree on.
- Empty-range shapes (`re.range` with a non-single-char endpoint, or
  `lo > hi`) and `re.loop` with `lo > hi` fold to ∅ per SMT-LIB —
  decided, not fenced.

## Non-goals (future slices of Spec 2)

- Symbolic-string membership against a constant regex — derivative-based
  unfolding into word equations; the `Rex` machinery built here is the
  seed. Fences.
- Symbolic regex sides, `RegLan` equality/containment/emptiness. Fences.
- `to_code` inequality atoms via a character-range gadget (banked in the
  slice-18 spec as pairing naturally with regex ranges).
- `str.<` / `str.<=` lexicographic ordering — still unparsed; separate
  future slice.
- Any change to the word-equation engine, arith seam, budgets, or fuel.

## Testing

- **Unit tests** (`regex.rs`): smart-constructor canonicalization;
  nullability + derivative rule per operator; boundary lattice — `""`
  against every constant, `to_re ""`, `re.range` multi-char / reversed /
  equal endpoints, `loop lo>hi`, `loop 0 0`, `re.^ 0`, `comp(none)` /
  `comp(all)`, nested `comp(comp(R))`, `inter`/`diff` interplay;
  fuel-exhaustion path; above-alphabet fence; `extract_const_regex` `None`
  cases; TermId stability of untouched subtrees.
- **Context/parser unit tests**: sort checks per new `BuiltinOp`; parse
  round-trips including the indexed forms; loop-index overflow
  diagnostic.
- **E2e pins** (`shinri-solver` tests): sat/unsat pins through the full
  solver with atoms under `not`/`or`/`ite`; `Unknown` pins for symbolic
  string side, symbolic regex leaf, `RegLan` equality, declared `RegLan`
  constant, above-alphabet literal. No canary flips expected — these
  operators were previously unparseable, so no existing test can contain
  them.
- **Differential oracle**: new family `qfs_regex_ground_matches_z3` under
  `--features oracle`, fresh seed, 200 iters — random constant-regex ASTs
  of bounded depth weighted across *all* operators × ground strings over
  a small **ASCII-only** alphabet (`{a,b,c}`; shinri's parser does not
  decode `\u{...}` escapes and z3 reads raw UTF-8 byte-wise — the
  slice-18 witness-harness lesson — so non-ASCII in a script shared with
  z3 is a harness-semantics mismatch, not a solver signal; non-ASCII and
  above-alphabet membership is covered by unit tests and shinri-only
  pins) — positive-biased by
  sampling matching strings via a regex walk on the `comp`/`inter`-free
  subset, with the small alphabet keeping random hits likely for
  `comp`/`inter` shapes; ~25% negation wrapping; unknown-tolerant;
  **0 disagreements required**. All existing string families re-run
  unperturbed with identical tallies.
- **Gates**: `cargo test -p shinri-core -p shinri-parser -p shinri-str
  -p shinri-solver --features oracle`, `cargo fmt --check`,
  `cargo clippy --workspace --all-targets` clean; the ~50-min full
  workspace run stays CI-side.
