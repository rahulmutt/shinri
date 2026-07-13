# Slice 20 design — symbolic `str.in_re` over finite / co-finite constant languages

Date: 2026-07-13
Status: IMPLEMENTED (slice 20 landed 2026-07-13).

Oracle (`qfs_regex_symbolic_matches_z3`, fresh seed `0x52_00_0000_0001`, 200
iters): 101 sat / 68 unsat / 31 shinri-unknown (tolerated) /
0 z3-unknown / 0 guard-bailout (tolerated) / 96 witnesses / **0
disagreements**. The pre-existing code_conv, const_int_conv, and
replace_all families re-ran with tallies identical to their committed
values; `qfs_regex_ground_matches_z3` improved to 66 sat / 107 unsat /
27 shinri-unknown / 31 witnesses (0 disagreements) — an intended effect
of this slice: ground-fold declines (derivative fuel) are now rescued by
the finite/co-finite enumeration rewrite, so strictly more instances are
decided (generator and seed untouched).

**Deviations from the spec.**
Production code matches the spec at every operator (the only
implementation-time adjustments were transient Task-1 clippy
`#[allow(dead_code)]` attributes, added and removed within the slice, as
slice 19 did). Three plan predictions needed correcting:
1. The slice-19 module test `non_ground_shapes_survive_to_fence` had one
   sub-case (symbolic string side over `str.to_re "a"`) that the new
   rewrite now correctly decides; the sub-case was swapped to a `re.*`
   shape so it keeps testing a genuine fence. (The plan predicted no
   non-oracle test pinned the old behavior — one did.)
2. The plan expected all pre-existing oracle tallies to be identical;
   `qfs_regex_ground_matches_z3`'s tally improved as quoted above
   (generator and seed untouched — the solver simply decides more).
3. The plan described the Task-3 pins as "shinri-only"; in fact the
   `expect()` helper cross-checks z3 for Sat/Unsat pins — stricter than
   described. Wording note only.

Predecessor: slice 19 (RegLan plumbing + ground `str.in_re` by Brzozowski
derivatives, landed 2026-07-13). This is the second slice of roadmap
**Spec 2 — Regular expressions**
(`docs/superpowers/specs/2026-06-24-shinri-qfs-core-design.md`, Spec 2 of 4).
Slice 19 established the full parse surface and decided the ground fragment
(literal string × constant regex); its non-goals banked "symbolic-string
membership against a constant regex" with the `Rex` machinery as the seed.
This slice decides the **finite / co-finite** sub-fragment of that item with
zero engine changes; derivative unfolding inside the wordeq engine (for
shapes like `[a-z]*`) stays banked for a later slice.

User-selected envelope (option A of three): pre-pass equivalence rewrite
only — no wordeq-engine changes, no character-range gadget, no new fences.

## Goal

Decide, at **any polarity, any position, any occurrence count**,
`str.in_re(t, R)` whenever:

- `t` is **any** String-sorted term (variable, concat, literal — anything),
  and
- `R` is a **constant regex** (slice-19 sense: every `str.to_re` argument
  and every `re.range` endpoint a literal, no RegLan variables), and
- `L(R)` is **finite** or **co-finite**, as recognized *structurally* by
  the enumerators below within an enumeration fuel cap. (The recognition
  is syntactic, not semantic: a shape like `re.++(re.all, re.all)` is
  semantically Σ* but is not recognized and keeps fencing — sound, just
  undecided.)

The atom rewrites to a full logical equivalence over string equalities:

- finite, `L(R) = {w₁ … wₖ}`:
  `str.in_re(t, R) ↔ (t = w₁ ∨ … ∨ t = wₖ)`; `k = 0` folds to `false`.
- co-finite, `Σ* \ L(R) = {w₁ … wₖ}`:
  `str.in_re(t, R) ↔ ¬(t = w₁ ∨ … ∨ t = wₖ)`; `k = 0` folds to `true`.

No fresh variables, no model repair, no polarity tracking — the produced
equalities are word equations / disequalities the existing engine already
owns (Spec-1 core; slice-11 disequality completeness), and the Boolean
structure goes through Tseitin as usual.

The slice-19 **ground fold stays first**: it is cheaper and also decides
infinite languages when `t` is a literal. The new rewrite fires only when
the ground fold does not apply. Everything else — languages that are
neither finite nor co-finite (`[a-z]*`, `(re.++ Σ* (str.to_re "x"))`),
symbolic regex sides, RegLan equality — keeps fencing to sound `Unknown`
exactly as today.

Decided idioms this unlocks (all previously `Unknown`):

- `x ∈ re.union(str.to_re "GET", str.to_re "POST")` — enumerations.
- `x ∈ re.comp(str.to_re "admin")` — i.e. `x ≠ "admin"`.
- `re.diff(re.all, str.to_re "a")` — co-finite via the `Inter`/`Comp`
  extraction shape.
- `x ∈ (_ re.loop 1 2 (re.range "a" "c"))` — bounded loops over small
  ranges.
- `t ∈ re.all → true`, `t ∈ re.none → false` for fully symbolic `t`.

## Enumeration mechanism

Two cap-bounded, mutually recursive enumerators over the existing private
`Rex` AST in `crates/shinri-str/src/regex.rs` (words returned in a
`BTreeSet<String>` for dedup + determinism):

**`enum_lang(r, cap) -> Option<BTreeSet<String>>`** — the words of `L(r)`
when finite and within cap; `None` otherwise (→ caller falls through):

| `Rex` node | rule |
|---|---|
| `Empty` | `∅` |
| `Eps` | `{""}` |
| `Range(lo, hi)` | the `hi − lo + 1` single-char words, if that count ≤ cap |
| `Concat(ps)` | cap-checked cross product of the parts' sets |
| `Loop(r, lo, hi)` | cap-checked `⋃_{n=lo..hi} enum_lang(r)ⁿ`; huge lazy bounds abort only if the set would actually keep growing (fixpoint: stop early when a power adds no new words) |
| `Union(ps)` | cap-checked union |
| `Inter(ps)` / extracted `ReDiff` shapes | some part enumerates finite → filter its words by `eval_membership` against every other part |
| `Star(_)`, `Comp(_)` | `None` — never finite except shapes the smart constructors already collapsed (`star(∅) = star(ε) = ε`) |

**`enum_comp(r, cap) -> Option<BTreeSet<String>>`** — the **exception set**
`Σ* \ L(r)` when co-finite and within cap:

| `Rex` node | rule |
|---|---|
| `Comp(inner)` | `enum_lang(inner, cap)` |
| `Star(Range(0, MAX_CODE))` (= `re.all`) | `Some(∅)` |
| `Inter(ps)` | all parts co-finite → cap-checked union of their exception sets (`Σ* \ ⋂ = ⋃ complements`) |
| `Union(ps)` | some part co-finite → its exception words filtered by **non**-membership (`eval_membership`) in every other part (`Σ* \ ⋃ = ⋂ complements`) |
| everything else (`Empty`, `Eps`, `Range`, `Concat`, `Loop`, other `Star`) | `None` — complements are infinite (or the shape is rare enough not to chase) |

`eval_membership` calls inside the `Inter`/`Union` filters run under the
existing `FUEL_NODE_CAP`; a `None` from fuel exhaustion aborts the whole
enumeration (→ fence), never guesses.

**Fuel.** Two new constants in `regex.rs`, both checked on every
intermediate word set of either enumerator; crossing either aborts the
enumeration → the atom survives → presence fence → sound `Unknown`:

- `ENUM_WORD_CAP: usize = 256` — maximum set cardinality.
- `ENUM_TOTAL_BYTES_CAP: usize = 4096` — maximum sum of word lengths.
  The cardinality cap alone does NOT bound work: `(_ re.loop n n)` over a
  one-word language has exactly one word of unbounded length, so `Loop`
  power-iteration must also be byte-capped (and must early-out when the
  inner language is `∅` or `{""}`, which the smart constructors cannot
  see — e.g. an `Inter` of disjoint literals — so a huge lazy bound never
  spins).

**Surrogate guard.** SMT-LIB's alphabet includes the surrogate block
`0xD800..=0xDFFF`, but Rust strings cannot represent those code points, so
a `Range` that intersects the block cannot be enumerated faithfully —
enumeration would silently MISS words and break the equivalence.
`enum_lang(Range)` returns `None` for any surrogate-intersecting range.
(Defense-in-depth: such a range necessarily spans ≥ 2050 characters —
range endpoints are Rust chars, hence non-surrogate — so the cardinality
cap already rejects it; the explicit guard makes the soundness argument
local instead of an accident of the cap constant.)

**Top-level driver** (extends `try_fold_in_re`): after the ground fold
declines, skip if the string side `t` contains any above-alphabet literal
character (slice-18/19 posture — don't guess semantics outside Σ, whether
`t` is a bare literal or a concat containing one); extract the constant
`Rex` (existing `extract_const_regex`; its above-alphabet fences apply
unchanged), then try `enum_lang`; on `None`, try `enum_comp`; on `None`,
leave the atom for the fence. On success, build `⋁ᵢ (t = wᵢ)` via
`ctx.mk_eq` / `mk_app(Or, …)` (co-finite: wrapped in `Not`), with 0-ary →
Bool const (`false` finite, `true` co-finite).

## Architecture

All production changes live in **`crates/shinri-str/src/regex.rs`**:

- `enum_lang` / `enum_comp` + `ENUM_WORD_CAP` (private, like the rest of
  the `Rex` machinery).
- `try_fold_in_re` grows the symbolic fallback above. The bottom-up
  memoized pass (`rewrite_ground_in_re`) is otherwise unchanged; its doc
  comment is updated to describe both stages (rename of the public symbol
  is NOT required — keeping `rewrite_ground_in_re`'s TermId-stability and
  seam contract intact matters more than the name; a doc alias "the regex
  rewrite pass" suffices).

**Unchanged**: the `lib.rs` seam (the pass already runs at the slice-19
position — after code_conv, before the substr fence and
`rewrite_str_predicates`, so downstream stages see the produced word
equations); `has_unreduced_regex` and the RegLan-declaration fence;
`string_stage.rs`; the wordeq engine, arith seam, budgets, existing fuel;
model construction and printing; the parser (nothing new to parse).

## Soundness

- Both rewrites are **full logical equivalences** over the SMT-LIB string
  domain (all strings over `0x0..=0x2FFFF`): membership in a finite
  language is exactly the disjunction of the word equalities; membership
  in a co-finite language is exactly the negated disjunction over the
  exception set. Any polarity, no repair, no demotion — the slice-18/19
  posture.
- **Alphabet.** Enumerated words are in-alphabet by construction:
  `extract_const_regex` already fences above-alphabet literals and range
  endpoints, enumeration only composes those characters, and the
  surrogate guard rejects the one shape (`Range` crossing
  `0xD800..=0xDFFF`) where in-alphabet words would be unrepresentable and
  silently dropped. The equivalences quantify over the SMT-LIB domain, so
  a symbolic `t` is covered regardless of which value the model builder
  later picks (it only mints in-alphabet strings today). A string side
  containing an above-alphabet **literal** skips the rewrite (→ fence) —
  same posture as the slice-19 ground path.
- **Fuel.** `ENUM_WORD_CAP` / `ENUM_TOTAL_BYTES_CAP` exhaustion — or
  `FUEL_NODE_CAP` exhaustion inside a filter's `eval_membership` — means
  no rewrite → presence fence → sound `Unknown`, never a wrong verdict.
- Co-finite `k = 0` (`re.all`-equivalent shapes) folds the atom to `true`;
  finite `k = 0` (`re.none`-equivalent) to `false` — evaluation, not
  heuristics.
- The produced equalities/disequalities land in the engine's decided
  fragment (concat word equations, diseqs); no new fence interactions:
  if `t` contains e.g. an unfoldable `str.substr`, the pre-existing
  substr fence downstream still fires on the rewritten assertion.

## Non-goals (banked for future slices)

- Derivative unfolding inside the wordeq engine — infinite/co-infinite
  languages against symbolic strings (`x ∈ [a-z]*`). Fences.
- The `to_code` inequality character-range gadget (banked since slice 18;
  natural companion to the engine slice above). Fences.
- Symbolic regex sides, RegLan equality/containment/emptiness. Fences.
- `str.<` / `str.<=` lexicographic ordering — still unparsed.
- Any change to the word-equation engine, arith seam, budgets, or fuel.

## Testing

- **Unit tests** (`regex.rs`): `enum_lang` per node type incl. the
  `Inter`/`Diff` filter path and the `Loop` fixpoint/early-outs
  (`L(inner) = ∅` and `= {""}` with huge lazy bounds must terminate);
  `enum_comp` for `Comp`, `re.all`, `Inter`-of-comps,
  `Union`-with-co-finite-part, and `None` for plain
  `Eps`/`Range`/`Concat`/`Star`; **both** cap aborts (cardinality and
  total-bytes — the one-long-word loop shape) plus the surrogate-range
  guard; dedup + determinism (`BTreeSet` order); the rewritten atom's
  shape (disjunction / negated disjunction / Bool consts at `k = 0`);
  the above-alphabet string-side skip (bare literal and concat-embedded);
  TermId stability of untouched subtrees.
- **E2e pins** (`shinri-solver` tests): sat/unsat/get-value through the
  full solver for symbolic-variable membership at both polarities, under
  `not`/`or`/`ite`; co-finite shapes (`re.comp`, `re.diff(re.all, ·)`);
  `Unknown` pins for neither-finite-nor-co-finite (`(re.* (re.range "a"
  "b"))`) and an over-cap enumeration (e.g. `(_ re.loop 1 300)` over a
  single-char language — 300 words). The slice-19 symbolic-string-side
  `Unknown` pin (`str.in_re s re.allchar`) does **not** flip: Σ has
  `0x30000` single-char words, far over the cap — it stays fenced, with
  its comment updated to name the new (over-cap) reason.
- **Differential oracle**: new family `qfs_regex_symbolic_matches_z3`
  (`--features oracle`, fresh seed, 200 iters): random finite/co-finite
  constant regexes over the ASCII `{a,b,c}` alphabet (slice-18/19 harness
  lesson: shinri's parser does not decode `\u{...}` escapes and z3 reads
  raw UTF-8, so scripts shared with z3 stay ASCII), one symbolic string
  variable additionally pinned or constrained by random
  equalities/disequalities/concat contexts, ~25% negation wrapping,
  unknown-tolerant, **0 disagreements required**. All existing string
  families re-run unperturbed with identical tallies.
- **Gates**: `cargo test -p shinri-core -p shinri-parser -p shinri-str
  -p shinri-solver --features oracle` (oracle families foreground with
  captured output), `cargo fmt --check`, `cargo clippy --workspace
  --all-targets` clean; the ~50-min full workspace run stays CI-side.
