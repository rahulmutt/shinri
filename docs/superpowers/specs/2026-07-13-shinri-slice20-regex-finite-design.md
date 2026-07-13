# Slice 20 design — symbolic `str.in_re` over finite / co-finite constant languages

Date: 2026-07-13
Status: DESIGNED — implementation pending.

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

**Fuel.** One new constant in `regex.rs`:
`ENUM_WORD_CAP: usize = 256` — the maximum set size at any intermediate
point of either enumerator. Crossing it aborts the enumeration; the atom
survives; the existing presence fence returns sound `Unknown`. No separate
byte cap: every word is composed from literals and ≤ 256-char ranges
already present in the query, composed at most cap-many times, so payload
is bounded as a consequence.

**Top-level driver** (extends `try_fold_in_re`): after the ground fold
declines, extract the constant `Rex` (existing `extract_const_regex`; its
above-alphabet fences apply unchanged), then try `enum_lang`; on `None`,
try `enum_comp`; on `None`, leave the atom for the fence. On success,
build `⋁ᵢ (t = wᵢ)` via `ctx.mk_eq` / `mk_app(Or, …)` (co-finite: wrapped
in `Not`), with 0-ary → Bool const.

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
  endpoints, and enumeration only composes those characters. The
  equivalences quantify over the SMT-LIB domain, so a symbolic `t` is
  covered regardless of which value the model builder later picks (it
  only mints in-alphabet strings today).
- **Fuel.** `ENUM_WORD_CAP` exhaustion — or `FUEL_NODE_CAP` exhaustion
  inside a filter's `eval_membership` — means no rewrite → presence fence
  → sound `Unknown`, never a wrong verdict.
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
  `Inter`/`Diff` filter path and the `Loop` fixpoint/early-stop; the
  degenerate collapses (`star(∅)`, `loop lo>hi`, empty ranges);
  `enum_comp` for `Comp`, `re.all`, `Inter`-of-comps,
  `Union`-with-co-finite-part, and `None` for plain
  `Eps`/`Range`/`Concat`/`Star`; cap-abort at both enumerators and via
  filter fuel; dedup + determinism (`BTreeSet` order); the rewritten
  atom's shape (disjunction / negated disjunction / Bool consts at
  `k = 0`); TermId stability of untouched subtrees.
- **E2e pins** (`shinri-solver` tests): sat/unsat/get-value through the
  full solver for symbolic-variable membership at both polarities, under
  `not`/`or`/`ite`; co-finite shapes (`re.comp`, `re.diff(re.all, ·)`);
  `Unknown` pins for neither-finite-nor-co-finite (`(re.* (re.range "a"
  "b"))`) and an over-cap enumeration (e.g. `(_ re.loop 1 3)` over a
  large union). Slice-19 `Unknown` flip-markers whose languages are
  finite/co-finite **flip to real verdicts** — update those pins.
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
