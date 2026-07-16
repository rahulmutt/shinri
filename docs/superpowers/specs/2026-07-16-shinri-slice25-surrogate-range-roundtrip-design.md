# Slice 25 design — surrogate-straddling range round-trip canonicalization

Date: 2026-07-16
Status: DRAFT

Predecessor: slice 24 (single-character `str.<` / `str.<=` vs. a constant,
landed 2026-07-16). Slice 24's implementation notes bank a follow-up it calls
"engine-side witness synthesis for non-nullable constant-regex memberships
over free variables," diagnosed as the driver of the 128/200 shinri-unknowns
in `qfs_str_order_single_char_matches_z3`. This slice cashes that item — but
the pre-spec diagnosis pass **falsified the banked framing**, and the fix this
spec commits to is different from (and much smaller than) witness synthesis.

Like slices 20, 22, 23, and 24, this is a slice with **zero changes to the
word-equation engine, the membership pass, the arith seam, `Fuel`, or the SAT
budgets**. It touches exactly one layer: the `Rex` smart constructors and
`extract_const_regex` in `regex.rs`. Every rewrite it adds is exact interval
arithmetic on character classes — language-preserving by construction.

## Corrected diagnosis (empirical, CLI probes 2026-07-16)

Slice 24's caveat says the engine self-decides SAT for a fully-free variable
"only when the language contains ε." That is not the operative distinction:

| Probe (free `s` unless noted)                          | Verdict     |
| ------------------------------------------------------ | ----------- |
| `s ∈ [c-d]·Σ*` (non-nullable, no ε)                    | **sat**     |
| `s ∈ [c-d]` (bare range)                               | **sat**     |
| order-shape union, ASCII-bounded ranges                | **sat**     |
| `s ∈ Range(c, U+D000)·Σ*` (big range, below block)     | **sat**     |
| `s ∈ Range(c, U+E000)` (bare, **straddles** D800–DFFF) | **unknown** |
| `s ∈ Range(c, U+E000)·Σ*`, even with `len(s) = 1`      | **unknown** |
| `(str.< "b" s)`, even with `len(s) = 1` or `= 2`       | **unknown** |

Non-nullable languages over fully-free variables decide fine. What never
decides is any shape containing a **surrogate-straddling range** — and the
order rewrite's constant-on-left arm always mints one (`Range(m+1, 0x2FFFF)`
straddles the surrogate block for every ASCII `m`). Slice 24's pre-spec spike
de-risked the engine with ASCII-bounded ranges (`re.range "a" "c"`), which is
exactly how the straddle case was missed.

### Root cause

`re.range` *terms* cannot carry surrogate endpoints (SMT-LIB string literals
have no surrogate chars), so `rex_to_term` encodes a straddling
`Rex::Range(lo, hi)` as

    union( Range(lo, D7FF),
           diff( Range(D7FF, E000), union(Range(D7FF), Range(E000)) ),  ; block
           Range(E000, hi) )

(`regex.rs::range_term`). Its own doc comment states the consequence: the
minted term re-extracts "with the SAME LANGUAGE — not always the same shape
(the surrogate-block diff extracts as Inter/Comp)." The membership pass
re-extracts the Rex from the term on every visit (`memb.rs::memb_check`,
`extract_const_regex`), so after one round-trip the range has become
`Union[Range, Inter[Range, Comp[Union[…]]], Range]`. Every downstream shape
test then misses:

- `head_forced` (`regex.rs`) sees no `Range` head → Rule S never fires;
- the bare-`Range` ground-out (`memb.rs`, the Rule-G/model-repair leaf skip)
  sees no bare `Range` → the leaf is never repair-eligible in the intended
  way;
- the atom falls down the Rule-E expansion path and dies in fences/fuel.

It is a **shape-stability bug in the term↔Rex round-trip**, not a missing
synthesis feature. Witness synthesis at model repair (the banked framing)
could not meet the bar anyway: the concat shapes stall *before* repair even
with length pinned (probe table, row 6).

## Goal

Make the round-trip shape-stable:

    extract_const_regex(rex_to_term(r)) == r      for every canonical Rex r

so surrogate-straddling ranges behave exactly like their non-straddling twins
everywhere the engine consumes a Rex. Hard guarantee, pinned by e2e tests:

- `(str.< "b" s)` and `(str.<= "b" s)` with `s` fully free decide **sat**
  (both were `unknown` before this slice), with model values verified by the
  post-solve self-check;
- a user-written straddling membership (`s ∈ re.range "c" <U+E000>`, bare and
  under concat) decides **sat**.

Expected corollary: `qfs_str_order_single_char_matches_z3`'s shinri-unknown
tally (128/200) drops substantially, since its unknowns are dominated by
constant-on-left atoms whose minted ranges straddle the block.

## 1. The fix — two exact normalizations in `regex.rs`

**(a) Union range coalescing** (in the `union` smart constructor). Collect the
`Rex::Range` members, sort by `lo`, and merge overlapping or adjacent
intervals (`[a,b] ∪ [b+1,c] → [a,c]`). Output order is fixed: coalesced
ranges first, sorted by `lo`, then non-range members in first-appearance
order (deterministic output — hash-consing and the engine's `(x, cur_t,
RULE)` dedup keys rely on `rex_to_term` determinism per Rex, preserved).

**(b) Character-class interval algebra on the `ReDiff` extraction arm** (in
`extract_const_regex`). When every operand extracts to a *character class* —
`Rex::Empty`, a `Range`, or a union of `Range`s — compute the set difference
as intervals and return the resulting union of `Range`s directly, instead of
building `inter(first, comp(rest…))`. Operands outside that shape keep the
existing `Inter/Comp` construction unchanged.

Together these fold the minted block gadget back to `Rex::Range(D800, DFFF)`
— a legal Rex *value*; only *terms* are barred from surrogate endpoints — and
then coalesce `Range(lo,D7FF) ∪ Range(D800,DFFF) ∪ Range(E000,hi)` to the
original `Range(lo, hi)`. `head_forced`, the bare-`Range` ground-out, `deriv`,
`next_classes`, and `search_word` then see the same shapes the non-straddling
cases already exercise. No consumer changes.

### Endpoint-domain safety

Interval cut points produced by (a)/(b) are `endpoint ± 1` of operand
endpoints. Operand endpoints are user chars (never surrogates: Rust `char`),
or the block-gadget constants `D7FF`/`E000`. So derived endpoints are at worst
the block edges `D800` (= `D7FF + 1`) and `DFFF` (= `E000 − 1`) — exactly the
domain `range_term`'s debug-asserts already admit ("only `lo = 0xD800` /
`hi = 0xDFFF` can arise"). No interior-surrogate endpoint is reachable.
`Rex::Range`'s invariant comment is updated to state this, and
`rex_to_term(Range(D800, DFFF))` round-trips through the gadget by
construction of (b).

### What deliberately does NOT change

- `rex_to_term`'s encoding (the gadget stays; it is the only way to *express*
  the block as a term). Only the extraction direction learns to fold it.
- `memb.rs`, `order.rs`, `model.rs`, `wordeq.rs`, `Fuel`, SAT budgets,
  fences (`FUEL_NODE_CAP`, `CLASS_SPLIT_CAP`), and all seam contracts.
- No general regex simplifier: (b) fires only when *all* `ReDiff` operands
  are character classes; everything else keeps today's structure.

TermIds of minted regex terms shift where unions now coalesce; existing unit
tests absorb this because they build `want` via the same smart constructors
(the slice-22/23/24 pattern).

## 2. Slice-24 spec truth-up

The banked-diagnosis paragraph in
`2026-07-16-shinri-slice24-str-order-single-char-design.md` ("Completeness
caveat on §Goal") gets a one-line correction pointing here: the driver was the
straddling-range round-trip, not non-nullability, and the banked follow-up is
cashed by this slice. Committed alongside this spec (docs-only edit).

## 3. Non-goals (banked)

- **Multi-character constant order** (`str.< s "bc"`) — unchanged from slice
  24 §5; this slice removes the straddle blocker its constant-on-left arms
  would have inherited.
- **Full symbolic lexicographic decision** (two free string variables) —
  unchanged (slice 23 §4).
- **Repair-side length-flexible witness search** (`memb_seeds` searching at a
  minimal feasible length when the variable's length is unpinned). No
  demonstrated need once shapes survive the round-trip: every non-straddling
  free-variable probe decides today. Re-bank only if post-slice tallies show
  a residual genuinely-nullability-shaped gap.
- Any interval algebra beyond the `ReDiff` character-class arm (e.g. general
  `Inter`/`Comp` class folding). YAGNI until a consumer demonstrably needs it.

## 4. Testing

**Unit tests (`regex.rs`).**

- Coalescing: adjacent, overlapping, contained, disjoint-stay-split, mixed
  range/non-range members, determinism under member permutation.
- ReDiff algebra: the exact block gadget folds to `Range(D800, DFFF)`; simple
  ASCII diffs; a non-class operand (e.g. a `Star`) keeps the `Inter/Comp`
  shape bit-for-bit.
- **Round-trip property test**: for generated canonical `Rex` values
  (including straddling and block-edge ranges),
  `extract_const_regex(rex_to_term(r)) == r`. This is the spec-level
  acceptance property.
- Pinned: `head_forced` and the bare-`Range` shape hold after a
  straddling-range round-trip (the two consumer misses named in Root cause).

**e2e pins (`script_e2e.rs` / unit-level solver tests where the text frontend
cannot express the literal).**

- `(str.< "b" s)`, `(str.<= "b" s)`, free `s` → **sat** (the hard guarantee;
  both orientations of the constant).
- User-written bare and concat straddling memberships (the probe-19/22
  shapes, built via raw `U+E000` literals) → **sat**.
- `targeted_str_order_symbolic_pair_known_gap` still passes (two-symbolic
  comparisons stay fenced).

**Differential oracle** (house cadence: **`--features oracle`**, run
**foreground with captured output**).

- `qfs_str_order_single_char_matches_z3` re-run on its existing seed:
  expectation **0 disagreements** and shinri-unknowns **substantially below
  128/200**; the exact post-slice tally is recorded in the truth-up.
- `qfs_str_order_matches_z3` (66 unknowns) and `qfs_to_code_range` (67
  unknowns; `code_conv::range_membership` mints straddling ranges too):
  expected to move **only** in the unknown→decided direction, 0
  disagreements. Any other movement is a finding to adjudicate, not to wave
  through.
- All remaining string/regex families and the full differential file
  (62/62): expected unchanged; movements adjudicated.
