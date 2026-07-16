# Slice 25 design — surrogate-straddling range round-trip canonicalization

Date: 2026-07-16
Status: IMPLEMENTED (2026-07-16). See "Implementation notes (truth-up)" at the end.

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

## Implementation notes (truth-up)

Commits (`git log --oneline f7be5c9..HEAD`, oldest first): `0a8823d`
(Task 1: union range coalescing), `0617a14` (Task 2: ReDiff character-class
interval algebra), `ee00411` + `67c5c6f` (Task 3: round-trip property test,
consumer-shape pins, Lcg comment fix), `9dd353f` (Task 4b, user-approved
amendment 1: `memb_seeds` length-1 witness search), `c3ac72a` + `6b62b79`
(Task 4 revised: e2e verdict pins and stale-pin truth-ups), `d9789ac` +
`6734699` + `43d719b` (Task 5b, user-approved amendment 2: regression fix —
`comp()` identities + guarded bare-range length axiom — and its pins),
`71fb714` (Task 5b fix round: gate the length axiom on `side_clean`).

### What the shape fix delivered, and what it did not

The `regex.rs`-only shape fix (Tasks 1–3: range coalescing in `union`, the
`ReDiff` character-class interval algebra in `extract_const_regex`) makes the
term↔`Rex` round-trip shape-stable for surrogate-straddling ranges, exactly
as designed. E2E it delivers straddle-under-concat via Rule S: a
user-written straddling membership, bare or under concat, decides **sat**
(`targeted_straddling_range_membership_decides`), and `head_forced` /
the bare-`Range` ground-out now fire on the folded shape the same way they
already did on non-straddling ranges.

It did **not**, on its own, deliver the spec's stated §Goal hard guarantee:
`(str.< "b" s)` / `(str.<= "b" s)` with `s` fully free do **not** decide sat
from the shape fix alone. Pre-spec CLI probing (recorded in the spec body
above) conflated three distinct mechanisms behind one "unknown" symptom: (1)
the straddling-range round-trip shape bug (this slice's actual, in-scope
fix), (2) a width/enumeration cap on bare wide ranges unrelated to
straddling (`ENUM_WORD_CAP`, model-repair witness search with an unpinned
length — fixed by amendment 1, see below), and (3) a length-seam/fuel stall
specific to the strict-order proper-prefix gadget, independent of
surrogates or width. Task 4's implementer investigation (BLOCKED, correctly)
separated these; only (1) was in the original plan's scope. Mechanism (3) is
NOT fixed by anything landed in this slice: all six left-free order shapes
(`str.<` / `str.<=` × free/len-1/len-2, constant-on-left) remain **sound
Unknowns**, pinned honestly as a named known gap
(`targeted_str_order_single_char_left_free_known_gap`,
`targeted_str_order_symbolic_pair_known_gap`). This is banked as the
dominant follow-up (candidate: slice 26, proper-prefix length-seam
termination in `memb.rs`/the string↔arith seam) — it is bigger than a
`regex.rs`-only fix and was correctly kept out of this slice.

### AMENDMENT 1 (user-approved): `memb_seeds` length-1 witness search

Task 4's investigation found mechanism (2) above: bare wide/straddling
memberships stall not on shape but because model-repair's `memb_seeds`
receives an unpinned length (`n == 0`) for a non-nullable goal, and
`search_word(range, 0)` correctly returns `None`, downgrading a genuinely-sat
case to Unknown via `""`-fill. The user approved a minimal, safety-backstopped
fix (Task 4b, `9dd353f`): `if n == 0 && !nullable(goal) { n = 1 }` before the
witness search, relying on the post-solve self-check (seeds are candidates
only; every candidate is re-verified against all assertions before Sat is
returned) to make the change decisiveness-only. This made bare wide/straddling
memberships decide, including the free `re.allchar` membership and both
`to_code` wide/boundary arms, and truthed up four stale pins in the deciding
direction (`targeted_regex_fences_unknown`'s first assertion; the `to_code`
`wide_arm` and surrogate-boundary pins; and the slice-20 `allchar`
known-gap pin, renamed to `_now_decides_sat`).

### REGRESSION FOUND AND FIXED (Task 5 → 5b)

The first Task 5 run (see `task-5-report.md`, "BLOCKED" section, preserved
below) correctly stopped: the amended adjudication bar's tally comparison —
not any pass/fail assertion — caught a genuine decisiveness regression that
`qfs_differential.rs`'s own asserts tolerate (`Unknown` is always an
accepted outcome; only the tally shift exposes a regression). The ReDiff
fold (`0617a14`, Task 2) regressed exactly 4 previously-decided verdicts, 0
disagreements produced at any point:

- **3× Sat→Unknown** in `qfs_str_order_matches_z3` (e.g. bare
  `(str.<= s1 "c")`, free `s1`, minimal repro `sat`→`unknown`). Mechanism:
  negative-polarity `memb_check` mints `Comp(Star(Range(0,MAX)))` (≡ ∅) and
  `Comp(Empty)` (≡ Σ*), which `comp()` never collapsed (only `Comp∘Comp`
  was recognized); the newly-folded, simpler `Σ`-shaped range concentrates
  case-splits on exactly these unrecognized tokens, exhausting the shared
  40-emission `Fuel` budget before nullability or model-build/witness
  self-check ever run.
- **1× Unsat→Unknown** in `qfs_to_code_range_matches_z3` (trivial repro:
  `str.to_code` of a length-0 string is `-1`, and `-1 >= 120` is unsat by
  elementary arithmetic). Mechanism: `code_conv::range_membership` mints a
  bare `Range` with no accompanying length fact; the folded bare-`Range`
  shape hits the leaf-skip in `memb.rs`, which is repair-only (can never
  produce Unsat), losing the length-0-vs-single-char conflict that the
  pre-fold bulkier shape had exposed directly.

Bisection (both repros, commit-by-commit `shinri-cli` builds) isolated both
to `0617a14` exactly, unaffected by Task 4b. The user approved a second
scope amendment (Task 5b): **Part 1** (`d9789ac`, `regex.rs`) —
`comp(Empty) → Star(Range(0,MAX))` and `comp(Σ*) → Empty`, pure semantic
identities closing the unrecognized-token gap. **Part 2** (`6734699`,
`memb.rs`) — a guarded tautological length=1 axiom on bare-range membership
leaves (same posture as the existing S2 axiom), restoring the lost
length-conflict information without minting a concat (repair-eligibility
preserved), deduplicated via `emitted_len_axioms`. Opus review of Task 5b
found one Important issue — Part 2's emission bypassed the module's
`side_clean` branch-independence gate mandated for NF-reading global
lemmas (latent unsoundness risk, no wrong verdict reachable with inputs
probed at review time) — fixed in `71fb714` by mirroring the existing
`memb.rs` gate argument-for-argument; re-review confirmed the gate addition
left all tallies bit-unchanged. Both parts combined: two previously-banked
known-gap pins (`split_bounds`, and the `str.<=` length-pinned sub-cases)
now genuinely decide, z3-confirmed sat.

**Fuel-competition note:** Part 2 alone costs 5 `single_char` decisions
relative to Part-1-only (comp identities alone would decide more of that
family, at the cost of leaving the Unsat→Unknown regression unfixed); the
combined fix is the user-approved target — Part 2's correctness gain
(restoring a genuine Unsat) was judged to outweigh 5 fewer decisions in a
family whose bar tolerates Unknown by design.

### Observed tallies (this run, RE-RUN post-5b)

All three families run twice (bit-for-bit identical both times) plus once
inside the full-file run — six observations total, all identical per family:

| Family | Pre-slice baseline | Post-slice (observed) |
|---|---|---|
| `qfs_str_order_single_char_matches_z3` | 54 / 18 / 128 / 0 / 0 | **81 / 18 / 101 / 0 / 0** |
| `qfs_str_order_matches_z3` | 54 / 80 / 66 | **54 / 80 / 66** (exact match, no regression) |
| `qfs_to_code_range_matches_z3` | 28 / 105 / 67, 26 witnesses | **77 / 110 / 13, 75 witnesses** |

Full differential file: **69 passed / 0 failed** (pre-slice 62; +2 Task 4
tests, +1 truth-up split, +2 Task 5b regression pins, +2 others — reconciled
against the commit log's test additions). `cargo test -p shinri-str`: 179
passed, 0 failed. `cargo test -p shinri-solver`: all binaries green, 0
failed (1 pre-existing `#[ignore]`, unrelated to this slice).

All values above exactly match the Task 5b reviewed, bit-reproduced
expected tallies (fixed seeds); 0 disagreements in every run.

### Adjudicated liberties

- Lcg provenance doc comment (`67c5c6f`): Task 3's plan text asserted the
  property test's `Lcg` uses "the same recurrence as the differential
  harness's," which is false (harness: `add 1, >>16`; this: Knuth MMIX,
  `>>33`). Fixed to the true provenance text; a deviation from the plan's
  literal words, not from its intent.
- Task 2's two out-of-brief doc-comment truth-ups (the `rex_to_term` doc and
  the `roundtrips_language` test comment, whose "extracts as Inter/Comp"
  claims became false once Task 2 landed) were accepted, then fully
  superseded by Task 3's exact plan-mandated replacement text.
- Banked minors (ledger, one line each): **m1** — no direct test of
  `union(vec![])` (pre-existing coverage gap, path unchanged). **m2** — no
  comment on `class_intervals` pointing at the no-interior-surrogate
  invariant it relies on. **m3** — no direct pins for the nested class-diff
  inductive case, the `blo=0` row, or the tail-overlap row (reviewer
  hand-derived all three correct). **m4** —
  `targeted_to_code_range_split_bounds_known_gap`'s docstring is partly
  stale post-flip (the pin itself is correct). **m5** —
  `emitted_len_axioms` dedup key drops a second guard on shared residuals
  (decisiveness-only). **m6** — a comment's `memb.rs:280` sibling reference
  is pre-fix line numbering (now `:301`), cosmetic. **m7** — the multi-atom
  residual case is now inert under `side_clean` + the seam; a reviewer's
  tally-changing single-atom-only restriction variant is banked as a
  follow-up. None of these affect soundness or the tallies above.

### RE-RUN history

Task 5's first attempt (pre-5b) correctly BLOCKED on exactly the regression
described above — full detail, both minimal repros, and the bisection
tables are preserved in `.superpowers/sdd/task-5-report.md`. This truth-up
reflects the RE-RUN performed after Task 5b's fix landed and was reviewed.
