# Slice 28 design — Rex intersection-emptiness refutation

Date: 2026-07-17
Status: DESIGN (2026-07-17) — awaiting implementation plan.

Predecessor: slice 27 (arith conflict-core sanitization seam, landed
2026-07-17). Slice 27's truth-up ("Newly banked: nothing") names exactly
one remaining explicitly-banked completeness item carried forward from
slice 26: **Rex intersection-emptiness refutation for conflicting infinite
leaf memberships**, pinned as the known-gap test
`targeted_leaf_membership_infinite_conflict_known_gap`
(`crates/shinri-solver/tests/qfs_differential.rs:4044`). Slice 26's
retained-known-gap note frames it precisely: "conflicting INFINITE leaf
memberships (`s ∈ a·Σ* ∧ s ∈ b·Σ*`) remain a sound Unknown … Rex
intersection-emptiness refutation remains a banked non-goal (repair can
never produce Unsat by construction); the new bounds-certificate collapse
in [slice 26] only catches length-disjoint (finite bounds) cases, not
infinite conflicting tails." This slice cashes that item.

## 1. Problem

A string term can carry several `str.in_re` membership atoms. When their
languages are jointly empty — e.g. `s ∈ a·Σ*` and `s ∈ b·Σ*`, whose
intersection requires the first character to be simultaneously `a` and `b`
— the conjunction is unsatisfiable (z3: unsat) for **any** value of `s`.
shinri returns a sound `Unknown` instead.

Root cause: the two exits that could refute it do not, by construction.

- **The check path** (`memb::memb_check`,
  `crates/shinri-str/src/memb.rs:142`) processes membership atoms **one at
  a time**. Each atom's regex is folded against the term's ground normal
  form (Rule G) and, for a lone repair-eligible leaf, carved out and left
  for model repair (slice 26 leaf carve-out, memb.rs:289–332). No step ever
  looks at *two* memberships on the same term together, so a per-term
  intersection is never formed on the exit where a `TCheck::Conflict` is
  legal.

- **The model-repair path** (`model::memb_seeds`,
  `crates/shinri-str/src/model.rs:462`) *does* group memberships per
  variable (`per_var: FxHashMap<TermId, Vec<Rex>>`, model.rs:470) and
  intersect them (`regex::inter`, model.rs:496) to search for a witness
  word. But repair can only ever *seed a value* — it cannot emit a conflict
  ("repair can never produce Unsat by construction"). When the intersected
  goal is empty, `search_word`/`search_shortest` simply find no witness,
  the variable is left un-seeded, and the post-solve self-check backstops
  to the prior sound `Unknown`.

So the per-term intersection that would expose the emptiness is formed only
on the path that cannot report it. The fix hoists the intersection — and a
genuine emptiness decision over it — onto the check path.

## 2. Scope

**General**, not pattern-matched. The conflict fires for **any** string
term carrying ≥2 memberships whose intersected language is *provably*
empty, regardless of the term's structure (free leaf, concat, or
equality-pinned). This is not a widening for its own sake — it is the
*natural* scope, and it is strictly easier to justify than a leaf-only
gate (see §5 soundness). The infinite-tail pinned case is one instance.

Non-goals are banked in §8.

## 3. The emptiness certificate (`regex.rs`)

Add a three-valued decision procedure:

```rust
pub(crate) enum Emptiness { Empty, NonEmpty, Unknown }
pub(crate) fn language_empty(r: &Rex) -> Emptiness
```

A dedicated worklist BFS over the Brzozowski-derivative automaton, sharing
the existing primitives (`nullable`, `next_classes`, `deriv`, `node_count`,
the `MEMB_SEARCH_STEP_CAP` / `CLASS_SPLIT_CAP` / `FUEL_NODE_CAP` fuels) and
a global `seen: FxHashSet<Rex>` memo — the same shape as `search_shortest`
(regex.rs:703). Semantics:

- **`NonEmpty`** — some reachable state is `nullable(state)` (an accepting
  path exists). Short-circuits.
- **`Empty`** — the frontier exhausts with every reachable state explored,
  none nullable, **and no taint occurred** during the traversal.
- **`Unknown`** (taint — the traversal could not be completed) — any of:
  - `MEMB_SEARCH_STEP_CAP` reached (state budget exhausted),
  - `next_classes(state)` returns `None` (its `CLASS_SPLIT_CAP` overflow —
    regex.rs:447; the character-class partition could not be built, so the
    outgoing transitions are unknown), or
  - a `deriv` result exceeds `FUEL_NODE_CAP` (derivative blowup —
    the transition is dropped, so the state is under-explored).

The taint flag is the load-bearing distinction: a `None` from
`search_shortest` today conflates "no witness within caps" with "language
empty," which is why the naive reuse is unsound. `Empty` is returned **only**
from a fully-explored, untainted automaton.

### 3.1 Why a dedicated function, not a mode flag on `search_shortest`

`search_shortest` **skips pure-surrogate character classes** (regex.rs:729,
`continue` — it cannot build a Rust `char` witness from a lone surrogate
code point). For witness extraction that skip is sound (completeness only —
the model-seed side has no way to realise a surrogate anyway). For an
*emptiness proof* the same skip would be **unsound**: a surrogate is a valid
SMT-LIB string code point (Σ includes `0xD800..=0xDFFF`), so a state whose
only accepting path runs through a surrogate class denotes a **non-empty**
language, and skipping it could wrongly certify `Empty`.

`language_empty` therefore must **explore** surrogate classes. It does not
need to materialise a `char` — `deriv(c: u32, r)` (regex.rs:331) operates on
raw code points, so taking the derivative over a representative surrogate
code point is well-defined. This makes the emptiness traversal both simpler
(no char materialisation, no word accumulation, no DFS backtracking string)
and *more complete* than `search_shortest`. Folding both behaviours into one
core behind a `build_witness` flag would entangle the surrogate divergence
exactly where soundness lives — rejected.

*Alternatives considered:* (B) shared core with a `build_witness` flag —
rejected for the surrogate tangle above. (C) reuse `search_shortest`
returning `None` as the empty signal — rejected: `None` conflates
cap-abort with true emptiness (unsound).

## 4. Check-path aggregation + conflict (`memb.rs`)

Add a per-term aggregation pass to `memb_check`, running **after** the
existing per-atom loop (so Rule-G ground conflicts, dedup, and the leaf
carve-out still fire first; the pass only inspects residual live
memberships). Sketch:

1. Group `s.memb_true` entries `(atom, lit, pos)` by the string-side term's
   equality-class representative. Use `memb_sides` (memb.rs:20) for the
   sides and the same class key the normal-form path uses, so two
   memberships on equality-merged terms group together.
2. For each group with ≥2 members: extract each regex with
   `regex::extract_const_regex`, applying `regex::comp` for negative
   polarity (`!pos`) — the identical polarity folding `memb_seeds` uses
   (model.rs:481–486). If any member's regex fails to extract as a constant,
   **skip the whole group** (fence to current behaviour — never guess).
3. Intersect via the `regex::inter` smart constructor (model.rs:496 does the
   same). `inter` already collapses `Empty` and slice-26 bounds-certified
   empty intersections at construction; `language_empty` decides the rest.
4. If `language_empty(&goal) == Emptiness::Empty`, return
   `TCheck::Conflict(just)` with
   `just = group.iter().map(|(_, lit, _)| EqLeaf::Asserted(*lit)).collect()`
   — the same core shape Rule G uses (memb.rs:217–219).
5. Otherwise (`NonEmpty` or `Unknown`) do nothing for this group — fall
   through to the existing Sat/repair/self-check flow (today's behaviour).

The pass emits **at most a conflict**; it never emits a lemma or a Sat, so
it interacts with `memb_check`'s D-satfuel saturation only as an additional
soundness fence, not a fuel consumer. (It runs regardless of `s.fuel`; the
emptiness caps are its own bound, mirroring how the const-regex/NF/node-cap
`Unknown` fences are soundness fences, not fuel — memb.rs comment at
lib.rs's membership pass.)

## 5. Soundness

`L(R₁ ∩ … ∩ Rₖ) = ∅` means there is **no** string `w` with
`w ∈ R₁ ∧ … ∧ w ∈ Rₖ`. Hence for the term `t` carrying those memberships,
`t ∈ R₁ ∧ … ∧ t ∈ Rₖ` is unsatisfiable for every value of `t`. The
conjunction of the `k` asserted membership literals is therefore a valid
conflict, and citing exactly those `k` literals (each `EqLeaf::Asserted`)
is a sound core — with **no dependence on `t`'s structure**. This is why the
general scope (§2) needs no leaf/free/pinned gate: the argument is
term-agnostic.

The certificate returns `Empty` **only** on a fully-explored, untainted
automaton (§3), so a cap/fuel/partition abort can only cost decisiveness
(the group falls through to today's sound `Unknown`), never fabricate a
conflict. Negative-polarity members are folded to `comp(R)` before
intersection, exactly as the witness path already does, so mixed-polarity
groups are handled uniformly and soundly. Because the pass runs after the
per-atom loop and only *adds* a conflict exit, it is verdict-monotone: it
turns some prior `Unknown`s into `Unsat`, and moves nothing else.

## 6. Completeness boundary (what stays `Unknown`)

Intersections whose emptiness proof exceeds `MEMB_SEARCH_STEP_CAP`,
`CLASS_SPLIT_CAP`, or `FUEL_NODE_CAP` remain sound `Unknown` — consistent
with house style ("completeness only; a sound Unknown is acceptable").
Single-atom empties (`t ∈ re.none`, or any regex the smart constructors
already fold to `Rex::Empty`) are decided upstream by the existing Rule-E /
ground paths (see `targeted_leaf_membership_empty_intersection_unsat`,
qfs_differential.rs:4062) — this pass adds nothing there and must not
double-handle them (a group needs ≥2 members to be considered). Raising the
caps to decide currently-tainted empties is banked (§8).

## 7. Testing

**Targeted e2e pins (`qfs_differential.rs`).**

- **Flip:** retire `targeted_leaf_membership_infinite_conflict_known_gap`
  into a `_now_decides` pin — `s ∈ a·Σ* ∧ s ∈ b·Σ*` → `Unsat`, z3
  re-confirmed unsat (capped).
- **New positive pins:**
  - disjoint finite × infinite: `s ∈ "a"·Σ*  ∧  s ∈ (str.to_re "bc")` →
    Unsat (the finite side forces first char `b`).
  - 3-way intersection empty only jointly (each pair non-empty) → Unsat.
  - negative polarity via comp: `s ∈ a·Σ* ∧ s ∉ a·Σ*` → Unsat (folds to
    `R ∩ comp(R) = ∅`).
- **New negative pins (must stay decided/Unknown correctly — guard against
  an over-eager `Empty`):**
  - non-empty intersection (`s ∈ Σ·Σ* ∧ s ∈ "a"·Σ*`) → Sat.
  - a deliberately cap-exceeding intersection stays sound `Unknown`.

**Unit (`regex.rs`).** `language_empty` on: `Empty`→Empty, `Eps`→NonEmpty,
`Σ*`→NonEmpty, disjoint infinite tails (`a·Σ* ∩ b·Σ*`)→Empty, a
surrogate-only accepting path→NonEmpty (the anti-`search_shortest`-skip
pin), and a `CLASS_SPLIT_CAP`/`STEP_CAP` case→Unknown.

**Differential oracle** (house cadence: `--features oracle`, run
**foreground with captured output**). Expect **0 shinri-vs-z3
disagreements**; unknowns down. Per-iteration dump-and-diff (base vs fix):
every flip must be `Unknown → Unsat`; zero decided→Unknown, zero sat↔unsat.

**Gate list (slice-27 lesson).** Run locally pre-push: `shinri-str`,
`qfs_differential --features oracle`, **and `script_e2e`** — a
completeness-shifting string change can flip string-side e2e pins. Any
z3-confirmed `Unknown → Unsat` flip surfaced by `script_e2e` is an
adjudicated flip, not a blocker (slice-25/26 precedent).

## 8. Non-goals (banked)

- **Conflict-core minimization.** Citing all of a term's contributing
  memberships is sound but may be a larger clause than necessary. Emitting a
  minimal contributing subset (drop members whose removal keeps the
  intersection empty) is banked — improves clause reuse in the SAT layer,
  not soundness.
- **Cross-term emptiness.** Emptiness that arises only through word
  equations / concat structure tying *different* terms together (not a
  single shared term's memberships) is out of scope — banked.
- **Cap-raising.** Deciding empties that currently exceed the derivative
  fuels by raising `MEMB_SEARCH_STEP_CAP` / `CLASS_SPLIT_CAP` /
  `FUEL_NODE_CAP` is banked; whatever the dump-and-diff surfaces beyond the
  caps gets banked, not fixed here.
