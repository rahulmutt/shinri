# Slice 26 design — leaf-membership length-seam termination

Date: 2026-07-16
Status: APPROVED (design review 2026-07-16); implementation pending.

Predecessor: slice 25 (surrogate-straddling range round-trip, landed
2026-07-16). Slice 25's truth-up banks this as the dominant follow-up,
framed as "proper-prefix length-seam termination in `memb.rs`/the
string↔arith seam" — the driver of the six constant-on-left order Unknowns
pinned in `targeted_str_order_single_char_left_free_known_gap`. As with
slices 24→25, the pre-spec diagnosis pass **corrected the banked framing**:
the gap is not order-specific and not proper-prefix-specific. It is a
membership-level gap — any constant-regex membership over a fully-free leaf
variable whose language has minimal word length ≥ 2 and a star tail churns
the length seam to the fuel fence — and the fix lives in the membership
pass's dispatch (`memb.rs`) plus model repair (`model.rs`), not in the order
lowering.

This slice also cashes the slice-25 re-banked item "repair-side
length-flexible witness search" (banked "only if post-slice tallies show a
residual genuinely-nullability-shaped gap" — the probe matrix below is that
demonstrated need).

## Corrected diagnosis (empirical, CLI probes 2026-07-16, debug CLI @ 18c40df)

All probes `(set-logic QF_S)(declare-fun s () String) … (check-sat)`. Every
Unknown below is z3-sat unless marked. All returns are fast (fuel fence, not
divergence).

Order shapes (the slice-25 pins, reconfirmed):

| Probe                                   | Verdict     |
| --------------------------------------- | ----------- |
| `(str.< "b" s)`                          | unknown     |
| `(str.<= "b" s)`                         | unknown     |
| `(str.< "b" s)` + `len(s)=1` (z3: sat, "c") | unknown  |
| `(str.< "b" s)` + `len(s)=2`             | unknown     |
| `(str.< "b" s)` + `len(s)=3`             | unknown     |
| `(str.< s "b")` (constant on RIGHT)      | **sat**     |
| `(str.< "" s)` (empty left constant)     | **sat**     |
| `(str.< "bc" s)`, `(str.< "a" s)`        | unknown     |

Pure regex memberships — the order operator eliminated entirely:

| Membership                               | min-len | Verdict     |
| ---------------------------------------- | ------- | ----------- |
| `b·Σ·Σ*` (the strict-< gadget arm)       | 2       | unknown     |
| `b·Σ*`                                   | 1       | **sat**     |
| `b·Σ`, `b·Σ·Σ` (finite)                  | 2, 3    | **sat**     |
| `Σ·Σ*`                                   | 1       | **sat**     |
| `Σ·Σ·Σ*`                                 | 2       | unknown     |
| `b·(Σ·Σ*)` (nested concat)               | 2       | unknown     |
| `bc·Σ*`                                  | 2       | unknown     |
| `b·[a-z]·Σ*`, `b·Σ·x*`                   | 2       | unknown     |
| `Σ·Σ*·Σ` (star in middle)                | 2       | **sat**     |
| `Σ*·b·Σ` (star in front)                 | 2       | unknown     |

Rescue attempts and adjacent cells:

| Probe                                             | Verdict                    |
| ------------------------------------------------- | -------------------------- |
| `b·Σ·Σ*` + `len(s)=2` pinned                       | unknown (pin doesn't help) |
| `bc·Σ*` + `len(s)=2` pinned                        | unknown                    |
| `(bc·Σ* ∪ "q")` (trivially-sat arm!)               | unknown (poisoned union)   |
| `b·Σ·Σ*` + `len(s)=1` (z3: unsat)                  | **unsat** (must not regress) |
| `s ∈ b·Σ ∧ s ∈ c·Σ` (finite conflict; z3: unsat)   | unknown                    |
| `s ∈ a·Σ* ∧ s ∈ b·Σ*` (infinite conflict; z3: unsat) | unknown                  |
| `(str.< "b" s) ∧ (str.< s "d")` (z3: sat, "c")     | unknown                    |
| `b·(bb)*` (parity-constrained lengths)             | **sat**                    |

Reading: everything with a star tail that decides has minimal word length
≤ 1 — i.e. it rides slice 25 amendment 1's `memb_seeds` length-1 bump. The
`Σ·Σ*·Σ` sat cell shows unfolding-order sensitivity, not a principled
boundary. Pinned lengths do not rescue, and a single stalling union arm
poisons problems with trivially-sat arms — both facts pointing at a stall
*inside* `check()`, upstream of model repair.

## Root cause (mechanism map, verified against code)

`(str.< "b" s)` lowers in `order_const_left` (`order.rs:179-188`) to

    s ∈ Range(99, MAX_CODE)·Σ*  ∪  word("b")·Σ·Σ*

For a fully-free `s`, `memb_check` (`memb.rs:142`) unfolds this via Rule S
(head-forced `C·R''`, `memb.rs:310-404`): S1 peels `x = "" ∨ x = h·z` with
fresh skolems `h, z`; S2/`len_link_split` mint `len(h) = 1` and
`len(x) = len(h·z)` through `arith_eq_companions` (`length.rs:13-39`) — the
literal string↔arith seam crossing. The `Σ*` tail is itself head-forced, so
every round recurses S with fresh skolems and fresh `str.len` terms. The
per-len-term defining-axiom loop (`lib.rs:429-467`) processes each fresh
term and **spends shared fuel** (default 40, `fuel.rs:21` — deliberately
small: the N-O entailed-equality probing over the shared len-term set is
quadratic, `fuel.rs:9-22`). Because a free `s` gives the unfolding no ground
to bottom out on, the loop drains the fuel and returns a **hard**
`TCheck::Unknown` (`lib.rs:458-459`).

Model repair never gets a chance *structurally*: `memb_seeds`
(`model.rs:434-494`) → `search_word` (`regex.rs:514-572`) runs only from
`model_with` (`lib.rs:1230`), which runs only after `check()` returns
`TCheck::Sat`. The hard Unknown fires first. (The saturation-to-Sat path
inside `memb_check` itself, `memb.rs:168-170`, is downstream of the
len-axiom loop and never gets the round.) This also explains why length
pins don't rescue — the fuel dies before the pin could feed a witness
search — and why one bad union arm poisons the whole problem.

The architecture already contains the answer in miniature: the bare-`Range`
LEAF carve-out (`memb.rs:222-287`, slice 25 task 5b) deliberately does NOT
unfold a lone single-class membership — it emits a guarded `len(residual)=1`
axiom and leaves the atom for Rule G / `memb_seeds`, precisely because
unfolding would destroy the leaf's repair eligibility (the "wrong-witness
channel", `memb.rs:222-246`). This slice generalizes that carve-out from
`Rex::Range` to every constant regex over a repair-eligible leaf.

## Goal (hard guarantee)

After this slice, all of the following decide (z3-agreeing verdicts):

1. The order-pin shapes (the four pinned in
   `targeted_str_order_single_char_left_free_known_gap`, plus the `len=3`
   probe): `(str.< "b" s)`, `(str.<= "b" s)` free → **Sat**;
   `(str.< "b" s)` + `len(s) ∈ {1,2,3}` → **Sat** (z3-adjudicated during
   planning: at length 1 the gadget's above-arm `Range(99,MAX)·Σ*` admits
   `"c"` — the Unsat-at-len-1 case is the PURE prefix-arm membership in
   item 2, not the order shape).
   `targeted_str_order_single_char_left_free_known_gap`
   retires into `_now_decides` pins, per its own comment ("a future slice
   should flip these to Sat deliberately once the seam is closed").
2. The membership-level cells behind them: `b·Σ·Σ*`, `bc·Σ*`, `Σ·Σ·Σ*`,
   `Σ*·b·Σ`, `b·[a-z]·Σ*`, `b·Σ·x*`, `b·(Σ·Σ*)`, `(bc·Σ* ∪ "q")`, and their
   pinned-length variants → **Sat**; `b·Σ·Σ* ∧ len(s)=1` stays **Unsat**
   (now via a direct arith conflict instead of churn-then-conflict).
3. Two-gadget conjunctions on one leaf: `(str.< "b" s) ∧ (str.< s "d")` →
   **Sat** (`memb_seeds` already intersects all of a leaf's Rexes).

Soundness posture is unchanged and load-bearing: seeds are CANDIDATES only;
every candidate model is re-verified against all assertions by the
post-solve self-check before Sat is returned (the amendment-1 house
pattern). Nothing in this slice can flip a verdict on its own; failures fall
back to today's sound Unknown.

## Design

Three components, one per file.

### (a) `regex.rs`: length bounds + shortest-word search

- `min_len(&Rex) -> u32`: structural sound **lower** bound on accepted-word
  length. Exact on the shapes in play: `Eps`→0, `Range`→1, concat→sum,
  union→min of arms, inter→max of arms, star→0. Conservative 0 for `Comp`
  (sound; exactness there is YAGNI). Soundness invariant: for every
  `w ∈ L(R)`, `|w| ≥ min_len(R)`.
- `max_len(&Rex) -> Option<u32>`: the dual upper bound; `None` where
  unbounded (star) or unknown (comp). `Range` yields `[1,1]` — the existing
  bare-range `len=1` axiom is the degenerate case of the pair.
- `search_shortest(&Rex) -> Option<String>`: breadth-first search by
  increasing word length over `next_classes` derivatives, memoizing visited
  Rex states, bounded by the existing `MEMB_SEARCH_STEP_CAP`. Abort = no
  witness, never a verdict — same posture as `search_word`.

### (b) `memb.rs`: the generalized leaf carve-out

A new dispatch arm directly after the bare-`Range` arm. The bare-`Range` arm
stays byte-for-byte untouched (it just landed in slice 25 with careful
dedup/guard semantics; unifying it into the general arm is banked). The new
arm fires when ALL of:

- `cur` is any constant regex other than a bare `Range` (those took the
  sibling arm), reached with a variable-head residual;
- the residual is a **lone repair-eligible leaf** variable: `nf[i..]` is a
  single atom, that atom is a nullary `Uninterpreted` app, and its class
  holds no string constant and no concat — the same predicate `memb_seeds`
  applies at `model.rs:445-467` (evaluated per-round; if the class grounds
  later, Rule G handles the atom then);
- `side_clean` holds (same gate, same arguments, same
  fall-through-to-`continue` semantics as the sibling arms at
  `memb.rs:266`/`301`).

Action: emit the guarded tautology `lit → len(residual) ≥ min_len(cur)`
(and `lit → len(residual) ≤ max_len(cur)` when finite) through the arith
routing, deduped via `emitted_len_axioms`, one clause per round — mirroring
the sibling arm's emission pattern — then `continue`. The atom stays in
`memb_true`: Rule G decides it whenever the class grounds; `memb_seeds`
realises it otherwise; the self-check backstops. **Rule S/E never fire for
these atoms** — no fresh skolems, no seam churn, fuel survives, `check()`
reaches `TCheck::Sat`. Non-leaf variables and multi-atom residuals keep
today's Rule S/E path unchanged.

Soundness of the axiom: `min_len`/`max_len` are true bounds on `L(cur)`, so
the guarded implication is a tautology — it can only add a fact arith
lacked, never flip a verdict (same argument as the slice-25 `len=1` axiom).
Routing note: the emitted atoms are inequalities, which route to Arith
natively (`length.rs:9-12` — only bare Int *equalities* need the companion
split); the implementer verifies the exact minting path and reuses
`arith_eq_companions` only where an equality form is minted.

### (c) `model.rs`: repair fallback (cashes the re-banked item)

In `memb_seeds`, replace amendment 1's

    if n == 0 && !nullable(&goal) { n = 1 }

with: try `search_word(&goal, n)`; on `None`, try `search_shortest(&goal)`.
This subsumes the bump (a nullable goal at n=0 still finds `""`; a
non-nullable goal falls back to the true shortest word) and rescues the case
where arith's model picked an arbitrary feasible length the goal cannot
realize (the min-len axiom is only a lower bound — e.g. parity-constrained
languages). A fallback seed that violates a genuinely-asserted length pin
simply fails the post-solve self-check → today's sound Unknown.

### Why every probe cell now decides (data flow)

The gadget membership is carved out at first visit; the only length facts
arith ever sees are 1-2 guarded bounded clauses; no skolems are minted; the
len-axiom loop stays small; `check()` reaches Sat; `model_with` runs
`memb_seeds`; the leaf's Rexes (all memberships on `s`, comp'd for negative
polarity) are intersected into one goal; `search_word` at the model length
or `search_shortest` produces the witness; the self-check verifies it.
Unions are handled uniformly (the goal is just a Rex); conjunctions of
gadgets are handled by the existing intersection.

### Error handling

- `side_clean` failure → skip this round, revisit when clean (never a
  verdict) — inherited semantics.
- Search caps hit / empty intersection → un-seeded → `""`-fill → self-check
  fails → Unknown (today's verdict; sound).
- Unexpected Rex shape in `min_len` → conservative 0 → vacuous-but-sound
  axiom.
- Fuel: the carve-out arm spends via the sibling arms' `emit_split` path
  (saturation peek first), at most 2 deduped clauses per atom — bounded.

## Non-goals (banked)

- **Two-free-variable order** (`str.< s u`) — unchanged
  (`targeted_str_order_symbolic_pair_known_gap`, slice 23 §4).
- **Multi-char constant-on-left order lowering** (`str.< "bc" s` shapes
  beyond what the membership fix delivers through the existing fence at
  `order.rs:114-119`) — unchanged. Note `(str.< "bc" s)` itself is fenced
  pre-lowering, so it stays Unknown; only already-lowered memberships gain.
- **Rex intersection-emptiness refutation** for conflicting leaf
  memberships (`s ∈ a·Σ* ∧ s ∈ b·Σ*` → Unsat). Unknown today, Unknown
  after; repair can never produce Unsat by construction. Pin as known gap.
- **Unifying the bare-`Range` arm** into the general carve-out ([1,1] is
  the degenerate case) — only if a future slice needs to touch that arm
  anyway.
- **Exact `min_len` for `Comp`/`Inter`** — conservative bounds suffice for
  every consumer shape today.

## Testing

**Unit tests (`shinri-str`).**

- `regex.rs`: `min_len`/`max_len` over the probe shapes (order gadget union
  → 1/None; `b·Σ·Σ*` → 2/None; `b·Σ·Σ` → 3/3; bare `Range` → 1/1; a comp'd
  shape → 0/None); `search_shortest` finds `"q"` in `(bc·Σ* ∪ "q")`, finds a
  length-2 word for `b·Σ·Σ*`, respects `MEMB_SEARCH_STEP_CAP`, and returns
  `None` for an empty intersection.
- `memb.rs`: the carve-out arm emits exactly the guarded ge/(le) clauses and
  nothing else (mirroring `rule_s_head_split_clause_sequence` /
  `bare_range_leaf_emits_guarded_len1_axiom`); no S1 skolems are minted for
  a lone-leaf star membership; a multi-atom residual still takes Rule S; a
  non-leaf (pinned-class) variable still takes Rule S; `!side_clean` falls
  through with repair eligibility untouched.
- `model.rs`: seed fallback — pinned-n success; n-fails-then-shortest
  succeeds; both-fail leaves the var un-seeded.

**e2e pins (`qfs_differential.rs`).**

- Retire `targeted_str_order_single_char_left_free_known_gap` into
  `_now_decides` pins: free `<` and `<=` → Sat; `len∈{1,2,3}` strict → Sat.
- New membership pins: `bc·Σ*`, `Σ·Σ·Σ*`, `Σ*·b·Σ`, `(bc·Σ* ∪ "q")`,
  pinned-length rescue (`b·Σ·Σ*` + `len=2` → Sat), `b·Σ·Σ*` + `len=1` →
  Unsat, `(str.< "b" s) ∧ (str.< s "d")` → Sat.
- New known-gap pin: conflicting infinite leaf memberships
  (`s ∈ a·Σ* ∧ s ∈ b·Σ*`) → Unknown (z3: unsat; banked emptiness item).
- Unchanged: `targeted_str_order_symbolic_pair_known_gap`,
  `targeted_regex_bare_range_multi_atom_residual_stays_unknown`, the
  slice-25 straddle and `len_pinned_decides` pins.

**Differential oracle** (house cadence: **`--features oracle`**, run
**foreground with captured output**).

- `qfs_str_order_single_char_matches_z3` and `qfs_str_order_matches_z3`
  (66 unknowns at slice 25 close): expectation **0 disagreements**, unknowns
  substantially down; exact post-slice tallies recorded in the truth-up.
- All other string/regex families and the full differential file (62/62):
  movements expected **only** unknown→decided; anything else is a finding to
  adjudicate, not wave through.
- `cargo fmt --check` locally before push (CI gates on it).

## Risks

1. **Blast radius**: any lone-leaf constant-regex membership that currently
   decides *via unfolding* now rides repair instead. Probing found only
   deciding-direction movement (`b·Σ·Σ` decides either way; finite
   conflicts were already Unknown), but the oracle sweep is the real
   adjudicator.
2. **Arbitrary model lengths**: arith may choose a feasible-but-unrealizable
   length (lower bound only); the `search_shortest` fallback covers it, and
   the self-check rejects any seed violating a real pin.
3. **Routing**: the ge/le atoms must actually reach Arith; the implementer
   verifies the minting path against `length.rs:9-12` before relying on the
   Unsat upgrade.
