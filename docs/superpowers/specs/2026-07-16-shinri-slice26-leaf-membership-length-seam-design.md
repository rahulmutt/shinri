# Slice 26 design — leaf-membership length-seam termination

Date: 2026-07-16
Status: IMPLEMENTED (2026-07-17). See "Implementation notes (truth-up)" at the end.

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

## Implementation notes (truth-up)

Commits (`git log --oneline main..HEAD`, oldest first): `4535522e`
(Task 1: `min_len`/`max_len` sound length bounds on `Rex`), `04154e10`
(Task 2: `search_shortest` — capped BFS for a shortest accepted word),
`94a5f375` (Task 3: `memb_seeds` shortest-word fallback replaces the
length-1 bump), `ed3f48dd` (Task 4: general const-`Rex` leaf carve-out — no
S/E unfolding on repair-eligible leaves), `1f6647f7` ("recovery" — see
deviation (e)), `50d28270` (Task 5 fix: de-recurse `search_word` — explicit-
stack DFS for deep exact-length witnesses), `157d6b2f` (Task 5: cap oracle
z3 time/memory; pow300 pin asserts shinri-only), `015340b6` (docs: fix stale
`known_gap` cross-ref in the order-pin comment), `359c5153` (Task 6 fix:
`inter()` collapses bounds-certified empty intersections), `aadc95ad`
(Task 6 fix: carve-out requires repair-eligibility — equality-pinned leaves
fall back to unfolding), `624360a7` (Task 6: flip `script_e2e` `in_re`
known-gap pins to decided), `ffba9ec8` (Task 6: this spec truth-up), and
`71ccd965` (Task 6c: `max_len` overflow yields `None` — the final
whole-branch review's soundness fix, deviation (l)).

### Post-slice oracle tallies vs. the `7ba55ed` pre-slice baseline (all 13 families)

| Family | Baseline (sat/unsat/unknown[/bailout]) | Post-slice (sat/unsat/unknown[/bailout]) | Movement |
|---|---|---|---|
| `qfs_str_order` | 54/80/66 | 61/80/59 | 7× unknown→sat |
| `qfs_str_order_single_char` | 81/18/101 | 175/18/7 | 94× unknown→sat |
| `qfs_to_code_range` | 77/110/13 | 83/110/7 | 6× unknown→sat |
| `qfs_regex_ground` | 74/113/13 | 77/113/10 | 3× unknown→sat |
| `qfs_regex_unfold` | 94/88/18 | 102/88/10 | 8× unknown→sat |
| `qfs_regex_symbolic` | 112/76/12/0 | 113/76/11/0 | 1× unknown→sat |
| `qfs_matches` | 90/137/73 | 90/137/73 | identical |
| `qfs_predicates` | 33/69/96/2 | 33/69/96/2 | identical |
| `qfs_indexof_replace` | 44/85/71 | 44/85/71 | identical |
| `qfs_replace_all` | 51/74/75 | 51/74/75 | identical |
| `qfs_to_from_int` | 69/116/14/1 | 69/116/14/1 | identical |
| `qfs_const_int_conv` | 59/57/84 | 59/57/84 | identical |
| `qfs_code_conv` | 92/97/11 | 92/97/11 | identical |

Verified by a per-iteration diff (not just aggregate tallies — see
deviation (k)) at fixed LCG seeds across all 13 families, 2700 iterations
total (`300 + 200×12`): query text confirmed byte-identical between baseline
and post-slice at every iteration (zero seed mismatches); every observed
movement is `unknown→decided` (sat or unsat); **zero** `decided→unknown`
regressions; **zero** `sat↔unsat` inversions; zero new bailouts anywhere.
Full method and per-family movement counts recorded in the task-6 rediff
notes.

### Deviations from the plan (controller-adjudicated; human-approved where noted)

a. **Task 4**: the `fuel_exhaustion_saturates_to_model_path` unit test's
   carrier was truthed up from a lone-leaf shape to a two-atom carrier
   (`x·y`) — the general carve-out now intercepts the original lone-leaf
   shape before fuel exhaustion is reachable, so the test's carrier had to
   change to keep exercising fuel exhaustion at all. A new pin,
   `lone_leaf_star_zero_bounds_carves_out_silently`, was added to cover the
   carved-out lone-leaf case directly (`x ∈ [a-c]*` stays silent — zero
   splits, `terminal == Sat` — deferring to `memb_seeds`).
b. **Task 5**: `targeted_regex_symbolic_fences_unknown` renamed to
   `..._now_decide`; the `loop300` and `pow300` pins flipped from Unknown to
   Sat (`loop300` z3-confirmed; `pow300` semantically forced — its language
   is the singleton `{a^9000}`, nonempty, so shinri's self-check-verified
   sat is correct independent of what z3 reports).
c. Two container OOM kills occurred during Task 5, root-caused: z3 4.16
   diverges (unbounded memory growth, ~250 MB/s) on the `pow300` query. The
   test harness's `z3_run` now caps `-T:120 -memory:4096` so divergence
   degrades to a parsed Unknown instead of exhausting the cgroup; the
   `pow300` pin (`157d6b2f`) asserts shinri's verdict only (no z3
   cross-check), per the semantic-forcing argument in (b).
d. `search_word` was de-recursed to an explicit-stack DFS (`50d28270`): the
   original recursion was one stack frame per matched character, and
   slice-26's length bounds legitimately request witnesses thousands of
   characters long (e.g. the `pow300` leaf's `a^9000`), overflowing a 2 MiB
   test-thread stack in a debug build. Semantics (visit order, step
   accounting, dead-set memoization) preserved exactly; a regression pin
   (`search_word_deep_witness_no_stack_overflow`, n=9000 over `Σ*`) was
   added — `Σ*` was chosen over `a*` for the pin because it costs 1 visited
   state per character versus `a*`'s 2, staying under
   `MEMB_SEARCH_STEP_CAP=10_000` at that length. Note: the `pow300` e2e
   witness itself is actually found by the iterative `search_shortest`
   fallback, not `search_word`.
e. Commit `1f6647f7` ("recovery") is a user salvage of the first
   OOM-killed session's in-flight Task 5 work; its subject does not follow
   house style, and it carries one benign unrelated hunk — the `mise.toml`
   Rust toolchain bump `1.97.0` → `1.97.1`.
f. **Task 3**: the union e2e case (`(bc·Σ* ∪ "q")`) already passed
   pre-fix — the old length-1 witness bump found `"q"` on its own. Kept as
   a pin (now exercising the shortest-word fallback path instead of the
   bump it superseded).
g. The `len=1` order-shape cell (`(str.< "b" s)` + `len(s)=1` → Sat) was
   z3-adjudicated during planning; the spec correction landed on `main`
   pre-slice (see the spec body's "z3-adjudicated during planning" note),
   not as an in-slice deviation.
h. **HUMAN-APPROVED in-slice additions**: Task 6's per-iteration oracle
   diff (not the aggregate tallies, which masked both) found two genuine
   `decided→unknown` regressions: `qfs_regex_unfold` iteration 145 and
   `qfs_regex_symbolic` iteration 194. Fixed by:
   - `359c5153` — `inter()` now collapses to the empty language when its
     computed `min_len > max_len`, a sound emptiness certificate the
     `Concat` bounds combination was previously discarding; the decisive
     path is the pre-existing Rule-E "no ε, no live class" conflict, which
     the general leaf carve-out explicitly excludes `Rex::Empty`/`Eps`
     from, so it never shadows this once collapsed.
   - `aadc95ad` — the carve-out's lone-leaf syntactic check missed
     equality-engine pinning that `memb_seeds`'s own `pinned` check would
     have rejected; the gate now shares `model.rs`'s `is_repair_pinned`
     check, so equality-pinned leaves fall back to Rule S/E unfolding
     instead of taking the (silently unproductive) carve-out.
i. **BANKED KNOWN ISSUE (follow-up slice)**: a pre-existing, latent
   `shinri-arith` bug was exposed (not caused) by this slice's trajectory
   change and is banked for a follow-up slice. `Arith::check`'s
   `strip_apriori` (`crates/shinri-arith/src/lib.rs:1067-1074`) filters
   only literals registered in `self.apriori_lits` (the a-priori Int box +
   FBBT bounds) — it does not also resolve/strip `iface_lit`-registered
   pseudo-literals minted by `assert_interface_equality`
   (`lib.rs:750-800`, sentinel minted via `fresh_sentinel`, `lib.rs:505-518`,
   from the reserved `SENTINEL_VAR_BASE = 1 << 30` region, `lib.rs:36`). When
   a later top-level `Arith::check` (`lib.rs:1162-1176`) independently finds
   a Farkas conflict (`check_full`, `lib.rs:415`) that transitively cites a
   still-live interface-equality bound, the leaked sentinel literal reaches
   `shinri-sat`'s `theory_conflict_analyzable` guard
   (`crates/shinri-sat/src/solver.rs:294-301`), which correctly rejects it
   (its raw var index vastly exceeds `assign.num_vars()`) and bails out
   (`solver.rs:658-660`) to a sound Unknown. This slice's carve-out changed
   the search trajectory on the `qfs_regex_symbolic` it194 repro enough to
   reach more rounds of EUF↔arith interface exchange than the pre-slice
   S/E-driven trajectory ever did, tripping this dormant leak; it was
   reproduced during root-causing and then re-hidden (not fixed) by the
   `aadc95ad` fix in (h), which addresses the carve-out eligibility gap
   that drove the extra rounds, not the underlying `shinri-arith` leak
   itself. The leak remains generally reachable by any other query that
   drives the same interface exchange far enough.
j. `script_e2e`: three pre-slice known-gap pins now decide Sat
   (z3-confirmed each, capped): `in_re_unfold_plus_with_length`,
   `in_re_unfold_plus_with_length2`, `in_re_unfold_unknown_fuel_depth` —
   renamed to `..._now_decides` forms and flipped, in `624360a7`.
k. **Methodology note**: aggregate family tallies masked both regressions
   in (h) via offsetting flips (a `decided→unknown` regression cancelled
   against an unrelated `unknown→decided` movement, leaving the 5-tuple
   counts bit-identical). Per-iteration dump-and-diff — enabled here by
   fixed LCG seeds giving query-text identity across runs — is the
   recommended house convention for future slices touching fuzz-exercised
   paths; aggregate-only comparison is not sufficient to rule out
   regressions.

l. **Final whole-branch review finding (Important), fixed in-slice**
   (`71ccd965`): `max_len`'s saturating arithmetic (`saturating_add` in the
   Concat arm, `saturating_mul` in the Loop arm) capped results DOWN past
   `u32::MAX`, violating the "every accepted word has `len ≤ max_len`"
   contract that the carve-out's guarded upper-bound axiom relies on —
   a confirmed wrong Unsat on `(_ re.loop 0 3000000000)("ab") ∧
   len(s) = 6·10⁹` (semantically Sat: the singleton word `(ab)^{3·10⁹}`
   has exactly that length; pre-fix verdict was `unsat`). Fixed by
   overflow-⇒-`None` (`checked_add` via `try_fold`, `checked_mul`), so no
   upper-bound axiom is emitted in the overflow regime; the sound verdict
   there is Unknown (repair cannot realize a witness beyond `usize`
   search scale), pinned by `targeted_leaf_membership_maxlen_overflow_not_unsat`
   and the `max_len_overflow_yields_none` unit test. `min_len` keeps
   saturating arithmetic deliberately — under-reporting a lower bound is
   sound — with the asymmetry documented at both functions. The `inter()`
   emptiness collapse is unaffected (an overflow `None` simply never
   certifies emptiness). Outside the fuzz families' reach (generators never
   emit billion-scale loop bounds), hence found only by review.

### Retained known gap

Conflicting INFINITE leaf memberships (`s ∈ a·Σ* ∧ s ∈ b·Σ*`) remain a
sound Unknown, pinned as `targeted_leaf_membership_infinite_conflict_known_gap`.
Rex intersection-emptiness refutation remains a banked non-goal (repair can
never produce Unsat by construction); the new bounds-certificate collapse
in (h) only catches length-disjoint (finite bounds) cases, not infinite
conflicting tails.
