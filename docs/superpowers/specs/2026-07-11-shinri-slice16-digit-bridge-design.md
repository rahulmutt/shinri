# Slice 16 design — bounded digit bridge for symbolic str.to_int / str.from_int

Date: 2026-07-11
Status: CLOSED — INFEASIBLE AS DESIGNED (2026-07-11). The encoding (Tasks 1–2)
was implemented, review-clean, and is archived at tag
`archive/slice16-eager-bridge` (commits 25ee5dd, 81927db); the solver wiring
was never merged. Three independent investigations proved the eager gadget
cannot be decided by the engine at K=8 (or any useful K): the wall is
compound — LIA a-priori bound-box blowup from the 10^7 digit-sum
coefficients, O(K²) cumulative String↔Arith interface probing, and B&B
divergence over the K length cases; the word-equation engine is never on the
critical path. The encoding itself is sound (all Unsat-demotion canaries held
throughout). Full evidence:
`docs/superpowers/research/2026-07-11-eager-digit-bridge-infeasibility.md`.
Successor: a lazy theory-level bridge — the alternative this spec's
design-selection note below rejected; the evidence now mandates it (lazy
int-conv propagator slice). Slice 15's presence fence remains the shipped
behavior.

Predecessor: slice 15 (str.to_int / str.from_int fold + roundtrip + fence,
landed 2026-07-11, PR #9). This slice replaces slice 15's presence fence with a
bounded encoding — the two canaries `targeted_symbolic_to_from_int_fences_unknown`
pinned as flip-markers flip to `Sat` here. User-selected over a two-sided
hybrid (bounded-exact + one-sided over-bound relaxation + model-region check)
and over a lazy theory-level CEGAR bridge: both directions in one slice, eager
under-approximate encoding, unsat demotion.

## Goal

Decide the sat-side of symbolic `str.to_int(u)` and `str.from_int(n)` — today
fenced to sound `Unknown` — by an **eager bounded under-approximation**:

- Every application surviving slice 15's fold/roundtrip pre-pass is replaced
  by a fresh value variable plus defining assertions that encode the op's
  semantics **exactly for arguments inside a digit bound K**, into shapes the
  existing engine already decides (word equations over fresh single-char
  variables + pure LIA digit sums).
- The bound itself (`str.len(u) <= K`; `n < 10^K`) is **asserted**, making the
  encoding an under-approximation of the unbounded semantics.

**Verdict contract (the heart of the slice):**

- `Sat` → `Sat`. Genuine: the encoding is exact inside the bound, and the
  fresh variables extend any model (they are definitionally determined or
  harmlessly free).
- `Unsat` → **demoted to `Unknown`** whenever the bridge fired. In-bound unsat
  does not imply unbounded unsat (an over-bound argument might satisfy the
  original query). Queries where no application survived to the bridge keep
  `Unsat` untouched.
- Wordeq fuel exhaustion → `Unknown`, as today.

Consequences pinned explicitly: `to_int(s) = 5` and `from_int(n) = "5"` become
`Sat` (the slice-15 canary flips); `to_int(x) = -5` (real verdict: unsat, since
to_int's range is `{-1} ∪ ℕ`) stays `Unknown` — deciding unsat-side queries is
the **one-sided range abstraction**, re-deferred (see §5).

Why under-approximation and not an exact bounded case-split: `to_int` admits
leading zeros (`to_int("0000005") = 5`), so `|u| > K` does NOT imply a large
value — the over-bound branch cannot be finitely encoded, only relaxed
(deferred) or assumed away (this slice).

## Pinned semantics the encoding must preserve

Slice 15's `eval_to_int` / `eval_from_int` remain the ground truth (ASCII-only
digits `'0'..='9'`; `to_int` = -1 on empty/any-non-digit; `from_int` = "" for
negative, canonical no-leading-zero decimal otherwise). The bridge encodes the
same function symbolically; the differential oracle cross-checks both against
z3.

## Design

### The digit-link gadget (shared by both directions)

Per char position: fresh single-char String var `c_i`, fresh Int `d_i`, fresh
selector Boolean `dig_i`, linked by a 10-way one-hot:

```
dig_i ↔ (c_i = "0" ∨ c_i = "1" ∨ … ∨ c_i = "9")
(c_i = "0" → d_i = 0) ∧ … ∧ (c_i = "9" → d_i = 9)
```

Under `¬dig_i`, `d_i` is unconstrained — harmless because every use of `d_i`
below is gated behind all-digits selectors. Pure LIA + word equations +
single-char (dis)equalities; the wordeq engine's diseq handling
(`diseq_sides`, diseq trail) covers the negative-polarity occurrences the
biconditionals produce under Tseitin.

### `str.to_int(u)` → fresh Int `v`

One shared char set `c_1..c_K` per occurrence (length cases reuse the prefix;
memoized on the application's TermId so repeated occurrences share one gadget
set). Defining assertions:

- `str.len(u) <= K`  ← the under-approximation
- `str.len(u) = 0 → v = -1`
- for `k = 1..K`:
  `str.len(u) = k → u = c_1 ++ … ++ c_k ∧ ⋀_{i≤k} str.len(c_i) = 1`
  `∧ (alldig_k → v = Σ_{i≤k} d_i·10^(k-i)) ∧ (¬alldig_k → v = -1)`
  where `alldig_k ↔ ⋀_{i≤k} dig_i`.

Leading zeros are correct **by construction** — the digit sum is
value-correct for `"007"` (d_1 = d_2 = 0 contribute nothing).

### `str.from_int(n)` → fresh String `s`

- `n < 10^K`  ← the under-approximation (the negative branch is exact and
  unbounded: `n < 0 < 10^K`, so the single upper-bound assertion is compatible
  with both branches)
- `n < 0 → s = ""`
- for `k = 1..K`:
  `(n ≥ 10^(k-1) ∧ n < 10^k) → s = c_1 ++ … ++ c_k ∧ ⋀ str.len(c_i) = 1`
  `∧ n = Σ_{i≤k} d_i·10^(k-i) ∧ digit links` (the `k = 1` case's lower bound
  is `n ≥ 0`). Here "digit links" is the bare one-hot
  `(c_i = "0" ∧ d_i = 0) ∨ … ∨ (c_i = "9" ∧ d_i = 9)` — `from_int` has no
  non-digit case, so the `dig_i` selector escape is `to_int`-only.

Canonicality (no leading zero) is **implied**, not asserted: `n ≥ 10^(k-1)`
plus the digit sum forces `d_1 ≥ 1` for `k ≥ 2`. No Int div/mod anywhere —
`shinri-core` has no such ops; the digit-sum form is pure *linear* arithmetic
(constant coefficients `10^(k-i)`), strictly simpler than the div/mod sketch
in slice 15's §5.

### Naming & model hygiene

Fresh vars use the `!` internal prefix via `reduce::next_fresh()` — `!tic{n}`
(to-int chars/value), `!fic{n}` (from-int) — matching slice 12's
`!pfx`/`!sfx` convention so they stay out of printed models.

### Bound

`const INT_CONV_DIGIT_CAP: usize = 8` in `int_conv.rs`, module-level with a
rationale comment (slice-13 `INDEXOF_CHAIN_CAP` convention). Per occurrence:
K char gadgets (shared across length cases), K length-case implications,
~10·K one-hot disjuncts, LIA coefficients ≤ 10^7. Small enough to stay well
inside the wordeq fuel budget (40 emissions) while covering the digit ranges
QF_S benchmarks exercise. There is no "over-cap fence": the cap IS the
asserted bound; over-bound instances are what the unsat demotion pays for.

## Architecture / wiring

`bridge_int_conv(ctx, assertions) -> (Vec<TermId>, bool)` joins
`partial_eval_int_conv` / `has_unreduced_int_conv` in `shinri-str`'s
`int_conv.rs` as the third stage of the same seam. It walks assertions,
replaces each surviving application with its fresh value var, appends the
defining assertions, and returns `fired = true` iff it replaced anything.

In `check_sat`'s string path (`crates/shinri-solver/src/lib.rs`), the slice-15
fence pair

```rust
assertions = shinri_str::int_conv::partial_eval_int_conv(&mut self.ctx, &assertions);
if shinri_str::int_conv::has_unreduced_int_conv(&self.ctx, &assertions) {
    return SolveOutcome::Unknown;
}
```

becomes fold-then-bridge:

```rust
assertions = shinri_str::int_conv::partial_eval_int_conv(&mut self.ctx, &assertions);
let (assertions_bridged, int_conv_bridged) =
    shinri_str::int_conv::bridge_int_conv(&mut self.ctx, assertions);
assertions = assertions_bridged;
debug_assert!(!shinri_str::int_conv::has_unreduced_int_conv(&self.ctx, &assertions));
```

The fold stage is untouched — literals still fold, the roundtrip still
rewrites — so the bridge only sees genuinely symbolic survivors.
`has_unreduced_int_conv` survives as the post-bridge debug assertion (nothing
may survive the bridge).

**Demotion gate:** local to this `check_sat` call — the string path's final
outcome passes through `if int_conv_bridged && outcome == Unsat { Unknown }`.
`Sat` and `Unknown` pass through untouched. No other routing path (BV, ABV,
FP) can observe the flag: string-path routing is exclusive.

**Polarity safety:** definitions are appended as top-level positive
assertions over fresh variables, so the original formula's polarity structure
is untouched. Both ops are value-sorted functions, so
replacement-by-definition is exact at any position and polarity — the ONLY
approximation in the design is the asserted bound.

## Testing

- **Unit (`int_conv.rs`):** encoding-shape pins (bound assertion present, K
  length cases, one-hot links); memoization (two occurrences of the same
  application → one gadget set); `fired` flag false when nothing survives the
  fold; post-bridge debug fence holds.
- **E2E (`qfs_differential.rs` targeted section):** the two pins in
  `targeted_symbolic_to_from_int_fences_unknown` flip to `Sat` and move into a
  new `targeted_digit_bridge_decided`. New pins:
  - `to_int(s) = 5 ∧ str.len(s) = 3` → Sat (leading zeros: `"005"`);
  - `to_int(s) = -1` → Sat (non-digit escape);
  - `from_int(n) = "42"` → Sat;
  - `to_int(x) = -5` → Unknown (demotion pin; documents the one-sided
    deferral — z3: unsat);
  - `from_int(n) = "05"` → Unknown (in-bound unsat, demoted; z3: unsat —
    documents the canonicality gap the demotion covers).
- **Differential oracle:** new family `qfs_digit_bridge_matches_z3`, **fresh
  seed** (new op-shape family = new seed; never perturb existing seeds),
  unknown-tolerant, **0-disagreement gate @ 200 iters**, sat/unsat
  non-degeneracy asserts. Generator mixes: symbolic-string `to_int` and
  symbolic-Int `from_int` at both polarities, nested in `str.++` / `str.len`
  / `=` / arithmetic; digit, non-digit, and empty literals; length
  constraints straddling `INT_CONV_DIGIT_CAP`. Unsoundness in the encoding
  surfaces as shinri-Sat/z3-Unsat disagreements — exactly what the gate
  catches.
- Existing oracle families (`qfs_matches_z3`, `qfs_predicates_matches_z3`,
  `qfs_indexof_replace_matches_z3`, `qfs_replace_all_matches_z3`,
  `qfs_to_from_int_matches_z3`, the nary and fp-bridge str families)
  **untouched**.

## 5. Out of scope

- **One-sided range abstraction** (over-bound branch relaxed to `v ≥ -1`, with
  post-solve model-region check) — would keep `Unsat` verdicts trustworthy and
  decide `to_int(x) = -5` → unsat. Re-deferred: it is its own slice-15 §5 item
  and needs model-introspection plumbing this slice does not add.
- Raising or making configurable `INT_CONV_DIGIT_CAP` beyond 8.
- `str.to_code` / `str.from_code`, `str.is_digit`, lexicographic `str.<` /
  `str.<=`, and all regex.

## Risks

- **R1 — demotion gate misplaced.** Demoting a non-bridge unsat (over-fencing)
  or missing a return path (unsound unsat). Mitigation: the flag is a local
  variable consumed at the single string-path outcome point; flag-false unit
  pin; all existing families re-run unperturbed.
- **R2 — unguarded `d_i` leak.** If any digit-sum use of `d_i` escapes its
  `alldig_k` / range guard, a free `d_i` fabricates values (unsound Sat).
  Mitigation: every sum occurrence is syntactically gated in the encoding
  constructor; the non-digit e2e pin; the oracle's Sat/Unsat cross-check.
- **R3 — wordeq fuel exhaustion.** Multi-occurrence instances mint up to
  K fresh single-char vars each into the shared String↔Arith set. Sound
  (`Unknown`), oracle-tolerated; watch the family's unknown-rate log line for
  degeneracy (assert non-zero sat AND unsat counts).
- **R4 — coefficient overflow.** `10^(k-i)` up to `10^7` at K = 8: built as
  `Rational`/`Integer` numerals (arbitrary precision), never native ints —
  same discipline as slice 15's R4.

## Verification

- `cargo test -p shinri-str -p shinri-solver` (per-crate iteration; full
  workspace run is the ~50-min CI gate).
- `cargo fmt --check` before push (CI fails fast on it).
- Oracle tally recorded back into this spec at truth-up, slice-15 style.
