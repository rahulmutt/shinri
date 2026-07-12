# Slice 17 design — constant-RHS decision stage for symbolic str.to_int / str.from_int

Date: 2026-07-12
Status: IMPLEMENTED (slice 17 landed 2026-07-12).

Oracle (`qfs_const_int_conv_matches_z3`, fresh seed `0x51_61_0000_0001`, 200
iters): 59 sat / 57 unsat / 84 shinri-unknown (tolerated) / 0 z3-unknown / 0
guard-bailout / 55 witnesses / **0 disagreements**. All five pre-existing
string families re-ran unperturbed with 0 disagreements; four are
tally-identical to their committed values, and `qfs_to_from_int_matches_z3`
improved as intended — previously-fenced constant-RHS instances are now
decided: shinri-unknown 69 → 14, sat 44 → 69, unsat 87 → 116, witnesses
16 → 36 (all z3-verified), still 0 disagreements.

**Deviations from the spec.**
1. *Witness rewrites restricted to nullary uninterpreted constants* — the R2
   repair overrides the variable's model value at output, which is only sound
   when `s` is itself a variable; `str.to_int` over compound arguments (e.g.
   a concat) fences to sound Unknown instead of taking the witness rewrite.
2. *`INT_CONV_PIN_LEN_CAP = 1024` pin guard* — length pins with
   `L > 1024` are ignored (the pinned atom fences) rather than expanded,
   guarding against memory-bomb padded witness strings.
None beyond the two above. (Tooling note, not a spec deviation: the Gates
command below needs `--features oracle` for `qfs_differential.rs` to actually
run — the whole file is `#![cfg(feature = "oracle")]`.)

Predecessor: slice 16 (eager bounded digit bridge) — CLOSED, INFEASIBLE AS
DESIGNED. Three investigations proved the eager per-length gadget cannot be
decided by the engine at any useful digit cap (compound wall: LIA a-priori
bound-box blowup, O(K²) cumulative String↔Arith interface probing, B&B
divergence); see
`docs/superpowers/research/2026-07-11-eager-digit-bridge-infeasibility.md`.
This slice takes the opposite tack: **no search at all**. It decides the
constant-RHS fragment of symbolic `str.to_int` / `str.from_int` by exact
static rewriting, and keeps slice 15's presence fence for everything else.
User-selected envelope: constant-RHS, both verdicts (genuine Sat AND genuine
Unsat — no bound, no Unsat→Unknown demotion). User-selected approach:
rewrite stage (over a DPLL(T) propagator, which remains future work for the
fully-symbolic envelope).

## Goal

Decide, with zero search and no new engine risk:

- `str.from_int(n) = "lit"` for any string literal — both verdicts, any
  polarity (full equivalence rewrites).
- `str.to_int(s) = k` for numeral `k` — `false` for `k ≤ -2`; exact
  finite expansion under a top-level length pin; lone-occurrence witness
  rewrite otherwise (any polarity, with model repair).

Everything outside the fragment (fully-symbolic linking like
`to_int(s) = n0`, inequality atoms, nested-arithmetic shapes,
non-lone occurrences without a length pin) continues to fence to sound
`Unknown` via `has_unreduced_int_conv` — never a wrong verdict.

## Non-goals

- Inequality atoms (`to_int(s) >= k` etc.) — future work.
- Symbolic Int linking (`to_int(s) = n0`) — future lazy-propagator slice
  (design input: the research note's §Design requirements).
- Any change to the word-equation engine, arith seam, budgets, or fuel.

## Architecture

`crates/shinri-str/src/int_conv.rs` gains a stage 2 between the slice-15
stages:

1. `partial_eval_int_conv` — fold + roundtrip rewrite (slice 15, unchanged).
2. **`decide_const_int_conv(ctx, assertions) -> (Vec<TermId>, Vec<IntConvRepair>)`
   (this slice)** — rewrites decidable constant-RHS equality atoms in place;
   returns the rewritten assertion list plus model-repair obligations.
3. `has_unreduced_int_conv` — presence fence (slice 15, unchanged): any
   surviving application ⇒ solver returns `Unknown`.

Solver wiring (`crates/shinri-solver/src/lib.rs`, string path): call stage 2
after stage 1, store the repair obligations, keep the fence exactly as
shipped. There is NO outcome-match change and NO demotion flag — every
rewrite preserves both verdicts. The only new cross-component state is the
repair list consumed at model output (see R2).

Atom shapes recognized (syntactic, either argument order):
`(= (str.to_int s) k)`, `(= (str.from_int n) "lit")` where `k` is an Int
numeral, `"lit"` a String literal, `s`/`n` arbitrary non-literal terms of
the right sort. Unchanged subterms keep their TermId (house structural-
sharing rule); rewrites replace the ATOM node, applicable at any depth in
the assertion's boolean structure except where a rule below restricts it.

## Rewrite semantics

### from_int — full equivalences, any polarity

| `"lit"` | rewrite of `(= (str.from_int n) "lit")` |
|---|---|
| canonical decimal (non-empty, all ASCII digits, no leading zero unless exactly `"0"`) | `(= n <val(lit)>)` |
| `""` | `(< n 0)` |
| anything else (leading zeros, non-digits, signs, non-ASCII digits) | `false` |

These are equivalences of the atom itself (semantics of `str.from_int`:
`n ≥ 0` ↦ canonical decimal, `n < 0` ↦ `""`), hence valid at any polarity
and under any boolean structure. `val(lit)` and all numeral handling are
arbitrary precision (shinri-num `Integer`/`Rational`; no i64/i128
round-trip — standing slice-15 rule).

### to_int — range fact, pin expansion, witness rewrite

For `(= (str.to_int s) k)`:

1. **`k ≤ -2` → `false`.** Range of `str.to_int` is `{-1} ∪ ℕ`.
   Polarity-free.
2. **`k ≥ 0` with a top-level length pin `(= (str.len s) L)`** (numeral
   `L`, either argument order, asserted as its own top-level assertion):
   - if `|dec(k)| ≤ L`: atom → `(= s "<0-padded dec(k) to width L>")`
     (e.g. `k=5, L=3` → `s = "005"`; `k=0, L=3` → `s = "000"`).
   - if `|dec(k)| > L`: atom → `false`.
   Conditionally valid given the pin; the pin is never removed, so the
   rewrite is sound at any polarity (R4). `k = -1` under a pin: NOT
   rewritten (fences) — "length-L non-digit-run" has no finite exact form.
3. **`k ≥ -1`, no pin, `s` lone** (occurs nowhere in the assertion set
   outside this atom, R3): witness rewrite, any polarity, with a model-
   repair obligation (R2):
   - `k ≥ 0`: atom → `(= s "<dec(k)>")`; obligation
     `(s, dec(k), "")`.
   - `k = -1`: atom → `(= s "")`; obligation `(s, "", "0")`.
4. Anything else: leave for the fence.

Verdict soundness of (3): with `s` lone, both the original atom and its
replacement are two-way realizable (each can be made true or false by some
value of `s`), so the boolean skeleton's satisfiability — and hence the
formula's — is preserved exactly, in both directions, at every polarity.

## Soundness rules

- **R1 (digit classification):** exactly ASCII `'0'..='9'`
  (`char::is_ascii_digit`), never `char::is_numeric()` — Unicode digits
  (`٣`, `３`) are non-digits here (standing repo rule since slice 15).
- **R2 (model repair for witness rewrites):** a witness rewrite is
  verdict-exact but can corrupt the REPORTED MODEL at negative polarity:
  the solver may falsify `s = dec(k)` with a value that still satisfies
  the original atom (`"05"` for `k = 5`; any non-digit string for
  `k = -1`), and the differential harness's z3 witness check would
  correctly reject such a model. Therefore every witness rewrite records
  `IntConvRepair { var, witness, fallback }`; at model output, if the
  model's value for `var` ≠ `witness`, it is REPLACED by `fallback` —
  the canonical value falsifying the ORIGINAL atom (`""` has
  `to_int = -1 ≠ k` for `k ≥ 0`; `"0"` has `to_int = 0 ≠ -1`). The
  replacement is safe because `var` is lone: it perturbs no other
  constraint, keeps the rewritten atom false, and restores the original
  atom's required truth value. Repair applies on the solver's model-output
  path (get-value), the single surface the differential harness checks.
  Equivalence rewrites (from_int, `k ≤ -2`, pin expansion) carry NO
  obligation.
- **R3 (lone occurrence is global):** the occurrence check for `s` walks
  the ENTIRE assertion set (DAG-aware, memoized), not just the enclosing
  assertion. `s` must appear exactly once: as the `str.to_int` argument in
  the candidate atom. The same atom TermId appearing in several assertions
  still counts as lone (all occurrences rewrite consistently to the same
  replacement).
- **R4 (length-pin discipline):** a pin is a TOP-LEVEL assertion
  `(= (str.len s) L)`, `L` a numeral. The pin stays asserted after the
  rewrite (conditional validity). Multiple/contradictory pins are
  harmless: each rewrite is valid given its own pin, and contradictory
  pins make the formula Unsat regardless.

## What this decides (vs. slice 16's targets)

All five slice-16 Sat pins, by construction, with zero search:
`to_int(s)=5` → `s="5"` (witness); `from_int(n)="5"` → `n=5`;
`to_int(s)=5 ∧ len(s)=3` → `s="005"` (pin expansion);
`to_int(s)=-1` → `s=""` (witness); `from_int(n)="42"` → `n=42`.
Two former demotion canaries become GENUINE Unsat matching z3:
`to_int(x)=-5` → `false`; `from_int(n)="05"` → `false`.
The third (`to_int(s)=-1 ∧ s="7"`) fences → sound Unknown (`s` not lone).

## Testing & verification

- **Unit tests** (`int_conv.rs`): one per rewrite rule and edge — canonical/
  empty/garbage from_int literals; `k=-2` false; pin expansion at
  `|dec(k)| = L`, `< L`, `> L`, `k = 0`; witness rewrites both `k ≥ 0`
  and `k = -1`; the R2 trap (negated lone atom still rewrites and emits an
  obligation); R3 (non-lone `s` does NOT rewrite); structural sharing
  (unchanged subterms keep TermId).
- **E2e pins** (`qfs_differential.rs`): the five Sat pins above; the two
  genuine-Unsat pins; fence canaries (`to_int(s)=-1 ∧ s="7"` → Unknown,
  `to_int(s) = n0` symbolic → Unknown); a negated lone-occurrence
  Sat pin whose get-value model must survive the z3 witness check
  (exercises repair end-to-end).
- **Differential oracle family** `qfs_const_int_conv_matches_z3`: fresh
  seed `0x51_61_0000_0001` (slice-15 family keeps `0x51_5A_0000_0001`;
  the never-landed slice-16 seed is not reused). Generator biased to
  constant-RHS shapes (to_int=k across k<-1/-1/0/multi-digit; from_int=
  canonical/leading-zero/garbage/empty literals; optional length pins
  straddling |dec(k)|; ~25% negation wrapping; occasional extra occurrence
  of `s` to exercise the fence), unknown-tolerant, witness-checking
  (get-value models validated by z3 — this is the R2 gate), 200 iters,
  0 disagreements required. Existing families and seeds untouched.
- **Gates:** `cargo test -p shinri-str -p shinri-solver`, `cargo fmt
  --check`, `cargo clippy --workspace --all-targets` clean; CI runs the
  full workspace (~50 min shinri-fp exhaustive stays CI-side).

## Future work

- Inequality atoms over `to_int` (interval facts + witness rewrites).
- Fully-symbolic linking (`to_int(s) = n0`): lazy DPLL(T) propagator
  slice; design constraints recorded in the research note (no eager
  length cases, Horner-small coefficients, bounded shared-set growth).
- `k = -1` under a length pin (needs a "non-digit at some position"
  gadget or the propagator).
