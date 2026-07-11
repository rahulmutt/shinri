# Eager digit-bridge infeasibility — research note

Date: 2026-07-11

Status: slice 16 closed: eager encoding infeasible; findings feed the
lazy-propagator slice.

Predecessor docs: plan `docs/superpowers/plans/2026-07-11-shinri-slice16-digit-bridge.md`,
spec `docs/superpowers/specs/2026-07-11-shinri-slice16-digit-bridge-design.md`.
Archived implementation: tag `archive/slice16-eager-bridge`, commits
`25ee5dd` (`to_int` gadget + `Bridger`) and `81927db` (`from_int` gadget) —
both review-clean on the now-archived branch `slice16-digit-bridge`. Solver
wiring (Task 3) existed only as `task3-wiring.patch`, applied ad hoc by each
investigation's worktree; never committed.

## Summary

Slice 16 set out to replace slice 15's sound `Unknown` fence on symbolic
`str.to_int`/`str.from_int` with an eager bounded under-approximation: mint
a fresh value variable plus K length-case gadgets (word equations over
fresh single-char vars + linear digit sums), assert the bound, demote
in-bound `Unsat` to `Unknown`. The encoding (Tasks 1-2) landed clean, but
wiring it (Task 3) diverged on a differential 5-pin target suite at the
shipped `K=8`, and three investigations chased a cheap fix. Inv-1
attributed the divergence to the word-equation engine and proposed a
`shinri-str` remedy. Inv-2 built that remedy's prerequisite (branch-local
fuel), proved the word-equation engine is *never reached* for these pins,
and relocated the wall to the arith/Nelson-Oppen `str.len` seam. Inv-3 went
further: it found the *dominant* K=8 cost is a third, previously unnamed
mechanism — the LIA a-priori termination box blowing up to ~7000-bit
rational arithmetic — and proved removing every arith cost centre it could
scope still leaves the pins `Unknown` (or diverging once forced). All three
converge by different evidence on the same conclusion: **the eager gadget
is infeasible at K=8, and no budget/encoding tweak reaches all five target
pins at any single K.** The encoding's soundness held throughout (0
spurious Sat, demotions correct in every configuration tested). The real
fix is a lazy, on-demand int-conv theory propagator — a new slice, not a
tweak to slice 16.

## The eager encoding

`bridge_int_conv` (`crates/shinri-str/src/int_conv.rs`, commits `25ee5dd`/
`81927db`) is a third stage after slice 15's fold/roundtrip pre-pass:
every surviving `str.to_int(u)` / `str.from_int(n)` application is
replaced by a fresh value variable plus defining assertions, memoized
per application `TermId` so repeated occurrences share one gadget set.

- `bridge_to_int`: per occurrence, K fresh single-char vars `c_1..c_K`, K
  fresh digit ints `d_1..d_K`, bound `0 <= str.len(u) <= K` (asserted),
  `str.len(u)=0 -> v=-1`, and per `k=1..K`: `str.len(u)=k -> (u =
  c_1++...++c_k ∧ (alldig_k -> v=Σd_i·10^(k-i)) ∧ (¬alldig_k -> v=-1))`.
  `dig_i` is the **char-only** selector `(or (= c_i "0") … (= c_i "9"))`
  — spec risk R2: a one-hot-with-values variant would be unsound (a
  mismatched `d_i` under `¬dig_i` could fabricate `v=-1` for a genuinely
  all-digit string), so `d_i` is only ever read behind `alldig_k`.
- `bridge_from_int`: symmetric, fresh string `s`, bound `n < 10^K`,
  `n<0 -> s=""`, K range-cases each pairing a bare one-hot char/digit link
  (no `dig_i` escape needed — `from_int` has no non-digit case).
- **Contract:** `Sat -> Sat` (exact inside the bound); `Unsat -> Unknown`
  whenever the bridge fired — the asserted bound makes in-bound `Unsat`
  compatible with an out-of-bound `Sat` of the true unbounded semantics,
  so it cannot be reported as real `Unsat`. This demotion held sound in
  every investigation (see "what remains sound" below).

## Investigation chronology

**Inv-1 (task-3 diagnosis).** Root-caused the K=8 divergence to the eager
gadget handing the string engine a length-*free* multi-variable concat word
equation — its known-divergent case — with the global, non-backtracked
`Fuel` budget exhausted by the SAT search over K candidate lengths.
Proposed remedy: length-directed word-equation alignment in `wordeq.rs`
(chop `lhs = c_1++...++c_k` at entailed lengths, no Nielsen split) plus
branch-local fuel, so a per-length concat becomes deterministic once a
length commits. Also landed a cheap, sound encoding tweak — ALT (move
`|c_i|=1` and value-links into each length-case body) and EXCL (an explicit
length disjunction) — that helps but doesn't reach K>=2 universally.

**Inv-2 (engine spike) refutes inv-1's remedy.** Built branch-local fuel
(Mechanism B) exactly as inv-1 sketched — sound, regression-clean (71/71
`shinri-str`, 29/30 differential, only target pins failing) — and found it
changes **no verdict**. Instrumenting the `resolve_equation` call site
showed **zero** `[wordeq]` invocations for any of the five pins, including
p3 (the length-pinned pin inv-1 believed would resolve via aligned concat).
Why: the length-case body is an *input-conditional* merge (`(=> (= |s| k)
(and (= s (str.++ ...)) ...))`, asserted at decision level > 0), and the E1
antecedent-precise gate `side_clean(cx.eq, cx.terms, l, &input_cond_roots)`
in `check` **skips** `resolve_equation` whenever a side sits in a class a
conditional input disjunct merged — routing the digit bridge's `s ≈ concat`
equality away from wordeq entirely. Mechanism A (length-directed alignment)
was therefore never implemented — its target subsystem is structurally
gated out for these pins. Inv-2 relocates the wall to the arith/Nelson-
Oppen `str.len` interface seam: the terminating `Unknown` is the cumulative
`STRING_PATH_PIVOT_BUDGET` (2000) tripping inside `entailed_equalities`'s
probes, swallowed as `None` (a sound completeness concession) and
resurfacing as `Unknown` from the top-level arith check.

**Inv-3 (seam spike) refines "the seam is the wall" into a compound wall.**
Confirms wordeq is never reached (matches inv-2) but shows pivot-budget
churn is **not** the dominant cost — raising the cumulative pivot cap
doesn't lower wall time proportionally, and a ceiling that *skips the seam
entirely* (`SHINRI_SKIP_EE`) still leaves all five pins `Unknown` at K=8.
The actual dominant cost, missed by both prior reports, is the LIA
solver's a-priori termination box: `M = (n+1)·((n+m)·a+1)^(n+m)`, seeded on
every Int problem variable. At K=8, `a = 10^7` (from `digit_sum`'s
positional coefficients) and `n+m ≈ 232`, so `M` is a **2175-decimal-digit**
integer — every subsequent pivot, FBBT pass, and N-O probe then runs on
~7000-bit rationals. Shrinking the box (sound only on the demote-Unsat
string path) roughly halves wall time by itself; box + seam-skip together
cut K=8 from ~8-10s to ~1.3-3.1s — but the pins **still never flip to Sat**,
and forcing the remaining search (raising the branch budget) makes the
B&B **diverge** (p4 >90s).

**Explicit conflict, unresolved between inv-1 and inv-2.** Inv-1's own
scaling table reports p1 (`to_int s=5`) at K=2 with ALT+EXCL and *default*
budgets as **Sat, 0.15s**. Inv-2's small-K table, built under Mechanism B
with the pivot budget *raised to 100k*, reports the same pin — p1 at K=2,
ALT+EXCL — as **still Unknown**. The reports don't reconcile this: inv-2
(§7) separately notes that without ALT/EXCL, p4 at K=2 with
`PIVOT=100000` is Unknown at 14.7s (not the Sat inv-2's own main table
reports for p4 under ALT+EXCL), flagging that its small-K numbers depend on
exactly which mechanisms are active and are "not directly comparable"
across reports. Treat both tables as configuration-dependent, not a
settled fact about "does p1 pass at K=2" — they used different fuel/
budget/mechanism combinations.

## Root causes — the compound wall

Four compounding, independently-sufficient-to-block-K=8 mechanisms, none of
which is fixed by patching another:

**1. The LIA a-priori box blowup (dominant, inv-3's new finding).**
`Arith::apriori_bound` (`crates/shinri-arith/src/lib.rs`, ~line 1040) computes
`M = (n+1)·((n+m)·a+1)^(n+m)` and `seed_apriori_if_needed` installs `±M` on
every Int problem variable, once, at level 0. Measured (pin p4, via
`SHINRI_DBG`):

| K | n_int | m_atoms | coeff_max a | n+m (exponent) | M decimal digits |
|---|-------|---------|-------------|----------------|-------------------|
| 1 | 4     | 32      | 9           | 36             | 92                |
| 2 | 6     | 58      | 10          | 64             | 181               |
| 3 | 8     | 84      | 100         | 92             | 366               |
| 8 | 18    | 214     | 10^7        | 232            | **2175**          |

`a = 10^(K-1)` comes straight from `digit_sum`'s positional coefficients
(`crates/shinri-str/src/int_conv.rs:188`, `10^(k-1-i)`); both `a`
(exponential in K) and `n+m` (linear, ≈26·K) grow with K. Section timers at
K=8 default budgets localise ~5s of wall time to `boundary prop` /
`p_arith` (the box seeding + FBBT over the giant-M tableau) for both p1 and
p4. `SHINRI_ABOX=1e9` (a sound override on the demote-Unsat string path)
drops `arith.propagate` from 5012ms to 2ms and roughly halves total time —
but the pins stay `Unknown`.

**2. The combiner's O(K²) same-β `str.len` interface probing (secondary,
inv-2's finding, refined by inv-3).** `Combiner::drive_final_check`
(`crates/shinri-theory/src/combiner.rs:483`) runs `entailed_equalities`
(arith → EUF) every Full check over `shared = euf.shared_arith_terms ∪
string.shared_arith_terms`; for the digit bridge `shared_arith_terms`
(`crates/shinri-str/src/lib.rs:1107`) returns ≈K+1 `str.len` terms (`str.len
u` plus every `str.len c_i`). `entailed_equalities` (`crates/shinri-arith/
src/lib.rs:570`) pre-filters to same-β pairs then runs 2 probes per
candidate pair, each a full `check_full` simplex re-solve — since every
`c_i` has length 1, all their `str.len` terms share β, giving O(K²)
candidate pairs (measured: 704-1480 candidate pairs per pin at K=8). The
pivot budget (`STRING_PATH_PIVOT_BUDGET=2000`, `lib.rs:91`) is cumulative
across the whole solve, never reset per-check, and a trip inside a probe is
swallowed as `TCheck::Unknown => None` (`lib.rs` ~720-730, ~786-795) —
sound (a completeness concession, never a false equality) but
non-terminating: the probe loop keeps churning already-`None` candidates
until the top-level arith check trips and the combiner bails `Unknown`
(`combiner.rs` ~532). Inv-3's `SHINRI_SKIP_EE` ceiling (removing this seam
entirely) still leaves all five pins `Unknown` at K=8 — real, but not
sufficient by itself.

**3. SAT/B&B search over the K length cases diverges once forced.** With
both arith cost centres removed (box shrunk + seam skipped), wall time drops
to 1.3-3.1s at K=8, but raising the branch budget to force a decision makes
p4 — the *easiest* target pin, whose model is the trivial `|s|=0 -> v=-1`
— **diverge (>90s)**. Inv-2 independently found the same shape: p4 at K=8,
ALT+EXCL, `PIVOT=2,000,000 BRANCH=1,000,000` did not terminate in 4 minutes.
The cost is the *presence* of the 8 length cases + K·10 value-links + the
`str.len` interface terms they all spawn, independent of which model is
found.

**4. Word equations are never on the critical path.** Confirmed by inv-2
(zero `[wordeq]` invocations for any pin, including the length-pinned p3)
and re-confirmed by inv-3 (str.check <= 64ms at K=8; the word-equation
engine never fires). Inv-1's proposed remedy — length-directed alignment in
`wordeq.rs` — targets a subsystem the digit bridge's conditional
(`dl>0`) length-case merges structurally never reach (the E1
`side_clean(input_cond_roots)` gate routes them away). Making Mechanism A
relevant at all would require *three* coordinated changes (EXCL-style
Boolean length commitment, relaxing the E1 gate with correct
merge-antecedent citation, and the alignment itself) — on top of, not
instead of, the arith-seam fix.

**Bottom line: 0/5 target pins pass at K=8** under any single mechanism or
combination tried (default; ALT+EXCL; branch-local fuel; raised pivot/
branch budgets to 2M/1M; box shrink; box+seam-skip; box+seam-skip+raised
branch, which diverges). No K decides the full 5-pin suite either: the
workable K per pin is tiny and the pins conflict — p1 needs K<=2, p2/p4
need K=1, p3 needs *exactly* K=3, p5 (a 2-digit `from_int`) solves at no K.

## What remains sound and reusable

- **The encoding's soundness held throughout every investigation.**
  Demotions (d1: real in-bound `to_int(x)=-5` unsat; d2: `from_int(n)="05"`
  leading-zero unsat; d3: the spec-R2 `dig_i` char-only-selector guard)
  stayed `Unknown` — correctly — under every mechanism combination in every
  report: 3/3 in inv-2, 3/3 in inv-3. Zero spurious `Sat` was ever produced.
  d1 reaches a genuine in-bound `Unsat` before demotion (verified explicitly
  in inv-2 with a raised pivot budget), proving the demotion gate actually
  fires on real unsats, not just an unreached dead branch.
- **The `Unsat -> Unknown` demotion contract** (`crates/shinri-solver/src/
  lib.rs`, the `int_conv_bridged` flag consumed at the single string-path
  outcome match) is architecturally sound and reusable as-is for any
  future bounded under-approximate string/int encoding.
- **Branch-local fuel** (`fuel_stack: Vec<u32>` in `StrSolver`, snapshot on
  push / restore on pop) was implemented twice (inv-2, inv-3's baseline),
  regression-clean both times (71/71 `shinri-str`, 29/30 differential, zero
  collateral regressions, **zero verdict changes** on the target pins). It
  is correct, complete-preserving infrastructure worth landing whenever a
  consumer needs it — it does not itself move the K=8 wall (it only stops
  the string-fuel bail from *masking* the deeper arith wall).
- **ALT/EXCL** (move `|c_i|=1`/value-links into each length-case body; add
  an explicit length disjunction) are sound, cheap encoding hygiene —
  entailed by the existing bounds, semantics-preserving — and strictly
  improve small-K solvability, though insufficient alone for K=8.
- **Horner-form `digit_sum`** caps the LIA coefficient `a` at 10 instead of
  `10^(K-1)` — a **partial mitigation only**: `n+m` (the box exponent)
  stays linear in K, so `M` remains hundreds of digits at K=8; it shrinks
  but does not eliminate the a-priori box blowup.

## Design requirements for the lazy int-conv propagator

Derived directly from the compound-wall evidence above — scope a future
slice against these, not against slice 16's encoding shape:

- **Must not eagerly mint K length cases, K·10 value-links, or K+1 shared
  `str.len` terms up front.** The single biggest lever: it drives both the
  O(K²) same-β interface probing (cause 2) and the SAT/B&B branching
  factor (cause 3). Derive digit facts on demand, only for lengths the
  search actually commits to.
- **Must keep arith coefficients small** (Horner / incremental digit
  derivation, not positional `10^(k-i)` powers baked into one linear
  term) — any LIA the propagator emits otherwise reseeds the same
  a-priori-box blowup (cause 1), which is generic to *any* eager encoding
  handing arith a large coefficient.
- **Must not grow the Nelson-Oppen shared set** (`euf.shared_arith_terms ∪
  string.shared_arith_terms`) super-linearly in digit count or occurrence
  count — the combiner's round cap and the seam's O(K²) probing both scale
  directly off `|shared|`.
- **Must preserve the fence-or-decide soundness contract**: never fabricate
  `Sat` (no unguarded digit-selector leak, cf. spec R2 / demotion d3), and
  never claim `Unsat` beyond what is actually derived — a propagator that
  only partially explores digit space must demote to `Unknown`, exactly as
  the eager bridge's asserted-bound `Unsat` does.
- **Should integrate as a DPLL(T) theory propagator** deriving int↔string
  digit facts incrementally (digit-by-digit or a length-guessing
  propagator) instead of a one-shot term-rewrite stage — the "principled
  fix" all three investigations converge on; sized as a new
  theory-propagator slice (multi-day, cross-crate), not an `int_conv.rs`
  tweak.
- **Open feasibility questions, honestly unresolved:** a lazy propagator
  still needs *some* representation of "this string's length is `k`" to
  derive digit facts, and inv-3 showed that representation reaching the
  arith/N-O seam at all (even without the box) still costs O(K²) probing
  once more than a couple `str.len` terms are shared — a propagator too
  close to the eager gadget's *shape* could still stress the same seam,
  just later. Any LIA it ever emits, even one term at a time, is subject
  to the same a-priori box formula; the mitigation must keep
  coefficient/variable count small at every step, not just defer emission.

## References

All three scratch reports are git-ignored and not part of the repo history;
this note is their permanent, superseding record.

- `/workspace/.superpowers/sdd/task-3-diagnosis.md` — inv-1: K-scaling,
  budget analysis; wordeq-alignment remedy refuted by inv-2.
- `/workspace/.superpowers/sdd/engine-spike-findings.md` — inv-2: refutes
  inv-1's remedy; finds the arith N-O seam; validates branch-local fuel.
- `/workspace/.superpowers/sdd/seam-spike-findings.md` — inv-3: seam
  mechanism map; a-priori box blowup; compound wall; box/seam fix
  prototypes.
- Plan: `docs/superpowers/plans/2026-07-11-shinri-slice16-digit-bridge.md`.
- Spec: `docs/superpowers/specs/2026-07-11-shinri-slice16-digit-bridge-design.md`.
- Archive: tag `archive/slice16-eager-bridge`; commits `25ee5dd` (to_int
  gadget), `81927db` (from_int gadget), branch `slice16-digit-bridge`.
