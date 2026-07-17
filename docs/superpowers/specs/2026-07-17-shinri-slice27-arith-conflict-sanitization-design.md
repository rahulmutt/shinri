# Slice 27 design — arith conflict-core sanitization seam

Date: 2026-07-17
Status: IMPLEMENTED (2026-07-17). See "Implementation notes (truth-up)" at the end.

Predecessor: slice 26 (leaf-membership length-seam termination, landed
2026-07-17). Slice 26's truth-up banks this as its explicit follow-up
(item i, "BANKED KNOWN ISSUE"): a pre-existing, latent `shinri-arith`
sentinel-literal leak, exposed (not caused) by slice 26's trajectory change
on the `qfs_regex_symbolic` it194 repro, reproduced during root-causing,
and then re-hidden (not fixed) by `aadc95ad`. Unlike slices 24→26, the
pre-spec diagnosis pass here **confirms the banked framing** — the leak is
exactly where the truth-up placed it — and adds one finding the bank did
not: the `assert` conflict exit is equally exposed, not just `check`'s.

## 1. Problem

`Arith` mints synthetic sentinel literals from the reserved top-half var
region (`SENTINEL_VAR_BASE = 1 << 30`, `crates/shinri-arith/src/lib.rs:36`,
minted by `fresh_sentinel`, lib.rs:505-515) for two distinct purposes:

- **Level-0 axiomatic bounds** — the a-priori Int box and FBBT
  tightenings, tracked in `apriori_lits` (lib.rs:74, populated at
  lib.rs:1038-1039 and lib.rs:1061). These are level-0-entailed facts; a
  conflict core remains valid with them removed.
- **Interface-equality pseudo-literals** — minted by
  `assert_interface_equality` (lib.rs:746-794) to carry a `TheoryJust`
  through the bounds layer (a `Lit` cannot pack one), tracked in
  `iface_lit` (lib.rs:65, keyed lit-code → tag → `iface_justs`). These are
  **live-level** facts with a real justification; a conflict core citing
  one must resolve it to `EqLeaf::Interface(just)` — omitting it would
  claim a conflict from too few antecedents (unsound).

Four paths return conflict cores out of the theory. Two sanitize
correctly via `resolve_iface_leaves` (lib.rs:799-816): the Nelson-Oppen
entailment probes (lib.rs:717, 721) and `assert_interface_equality`'s own
conflict arms (lib.rs:778, 781, 786). Two sanitize with `strip_apriori`
(lib.rs:1067-1074), which only filters `apriori_lits` membership and knows
nothing of `iface_lit`:

- `TheorySolver::assert` (lib.rs:1146),
- `TheorySolver::check` (lib.rs:1168).

**Failure mode**: when a later top-level `Arith::check` independently
finds a Farkas conflict (`check_full`, lib.rs:352) that transitively cites
a still-live interface-equality bound, the raw pseudo-literal survives
`strip_apriori` and reaches `shinri-sat`'s `theory_conflict_analyzable`
guard (`crates/shinri-sat/src/solver.rs:294-301`), which correctly rejects
it (var index ≥ `assign.num_vars()`) and bails to a sound Unknown
(solver.rs:658-660). The verdict is never wrong — the cost is
completeness: a decidable conflict degrades to Unknown, and the learnt
clause that would have pruned the search is never produced.

The `assert` exit has the same shape: an interface equality installs
fixed bounds on the slack var of the difference combination `a − b`
(lib.rs:760-762); an input atom over the same combination normalizes to
the **same slack var** (`slack_var(&comb)` is keyed by combination), so an
asserted bound can cross the iface bound directly in `apply_bound`, and
the crossing bound's sentinel lit lands in the conflict core. This is the
mechanism behind slice 8's a-priori assert-path leak (the lib.rs:1135-1145
comment) with the second sentinel flavor substituted; it was not named in
the slice-26 bank, which cited only the `check` path.

`integer_check` (lib.rs:826-904) returns only Sat/Unknown/Split — never
`Conflict` — so it is not an exit and needs no change. The entailed-
equality `explain` path already debug-asserts sentinel-freedom at
antecedent-build time (lib.rs:1187-1189).

## 2. The fix — one sanitizer owns the exit invariant

Approach chosen over two alternatives (§5): unify every conflict exit on
the existing, correct sanitizer.

- **Rename** `resolve_iface_leaves` → `sanitize_conflict`, with a doc
  comment declaring the invariant it owns: **no raw sentinel literal ever
  leaves `Arith` in a conflict core.** Interface pseudo-lits resolve to
  `EqLeaf::Interface(just)`; every other sentinel (a-priori box, FBBT,
  probe) drops as a level-0-entailed fact.
- **Route** the two leaky exits through it: replace the `strip_apriori`
  calls at lib.rs:1146 (`assert`) and lib.rs:1168 (`check`) with
  `sanitize_conflict`.
- **Delete** `strip_apriori`. It is subsumed: every a-priori/FBBT lit is
  minted via `fresh_sentinel`, so `sanitize_conflict`'s
  is-sentinel-and-not-iface arm (lib.rs:808) already drops all of them
  without consulting `apriori_lits`. The `apriori_lits` set itself stays —
  it is still read by the seeding-idempotence unit pin
  (lib.rs:2159-2163) — but its only production read disappears; note this
  in its field comment.
- **Enforce** at the choke point: a tail `debug_assert!` in
  `sanitize_conflict` that no surviving leaf is
  `EqLeaf::Asserted(l)` with `is_sentinel(l)`. Every debug-mode test run
  (unit, oracle, fuzz) then checks the invariant on every conflict; a
  third sentinel flavor added without a resolution rule fails loudly
  instead of leaking silently.
- **Truth-up comments** that name `strip_apriori` or narrate the old
  split: the branch-and-bound level-0 note (lib.rs:1015), the assert-path
  soundness block (lib.rs:1135-1145), and the unit test whose comment
  references `strip_apriori` (lib.rs:2266).

No changes outside `shinri-arith` (see §6 for what stays put).

## 3. Soundness argument

Two arguments, one per sentinel flavor — both pre-existing, now applied
uniformly:

- **Dropping** a-priori/FBBT/probe sentinels is sound because those
  bounds are level-0-entailed facts (a-priori box, FBBT fixpoint) or
  probe-local assumptions already discharged at probe scope; the
  remaining core is a valid conflict over real assertions. This is the
  slice-8 stripping argument, unchanged, with the differential oracle as
  the empirical net.
- **Resolving** iface pseudo-lits to `EqLeaf::Interface(just)` is
  *required*, not optional: interface-equality bounds are installed at
  the live decision level under a real `TheoryJust` (lib.rs:772-774), so
  the core must cite them for the Combiner to expand recursively via the
  owning theory's `explain` (the CRITICAL-1 protocol). Widening the strip
  filter to swallow them would be unsound; that asymmetry is why the fix
  reuses resolution rather than teaching `strip_apriori` about a second
  set.

Consumer surface is unchanged: the Combiner already receives
`EqLeaf::Interface` leaves from the probe and `assert_interface_equality`
exits today; after the fix the `assert`/`check` exits produce the same
leaf vocabulary.

Behavioral delta: conflicts that previously bailed at the shinri-sat
guard become analyzable — strictly more learnt clauses, strictly fewer
guard bailouts. Verdict changes can only be Unknown → decided; any
decided → unknown movement is a regression by definition (§4).

## 4. Testing

- **Required unit pins (fail pre-fix), one per leaky exit**, in
  `shinri-arith`'s test module, driving the public `Arith` API directly
  (no Combiner needed, per the existing Nelson-Oppen unit-test pattern):
  - *check path*: `assert_interface_equality(a, b, just)` on shared Int
    terms, then `new_var`/`assert` real atom bounds that make
    `check_full` infeasible **through** the iface-pinned slack (e.g.
    `a − b` forced nonzero transitively); assert the conflict contains
    `EqLeaf::Interface(just)`, contains the real asserted lits, and
    contains no leaf with a sentinel lit.
  - *assert path*: install the interface equality, then assert an atom
    over the same difference combination that crosses the fixed bound at
    `apply_bound` time; same three assertions on the returned core.
- **Choke-point invariant**: the `debug_assert!` in `sanitize_conflict`
  (§2) upgrades every existing debug-mode run into a regression net for
  the whole bug class.
- **Regression net**: `shinri-arith` and `shinri-solver` suites, the
  differential oracle with `--features oracle` (foreground, captured
  output), and per-iteration dump-and-diff on the fuzz families —
  slice 26's methodology note (k): fixed LCG seeds give query-text
  identity, so per-iteration verdict diffs are exact. Acceptance:
  tallies bit-identical or strictly improved (Unknown → decided, each
  z3-confirmed, capped). Any decided → unknown flip is stop-the-line.
- **Best-effort e2e (timebox: one focused session, ~half a day)**: hunt
  for a full-stack query that trips
  `theory_guard_bailouts` pre-fix. First candidate: replay the
  `qfs_regex_symbolic` it194 repro against a temporary local revert of
  `aadc95ad` (the slice-26 fix that re-hid the trajectory) to confirm the
  leak fires pre-fix and dies post-fix on the same build; if a
  non-reverted trigger falls out of the dump-and-diff, pin it as a
  targeted test. If the timebox expires with no stable e2e pin, record
  that in the truth-up and rely on the unit pins + choke-point assert.
  This slice does not block on an e2e pin (decided at design time).

## 5. Alternatives considered

- **Widen `strip_apriori`** to also consult `iface_lit`: same behavior,
  but keeps two near-duplicate sanitizers with the invariant split across
  them — the exact structure that produced this bug (a-priori stripping
  was added in slice 8 for one exit pair; nobody revisited the iface
  flavor). Rejected: strictly dominated by unification.
- **Typed antecedent enum** in the bounds layer (`Lit | AprioriTag |
  IfaceTag` instead of packing justifications behind pseudo-lits): the
  type system would make leaking impossible. Rejected *for this slice*:
  it touches `Bounds`, `apply_bound`, Farkas-core assembly, and every
  explain path — a refactor slice with its own regression risk, for a
  guarantee the choke-point assert approximates at near-zero cost. Banked
  (§6).

## 6. Non-goals (banked)

- **Typed-antecedent refactor** (§5): banked structural hardening. Cash
  it if the sentinel-leak invariant is violated a third time despite the
  choke point.
- **shinri-sat guard**: `theory_conflict_analyzable` and its bailout
  (solver.rs:294-301, 658-660) stay untouched as defense-in-depth; the
  `theory_guard_bailouts` counter stays as the observable.
- **Completeness work beyond the fix**: no attempt to chase whatever
  residual Unknowns remain on interface-exchange-heavy queries once the
  leak is closed; whatever the dump-and-diff surfaces gets banked, not
  fixed here.

## Implementation notes (truth-up)

Implemented 2026-07-17 on branch `slice27-arith-conflict-sanitization`
(base `ffc27248` = main with plan/spec docs pre-landed).

**Landed as designed:**

- `09c32459` — check-path pin + unified sanitizer. `resolve_iface_leaves`
  renamed to `sanitize_conflict` (invariant doc comment + tail
  `debug_assert!` choke point appended; body otherwise byte-identical),
  all five call sites + probe doc-comment mention updated, the
  `TheorySolver::check` conflict exit rerouted from `strip_apriori` to
  `sanitize_conflict`. New TDD pin
  `check_conflict_through_iface_bound_resolves_no_sentinel` (Ge shapes on
  three distinct slack vars — infeasibility only visible to simplex at
  check time; pre-fix run captured the raw leaked sentinel
  `Asserted(Lit(2147483648))`).
- `af7b53f3` — assert-path pin, `strip_apriori` deleted as subsumed, the
  three mandated comment truth-ups (`apriori_lits` field doc, B&B level-0
  comment, Bug-1 regression-test doc comment). New TDD pin
  `assert_conflict_crossing_iface_bound_resolves_no_sentinel` (Le atom
  canonicalizes onto the iface diff-comb slack var — crossing at assert
  time; pre-fix leak captured). Full `shinri-arith` suite 59/59.
- `aebb0f83` — Task 4's best-effort e2e pin turned out NOT to need the
  revert-replay fallback: the Task 3 dump-and-diff surfaced natural
  triggers, one of which is committed as
  `targeted_arith_iface_sentinel_conflict_now_decides`
  (qfs_differential.rs, house `expect(query, Verdict::Sat)` pattern; the
  pin also asserts `theory_guard_bailouts == 0`, so it fails pre-fix).

**Deviations (all minor):**

- (a) Task 1's test replaces the plan's `other => panic!("… got
  {other:?}")` arm with `_ => panic!("…")` — compiler-forced: `TCheck`
  derives no `Debug`.
- (b) No other code deviations; test/comment text otherwise verbatim from
  the plan (modulo rustfmt rewrapping).

**Task 3 dump-and-diff result (base `ffc27248` vs fix `af7b53f3`):**

- Fix-side oracle differential: 76 passed / 0 failed, 0 shinri-vs-z3
  disagreements, 0 guard bailouts across all 13 fuzz families.
- Per-iteration diff (3680 base / 3682 fix DIFFDUMP lines; the +2 are
  witness-fetch dumps newly reachable on iterations that became sat):
  exactly THREE flips, all strict improvements —
  `qfs_predicates` hash `d9788e5ca38388b1`: unknown bail=1 → sat bail=0
  (committed as the Task-4 pin); `qfs_predicates` second flip: unknown
  bail=1 → unknown bail=0 (bailout eliminated, verdict unchanged);
  `qfs_to_from_int`: unknown bail=1 → sat bail=0. Zero decided→Unknown,
  zero sat↔unsat, zero bailout increases. Spec §4 acceptance met.

**Task 4 outcome:** natural-trigger pin committed (`aebb0f83`); the
plan's Step-2 revert-replay confirmation was unnecessary and skipped.

**Newly banked:** nothing. The slice-26 banked items other than this leak
(Rex intersection-emptiness for infinite conflicting tails) remain banked
unchanged. The remaining two Unknown-with-bailout=0 iterations surfaced by
the dump are ordinary incompleteness, per this spec's non-goal ("whatever
the dump-and-diff surfaces gets banked, not fixed here") — no new solver
work identified.
