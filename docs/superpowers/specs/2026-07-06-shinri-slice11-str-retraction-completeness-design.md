# Slice 11 design — str retraction completeness + analyze OOB hardening

Date: 2026-07-06
Status: IMPLEMENTED (slice 11 landed). Root cause: Combiner::pending_conflict
survived pop (assert→propagate bridge) — cleared in pop; debug retraction
audit added (shinri-sat sweep over str stores + shared-engine forest/diseqs +
pending_conflict); guard hardened with bounds check + bailout counter
(harness-asserted 0). Sweep: sat=13/unsat=179/unknown=8, z3_checked=192,
0 disagreements. RESIDUE (risk §5.3, new follow-up): the canonical slice-8
cluster-B input remains a sound fuel-Unknown — shinri-str's word-equation
search does not converge on it even at 100× fuel; decisive-SAT there needs
wordeq-completeness work, out of slice-11 scope. The decisive-verdict
acceptance is carried by targeted_pending_conflict_pop_decides_sat instead.
Predecessor: slice 10 (`61dfad9..c4885f9`, PR #3, landed 2026-07-06)

## Goal

Recover decisive verdicts on the string inputs where slice 8's cluster-B
guard (`theory_conflict_analyzable`, `shinri-sat/src/solver.rs:257`) currently
bails to sound `Unknown`, by root-causing and fixing the failed retraction
that lets a string-theory conflict cite a stale-level (unassigned) literal.
Bundle the still-open `analyze` unregistered-var OOB (slice-8 follow-up #2).
Landing this retires **both** remaining slice-8 follow-ups.

Approach (chosen over repro-only debugging and over a structural
level-tagged-store rewrite): **A+B hybrid** — build a debug-mode retraction
invariant checker first (it is simultaneously the localization tool and the
permanent alarm), root-cause the known repro under it, fix minimally at
whichever layer actually owns the bug, keep the checker and a guard-fires
counter permanently.

Non-goals:

- No completeness work beyond un-blocking the guard-bailed inputs; the
  general word-equation completeness of `shinri-str` is untouched.
- No fence lifts (Array-Real / Str-Real bridge, `fp.to_real` eb>8 all stay
  as pinned by slice 10).
- No string-oracle seed change unless verdict counts legitimately change
  (expected: some of the current 9 unknowns at seed `0xB000_9E38` flip to
  decided; counts re-baselined in place with the reason documented).
- Slice-8 cluster-A str fix **stays** (user re-confirmed KEEP 2026-07-06;
  the standing re-confirm item is closed).

## 1. Problem statement

`shinri-str` stores asserted (dis)equalities in `eq_true`/`diseq_true`,
truncated on `pop` via trail marks (`shinri-str/src/lib.rs:703-712`). Conflict
justifications cite `EqLeaf::Asserted(lit)` from **two provenances**: those
stores directly, and the shared EUF proof forest walked in
`lib.rs:645-683`. Somewhere, a lit survives backtracking: slice 8 observed a
string-theory `Conflict::Lits` citing an `Unset` var whose stale `level`
(not cleared by `unassign`) exceeded the current decision level. Pre-slice-8
that panicked at `trail.rs:91`; since slice 8 the guard converts it to a
sound `Unknown`. Known repro: string-oracle seed `0xB000_9E38`, iteration
1013.

Slice-8 lesson that shapes this design: the filed cluster-A string bug turned
out to be a downstream symptom of an EUF-layer corruption in a **different
crate**. The design therefore does not presume the owning layer; the checker
covers both provenances and the fix lands wherever the evidence points
(str trail, proof-forest tags, eq_engine pop, or push/pop dispatch ordering).

Separately, `analyze` (`solver.rs:310`, `analyzer.seen[v.index()]`) and
`theory_conflict_analyzable` itself (direct assignment indexing) can panic if
a theory conflict cites a var never registered with the SAT solver. Never
triggered by the current corpus (needs a `str.len`-bearing conflict); the
var-range registration path was deferred YAGNI in slice 8 and stays deferred —
this slice hardens the read sites instead.

## 2. Components

### 2.1 Retraction invariant checker (debug-only, permanent)

A `#[cfg(debug_assertions)]` audit hook on the `TheorySolver` trait:

- `cited_lits() -> Vec<Lit>` (default impl: empty) — every literal the theory
  could currently cite in a conflict justification.
- Implemented by `StrSolver` (the `eq_true`/`diseq_true` stores). The shared
  `EqualityEngine` is not a `TheorySolver`; it exposes an equivalent
  debug-only accessor over its `Asserted` proof-forest tags — the second
  provenance — swept by the same audit.
- The CDCL(T) backtrack path, immediately after dispatching theory pops,
  sweeps all cited lits and **panics with provenance** (which store, which
  atom, stored level vs current decision level) on any entry that is not
  still False-assigned at level ≤ the current decision level.

This moves the failure signal from conflict time (far from the cause) to pop
time (at the cause). Release builds are unaffected. Exact plumbing (where the
sweep hooks into the solve loop, how the eq_engine exposes its tags) is a
plan-time decision; the contract above is the design.

### 2.2 Root-cause + minimal fix

Reproduce seed-`0xB000_9E38` iter-1013 (and harvest any of the sweep's 9
unknowns that are guard-bails) under the checker; it should panic at the
exact pop that leaks. Diagnose with the systematic-debugging discipline; fix
**minimally at the owning layer**, deliberately unspecified until diagnosis.
Acceptance (not mechanism) is what the design pins:

- checker clean across the full string-oracle fuzz sweep;
- the guard counter (§2.4) is 0 across the corpus (subject to the
  documented-residue exception in risk §5.3);
- the **iter-93 guard-bail input** flips Unknown → decisive SAT (z3-agreed), pinned as `targeted_pending_conflict_pop_decides_sat`; the canonical slice-8 pin remains a documented sound fuel-Unknown (see Status).

### 2.3 `analyze` / guard OOB hardening

- `theory_conflict_analyzable` bounds-checks each cited var against the
  registered var range and returns `false` when out of range — an
  unregistered var is definitionally unanalyzable, so this rides the
  existing sound-Unknown bail. Converts a would-be panic into soundness.
- `analyze` gets a `debug_assert!` that every conflict var is in range —
  unreachable from theory conflicts once both call sites
  (`solver.rs:504`, `solver.rs:609`) guard first; the assert documents and
  enforces that.
- Unit test: a synthetic theory conflict citing an out-of-range var →
  sound `Unknown`, no panic (both debug and release semantics).

### 2.4 Guard alarm

A test-visible `theory_guard_bailouts` counter on solver stats. The
differential/oracle harnesses assert it is **zero** post-fix — a firing is a
retraction regression and reads as red CI. Runtime semantics of the guard are
unchanged (sound bail, never a panic in release), so a genuinely novel stale
conflict in production still degrades to `Unknown` rather than crashing.

## 3. Error handling / soundness posture

Every new path degrades sound: the checker is debug-only; the guard's bail
semantics are untouched; the OOB fix converts a panic into the existing
sound-Unknown route. Only §2.2's fix can change verdicts — and only in the
decided-more direction — netted by the full differential sweeps below. If the
fix lands in shared infrastructure (eq_engine, dispatch), the blast radius is
every theory; the full-workspace + full-oracle net is mandatory, not
optional.

## 4. Testing

- **Pre-flight canary hunt** (standing cross-slice lesson): before fixing,
  enumerate tests/canaries pinning `Unknown` (or a panic-shaped bail) on the
  affected string inputs — flipping them to decided breaks stale pins.
  Front-load the list into the plan.
- **Unit:** synthetic out-of-range theory conflict → sound Unknown, no panic;
  checker catches a hand-built stale-lit store in a debug-build test.
- **Regression pin:** seed-`9E38` iter-1013 input as a named e2e test with
  its decisive, z3-agreed verdict.
- **Sweeps:** string differential oracle at the current seed — `unknown`
  expected to drop from 9; counts re-baselined in place with the reason in
  the test comment; guard counter asserted 0. Full `cargo test --workspace`
  and the full oracle sweep (including fp, ~915 s) as the net. Clippy on a
  **clean** cache (warm-cache clippy false-passes in this environment).
  Long gates run by the controller in the background — no subagent
  wait-loops.

## 5. Risks

1. **Repro may not reproduce** after slices 9/10 changed surrounding
   behavior. Mitigation: the checker + extended fuzz iterations is an
   independent path to the same bug class; if nothing fires anywhere, the
   slice pivots to documenting the gap as closed-by-evidence (with the
   checker kept) rather than fixing blind.
2. **Root cause in shared infrastructure** (eq_engine pop, dispatch
   ordering) — wider blast radius; covered by the mandatory full net.
3. **Some guard-bails may be legitimately unanalyzable** for a second,
   different reason. Then the counter-zero assertion applies to the corpus
   that the fix explains; the residue is documented as a new, separate
   follow-up — not force-fixed in this slice.

## 6. Acceptance summary

| Criterion | Bar |
|---|---|
| Repro verdict | seed-9E38 iter-1013 decides, agrees with z3, pinned e2e |
| Checker | clean across full string fuzz sweep; permanent debug net |
| Guard counter | 0 across differential corpus, asserted in harnesses |
| OOB | out-of-range citation → sound Unknown, no panic; unit-pinned |
| Net | full workspace + full oracle sweep 0 disagreements; clean-cache clippy 0 net-new |
| Ledger | both slice-8 follow-ups retired; residue (if any) filed as new follow-up |
