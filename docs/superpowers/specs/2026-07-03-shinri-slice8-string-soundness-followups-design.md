# Slice 8 design — string-soundness follow-ups (analyze/backtrack + explain-not-connected + distinct-over-concat)

Date: 2026-07-03
Status: IMPLEMENTED (slice 8 landed 2026-07-03). Both open follow-ups retired
by slice 11: #1 root-caused (Combiner::pending_conflict not cleared on pop —
NOT a shinri-str retraction failure; fixed + debug retraction audit) with a
wordeq-completeness residue follow-up on the canonical cluster-B input; #2
closed (guard bounds check; analyze debug-assert).
Predecessor: slice 7 (`d7089c2..47c8342`, landed 2026-07-03)

## Goal

Make the string differential oracle run clean at the target re-baseline seed
`0xB000_9E38` — 0 disagreements AND 0 debug panics — then advance the seed. A
repro hunt at `0xB000_9E38` (recorded in `.superpowers/sdd/slice8-repro-findings.md`)
showed the seed is blocked by **three** defect clusters, not the two originally
filed. All are pre-existing at base `d7089c2` (not slice-introduced); the wider
seed surfaces them.

- **Cluster A / #1** — string `distinct`-over-concat wrong-UNSAT. At
  `Effort::Full`, `distinct("", s2++"a")` drives a unit conflict that unsoundly
  forces `s2++"a" = ""` (impossible: a concat ending in the constant `"a"` is
  never empty). z3=sat, shinri=unsat. BROAD-HIGH risk class. (First disagreement
  at seed 9E38 iter 93; matches task-4b §6.)
- **Cluster B / #2** — `analyze`-family robustness. Manifests in this corpus as a
  `trail.rs:91` debug-assert `"backtrack above current level"` (analyze produced a
  backjump level above the current decision level). The originally-filed
  `solver.rs:293` `seen[v.index()]` OOB is the SAME family (both fired by
  string-theory `Conflict` literals); line numbers shifted after slice 7. Repro:
  seed 9E38 iter 1013.
- **Cluster C / NEW** — RESIDUAL `eq_engine.rs:379` debug-assert
  `"explain: a,b not connected"` — the SAME assert slice 7's `InsertOverwrite`
  fix (then at `:366`) was meant to close. It still fires via a SECOND, unguarded
  diseq-map mutation/undo path. Per task-4b §4 this class is a genuine RELEASE
  soundness bug (unsound merge + fabricated conflict), not debug-only. Repro:
  seed 9E38 iter 1524; seed 9E3A iter 672.

Non-goal: no new theory/op admission, no fence lift, no fuzz-seed widening beyond
the single re-baseline. This slice is soundness repair + re-baseline only.

## Scope & sequencing

Four units, in this order, each its own commit, each via TDD +
systematic-debugging. Panics (B, C) come before the wrong-verdict (A) and the
re-baseline, so the debug sweep can progress without aborting:

1. **Cluster B first** — `analyze`/backtrack robustness (SAT core). Prioritized;
   stabilizes the fuzzing harness so later sweeps don't abort on a panic.
2. **Cluster C second** — finish the slice-7 eq_engine diseq-undo work (the
   residual explain-not-connected path). shinri-theory.
3. **Cluster A third** — string `distinct`-over-concat wrong-UNSAT (shinri-str).
   Broad; minimized repro exists (task-4b §6, and seed 9E38 iter 93).
4. **Re-baseline last** — bump the string oracle seed `0xB000_9E37 → 0xB000_9E38`,
   regenerate the baseline, verify 0 disagreements AND 0 panics.

## Unit 1 — Cluster B: `analyze`/backtrack robustness

Observed manifestation: `trail.rs:91` `debug_assert!(level <= self.decision_level(),
"backtrack above current level")` fires because `analyze` returned a backjump
level `bt` above the current decision level (solver.rs:574–575, `backtrack_to(bt)`
after a `TheoryResult::Conflict`). The originally-filed `solver.rs:293`
`seen[v.index()]` OOB is the same family; whichever assert the repro hits, the
fix is the same class (analyze consuming a theory conflict whose literals/levels
are not consistent with the SAT var/level state).

### Diagnosis surface

`analyze` (solver.rs:275) indexes `self.analyzer.seen[v.index()]` at line 293.
`analyzer.seen` is grown ONLY through `new_var() → ensure_vars()` (solver.rs:85,
analyze.rs:14). The `TheoryResult::Conflict(lits)` arm (solver.rs:559) feeds
theory-returned literals directly into `analyze` WITHOUT allocating vars — unlike
the `SplitAtoms` arm, which mints+binds a fresh var per new atom (solver.rs:629).

**Hypothesis:** the string theory emits a conflict (or a reason literal reachable
from one) over a `Var` whose index was never registered via `new_var()`, so
`seen[v.index()]` is out of bounds. Consistent with the `str.++`/`str.len` trigger
(the string theory mints fresh skolem/length terms) and with the VMTF-raises-
exposure note.

### Approach (decided by the minimized repro)

- **Root-cause fix (preferred):** locate where the theory produces the unregistered
  literal and route it through the proper var-registration path, so no code path
  can hand `analyze` a var outside `seen`'s range.
- **Defensive floor:** at the theory-conflict entry, `ensure_vars(num_vars())`
  before `analyze`, and add a `debug_assert!` that every theory-literal var is
  `< seen.len()`. Cheap, always-sound; kept as a guard even if the root-cause fix
  lands, so the invariant is enforced structurally.

Repro-hunt first (systematic-debugging): a minimized `str.++`/`str.len` input that
OOBs `analyze` in debug. Likely outcome: guard + root-cause together.

### Pin

A no-panic / no-OOB regression pin over the cluster-B repro (seed 9E38 iter 1013)
in the string differential suite. (Verdict-neutral: the pin asserts "does not
panic / OOB", not a specific sat/unsat — the correct verdict for that input is
established once A and C also land.)

## Unit 2 — Cluster C: residual `eq_engine.rs:379` explain-not-connected

### Diagnosis surface

Slice 7 added `DiseqUndo::InsertOverwrite` (assert_diseq collision, eq_engine.rs:170)
and `DiseqUndo::RekeyOverwrite` (merge rekey collision, eq_engine.rs:256), each
mirrored in `pop` (eq_engine.rs:466–486). The assert at eq_engine.rs:379 still
fires, so a diseq-map mutation reachable from string-theory merges is STILL not
exactly reversed on `pop`. Candidate residual paths (to be isolated by the repro):
- multi-rekey replay ordering: the merge loop (eq_engine.rs:223–263) processes
  several stale keys; the reverse `pop` replay of `Rekey`/`RekeyOverwrite` may not
  invert when two rekeys in one merge touch overlapping keys;
- `merge_congruence` (eq_engine.rs:269) mutating diseqs without the mirrored undo;
- the early-conflict / self-key branch leaving the map in a state `explain` later
  looks up with a mismatched canonical key.

### Approach

Systematic-debugging from the in-hand repro (seed 9E38 iter 1524; seed 9E3A iter
672): instrument the diseq-map mutation + undo log across the failing push/pop,
find the mutation whose `pop` does not restore the exact pre-mutation entry, and
fix it by mirroring the proven `InsertOverwrite`/`RekeyOverwrite` undo pattern so
every mutation is exactly reversible. Blast radius held to the offending branch +
its `pop` arm (as the slice-7 fixes were).

### Pins

A no-panic pin (debug) over the cluster-C repro in the string differential suite,
AND — because the class is a release soundness bug — a z3-checked `expect_not_unsat`
/ verdict pin confirming the repro's release verdict is correct. Plus a
shinri-theory unit test asserting the specific mutation is restored across
`push → mutate → pop` (mirroring `assert_diseq_collision_preserves_displaced_diseq_across_backtrack`,
eq_engine.rs:674).

## Unit 3 — Cluster A / #1: string `distinct`-over-concat wrong-UNSAT

### Diagnosis surface

The wrong-UNSAT flows through the disequality **empty-length link**
(lib.rs:431–445). For `"" ≠ s2++"a"` it computes `len_class_zero(len(s2++"a"))`
= `eq.are_equal(len(s2++"a"), 0)` (lib.rs:729). When that returns `Some`, it emits
`Conflict([Asserted(lit)] + eq.explain(len(other), 0))`.

The bug is one (or both) of:
- `len(s2++"a") ≈ 0` is accepted as a conflict source even though a concat carrying
  a non-empty constant has length ≥ 1 — so it can never equal `""`; the diseq is
  trivially satisfiable and must NOT conflict.
- `eq.explain(len, 0)` returns no antecedents, collapsing the "conflict" to a UNIT
  clause `[Lit(diseq)]` that unsoundly forces `"" = s2++"a"` (the observed
  `Lit(6)` unit conflict in task-4b §6).

Both point at the same fix surface: the length-zero reasoning must respect the ≥1
lower bound of a concat that carries a non-empty string constant.

### Approach — target (A), fall back to (C)

- **(A) complete, SAT-preserving (target):** before the empty-length link fires,
  reject `other` whose normal form contains a non-empty string constant (structural
  length ≥ 1), so `len(concat-with-nonempty-const) ≈ 0` is never treated as a
  conflict source. The minimized input then correctly returns **SAT**. Guard the
  fix so it fires only on the genuinely-entailed-zero case with sound, complete
  antecedents.
- **(C) sound-Unknown floor (fallback):** if (A) bleeds into the String↔Arith seam,
  narrow the empty-length link to fire only when it can emit a fully-justified
  non-unit conflict, else yield `Unknown`. Guaranteed sound; the input returns
  `unknown` rather than `sat`.

Decision rule: implement (A); if root-causing shows the complete fix requires
broad length-integration changes touching the arith seam, drop to (C) and record
the reason in the progress ledger. Either way the verdict is never wrong.

### Pins

A z3-checked pin in `qfs_differential.rs` over the task-4b §6 minimized input:
```smt2
(declare-const s2 String)(declare-const s3 String)
(assert (not (distinct s3 "" (str.++ s2 "a"))))
(assert (not (= (str.++ s3 "a") "" s3 s2)))
(assert (distinct s3 (str.++ s2 "a")))
(check-sat)   ; z3: sat
```
Assert `run_outcome != Unsat` under (A) (ideally `Sat`); under (C) assert
`!= Unsat` (Unknown-or-Sat). Plus a focused unit test that `len(concat-with-const)`
is never in EUF class 0's conflict path.

## Unit 4 — string-oracle re-baseline

With clusters A, B, C closed, bump the `differential_qf_s_nary` seed
(nary_oracle.rs:227) `0xB000_9E37 → 0xB000_9E38`, regenerate the baseline counts,
and verify the debug sweep returns 0 disagreements AND 0 panics. Update the seed
comment (nary_oracle.rs:222–226) to drop the now-closed skirt rationale. Record
the new baseline counts. If Unit 3 landed as (C), the task-4b-shaped inputs appear
as `unknown` in the counts (sound), not `unsat`.

## Verification net (per fence-canary memory)

- Pre-flight canary re-grep BEFORE editing: enumerate e2e + unit canaries pinned to
  the current Unknown/wrong verdicts on the touched shapes; net any that flip.
- `cargo test --workspace` — all suites 0-failed.
- Oracle sweep — 0 disagreements AND 0 panics (including the re-baselined string
  oracle at seed 0xB000_9E38).
- `clippy` — zero net-new warnings.
- All three regression pins green (clusters A, B, C).

## Risks

- **Cluster A breadth:** the complete (A) fix could touch the String↔Arith length
  seam; the (C) floor bounds this to a sound-Unknown. Mitigated by the decision rule.
- **Cluster B diffuseness:** if multiple theory paths can hand `analyze` an
  inconsistent conflict, the defensive guard (`ensure_vars` + level/var
  `debug_assert`s at the theory-conflict entry) covers them structurally even if
  the root-cause fix only addresses the one the repro found.
- **Cluster C is another undo gap:** the residual may be a subtle multi-rekey
  ordering bug rather than a missing single-site undo; the shinri-theory
  push/mutate/pop unit test pins the exact invariant so a partial fix can't pass.
- **Canary breakage:** touching diseq/length verdicts on string shapes, and the
  eq_engine undo path, may flip canaries pinned to the old wrong-UNSAT / old panic
  behavior; the pre-flight re-grep front-loads this.

## Settled decisions

- **Scope** (user, this session): fold in cluster C — the slice fixes A, B, C then
  re-baselines. Recorded in `.superpowers/sdd/slice8-repro-findings.md`.
- **Cluster A fix depth** (user-approved spec): target (A) SAT-preserving, fall
  back to (C) sound-Unknown per the decision rule.
