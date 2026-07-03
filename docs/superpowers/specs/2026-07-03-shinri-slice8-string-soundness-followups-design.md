# Slice 8 design — string-soundness follow-ups (analyze OOB + distinct-over-concat wrong-UNSAT)

Date: 2026-07-03
Status: DESIGN (awaiting user review)
Predecessor: slice 7 (`d7089c2..47c8342`, landed 2026-07-03)

## Goal

Close the two OPEN pre-existing soundness follow-ups filed at the end of slice 7,
then unblock the string-oracle re-baseline that both of them were holding back.
Both were confirmed pre-existing at base `d7089c2` (not slice-introduced); the
widened string oracle surfaced them. Repros live in
`.superpowers/sdd/task-4b-report.md`.

- **#2** — `shinri-sat/src/solver.rs:293` `analyze` index-out-of-bounds on some
  `str.++`/`str.len` shapes. PRIORITIZED: the slice-7 VMTF fix recovers more
  branching vars, which raises this bug's exposure on wide-seed fuzzing.
- **#1** — string `distinct`-over-concat wrong-UNSAT. At `Effort::Full`,
  `distinct("", s2++"a")` drives a unit conflict that unsoundly forces
  `s2++"a" = ""` (impossible: a concat ending in the constant `"a"` is never
  empty). BROAD-HIGH risk class.

Non-goal: no new theory/op admission, no fence lift, no fuzz-seed widening beyond
the single deferred re-baseline. This slice is soundness repair + re-baseline only.

## Scope & sequencing

Three units, in this order, each its own commit, each via TDD +
systematic-debugging:

1. **#2 first** — `analyze` OOB (SAT core). Prioritized, and fixing it stabilizes
   the differential-oracle fuzzing harness so unit 3's re-baseline sweep cannot
   crash mid-run.
2. **#1 second** — string `distinct`-over-concat wrong-UNSAT (shinri-str). Broad;
   full minimized repro already exists (task-4b §6).
3. **Re-baseline last** — bump the string oracle seed `0xB000_9E37 → 0xB000_9E38`,
   regenerate the baseline, verify 0 disagreements. This is the deferred work both
   bugs were blocking.

## Unit 1 — #2 `analyze` OOB

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

A no-OOB / no-panic regression pin over the minimized #2 input in the string
differential suite. (Verdict-neutral until we know the correct verdict; the pin
asserts "does not panic / OOB", not a specific sat/unsat.)

## Unit 2 — #1 string `distinct`-over-concat wrong-UNSAT

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

## Unit 3 — string-oracle re-baseline

With both soundness bugs closed, bump the string differential-oracle seed
`0xB000_9E37 → 0xB000_9E38`, regenerate the baseline counts, and verify the sweep
returns 0 disagreements. Record the new baseline file. If unit 2 landed as (C), the
task-4b-shaped inputs appear as `unknown` in the counts (sound), not `unsat`.

## Verification net (per fence-canary memory)

- Pre-flight canary re-grep BEFORE editing: enumerate e2e + unit canaries pinned to
  the current Unknown/wrong verdicts on the touched shapes; net any that flip.
- `cargo test --workspace` — all suites 0-failed.
- Oracle sweep — 0 disagreements (including the re-baselined string oracle).
- `clippy` — zero net-new warnings.
- Both regression pins green.

## Risks

- **#1 breadth:** the complete (A) fix could touch the String↔Arith length seam;
  the (C) floor bounds this to a sound-Unknown. Mitigated by the decision rule.
- **#2 diffuseness:** if multiple theory paths can emit unregistered-var literals,
  the defensive `ensure_vars` guard covers all of them structurally even if the
  root-cause fix only addresses the one the repro found.
- **Canary breakage:** touching diseq/length verdicts on string shapes may flip
  canaries pinned to the old wrong-UNSAT; the pre-flight re-grep front-loads this.
```

## Open decision (deferred, user away)

Fix depth for #1 was posed as A / A-only / C. Proceeding with **target (A), fall
back to (C)** (recommended) unless the user redirects.
