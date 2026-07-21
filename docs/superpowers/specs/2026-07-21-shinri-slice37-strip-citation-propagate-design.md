# Slice 37 — Cite the strips (un-bank approach B, Propagate path)

Status: design. Author: brainstorming session, 2026-07-21.
Follows: slice 36 (`2026-07-21-shinri-slice36-sibling-skolem-mints-design.md`).

## 1. Context and trigger

`resolve_equation` (`crates/shinri-str/src/wordeq.rs:445`) is the wrapper
over `resolve_inner`. When any atom of either word is a `str.++` concat
rep, it **flattens** the concat atoms (`wordeq.rs:468-469`) and then
post-processes the inner resolver's result:

- `Conflict → Saturated` (`wordeq.rs:474`) — slice 33 vintage.
- `Propagate → Saturated` (`wordeq.rs:482`) — slice 35 T1.

Both downgrades exist because `resolve_inner`'s head/tail strip loops
(`wordeq.rs:546-555`) consume atom pairs via `same()` (`wordeq.rs:407`),
whose EUF branch (`eq.are_equal`, `wordeq.rs:414-416`) matches two atoms
that a **merge** placed in the same equivalence class — **without citing
that merge's antecedent**. On the flattened path the flattened inner
atoms were never rep-substituted by `normal_form`, so a class equality a
strip consumes is cited in **neither** the equation's own `just` nor the
normal-form antecedent set (`nf_ante`). A `Propagate { var, word, just }`
built after such a strip would carry an **under-justified** `just`: the
EUF merge the caller lands (tagged `EqJust::Interface`) rests on an
uncited fact. That is a wrong-UNSAT shape, and slice 35 fenced it by
blanket-downgrading the flattened `Propagate` to `Saturated` (a sound
`Unknown` / witness-checked SAT).

**The un-banking trigger has fired.** Slice 35's §5 dump-and-diff
measured the downgrade's completeness cost: exactly one `decided →
unknown` flip — source hash `8e950d0d36e258cb`, family
`qfs_predicates_matches_z3`, `sat` at base → `unknown` at fix, z3-agreeing
`sat`, no `sat ↔ unsat` disagreement, `bail=0` both sides. The human
partner adjudicated it accepted-as-is and recorded it verbatim as *"the
trigger for un-banking approach B (§2) in a future slice — it is not
un-banked by this decision, only logged as the qualifying event."* This
slice is that future slice. Its whole mandate is to restore that one hash
(and any siblings of the same shape) to `sat` **soundly**, by citing the
strips instead of suppressing the propagation.

## 2. Scope

**In scope.**

- A strip-explain pass in `resolve_inner`'s two strip loops that appends
  `eq.explain` leaves for every pair consumed via the `eq.are_equal`
  branch, threading them into `just` so both `Propagate` report sites
  (`wordeq.rs:775`, `wordeq.rs:802`) carry a complete antecedent set.
- The wrapper stops downgrading the flattened-path `Propagate`: it passes
  the outcome through with the now-complete `just` (`wordeq.rs:482`
  becomes a passthrough arm).
- Unit pins (leaf-level, not outcome-level) + dump-and-diff both suites +
  `script_e2e` + oracle-foreground gates (§4).

**Out of scope (banked, unchanged).**

- **The `Conflict → Saturated` downgrade** (`wordeq.rs:474`) stays. It is
  slice-33 vintage and has **no qualifying measured trigger** of its own
  — no recorded `decided → unknown` flip attributable to it. Lifting it
  is a separate future slice, un-banked only when its own dump-and-diff
  surfaces a cost worth buying back. Citing the strips makes the *inputs*
  to that lift available (the same enriched `just` reaches the Conflict
  report sites too), but this slice deliberately does not flip the arm:
  the Conflict `just` feeds a theory **conflict clause** directly, a
  strictly larger analyzability-guard surface than a Propagate merge, and
  it earns its own measured slice.
- `fresh_str` / word_norm `ite!` freshness regimes (slice 35 T2, slice 5):
  untouched.
- Standing bank unchanged: tracked skolem-TermId set, multi-atom
  variable-bearing propagation (slice-34 §10), `Split` passthrough audit,
  `Context::declare_fun` user→user conformance (slice-36 §2), slice-28 §8,
  slice-27 typed-antecedent refactor, slice-29 approach-C, slice-31 §11
  walls 1/2/4, the retracted wall-3 seam.

## 3. Mechanism — strip-explain, then lift on the flattened path

### 3a. The strip-explain pass

Today the strip loops call `same(terms, eq, a, b)` for the side-effect-free
boolean and discard *why* the pair matched. `same` returns `true` through
three doors: identical `TermId` (`wordeq.rs:408`), equal literal string
values (`wordeq.rs:411-413`), or same EUF class via `eq.are_equal`
(`wordeq.rs:414-416`). Only the **third** door involves a merge with an
antecedent that may be uncited. The first two are self-justifying (an
identity or a literal-value equality needs no leaf — mirroring
`nf_equal_explain`'s two `continue` guards at `wordeq.rs:228-236`).

The pass replaces the bare `same()` strip guard with a strip-explain
helper that, on a match through the EUF door, appends
`eq.explain(an, bn, &mut just)` — the identical call `nf_equal_explain`
makes at `wordeq.rs:241`. Concretely, `just` becomes `mut just` in
`resolve_inner`'s signature (`wordeq.rs:537`), and each of the two strip
loops (`wordeq.rs:546-549`, `551-555`) is rewritten to, per stripped pair,
determine the door taken and push explain leaves only for the EUF door.
The natural factoring is one small helper — call it `same_explain(terms,
eq, a, b, &mut just) -> bool` — that returns the same boolean `same` does
but has the `&mut Vec<EqLeaf>` side effect on the EUF branch; the strip
loops call it in place of `same`.

`eq.explain` is idempotent-safe to over-call (it appends the asserted-lit
antecedents of the merge path); duplicate leaves across multiple strips
are harmless to the downstream conflict/merge machinery (the SAT layer
dedups by var). No new terms are minted, no counter touched.

### 3b. Lift the flattened-path Propagate downgrade

With `just` now complete at both `Propagate` sites, the wrapper's
under-citation reason for the downgrade no longer holds. The `Propagate`
arm of the wrapper `match` (`wordeq.rs:482`) changes from
`StepResult::Propagate { .. } => StepResult::Saturated` to
`other @ StepResult::Propagate { .. } => other` (i.e. it folds into the
existing `other => other` passthrough — the arm is simply deleted). The
`Conflict` arm above it (`wordeq.rs:474`) is **unchanged**.

The wrapper's doc comment (`wordeq.rs:440-443`, item 3) is rewritten to
record that the Propagate is now passed through with a strip-cited `just`,
cross-referencing this spec and the slice-35 trigger; item 2 (Conflict)
keeps its existing rationale with a note that its lift is separately
banked.

### 3c. Shared strip, both paths — the measured wrinkle

The strip loops live in `resolve_inner`, which serves **both** the
flattened path (via the wrapper) and the non-flattened path (the early
return at `wordeq.rs:466`, and every non-concat equation). So the
strip-explain enrichment grows the `just` on the **non-flattened**
`Propagate` too (the slice 33/34 single-var and var–var cases), even
though those cases already propagate and their *outcome* does not change.

This is **sound** unconditionally: citing additional *true* antecedents of
a merge never makes a valid inference invalid. The residual risk is
purely the **analyzability guard** (`crates/shinri-sat/src/solver.rs:294`,
`theory_conflict_analyzable`): a `Propagate` merge tagged `Interface` can
later surface inside a theory **conflict clause** when its class collides
with a disequality, and the guard bails the *entire* conflict (a `bail`,
degrading to `Unknown`) if any cited var is out of the SAT solver's range
or sits above the current decision level. Over-citing a strip could — in
principle — drag a higher-level or wider-provenance leaf into a conflict
core that was analyzable before.

The decision (adjudicated in brainstorming): keep the strip-explain
**shared** — one implementation, not a flattened-path-only fork — and
**measure** the non-flattened path for regressions in the §4 gates rather
than dodge it with a parallel code path. The gates already have to watch
both suites regardless; a `bail` increase or a new disagreement on either
path is the halt-and-adjudicate tripwire (§4). If the shared pass ever
trips the guard on a non-flattened case, the confined-fork fallback (grow
only the flattened-path `just`) is the pre-costed remediation — recorded
here so a follow-up starts from the measurement, not from scratch.

## 4. Testing and gates

### 4a. Unit pins (`crates/shinri-str/src/wordeq.rs` tests)

- **Leaf-level, not outcome-level.** A flattened-rep equation whose strip
  consumes a pair through the EUF door (set up a merge `a ≈ b` via
  `eq.merge` (`eq_engine.rs:182`) on distinct non-literal TermIds, then a
  concat rep that flattens so the strip cancels `a` against `b`), driven
  to `Propagate`. Assert the returned `just` **contains the explain leaf**
  for that merge — not merely that the outcome is `Propagate`. This is the
  pin that would have caught a silent no-op citation.
- **Non-flattened invariance.** A pure assignment `v = W` with no EUF-door
  strip (all cancellations are `a == b` or literal-value): assert the
  `just` is byte-identical to the pre-slice-37 `just` (no spurious leaves
  from the self-justifying doors). Guards §3a's two-door `continue`.
- **Wrapper passthrough.** A flattened `Propagate` case now returns
  `Propagate`, not `Saturated` (the outcome the trigger hash needs),
  with the merge leaf present.
- Existing pins (`pure_assignment_propagates_*`, `alias_residual_*`,
  `flattened_*_does_not_propagate`, the skolem-residual fences) must all
  still pass — the last group in particular confirms the skolem exclusion
  (`is_minted_skolem`) is orthogonal to citation.

### 4b. Dump-and-diff, both suites

Per the DIFFDUMP discipline (`shinri-diffdump-nocapture` memory): run with
`--nocapture` and **verify the line count is non-zero before trusting the
diff** — a passing run swallows `eprintln` and reads as green at 0 lines.
Base = slice-36 HEAD (`acf1bea5`), fix = this slice.

- `qfs_differential` and the string e2e suite, base vs fix, sorted diff.
- **Expected:** source hash `8e950d0d36e258cb` (family
  `qfs_predicates_matches_z3`) flips **`unknown → sat`** and z3-agrees —
  the trigger cost bought back. The derived witness-check sub-query hash
  (`36069f2398aeda7e` in slice 35's record) reappears once the primary is
  `sat` again. Any *other* hash movement is enumerated and adjudicated.
- **Halt-and-adjudicate tripwires:** any new `sat ↔ unsat` disagreement
  against z3 (soundness — blocks), OR any `bail` count increase on either
  path (the analyzability-guard signal from §3c — blocks pending
  adjudication). A `decided → unknown` flip anywhere is also a block (this
  slice only buys completeness back, never spends it).

### 4c. Oracle + e2e + full gate

- **Oracle differential foreground**, captured output, with
  `--features oracle` — without the flag the suite silently runs 0 tests
  (`shinri-oracle-feature-gate` memory); a 0-test run is **not** green
  coverage. Confirm the test count is non-zero.
- **`script_e2e` locally pre-push** — completeness-shifting slice
  (`shinri-script-e2e-gate` memory). A z3-confirmed `unknown → sat` pin
  flip is an adjudicated flip, not a blocker; a `sat/unsat` disagreement
  is a blocker.
- Use nextest `-E 'test(name)'` filter form, not the positional
  `mod::name` form, and **confirm discovery** — a 0-test run reads as
  green (`shinri-nextest-filter-syntax` memory).
- Full gate: `cargo fmt --all -- --check` (CI fails fast on fmt —
  `shinri-ci-fmt-gate` memory), `cargo clippy --workspace --all-targets --
  -D warnings`, `cargo nextest run --workspace` within the 10–15 min
  blocking-tier budget.

## 5. Alternatives considered

- **Conditional lift, no citation** — track only *whether* any strip used
  the EUF door; if none did, the existing `just` is already complete, so
  lift the downgrade for exactly those cases. Zero over-citation risk, but
  it restores completeness only for syntactic-strip cases and we do not
  know a priori that the trigger hash is one of them; it also leaves the
  genuinely-EUF-consuming cases fenced forever. Rejected: does not
  discharge the trigger with confidence.
- **Cite + sanitize** — cite the strips and pass the enriched `just`
  through an arith-`sanitize_conflict`-style validator
  (`crates/shinri-arith/src/lib.rs` sanitizer shape) that drops
  unanalyzable leaves and falls back to `Saturated`. Most robust against
  the analyzability guard, but sanitizing `Interface` leaves at the string
  seam has no precedent and is a materially bigger slice than a
  single-hash trigger warrants. Rejected as over-scoped; held as the
  escalation if §4b shows a `bail` increase the shared pass cannot absorb.
- **Lift both downgrades** — restores more completeness in one slice but
  doubles the analyzability surface and lifts the Conflict arm with no
  qualifying trigger. Rejected per §2.

## 6. Files touched (anticipated)

- `crates/shinri-str/src/wordeq.rs` — `same_explain` helper; `mut just` +
  strip-explain in the two strip loops of `resolve_inner`; delete the
  `Propagate → Saturated` wrapper arm; doc-comment truth-up at
  `resolve_equation` items 2–3; new unit pins.
- No changes to `shinri-sat`, `shinri-theory`, or the solver crate are
  anticipated. If the §4b measurement forces the confined-fork fallback
  (§3c), that stays within `wordeq.rs` as well.

## 7. Success criteria

1. Trigger hash `8e950d0d36e258cb` answers `sat`, z3-agreeing, at fix.
2. Zero new `sat ↔ unsat` disagreements and zero `bail` increases on
   either path across both differential suites.
3. Zero `decided → unknown` flips introduced.
4. Full gate green within the blocking-tier budget; fmt/clippy clean.
5. The one lifted arm is the Propagate arm only; the Conflict downgrade is
   demonstrably untouched (its pins unchanged).
