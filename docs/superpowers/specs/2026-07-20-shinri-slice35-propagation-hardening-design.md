# Slice 35 — propagation hardening (uncited-Propagate window + skolem freshness)

Date: 2026-07-20. Base: `dc718d8a` (slice-34 merge).

## 1. Problem

Two items from the slice-34 final-review bank, both soundness-shaped, both
small.

**(a) The uncited EUF-strip window for `Propagate` off wrapper-flattened
words** (marked *Important* in the slice-34 bank; inherited from slice 33).
When a word-equation side contains a concat CLASS REPRESENTATIVE, the
`resolve_equation` wrapper structurally flattens it
(`wordeq.rs:436-437`) and the flattened inner atoms are never
rep-substituted by `normal_form` — so the head/tail strip loops
(`wordeq.rs:506-515`) can consume an atom pair through `same()`'s
`eq.are_equal` branch (`wordeq.rs:388`) on a class equality cited in
**neither** `just` **nor** `nf_ante`. The wrapper downgrades `Conflict`
to `Saturated` for exactly this reason (`wordeq.rs:442`), but
`StepResult::Propagate` — added in slices 33/34 — passes through
unguarded. A `Propagate` whose residual was shaped by an uncited strip
lands an EUF merge with an incomplete justification; a later conflict
expanding through that merge under-cites its core. That is a wrong-UNSAT
shape, reachable (narrowly) today.

Empirical status: never observed firing — clean across the slice-34
dump-and-diff (3901 shared hashes) and the full oracle gate (497 tests).
This slice closes the window before slice-34 §10's multi-atom follow-up
widens `Propagate`'s reachability over exactly this path.

**(b) The `fresh_str` freshness gap** (minor, pre-existing).
`fresh_str` (`wordeq.rs:56-64`) interns `!strk<N>` via bare
`declare_fun`, with neither collision direction handled:

- a user-declared `|!strkN|` that predates minting hash-conses with the
  minted skolem — the minted-skolem-as-user-term hazard (the slice-34
  guard's documented false positive is the harmless face of this; the
  shared-TermId identity itself is the standing hazard);
- a user `declare-fun` of `|!strkN|` *after* minting hash-conses onto the
  skolem and inherits its internal identity — the same wrong-verdict shape
  word_norm's slice-5 final review found for `ite!` and fixed with
  `reserve_symbol` (`word_norm.rs:107-111`).

## 2. Scope

**In scope.**

- One new arm in the `resolve_equation` wrapper: `Propagate → Saturated`
  when flattening occurred (approach A below).
- `fresh_str` adopts the word_norm mint pattern (lookup-skip +
  `reserve_symbol`).

**Out of scope (banked).**

- **Approach B — cite the strips**: append `eq.explain(an, bn, &mut just)`
  leaves on every strip that consumed via the `eq.are_equal` branch
  (the API exists; `nf_equal_explain` at `wordeq.rs:191` is the shape).
  This is the completeness-*restoring* follow-up, to be taken only if the
  §5 dump-and-diff ever shows approach A costing a decided verdict. It
  touches the strip loops shared by every outcome, and the wrapper's own
  doc (`wordeq.rs:406-410`) records that threading merge antecedents into
  this path over-approximates and trips the SAT conflict-analyzability
  guard — it needs its own measured slice.
- **Tracked skolem-TermId set** replacing the `is_minted_skolem`
  name-prefix heuristic. With §3b landed, the only residual false positive
  is a user `|!strkN|` declared *before* any minting — completeness-
  narrowing, never unsound. Stays banked.
- **Multi-atom variable-bearing propagation** (slice-34 §10): untouched;
  probe B1 stays `unknown`.
- Standing bank unchanged: slice-28 §8, slice-27 typed-antecedent
  refactor, slice-29 approach-C, slice-31 §11 walls 1/2/4, the retracted
  wall-3 seam.

## 3. Mechanism

### 3a. Symmetric downgrade (approach A)

One new arm in the wrapper match (`wordeq.rs:438-444`), firing only on the
`had_concat_atom` path:

```rust
match resolve_inner(/* flattened words */) {
    // A conflict off a flattened concat rep would be under-cited → Saturate.
    StepResult::Conflict(_) => StepResult::Saturated,
    // A Propagate off a flattened concat rep is under-cited the same way:
    // its residual may have been shaped by an eq.are_equal strip cited in
    // neither `just` nor `nf_ante`, so the EUF merge it would land is
    // under-justified (wrong-UNSAT shape). Saturate, symmetrically.
    StepResult::Propagate { .. } => StepResult::Saturated,
    other => other,
}
```

`Done`, `Saturated`, and `Split` pass through unchanged — `Split`'s
learnt clause is guarded by `¬eqn` and predates `Propagate`; its regime is
untouched by this slice. Words with no concat atom never enter the wrapper
path (`wordeq.rs:433-435`), so slice-33/34 propagation over normal words
is unaffected.

This is a pure restriction of when `Propagate` fires — the identical
soundness argument the `Conflict` arm already carries (and the same shape
as slice-34's T4b skolem exclusion). It can lose completeness, never
soundness; §5 measures the loss (expected zero).

**Alternatives rejected.** Approach B (cite the strips — banked, see §2)
and approach C (thread a "did any strip consume via non-identity
`eq.are_equal`?" flag out of the strip loops and downgrade only then).
C is more precise than A but adds plumbing through `same()` and the strips
for a window never observed firing, and still loses the cases B would
save. A's one-arm change with the free soundness argument wins.

### 3b. `fresh_str` freshness

Adopt the `word_norm.rs:100-117` mint pattern verbatim:

```rust
pub fn fresh_str(terms: &mut Context, ctr: &mut u32) -> TermId {
    let str_s = terms.string_sort();
    loop {
        let name = format!("!strk{}", *ctr);
        *ctr += 1;
        if terms.lookup_symbol(&name).is_some() {
            continue; // user (or an earlier check) owns this name
        }
        let sym = terms.declare_fun(&name, &[], str_s);
        terms.reserve_symbol(sym);
        return terms.mk_app(Op::Uninterpreted(sym), &[]).expect("well-sorted");
    }
}
```

- The `lookup_symbol` skip closes the pre-mint direction: a user-declared
  `|!strkN|` is never adopted as a skolem; the counter bumps past it.
- `reserve_symbol` closes the post-mint direction: a later user
  `declare-fun` of the minted name is rejected at parse time, exactly as
  for `ite!` names.
  > **Slice-35-measured correction (see §6):** this claim is
  > architecturally FALSE for `fresh_str` mints reached via
  > `Solver::check_sat`. `check_sat` clones `self.ctx` into the theory
  > Combiner *before* search (`lib.rs:711`); `fresh_str`'s mint +
  > `reserve_symbol` run inside that discarded clone, so the reservation
  > never reaches the parser-visible context. A post-mint
  > `declare-const !strk0` is accepted, not rejected. `word_norm`'s
  > `ite!` regime is unaffected because it mints on `self.ctx`
  > pre-clone (`lib.rs:384`). The hazard is still closed by other means
  > — see §6 for the full mechanism and adjudication.
- The `!strk` BRANDING CONTRACT with `is_minted_skolem` is unchanged; the
  doc comments on both (`wordeq.rs:52-55`, `wordeq.rs:66-81`) are updated
  to note the freshness guarantee and the narrowed false-positive story
  (pre-declared user `|!strkN|` only, and such a term is now never also a
  skolem).

`fresh_str` is the single skolem mint for the str theory (char-peel,
F-split, order_engine, memb all route through it), so both fixes land at
one site.

## 4. Testing

**Unit (`wordeq.rs`).**

- A word equation with a concat class-rep atom whose flattened residual is
  a pure assignment (and an alias variant) returns `Saturated`, not
  `Propagate`.
- Control: the same residual shape with no concat atom still returns
  `Propagate` — slices 33/34 behavior pinned.
- `fresh_str` with `|!strk0|` pre-declared: mint skips to `!strk1`,
  TermIds distinct from the user term.
- Post-mint re-declaration of a minted `!strk` name is rejected — mirror
  the two `ite!` reservation cases in `script_e2e.rs:118-166` (post-mint
  declaration rejected with the "reserved for solver-internal use" error;
  pre-declared name stays a usable free constant and the script stays
  SAT).
  > **Slice-35-measured correction (see §6):** FALSIFIED for the
  > post-mint case. The actual e2e test is
  > `post_mint_declaration_of_strk_name_is_accepted_no_aliasing` — both
  > verdicts `unknown`, z3-sat-confirmed, no error. The pre-declared-name
  > case (`user_strk_name_declared_before_any_mint_still_works`) is
  > unaffected and passes as designed. Human-adjudicated: pin real
  > behavior rather than the spec's assumption.

**e2e pins.** Slice-33 probes (C/E/G/F/H) and slice-34 probes (A1–A4, B1)
all read unchanged — the downgrade must not touch non-flattened
propagation, and B1 stays `unknown`.

**Gates** (in order):

- `cargo nextest run -p shinri-solver --features oracle` with a
  **confirmed non-zero test count**.
- **Oracle dump-and-diff, base vs fix**: expected **zero** verdict
  changes — the window has never been observed firing. Any
  `decided → unknown` is approach A's measured completeness cost: record
  it in the truth-up, adjudicate, and it becomes the trigger for
  un-banking approach B. Run with `--nocapture` and verify the dump line
  count is non-zero before trusting the diff.
- `script_e2e` locally, filtered with `-E 'binary(script_e2e)'` (the
  positional filter finds 0 tests on nextest 0.9.140). z3-confirmed
  `unknown → decided` flips are adjudicated, not blockers; none expected
  here.
- `cargo fmt --all -- --check`, `cargo clippy --workspace --all-targets
  -- -D warnings`, `cargo nextest run --workspace`.

## 5. Risks

- **Completeness regression from the downgrade**: bounded by the
  dump-and-diff gate; expected zero (3901-hash + 497-oracle-test empirical
  cleanliness of the window). Adjudicated flips route to approach B.
- **Counter-skip behavioral drift** (`fresh_str` now bumps past user-owned
  names): skolem names are internal; no test may pin a specific `!strkN`
  spelling against a query that also declares one. The workspace gate
  catches any accidental pin.
- **Parse-time rejection surprises**: a user file that declares
  `|!strkN|` *after* solving has begun now errors instead of silently
  aliasing a skolem. This is the fix, not a regression (identical to the
  `ite!` regime), and such inputs are already outside any documented
  contract.
  > **Slice-35-measured correction (see §6):** FALSIFIED — no parse-time
  > error occurs post-mint; `check_sat`'s pre-search context clone
  > (`lib.rs:711`) discards the mint-time `reserve_symbol` before the
  > parser ever sees it. No "surprise" rejection ships in this slice.
  > The hazard this bullet worried about is closed by clone isolation
  > instead (the skolem never exists in the parser-visible context) plus
  > the Task-2 lookup-skip (no pre-mint adoption on the next solve).

## 6. Outcome

Measured, in gate order. Task commits: `e9264cae` (T1, downgrade),
`4cb491c9` (T2, `fresh_str` freshness), `b7ff6cb1` (T3, e2e pins).

**Unit fences (T1).** Two new `wordeq.rs` unit tests (TDD red → green: a
concat-class-rep residual returns `Saturated` not `Propagate`, plus an
alias variant; control case with no concat atom still returns
`Propagate`, pinning slice-33/34 behavior). `shinri-solver` crate suite:
228/228 after T1.

**`fresh_str` freshness (T2).** Two new unit tests (pre-declared
`|!strk0|` skips the mint to `!strk1` with distinct `TermId`s; post-mint
re-declaration rejected via `reserve_symbol`, mirroring the `ite!`
cases). Crate suite: 230/230 after T2.

**e2e pins (T3).** Both new `script_e2e` pins measured `unknown`/`unknown`
verdicts, z3-sat-confirmed on both scripts, no error either way. Per the
§3b/§5 truth-up above, the post-mint case is `unknown` — not rejected at
parse time — because `check_sat`'s pre-search `self.ctx` clone
(`lib.rs:711`) discards the mint's `reserve_symbol` before the parser
ever observes it; `word_norm`'s `ite!` mint avoids this because it runs
on `self.ctx` pre-clone (`lib.rs:384`). Human-adjudicated (Option A): pin
the real, architecturally-explained behavior rather than rewrite it to
match the spec's (false) assumption. The hazard §1b worried about
(minted-skolem identity aliasing a later user term) is still closed:
clone isolation makes post-mint aliasing impossible (the skolem never
exists in the parser-visible context the user's `declare-const` runs
against), and the Task-2 lookup-skip prevents pre-mint adoption on the
solve after that. `reserve_symbol` is retained as unit-level
defense-in-depth against a future refactor of the clone discipline, not
as the mechanism that currently protects the e2e case. Slice-33/34 probe
regression gate (Task-4 script_e2e run, folded into the count below):
80 passed / 1 skipped, `B1` held `unknown` as expected.

**Oracle gate (Step 1).** `cargo nextest run -p shinri-solver --features
oracle`: **499 passed, 0 failed, 3 skipped**, confirmed non-zero,
~1202 s (~20 min). (The slice-34 baseline quoted 497 passed; this
slice's own 2 new e2e pins land in the `script_e2e` binary, not the
oracle-gated suites, so the +2 is pre-existing drift between slice-34's
measurement and this run, not new-in-this-slice tests. Not a concern.)

**Dump-and-diff (Steps 2–6), base `6fc62643` vs fix `b7ff6cb1`.** Both
runs required `--nocapture` (the first fix-side attempt without it
produced 0 `DIFFDUMP` lines — the harness swallows `eprintln!` on
passing tests — re-run per the known gotcha before trusting any count).

- Base side: 3905 `DIFFDUMP` lines, 90/90 tests passed.
- Fix side: 3904 `DIFFDUMP` lines, 90/90 tests passed.
- Sorted diff (`base-sorted.txt` vs `fix-sorted.txt`): **not empty** —
  two lines differ, both explained by one underlying case:
  - `DIFFDUMP 8e950d0d36e258cb Some("sat")` (base) →
    `DIFFDUMP 8e950d0d36e258cb Some("unknown")` (fix) — a **decided →
    unknown** flip. Same source hash both sides (deterministic LCG
    seeds), so this is the identical query deciding differently under
    the T1 downgrade.
  - `DIFFDUMP 36069f2398aeda7e Some("sat")` present only at base,
    absent at fix — this is the derived witness-check sub-query for the
    same case (`qfs_predicates_matches_z3` only re-solves a
    model-substituted script when the primary verdict is `Sat`); once
    the primary verdict became `unknown` at fix, the witness check never
    ran, so its hash simply never appears. Not a second flip.
  - Family: `qfs_predicates_matches_z3` (the flip is visible directly in
    that test's own printed tally — base `35 sat / 96 shinri-unknown`,
    fix `34 sat / 97 shinri-unknown`; re-run in isolation on the fix side
    reproduced `34 sat / 97 shinri-unknown` exactly, confirming
    determinism, not flakiness).
  - No `sat ↔ unsat` disagreement (both commits report `0 disagreements`
    against z3 for this family) and no bailout increase (`bail=0` both
    sides) — this is **not** a soundness regression. It is exactly the
    completeness cost spec §4/§5 anticipated and gave an escape valve
    for: *"any `decided → unknown` is approach A's measured completeness
    cost: record it in the truth-up, adjudicate, and it becomes the
    trigger for un-banking approach B."*
  - **Adjudication status: RESOLVED — accepted, merge as-is.** The human
    partner accepted the single-hash completeness cost: soundness is
    intact (no `sat ↔ unsat` disagreement, clean z3 agreement) and the
    cost is 1 of ~3900 hashes. The flip stands as the recorded trigger
    for un-banking approach B (§2) in a future slice — it is not
    un-banked by this decision, only logged as the qualifying event.

Instrumentation reverted (`git checkout --
crates/shinri-solver/tests/qfs_differential.rs`) and the base worktree
removed (`git worktree remove --force`) before proceeding; working tree
confirmed clean.

**`script_e2e` gate (Step 7).** `cargo nextest run -p shinri-solver -E
'binary(script_e2e)'`: **69 tests run, 69 passed, 1 skipped** (67 prior +
2 new pins; the skip is pre-existing and unrelated to this slice). No
`decided → unknown` or `sat`/`unsat` disagreement.

**Full gate (Step 8).** `cargo fmt --all -- --check`: clean.
`cargo clippy --workspace --all-targets -- -D warnings`: 0 warnings.
`cargo nextest run --workspace`: **1138 passed, 0 failed, 7 skipped**
(the `#[ignore]`d nightly `shinri-fp` exhaustives), ~268 s (~4.5 min).

**Net.** T1–T3 are soundness-neutral-or-better and gate-green everywhere
except the one measured completeness cost above, which is a known,
anticipated, non-blocking-by-design-but-adjudication-gated outcome per
this spec's own §4/§5 language. The §3b architecture-truth correction is
independent of that cost and does not change the hazard-closed
conclusion (see the inline notes at §3b/§4/§5 above). **Adjudicated:**
the human partner accepted the single-hash completeness cost as-is
(soundness intact, z3 agreement clean, 1 of ~3900 hashes); it stands as
the recorded un-banking trigger for approach B (§2). Cleared to merge.
