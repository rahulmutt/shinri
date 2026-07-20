# Slice 34 — alias propagation (var–var residual merge)

Date: 2026-07-20. Base: `17ef967e` (slice-33 merge).

## 1. Problem

After head/tail stripping, a word-equation residual `[v] = [u]` — one free
variable on each side, in distinct EUF classes — entails `v ≈ u` by
cancellation in the free monoid. Today that shape falls through to the
variable-headed F-split, hits the head-pair dedup, and returns `Saturated` →
a sound but needless `Unknown`.

Measured on the base tip (engine vs z3, both z3-`unsat`):

| Query | shinri | z3 |
|---|---|---|
| `(= (str.++ "a" x) (str.++ "a" y)) ∧ (distinct x y)` | `unknown` | `unsat` |
| `(= (str.++ x "a") (str.++ y "a")) ∧ (distinct x y)` | `unknown` | `unsat` |

Slice 33 landed the propagation outcome for the all-constant residual
(`StepResult::Propagate`, `wordeq.rs:625-682`) and explicitly deferred the
variable-bearing side "until the citation discipline here is proven"
(slice-33 §2). It is now proven: `explain` over trail-scoped prop tags,
`cited_lits` sweeping, the T5b `prop_merge_info` cond_roots fold-in, and the
§11.6 eager intra-check insertion all landed and are oracle-green (486/486).
This slice lifts the fence by exactly one step.

## 2. Scope

**In scope.** The alias shape: both residuals have length 1 and both atoms
are free variables — no `string_const_value`, and not a `StrConcat`
application (the existing `is_free_var` test at `wordeq.rs:653-655`).

**Out of scope (measured, then banked).** Multi-atom variable-bearing words
— `[v] = [u, "b"]` and kin. This is the deleted E1 probe's full shape; it
needs a CONCAT merge target, which reintroduces the normal-form dependency
slice-33 §3 deliberately avoided ("merging `var` against a multi-atom CONCAT
term would make the merge depend on that term's own normal form"). The slice
takes a probe-bank baseline of this shape (§7, probe B1) so the bank entry
carries a measurement, and stops there.

Also unchanged: the retracted wall-3 grounding seam, slice-31 §11 walls
1/2/4, the order preprocessing fence (stays **down**), and the standing bank.

## 3. Mechanism

One new case in the slice-33 pair-detection block (`wordeq.rs:660-666`):

- current: `l_res` single free var + `r_res` all-constant (either
  orientation) → fold constants, propagate `v ≈ W`;
- new: `l_res` and `r_res` BOTH single free variables → return
  `StepResult::Propagate { var: l_res[0], word: r_res[0], just }`.

Orientation is arbitrary — the EUF merge is symmetric — so the left residual
is `var`, fixed, for determinism. No constant folding runs; `word` is the
other variable's `TermId` unchanged.

**No occurs-check is needed for this shape, and the reason is structural,
not incidental.** Head/tail stripping (`wordeq.rs:468-477`) removes
same-class pairs via `same(terms, eq, ...)`, so a *surviving* residual
`[v] = [u]` proves `v` and `u` are in distinct EUF classes at resolution
time — the merge is never `v ≈ v`, and a one-atom variable side cannot
contain `v` any other way. (Contrast the multi-atom shape, where `v` can
occur inside the word — one of the two reasons it stays fenced.)

**Naming truth-up (ride-along).** The `Propagate` variant's doc comment and
the driver's "pure assignment" framing become "single-atom propagation".
The field name `word` stays — a single variable is a legitimate one-atom
word — but its doc no longer claims it is always a constant.

## 4. Citation

Inherited verbatim from slice 33; nothing new is built. The driver arm
(`lib.rs:890-976`) is shape-agnostic — it interns both `TermId`s and merges:

- `just` = `Asserted(lit)` + `nf_ante` (normal-form substitution
  antecedents, `lib.rs:900`), sorted/deduped, allocated as a prop tag. An
  alias residual whose heads stripped only via a prior merge is exactly the
  case `nf_ante` exists for.
- `StrSolver::explain` expands the tag; `cited_lits` sweeps it (slice-33
  T2/T3).

## 5. Soundness: what is new and what is inherited

Inherited, shape-agnostic (the spec relies on these, the plan re-verifies
none of them beyond the gates):

- **Branch-locality.** The merge is scoped by `EqualityEngine::push/pop`;
  the tag by the str trail. T5b records `(var, word, level)` in
  `prop_merge_info` for the check-entry cond_roots fold-in; the §11.6 Ok-arm
  insertion covers merges minted mid-invocation. Both operate on whatever
  two terms were merged.
- **No atom is minted and no clause is learnt**, so E1's clause gates have
  nothing to reject; the *tracking premise* (every string-leaf merge visible
  to cond_roots) is satisfied by the two mechanisms above.

New fact this slice must state and test:

- **A var–var merge creates a string class with NO constant member**, which
  slice-33 propagation merges never did. Model construction already handles
  constant-free string classes (a plain asserted `(= x y)` creates one
  today), so no model-path change is expected — but this is a claim about
  existing code, so §7's probe A3 (SAT control) pins it: the alias equation
  alone must stay `sat` with a self-check-passing model, never crash or
  flip.

## 6. Conflict path

When the merge unites a known-disequal pair — probe A1's `distinct x y` —
the existing `Err(conflict)` arm (`lib.rs:957+`) assembles the three-part
conflict (tag + diseq reason + congruence leaves), the same code slice-33
probes E/G exercised against constants. The alias probes exercise it
var-vs-var. No changes.

## 7. Acceptance (to be measured; predictions, not results)

| Probe | Query | Before (measured at base) | Predicted after |
|---|---|---|---|
| A1 | `"a"·x = "a"·y ∧ distinct x y` | `unknown` | `unsat` |
| A2 | `x·"a" = y·"a" ∧ distinct x y` | `unknown` | `unsat` |
| A3 | `"a"·x = "a"·y` alone (SAT control) | `sat` (z3: `sat`) | `sat` |
| A4 | chain `"a"·x = "a"·y ∧ "b"·y = "b"·z ∧ distinct x z` | `unknown` (z3: `unsat`) | `unsat` |
| B1 | `"a"·x = "a"·y·"b" ∧ distinct x (y·"b")` | `unknown` (z3: `unsat`) | `unknown` — banked shape, must NOT flip |
| Ctrl | slice-33 probes E/G/C/F/H | as pinned | unchanged |

Every `unknown → unsat` flip is z3-confirmed before the pin is written, and
mirrored as an oracle case in `qfs_differential.rs`. B1 doubles as the scope
fence's e2e witness: if it flips, the fence broke.

## 8. Testing

- **Unit (wordeq.rs):** alias residual → `Propagate` with the right
  endpoints; single-CONCAT-atom residual does NOT propagate; the slice-33
  fence test narrows from "variable-bearing word does not propagate" to
  "**multi-atom** variable-bearing word does not propagate" (its multi-atom
  case is unchanged).
- **e2e pins (`slice34_probes.rs`):** the §7 table, baseline first
  (measured T1), flips re-measured and adjudicated at the end.
- **Oracle:** `cargo nextest run -p shinri-solver --features oracle` with a
  **confirmed non-zero test count**; new `targeted_probe_a{1,2,4}_*` cases.
- **Oracle dump-and-diff (base vs fix):** every flip `unknown → decided`,
  zero `decided → unknown`, zero `sat ↔ unsat`, zero guard-bailout
  increases.
- **Full gates:** workspace nextest, `script_e2e` (pin flips adjudicated
  per the standing rule), `cargo clippy --workspace --all-targets -- -D
  warnings`, `cargo fmt --all` pre-push.

## 9. Risks

- **Chained aliasing** (`x≈y` then `y≈z` inside one check round): each
  propagation re-inserts its own post-merge root into both cond_roots sets
  (§11.6 behavior). Probe A4 pins the chain e2e.
- **Fence regression:** the narrowed unit test plus probe B1 pin the
  multi-atom shape at both tiers.
- **Verdict drift elsewhere** (the alias merge feeds classes other
  machinery reads — lengths, memberships): caught empirically by the
  dump-and-diff gate, as in slices 28/29/33.

## 10. Non-goals (banked)

- **Multi-atom variable-bearing propagation** — banked WITH the B1
  measurement (`unknown` at base, z3 `unsat`), so the future slice starts
  from data. Its two open designs: the CONCAT merge target's normal-form
  dependency, and the in-word occurs-check.

## 11. Outcome

This section records what actually happened, in the order it happened,
including a completeness regression that was caught, diagnosed, and fixed
mid-slice. Every value below is measured, not predicted.

### T1 — baseline (commit `6661b492`)

The §7 table's "before" column, measured directly against the branch base
(`17ef967e`), matched the prediction exactly: A1/A2/A4 → `unknown` (z3:
`unsat` for all three — the needless-incompleteness gap is real); A3 → `sat`
(control); B1 → `unknown` (z3: `unsat` — the banked multi-atom gap is also
real).

### T3 — alias propagation lands (commits `a8008dcc`, `ab717f1a`)

After the `resolve_inner` alias case landed and was pinned: A1, A2, A4 all
flipped `unknown → unsat`, each z3-confirmed **before** the pin was written.
A3 held `sat` (SAT control intact — a var–var merge creates a constant-free
string class and model construction still produces a self-check-passing
witness, confirming spec §5). B1 held `unknown` — the scope fence (§2, the
multi-atom variable-bearing shape) did not flip, confirmed at both the unit
tier (`skolem`-independent multi-atom fence test) and e2e (`probe_b1_multi_atom_fence`).
Oracle: the three new `targeted_probe_a{1,2,4}_*` cases were added to
`qfs_differential.rs`, 3/3 green. A3 has no oracle case of its own — it is
an e2e-only SAT control that lives solely in `slice34_probes.rs`; it was
never mirrored into `qfs_differential.rs`. (T4b, below, adds a fourth oracle
case, `targeted_probe_c1_charpeel_skolem_sat`, bringing the branch's total
oracle additions to 4: A1/A2/A4 here plus C1.)

### T4 first run — dump-and-diff CAUGHT a forbidden flip

Running the Step 1–4 dump-and-diff against `ab717f1a` (before the T4b fix)
surfaced a **forbidden** `sat → unknown` flip at hash `267be3752621a073`.
Minimized repro (`task-4-blocker-diagnosis.md`): a NEGATIVE (complement)
regex membership on `s2` combined with a literal-PREFIX concat
`s2 = "ab" ++ s0`. z3: `sat`, witness `s0 = ""`, `s2 = "ab"`.

Root cause: spec §3's implicit assumption — "any surviving var–var residual
is safe to merge, structurally guaranteed distinct-class by the stripping
step" — was **FALSIFIED** for a residual whose atoms are internal char-peel
skolems, not input variables. Peeling the literal head `"ab"` off `s2`'s
concat mints fresh remainders and eventually produces a residual
`[!strk1] = [!strk0]` — both atoms are minted skolems, and the slice-34
guard (shape-only: single free var each side) accepted it, propagating
`!strk1 ≈ !strk0` directly into EUF and **replacing the F-split** the model
builder needed. The model builder then resolved `s2`'s value through the
char-peel skolem concat (`t40 = "a" ++ !strk0`, `!strk0` free-filling to `""`
for zero class-length) instead of the anchoring original concat
(`t9 = "a"·"b"... = "ab" ++ s0`), producing a too-short value that
disagreed with `s2`'s class length; the length-consistency guard discarded
it and free-filled `s2` to a garbage value that failed the asserted
equation. The post-solve witness self-check correctly rejected that model
and downgraded `sat → unknown`. **The verdict was sound at every step** —
the bug was a lost decision (completeness regression), never an
unsoundness. Say this plainly: the slice-34 mechanism as first landed was
over-general, and the dump-and-diff gate that spec §8/§9 called for is
exactly what caught it before merge.

### T4b — fix (commit `4338040b`)

Fix: exclude minted `!strk*` skolems from the alias guard
(`is_minted_skolem`, a name-prefix check on the `fresh_str` branding
contract) — neither atom of the propagated pair may be a minted skolem; a
skolem-involving residual now falls through to the pre-existing F-split
path (exactly base behavior for that residual, no new merge, no new
citation/`cond_roots` concern). Regression pinned at three tiers: a unit
test (`skolem_skolem_residual_does_not_propagate`, both atoms named
`!strk*` exactly as `fresh_str` brands them, asserts the residual does NOT
propagate), an e2e probe (`probe_c1_charpeel_skolem_sat`, the minimized T4
repro, asserts `sat`), and an oracle case
(`targeted_probe_c1_charpeel_skolem_sat`). Reviewer-verified reasoning
(diagnosis doc, Option A): reduction-minted term families that DO carry
user-visible structure (`!pre`/`!mid`/`!post`/`!pfx`/`!sfx`/`!ctnl`/`!ctnr`/
`!ite`) are anchored like input variables and remain legitimately
propagatable — only `!strk` is minted purely as internal char-peel/F-split
bookkeeping during word-equation solving, and it is the only family excluded.

### T4 resumed — dump-and-diff against the FIXED code

Reused the base dump (`dump-base.txt`, 3901 `DIFFDUMP` lines from
`17ef967e` — unchanged, so no new worktree was needed) and re-dumped the
fix side against `4338040b` (90 tests, 0 failed — 89 pre-existing + the new
T4b oracle case; 3905 `DIFFDUMP` lines). Sorted diff, base vs fix:

```
283a284
> DIFFDUMP 1267c004253c1848 Some("sat") bail=0
333a335
> DIFFDUMP 14ff5e5dc4551055 Some("unsat") bail=0
3199a3202
> DIFFDUMP d0dc21629c9c905c Some("unsat") bail=0
3322a3326
> DIFFDUMP d9a3304b27bdcd35 Some("unsat") bail=0
```

**Final tally: exactly 4 lines of difference, all pure additions (0 lines
removed, 0 lines changed in place)** — the four new targeted test cases
(A1/A2/A4 from T3 + C1 from T4b), each a `src` string that literally does
not exist in the base test file. Zero hash-keyed flips of any direction on
shared cases: zero `decided → unknown`, zero `sat ↔ unsat`, zero bailout
increases. The invariant holds, with one notable and expected detail:
hash `267be3752621a073` (the forbidden-flip case) now reads `Some("sat")`
identically on **both** sides — the regression is fully closed, not merely
masked. Hash `74c5d57da2094bbc` (and its base-side bookkeeping companion
`c822a44df2057c87`), which showed an *allowed* `unknown → sat` flip in the
first (pre-fix) dump-and-diff run, now reads identically on both sides too
(`unknown`/`unknown` and `sat`/`sat` respectively) — it no longer appears
in the diff at all. That bonus win was itself a side effect of the
over-general (unfixed) alias guard firing on a skolem-involving residual
that happened not to corrupt that particular model; T4b's fix is a strict
narrowing back to base behavior on every skolem-involving residual, so this
incidental win reverted along with the regression. This is expected and
correct per Option A's design (a pure restriction of when `Propagate`
fires), not a new problem.

### Step 6 — completeness-shifting gate (`script_e2e`)

The plan's literal filter `test(script_e2e)` finds 0 tests on this nextest
version (a recorded harness gotcha); `-E 'binary(script_e2e)'` discovered
67 tests. Result: **67 passed, 1 skipped, 0 failed** — no pin flips at all,
so no adjudication was needed.

### Step 7 — full gate

- `cargo fmt --all -- --check`: clean.
- `cargo clippy --workspace --all-targets -- -D warnings`: clean, 0 warnings.
- `cargo nextest run --workspace`: **1131 passed, 0 failed, 7 skipped**
  (the `#[ignore]`d nightly-tier `shinri-fp` exhaustives, per
  `AGENTS.md`), ~265s.
- `cargo nextest run -p shinri-solver --features oracle`: **497 passed, 0
  failed, 3 skipped**, ~1175s. Non-zero confirmed (this count covers every
  oracle-gated binary in the crate — `qfs_differential`, `fp_oracle`,
  `qfabv_oracle`, etc. — not only the `qfs_differential` subset the plan's
  "~489" estimate was scoped to; the `qfs_differential` binary alone ran 90
  of these, matching the dump-and-diff run above).

### Fence and scope, final status

The scope fence held throughout: probe B1 (`unknown`, unchanged) and the
unit fence test (renamed from "variable-bearing does not propagate" to
"**multi-atom** variable-bearing does not propagate" per §3's naming
truth-up) both still pin the multi-atom shape as banked, untouched by this
slice. The dump-and-diff and full-gate results above are the drift check
called for in §9; no drift was found beyond the two expected additions/
reversions discussed above.

### Open

Multi-atom variable-bearing propagation remains banked exactly as §10
describes, now WITH the T1/T4 B1 measurement reconfirmed unchanged. Items
banked for future hardening, surfaced by this slice's own review:

- The skolem exclusion in `resolve_inner` is a **name-prefix check** on the
  `!strk` branding contract (`is_minted_skolem`), not a tracked-TermId set —
  documented as a heuristic in the fix's own comment (a false positive only
  narrows completeness, never introduces unsoundness, so this is safe but
  not maximally precise). A tracked set of minted skolem `TermId`s would be
  the principled version; noted as future hardening, not required for this
  slice.
- (Important, inherited from slice 33, empirically clean across 3901 dump
  hashes + 497 oracle tests) Uncited EUF-strip window for `Propagate` off
  wrapper-flattened words: when a class rep is itself a CONCAT, the wrapper
  structurally flattens it and inner atoms are never rep-substituted, so the
  strip loops (wordeq.rs ~506-515) can fire via `same()`'s `eq.are_equal`
  branch on a class equality cited in neither `just` nor `nf_ante`, so a tag
  reached through such a strip is under-cited — the wrapper downgrades
  `Conflict` for exactly this reason (~line 442) but passes `Propagate`
  through unguarded (wrong-UNSAT shape, narrow reachability). Candidate
  fixes: append `eq.explain(a,b)` leaves into `just` on EUF-branch strips, or
  downgrade `Propagate` off flattened words symmetrically with `Conflict`.
- (Minor, pre-existing) `fresh_str` freshness gap: it interns via
  `declare_fun` by name without `reserve_symbol`, so a user-declared
  `|!strk0|` hash-conses with a later-minted skolem — for the slice-34 guard
  this is the documented harmless false positive, but the minted-skolem-as-
  user-term collision is a standing freshness hazard; follow-up = reserve
  minted `!strk` symbols (mechanism exists for word_norm).

Standing bank unchanged: slice-28 §8, slice-27 typed-antecedent refactor,
slice-29 approach-C, slice-31 §11 walls 1/2/4, the retracted wall-3 seam.
