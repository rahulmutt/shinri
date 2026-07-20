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
- Standing bank unchanged: slice-28 §8, slice-27 typed-antecedent refactor,
  slice-29 approach-C, slice-31 §11 walls 1/2/4, the retracted wall-3 seam.
