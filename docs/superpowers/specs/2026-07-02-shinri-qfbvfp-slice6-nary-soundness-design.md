# shinri QF_BVFP — Slice 6: n-ary `=` soundness closure + carried minors

**Date:** 2026-07-02
**Status:** Landed 2026-07-02 (commits 22d75fb..HEAD, 9 tasks incl. controller-run
pre-flight). Verification: full `cargo test --workspace` green (30 suite results, 0
failed, incl. shinri-fp 86/86 @2079s); full differential oracle green — all pre-existing
suite counts byte-identical to the slice-5 baseline, NEW `differential_qf_uf_nary`
sat=68 unsat=132 unknown=0 z3_checked=200/200 zero disagreements; clippy net-new zero
(solver=2/fp=22/parser=3/theory=4/str=9 = slice-5 known set); canary sweep clean.
**Pre-flight corrections to §2 (evidence: slice-6 ledger):** (a) n-ary `=` over
**String** was a THIRD live wrong-SAT (routes to EUF, same dropping arm; also a
user-reachable debug-build panic at euf/solver.rs:114). **Narrowed by the final
review:** only the **variable-only** n-ary String `=` is fixed by the expansion
and pinned `unsat`. **Compound-term** cases (operands like `(str.++ si "a")`)
stayed wrong-SAT until the slice-6 final-review C1 fix: word_norm wraps the
expansion in `(and …)`, which the string model self-check skipped — now it
descends positive top-level `And` chains and downgrades to a sound `unknown`
(z3-verified: repro `(= (str.++ s3 "a") (str.++ s1 "b") (str.++ s3 "b"))` is
unsat; shinri no longer answers sat). **Negated n-ary String `distinct`** is
still wrong (filed follow-up I1 below); (b) **Array** n-ary `=` was already CORRECT — arrays over BV route
to the ABV path whose own `normalize.rs` pre-pass expands n-ary array atoms (spec's
extensionality-fence assumption was wrong for ABV-routable queries) — pinned as the
decided pair, and that pass is now dead-but-harmless for n-ary shapes since word_norm
expands first. All four minors landed: ABV bare-Bool exemption (slice-5 canary flipped
to decided pair, z3-verified), RM get-model values (one-hot decode channel), get-value
through eliminated ites (BV/FP/RM, get-model output unchanged), 0-ary define-fun
bare-symbol expansion (let → macro → fun order).
**Follow-ups filed (pre-existing-shaped, out of scope):** nested-ite `get-value` on the
OUTER term still degrades to sound `?` (word_norm's `ite_var` is keyed by the
child-rewritten term; the query term hash-conses the original child — completeness
gap, no wrong value, no name leak); the QF_ABV path lacks the eliminated-ite get-value
channel entirely (same degrade-to-`?`).
**Follow-ups filed by the slice-6 FINAL REVIEW (pre-existing-shaped, out of scope):**
- **C2 — negated arith n-ary `=` wrong-SAT** (pre-existing at base): `lower()`'s
  binary `Not(Eq)` pure-arith special case (`lib.rs:936`) does not fire on eqs
  nested under `Not(And(...))` (see §3 CORRECTED note). Repro
  `(not (= x y z)) ∧ x≤y ∧ x≥y ∧ y≤z ∧ y≥z` → shinri sat, z3 unsat. Candidate
  fix: eq ↔ (le ∧ ge) linking clauses, or descend `Not(And)` in that special case.
- **I1 — negated n-ary String `distinct` wrong-UNSAT** (pre-existing string-theory
  defect): `(not (distinct s1 s2 s2)) ∧ (= s2 s1) ∧ (= s1 (str.++ s3 "ab"))` →
  shinri unsat, z3 sat.
- **I2 — debug-build panic** `"returned SAT but a clause is unsatisfied"`
  (`shinri-sat/src/solver.rs:553`) on the premature-SAT family, e.g.
  `(not (= s1 s2 s3)) ∧ (= s1 "a")`; TermId-layout-sensitive. A sibling
  debug-assert `"explain: a,b not connected"` (`shinri-theory/src/eq_engine.rs:366`)
  fires from the same string/eq premature-SAT family (surfaced by the new
  `differential_qf_s_nary` corpus; its seed is chosen to skirt both). Debug-only;
  release builds return a verdict.
**Plan:** 5 (post-Plan-4 completeness & robustness), second slice — the slice-5 final
review's filed follow-ups (wrong-SAT Imp#2 + carried minors Min#4/#5/#6 + parser gap)
**Predecessors:** slice 5 (`word_norm` pass, whose final review filed all of this)
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md`

## 1. Goal & Scope

Close every known-wrong verdict left open after slice 5, and sweep in the four
carried minors. **No new FP surface** — this is a soundness/conformance slice.

In scope:

1. **Wrong-SAT fix (core):** n-ary `=` over **Bool** and over **uninterpreted
   sorts** — both z3-confirmed live at slice-5 final review.
2. **Carried minors:** ABV bare-Bool fence-exemption port; RM model extraction;
   `get-value` leaking internal `ite!<n>` names; parser 0-ary `define-fun`
   bare-symbol expansion.

Out of scope (§8): the Real bridge (v2), fp.div circuit depth/performance, new
FP ops, incremental-solving features.

## 2. The defect, precisely

Verified against the working tree at 784f719. The n-ary `=`/`distinct`
normalization surface is split across three sites with a coverage hole:

| Site | What it expands today | Hole |
|---|---|---|
| `lower()` (`shinri-solver/src/lib.rs:847`) | n-ary `=` chained **only when arith-sorted** (adds Le/Ge companions) | Bool/UF/Array/String `=` passes through as `t` |
| `lower()` (`lib.rs:916`) | n-ary `distinct` expanded pairwise **for all sorts** | none — this is why n-ary Bool `distinct` is fine |
| `word_norm` (`shinri-solver/src/word_norm.rs:137-169`) | n-ary `=` and `distinct` over **word sorts only** (BitVec/Float/RM, `is_word_sort` gate at :44) | Bool/UF/Array/String `=` walks past |

An unexpanded n-ary `=` then reaches one of two dropping consumers:

- **Bool:** `tseitin.rs:141-147` encodes `(= p q r)` as `p ↔ q` — kids[2..]
  silently dropped. Repro: `(= p q r) ∧ p ∧ q ∧ ¬r` → shinri **sat**, z3 unsat.
- **Uninterpreted sorts:** `shinri-euf/src/solver.rs:69-71` (`new_var`)
  registers only `kids[0], kids[1]` as the eq atom. Repro: `(= a b d) ∧
  (distinct a d)` over sort U → shinri **sat**, z3 unsat. Notably the EUF
  `assert` path (`solver.rs:114`) already `debug_assert!`s "Eq atom must be
  binary" — the invariant is stated but unenforced upstream.
- **String:** n-ary String `=` routes to `Owner::String` (`shinri-theory/src/
  atom.rs`) — untested against z3; the pre-flight (§5) diffs it.
- **Array:** array-to-array `=`/`distinct` is extensionality-fenced to
  `Unsupported` → sound Unknown (`atom.rs:27-41`). Not wrong today; the
  pre-flight confirms.

## 3. Core fix — sort-universal n-ary expansion in `word_norm` (Approach A)

Delete the `is_word_sort` conjunct from **both n-ary arms** of `word_norm`
(`word_norm.rs:138` and `:152`). The expansion is pure, polarity-independent
term rewriting — adjacent chain for `=`, all-pairs for `distinct` — valid at
every sort. After the change, every sort (Bool, uninterpreted, Array, String,
Int, Real, and the word sorts) is expanded **before any stage sees the term**.

The **ite-elimination arm keeps its word-sort gate unchanged** — fresh-var
minting stays scoped to BitVec/Float/RM; Bool `ite` is tseitin-native and the
arith/array/string `ite` paths are untouched by this slice.

**New structural invariant:** downstream of `word_norm`, no `=`/`distinct`
node has arity > 2. This converts the per-sort audit into a guarantee.

Interactions, considered:

- **Arith redundancy:** `word_norm` runs first (slice 5); `lower()` now
  receives pre-chained binary arith `=` and still adds its Le/Ge companions
  per pair — semantically identical output, but term shapes shift, so the
  full-net baseline check applies (§6). `lower()`'s own n-ary arms become
  effectively dead but are left in place as defense in depth.
- **Not-wrapped forms (CORRECTED — final review):** the expansion
  `(not (= a b c))` → `(not (and (= a b) (= b c)))` IS equivalence-preserving,
  but `lower()`'s binary `Not(Eq)` pure-arith special case (`lib.rs:936`) does
  NOT fire on eqs nested under `Not(And(...))` — it only matches a bare
  top-level `Not(Eq(_,_))`. So **negated n-ary arith `=` is wrong-SAT**
  (pre-existing at base, surfaced by the final review; repro
  `(not (= x y z)) ∧ x≤y ∧ x≥y ∧ y≤z ∧ y≥z` → shinri sat, z3 unsat). Filed as
  follow-up C2 in the Status block (candidate fix: eq ↔ (le ∧ ge) linking
  clauses, or descend Not(And) in the pure-arith special case).
- **Array `=`:** binary array equalities remain extensionality-fenced →
  verdicts unchanged (sound Unknown), no fence lift in this slice.

Alternatives rejected: **(B)** fixing each consumer arm in place (tseitin
iff-fold + EUF n-ary registration) — multiple fix sites, and any future
consumer re-inherits the bug, which is exactly how this family survived slice
5; **(C)** expanding in `lower()` — touches the shared arith chaining path,
largest blast radius for no added benefit over A.

## 4. Pin the old dropping arms

Once §3 makes >2-ary `=` unreachable downstream:

- `tseitin.rs:141` (Bool-Eq iff arm): add `debug_assert_eq!(kids.len(), 2)`.
- `shinri-euf/src/solver.rs:69` (`new_var` Eq arm): add the same assert,
  matching the one already in `assert` at `:114`.

Any future bypass path fails loudly in debug/test builds instead of silently
dropping operands.

## 5. Pre-flight (front-loaded, per the cross-slice canary lesson)

Before writing code:

1. **z3-diff n-ary `=` (and `distinct`) over Array and String sorts** to learn
   whether current verdicts are wrong (→ the fix's e2e tests are "fixes") or
   sound (→ they are "pins").
2. **Canary grep** for tests pinning old behavior: the `script_e2e` ABV
   bare-Bool sound-Unknown pin (flipped by Min#4 below), and any test
   asserting n-ary `=` verdicts or arith term shapes that §3 perturbs.

## 6. Carried minors (independent tasks)

1. **ABV bare-Bool exemption port (Min#4):** port `fp_stage`'s bare-Bool-
   condition fence exemption to `abv_stage`, so an ABV `ite` with a bare-Bool
   condition decides instead of fencing. Flip the pinned sound-Unknown canary
   in `script_e2e` to a decided-verdict pair.
2. **RM model extraction (Min#5):** RM variables currently get no value in
   `get-model` (visible since slice 5 routed RM to the FP path). Extract the
   assignment from the FP path's `rm` one-hot selector bits and render the RM
   literal (`RNE`/`RNA`/`RTP`/`RTN`/`RTZ`), extending `ModelVal` as needed.
3. **`get-value` through eliminated ites (Min#6):** `get-value` on a term whose
   word-`ite` was eliminated leaks the internal `ite!<n>` name. Fix by
   evaluating through the stored ite definition (the `w = (ite c x y)`
   defining assertion) at model-query time, so reserved names never surface
   to the user. (Substituting definitions back into the term is the fallback
   only if definition-directed evaluation proves infeasible in the model
   layer.)
4. **0-ary `define-fun` bare-symbol expansion:** the parser expands `(one)`
   but not bare `one` for a 0-ary macro. Fix bare-symbol resolution to consult
   the macro table (`lookup_macro`) before treating a name as a declared
   constant. SMT-LIB conformance.

## 7. Testing

- **e2e repros:** the four z3-confirmed wrong-SAT cases from the slice-5
  ledger, asserting corrected verdicts, each with a SAT twin.
- **Oracle extension:** a new differential-z3 family for n-ary `=`/`distinct`
  over Bool + uninterpreted sorts (plus Array/String shapes if the §5 diff
  shows them reachable), following the slice-5 oracle pattern: seeded Lcg,
  hard-assert `unknown == 0` where the surface is total and zero z3
  disagreements.
- **Unit:** `word_norm` expansion tests for the newly covered sorts, mirroring
  the existing word-sort tests; per-minor unit/e2e as fits (RM `get-model`
  probe, `get-value` ite probe, 0-ary macro parse test, ABV decided pair).
- **Net:** full `cargo test --workspace` + full differential-oracle baseline
  run in background (run directly, not via subagents — multi-minute suites).
  Pre-existing suite counts must match the slice-5 baseline byte-identically
  **except** deliberately flipped canaries, each named in the implementation
  plan (known: the ABV bare-Bool Unknown pin).
- **Clippy:** net-new zero against the slice-5 known set.

## 8. Non-goals

- `fp.to_real` / symbolic-Real `to_fp` (the permanent v1 Real bridge — v2).
- Array extensionality (`=`/`distinct` over Array stays soundly fenced).
- fp.div / deep-circuit SAT recursion performance.
- New FP operations or incremental-solving features.
