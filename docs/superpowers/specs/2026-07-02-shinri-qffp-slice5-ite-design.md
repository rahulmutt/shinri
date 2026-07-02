# shinri QF_BVFP — Slice 5: word-level `ite` (BV / FP / RM)

**Date:** 2026-07-02
**Status:** Landed 2026-07-02 (commits 0fb8218..HEAD, 8 tasks). Verification: full
`cargo test --workspace` green (all suites 0-failed incl. shinri-fp exhaustive, solver
non-oracle net, fp_e2e 75, qfbv_witnesses 33, shinri-bv 98); full differential z3 oracle
15/15 zero-disagreement — all 14 pre-existing suite counts byte-identical to the 4e
baseline, new `differential_qf_bvfp_ite` sat=128 unsat=72 unknown=0 z3_checked=200/200;
clippy net-new zero; canary sweep clean (remaining e2e Unknown pins are all Real-bridge).
All six confirmed repros fixed and pinned: R1 BV-ite panic → sat, R2-R5 n-ary =/distinct
wrong-SATs → unsat, R6 RM/EUF pigeonhole wrong-SAT → unsat, each with SAT twins. Bonus
fix folded in (Task 3, reviewer-verified sound): pre-existing fence gap that sent bare
declared Bool constants mixed with BV/FP content to Unknown.
**Plan:** 5 (post-Plan-4 completeness & robustness), first slice — the 4e final
review's filed follow-up (user-reachable `unreachable!` on BV-sorted `ite`,
`crates/shinri-bv/src/blast/mod.rs:430`)
**Predecessors:** slice 4a (unified `Lowerer`), 4b (mixed fence-lift), 4e
(FP→BV, whose final review filed this)
**Parent design:** `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md`

## 1. Goal & Scope

Admit `(ite c x y)` where the branches are **BitVec-, Float-, or
RoundingMode-sorted**, with an **unrestricted Bool condition** (arbitrary
connectives, nested BV/FP atoms, Bool variables shared with the skeleton,
Bool-sorted `ite`). Today this shape is:

- a **user-reachable panic** on the BV path — `(= (ite c x y) z)` passes every
  fence (the enclosing atom is a leaf in every walk) and hits the
  `_ => unreachable!("non-BV builtin reached blast_word")` catch-all;
- a **sound `Unknown`** on the FP path (`fp_atoms_fully_supported` /
  `is_supported_fp_word` positively enumerate ops; `ite` is not among them);
- a **sound `Unknown`** for RM operands (`is_rounding_mode_term` accepts only
  RM literals and nullary RM variables).

Design-time review also surfaced a fourth, adjacent defect — a
**pre-existing wrong-SAT soundness bug**, empirically confirmed 2026-07-02:
`(declare-const r RoundingMode) (assert (distinct r RNE RNA RTP RTN RTZ))`
answers `sat` (z3: `unsat` — RoundingMode has exactly 5 values). Cause:
`solver_uses_fp`'s `is_fp_sorted` matches only `Float(_,_)`, so an RM-only
script never enters the FP path; the RM (dis)equality falls through to
`classify_equality` → `Owner::Euf`, and EUF treats RoundingMode as an
unbounded uninterpreted sort. The RM-equality admission this slice already
needs (§5) is also the fix, so it is pulled into scope.

Plan-time pre-flight (2026-07-02) then confirmed a further **wrong-SAT
family** in the same seam: **n-ary `=` and n-ary `distinct` over BV and FP
operands**. Four repros, all `sat` from shinri / `unsat` from z3:
`(distinct x y z)` over `(_ BitVec 1)`; `(distinct a b c)` over three
`fp.isZero`-pinned `(_ FloatingPoint 2 2)` vars; `(= x y z) ∧ (distinct x z)`
over BV8; the same shape over Float32. Cause: `collect_bv_atoms` /
`collect_fp_atoms` run BEFORE the solver's `lower` pass, which pairwise-expands
n-ary `distinct` (all sorts) — so the expanded binary atoms are never blasted
and Tseitin treats them as free Bool leaves (and n-ary `=` is blasted by a
binary-only arm that silently ignores `kids[2..]`). The comment at the `lower`
call site ("BV atoms pass through unchanged, so their TermIds are preserved")
is false precisely for this family. Since the fix is the same
run-a-rewrite-before-collection mechanism the ite elimination needs, it is
pulled into this slice's pass.

After this slice, none of those shapes fences, crashes, or lies. This closes
the last non-Real incompleteness in QF_BV/QF_FP/QF_BVFP; the remaining fence
is exactly the permanent v1 Real bridge (`fp.to_real`, symbolic-Real `to_fp`).

**Also in scope (forced by the approach, and a user-facing win on its own):**
`=`/`distinct` over **RoundingMode**-sorted operands as first-class atoms
(today they fence to `Unknown` via the third-theory walk).

**Explicitly NOT in scope:**
- `ite` over Real/Int/Array/String-sorted branches — untouched, keeps each
  stage's current behavior (fence/refuse). Only BV/Float/RM sorts rewrite.
- The Real bridge (permanent v1 non-goal).
- Persistent incremental blasting (unchanged: re-blast per `check-sat`).

**Soundness contract (unchanged):** anything out of scope returns `unknown`,
never a wrong SAT/UNSAT verdict — and never a panic.

## 2. Semantics

SMT-LIB `ite` is total and fully specified: the value of `x` if `c` holds,
else the value of `y`. The sort checker (`context.rs`, `Ite` arm) already
enforces Bool condition + same-sorted branches. Two FP-specific notes:

- **FP `ite` operates on the FP value domain.** All NaN payloads are one
  value; ±0 are distinct values. The chosen encoding equates the result with
  a branch via SMT `=` (blasted through the NaN-aware
  `blast/compare.rs::core_eq`), so a NaN result may carry a *different bit
  pattern* than the selected branch. That is correct — the blasted world is
  already non-canonical for NaN — and it composes with 4e's FP→BV congruence,
  whose trigger equality is also `core_eq` (a NaN `ite` result and its NaN
  branch feed the same UF value).
- **RM `ite` preserves the one-hot invariant** because the result is a fresh
  RM variable constrained equal to one of two one-hot words, and `blast_rm`
  already emits exactly-one constraints for RM variables.

No z3 probing is needed: `ite` has no unspecified cases and no rounding
behavior. The differential oracle (§7) still nets the encoding.

## 3. Approaches considered

**A. Term-level ite elimination (CHOSEN).** A preprocessing pass in
`shinri-solver` rewrites every word-sorted `ite` occurrence to a fresh nullary
symbol `w` plus one top-level defining assertion
`(ite c (= w x) (= w y))` (Bool-sorted `ite` — already Boolean structure for
every stage). Conditions land in the Bool skeleton, where Tseitin, atom
collection, and every fence already handle arbitrary structure, nested atoms,
and shared Bool variables. Blasters never see `ite`; fences barely change
(fresh `w` is a nullary variable — already supported by every walk).

**B. Native blaster muxes.** Add `Ite` arms to `blast_bv_word` /
`blast_fp_word` / `blast_rm` (per-bit `Blaster::mux2`; the word-mux gadget
already exists privately in `blast/minmax.rs`), plus a new generic
`blast_bool` encoder inside the blaster for conditions, a Bool-leaf registry
on `Lowered`, and bridge clauses in `replay_bv_cnf` tying condition-side Bool
variables and nested atoms to their Tseitin/skeleton literals. Slightly
smaller CNF (direct mux vs. equality definitions), no ctx mutation, no fresh
symbols — but it duplicates the Bool encoder inside the blaster and the
skeleton to blaster bridging is brand-new soundness surface (a missed bridge
silently decouples the two copies of a shared Bool variable: wrong SAT).

**C. Crash-fix only.** Add a BV-side positive-enumeration fence (analog of
`fp_atoms_fully_supported`) so BV `ite` returns `Unknown` instead of
panicking; admit nothing. Smallest diff, defers all value; the filed bug was
"fix as its own slice", and the incremental cost of A over C is one contained
pass.

A is chosen: it has strong in-repo precedent (the arith `lower` pass and
`shinri_bv::rewrite` already rewrite terms per check; n-ary `distinct`
lowering already mutates `ctx`), it fixes the panic on **every** blasted path
at once (pure-BV, mixed BVFP, and any stage that reuses `blast_bv_word` —
e.g. an eliminated `ite` nested under a QF_ABV BV atom never reaches the
blaster), and it makes the fence delta nearly zero.

## 4. The normalization pass (`crates/shinri-solver/src/word_norm.rs`)

One pass, two rewrites over word-sorted (BV/Float/RM) shapes: **ite
elimination** and **n-ary `=`/`distinct` expansion** (adjacent-pair chain for
`=`, pairwise conjunction for `distinct` — both producing binary atoms that
the existing binary-only blast arms handle correctly, fixing the §1 wrong-SAT
family). N-ary `=`/`distinct` over other sorts (Bool/arith/EUF) are left
untouched — the later `lower` pass keeps handling them as today.

Runs at the **top of `solve()`**, on the snapshot of the assertion stack,
**before** `uses_fp` detection, atom collection, crossing/fence walks, and
Tseitin — so every downstream consumer sees one consistent post-elimination
assertion set (this ordering is load-bearing: atom collection is keyed by
TermIds that Tseitin must later look up; collection and encoding must see the
same terms).

Bottom-up memoized rebuild over each assertion:

- **`(ite c x y)` with BV/Float/RM-sorted branches:** recurse into `c`, `x`,
  `y` first (inner word-ites rewrite too), then replace the node with a fresh
  nullary symbol `w` of the branch sort and append
  `(ite c' (= w x') (= w y'))` to the assertion vector.
- **Bool-sorted `ite`:** keep the node (rebuild if children changed) — Tseitin
  handles it.
- **Any other sort of `ite`** (Real/Int/Array/String): keep the node —
  out-of-scope stages keep their current behavior.
- **Every other App:** rebuild only if a child changed (standard memoized
  rewrite, same shape as `lower`).

**Fresh-symbol discipline:**
- One `w` per distinct `ite` TermId, memoized in a **solver-lifetime map**
  (`FxHashMap<TermId, TermId>`), so shared subterms and repeated `check-sat`s
  reuse one symbol and ctx growth is bounded by the number of distinct
  word-ite terms. The defining assertion is (re-)emitted per `check-sat` (v1
  re-blasts anyway); the definition is attached to the per-check assertion
  snapshot, never to the user-visible assertion stack, so push/pop is
  unaffected.
- Names come from a reserved counter (`ite!<n>`) and are **uniquified against
  the ctx symbol table** (a user may legally declare `|ite!0|`); model
  filtering keys on an **internal-TermId set** owned by the solver, never on
  the name (§6).

**Correctness argument:** `w` is functionally determined by `(c, x, y)`
(exactly one branch of the defining `ite` holds, and each branch pins `w` by
`=` on the value domain), so the rewrite is equisatisfiable and
model-preserving for all user symbols. The definition sits at top level with
positive polarity — no polarity subtlety. CNF cost per ite: both branch words
were already blasted (a mux would blast both too) plus one `core_eq`/bitwise
equality per branch — O(width) clauses, no deep recursion (no interaction
with the fp.div circuit-depth constraint).

## 5. RM equality atoms (the one new blast face)

The RM-ite definition emits `(= w RNE)`-shaped atoms, so RM equality becomes
part of the admitted atom language (it is also directly user-writable and
currently fences):

- **Routing:** `solver_uses_fp` must treat RM-sorted subterms as FP content
  (today it keys on `Float(_,_)` sorts and FP ops only), so RM-only scripts
  enter the FP path instead of leaking to EUF — this is the fix for the
  wrong-SAT bug in §1. Whether that is a widened `is_fp_sorted` or a parallel
  RM check is a plan-level choice; audit every `is_fp_sorted` call site either
  way.
- `collect_fp_atoms` additionally collects `Eq`/`Distinct` whose operands are
  RoundingMode-sorted (exactly parallel to the existing Float-operand arm —
  and like that arm, this is SOUNDNESS-CRITICAL: an RM equality that escapes
  collection routes to EUF, which answers wrong SATs on pigeonhole shapes).
- **N-ary `distinct` over RM operands must be handled** (the confirmed repro
  is 6-ary). Whether the blaster expands pairwise or a pre-lowering does is a
  plan-level choice; the FP path's existing treatment of n-ary Float
  `distinct` is the template — pre-flight must check what that actually is.
- `blast_fp_atom` gains an RM arm: blast both sides via the existing
  `blast_rm` (one-hot `[BitLit; 5]`, shared `rm_cache`), then
  `eq = OR_i (a_i AND b_i)` — correct under the one-hot invariant that
  `blast_rm` establishes for both literals and variables. `Distinct` is the
  negation.
- `Lowerer::atom`'s first-operand sort dispatch routes RM-sorted operands to
  `blast_fp_atom` (today it would fall through to the FP arm anyway; make the
  dispatch explicit).
- `has_non_bvfp_theory_atom` / `has_non_bv_theory_atom`: RM equalities are now
  collected as FP atoms (leaves), so the mixed walk accepts them; the pure-BV
  path cannot contain RM sorts (parser/sort-check), so no change there.
- `is_rounding_mode_term` is **unchanged**: after elimination, RM operands of
  FP ops are still only literals or nullary RM variables (the fresh `w` is a
  nullary variable). RM model read-back: RM variables already appear in
  `rm_cache`, not `var_bits`; model behavior for user RM constants is
  unchanged by this slice (whatever `get-model` reports for RM variables
  today, it reports tomorrow).

## 6. Fence delta & model hygiene

**Fence delta (small, mostly deletions-by-unreachability):**
- `is_supported_fp_word` / `fp_atoms_fully_supported` /
  `bv_atoms_fp_supported`: no code change required — eliminated assertions
  contain no word-sorted `ite`, and fresh variables are nullary uninterpreted
  (already supported). The doc-comment listing "FP-sorted ite" as the fenced
  example must be updated; the arm stays as defense-in-depth for future ops.
- The `blast_bv_word` catch-all `unreachable!` at `blast/mod.rs:430` stays,
  and becomes an internal invariant with a one-line comment: word-ite cannot
  reach it because elimination runs unconditionally before every stage.
  **Invariant:** the elimination pass must remain the first assertion
  transform in `solve()`.
- `uses_crossing_conversion` walks the post-elimination set — defining
  assertions are walked like any other (a still-crossing op nested in an ite
  branch still fences, exactly as before).

**Model hygiene (required, verified by test):** fresh `w` symbols are nullary
uninterpreted apps, so they land in the `Lowerer` cache, then
`var_bits_split`, then `last_model.values`, and `format_model` would print
them. The solver keeps the set of internal fresh TermIds (the memo map's
value set) and the model builder **excludes** them from `get-model` output.
`get_value` on an original `ite` TermId returns `None` today and continues to
(not a regression; noted as a possible later nicety).

## 7. Testing (the established slice pattern)

**Pre-flight canary hunt (front-loaded, per the standing lesson):** the
fence flips from `Unknown` to real verdicts, so pins on the old behavior
break. Known: the `fp_stage.rs` unit test at ~813–824 ("an UNSUPPORTED FP
shape (FP-sorted ite)… is not a supported FP word") — repoint at a shape that
stays fenced (e.g. a symbolic-Real `to_fp`) or at the walk's defensive arm
directly. Sweep `rg -i 'ite'` across all test files for further Unknown-pins
before implementation, then net with full `cargo test --workspace`.

**Unit — elimination pass (`shinri-solver`):** nested ite (branch-in-branch,
ite-inside-condition-atom), sharing (one ite term under two assertions → one
`w`), memo reuse across two `check-sat`s, sort scoping (Real-sorted ite left
untouched), name uniquification against a user-declared `|ite!0|`.

**Unit — RM equality (`shinri-fp`):** exhaustive 5×5 RM-literal pairs
(SAT-solve the reified atom, assert it matches `==` on modes); variable-vs-
literal and variable-vs-variable shapes; `distinct` negation.

**Lowerer tests (`lower.rs`):** post-elimination shapes end-to-end through
`lower_mixed`: BV ite word equality; FP ite whose branches are NaN vs. −0
(observed through `fp.isNaN` / `fp.isNegative`, not raw bits); RM ite
steering `fp.add` (RNE vs. RTP on a halfway sum — the two modes give
different, individually pinned results).

**e2e (`fp_e2e.rs` + BV e2e):** the filed crash repro `(= (ite c x y) z)` as
a SAT/UNSAT pair (this is the regression test for the panic); FP-sorted ite
SAT/UNSAT; RM-sorted ite observable through rounding; a mixed condition
`(ite (and p (fp.lt a b)) x y)` with `p` also asserted at the skeleton level
(the shared-Bool-variable shape that approach B would have had to bridge);
`get-model` on a SAT instance never mentions `ite!` symbols and evaluates the
user constants correctly; and the confirmed soundness repro pinned UNSAT:
`(declare-const r RoundingMode) (assert (distinct r RNE RNA RTP RTN RTZ))`
plus its SAT twin with one literal dropped (5-ary distinct → `sat`); and the
four n-ary `=`/`distinct` repros from §1 pinned to their z3 verdicts, each
with a SAT twin.

**Differential z3 oracle:** new `differential_qf_bvfp_ite` suite — randomly
generated nested ites over BV/FP/RM branches with mixed-atom conditions,
~200 cases, every verdict z3-checked, zero disagreements required; all
pre-existing differential counts must stay byte-identical to the 4e baseline.

**Full net:** `cargo test --workspace` EXIT=0 (run in background — the FP
exhaustive suites are multi-minute); clippy net-new zero.

## 8. Risks

- **Ordering regressions.** Moving a rewrite ahead of atom collection touches
  the one invariant the 4b/4e work leaned on (collection and Tseitin must see
  the same TermIds). Mitigation: elimination replaces the assertion vector
  wholesale before anything else reads it; every stage consumes the same
  vector; the full-workspace net plus byte-identical differential baselines
  catch drift on the non-FP stages (string/arith/abv assertions without
  word-ites rebuild to themselves — the memoized rewrite returns the original
  TermId when nothing changed, so non-ite paths see *identical* TermIds, not
  equal-but-fresh ones. This no-change-means-same-TermId property is a hard
  requirement of the pass).
- **Canary flips beyond the known one.** Standing 4-slice lesson; the
  pre-flight hunt plus workspace net is the mitigation.
- **Model leakage of `ite!` symbols.** Covered by an explicit e2e assertion.
- **Routing flip for RM-only scripts.** Scripts whose only theory content is
  RM (dis)equality move from the EUF path to the FP path. Today's answers on
  such scripts are untrustworthy (the confirmed wrong SAT), so flips are
  fixes, but pre-flight should sweep tests for anything pinning the old
  routing or its verdicts.
- **One-hot dependence of the RM-eq gadget.** `OR_i(a_i ∧ b_i)` is wrong for
  non-one-hot words; it is only ever applied to `blast_rm` outputs, which
  carry the exactly-one constraint. Noted at the gadget with a debug
  assertion on width 5.

## 9. Decisions locked for slice 5

| Decision | Choice |
|---|---|
| Mechanism | Term-level elimination to fresh symbol + defining assertion (approach A) |
| N-ary `=`/`distinct` over BV/FP/RM | Expanded to binary in the same pass (chain / pairwise) — fixes the confirmed wrong-SAT family |
| Sorts rewritten | BitVec, Float, RoundingMode only |
| Conditions | Unrestricted Bool (connectives, nested atoms, shared skeleton vars) |
| Definition shape | `(ite c (= w x) (= w y))`, top-level, per-check snapshot |
| FP equality in definition | NaN-aware `core_eq` (SMT `=` value semantics) |
| RM equality atoms | Admitted; `OR_i(a_i ∧ b_i)` over one-hot selectors |
| RM-only routing | `solver_uses_fp` treats RM-sorted content as FP — fixes the confirmed EUF wrong-SAT pigeonhole |
| `is_rounding_mode_term` | Unchanged |
| Fresh symbols | `ite!<n>`, uniquified; excluded from `get-model` via internal-TermId set |
| blast-side `Ite` arms | None — `unreachable!` stays an internal invariant |
| Real/Int/Array/String ite | Untouched (current fence/refuse behavior) |
| Validation | Elimination units, RM-eq units, lowerer, e2e, new z3 differential suite, canary hunt, full workspace net |
