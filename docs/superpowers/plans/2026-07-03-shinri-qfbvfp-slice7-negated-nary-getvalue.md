# shinri QF_BVFP Slice 7 — Negated n-ary Soundness + Get-value Completeness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the five slice-6 follow-ups — three wrong-verdict/panic soundness defects (C2 negated arith n-ary `=`, I1 negated n-ary String `distinct`, I2 debug-build panics) and two get-value completeness gaps (nested-ite outer term, QF_ABV channel).

**Architecture:** Targeted fixes in the existing lowering pipeline. C2 generalizes the binary `Not(Eq)` pure-arith rewrite to n-ary in `lib.rs::lower`. I1 folds trivial self-pairs to `false` in `word_norm` distinct expansion (plus a diagnosis-gated `shinri-str` polarity fix). I2 diagnoses the two premature-SAT debug asserts and either fixes the upstream state or guards the assert. Items 4/5 add an original-term-keyed eliminated-ite map and wire the get-value remap into the QF_ABV path.

**Tech Stack:** Rust workspace (`shinri-solver`, `shinri-str`, `shinri-sat`, `shinri-theory`, `shinri-abv`, `shinri-core`); `cargo test`; z3 on PATH for the `oracle` feature; `easy_smt` for the differential harness.

## Global Constraints

- **No new FP surface, no fence changes.** This slice touches only soundness/conformance/completeness. Do not add a theory operator or alter the FP admission fence.
- **z3 is the source of truth** for every hard pin. Any e2e verdict pin must match a z3 run of the same SMT-LIB.
- **No-change ⇒ same TermId** in `word_norm::walk` (hard requirement, `word_norm.rs:116`): only rebuild when a child actually changed.
- **Clippy net-new zero** against the slice-6 known set: solver=2 / fp=22 / parser=3 / theory=4 / str=9. Do not introduce new warnings.
- **Get-model output unchanged.** Get-value completeness work must not add entries to `get-model`; the `word_norm.internal` filter set stays authoritative for model output.
- **Long test suites run in the background by the implementer directly**, not via looping subagents (the FP/SAT suites take minutes; e.g. shinri-fp ~2079s).
- **Soundness-first ordering with I2 before the string oracle re-baseline** (C2/I1 shift TermId numbering; the `differential_qf_s_nary` seed was chosen to skirt the I2 panics — that constraint only lifts once I2 is fixed).

---

### Task 1: Pre-flight & canary hunt

No code changes. Confirm the spec's assumptions hold against the live tree and enumerate every test currently pinned to a wrong/degraded verdict so later tasks flip them in the same commit as the fix. Record findings in the task's completion note.

**Files:**
- Read only: `crates/shinri-solver/src/lib.rs`, `crates/shinri-solver/src/word_norm.rs`, `crates/shinri-solver/src/abv_stage.rs`, `crates/shinri-str/src/lib.rs`

- [ ] **Step 1: Confirm C2 reaches the generic n-ary path**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --lib not_eq_different_terms_int_is_unsat -- --nocapture
```
Expected: PASS (the binary `Not(Eq)` fix is intact — we generalize it, not replace it).

- [ ] **Step 2: Reproduce C2 as a failing verdict (throwaway)**

Run z3 to confirm the ground truth, then shinri to confirm the bug:
```bash
cd /workspace
printf '(declare-const x Int)(declare-const y Int)(declare-const z Int)\n(assert (not (= x y z)))(assert (<= x y))(assert (>= x y))(assert (<= y z))(assert (>= y z))(check-sat)\n' | z3 -smt2 -in
```
Expected: `unsat`. (shinri currently answers sat — confirmed in Task 2's failing test.)

- [ ] **Step 3: Reproduce I1 ground truth**

Run:
```bash
cd /workspace
printf '(declare-const s1 String)(declare-const s2 String)(declare-const s3 String)\n(assert (not (distinct s1 s2 s2)))(assert (= s2 s1))(assert (= s1 (str.++ s3 "ab")))(check-sat)\n' | z3 -smt2 -in
```
Expected: `sat`. (shinri currently answers unsat.)

- [ ] **Step 4: Probe the I1 semantic-duplicate variant ground truth**

This determines whether Task 3 needs the `shinri-str` polarity fix (approach B) in addition to the word_norm fold (approach A):
```bash
cd /workspace
printf '(declare-const s1 String)(declare-const s2 String)(declare-const s3 String)\n(assert (not (distinct s1 s2 s3)))(assert (= s2 s3))(check-sat)\n' | z3 -smt2 -in
```
Expected: `sat` (s2=s3 makes the distinct false, so its negation is true). Note the shinri answer in Step 6; if shinri says unsat here, Task 3 MUST include the polarity fix.

- [ ] **Step 5: Confirm the ABV path keeps a BV-ite query on the QF_ABV route**

Read `crates/shinri-solver/src/abv_stage.rs` `uses_arrays_over_bv` and `fenced`. Confirm that a query mixing a `(select a i)` atom with a plain BV-sorted `(ite c x y)` (which word_norm eliminates to a BV const before the ABV stage sees it) is NOT fenced. Record the conclusion; if it IS fenced, Task 6's e2e test must be restructured so the eliminated ite still lands on the ABV path.

- [ ] **Step 6: Canary hunt**

Run:
```bash
cd /workspace
grep -rn "distinct\|not (= \|ite\|get-value\|Unknown\|wrong" crates/shinri-solver/tests crates/shinri-solver/src crates/shinri-str/src | grep -in "canary\|pre-existing\|wrong\|follow-up\|slice 6\|slice-6" | head -40
```
Enumerate any test asserting the current wrong verdict (C2 sat / I1 unsat) or a degraded `?` on the nested-ite / ABV get-value shapes. There should be none pinning the *wrong* C2/I1 verdicts (they were filed, not pinned), but confirm. List every hit in the completion note so later tasks know what to flip.

- [ ] **Step 7: Record findings**

Write a one-paragraph completion note: C2/I1 ground truths confirmed, the I1 semantic-duplicate shinri answer (→ whether Task 3 needs approach B), the ABV-route conclusion, and the canary list. No commit (investigation only).

---

### Task 2: C2 — generalize `Not(Eq)` pure-arith rewrite to n-ary

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (the `Not` → `Eq` arm, ~1027-1058)
- Test: `crates/shinri-solver/src/lib.rs` (new `mod nary_soundness_tests` after `run_outcome`, ~1548)

**Interfaces:**
- Consumes: `self.is_arith_sorted(TermId) -> bool` (`lib.rs:895`); `Solver::is_pure_arith(&Context, TermId) -> bool` (`lib.rs:874`); `self.ctx.mk_app(Op, &[TermId]) -> Result<TermId, _>`; `BuiltinOp::{Lt, Gt, Or}`.
- Produces: no new public API; behaviour change only.

- [ ] **Step 1: Write the failing e2e test**

Add after the `run_outcome` function (`crates/shinri-solver/src/lib.rs:1548`):

```rust
#[cfg(test)]
mod nary_soundness_tests {
    use super::*;

    /// C2 (slice 7): negated n-ary arith `=` must be sound. `x=y=z` is forced
    /// by the four bound constraints, so `(not (= x y z))` is UNSAT. Pre-fix the
    /// generic `(not (and …))` path let SAT pick `¬Eq_euf` independently of the
    /// Arith `Le∧Ge` companions → wrong-SAT. z3-verified unsat.
    #[test]
    fn not_nary_eq_int_forced_equal_is_unsat() {
        let src = "(declare-const x Int)(declare-const y Int)(declare-const z Int)\
                   (assert (not (= x y z)))\
                   (assert (<= x y))(assert (>= x y))\
                   (assert (<= y z))(assert (>= y z))(check-sat)";
        assert_eq!(run_outcome(src), SolveOutcome::Unsat);
    }

    /// C2 companion: negated n-ary arith `=` that IS satisfiable stays sat
    /// (z=y forced, but x free → x can differ). z3-verified sat.
    #[test]
    fn not_nary_eq_int_satisfiable_is_sat() {
        let src = "(declare-const x Int)(declare-const y Int)(declare-const z Int)\
                   (assert (not (= x y z)))\
                   (assert (<= y z))(assert (>= y z))(check-sat)";
        assert_eq!(run_outcome(src), SolveOutcome::Sat);
    }
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --lib not_nary_eq_int_forced_equal_is_unsat -- --nocapture
```
Expected: FAIL — `assertion `left == right`` with `left: Sat, right: Unsat` (the wrong-SAT bug).

- [ ] **Step 3: Generalize the special case**

In `crates/shinri-solver/src/lib.rs`, replace the binary-only guard body inside the `Not` handler's `Eq` arm (currently `if eq_kids.len() == 2 && … { let a=…; let b=…; let lt=…; let gt=…; Some(Or[lt,gt]) } else { None }`, ~1035-1057) with:

```rust
// (not (= a b c …)) over ALL-pure-arith operands ≡ (or (a≠b) (b≠c) …);
// each pure-arith a≠b lowers to (or (Lt a b) (Gt a b)). Binary stays
// byte-identical (single disjunct returned bare). Mixed-EUF operands (any
// non-pure-arith kid) fall through to the generic recursion below, exactly
// as the binary case did. (C2 wrong-SAT fix, slice 7.)
if eq_kids.len() >= 2
    && self.is_arith_sorted(eq_kids[0])
    && eq_kids.iter().all(|&k| Self::is_pure_arith(&self.ctx, k))
{
    let mut disj: Vec<TermId> = Vec::with_capacity(eq_kids.len() - 1);
    for w in eq_kids.windows(2) {
        let lt = self
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Lt), &[w[0], w[1]])
            .expect("Lt well-sorted");
        let gt = self
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Gt), &[w[0], w[1]])
            .expect("Gt well-sorted");
        let ne = self
            .ctx
            .mk_app(Op::Builtin(BuiltinOp::Or), &[lt, gt])
            .expect("or well-sorted");
        disj.push(ne);
    }
    if disj.len() == 1 {
        // Binary case: return (or Lt Gt) bare — identical to the pre-slice-7
        // output, so the TermId layout and existing pins are undisturbed.
        Some(disj.pop().unwrap())
    } else {
        Some(
            self.ctx
                .mk_app(Op::Builtin(BuiltinOp::Or), &disj)
                .expect("or well-sorted"),
        )
    }
} else {
    None
}
```

- [ ] **Step 4: Run the C2 tests to verify they pass**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --lib nary_soundness_tests -- --nocapture
cargo test -p shinri-solver --lib not_eq_different_terms_int_is_unsat -- --nocapture
```
Expected: all PASS (new C2 tests green; the existing binary pin still green).

- [ ] **Step 5: Commit**

```bash
cd /workspace
git add crates/shinri-solver/src/lib.rs
git commit -m "fix(solver): generalize Not(Eq) pure-arith rewrite to n-ary — closes C2 negated n-ary = wrong-SAT (slice 7)"
```

---

### Task 3: I1 — fold self-pair n-ary `distinct` to `false` (+ diagnosis-gated str fix)

**Files:**
- Modify: `crates/shinri-solver/src/word_norm.rs` (the `Distinct` arm, ~158-175)
- Possibly modify: `crates/shinri-str/src/lib.rs` (only if Task 1 Step 4 showed the semantic-duplicate variant is also wrong)
- Test: `crates/shinri-solver/src/lib.rs` (`mod nary_soundness_tests`); `crates/shinri-solver/src/word_norm.rs` (`mod tests`)

**Interfaces:**
- Consumes: `ctx.mk_const_bool(bool) -> TermId` (`context.rs:739`); `new_kids: Vec<TermId>`.
- Produces: no new public API; `word_norm` distinct expansion now emits `false` when any two operands are syntactically equal.

- [ ] **Step 1: Write the failing e2e test**

Add to `mod nary_soundness_tests` in `crates/shinri-solver/src/lib.rs`:

```rust
    /// I1 (slice 7): `(distinct s1 s2 s2)` has a repeated operand, so it is
    /// unsatisfiable-as-true → false; `(not (distinct s1 s2 s2))` is therefore
    /// true and imposes no constraint. With s2=s1 and s1=s3++"ab" the query is
    /// SAT. Pre-fix shinri answered unsat (wrong-UNSAT). z3-verified sat.
    #[test]
    fn not_nary_string_distinct_with_dup_is_sat() {
        let src = "(declare-const s1 String)(declare-const s2 String)\
                   (declare-const s3 String)\
                   (assert (not (distinct s1 s2 s2)))\
                   (assert (= s2 s1))\
                   (assert (= s1 (str.++ s3 \"ab\")))(check-sat)";
        assert_eq!(run_outcome(src), SolveOutcome::Sat);
    }
```

- [ ] **Step 2: Run the test to verify it fails**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --lib not_nary_string_distinct_with_dup_is_sat -- --nocapture
```
Expected: FAIL — `left: Unsat, right: Sat`.

- [ ] **Step 3: Write the word_norm unit test (failing)**

Add to `crates/shinri-solver/src/word_norm.rs` `mod tests`:

```rust
    #[test]
    fn distinct_with_duplicate_operand_folds_to_false() {
        use shinri_core::{ConstVal, TermNode};
        let mut ctx = Context::new();
        let a = bv_var(&mut ctx, "a", 8);
        let b = bv_var(&mut ctx, "b", 8);
        // (distinct a b b) — b repeated ⇒ unsatisfiable-as-true ⇒ false.
        let d = ctx
            .mk_app(Op::Builtin(BuiltinOp::Distinct), &[a, b, b])
            .unwrap();
        let mut wn = WordNorm::default();
        let out = wn.run(&mut ctx, &[d]);
        // Single assertion rewritten to the `false` constant.
        assert_eq!(out.len(), 1);
        assert!(
            matches!(
                ctx.term_node(out[0]),
                TermNode::Const(ConstVal::Bool(false))
            ),
            "expected false constant, got {:?}",
            ctx.term_node(out[0])
        );
    }
```

Note: confirm the `run` entry point name/signature and the `Const` node shape while writing this — grep `pub fn run` in `word_norm.rs` and the `ConstVal::Bool` variant in `shinri-core`. Adjust the constructor call and the match pattern to the actual API if they differ.

- [ ] **Step 4: Run the unit test to verify it fails**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --lib word_norm::tests::distinct_with_duplicate_operand_folds_to_false -- --nocapture
```
Expected: FAIL (currently expands to a pairwise `And`, not `false`).

- [ ] **Step 5: Fold self-pairs in the distinct expansion**

In `crates/shinri-solver/src/word_norm.rs`, replace the body of the `Op::Builtin(BuiltinOp::Distinct) if new_kids.len() > 2 =>` arm (~158) with:

```rust
{
    // An n-ary distinct with a repeated operand can never hold (a value
    // cannot differ from itself), so the whole atom is `false`. Fold it
    // directly rather than emit a self-distinct pair `(distinct x x)` that
    // the string/EUF theory then mishandles regardless of polarity
    // (I1 wrong-UNSAT, slice 7).
    let mut has_dup = false;
    'outer: for i in 0..new_kids.len() {
        for j in (i + 1)..new_kids.len() {
            if new_kids[i] == new_kids[j] {
                has_dup = true;
                break 'outer;
            }
        }
    }
    if has_dup {
        ctx.mk_const_bool(false)
    } else {
        // (distinct a b c ...) → conjunction over all pairs i<j.
        let mut pairs: Vec<TermId> = Vec::new();
        for i in 0..new_kids.len() {
            for j in (i + 1)..new_kids.len() {
                pairs.push(
                    ctx.mk_app(
                        Op::Builtin(BuiltinOp::Distinct),
                        &[new_kids[i], new_kids[j]],
                    )
                    .expect("binary distinct well-sorted"),
                );
            }
        }
        ctx.mk_app(Op::Builtin(BuiltinOp::And), &pairs)
            .expect("and well-sorted")
    }
}
```

- [ ] **Step 6: Run both I1 tests to verify they pass**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --lib not_nary_string_distinct_with_dup_is_sat -- --nocapture
cargo test -p shinri-solver --lib word_norm::tests::distinct_with_duplicate_operand_folds_to_false -- --nocapture
```
Expected: both PASS.

- [ ] **Step 7: Handle the semantic-duplicate variant (conditional on Task 1 Step 4)**

Add the e2e probe to `mod nary_soundness_tests`:

```rust
    /// I1 semantic-duplicate: s2=s3 makes `(distinct s1 s2 s3)` false via EUF
    /// (not syntax), so `(not (distinct s1 s2 s3))` is true → SAT. z3-verified.
    #[test]
    fn not_nary_string_distinct_semantic_dup_is_sat() {
        let src = "(declare-const s1 String)(declare-const s2 String)\
                   (declare-const s3 String)\
                   (assert (not (distinct s1 s2 s3)))\
                   (assert (= s2 s3))(check-sat)";
        assert_eq!(run_outcome(src), SolveOutcome::Sat);
    }
```

Run:
```bash
cd /workspace
cargo test -p shinri-solver --lib not_nary_string_distinct_semantic_dup_is_sat -- --nocapture
```

- **If PASS:** the syntactic fold plus existing theory handling suffices; no `shinri-str` change needed. Proceed to Step 8.
- **If FAIL (wrong-UNSAT):** the root cause is polarity/self-reference handling in `shinri-str`. Use superpowers:systematic-debugging: instrument the `eq_true` / distinct-atom path (`crates/shinri-str/src/lib.rs:107-136` and `first_distinct_const_clash`, `749`) to find where a distinct atom drives a conflict irrespective of assertion polarity. Fix it there so a distinct atom asserted FALSE (¬distinct ≡ eq) never yields a conflict from its own operands. Add the minimal fix, then re-run until this test passes. Keep the fix in-family (negated distinct only); do not broaden.

- [ ] **Step 8: Commit**

```bash
cd /workspace
git add crates/shinri-solver/src/word_norm.rs crates/shinri-solver/src/lib.rs
# add crates/shinri-str/src/lib.rs only if Step 7 required the polarity fix
git commit -m "fix(solver): fold self-pair n-ary distinct to false — closes I1 negated distinct wrong-UNSAT (slice 7)"
```

---

### Task 4: I2 — diagnose and resolve the premature-SAT debug panics

**Files:**
- Read: `crates/shinri-sat/src/solver.rs` (~553, `check_model` assert), `crates/shinri-theory/src/eq_engine.rs` (~366, `explain` assert), `crates/shinri-solver/src/lib.rs:687` (`string_model_satisfies` downgrade)
- Modify: whichever of the above the diagnosis implicates
- Test: `crates/shinri-solver/tests/qfs_differential.rs` or `crates/shinri-solver/src/lib.rs` (debug no-panic pins)

**Interfaces:**
- Consumes: `run_outcome` / `run_values` test helpers; the existing `string_model_satisfies` sound-Unknown downgrade.
- Produces: no new public API; either a corrected upstream theory state or a documented, narrowed assert guard.

- [ ] **Step 1: Write the failing debug no-panic pins**

Add to `mod nary_soundness_tests` in `crates/shinri-solver/src/lib.rs`:

```rust
    /// I2 (slice 7): the premature-SAT string/eq family must NOT panic in debug
    /// builds. The downstream string self-check (`string_model_satisfies`)
    /// soundly downgrades these to Unknown; the two debug_asserts on the way
    /// there must not fire. We assert only that solving returns *some* verdict
    /// without panicking (release already does; this guards debug).
    #[test]
    fn premature_sat_string_family_no_debug_panic_a() {
        let src = "(declare-const s1 String)(declare-const s2 String)\
                   (declare-const s3 String)\
                   (assert (not (= s1 s2 s3)))(assert (= s1 \"a\"))(check-sat)";
        let out = run_outcome(src);
        assert!(matches!(
            out,
            SolveOutcome::Sat | SolveOutcome::Unsat | SolveOutcome::Unknown
        ));
    }

    #[test]
    fn premature_sat_string_family_no_debug_panic_b() {
        let src = "(declare-const s1 String)(declare-const s2 String)\
                   (assert (not (= s1 s2)))(assert (= s1 \"a\"))(assert (= s2 \"a\"))\
                   (check-sat)";
        let out = run_outcome(src);
        assert!(matches!(
            out,
            SolveOutcome::Sat | SolveOutcome::Unsat | SolveOutcome::Unknown
        ));
    }
```

- [ ] **Step 2: Run under a DEBUG build to reproduce the panic**

Run (debug asserts are on in the default dev profile):
```bash
cd /workspace
cargo test -p shinri-solver --lib premature_sat_string_family_no_debug_panic -- --nocapture
```
Expected: FAIL — panic `returned SAT but a clause is unsatisfied` (`sat/solver.rs:553`) or `explain: a,b not connected` (`eq_engine.rs:366`). If neither panics on these exact inputs, use superpowers:systematic-debugging to find the TermId-layout-sensitive input that does (vary operand count/order; the slice-6 note flags layout sensitivity) and pin THAT input instead.

- [ ] **Step 3: Diagnose which invariant is violated**

Use superpowers:systematic-debugging. At each assert site, capture the state it inspects:
- `sat/solver.rs:553` — WHICH clause is unsatisfied when SAT is declared? Is it a genuine Boolean-level inconsistency (real bug: fix the upstream theory propagation that let SAT declare Sat prematurely) or a theory-incompleteness interlude the string self-check will downgrade (the assert is too strict for this known family)?
- `eq_engine.rs:366` — are `a` and `b` genuinely in different forest roots when `explain` is called (real bug in the caller passing an unconnected pair) or is `explain` reachable on a pair the premature-SAT state never actually merged?

Record the verdict per site.

- [ ] **Step 4: Apply the diagnosis-driven fix**

Two mutually exclusive branches (decide per Step 3, per site):

- **Genuine inconsistency:** fix the upstream state — the theory must not report `Sat` (or must not call `explain` on an unconnected pair) in this configuration. This is the preferred outcome.
- **Known, handled interlude:** narrow the `debug_assert` so it does not fire for this specific premature-SAT family, with a comment naming the family AND citing `string_model_satisfies` (`lib.rs:687`) as the downstream sound downgrade that makes it safe. Do NOT blanket-disable the assert — guard only the identified condition (e.g. skip the check when the string path is active and a self-check downgrade will follow).

- [ ] **Step 5: Run the debug pins to verify no panic**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --lib premature_sat_string_family_no_debug_panic -- --nocapture
```
Expected: both PASS (no panic; verdict returned).

- [ ] **Step 6: Commit**

```bash
cd /workspace
git add crates/shinri-sat/src/solver.rs crates/shinri-theory/src/eq_engine.rs crates/shinri-solver/src/lib.rs
# stage only the files the diagnosis actually changed
git commit -m "fix(solver): resolve I2 premature-SAT debug panics in the string/eq family (slice 7)"
```

---

### Task 5: Item 4 — nested-ite get-value via original-term-keyed map

**Files:**
- Modify: `crates/shinri-solver/src/word_norm.rs` (`struct WordNorm` fields ~30; the ite arm in `walk` ~122-144; add an accessor near `ite_map` ~47)
- Modify: `crates/shinri-solver/src/lib.rs` (the get-value remap loop ~668-677)
- Test: `crates/shinri-solver/tests/fp_e2e.rs` (using `run_values`)

**Interfaces:**
- Consumes: `walk`'s original term id `t` and the fresh symbol `w`; `WordNorm::internal` (`internal_vals` stash in `lib.rs`).
- Produces: `WordNorm::orig_ite_map(&self) -> &FxHashMap<TermId, TermId>` — original (child-un-rewritten) eliminated-ite term → its internal fresh symbol term. Task 6 consumes this too.

- [ ] **Step 1: Write the failing nested-ite e2e test**

Add to `crates/shinri-solver/tests/fp_e2e.rs`:

```rust
#[test]
fn get_value_on_nested_eliminated_ite_returns_value() {
    // Item 4 (slice 7): the OUTER term of a nested eliminated ite. `ite_var` was
    // keyed by the child-rewritten ite, so the outer key embedded the inner
    // fresh var and never matched the user's original nested query term →
    // get-value degraded to "?". With orig_ite keyed by the original term it
    // resolves. c,d true → inner (ite d x y)=x=#x0f → outer=#x0f.
    let (o, values) = run_values(
        "(declare-const c Bool)(declare-const d Bool)\
         (declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))\
         (declare-const z (_ BitVec 8))\
         (assert c)(assert d)(assert (= x #x0f))(assert (= y #x07))\
         (assert (= z (ite c (ite d x y) #x00)))\
         (check-sat)(get-value ((ite c (ite d x y) #x00)))",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert_eq!(values.len(), 1);
    assert!(!values[0].contains("ite!"), "internal name leaked: {}", values[0]);
    assert!(!values[0].contains('?'), "no value produced (item-4 gap): {}", values[0]);
    assert!(values[0].contains("#x0f"), "expected #x0f: {}", values[0]);
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --test fp_e2e get_value_on_nested_eliminated_ite_returns_value -- --nocapture
```
Expected: FAIL — the assert `no value produced` fires (value is `?`).

- [ ] **Step 3: Add the original-term-keyed field and accessor**

In `crates/shinri-solver/src/word_norm.rs`, add a field to `struct WordNorm` (after `ite_var`, ~30):

```rust
    /// Original (child-un-rewritten) eliminated-ite term → its fresh symbol.
    /// `ite_var` is keyed by the POST-rewrite ite (needed for structural dedup
    /// during the walk); a nested outer ite's post-rewrite key embeds the inner
    /// fresh var and never matches the user's original get-value query term.
    /// This parallel map keyed by the original `t` closes that gap (item 4,
    /// slice 7). Get-value only; get-model output is unchanged.
    orig_ite: FxHashMap<TermId, TermId>,
```

Add an accessor next to `ite_map` (~47):

```rust
    /// Original eliminated-ite term → internal fresh symbol, for get-value on
    /// nested ites (item 4, slice 7).
    pub(crate) fn orig_ite_map(&self) -> &FxHashMap<TermId, TermId> {
        &self.orig_ite
    }
```

- [ ] **Step 4: Populate `orig_ite` in the ite arm of `walk`**

In the `Op::Builtin(BuiltinOp::Ite) if is_word_sort(...)` arm (`word_norm.rs:122-144`), after the fresh symbol `w` is resolved and before returning `w`, record the original term `t`:

```rust
                // Item 4 (slice 7): also key by the ORIGINAL term so get-value on
                // a nested outer ite (whose original child was not yet rewritten)
                // resolves. `t` is this ite's original id; `w` its fresh symbol.
                self.orig_ite.insert(t, w);
                w
```

(Place the `self.orig_ite.insert(t, w);` immediately before the trailing `w` that the arm evaluates to, keeping the existing `ite_var`/`def` logic untouched.)

- [ ] **Step 5: Consume `orig_ite_map` in the get-value remap loop**

In `crates/shinri-solver/src/lib.rs`, the remap loop (~672) currently iterates `self.word_norm.ite_map()`. Change it to ALSO map the original-keyed entries so nested outer terms resolve. Replace the loop (~672-676) with:

```rust
                for (&ite_t, &w) in self.word_norm.ite_map() {
                    if let Some(v) = internal_vals.get(&w) {
                        ite_vals.insert(ite_t, v.clone());
                    }
                }
                // Item 4 (slice 7): original-term-keyed entries (nested outer ites).
                for (&ite_t, &w) in self.word_norm.orig_ite_map() {
                    if let Some(v) = internal_vals.get(&w) {
                        ite_vals.insert(ite_t, v.clone());
                    }
                }
```

- [ ] **Step 6: Run the nested-ite test AND the existing single-ite tests**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --test fp_e2e get_value_on_nested_eliminated_ite_returns_value -- --nocapture
cargo test -p shinri-solver --test fp_e2e get_value_on_eliminated_ite -- --nocapture
cargo test -p shinri-solver --test fp_e2e pop_clears_eliminated_ite_value_no_stale_get_value -- --nocapture
```
Expected: new test PASS; the slice-6 single-ite / RM-ite / pop tests still PASS (get-model output unchanged, no stale values).

- [ ] **Step 7: Commit**

```bash
cd /workspace
git add crates/shinri-solver/src/word_norm.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/fp_e2e.rs
git commit -m "feat(solver): nested-ite get-value via original-term-keyed map — closes item-4 completeness gap (slice 7)"
```

---

### Task 6: Item 5 — QF_ABV eliminated-ite get-value channel

**Files:**
- Modify: `crates/shinri-solver/src/abv_stage.rs` (`solve_qfabv_with_models`, ~646)
- Modify: `crates/shinri-solver/src/lib.rs` (the QF_ABV route, ~357-370)
- Possibly modify: `crates/shinri-abv/src/*` (only if no scalar-value extractor exists)
- Test: `crates/shinri-solver/tests/fp_e2e.rs` (using `run_values`)

**Interfaces:**
- Consumes: `WordNorm::ite_map()` + `WordNorm::orig_ite_map()` (Task 5); the ABV `bridge`/`collect` state inside `solve_qfabv_with_models`.
- Produces: an extended `solve_qfabv_with_models` that ALSO returns eliminated-ite internal-symbol values (BV `ModelVal`s keyed by internal symbol term), which `lib.rs` remaps into `eliminated_ite_vals` via the Task-5 maps.

- [ ] **Step 1: Write the failing ABV get-value e2e test**

Add to `crates/shinri-solver/tests/fp_e2e.rs` (confirm the query stays on the QF_ABV route per Task 1 Step 5; adjust if fenced):

```rust
#[test]
fn get_value_on_eliminated_ite_qfabv_returns_value() {
    // Item 5 (slice 7): the QF_ABV path had no eliminated-ite get-value channel,
    // so get-value on an eliminated ite in an array query degraded to "?". The
    // ite (ite c x #x00) is word_norm-eliminated to a BV const before the ABV
    // stage; c true, x=#x0f → its value is #x0f.
    let (o, values) = run_values(
        "(declare-const c Bool)\
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const x (_ BitVec 8))\
         (assert c)(assert (= x #x0f))\
         (assert (= (select a #x00) (ite c x #x00)))\
         (check-sat)(get-value ((ite c x #x00)))",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert_eq!(values.len(), 1);
    assert!(!values[0].contains("ite!"), "internal name leaked: {}", values[0]);
    assert!(!values[0].contains('?'), "no value produced (item-5 gap): {}", values[0]);
    assert!(values[0].contains("#x0f"), "expected #x0f: {}", values[0]);
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --test fp_e2e get_value_on_eliminated_ite_qfabv_returns_value -- --nocapture
```
Expected: FAIL — `no value produced` (the ABV path never populates `eliminated_ite_vals`).

- [ ] **Step 3: Locate/confirm the scalar-value extractor in shinri-abv (diagnosis)**

Use superpowers:systematic-debugging. The internal `ite!<n>` symbols are BV-sorted constants appearing in the (normalized, binary) array atoms, so the blaster assigns them. Confirm how a scalar BV value is read from the live `bridge`/`c`/`abs` state after SAT — grep `crates/shinri-abv/src` for the analog of `array_model` for scalar terms (e.g. a `scalar_model` / bit-reading helper on `RealBridge`). Record the exact function to call. If none exists, the smallest addition is a helper that packs a BV term's assigned bits (mirroring how `array_model` reads element values). Note the chosen mechanism before coding.

- [ ] **Step 4: Extend `solve_qfabv_with_models` to return internal-ite values**

In `crates/shinri-solver/src/abv_stage.rs`, add a third return element: a `FxHashMap<TermId, shinri_theory::types::ModelVal>` mapping each internal eliminated-ite symbol term (those in `word_norm`'s ite maps that are BV-sorted and present in these assertions) to its extracted BV `ModelVal`. Build it in the same `if outcome == Sat` block where array models are built, using the Step-3 extractor over the internal symbol terms. Update the signature to:

```rust
pub fn solve_qfabv_with_models(
    ctx: &mut Context,
    assertions: &[TermId],
    internal_ite_syms: &[TermId],
) -> (
    shinri_abv::AbvOutcome,
    FxHashMap<TermId, String>,
    FxHashMap<TermId, shinri_theory::types::ModelVal>,
) {
```

Return the new map (empty on non-SAT, like `models`). The caller passes the set of internal ite symbol terms harvested from `self.word_norm.ite_map()`/`orig_ite_map()` values (the `w`s).

- [ ] **Step 5: Wire the remap in the QF_ABV route**

In `crates/shinri-solver/src/lib.rs` (~357-370), after collecting the internal symbols and calling the extended `solve_qfabv_with_models`, remap into `eliminated_ite_vals` using the Task-5 maps (original-term → internal symbol → value):

```rust
        if crate::abv_stage::uses_arrays_over_bv(&self.ctx, &assertions) {
            if crate::abv_stage::fenced(&self.ctx, &assertions) {
                return SolveOutcome::Unknown;
            }
            let assertions_owned = assertions.clone();
            // Harvest the internal eliminated-ite symbols so the ABV stage can
            // return their BV values (item 5, slice 7).
            let internal_ite_syms: Vec<TermId> = self
                .word_norm
                .ite_map()
                .values()
                .chain(self.word_norm.orig_ite_map().values())
                .copied()
                .collect();
            let (outcome, array_models, ite_sym_vals) =
                crate::abv_stage::solve_qfabv_with_models(
                    &mut self.ctx,
                    &assertions_owned,
                    &internal_ite_syms,
                );
            self.abv_array_models = array_models;
            // Remap original ite terms → their internal symbol's value.
            let mut ite_vals: rustc_hash::FxHashMap<TermId, shinri_theory::types::ModelVal> =
                rustc_hash::FxHashMap::default();
            for (&ite_t, &w) in self
                .word_norm
                .ite_map()
                .iter()
                .chain(self.word_norm.orig_ite_map().iter())
            {
                if let Some(v) = ite_sym_vals.get(&w) {
                    ite_vals.insert(ite_t, v.clone());
                }
            }
            self.eliminated_ite_vals = ite_vals;
            return match outcome {
                shinri_abv::AbvOutcome::Sat => SolveOutcome::Sat,
                shinri_abv::AbvOutcome::Unsat => SolveOutcome::Unsat,
                shinri_abv::AbvOutcome::Unknown => SolveOutcome::Unknown,
            };
        }
```

Update `solve_qfabv_model_string` (the `#[cfg(test)]` helper, `abv_stage.rs:680`) and any other caller to the new 3-tuple signature (pass `&[]` for `internal_ite_syms`).

- [ ] **Step 6: Run the ABV get-value test and the existing ABV tests**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --test fp_e2e get_value_on_eliminated_ite_qfabv_returns_value -- --nocapture
cargo test -p shinri-solver --test qfax_e2e -- --nocapture
cargo test -p shinri-solver --test qfabv_oracle -- --nocapture 2>/dev/null || echo "(oracle needs --features oracle; run in Task 8)"
```
Expected: new test PASS; array-model e2e tests still PASS (`abv_array_models` unchanged).

- [ ] **Step 7: Commit**

```bash
cd /workspace
git add crates/shinri-solver/src/abv_stage.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/fp_e2e.rs
# add crates/shinri-abv/src/... only if Step 3 required a new scalar extractor
git commit -m "feat(solver): QF_ABV eliminated-ite get-value channel — closes item-5 completeness gap (slice 7)"
```

---

### Task 7: Differential oracle — negated n-ary arith coverage + string re-baseline

**Files:**
- Create: `crates/shinri-solver/tests/nary_arith_oracle.rs` (new — C2's family: no existing oracle covers arith n-ary `=`)
- Modify: `crates/shinri-solver/tests/qfs_differential.rs` (drop the I2-skirt seed constraint now that I2 is fixed; record new counts)

**Interfaces:**
- Consumes: the `Lcg`, `shinri_outcome`, and z3 harness conventions from `crates/shinri-solver/tests/nary_oracle.rs` (copy verbatim per the existing convention).
- Produces: `differential_qf_lia_nary` — a z3-checked oracle over random negated/positive n-ary `=` atoms on Int variables with bound constraints.

- [ ] **Step 1: Write the arith n-ary oracle**

Create `crates/shinri-solver/tests/nary_arith_oracle.rs`. Copy the `Lcg`, `shinri_outcome`, and z3-send scaffolding from `nary_oracle.rs` (lines 9-58), then generate Int-sorted scripts whose assertions include `(not (= a b c …))` and bound constraints (`(<= a b)`, `(>= a b)`) that sometimes force equality — the exact C2 shape. Use `set_logic("QF_LIA")` for z3. Gate on `#![cfg(feature = "oracle")]`. Assert every iteration is z3-checked with zero disagreements, mirroring `differential_qf_uf_nary` (lines 104-149). Seed: `0x51CE7_0001`.

```rust
#![cfg(feature = "oracle")]
// Differential oracle: shinri vs z3 on negated/positive n-ary arith `=` over
// Int with bound constraints (slice 7 — C2's family; no prior oracle covered
// arith n-ary =). Requires z3 on PATH.
// (Copy Lcg + shinri_outcome + z3 send scaffolding from nary_oracle.rs.)
```

Fill in the generators and the `#[test] fn differential_qf_lia_nary()` body concretely following `nary_oracle.rs` (do not leave the sketch above as-is — write the full generator: N vars `a..d` of Int, 2-4 assertions each a negated-or-positive n-ary `=` of arity 2-4 and/or a bound pair, `(check-sat)`).

- [ ] **Step 2: Run the arith oracle to verify zero disagreements**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --features oracle --test nary_arith_oracle -- --nocapture
```
Expected: PASS — prints `sat=… unsat=… unknown=0 z3_checked=200/200`, zero disagreements. If it finds a disagreement, that is a real bug surfaced by the corpus — stop and fix it (likely a C2-adjacent case Task 2 missed) before continuing.

- [ ] **Step 3: Re-baseline the string oracle seed (drop the I2 skirt)**

In `crates/shinri-solver/tests/qfs_differential.rs`, the `qfs_matches_z3` seed (`0x5_1_1A_0000_0001`, ~402) and/or the slice-6 `differential_qf_s_nary` seed `0xB000_9E37` were chosen to skirt the I2 debug panics. Now that I2 is fixed (Task 4), widen coverage: change the string-family seed to `0xB000_9E38` (one past the skirt) so the corpus can include the previously-panicking premature-SAT shapes.

Run:
```bash
cd /workspace
cargo test -p shinri-solver --features oracle --test qfs_differential -- --nocapture
```
Expected: PASS with the new seed — no panic (I2 fixed), zero disagreements. Record the new `sat/unsat/unknown/z3_checked` counts.

- [ ] **Step 4: Commit**

```bash
cd /workspace
git add crates/shinri-solver/tests/nary_arith_oracle.rs crates/shinri-solver/tests/qfs_differential.rs
git commit -m "test(solver): negated n-ary arith oracle + string re-baseline post-I2 (slice 7)"
```

---

### Task 8: Full verification sweep + spec Status block

**Files:**
- Modify: `docs/superpowers/specs/2026-07-03-shinri-qfbvfp-slice7-negated-nary-getvalue-design.md` (Status block)

- [ ] **Step 1: Full workspace test (background)**

Run in the background (multi-minute; do NOT loop subagents — run it yourself and poll):
```bash
cd /workspace
cargo test --workspace 2>&1 | tee /tmp/claude-1000/-workspace/scratch-slice7-test.log
```
Expected: 0 failed across all suites (incl. shinri-fp). Capture the suite-count summary.

- [ ] **Step 2: Full differential oracle sweep (background)**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --features oracle 2>&1 | tee /tmp/claude-1000/-workspace/scratch-slice7-oracle.log
```
Expected: every oracle green; all PRE-EXISTING suite counts byte-identical to the slice-6 baseline EXCEPT the newly-added `nary_arith_oracle` and the re-seeded `qfs_differential` family. Diff against the slice-6 numbers in the parent spec.

- [ ] **Step 3: Clippy net-new zero**

Run:
```bash
cd /workspace
cargo clippy --workspace --all-targets 2>&1 | grep -c "^warning" || true
```
Expected: warning count ≤ the slice-6 known set (solver=2 / fp=22 / parser=3 / theory=4 / str=9). Any NEW warning must be fixed.

- [ ] **Step 4: Canary sweep**

Re-run the Task 1 Step 6 grep and confirm every canary/pin that changed did so intentionally with a z3-verified target. No unexplained flips.

- [ ] **Step 5: Debug no-panic confirmation**

Run:
```bash
cd /workspace
cargo test -p shinri-solver --lib premature_sat_string_family_no_debug_panic -- --nocapture
```
Expected: PASS (debug build, no panic) — the I2 definition-of-done.

- [ ] **Step 6: Update the spec Status block**

Edit the design doc's `**Status:**` line from "Design — not yet implemented." to "Landed 2026-07-03" with: the commit range, the verification summary (workspace suite counts, the new oracle baselines with exact `sat/unsat/unknown/z3_checked`, clippy set, canary sweep clean), and — for I1 and I2 — which diagnosis branch was taken (I1: fold-only vs fold+str-polarity; I2: upstream-fix vs guarded-assert-per-site).

- [ ] **Step 7: Commit**

```bash
cd /workspace
git add docs/superpowers/specs/2026-07-03-shinri-qfbvfp-slice7-negated-nary-getvalue-design.md
git commit -m "docs(qfbvfp): mark slice-7 landed — C2/I1/I2 closed, item-4/5 get-value channels, oracle baselines (slice 7)"
```

---

## Self-Review

**Spec coverage:**
- C2 → Task 2. I1 → Task 3 (+ conditional str fix). I2 → Task 4. Item 4 → Task 5. Item 5 → Task 6.
- §3 pre-flight & canary hunt → Task 1. §3 ordering (soundness-first, I2 before string re-baseline) → task order 2→3→4→5→6→7, with Task 7 Step 3 gated on Task 4.
- §4 testing: e2e hard pins → Tasks 2/3/5/6; I2 debug pins → Task 4; differential oracle → Task 7; word_norm unit → Task 3. §5 verification → Task 8. §6 risks (diagnosis-gated I1/I2, TermId layout) → Task 3 Step 7, Task 4, and the ordering constraint.

**Placeholder scan:** All code steps carry concrete code. Two steps intentionally defer to live inspection with explicit fallbacks: Task 3 Step 3 (`run` entry-point/`ConstVal` shape — grep-and-adjust) and Task 6 Step 3 (scalar-value extractor diagnosis) — both name exactly what to confirm and the fallback if absent. These are diagnosis steps the spec's §6 flags as gated, not hidden work.

**Type consistency:** `orig_ite` / `orig_ite_map()` defined in Task 5, consumed in Task 6. `solve_qfabv_with_models` 3-tuple signature defined in Task 6 Step 4, all callers updated in Step 5. `run_outcome` (verdict-only) and `run_values` (collects get-value) used consistently. `mk_const_bool(false)`, `is_pure_arith`, `is_arith_sorted`, `ite_map()` all match the verified live signatures.
