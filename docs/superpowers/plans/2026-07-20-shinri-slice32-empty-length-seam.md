# Slice 32 — Empty-Length Seam Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Emit a two-literal emptiness tautology per bare string variable so an
arith-derived `len(x) = 0` grounds `x = ""` in the string theory's EUF.

**Architecture:** A new emission channel in `StrSolver::check`'s existing
per-len-term axiom pump (`crates/shinri-str/src/lib.rs:462-504`). For each
`str.len(a)` where `a` is a bare uninterpreted nullary string symbol, emit the
clause `(or (= a "") (>= (str.len a) 1))` exactly once, guard-free (it is a
tautology), with a per-atom phase hint preferring TRUE on the `≥ 1` disjunct so
the clause stays dormant until arith actually refutes it. Dedup rides the
existing `emitted_len_axioms` set. Nothing outside `shinri-str` changes.

**Tech Stack:** Rust 2021, `shinri-str` / `shinri-theory` / `shinri-core`,
`cargo nextest`, mise tasks, z3+cvc5 oracles.

## Global Constraints

- **Pure-Rust mandate:** no native-link dependencies. `deny.toml` bans `rug`,
  `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`. This slice adds no dependencies.
- **Formatting gate:** `cargo fmt --all` before every push; CI runs
  `cargo fmt --check` and fails fast.
- **Lint gate:** `cargo clippy --workspace --all-targets -- -D warnings` must
  be clean.
- **Blocking test tier budget:** 10–15 min wall-clock (CI hard cap 20 min).
  Any test measured >5 min must be `#[ignore]`d with
  `#[ignore = "exhaustive: nightly tier (~N min in CI)"]` plus a fast smoke
  companion on the blocking tier.
- **Oracle suites are feature-gated:** run with
  `cargo nextest run -p shinri-solver --features oracle`. **Without
  `--features oracle` these suites compile to zero tests** — a green run
  without the flag proves nothing. Always confirm a non-zero test count.
- **nextest filter syntax:** use `-E 'test(name)'`. The bare `mod::name`
  positional filter finds 0 tests on the pinned nextest, and a 0-test run
  reads as green.
- **Soundness posture:** anything not decided is `Unknown`, never a wrong
  `sat`/`unsat`. Verdict-monotonicity required: `Unknown → decided` flips are
  allowed; `decided → Unknown` and `sat ↔ unsat` are blockers.
- **Branch discipline:** work on branch `slice32-empty-length-seam`, PR to
  `main`, merge with a merge commit when CI is green, then delete the branch
  remote and local.

## Verified Baselines (measured 2026-07-20, pre-implementation)

These were measured on the current `main` (`fc717c63`). Do not re-derive; use
them as the before-numbers for the regression gate.

- `cargo nextest run -p shinri-str` → **211 tests run, 211 passed**, 0.243s
  summary / 0.940s wall.
- `cargo nextest run -p shinri-solver --test script_e2e` → **67 tests run, 67
  passed, 1 skipped**, 0.136s summary / 0.605s wall.
- The acceptance pin (Task 3) returns `unknown` on current `main`, and z3
  returns `unsat`. Confirmed by direct invocation of `target/debug/shinri`.

**Pins that do NOT work as acceptance criteria** — these already decide
`unsat` on current `main` via other channels (head-peeling, and the
`len_class_zero` read in the disequality loop at `lib.rs:506-508`). Do not use
them; they would produce a test that passes before the change and prove
nothing:

- `(<= (str.len x) 0) ∧ (= (str.++ x "a") "b")` — decided by head-peel.
- `(<= (str.len x) 0) ∧ (distinct x "")` — decided by `len_class_zero`.
- `(= (str.len x) 0) ∧ (str.in_re x (re.+ (str.to_re "a")))` — decided.

## File Structure

- **Modify** `crates/shinri-str/src/length.rs` — add the qualifier predicate
  and the clause builder. This file already owns per-`str.len` axiom
  construction (`ge_zero`, `defining_eq`, `arith_eq_companions`,
  `next_axiom`), so the new builder belongs beside them rather than in a new
  module. Its unit tests go in the existing `mod tests` at the file's end.
- **Modify** `crates/shinri-str/src/lib.rs` — add the emission channel to the
  axiom pump inside `check`, immediately after the existing `next_axiom` loop
  (`lib.rs:462-504`) and before the `len_class_zero` comment at
  `lib.rs:506-508`.
- **Modify** `crates/shinri-solver/tests/script_e2e.rs` — add the end-to-end
  acceptance pin.

No new files. No changes to `shinri-theory`, `shinri-sat`, the parser, or
preprocessing.

---

### Task 1: The qualifier predicate and clause builder in `length.rs`

**Files:**
- Modify: `crates/shinri-str/src/length.rs` (add after `ge_zero`, which ends
  at line 48)
- Test: `crates/shinri-str/src/length.rs` (the existing `mod tests` block
  beginning at line 263)

**Interfaces:**
- Consumes: nothing from earlier tasks. Uses existing `shinri_core` API:
  `Context::mk_app`, `Context::mk_eq`, `Context::mk_numeral`,
  `Context::mk_string_const`, `Context::string_const_value`,
  `Context::term_node`, `Context::children`, `Context::int_sort`.
- Produces: `pub fn empty_length_tautology(terms: &mut Context, len_term:
  TermId) -> Option<(TermId, TermId)>`. Returns `Some((eq_empty, ge_one))`
  where `eq_empty` is `(= a "")` and `ge_one` is `(>= (str.len a) 1)`, for a
  qualifying `len_term = (str.len a)`; `None` otherwise. Task 2 consumes this.

- [ ] **Step 1: Write the failing tests**

Add these three tests inside the existing `mod tests` block at the end of
`crates/shinri-str/src/length.rs` (after `emits_concat_length_axiom`, which
ends at line 390). Note the existing block's imports at lines 265-268 do not
include `TermId`/`super::*`; add `use super::empty_length_tautology;` at the
top of each test as shown, or add it to the module's import list.

```rust
    #[test]
    fn tautology_offered_for_bare_string_variable() {
        use super::empty_length_tautology;
        use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermNode};
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let sym = ctx.declare_fun("x", &[], str_s);
        let x = ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap();
        let len_x = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();

        let (eq_empty, ge_one) =
            empty_length_tautology(&mut ctx, len_x).expect("bare variable qualifies");

        // eq_empty must be (= x "").
        let empty = ctx.mk_string_const("");
        let expected_eq = ctx.mk_eq(x, empty).unwrap();
        assert_eq!(eq_empty, expected_eq, "first disjunct is (= x \"\")");

        // ge_one must be (>= (str.len x) 1).
        let int_s = ctx.int_sort();
        let one = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
        let expected_ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_x, one])
            .unwrap();
        assert_eq!(ge_one, expected_ge, "second disjunct is (>= (str.len x) 1)");

        // Sanity: the empty constant really is the empty string.
        assert!(matches!(
            ctx.term_node(empty),
            TermNode::Const { val: ConstVal::String(_), .. }
        ));
    }

    #[test]
    fn tautology_declined_for_concat_and_literal_lengths() {
        use super::empty_length_tautology;
        use shinri_core::{BuiltinOp, Context, Op};
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");

        // Concat length: len(x ++ y) must NOT qualify — a concat carries hidden
        // mandatory constant length and multiplies as the engine rewrites; this
        // is exactly the per-str.len flood the length.rs:254 note warns about.
        let cc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        let len_cc = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[cc]).unwrap();
        assert!(
            empty_length_tautology(&mut ctx, len_cc).is_none(),
            "concat length must not qualify"
        );

        // Literal length: len("ab") must NOT qualify — its length is already
        // pinned by the structural defining equation.
        let lit = ctx.mk_string_const("ab");
        let len_lit = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[lit]).unwrap();
        assert!(
            empty_length_tautology(&mut ctx, len_lit).is_none(),
            "literal length must not qualify"
        );
    }

    #[test]
    fn tautology_declined_for_non_len_term() {
        use super::empty_length_tautology;
        use shinri_core::{BuiltinOp, Context, Op};
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let sym = ctx.declare_fun("n", &[], int_s);
        let n = ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap();
        let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero]).unwrap();
        assert!(
            empty_length_tautology(&mut ctx, ge).is_none(),
            "a non-str.len term must not qualify"
        );
    }
```

- [ ] **Step 2: Run the tests to verify they fail**

```bash
cargo nextest run -p shinri-str -E 'test(tautology_)'
```

Expected: compilation FAILS with `cannot find function `empty_length_tautology`
in module `super``. (A compile failure is the correct red state here — the
function does not exist yet.) If instead you see "0 tests run", the filter
matched nothing; re-check the `-E 'test(...)'` syntax before proceeding.

- [ ] **Step 3: Write the implementation**

Insert into `crates/shinri-str/src/length.rs` immediately after `ge_zero`
(i.e. after line 48, before `defining_eq`):

```rust
/// For `str.len(a)` where `a` is a bare string VARIABLE, build the two
/// disjuncts of the emptiness tautology `(or (= a "") (>= (str.len a) 1))`.
/// Returns `None` for any other shape.
///
/// The clause is VALID in the SMT-LIB String theory for every string term: a
/// string is either empty or has length at least one. Being a tautology, it is
/// entailed at level 0 unconditionally and needs NO guard — unlike the
/// merge-derived length lemmas in this module, it has no antecedents that a
/// backtracked branch could invalidate.
///
/// Its purpose is to close the one-way N–O seam: arith owns lengths and the
/// string theory owns word equations, so when arith derives `len(a) = 0`
/// nothing today tells the string theory that `a = ""`. Under `len(a) ≤ 0` the
/// arith disjunct is false and unit propagation forces `a = ""` into EUF.
///
/// **Qualifier — bare leaf variables only.** `a` must be an uninterpreted
/// NULLARY symbol and not a string constant. Concat lengths, literal lengths,
/// and any compound are declined. This is the flood control: emission is then
/// bounded by the number of string variables rather than the number of
/// `str.len` terms, and concat lengths — the terms that multiply as the
/// word-equation engine rewrites — contribute nothing. Emitting an empty-link
/// for EVERY `str.len` term is the shape documented at the bottom of this file
/// as livelocking concat+length queries; do not widen this qualifier without
/// re-running the timing gate.
pub fn empty_length_tautology(
    terms: &mut Context,
    len_term: TermId,
) -> Option<(TermId, TermId)> {
    // Extract the single argument of the str.len application.
    let arg = match terms.term_node(len_term).clone() {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrLen),
            args,
            ..
        } => terms.children(args)[0],
        _ => return None,
    };

    // Qualifier: a bare uninterpreted nullary symbol, not a string constant.
    // Mirrors the `all_var` predicate the empty-residual lemma uses
    // (lib.rs:577-586) rather than inventing a second notion of leafness.
    let is_bare_var = terms.string_const_value(arg).is_none()
        && match terms.term_node(arg) {
            TermNode::App {
                op: Op::Uninterpreted(_),
                args,
                ..
            } => terms.children(*args).is_empty(),
            _ => false,
        };
    if !is_bare_var {
        return None;
    }

    let empty = terms.mk_string_const("");
    let eq_empty = terms.mk_eq(arg, empty).expect("(= a \"\") well-sorted");
    let int_s = terms.int_sort();
    let one = terms.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
    let ge_one = terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_term, one])
        .expect("(>= (str.len a) 1) well-sorted");
    Some((eq_empty, ge_one))
}
```

- [ ] **Step 4: Run the tests to verify they pass**

```bash
cargo nextest run -p shinri-str -E 'test(tautology_)'
```

Expected: `3 tests run: 3 passed`. Confirm the count is 3 — not 0.

- [ ] **Step 5: Run the full crate suite to confirm no regression**

```bash
cargo nextest run -p shinri-str
```

Expected: `214 tests run: 214 passed` (211 baseline + 3 new).

- [ ] **Step 6: Format, lint, and commit**

```bash
cargo fmt --all
cargo clippy -p shinri-str --all-targets -- -D warnings
git add crates/shinri-str/src/length.rs
git commit -m "feat(str): slice32 T1 — emptiness tautology builder for bare string variables"
```

---

### Task 2: Wire the emission channel into the axiom pump

**Files:**
- Modify: `crates/shinri-str/src/lib.rs:462-508` (insert a new loop after the
  existing `next_axiom` loop, before the `len_class_zero` comment)
- Test: `crates/shinri-str/src/lib.rs` — add to the crate's existing test
  module, or `crates/shinri-str/src/length.rs`'s `mod tests` if the solver-level
  test harness there is more convenient (it already constructs `StrSolver`,
  `EqualityEngine`, `AtomRegistry`, and `TheoryCtx` — see
  `emits_literal_length_axiom` at length.rs:270 for the exact setup shape).

**Interfaces:**
- Consumes: `length::empty_length_tautology(terms, len_term) ->
  Option<(TermId, TermId)>` from Task 1.
- Produces: no new public API. Behavioural contract for Task 3: for each bare
  string variable reachable through `self.len_terms`, `check` returns exactly
  one `TCheck::Split { atoms: vec![eq_empty, ge_one], guard: None, phases:
  vec![None, Some(true)] }` per solve, deduplicated via
  `self.emitted_len_axioms`.

- [ ] **Step 1: Write the failing test**

Add to the `mod tests` block at the end of `crates/shinri-str/src/length.rs`:

```rust
    #[test]
    fn emits_emptiness_tautology_once_per_bare_variable() {
        use shinri_core::{BuiltinOp, Context, Op};
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let sym = ctx.declare_fun("x", &[], str_s);
        let x = ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap();
        let len_x = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_x, zero])
            .unwrap();

        let empty = ctx.mk_string_const("");
        let expected_eq = ctx.mk_eq(x, empty).unwrap();
        let one = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
        let expected_ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_x, one])
            .unwrap();

        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);

        // Drive to fixpoint, counting emissions of the two-literal tautology.
        let mut taut_count = 0;
        for _ in 0..16 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split {
                    atoms: a,
                    guard,
                    phases,
                } => {
                    if a.len() == 2 && a[0] == expected_eq && a[1] == expected_ge {
                        taut_count += 1;
                        assert!(guard.is_none(), "a tautology needs no guard");
                        assert_eq!(
                            phases,
                            vec![None, Some(true)],
                            "phase hint prefers TRUE on the (>= len 1) disjunct"
                        );
                    }
                }
                TCheck::Sat => break,
                TCheck::Conflict(_) => panic!("no conflict expected"),
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
            }
        }
        assert_eq!(
            taut_count, 1,
            "the emptiness tautology is emitted exactly once per bare variable"
        );
    }
```

- [ ] **Step 2: Run the test to verify it fails**

```bash
cargo nextest run -p shinri-str -E 'test(emits_emptiness_tautology_once_per_bare_variable)'
```

Expected: FAIL with `assertion `left == right` failed: the emptiness tautology
is emitted exactly once per bare variable`, showing `left: 0, right: 1`. The
builder from Task 1 exists but nothing calls it yet.

- [ ] **Step 3: Write the implementation**

In `crates/shinri-str/src/lib.rs`, insert this loop immediately after the
closing brace of the existing `next_axiom` `for lt in lens` loop (which ends at
line 504) and before the `len_class_zero` comment at line 506:

```rust
        // Emptiness tautology (slice 32): `(or (= a "") (>= (str.len a) 1))`
        // for each bare string VARIABLE `a`. Closes the one-way N–O seam —
        // arith owns lengths, so a derived `len(a) = 0` otherwise never reaches
        // this theory's EUF as `a = ""`. Under `len(a) ≤ 0` the arith disjunct
        // dies and propagation forces the merge.
        //
        // Guard-free: the clause is VALID for every string term, so unlike the
        // merge-derived lemmas above it has no antecedent that a backtracked
        // branch could invalidate (no E1 / side_clean / leaves_all_dl0 gate is
        // needed or correct here).
        //
        // The phase hint prefers TRUE on the `≥ 1` disjunct, so the SAT layer's
        // default guess leaves the clause satisfied and DORMANT; the `a = ""`
        // branch is entered only when arith actually refutes it. That is what
        // makes this behave demand-driven without a value-view seam into arith.
        let taut_lens: Vec<TermId> = self.len_terms.iter().copied().collect();
        for lt in taut_lens {
            if let Some((eq_empty, ge_one)) = length::empty_length_tautology(cx.terms, lt) {
                // Dedup on the `≥ 1` disjunct: it is unique per len term, so one
                // key suffices and rides the existing emitted-axiom set.
                if self.emitted_len_axioms.contains(&ge_one) {
                    continue;
                }
                // Spend fuel FIRST; only record as emitted if the split is
                // actually delivered (tracks-only-delivered-axioms invariant,
                // matching the next_axiom loop above).
                if !self.fuel.spend() {
                    return TCheck::Unknown;
                }
                self.emitted_len_axioms.insert(ge_one);
                return TCheck::Split {
                    atoms: vec![eq_empty, ge_one],
                    guard: None,
                    phases: vec![None, Some(true)],
                };
            }
        }
```

- [ ] **Step 4: Run the test to verify it passes**

```bash
cargo nextest run -p shinri-str -E 'test(emits_emptiness_tautology_once_per_bare_variable)'
```

Expected: `1 test run: 1 passed`.

- [ ] **Step 5: Run the full crate suite**

```bash
cargo nextest run -p shinri-str
```

Expected: `215 tests run: 215 passed`. If any previously-passing test now
fails, STOP — do not adjust the failing test to match new behaviour. A
`decided → Unknown` or `sat ↔ unsat` move is a blocker under the global
constraints; diagnose it before continuing.

- [ ] **Step 6: Format, lint, and commit**

```bash
cargo fmt --all
cargo clippy -p shinri-str --all-targets -- -D warnings
git add crates/shinri-str/src/lib.rs crates/shinri-str/src/length.rs
git commit -m "feat(str): slice32 T2 — emit emptiness tautology from the axiom pump"
```

---

### Task 3: End-to-end acceptance pin

**Files:**
- Modify: `crates/shinri-solver/tests/script_e2e.rs` (append a new test; the
  file's `run_script` helper is defined at lines 6-24)

**Interfaces:**
- Consumes: the behaviour from Task 2, through the full parser → solver stack.
  No direct API use.
- Produces: nothing consumed by later tasks.

- [ ] **Step 1: Write the failing test**

Append to `crates/shinri-solver/tests/script_e2e.rs`:

```rust
/// Slice 32 — the empty-length seam. `len(x) ≤ 0 ∧ x·y = "ab" ∧ y ≠ "ab"` is
/// UNSAT: the length bound forces `x = ""`, so `y = "ab"`, contradicting the
/// disequality. Before slice 32 this returned `unknown` — arith derived
/// `len(x) = 0` but nothing carried `x = ""` across the N–O seam into the
/// word-equation engine, so the concat never ground out.
///
/// This specific shape is load-bearing. Simpler candidates already decide via
/// OTHER channels and would pass without the fix, proving nothing:
///   * `len(x) ≤ 0 ∧ x·"a" = "b"`      — decided by head-peeling.
///   * `len(x) ≤ 0 ∧ x ≠ ""`           — decided by the `len_class_zero` read
///                                        in the disequality loop.
/// Verdict confirmed `unsat` by the z3 oracle.
#[test]
fn str_empty_length_seam_grounds_word_equation() {
    let out = run_script(
        "(set-logic QF_SLIA)\
         (declare-fun x () String)\
         (declare-fun y () String)\
         (assert (<= (str.len x) 0))\
         (assert (= (str.++ x y) \"ab\"))\
         (assert (distinct y \"ab\"))\
         (check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
}
```

- [ ] **Step 2: Run the test to verify it fails**

Check out the pre-Task-2 state to confirm the red baseline, then return:

```bash
git stash
cargo nextest run -p shinri-solver --test script_e2e -E 'test(str_empty_length_seam_grounds_word_equation)'
```

Expected on stashed (pre-fix) state: FAIL — `left: ["unknown"], right:
["unsat"]`. Then restore:

```bash
git stash pop
```

(If you prefer not to stash, the baseline is already recorded in this plan:
the pin returns `unknown` on `main` at `fc717c63`, verified by direct
invocation of `target/debug/shinri`.)

- [ ] **Step 3: Run the test against the implemented state**

```bash
cargo nextest run -p shinri-solver --test script_e2e -E 'test(str_empty_length_seam_grounds_word_equation)'
```

Expected: `1 test run: 1 passed`.

If it still returns `unknown`, the tautology is being emitted but not
propagating. Diagnose before proceeding — do NOT weaken the pin. The likely
causes, in order: (a) the `≥ 1` disjunct is not routing to Arith (check it is
built as a `Ge` over the `str.len` term, matching the `arith_eq_companions`
seam note at length.rs:8-12); (b) `x`'s `str.len` term never entered
`self.len_terms` (check `collect::collect` reached it); (c) the phase hint is
pinning the wrong polarity (temporarily set `phases: vec![None, None]` and
re-run — if it then decides, the hint's polarity is inverted).

- [ ] **Step 4: Run the full e2e suite**

```bash
cargo nextest run -p shinri-solver --test script_e2e
```

Expected: `68 tests run: 68 passed, 1 skipped` (67 baseline + 1 new).

- [ ] **Step 5: Format and commit**

```bash
cargo fmt --all
git add crates/shinri-solver/tests/script_e2e.rs
git commit -m "test(str): slice32 T3 — e2e pin, arith-derived zero length grounds the word equation"
```

---

### Task 4: Livelock-regression timing gate and oracle differential

This task has no new production code. Its deliverable is evidence that the
flood hazard did not materialize — the one risk the spec flags as empirical
rather than structural.

**Files:**
- No source changes expected. If the oracle diff surfaces a regression, fix it
  in `crates/shinri-str/src/` and note it here.

**Interfaces:**
- Consumes: the complete implementation from Tasks 1-3.
- Produces: measured before/after numbers for the truth-up section.

- [ ] **Step 1: Time the string unit suite and compare to baseline**

```bash
time cargo nextest run -p shinri-str
```

Expected: `215 tests run: 215 passed`. Baseline wall-clock was **0.940s** for
211 tests. A move into multiple seconds means the clause is multiplying —
STOP and re-check the Task 1 qualifier (concat lengths must be declined).

- [ ] **Step 2: Time the e2e suite and compare to baseline**

```bash
time cargo nextest run -p shinri-solver --test script_e2e
```

Expected: `68 tests run: 68 passed, 1 skipped`. Baseline wall-clock was
**0.605s** for 67 tests. The concat+length tests the `length.rs:254` livelock
note was written about live in this suite — among them
`str_var_eq_concat_length_link_model_is_self_consistent` (0.028s baseline) and
`str_e1_wrong_unsat_regression_pins` (0.067s baseline). Confirm each is still
sub-second in the per-test output; a hang or multi-second jump on either is the
livelock reappearing and is a blocker.

- [ ] **Step 3: Run the oracle differential suite in the FOREGROUND**

```bash
cargo nextest run -p shinri-solver --features oracle --no-capture 2>&1 | tee /tmp/claude-1000/-workspace/712d9fce-cad5-4a18-9dcf-734bf863cca5/scratchpad/slice32-oracle.log
```

`--features oracle` is mandatory: without it these suites compile to **zero
tests** and the run is green while proving nothing. `--no-capture` is mandatory
for any dump-and-diff output: `eprintln` is swallowed on passing runs, yielding
0 lines that still read as "green".

Expected: a non-zero test count in the summary line. **Before trusting the
result, confirm the count is non-zero and the log is non-empty:**

```bash
wc -l /tmp/claude-1000/-workspace/712d9fce-cad5-4a18-9dcf-734bf863cca5/scratchpad/slice32-oracle.log
```

- [ ] **Step 4: Adjudicate any verdict flips**

Review the oracle log for disagreements. Apply the standing rule:

- `Unknown → decided` (shinri now decides what it previously could not), with
  the verdict matching z3/cvc5 → **adjudicated flip, expected**. This slice
  shifts completeness; such flips are the point, not a blocker. Record each in
  the truth-up.
- `decided → Unknown` → **blocker**. Diagnose; do not proceed.
- `sat ↔ unsat` against the oracle → **P0 blocker**. Stop all work and
  diagnose; this is a soundness bug.

If a pin in the suite must be updated because shinri now decides it, update the
pin to the oracle-confirmed verdict and record the flip — never relax a pin to
`unknown` to make the suite pass.

- [ ] **Step 5: Run the full blocking CI tier**

```bash
mise run ci
```

Expected: green — fmt check, clippy, dependency policy, secret scan, and the
fast test suite. Wall-clock must stay inside the 10–15 min budget.

- [ ] **Step 6: Commit any fixes surfaced by this task**

If Steps 1-5 required source changes:

```bash
cargo fmt --all
git add -A
git commit -m "fix(str): slice32 T4 — <what the gate surfaced>"
```

If no changes were needed, skip the commit and note "gate clean, no fixes" in
the truth-up.

---

### Task 5: Truth-up the spec and open the PR

**Files:**
- Modify:
  `docs/superpowers/specs/2026-07-20-shinri-slice32-empty-length-seam-design.md`
  (append an "Implementation notes (truth-up)" section, matching the convention
  used by slices 25-31 — see the slice-27 spec's section of that name for the
  established shape)

**Interfaces:**
- Consumes: the measured results from Task 4.
- Produces: the merged slice.

- [ ] **Step 1: Append the truth-up section to the spec**

Write an "## Implementation notes (truth-up)" section recording, concretely:

- The branch name and base commit.
- What landed as designed, with the commit SHA per task.
- Any deviation from the design, and why. If the qualifier, the phase-hint
  polarity, or the dedup key changed during implementation, say so explicitly
  and state what the spec claimed versus what shipped.
- The measured before/after timings from Task 4 Steps 1-2, as numbers.
- Every oracle verdict flip from Task 4 Step 4, with its adjudication.
- **Newly banked:** anything the work surfaced that is not being fixed here.
  If nothing, write "nothing" — the standing bank (slice-28 §8, slice-27
  typed-antecedent refactor, slice-29 approach-C, and slice-31 §11's remaining
  walls 1/2/4) carries forward unchanged.
- Whether slice-31 §11's wall 3 is now closed, and an explicit restatement that
  walls 1, 2, and 4 remain open and the order preprocessing fence stays down.

- [ ] **Step 2: Commit the truth-up**

```bash
git add docs/superpowers/specs/2026-07-20-shinri-slice32-empty-length-seam-design.md
git commit -m "docs: slice32 truth-up"
```

- [ ] **Step 3: Push and open the PR**

```bash
git push -u origin slice32-empty-length-seam
gh pr create --title "Slice 32 — empty-length seam" --body "$(cat <<'EOF'
Emits `(or (= x "") (>= (str.len x) 1))` per bare string variable, closing the
one-way N-O seam where an arith-derived `len(x) = 0` never reached the string
theory's EUF as `x = ""`.

Cashes slice-31 §11 wall 3 — the one wall that analysis identified as cheap,
reusable, and spike-validated. Walls 1, 2, and 4 remain open; the order
preprocessing fence stays down.

The clause is a tautology, so it is guard-free and adds no wrong-UNSAT surface.
Flood control is the bare-leaf-variable qualifier: emission is bounded by
variable count, not `str.len`-term count. Timing evidence against the
documented concat+length livelock is in the spec truth-up.

First load-bearing consumer of the slice-31b phase-hint channel.
EOF
)"
```

- [ ] **Step 4: Merge when CI is green**

Per the standing merge-on-green rule, once CI passes:

```bash
gh pr merge --merge
git checkout main && git pull
git branch -d slice32-empty-length-seam
git push origin --delete slice32-empty-length-seam
git remote prune origin
```

---

## Self-Review

**Spec coverage.** §1 (problem + emission mechanism) → Tasks 1-2. §1.1's
qualifier, dedup, phase hint, and guard-free clause → Task 1 Step 3 and Task 2
Step 3. §2's soundness argument is structural and needs no task; §2's flood
control → the Task 1 qualifier plus the Task 4 timing gate; §2's termination →
the `fuel.spend()` call in Task 2 Step 3; §2's empirical gate → Task 4. §3's
banked non-goals → Task 5 Step 1 restates them. §4's five test categories →
Task 1 (unit), Task 3 (integration), Task 4 Steps 1-2 (regression), Task 4
Step 3 (oracle), Task 4 Step 2 + Step 5 (`script_e2e`). No gaps.

**Placeholder scan.** No TBDs. Every code step carries complete code. The one
prose-only step (Task 5 Step 1) enumerates the exact facts to record, because
its content depends on measurements that do not exist until Task 4 runs. The
Task 4 Step 6 and Task 5 Step 1 conditionals specify what to write in both
branches.

**Type consistency.** `empty_length_tautology(terms: &mut Context, len_term:
TermId) -> Option<(TermId, TermId)>` is defined in Task 1 and called with that
exact signature and return destructuring in Task 2. The `TCheck::Split` payload
uses `atoms` / `guard` / `phases`, matching `solver_trait.rs:31-36`. Dedup uses
`self.emitted_len_axioms` (an `FxHashSet<TermId>`, `lib.rs:60`), keyed on
`ge_one`, consistently in Task 2's implementation and its test.

**One correction folded in during review.** The spec's §4 suggested
`(<= (str.len x) 0) ∧ (= (str.++ x "a") "b")` as the integration pin. Direct
measurement showed it already decides `unsat` on `main` via head-peeling, so it
would have passed before the change. Task 3 uses the verified-`unknown` shape
instead and documents the rejected candidates so no one reintroduces them.
