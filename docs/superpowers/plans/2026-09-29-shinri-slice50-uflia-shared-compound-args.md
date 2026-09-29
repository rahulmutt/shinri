# Slice 50 — QF_UFLIA: define compound shared arithmetic terms; eager ⊤≠⊥ — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stop shinri answering `sat` on QF_UFLIA/QF_UFLRA inputs where a UF is applied to a compound arithmetic argument (`f(a+1)`). Separately, make EUF's ⊤≠⊥ disequality survive backtracking.

**Architecture:** Today `Arith::ensure_shared_var` interns a compound shared term such as `(+ a 1)` as a fresh, unconstrained problem variable. Nothing ties it to `a`, and slice 42's constrainedness filter then hides it from entailment and MBTC. The fix linearizes the term and installs a permanent tableau row `v_t − Σqᵢxᵢ = c` over a slack pinned to `[c, c]`, re-pinned at every final check exactly like numeral pins, and marks `v_t` constrained. Separately, a new `TheorySolver::install_truth_terms` seam lets the solver install ⊤/⊥ and EUF's ⊤≠⊥ at level 0 before any atom is encoded, so a mid-search `bind_fresh` can no longer scope it to a decision level.

**Tech Stack:** Rust workspace, `mise` tasks, `cargo nextest` 0.9.140, z3/cvc5 from mise behind the `oracle` cargo feature (`easy-smt` harness), `shinri-bench` for corpus runs.

**Spec:** `docs/superpowers/specs/2026-09-29-shinri-slice50-uflia-shared-compound-args-design.md`. Read it alongside this plan. §1.3 is the mechanism, §3 the arith fix, §4 the sentinel fix, §5 the tasks, §7 the measurement and success criteria.

## Global Constraints

- **Branch:** all work goes on `slice50-uflia-shared-compound-args`, branched from `main` at the commit that adds this plan (the spec+plan pair). Open a PR to `main` and merge with a merge commit when CI is green, then delete the branch remote and local.
- **Pure-Rust mandate:** no native-link dependencies. `deny.toml` bans `rug`, `gmp-mpfr-sys`, `z3-sys`, `cadical-rs`. This slice adds **no** dependency of any kind.
- **Shared core:** `shinri-arith` and `shinri-euf` back every logic that runs the N-O exchange. The full **unfiltered** oracle run (`cargo nextest run -p shinri-solver --features oracle`) is a gate.
- **Oracle feature gate:** `crates/shinri-solver/tests/oracle.rs` is `#![cfg(feature = "oracle")]`. Every oracle command carries `--features oracle`. **Without it the file compiles to zero tests and the run reads as green.** Always confirm a non-zero discovered count.
- **nextest filters:** expression form only. `-E 'test(<name>)'` selects by test name, and `-E 'binary(<name>)'` selects an integration-test binary. A positional `mod::name` filter matches nothing on nextest 0.9.140.
- **Formatting gate:** `cargo fmt --all` before every push. CI runs `cargo fmt --check` and fails fast.
- **Lint gate:** `cargo clippy --workspace --all-targets -- -D warnings` must be clean (`mise run lint` covers fmt + clippy).
- **Test tier:** nothing new may take more than 5 minutes. Never remove `#[ignore]` from the `shinri-fp` exhaustive suites.
- **Tests before fixes:** Task 1 commits tests that stay **red** on the branch until Task 2 lands. Do not push before Task 5. Each "must fail on `main`" step records the verbatim failure output in the task report.
- **Never weaken a test to get green.** If a test that must pass after the fix still fails, the failing input is evidence. Minimize it and trace it to a named code path before changing anything.
- **Step-up trigger (spec §5, Task 1):** if `xs-05-08-4-2-5-4.smt2` still answers `sat` after Task 2, **stop**. The slice steps up to approach B (spec §9), and the spec is amended with the user before continuing.

**Ordering note.** Spec §5 has five tasks. The plan maps them as spec 1 → plan 1; spec 2 → plan 2, which also carries spec 1's Wisa confirmation because that is only observable once the fix is in; spec 3 → plan 3; spec 4 → plan 4; spec 5 → plan 6. Plan 5 (gates + PR) and plan 7 (whole-branch review + merge) follow the repo convention used by slices 47–49.

## Review Focus

These are the input classes spec §1–§3 imply but do not name. A person writing QF_UFLIA/QF_UFLRA will hit them first. Each has a test in the task that owns the code:

1. **Two structurally different compound arguments that are only arithmetically equal** (`a = b + 1`, `f(a+1) ≠ f(b+2)`) must be `unsat`. This needs entailment *between two defined shared variables*, not just against a numeral. (`a = b`, `f(a+1) ≠ f(b+1)` is already `unsat` on `main`, because EUF congruence over `+` handles it without arithmetic, so it would not test the fix.) → Task 1, `slice50_two_compound_args_equal_unsat`.
2. **A compound argument that cancels to a constant** (`f(a − a)`) must equal `f(0)`. This is the degenerate `comb == [(v, 1)]` branch. → Task 1, `slice50_cancelling_arg_unsat`.
3. **A UF application nested inside a compound argument** (`f(g(a+1) + 1)`) must work. The inner UF app is a linearization leaf and must be the *same* arith variable as its own shared var. → Task 1, `slice50_nested_uf_leaf_unsat`.
4. **A compound argument that is genuinely free** (`a = 0`, `f(1) = 5`, `f(a+2) ≠ 5`) must stay `sat`. The row must not over-constrain. → Task 1, `slice50_compound_arg_sat_direction`.
5. **A nonlinear compound argument** (`f(a*a)`) is outside QF_UFLIA. It must not reach `linearize`'s "nonlinear reached normalize" debug assertion; it stays opaque, as today. → Task 1, `slice50_nonlinear_arg_does_not_panic`. This is a guard, not a red test.

## File Structure

| file | responsibility | task |
| --- | --- | --- |
| `crates/shinri-solver/tests/uflia_e2e.rs` | e2e pins: spec §1.2, its variants, Review Focus 1–5 | 1 |
| `crates/shinri-solver/tests/uflra_e2e.rs` | e2e pin: Real-sorted compound argument | 1 |
| `crates/shinri-arith/src/lib.rs` | production: `ensure_shared_var` gains the compound branch, plus `define_shared_compound`, `is_compound_arith`, `is_linear_arith`; unit tests in `nelson_oppen_tests` | 1, 2 |
| `crates/shinri-arith/src/normalize.rs` | `linearize` and `canonicalize` become `pub(crate)` | 2 |
| `crates/shinri-theory/src/solver_trait.rs` | new seam `TheorySolver::install_truth_terms` (default no-op) | 3 |
| `crates/shinri-theory/src/combiner.rs` | `Combiner::install_truth_terms` | 3 |
| `crates/shinri-theory/src/eq_engine.rs` | `EqualityEngine::level()` | 3 |
| `crates/shinri-euf/src/solver.rs` | `Euf::install_truth_terms`; I1 comment rewrite; unit tests | 3 |
| `crates/shinri-euf/src/egraph.rs` | base-level `debug_assert` in `truth_nodes` | 3 |
| `crates/shinri-euf/tests/qfuf_euf.rs` | combiner-level sentinel test | 3 |
| `crates/shinri-solver/src/lib.rs` | call `install_truth_terms` in place of `set_truth_terms` | 3 |
| `crates/shinri-solver/tests/oracle.rs` | new generator `differential_qf_uflia_compound_args` | 4 |
| `docs/superpowers/research/2026-09-29-smtlib-2024-slice50-uflia-report.md` (new) | the measured outcome | 6 |
| `docs/superpowers/specs/2026-09-29-shinri-slice50-uflia-shared-compound-args-design.md` | append `## 12. Measured outcomes` | 6 |

---

### Task 0: Branch

- [ ] **Step 1: Publish the spec+plan pair and branch**

```bash
git checkout main
git log --oneline -2   # the spec commit (d1ca800) and the plan commit
git push origin main
git checkout -b slice50-uflia-shared-compound-args
```

The planning step committed the spec and the plan to `main` locally. This step publishes the pair and branches from it.

---

### Task 1: Red tests — e2e pins and arith unit tests

These tests encode spec §1.2, its variant table, and Review Focus 1–5. All but the nonlinear guard must fail on `main`.

**Files:**
- Modify: `crates/shinri-solver/tests/uflia_e2e.rs` (append)
- Modify: `crates/shinri-solver/tests/uflra_e2e.rs` (append)
- Modify: `crates/shinri-arith/src/lib.rs` (append inside `mod nelson_oppen_tests`, which starts at `:1764`)

**Interfaces:**
- Consumes: `Solver::{new, int_sort, real_sort, declare_const, declare_fun, numeral, app, eq, assert, check_sat}`; the existing `uflia_e2e.rs` helpers `int_const`, `int_num`, `int_fun1` and `uflra_e2e.rs` helpers `real_const`, `real_num`, `real_fun1`; the arith test `Harness` (`assert_atom`, `ctx`, `arith`), `int_var_no`, `pairset`, `dr`.
- Produces: nothing that later tasks call. Task 2 turns these tests green.

- [ ] **Step 1: Append the e2e tests to `crates/shinri-solver/tests/uflia_e2e.rs`**

```rust
// ----- Slice 50: compound UF arguments (spec §1.2, Review Focus 1–5) -----

/// Assert `a = a_val`, `f(k) = 5`, `¬(f(arg) = 5)` with `arg = build(s, a)`,
/// and return the verdict. `build` may declare and assert extra context.
fn slice50_case(
    a_val: i128,
    k: i128,
    build: impl FnOnce(&mut Solver, shinri_core::TermId) -> shinri_core::TermId,
) -> SolveOutcome {
    let mut s = Solver::new();
    let a = int_const(&mut s, "a");
    let f = int_fun1(&mut s, "f");
    let av = int_num(&mut s, a_val);
    let kn = int_num(&mut s, k);
    let five = int_num(&mut s, 5);
    let arg = build(&mut s, a);
    let fk = s.app(Op::Uninterpreted(f), &[kn]);
    let farg = s.app(Op::Uninterpreted(f), &[arg]);
    let a_eq = s.eq(a, av);
    let fk_eq = s.eq(fk, five);
    let farg_eq = s.eq(farg, five);
    let not_farg = s.app(Op::Builtin(BuiltinOp::Not), &[farg_eq]);
    s.assert(a_eq);
    s.assert(fk_eq);
    s.assert(not_farg);
    s.check_sat()
}

/// Spec §1.2: a=0 ∧ f(1)=5 ∧ ¬f(a+1)=5 ⇒ UNSAT (z3: unsat). Was `sat` with
/// `(+ a 1) ↦ 0`: the compound argument had no arithmetic definition.
#[test]
fn slice50_compound_arg_add_unsat() {
    let got = slice50_case(0, 1, |s, a| {
        let one = int_num(s, 1);
        s.app(Op::Builtin(BuiltinOp::Add), &[a, one])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Spec §1.2 variant: a=1 ∧ f(1)=5 ∧ ¬f(a+0)=5 ⇒ UNSAT (z3: unsat).
#[test]
fn slice50_compound_arg_add_zero_unsat() {
    let got = slice50_case(1, 1, |s, a| {
        let zero = int_num(s, 0);
        s.app(Op::Builtin(BuiltinOp::Add), &[a, zero])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Spec §1.2 variant: a=0 ∧ f(0)=5 ∧ ¬f(2·a)=5 ⇒ UNSAT (z3: unsat).
#[test]
fn slice50_compound_arg_mul_unsat() {
    let got = slice50_case(0, 0, |s, a| {
        let two = int_num(s, 2);
        s.app(Op::Builtin(BuiltinOp::Mul), &[two, a])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// The Wisa shape `(- (- fmt1 2) fmt0)`: a=3 ∧ b=0 ∧ f(1)=5 ∧ ¬f((a−2)−b)=5
/// ⇒ UNSAT (z3: unsat).
#[test]
fn slice50_compound_arg_nested_sub_unsat() {
    let got = slice50_case(3, 1, |s, a| {
        let b = int_const(s, "b");
        let zero = int_num(s, 0);
        let two = int_num(s, 2);
        let b_eq = s.eq(b, zero);
        s.assert(b_eq);
        let a2 = s.app(Op::Builtin(BuiltinOp::Sub), &[a, two]);
        s.app(Op::Builtin(BuiltinOp::Sub), &[a2, b])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Review Focus 2: a=7 ∧ f(0)=5 ∧ ¬f(a−a)=5 ⇒ UNSAT (z3: unsat). The row
/// cancels to `v = 0` (the degenerate `comb == [(v, 1)]` branch).
#[test]
fn slice50_cancelling_arg_unsat() {
    let got = slice50_case(7, 0, |s, a| s.app(Op::Builtin(BuiltinOp::Sub), &[a, a]));
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Review Focus 3: a=0 ∧ g(1)=4 ∧ f(5)=5 ∧ ¬f(g(a+1)+1)=5 ⇒ UNSAT (z3: unsat).
/// `g(a+1)` is a linearization leaf and must share its arith var with the
/// shared term `g(a+1)`; `a+1` is itself a defined compound.
#[test]
fn slice50_nested_uf_leaf_unsat() {
    let got = slice50_case(0, 5, |s, a| {
        let g = int_fun1(s, "g");
        let one = int_num(s, 1);
        let four = int_num(s, 4);
        let g1 = s.app(Op::Uninterpreted(g), &[one]);
        let g1_eq = s.eq(g1, four);
        s.assert(g1_eq);
        let a1 = s.app(Op::Builtin(BuiltinOp::Add), &[a, one]);
        let ga1 = s.app(Op::Uninterpreted(g), &[a1]);
        s.app(Op::Builtin(BuiltinOp::Add), &[ga1, one])
    });
    assert_eq!(got, SolveOutcome::Unsat);
}

/// Review Focus 4: a=0 ∧ f(1)=5 ∧ ¬f(a+2)=5 ⇒ SAT (z3: sat). f(2) is free; the
/// definitional row must not over-constrain.
#[test]
fn slice50_compound_arg_sat_direction() {
    let got = slice50_case(0, 1, |s, a| {
        let two = int_num(s, 2);
        s.app(Op::Builtin(BuiltinOp::Add), &[a, two])
    });
    assert_eq!(got, SolveOutcome::Sat);
}

/// Review Focus 1: a=b+1 ∧ ¬(f(a+1)=f(b+2)) ⇒ UNSAT (z3: unsat). The two
/// arguments are structurally different and neither is a numeral: only an
/// arith entailment between two DEFINED shared vars can merge them. (`a=b` with
/// `f(a+1)` vs `f(b+1)` is already unsat on `main` via EUF congruence over `+`.)
#[test]
fn slice50_two_compound_args_equal_unsat() {
    let mut s = Solver::new();
    let a = int_const(&mut s, "a");
    let b = int_const(&mut s, "b");
    let f = int_fun1(&mut s, "f");
    let one = int_num(&mut s, 1);
    let two = int_num(&mut s, 2);
    let b_plus_1 = s.app(Op::Builtin(BuiltinOp::Add), &[b, one]);
    let a1 = s.app(Op::Builtin(BuiltinOp::Add), &[a, one]);
    let b2 = s.app(Op::Builtin(BuiltinOp::Add), &[b, two]);
    let fa1 = s.app(Op::Uninterpreted(f), &[a1]);
    let fb2 = s.app(Op::Uninterpreted(f), &[b2]);
    let a_eq = s.eq(a, b_plus_1);
    let ff = s.eq(fa1, fb2);
    let not_ff = s.app(Op::Builtin(BuiltinOp::Not), &[ff]);
    s.assert(a_eq);
    s.assert(not_ff);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

/// Review Focus 5 (guard, not red): a nonlinear argument is outside QF_UFLIA.
/// It must stay opaque and must not reach `linearize`'s "nonlinear reached
/// normalize" debug assertion. Any verdict is acceptable; a panic is not.
#[test]
fn slice50_nonlinear_arg_does_not_panic() {
    let _ = slice50_case(0, 0, |s, a| s.app(Op::Builtin(BuiltinOp::Mul), &[a, a]));
}
```

- [ ] **Step 2: Append the Real-sorted pin to `crates/shinri-solver/tests/uflra_e2e.rs`**

```rust
/// Slice 50 (spec §1.4): the compound-argument defect in QF_UFLRA.
/// x = 1/2 ∧ f(1) = 5 ∧ ¬(f(x + 1/2) = 5) ⇒ UNSAT (z3: unsat).
#[test]
fn slice50_real_compound_arg_unsat() {
    let mut s = Solver::new();
    let x = real_const(&mut s, "x");
    let f = real_fun1(&mut s, "f");
    let real = s.real_sort();
    let half = s.numeral(Rational::new(1i128.into(), 2i128.into()), real);
    let one = real_num(&mut s, 1);
    let five = real_num(&mut s, 5);
    let xh = s.app(Op::Builtin(BuiltinOp::Add), &[x, half]);
    let f1 = s.app(Op::Uninterpreted(f), &[one]);
    let fxh = s.app(Op::Uninterpreted(f), &[xh]);
    let x_eq = s.eq(x, half);
    let f1_eq = s.eq(f1, five);
    let fxh_eq = s.eq(fxh, five);
    let not_fxh = s.app(Op::Builtin(BuiltinOp::Not), &[fxh_eq]);
    s.assert(x_eq);
    s.assert(f1_eq);
    s.assert(not_fxh);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}
```

If `Rational::new` does not accept `i128` via `.into()`, use the constructor `shinri_num::Integer` exposes for small ints (see `crates/shinri-num/src/integer.rs`). Do not change the value 1/2.

- [ ] **Step 3: Append the arith unit tests inside `mod nelson_oppen_tests` in `crates/shinri-arith/src/lib.rs`**

Place them after `numeral_pin_constrains`, beside the other slice-42 tests.

```rust
    // ----- Slice 50: compound shared terms (spec §3) -----

    fn int_num_no(ctx: &mut Context, n: i128) -> TermId {
        let int = ctx.int_sort();
        ctx.mk_numeral(Rational::from_int(n.into()), int)
    }

    /// Builds `a <= 0 ∧ a >= 0` (vars 0, 1) and returns `(a, (+ a 1), 1)`.
    fn a_pinned_to_zero(h: &mut Harness) -> (TermId, TermId, TermId) {
        let a = int_var_no(&mut h.ctx, "a");
        let zero = int_num_no(&mut h.ctx, 0);
        let one = int_num_no(&mut h.ctx, 1);
        let t = h.ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[a, one]).unwrap();
        let le = h.ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[a, zero]).unwrap();
        let ge = h.ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[a, zero]).unwrap();
        h.assert_atom(0, le);
        h.assert_atom(1, ge);
        (a, t, one)
    }

    /// Spec §1.3: `ensure_shared_var((+ a 1))` must define the shared var as
    /// `a + 1`, mark it constrained, and let arith entail `(+ a 1) = 1` when
    /// `a = 0`. On `main` it is a free, unconstrained var: its value is
    /// arbitrary and the entailment probe skips it.
    #[test]
    fn compound_shared_term_is_defined_by_its_linearization() {
        let mut h = Harness::new();
        let (_a, t, one) = a_pinned_to_zero(&mut h);
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.ensure_shared_var(&ctx, t);
        h.arith.ensure_shared_var(&ctx, one);
        assert!(matches!(h.arith.check_full(), TCheck::Sat));
        let tv = h.arith.vars.problem_var(t);
        assert_eq!(h.arith.value[tv.index()], dr(1), "(+ a 1) must take a + 1 = 1");
        assert!(
            h.arith.is_constrained(tv),
            "a defined compound shared var is constrained (spec §3.1)"
        );
        let got = pairset(&h.arith.entailed_equalities(&ctx, &[t, one]));
        assert!(
            got.contains(&(t.index().min(one.index()), t.index().max(one.index()))),
            "a = 0 must entail (+ a 1) = 1: {got:?}"
        );
    }
```

- [ ] **Step 4: Run the new tests on `main`'s code and record the failures**

```bash
cargo nextest run -p shinri-solver -E 'binary(uflia_e2e) and test(slice50_)'
cargo nextest run -p shinri-solver -E 'binary(uflra_e2e) and test(slice50_)'
cargo nextest run -p shinri-arith -E 'test(compound_shared_term_is_defined_by_its_linearization)'
```

Expected: the discovered counts are 9, 1 and 1. Every test **fails** except `slice50_compound_arg_sat_direction` and `slice50_nonlinear_arg_does_not_panic`, which pass. The seven `…_unsat` tests in `uflia_e2e` and the one in `uflra_e2e` fail with `left: Sat, right: Unsat`. The arith test fails on the value assertion. Record the verbatim output in the task report.

These expectations were measured at plan time with the CLI on `main` (`b94d4ce`) against z3 4.16.0. All eight `…_unsat` shapes answered `sat` on `main` and `unsat` on z3. The sat-direction shape answered `sat` on both, and the nonlinear shape answered `unknown` on `main` with no panic.

If `slice50_nonlinear_arg_does_not_panic` **panics** on `main`, record it. That means `linearize` is already reachable with a nonlinear term, and Task 2's `is_linear_arith` guard fixes it. If `slice50_compound_arg_sat_direction` fails on `main`, stop and report: the premise that a free compound argument answers `sat` today is wrong.

- [ ] **Step 5: Commit (do not push)**

```bash
git add crates/shinri-solver/tests/uflia_e2e.rs crates/shinri-solver/tests/uflra_e2e.rs crates/shinri-arith/src/lib.rs
git commit -m "test(uflia): slice50 T1 - red pins for compound UF arguments"
```

---

### Task 2: Definitional rows for compound shared terms

Spec §3. This is the production fix. It also carries the backtracking test and the Wisa confirmation.

**Files:**
- Modify: `crates/shinri-arith/src/normalize.rs:106` (`fn linearize` → `pub(crate) fn linearize`) and `:205` (`fn canonicalize` → `pub(crate) fn canonicalize`)
- Modify: `crates/shinri-arith/src/lib.rs:648–675` (`ensure_shared_var`), plus new private fns next to it
- Test: `crates/shinri-arith/src/lib.rs` (`mod nelson_oppen_tests`)

**Interfaces:**
- Consumes: `normalize::linearize(&Context, &mut VarStore, TermId) -> (Vec<(ArithVar, Rational)>, Rational)`, `normalize::canonicalize(Vec<(ArithVar, Rational)>) -> LinComb`, `VarStore::{slack_var, term_of, mark_int}`, `Tableau::{define_slack, is_basic}`, `Bounds::{lower, upper, tighten}`, `Arith::{grow_value, recompute_basic_values, mark_constrained, fresh_sentinel}`. All exist on `main`.
- Produces: `Arith::ensure_shared_var` (same signature) now defines compound linear terms. The private helpers `is_compound_arith(&Context, TermId) -> bool`, `is_linear_arith(&Context, TermId) -> bool` and `Arith::define_shared_compound(&mut self, &Context, TermId, ArithVar)`.

- [ ] **Step 1: Write the backtracking test (red)**

Append to `mod nelson_oppen_tests`, after the Task 1 test:

```rust
    /// Spec §3.2: the pin is trailed, so a pop below the level it was installed
    /// at removes it. The combiner re-calls `ensure_shared_var` for every
    /// shared term at every final check; that re-call must re-install the pin
    /// (an "already defined" flag that skipped it would leave `(+ a 1)` free).
    #[test]
    fn compound_definition_is_reinstalled_after_pop() {
        let mut h = Harness::new();
        let (_a, t, one) = a_pinned_to_zero(&mut h);
        let ctx = std::mem::replace(&mut h.ctx, Context::new());
        h.arith.push(); // level 1
        h.arith.ensure_shared_var(&ctx, t);
        h.arith.ensure_shared_var(&ctx, one);
        assert!(matches!(h.arith.check_full(), TCheck::Sat));
        let tv = h.arith.vars.problem_var(t);
        assert_eq!(h.arith.value[tv.index()], dr(1), "level 1: (+ a 1) = 1");

        h.arith.pop(0);
        // Next final check, as `drive_final_check` does it:
        h.arith.ensure_shared_var(&ctx, t);
        h.arith.ensure_shared_var(&ctx, one);
        assert!(matches!(h.arith.check_full(), TCheck::Sat));
        assert_eq!(
            h.arith.value[tv.index()],
            dr(1),
            "after pop + re-ensure: (+ a 1) must again equal a + 1"
        );
        let got = pairset(&h.arith.entailed_equalities(&ctx, &[t, one]));
        assert!(
            got.contains(&(t.index().min(one.index()), t.index().max(one.index()))),
            "after pop + re-ensure: a = 0 must entail (+ a 1) = 1: {got:?}"
        );
    }
```

Run: `cargo nextest run -p shinri-arith -E 'test(compound_definition_is_reinstalled_after_pop)'`
Expected: 1 discovered, FAIL on the first value assertion. Record it.

- [ ] **Step 2: Make `linearize` and `canonicalize` crate-visible**

In `crates/shinri-arith/src/normalize.rs`, change `fn linearize(` at `:106` to `pub(crate) fn linearize(`, and `fn canonicalize(` at `:205` to `pub(crate) fn canonicalize(`. Change nothing else. Also update the module doc's stale line "The functions `normalize_atom` / `linearize` / `canonicalize` are added in Task 4; this file only provides the type definitions…" to: "`linearize` and `canonicalize` are also used by `Arith::ensure_shared_var` to define compound shared terms (slice 50)."

- [ ] **Step 3: Add the two predicates**

In `crates/shinri-arith/src/lib.rs`, as free functions directly above `impl Arith` (or next to other free helpers in the file, whichever comes first):

```rust
/// Slice 50: `t` is a compound arithmetic application (`+`, `-`, unary `-`,
/// `*`) rather than a numeral or an opaque leaf (UF application, `str.len`, …).
fn is_compound_arith(ctx: &Context, t: TermId) -> bool {
    use shinri_core::{BuiltinOp, Op, TermNode};
    if ctx.numeral_value(t).is_some() {
        return false;
    }
    matches!(
        ctx.term_node(t),
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Add | BuiltinOp::Sub | BuiltinOp::Neg | BuiltinOp::Mul),
            ..
        }
    )
}

/// Slice 50: `t` is linear all the way down: every `*` has at most one
/// non-numeral factor, which is itself linear. This is exactly the input
/// `normalize::linearize` accepts without its "nonlinear reached normalize"
/// debug assertion. Opaque leaves are linear.
fn is_linear_arith(ctx: &Context, t: TermId) -> bool {
    use shinri_core::{BuiltinOp, Op, TermNode};
    if ctx.numeral_value(t).is_some() {
        return true;
    }
    match ctx.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Add | BuiltinOp::Sub | BuiltinOp::Neg),
            args,
            ..
        } => ctx.children(*args).iter().all(|&k| is_linear_arith(ctx, k)),
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Mul),
            args,
            ..
        } => {
            let mut nonconst = ctx
                .children(*args)
                .iter()
                .copied()
                .filter(|&k| ctx.numeral_value(k).is_none());
            match (nonconst.next(), nonconst.next()) {
                (None, _) => true,
                (Some(k), None) => is_linear_arith(ctx, k),
                (Some(_), Some(_)) => false,
            }
        }
        _ => true,
    }
}
```

If `use shinri_core::{…}` inside a fn clashes with a module-level import, drop the local `use` and rely on the existing one.

- [ ] **Step 4: Add `define_shared_compound` and call it from `ensure_shared_var`**

Replace the doc comment and body of `ensure_shared_var` (`crates/shinri-arith/src/lib.rs:648–675`) so it reads as below. The numeral branch is kept byte-for-byte; only the `else if` arm is new.

```rust
    /// Intern the shared term `t` as a problem var (stamping Int-sortedness).
    /// Numerals are pinned to their value (slice 42). Compound linear terms
    /// (`(+ a 1)`, `(* 2 a)`, …) are pinned to their linearization by a
    /// permanent row (slice 50, `define_shared_compound`); without it the var
    /// is free and unrelated to its own arguments. Opaque leaves are left free.
    ///
    /// Pins are trailed bounds, so a pop can remove them. That is safe ONLY
    /// because `drive_final_check` re-calls this for every shared term at EVERY
    /// final check, before any `Sat`: keep it that way.
    pub fn ensure_shared_var(&mut self, ctx: &Context, t: TermId) {
        // Stamp Int-sortedness so shared Int terms (f-apps, numerals, vars) are
        // integral in the simplex / integer layer — required for QF_UFLIA.
        let is_int = ctx.sort_of(t) == ctx.int_sort();
        let v = self.vars.problem_var_sorted(t, is_int);
        self.grow_value();
        if let Some(r) = ctx.numeral_value(t) {
            // ... existing slice-42 numeral block, unchanged ...
        } else if is_compound_arith(ctx, t) && is_linear_arith(ctx, t) {
            self.define_shared_compound(ctx, t, v);
        }
    }

    /// Slice 50 (spec §3.1): pin the compound shared term `t` (var `v`) to its
    /// linearization `Σ qᵢ·xᵢ + c`, as the row `v − Σ qᵢ·xᵢ = c`: a permanent
    /// tableau row over a slack pinned to `[c, c]`. If the row cancels to `v`
    /// alone (e.g. `(- a a)`), `v` itself is pinned. The sentinel literal is
    /// dropped by `sanitize_conflict`, so every conflict core stays justified by
    /// input literals.
    ///
    /// `v` is marked constrained: it can no longer shift on its own, and slice
    /// 42's filter would otherwise hide it from `entailed_equalities` and MBTC
    /// (spec §3.1, *Constrainedness*). That errs toward more probing, the
    /// documented sound direction.
    fn define_shared_compound(&mut self, ctx: &Context, t: TermId, v: ArithVar) {
        let (raw, c) = crate::normalize::linearize(ctx, &mut self.vars, t);
        // `linearize` is sort-blind (as in `new_var`): stamp Int leaves here.
        let int_s = ctx.int_sort();
        for (x, _) in &raw {
            if let Some(xt) = self.vars.term_of(*x) {
                if ctx.sort_of(xt) == int_s {
                    self.vars.mark_int(*x);
                }
            }
        }
        let mut pairs = Vec::with_capacity(raw.len() + 1);
        pairs.push((v, Rational::one()));
        pairs.extend(raw.into_iter().map(|(x, q)| (x, -q)));
        // `v` is interned by TermId `t`, never by one of `t`'s leaves, so it
        // survives canonicalization with coefficient exactly 1.
        let comb = crate::normalize::canonicalize(pairs);
        let target = if comb.0.len() == 1 {
            debug_assert!(comb.0[0].0 == v && comb.0[0].1 == Rational::one());
            v
        } else {
            let s = self.vars.slack_var(&comb);
            let is_new = !self.tableau.is_basic(s);
            self.tableau.define_slack(s, &comb);
            self.grow_value();
            if is_new {
                self.recompute_basic_values();
            }
            s
        };
        self.mark_constrained(v);
        let dr = DeltaRational::from_rational(c);
        // Idempotent, as for numerals: skip if already pinned to this value.
        let already = matches!(self.bounds.lower(target), Some((lo, _)) if *lo == dr)
            && matches!(self.bounds.upper(target), Some((hi, _)) if *hi == dr);
        if !already {
            let def = self.fresh_sentinel();
            let _ = self.bounds.tighten(target, BoundKind::Lower, dr.clone(), def);
            let _ = self.bounds.tighten(target, BoundKind::Upper, dr.clone(), def);
            if !self.tableau.is_basic(target) {
                self.value[target.index()] = dr;
            }
        }
    }
```

Why the `tighten` results can be ignored: `target` is either a slack unique to `t`'s comb, or `v` itself. Neither carries bounds from any other source. Atoms linearize through `t`'s leaves, never through the TermId `t`, and interface equalities bound diff slacks, not `v`. `c` is a function of `t` alone, so a re-pin never disagrees with a live one. If clippy or the borrow checker objects to the `matches!` guards (the same shape as the numeral block), copy the numeral block's exact form.

- [ ] **Step 5: Run the unit tests**

```bash
cargo nextest run -p shinri-arith
```

Expected: all green, including `compound_shared_term_is_defined_by_its_linearization` and `compound_definition_is_reinstalled_after_pop`. `ensure_shared_var_alone_does_not_constrain` must still pass, because a plain variable is not compound.

- [ ] **Step 6: Run the e2e pins**

```bash
cargo nextest run -p shinri-solver -E 'binary(uflia_e2e)'
cargo nextest run -p shinri-solver -E 'binary(uflra_e2e)'
```

Expected: both green with non-zero counts, including all nine `slice50_` tests in `uflia_e2e` and the one in `uflra_e2e`.

- [ ] **Step 7: Confirm the Wisa row (spec §5 Task 1, the step-up trigger)**

```bash
test -d bench/corpus/QF_UFLIA || BENCH_LOGICS=QF_UFLIA mise run bench-fetch
cargo build --release -p shinri-cli
time target/release/shinri bench/corpus/QF_UFLIA/mathsat/Wisa/xs-05-08-4-2-5-4.smt2 | grep -Ex 'sat|unsat|unknown'
```

Expected: `unsat` (pre-slice: `sat` in about 4 s). Record the answer and the time.

**If it prints `sat`: STOP.** Do not continue to Task 3. Delta-debug the file by deleting conjuncts while it still answers `sat` and z3 still says `unsat` (`z3 <file>`), then report the reduced file and the named code path to the user. Per spec §5 and §9, a second, independent mechanism steps the slice up to approach B, and the spec is amended before continuing. If it prints `unknown`, record it and continue: that is sound, and criterion 2 is then reported as missed in Task 6.

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-arith/src/lib.rs crates/shinri-arith/src/normalize.rs
git commit -m "fix(arith): slice50 T2 - define compound shared terms by their linearization"
```

---

### Task 3: Eager ⊤/⊥ sentinels

Spec §4. Independent of Tasks 1–2.

**Files:**
- Modify: `crates/shinri-theory/src/eq_engine.rs` (add `level()` next to `push` at `:456`)
- Modify: `crates/shinri-theory/src/solver_trait.rs` (add a seam method in the N-O seam block, after `mint_eq_tag` at `:107`)
- Modify: `crates/shinri-theory/src/combiner.rs` (add `install_truth_terms` after `euf_mut` at `:89–91`)
- Modify: `crates/shinri-euf/src/solver.rs` (impl the seam; rewrite the I1 comment at `:92–101`; add unit tests)
- Modify: `crates/shinri-euf/src/egraph.rs:367–392` (`truth_nodes` debug assertion)
- Modify: `crates/shinri-solver/src/lib.rs:1238–1243`
- Modify: `crates/shinri-euf/tests/qfuf_euf.rs` (append the combiner-level test)

**Interfaces:**
- Consumes: `EGraph::truth_nodes(&mut self, &mut TheoryCtx, TermId, TermId) -> (ENodeId, ENodeId)`, `Euf::set_truth_terms`, `UndoLog::level()`.
- Produces:
  - `EqualityEngine::level(&self) -> usize`
  - `TheorySolver::install_truth_terms(&mut self, cx: &mut TheoryCtx, t_true: TermId, t_false: TermId)` (default no-op)
  - `Combiner::install_truth_terms(&mut self, t_true: TermId, t_false: TermId)`

- [ ] **Step 1: Write the EUF unit tests (red)**

Append inside `mod tests` in `crates/shinri-euf/src/solver.rs`:

```rust
    // ----- Slice 50: ⊤≠⊥ must live at level 0 (spec §4) -----

    struct SentinelWorld {
        ctx: shinri_core::Context,
        atoms: shinri_theory::AtomRegistry,
        t_true: TermId,
        t_false: TermId,
        eq_ab: TermId,
        pa: TermId,
        pb: TermId,
        v_ab: Var,
        v_pa: Var,
        v_pb: Var,
    }

    fn sentinel_world() -> SentinelWorld {
        use shinri_core::{Context, Op};
        use shinri_theory::types::Owner;
        use shinri_theory::AtomRegistry;

        let mut ctx = Context::new();
        let u = ctx.declare_sort("U");
        let bool_s = ctx.bool_sort();
        let a_sym = ctx.declare_fun("a", &[], u);
        let a = ctx.mk_app(Op::Uninterpreted(a_sym), &[]).unwrap();
        let b_sym = ctx.declare_fun("b", &[], u);
        let b = ctx.mk_app(Op::Uninterpreted(b_sym), &[]).unwrap();
        let p = ctx.declare_fun("p", &[u], bool_s);
        let pa = ctx.mk_app(Op::Uninterpreted(p), &[a]).unwrap();
        let pb = ctx.mk_app(Op::Uninterpreted(p), &[b]).unwrap();
        let eq_ab = ctx.mk_eq(a, b).unwrap();
        let t_true = ctx.mk_const_bool(true);
        let t_false = ctx.mk_const_bool(false);
        let mut atoms = AtomRegistry::default();
        let (v_ab, v_pa, v_pb) = (Var::new(0), Var::new(1), Var::new(2));
        atoms.register(v_ab, eq_ab, Owner::Euf);
        atoms.register(v_pa, pa, Owner::Euf);
        atoms.register(v_pb, pb, Owner::Euf);
        SentinelWorld { ctx, atoms, t_true, t_false, eq_ab, pa, pb, v_ab, v_pa, v_pb }
    }

    /// The slice-49 report's repro, in combiner order: `a = b` registered at
    /// level 0; `p(a)`, `p(b)` registered at level 1 (as `bind_fresh` does);
    /// pop to 0; assert `p(a)`, `¬p(b)`, `a = b`. Returns whether assert,
    /// propagate or check reported a conflict.
    fn sentinel_sequence_conflicts(
        euf: &mut Euf,
        eq: &mut shinri_theory::EqualityEngine,
        w: &mut SentinelWorld,
    ) -> bool {
        {
            let mut cx = TheoryCtx { terms: &mut w.ctx, eq: &mut *eq, atoms: &w.atoms };
            euf.new_var(&mut cx, w.v_ab, w.eq_ab);
        }
        eq.push();
        euf.push();
        {
            let mut cx = TheoryCtx { terms: &mut w.ctx, eq: &mut *eq, atoms: &w.atoms };
            euf.new_var(&mut cx, w.v_pa, w.pa);
            euf.new_var(&mut cx, w.v_pb, w.pb);
        }
        eq.pop(0);
        euf.pop(0);
        let mut cx = TheoryCtx { terms: &mut w.ctx, eq: &mut *eq, atoms: &w.atoms };
        let mut conflict = false;
        conflict |= euf.assert(&mut cx, Lit::new(w.v_pa, true)).is_some();
        conflict |= euf.assert(&mut cx, Lit::new(w.v_pb, false)).is_some();
        conflict |= euf.assert(&mut cx, Lit::new(w.v_ab, true)).is_some();
        let mut out = Vec::new();
        conflict |= euf.propagate(&mut cx, &mut out).is_some();
        conflict |= matches!(euf.check(&mut cx, Effort::Full), TCheck::Conflict(_));
        conflict
    }

    /// Spec §4: with the eager install, ⊤≠⊥ lives at level 0 and the
    /// sequence conflicts. Red on `main`: `install_truth_terms` does not exist.
    #[test]
    fn eager_truth_install_survives_midsearch_registration() {
        let mut w = sentinel_world();
        let mut euf = Euf::default();
        let mut eq = shinri_theory::EqualityEngine::default();
        {
            let mut cx = TheoryCtx { terms: &mut w.ctx, eq: &mut eq, atoms: &w.atoms };
            euf.install_truth_terms(&mut cx, w.t_true, w.t_false);
        }
        assert!(
            sentinel_sequence_conflicts(&mut euf, &mut eq, &mut w),
            "p(a), ¬p(b), a = b must conflict: ⊤≠⊥ must survive the pop"
        );
    }

    /// Spec §4 step 4: the lazy install above the base level is now a loud
    /// failure in debug builds, not a silently level-scoped ⊤≠⊥. Red on
    /// `main`: nothing panics, and the sequence is silently accepted.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "⊤/⊥ sentinels must be installed at the base level")]
    fn lazy_truth_install_above_base_level_is_rejected() {
        let mut w = sentinel_world();
        let mut euf = Euf::default();
        let mut eq = shinri_theory::EqualityEngine::default();
        euf.set_truth_terms(w.t_true, w.t_false);
        let _ = sentinel_sequence_conflicts(&mut euf, &mut eq, &mut w);
    }
```

If the test module's existing imports don't cover `TermId`, `Var`, `Lit`, `Effort`, `TCheck` or `TheoryCtx`, add them the way the neighbouring `registration_collision` test does. It uses `shinri_theory::{AtomRegistry, EqualityEngine}` and `shinri_theory::types::Owner` locally.

- [ ] **Step 2: Write the combiner-level test (red)**

Append to `crates/shinri-euf/tests/qfuf_euf.rs`:

```rust
/// Slice 50 (spec §4): the solver's path. `Combiner::install_truth_terms` at
/// level 0, then `bind_fresh` registers the predicate atoms at level 1 (as a
/// mid-search split does), pop, then assert p(a), ¬p(b), a = b ⇒ conflict.
#[test]
fn combiner_truth_install_survives_bind_fresh_and_pop() {
    use shinri_sat::{Effort, Theory, TheoryResult};
    use shinri_theory::{Combiner, EmptyTheory};

    let mut c: Combiner<Euf, EmptyTheory, EmptyTheory, EmptyTheory, EmptyTheory> =
        Combiner::default();
    let (t_true, t_false, eq_ab, pa, pb) = {
        let ctx = c.context_mut();
        let u = ctx.declare_sort("U");
        let bool_s = ctx.bool_sort();
        let a = uconst(ctx, "a", u);
        let b = uconst(ctx, "b", u);
        let p = ctx.declare_fun("p", &[u], bool_s);
        let pa = ctx.mk_app(Op::Uninterpreted(p), &[a]).unwrap();
        let pb = ctx.mk_app(Op::Uninterpreted(p), &[b]).unwrap();
        let eq_ab = ctx.mk_eq(a, b).unwrap();
        (ctx.mk_const_bool(true), ctx.mk_const_bool(false), eq_ab, pa, pb)
    };
    let (v_ab, v_pa, v_pb) = (Var::new(0), Var::new(1), Var::new(2));
    c.install_truth_terms(t_true, t_false);
    c.register_atom(v_ab, eq_ab).unwrap();
    Theory::push(&mut c);
    c.bind_fresh(v_pa, pa);
    c.bind_fresh(v_pb, pb);
    Theory::pop(&mut c, 1);
    Theory::assert(&mut c, Lit::new(v_pa, true));
    Theory::assert(&mut c, Lit::new(v_pb, false));
    Theory::assert(&mut c, Lit::new(v_ab, true));
    let mut out = Vec::new();
    let conflict = c.propagate(&mut out).is_some()
        || matches!(c.check(Effort::Full), TheoryResult::Conflict(_));
    assert!(conflict, "p(a), ¬p(b), a = b must conflict after bind_fresh + pop");
}
```

If `EmptyTheory` does not satisfy a bound `Combiner` needs for its `Theory` impl, or `check` needs a theory in a slot this test leaves empty, use the concrete theory types that `crates/shinri-solver/src/lib.rs:2470–2480` uses for the missing slots. This crate cannot depend on them, so in that case move this test to a new file `crates/shinri-solver/tests/truth_sentinel.rs` with the same body.

- [ ] **Step 3: Run the new tests on `main`'s code and record the failures**

```bash
cargo nextest run -p shinri-euf -E 'test(truth_install)'
```

Expected: a **compile error** (E0599, no method `install_truth_terms`) for the two tests that call it. Record it. Then temporarily comment out those two tests and re-run: `lazy_truth_install_above_base_level_is_rejected` fails with "test did not panic as expected". Record that too, then uncomment them.

- [ ] **Step 4: Implement**

`crates/shinri-theory/src/eq_engine.rs`, next to `push`:

```rust
    /// The current decision level (number of un-popped `push`es).
    pub fn level(&self) -> usize {
        self.undo.level()
    }
```

`crates/shinri-theory/src/solver_trait.rs`, after `mint_eq_tag`:

```rust
    /// Install the canonical ⊤/⊥ Bool terms and any permanent state they need
    /// (EUF: the Definitional ⊤≠⊥ disequality) NOW, at the solve's base level,
    /// before any atom is registered (slice 50). `bind_fresh` can register atoms
    /// mid-search, so this must not wait for the first predicate atom.
    fn install_truth_terms(&mut self, _cx: &mut TheoryCtx, _t_true: TermId, _t_false: TermId) {}
```

`crates/shinri-theory/src/combiner.rs`, after `euf_mut`:

```rust
    /// Install ⊤/⊥ and EUF's ⊤≠⊥ at the base level, before solving (slice 50,
    /// spec §4). Must be called before any atom is encoded.
    pub fn install_truth_terms(&mut self, t_true: TermId, t_false: TermId) {
        let mut cx = TheoryCtx {
            terms: &mut self.terms,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        self.euf.install_truth_terms(&mut cx, t_true, t_false);
    }
```

`crates/shinri-euf/src/solver.rs`, inside `impl TheorySolver for Euf` (next to `mint_eq_tag`, or any seam method):

```rust
    fn install_truth_terms(&mut self, cx: &mut TheoryCtx, t_true: TermId, t_false: TermId) {
        self.set_truth_terms(t_true, t_false);
        self.inner.truth_nodes(cx, t_true, t_false);
    }
```

Replace the comment in `new_var`'s catch-all arm (`:92–99`) with:

```rust
                // The ⊤/⊥ sentinels and the Definitional ⊤≠⊥ diseq must live at
                // level 0: an undo recorded at a higher level would let a pop drop
                // ⊤≠⊥ while `truth` stays cached (the I1 bug, and slice 50 §1.5).
                // The solver installs them eagerly via `install_truth_terms` before
                // encoding, so this call is a cache hit in production; `bind_fresh`
                // CAN reach this arm above level 0. It remains for standalone EUF
                // (tests that only call `set_truth_terms`), where `truth_nodes`
                // debug-asserts it runs at the base level.
```

`crates/shinri-euf/src/egraph.rs`, in `truth_nodes`, directly after the `if let Some(tf) = self.truth { return tf; }` early return:

```rust
        debug_assert_eq!(
            cx.eq.level(),
            0,
            "⊤/⊥ sentinels must be installed at the base level (slice 50): \
             call install_truth_terms before solving"
        );
```

`crates/shinri-solver/src/lib.rs:1238–1243`, replace the comment and the `set_truth_terms` call with:

```rust
        // Install ⊤/⊥ AND EUF's ⊤≠⊥ now, at level 0, before any atom encoding
        // (slice 50): `bind_fresh` can register EUF atoms mid-search, so the
        // install must not wait for the first predicate atom.
        sat.theory_mut()
            .install_truth_terms(self.t_true, self.t_false);
```

Leave the second `Combiner::with_context` site at `lib.rs:2484` unchanged: it encodes a formula for inspection and never solves.

- [ ] **Step 5: Run the affected crates**

```bash
cargo nextest run -p shinri-euf
cargo nextest run -p shinri-theory
cargo nextest run -p shinri-solver
```

Expected: all green. The three new tests pass.

If an **existing** test now panics with "⊤/⊥ sentinels must be installed at the base level", it registers or asserts its first predicate atom above level 0 using only `set_truth_terms`, which is exactly the hazard. Change that test's setup to call `install_truth_terms` at level 0. Do not remove the assertion. List each migrated test in the task report. The known callers of `set_truth_terms` in tests are `crates/shinri-euf/tests/qfuf_euf.rs:140` and `:187`.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-theory/src/eq_engine.rs crates/shinri-theory/src/solver_trait.rs \
        crates/shinri-theory/src/combiner.rs crates/shinri-euf/src/solver.rs \
        crates/shinri-euf/src/egraph.rs crates/shinri-euf/tests/qfuf_euf.rs \
        crates/shinri-solver/src/lib.rs
git commit -m "fix(euf): slice50 T3 - install truth sentinels at level 0 before solving"
```

---

### Task 4: Oracle coverage for compound UF arguments

Spec §5 Task 4. Neither `differential_qf_uflia_small` (`oracle.rs:1590`, arguments are bare constants) nor `differential_qf_uflra` (`oracle.rs:321`, arguments are variables or nested UF apps) emits a compound arithmetic argument. That gap is how §1 went unnoticed. Add a separate test with its own seed, so the existing generators' random streams are unchanged.

**Files:**
- Modify: `crates/shinri-solver/tests/oracle.rs` (append after `differential_qf_uflia_small`)

**Interfaces:**
- Consumes: `Lcg`, `z_int` (both in `oracle.rs`), `easy_smt::Context::{declare_const, declare_fun, atom, list, plus, times, numeral, eq, not, assert, check}`.
- Produces: `differential_qf_uflia_compound_args`.

- [ ] **Step 1: Write the generator**

```rust
/// Slice 50: UF applications over COMPOUND linear arguments (`f(c + d)`,
/// `f(2·c)`), mixed with pins `c = k` and ground values `f(k) = m`. The
/// generators above only ever apply `f` to a bare constant, so they could not
/// reach the undefined-compound-shared-var defect (spec §1.3).
#[test]
fn differential_qf_uflia_compound_args() {
    let mut rng = Lcg(0x5150);
    let (mut n_sat, mut n_unsat) = (0usize, 0usize);
    for iter in 0..200 {
        let mut s = Solver::new();
        let int = s.int_sort();
        let consts: Vec<_> = (0..2).map(|i| s.declare_const(&format!("c{i}"), int)).collect();
        let f = s.declare_fun("f", &[int], int);

        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .unwrap();
        let zint = ctx.atom("Int");
        let z_consts: Vec<_> = (0..2)
            .map(|i| ctx.declare_const(format!("c{i}"), zint).unwrap())
            .collect();
        let _zf = ctx.declare_fun("f", vec![zint], zint).unwrap();
        let zf = ctx.atom("f");

        let mut script = Vec::new();
        let n_lits = 2 + rng.below(4) as usize;
        for _ in 0..n_lits {
            let i = rng.below(2) as usize;
            match rng.below(3) {
                // Pin: c_i = k, k ∈ [0, 3)
                0 => {
                    let k = rng.below(3) as i128;
                    let kn = s.numeral(Rational::from_int(k.into()), int);
                    let e = s.eq(consts[i], kn);
                    s.assert(e);
                    ctx.assert(ctx.eq(z_consts[i], ctx.numeral(k as i32))).unwrap();
                    script.push(format!("(= c{i} {k})"));
                }
                // Ground value: f(k) = m, k ∈ [-1, 4), m ∈ [0, 2)
                1 => {
                    let k = rng.below(5) as i32 - 1;
                    let m = rng.below(2) as i128;
                    let kn = s.numeral(Rational::from_int((k as i128).into()), int);
                    let mn = s.numeral(Rational::from_int(m.into()), int);
                    let fk = s.app(Op::Uninterpreted(f), &[kn]);
                    let e = s.eq(fk, mn);
                    s.assert(e);
                    let zfk = ctx.list(vec![zf, z_int(&ctx, k)]);
                    ctx.assert(ctx.eq(zfk, ctx.numeral(m as i32))).unwrap();
                    script.push(format!("(= (f {k}) {m})"));
                }
                // Compound: [¬] f(arg) = m with arg ∈ {c_i + d, 2·c_i}
                _ => {
                    let m = rng.below(2) as i128;
                    let neg = rng.below(2) == 1;
                    let (arg, zarg, txt) = if rng.below(2) == 0 {
                        let d = rng.below(3) as i32 - 1;
                        let dn = s.numeral(Rational::from_int((d as i128).into()), int);
                        (
                            s.app(Op::Builtin(BuiltinOp::Add), &[consts[i], dn]),
                            ctx.plus(z_consts[i], z_int(&ctx, d)),
                            format!("(+ c{i} {d})"),
                        )
                    } else {
                        let two = s.numeral(Rational::from_int(2i128.into()), int);
                        (
                            s.app(Op::Builtin(BuiltinOp::Mul), &[two, consts[i]]),
                            ctx.times(ctx.numeral(2), z_consts[i]),
                            format!("(* 2 c{i})"),
                        )
                    };
                    let mn = s.numeral(Rational::from_int(m.into()), int);
                    let fa = s.app(Op::Uninterpreted(f), &[arg]);
                    let e = s.eq(fa, mn);
                    let lit = if neg { s.app(Op::Builtin(BuiltinOp::Not), &[e]) } else { e };
                    s.assert(lit);
                    let ze = ctx.eq(ctx.list(vec![zf, zarg]), ctx.numeral(m as i32));
                    ctx.assert(if neg { ctx.not(ze) } else { ze }).unwrap();
                    let body = format!("(= (f {txt}) {m})");
                    script.push(if neg { format!("(not {body})") } else { body });
                }
            }
        }

        let ours = s.check_sat();
        let theirs = ctx.check().unwrap();
        match (ours, theirs) {
            (SolveOutcome::Unknown, _) => {}
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (o, t) => panic!(
                "DISAGREEMENT (QF_UFLIA compound args) iter {iter}: shinri={o:?} z3={t:?}\n{}",
                script.join("\n")
            ),
        }
    }
    eprintln!("compound-args oracle: sat {n_sat}, unsat {n_unsat}");
    assert!(n_unsat > 0, "generator must produce some UNSAT instances");
    assert!(n_sat > 0, "generator must produce some SAT instances");
}
```

If `easy_smt::Context` lacks `plus` or `times` under those names, use the names the file's LRA generator uses for sums and products (`oracle.rs:145–319`).

- [ ] **Step 2: Check it would have caught the bug**

```bash
git stash push crates/shinri-arith/src/lib.rs crates/shinri-arith/src/normalize.rs
cargo nextest run -p shinri-solver --features oracle -E 'test(differential_qf_uflia_compound_args)'
git stash pop
```

Expected: 1 discovered, **FAIL** with a `DISAGREEMENT … shinri=Sat z3=Unsat` dump. Record the dump. If it passes on pre-Task-2 arith code, the generator is too weak: raise the compound-arm probability or `n_lits` until it fails, and record the change.

- [ ] **Step 3: Run it with the fix**

```bash
cargo nextest run -p shinri-solver --features oracle -E 'test(differential_qf_uflia_compound_args)' --no-capture
```

Expected: 1 discovered, PASS, printing non-zero `sat` and `unsat` counts. Record the counts.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/oracle.rs
git commit -m "test(oracle): slice50 T4 - QF_UFLIA differential over compound UF arguments"
```

---

### Task 5: Gates, push, and PR

**Files:** none modified unless a gate fails.

**Interfaces:**
- Consumes: Tasks 1–4.
- Produces: a pushed branch and an open PR, green in CI, for Tasks 6 and 7.

- [ ] **Step 1: Run the fast blocking tier**

Run: `mise run test`

Expected: green. This is the tier CI gates on.

- [ ] **Step 2: Run the FULL unfiltered oracle**

```bash
cargo nextest run -p shinri-solver --features oracle
```

Expected: green, with a non-zero discovered count. Record discovered and passed counts for the Task 6 report. The run is unfiltered on purpose: both fixes are in shared core.

- [ ] **Step 3: Run `script_e2e` locally**

Run: `cargo nextest run -p shinri-solver -E 'binary(script_e2e)'`

Expected: green, with a non-zero discovered count. This slice can shift answers: a `sat` may now be `unsat`. If z3 confirms the flip, it is an adjudicated flip: re-pin it and say so in the commit. If z3 does *not* confirm the flip, it is a bug: stop and diagnose.

- [ ] **Step 4: Lint and format**

```bash
cargo fmt --all
cargo clippy --workspace --all-targets -- -D warnings
```

Expected: no clippy warnings. If `fmt` changed files, commit them as `style: slice50 - cargo fmt`.

- [ ] **Step 5: Push and open the PR**

```bash
git push -u origin slice50-uflia-shared-compound-args
gh pr create --base main --title "slice50: define compound shared arith terms; eager truth sentinels"
```

PR body:
- the spec §1.3 mechanism, in three sentences;
- the §1.2 repro, before (`sat`) and after (`unsat`), plus Task 2 Step 7's Wisa answer and time;
- the sentinel fix in two sentences, with "no corpus row attributed";
- "Corpus measurement follows in this PR (Task 6)".

- [ ] **Step 6: Confirm CI is green**

Run: `gh pr checks --watch`

Do not merge while any check is red. Task 6 can start as soon as the branch builds.

---

### Task 6: Corpus measurement and report

Spec §7 is the gate that decides whether this slice delivered anything on the corpus.

**Files:**
- Create: `docs/superpowers/research/2026-09-29-smtlib-2024-slice50-uflia-report.md`
- Modify: `docs/superpowers/specs/2026-09-29-shinri-slice50-uflia-shared-compound-args-design.md` (append `## 12. Measured outcomes`)

**Interfaces:**
- Consumes: the branch build (`target/release/shinri` at the branch HEAD).
- Produces: the report and the spec's measured-outcomes section, which Task 7 reviews.

Throughout this task, `$SCRATCH` is the session scratch directory. Nothing under it is committed.

- [ ] **Step 1: Fetch the corpus**

```bash
BENCH_LOGICS=QF_UF,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA,QF_DT mise run bench-fetch
```

Expected: md5 ok for each archive, and extracted counts QF_UF 7,503, QF_UFLIA 659, QF_UFLRA 1,284, QF_S 18,940, QF_SLIA 84,395 and QF_DT 8,700. An already-extracted logic may be skipped.

- [ ] **Step 2: Decide the comparison run, and build a pre-slice binary**

```bash
ls bench/results/slice49/results.jsonl bench/results/baseline-8de004d44944/results.jsonl 2>&1
BASE=$(git merge-base main slice50-uflia-shared-compound-args)
git worktree add "$SCRATCH/slice50-base" "$BASE"
(cd "$SCRATCH/slice50-base" && cargo build --release -p shinri-cli)
"$SCRATCH/slice50-base/target/release/shinri" bench/corpus/QF_UFLIA/mathsat/Wisa/xs-05-08-4-2-5-4.smt2 | grep -Ex 'sat|unsat|unknown'
```

Expected: the last command prints `sat`. This binary is "pre-slice `main`" for criteria 5–7.

The comparison runs spec §7 names (`slice49`, `baseline-8de004d44944`) are git-ignored. **If both `results.jsonl` files exist,** use them as spec §7 says. **If either is missing (the expected case on a fresh machine),** the comparison run for every logic is a same-machine base run instead (Step 3b). Record which was used in the report. A same-machine base run is the stricter comparison, because it removes hardware and load differences. Spec §7's comparison table is still reported as context.

- [ ] **Step 3: Run the corpus (branch)**

```bash
BENCH_LOGICS=QF_UF,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA,QF_DT BENCH_RUN_ID=slice50 mise run bench-run
```

Limits are the baseline's (20 s / 3072 MB / 6 jobs). That is 121,481 instances. Do not trust any duration estimate: after about 15 minutes, read `wc -l bench/results/slice50/results.jsonl`, project from the rate, and tell the user the projection before walking away.

- [ ] **Step 3b: Run the corpus (base), only if Step 2 found a comparison run missing**

```bash
cargo build --release -p shinri-bench
target/release/shinri-bench run --solver "$SCRATCH/slice50-base/target/release/shinri" \
  --logics QF_UF,QF_UFLIA,QF_UFLRA,QF_S,QF_SLIA,QF_DT \
  --timeout 20 --mem-mb 3072 --jobs 6 --run-id slice50-base
```

Run it after Step 3 finishes, not concurrently: both runs use 6 jobs, and concurrent load would move timeout-boundary rows. It uses the same flags as the `bench-run` mise task, with `--solver` pointing at the base binary.

- [ ] **Step 4: Render the reports**

```bash
BENCH_RUN_ID=slice50 mise run bench-report
BENCH_RUN_ID=slice50-base mise run bench-report   # only if Step 3b ran
```

- [ ] **Step 5: Compute the transition matrices**

Save as `$SCRATCH/transitions.py` and run it with `python3 "$SCRATCH/transitions.py" <old-run-dir>…`. Pass `bench/results/slice50-base`, or, if Step 2 found the committed runs, `bench/results/baseline-8de004d44944 bench/results/slice49`. Later directories override earlier ones per path.

```python
import collections, json, sys

def load(path):
    rows = {}
    with open(path) as f:
        next(f)  # fixture header
        for line in f:
            r = json.loads(line)
            rows[r["path"]] = r
    return rows

LOGICS = {"QF_UF", "QF_UFLIA", "QF_UFLRA", "QF_S", "QF_SLIA", "QF_DT"}
new = load("bench/results/slice50/results.jsonl")
old = {}
for d in sys.argv[1:]:
    old.update({p: r for p, r in load(f"{d}/results.jsonl").items() if r["logic"] in LOGICS})

common = set(old) & set(new)
print(f"common {len(common)}  missing {len(set(old) - set(new))}  extra {len(set(new) - set(old))}")

per_logic = collections.defaultdict(lambda: [collections.Counter(), collections.Counter()])
cells = collections.Counter()
families = collections.defaultdict(collections.Counter)
rows = collections.defaultdict(list)
for p in sorted(common):
    a, b, logic = old[p]["verdict"], new[p]["verdict"], new[p]["logic"]
    per_logic[logic][0][a] += 1
    per_logic[logic][1][b] += 1
    if a != b:
        key = (logic, a, b)
        cells[key] += 1
        families[key][p.split("/")[1]] += 1
        rows[key].append((p, old[p]["wall_ms"], new[p]["wall_ms"]))

for logic, (before, after) in sorted(per_logic.items()):
    print(f"\n{logic}\n  before {dict(before)}\n  after  {dict(after)}")
print("\nchanged cells (logic, before, after, count, families):")
for key, n in sorted(cells.items()):
    print(" ", *key, n, dict(families[key]))
print("\nrows needing individual attention (from correct, from wrong, or into wrong):")
for key, rs in sorted(rows.items()):
    if key[1] in ("correct", "wrong") or key[2] == "wrong":
        print("##", *key)
        for r in rs:
            print("  ", *r)
```

Expected: `common 121481 missing 0 extra 0`. Missing or extra rows invalidate the same-path comparison: stop and find out why before reporting anything.

- [ ] **Step 6: A/B-time every `correct → {timeout, unknown:*, oom}` row (criteria 5 and 6)**

Write the paths from Step 5's `correct → …` cells (excluding `correct → wrong`) to `$SCRATCH/ab-rows.txt`, one per line. Then:

```bash
while read -r path; do
  for label in base branch; do
    if [ "$label" = base ]; then bin="$SCRATCH/slice50-base/target/release/shinri"; else bin=target/release/shinri; fi
    start=$(date +%s%3N)
    ans=$(timeout 20 prlimit --as=$((3072 * 1024 * 1024)) "$bin" "bench/corpus/$path" 2>/dev/null | grep -Ex 'sat|unsat|unknown' | tail -1)
    echo "$path $label $(( $(date +%s%3N) - start ))ms ${ans:-none}"
  done
done < "$SCRATCH/ab-rows.txt" | tee "$SCRATCH/ab-results.txt"
```

For each row:
- **Boundary noise:** `base` also fails to answer within 20 s on this re-run. Exclude it from criterion 5 and list it. Spec §7 pre-declares QF_S `instance10273` and QF_UF's `qg5` set as expected noise. An oracle-side flip (the same shinri answer, verdict `correct ↔ unverified`) also counts as noise.
- **The slice's cost:** `base` answers and `branch` does not. It counts against criterion 5 and is listed under criterion 6. If several such rows share a family, time one with a counter of `define_shared_compound` calls (a throwaway `eprintln!`, not committed). That settles spec §9's un-banking trigger for the unit-difference class join.

- [ ] **Step 7: Check every non-`correct → wrong` row against pre-slice `main` (criterion 7)**

For each row in a `… → wrong` cell whose "before" verdict is not `correct`:

```bash
timeout 120 "$SCRATCH/slice50-base/target/release/shinri" "bench/corpus/$path" | grep -Ex 'sat|unsat|unknown'
```

Record whether pre-slice `main` gives the same wrong answer within 120 s (a pre-existing wrong answer this slice merely reached faster) or not (the slice changed the answer; trace it).

- [ ] **Step 8: Write the report**

Create `docs/superpowers/research/2026-09-29-smtlib-2024-slice50-uflia-report.md`, following the structure of `2026-09-11-smtlib-2024-slice49-euf-report.md`:

1. **Headline.**
2. **Comparison run used** (Step 2's decision) and why.
3. **Per-logic matrix** copied from `bench/results/slice50/report.md`.
4. **Before/after verdict counts per logic**, alongside spec §7's comparison table.
5. **Transition matrices** (changed cells only, with families), with the closure arithmetic `new = old − outbound + inbound` per logic.
6. **Success criteria**, using the table below.
7. **Oracle and test evidence:** each task's recorded red output, today's green, Task 4's disagreement dump and counts, and Task 5's unfiltered-oracle counts.
8. **Queued for the next slice:** spec §10, updated with what this run showed. Name the Wisa rows that moved and any that did not. Name any QF_SLIA wrong rows that moved, without claiming a cause.

| # | criterion | gate | how to report |
| --- | --- | --- | --- |
| 1 | Tasks 1–3's tests failed on pre-slice `main` and pass now | hard | quote each task report's failure and today's pass |
| 2 | §1.2 repro and `xs-05-08-4-2-5-4.smt2` answer `unsat` | hard | Task 1/2 tests; Task 2 Step 7; the `slice50` row |
| 3 | `correct → wrong`, all six logics | **0**, hard | Step 5 |
| 4 | QF_UFLIA `wrong` ≤ 11 | hard | the actual delta per family; no causal claim for any row without a trace |
| 5 | per-logic `correct` ≥ comparison run | hard | exclude only Step 6's boundary-noise rows, each listed |
| 6 | `correct → {timeout, unknown, oom}` | measured | every row with its Step 6 A/B result |
| 7 | `* → wrong` from a non-`correct` verdict | measured | every row with its Step 7 result |
| 8 | QF_SLIA `wrong` delta; QF_S 2 wrong rows | measured | the numbers, whatever they are |

If a hard criterion is missed, **decompose it rather than relaxing it**, and stop for a decision with the user before merge. If QF_UFLIA rows are still `wrong` with no named cause, that is spec §9's approach-B un-banking trigger: say so in the report.

- [ ] **Step 9: Append measured outcomes to the spec**

Append `## 12. Measured outcomes` to the spec. Include the criteria table with verdicts, the transitions that actually happened, the comparison run used, and any premise this run discarded. If fewer rows moved than §1.4's blast radius might suggest, say so plainly: that is a result, not a failure.

- [ ] **Step 10: Commit and push**

```bash
git add docs/superpowers/research/2026-09-29-smtlib-2024-slice50-uflia-report.md \
        docs/superpowers/specs/2026-09-29-shinri-slice50-uflia-shared-compound-args-design.md
git commit -m "docs(bench+spec): slice50 - UFLIA re-run report and measured outcomes"
git push
```

- [ ] **Step 11: Remove the A/B worktree**

```bash
git worktree remove "$SCRATCH/slice50-base"
```

---

### Task 7: Whole-branch review and merge

This review supplements the per-task reviews; it does not replace them. Both fixes sit in shared soundness paths, and slice 44's whole-branch review caught a Critical that every task review missed.

**Files:** none unless the review finds something.

- [ ] **Step 1: Review the full branch diff against the spec**

```bash
git diff main...slice50-uflia-shared-compound-args
```

Review the **whole diff at once**. Hunt specifically for:

1. **The re-pin invariant.** `grep -n "ensure_shared_var" crates/shinri-theory/src/combiner.rs`. Every final check must call it for **every** shared term **before** the first `arith.check` that can lead to `FinalCheck::Sat`. A path that returns `Sat` without re-pinning after a pop is a Critical.
2. **Sentinel hygiene.** The new pin's literal comes from `fresh_sentinel` and must be dropped by `sanitize_conflict`, not resolved as an interface literal. Confirm it is never inserted into `iface_lit`.
3. **Linearization scope.** `is_linear_arith` must reject exactly what `linearize` would `debug_assert!` on. Compare it arm by arm with `normalize.rs:106–200`. A `Mul` whose "constant" factor is `(- 4)` as an application rather than a numeral is rejected by both, and so stays opaque: acceptable, but say so in the review.
4. **Constrainedness blast radius.** `mark_constrained(v)` is the only new marking site. Confirm it is not reached for opaque leaves: the slice-42 `ensure_shared_var_alone_does_not_constrain` test must still pass, and DT selector apps must never be marked.
5. **The base-level assertion.** `grep -rn "truth_nodes\|set_truth_terms" crates --include=*.rs`. Every production call site must be behind `install_truth_terms` or be a cache hit. Every test migrated in Task 3 Step 5 must be listed in that task's report.
6. **The spec §10 queue** still holds: `combiner.rs:185` is untouched and still unverified; the `get-value` printer is untouched.

- [ ] **Step 2: Verify any "unreachable" or "blocked" claim by direct repro**

If the review concludes a path is unreachable or a finding is not real, do not accept that on a read. Build the state (an arith `Harness` or an e2e `Solver` script) and run it.

- [ ] **Step 3: Fix findings, re-run the gates, and merge on green**

Any fix repeats Task 5's gates: `mise run test`, the full unfiltered `--features oracle` run, `script_e2e`, `cargo fmt --all` and `mise run lint`. A fix that touches `ensure_shared_var` also re-runs Task 6 Step 5's transition check on QF_UFLIA at minimum (`BENCH_LOGICS=QF_UFLIA BENCH_RUN_ID=slice50-fix mise run bench-run`) and appends the result to the report.

Then, once CI is green and every hard criterion in Task 6 is met:

```bash
gh pr merge --merge
git checkout main && git pull
git branch -d slice50-uflia-shared-compound-args
git push origin --delete slice50-uflia-shared-compound-args
```
