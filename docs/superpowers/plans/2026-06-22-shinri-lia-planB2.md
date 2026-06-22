# QF_LIA Plan B2 Implementation Plan — Stage-B GMI cuts + FBBT + integer bound rounding

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make pure QF_LIA UNSAT instances practically decidable by adding three optimizations on top of the B1 baseline — integer bound rounding, level-0 feasibility-based bound tightening (FBBT), and mixed-integer Gomory (GMI) cuts — all behind a single Stage-B gate, and re-enable the differential UNSAT oracle on curated tiers.

**Architecture:** B1 already decides QF_LIA via simplex + a-priori finite box `M` + splitting-on-demand branch-and-bound, but UNSAT requires exhausting the `~3×10¹²` box. B2 adds (a) integer bound rounding in `build_encoding` that drops the δ-infinitesimal for integer-valued vars, (b) FBBT that shrinks each var's interval inside the box at level 0, and (c) GMI cuts that tighten the LP relaxation until it goes infeasible (Farkas → UNSAT with no enumeration). Cuts are introduced as a **unit** `TCheck::Split(vec![cut])` through the existing Plan A seam — no cross-crate seam change. All three sit behind a `stage_b: bool` flag on `Arith` (default ON); with it OFF, behavior is byte-identical to B1, which makes the differential a direct A/B.

**Tech Stack:** Rust (workspace crates `shinri-arith`, `shinri-theory`, `shinri-sat`, `shinri-solver`); exact-rational arithmetic via `shinri-num` (`Rational`, `Integer`, `DeltaRational`); `easy-smt` driving `z3` + `cvc5` for the differential oracle (dev-only).

## Global Constraints

- **Exact arithmetic only.** All cut/bound/FBBT arithmetic uses `shinri-num` `Rational`/`Integer`/`DeltaRational`. **No floating point** anywhere on the solving path.
- **Soundness is decoupled from optimization.** Completeness and termination rest solely on B1's a-priori box `M` + SAT no-repeat. Cuts, FBBT, and rounding are pure optimizations: with the Stage-B gate OFF the procedure must be byte-identical to B1.
- **Stage-B gate default ON** in production (`Arith::default()` → `stage_b = true`); the differential harness constructs an OFF solver explicitly.
- **Fences unchanged.** QF_UFLIA and mixed QF_LIRA stay fenced to `unknown` (`saw_int_arith && saw_real_arith` → Unknown in `shinri-solver/src/lib.rs`). QF_LRA / QF_UFLRA paths untouched. Pure-Real atoms keep the δ-infinitesimal — rounding must not leak across the Int fence.
- **Cuts/branches are not proof-certified** (out of scope per master spec §1; the debug re-derivation check + differential oracle are the soundness net).
- **Phase gate:** only `shinri-num` on the arithmetic shipping path; `num-bigint`/`num-rational` are dev-only oracle deps.
- **Unit test command:** `cargo test -p shinri-arith <name>`. **Oracle command:** `cargo test -p shinri-solver --features oracle <name> -- --nocapture`. **Workspace:** `cargo test --workspace`.

**Design reference:** `docs/superpowers/specs/2026-06-22-shinri-lia-planB2-design.md`.

---

## Task 1: Stage-B gate plumbing

Add a `stage_b: bool` flag to `Arith` (default `true`), a setter, an `arith_mut()` accessor on `Combiner` (mirroring `euf_mut()`), and a `stage_b` field + setter on the public `Solver`, wired in `check_sat`. Nothing reads the flag yet — this is the seam every later task hides behind.

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (`Arith` struct + `Default` + new `set_stage_b`)
- Modify: `crates/shinri-theory/src/combiner.rs` (add `arith_mut`)
- Modify: `crates/shinri-solver/src/lib.rs` (`Solver` struct + `new` + `set_stage_b` + `check_sat` wiring)
- Test: `crates/shinri-solver/src/lib.rs` (a `#[cfg(test)]` test)

**Interfaces:**
- Produces: `Arith::set_stage_b(&mut self, on: bool)`; `Arith.stage_b: bool` (private field, default `true`); `Combiner::arith_mut(&mut self) -> &mut A`; `Solver::set_stage_b(&mut self, on: bool)`.

- [ ] **Step 1: Add the field and setter to `Arith`.**

In `crates/shinri-arith/src/lib.rs`, add `stage_b: bool` as the last field of `struct Arith` (after `apriori_lits`):

```rust
    /// Master gate for all Plan B2 optimizations (integer bound rounding, FBBT,
    /// GMI cuts). Default ON; the differential harness builds an OFF solver to
    /// reproduce the byte-identical B1 baseline.
    stage_b: bool,
```

In `impl Default for Arith`, set it last in the struct literal:

```rust
            apriori_lits: FxHashSet::default(),
            stage_b: true,
```

In `impl Arith` (any inherent block), add:

```rust
    /// Toggle the Plan B2 optimization gate (default ON). OFF = B1 baseline.
    pub fn set_stage_b(&mut self, on: bool) {
        self.stage_b = on;
    }
```

- [ ] **Step 2: Add `arith_mut` to `Combiner`.**

In `crates/shinri-theory/src/combiner.rs`, right below the existing `pub fn euf_mut(&mut self) -> &mut E { ... }` (~line 62), add:

```rust
    /// Mutable access to the arith theory slot (mirrors `euf_mut`). Used by the
    /// solver to set the Plan B2 Stage-B gate before solving.
    pub fn arith_mut(&mut self) -> &mut A {
        &mut self.arith
    }
```

- [ ] **Step 3: Add the field + setter to `Solver`.**

In `crates/shinri-solver/src/lib.rs`, add to `struct Solver` (after `last_model`):

```rust
    /// Plan B2 Stage-B optimization gate, forwarded to Arith in check_sat.
    stage_b: bool,
```

In `Solver::new`, add `stage_b: true,` to the struct literal, and add the setter to `impl Solver`:

```rust
    /// Toggle the Plan B2 Stage-B gate (default ON). Used by the differential
    /// oracle to compare the cuts-on solver against the B1 baseline.
    pub fn set_stage_b(&mut self, on: bool) {
        self.stage_b = on;
    }
```

- [ ] **Step 4: Wire the gate in `check_sat`.**

In `crates/shinri-solver/src/lib.rs::check_sat`, immediately after the existing
`sat.theory_mut().euf_mut().set_truth_terms(self.t_true, self.t_false);` block (~line 216), add:

```rust
        sat.theory_mut().arith_mut().set_stage_b(self.stage_b);
```

- [ ] **Step 5: Write the test.**

Add to a `#[cfg(test)]` module in `crates/shinri-solver/src/lib.rs` (reuse or create a small `mod stage_b_tests`):

```rust
#[cfg(test)]
mod stage_b_gate_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Op};

    fn build(stage_b: bool) -> SolveOutcome {
        // x >= 0 ; x <= 2 ; 2x = 3  (UNSAT over Int: no integer x with 2x=3)
        let mut s = Solver::new();
        s.set_stage_b(stage_b);
        let int = s.int_sort();
        let x = s.declare_const("x", int);
        let zero = s.numeral(Rational::zero(), int);
        let two = s.numeral(Rational::from_int(2i128.into()), int);
        let three = s.numeral(Rational::from_int(3i128.into()), int);
        let ge0 = s.app(Op::Builtin(BuiltinOp::Ge), &[x, zero]);
        let le2 = s.app(Op::Builtin(BuiltinOp::Le), &[x, two]);
        let twox = s.app(Op::Builtin(BuiltinOp::Mul), &[two, x]);
        let eq3 = s.eq(twox, three);
        s.assert(ge0);
        s.assert(le2);
        s.assert(eq3);
        s.check_sat()
    }

    #[test]
    fn gate_toggles_without_changing_verdict() {
        assert!(matches!(build(true), SolveOutcome::Unsat));
        assert!(matches!(build(false), SolveOutcome::Unsat));
    }
}
```

- [ ] **Step 6: Run the test.**

Run: `cargo test -p shinri-solver stage_b_gate_tests`
Expected: PASS (both gate states agree; nothing reads the flag yet).

- [ ] **Step 7: Verify the workspace still builds and is green.**

Run: `cargo test --workspace`
Expected: PASS (no behavior change).

- [ ] **Step 8: Commit.**

```bash
git add crates/shinri-arith/src/lib.rs crates/shinri-theory/src/combiner.rs crates/shinri-solver/src/lib.rs
git commit -m "feat(lia): Plan B2 Stage-B gate plumbing (Arith.stage_b + Solver/Combiner accessors)"
```

---

## Task 2: Integer bound rounding (folds in B1 §3.5 deferred task)

When the Stage-B gate is on and the bounded quantity is integer-valued, round every bound to an integer at encode time and drop the δ-infinitesimal. This pre-empts the δ-branch (strict bounds) and the coefficient-division branch (`2x ≤ 5` → `x ≤ 2`).

**Files:**
- Modify: `crates/shinri-arith/src/branch.rs` (expose `floor_rational` as `pub(crate)`; add `round_int_bound`)
- Modify: `crates/shinri-arith/src/lib.rs` (`build_encoding`: post-process integer-valued encodings)
- Test: `crates/shinri-arith/src/branch.rs` (round_int_bound unit tests) and `crates/shinri-arith/src/lib.rs` (`mod rounding_tests`)

**Interfaces:**
- Consumes: `Arith.stage_b` (Task 1); `VarStore::is_int`; `crate::branch::floor_ceil`.
- Produces: `crate::branch::round_int_bound(rhs: &Rational, kind: BoundKind, strict: bool) -> DeltaRational` (returns an integer DeltaRational with `k = 0`).

- [ ] **Step 1: Write the failing test for `round_int_bound`.**

In `crates/shinri-arith/src/branch.rs`, inside its `#[cfg(test)] mod tests`, add:

```rust
    use crate::bounds::BoundKind;
    use super::round_int_bound;

    fn dri(n: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::from_int(Integer::from(n)))
    }

    #[test]
    fn round_int_bound_handles_all_cases() {
        // Upper, non-strict: x <= 5/2  ⟹  x <= 2
        assert_eq!(round_int_bound(&r(5, 2), BoundKind::Upper, false), dri(2));
        // Upper, strict: x < 5 (int rhs)  ⟹  x <= 4
        assert_eq!(round_int_bound(&Rational::from_int(5i128.into()), BoundKind::Upper, true), dri(4));
        // Upper, strict: x < 5/2  ⟹  x <= 2  (ceil(5/2)-1 = 3-1 = 2)
        assert_eq!(round_int_bound(&r(5, 2), BoundKind::Upper, true), dri(2));
        // Lower, non-strict: x >= 5/2  ⟹  x >= 3
        assert_eq!(round_int_bound(&r(5, 2), BoundKind::Lower, false), dri(3));
        // Lower, strict: x > 5 (int rhs)  ⟹  x >= 6
        assert_eq!(round_int_bound(&Rational::from_int(5i128.into()), BoundKind::Lower, true), dri(6));
        // Negative: x <= -5/2  ⟹  x <= -3
        assert_eq!(round_int_bound(&r(-5, 2), BoundKind::Upper, false), dri(-3));
    }
```

- [ ] **Step 2: Run it to verify failure.**

Run: `cargo test -p shinri-arith round_int_bound_handles_all_cases`
Expected: FAIL — `round_int_bound` not found.

- [ ] **Step 3: Implement `round_int_bound` and expose `floor_rational`.**

In `crates/shinri-arith/src/branch.rs`, change `fn floor_rational` to `pub(crate) fn floor_rational`, and add (after `floor_ceil`):

```rust
use crate::bounds::BoundKind;

/// Round a bound on an integer-valued variable to an integer `DeltaRational`
/// (k = 0), absorbing strictness:
///   Upper, non-strict  `x ≤ rhs`  ⟹ `x ≤ ⌊rhs⌋`
///   Upper, strict      `x < rhs`  ⟹ `x ≤ ⌈rhs⌉ − 1`
///   Lower, non-strict  `x ≥ rhs`  ⟹ `x ≥ ⌈rhs⌉`
///   Lower, strict      `x > rhs`  ⟹ `x ≥ ⌊rhs⌋ + 1`
pub(crate) fn round_int_bound(rhs: &Rational, kind: BoundKind, strict: bool) -> DeltaRational {
    let floor = floor_rational(rhs);
    let is_int = &Rational::from_int(floor.clone()) == rhs;
    let ceil = if is_int { floor.clone() } else { floor.clone() + Integer::one() };
    let bound = match (kind, strict) {
        (BoundKind::Upper, false) => floor,
        (BoundKind::Upper, true) => ceil - Integer::one(),
        (BoundKind::Lower, false) => ceil,
        (BoundKind::Lower, true) => floor + Integer::one(),
    };
    DeltaRational::from_rational(Rational::from_int(bound))
}
```

- [ ] **Step 4: Run the helper test.**

Run: `cargo test -p shinri-arith round_int_bound_handles_all_cases`
Expected: PASS.

- [ ] **Step 5: Write the failing integration test for `build_encoding` rounding.**

In `crates/shinri-arith/src/lib.rs`, add a new test module. It asserts that an Int strict atom encodes to an integer bound with `k = 0` (no δ) when the gate is on, and that a Real atom keeps its δ.

```rust
#[cfg(test)]
mod rounding_tests {
    use super::*;
    use crate::encode::AtomEncoding;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn int_var(ctx: &mut Context, name: &str) -> TermId {
        let int = ctx.int_sort();
        let s = ctx.declare_fun(name, &[], int);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    // x < 5 over Int (gate ON) must encode pos as Upper bound 4 with k = 0.
    #[test]
    fn int_strict_bound_rounds_and_drops_delta() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), ctx.int_sort());
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::Lt), &[x, five]).unwrap();
        let mut arith = Arith::default(); // stage_b = true
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        arith.new_var(&mut cx, Var::new(0), lt);
        match arith.enc[0].clone().unwrap() {
            AtomEncoding::Ineq { pos: (BoundKind::Upper, dr), .. } => {
                assert_eq!(*dr.c(), Rational::from_int(4i128.into()));
                assert!(dr.k().is_zero(), "δ must be dropped for an Int strict bound");
            }
            other => panic!("expected Upper Ineq, got {other:?}"),
        }
    }

    // 2x <= 5 over Int (gate ON): bound on x is 5/2 → rounds to 2.
    #[test]
    fn int_coefficient_division_rounds() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), ctx.int_sort());
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), ctx.int_sort());
        let twox = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[two, x]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[twox, five]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        arith.new_var(&mut cx, Var::new(0), le);
        match arith.enc[0].clone().unwrap() {
            AtomEncoding::Ineq { pos: (BoundKind::Upper, dr), .. } => {
                assert_eq!(*dr.c(), Rational::from_int(2i128.into()));
                assert!(dr.k().is_zero());
            }
            other => panic!("expected Upper Ineq, got {other:?}"),
        }
    }

    // Real x < 5 must KEEP its δ (rounding does not cross the Int fence).
    #[test]
    fn real_strict_bound_keeps_delta() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let xs = ctx.declare_fun("x", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let five = ctx.mk_numeral(Rational::from_int(5i128.into()), real);
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::Lt), &[x, five]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        arith.new_var(&mut cx, Var::new(0), lt);
        match arith.enc[0].clone().unwrap() {
            AtomEncoding::Ineq { pos: (BoundKind::Upper, dr), .. } => {
                assert!(!dr.k().is_zero(), "Real strict bound must keep δ");
            }
            other => panic!("expected Upper Ineq, got {other:?}"),
        }
    }
}
```

Note: `enc` is a private field, but these tests live in the same crate/module tree (`super::*`), so direct field access is fine.

- [ ] **Step 6: Run to verify failure.**

Run: `cargo test -p shinri-arith rounding_tests`
Expected: FAIL — `int_strict_bound_rounds_and_drops_delta` and `int_coefficient_division_rounds` fail (δ still present / bound not rounded); `real_strict_bound_keeps_delta` already passes.

- [ ] **Step 7: Implement rounding in `build_encoding`.**

In `crates/shinri-arith/src/lib.rs::build_encoding`, after the `AtomEncoding::Ineq { var, pos, neg }` value is constructed and **before** it is returned, capture it into a mutable local and post-process. Replace the final `AtomEncoding::Ineq { ... }` expression in the `Rel::Le | Rel::Lt` arm with:

```rust
                let mut enc = AtomEncoding::Ineq {
                    var,
                    pos: (pk, DeltaRational::new(rhs.clone(), pkk)),
                    neg: (nk, DeltaRational::new(rhs, nkk)),
                };
                // Stage-B integer bound rounding: if the bounded quantity is
                // integer-valued, replace each (kind, value) with the integer
                // round and drop the δ. `strict` is read off the δ-coefficient
                // (nonzero ⇒ strict). Handles flipped-coefficient cases because
                // `kind` and `value` are already resolved here.
                if self.stage_b && self.comb_is_int_valued(&n.comb) {
                    if let AtomEncoding::Ineq { pos, neg, .. } = &mut enc {
                        for slot in [pos, neg] {
                            let strict = !slot.1.k().is_zero();
                            slot.1 = crate::branch::round_int_bound(slot.1.c(), slot.0, strict);
                        }
                    }
                }
                enc
```

(`n` is the `&Normalized` parameter of `build_encoding`; `n.comb` is in scope.)

- [ ] **Step 8: Add the `comb_is_int_valued` helper.**

In `impl Arith`, add:

```rust
    /// True iff the linear combination evaluates to an integer for every model:
    /// every variable is Int-sorted AND every coefficient is an integer. In a
    /// pure-Int query this holds for all problem vars and all slacks.
    fn comb_is_int_valued(&self, comb: &LinComb) -> bool {
        !comb.0.is_empty()
            && comb
                .0
                .iter()
                .all(|(v, c)| self.vars.is_int(*v) && c.denom() == Integer::one())
    }
```

- [ ] **Step 9: Run the rounding tests.**

Run: `cargo test -p shinri-arith rounding_tests`
Expected: PASS (all three).

- [ ] **Step 10: Run the whole arith crate.**

Run: `cargo test -p shinri-arith`
Expected: PASS — existing B1 tests still green (they use Real vars, unaffected; Int tests now round but remain sat/unsat-equivalent).

- [ ] **Step 11: Commit.**

```bash
git add crates/shinri-arith/src/branch.rs crates/shinri-arith/src/lib.rs
git commit -m "feat(lia): Stage-B integer bound rounding — drop δ for integer-valued bounds (folds in B1 §3.5)"
```

---

## Task 3: FBBT bound-derivation module (`propagate.rs`)

A pure module that, given the tableau rows + current bounds + var store, derives tightened **integer** bounds to a fixpoint. No I/O, no `Arith` mutation — returns the list of tightenings for the caller (Task 4) to install.

**Files:**
- Create: `crates/shinri-arith/src/propagate.rs`
- Modify: `crates/shinri-arith/src/lib.rs` (add `pub mod propagate;`)
- Test: `crates/shinri-arith/src/propagate.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `Tableau` (`rows`, `basic`, `Row::coeff`, `Row::vars`), `Bounds` (`lower`/`upper` → `Option<&(DeltaRational, Lit)>`), `VarStore` (`is_int`, `len`).
- Produces: `crate::propagate::tighten_to_fixpoint(tableau: &Tableau, bounds: &Bounds, vars: &VarStore, max_rounds: usize) -> Vec<(ArithVar, BoundKind, DeltaRational)>` — each entry is a new, strictly tighter integer bound to install.

- [ ] **Step 1: Register the module.**

In `crates/shinri-arith/src/lib.rs`, add to the module list (with the others near the top): `pub mod propagate;`

- [ ] **Step 2: Write the failing test.**

Create `crates/shinri-arith/src/propagate.rs` with only the test first:

```rust
//! Feasibility-based bound tightening (FBBT) over the tableau rows. Pure: reads
//! tableau + bounds, returns tighter INTEGER bounds for the caller to install.

#[cfg(test)]
mod tests {
    use super::tighten_to_fixpoint;
    use crate::bounds::{BoundKind, Bounds};
    use crate::normalize::LinComb;
    use crate::tableau::Tableau;
    use crate::vars::{ArithVar, VarStore};
    use shinri_core::{Lit, Var};
    use shinri_num::{DeltaRational, Integer, Rational};

    fn dr(n: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::from_int(Integer::from(n)))
    }
    fn lit() -> Lit {
        Lit::new(Var::new(0), true)
    }

    // System: x, y integer in [0, 10]; slack s = x + y with s <= 1.
    // FBBT must derive x <= 1 and y <= 1 (since the other var ≥ 0).
    #[test]
    fn fbbt_tightens_from_a_sum_bound() {
        let mut vars = VarStore::default();
        let tx = shinri_core::TermId::new(1).unwrap();
        let ty = shinri_core::TermId::new(2).unwrap();
        let x = vars.problem_var_sorted(tx, true);
        let y = vars.problem_var_sorted(ty, true);
        let comb = LinComb(vec![(x, Rational::one()), (y, Rational::one())]);
        let s = vars.slack_var(&comb);

        let mut tab = Tableau::default();
        tab.define_slack(s, &comb);

        let mut b = Bounds::default();
        b.ensure(vars.len());
        // x, y in [0, 10]
        for v in [x, y] {
            b.tighten(v, BoundKind::Lower, dr(0), lit());
            b.tighten(v, BoundKind::Upper, dr(10), lit());
        }
        // s <= 1, s >= 0
        b.tighten(s, BoundKind::Lower, dr(0), lit());
        b.tighten(s, BoundKind::Upper, dr(1), lit());

        let out = tighten_to_fixpoint(&tab, &b, &vars, 8);
        // Expect x <= 1 and y <= 1 among the tightenings.
        assert!(out.contains(&(x, BoundKind::Upper, dr(1))), "got {out:?}");
        assert!(out.contains(&(y, BoundKind::Upper, dr(1))), "got {out:?}");
    }

    // Integer rounding: slack s = 3x with s <= 7  ⟹  x <= 2  (⌊7/3⌋), not 7/3.
    #[test]
    fn fbbt_rounds_to_integer() {
        let mut vars = VarStore::default();
        let tx = shinri_core::TermId::new(1).unwrap();
        let x = vars.problem_var_sorted(tx, true);
        let comb = LinComb(vec![(x, Rational::from_int(3i128.into()))]);
        let s = vars.slack_var(&comb);
        let mut tab = Tableau::default();
        tab.define_slack(s, &comb);
        let mut b = Bounds::default();
        b.ensure(vars.len());
        b.tighten(x, BoundKind::Lower, dr(0), lit());
        b.tighten(x, BoundKind::Upper, dr(100), lit());
        b.tighten(s, BoundKind::Lower, dr(0), lit());
        b.tighten(s, BoundKind::Upper, dr(7), lit());
        let out = tighten_to_fixpoint(&tab, &b, &vars, 8);
        assert!(out.contains(&(x, BoundKind::Upper, dr(2))), "got {out:?}");
    }
}
```

- [ ] **Step 3: Run to verify failure.**

Run: `cargo test -p shinri-arith fbbt_`
Expected: FAIL — `tighten_to_fixpoint` not found.

- [ ] **Step 4: Implement the module.**

Prepend to `crates/shinri-arith/src/propagate.rs` (above the test module):

```rust
use crate::bounds::{BoundKind, Bounds};
use crate::branch::round_int_bound;
use crate::tableau::Tableau;
use crate::vars::{ArithVar, VarStore};
use shinri_num::{DeltaRational, Rational};

/// A working copy of the bounds as plain rationals (δ dropped — FBBT reasons
/// over the closed integer relaxation). `None` = unbounded on that side.
#[derive(Clone)]
struct Interval {
    lo: Option<Rational>,
    hi: Option<Rational>,
}

/// Derive tighter INTEGER bounds from the tableau rows by interval propagation
/// to a fixpoint (or `max_rounds`). Returns only bounds strictly tighter than
/// the input. Monotone: never widens, so always sound.
pub fn tighten_to_fixpoint(
    tableau: &Tableau,
    bounds: &Bounds,
    vars: &VarStore,
    max_rounds: usize,
) -> Vec<(ArithVar, BoundKind, DeltaRational)> {
    let n = vars.len();
    // Seed working intervals from the live bounds (drop δ: use the rational part).
    let mut iv: Vec<Interval> = (0..n)
        .map(|i| {
            let v = ArithVar(i as u32);
            Interval {
                lo: bounds.lower(v).map(|(d, _)| d.c().clone()),
                hi: bounds.upper(v).map(|(d, _)| d.c().clone()),
            }
        })
        .collect();

    for _ in 0..max_rounds {
        let mut changed = false;
        // Each basic row is  s = Σ a_j x_j. Treat it as the equality
        // s − Σ a_j x_j = 0 and propagate a bound onto each member, including s.
        let basics: Vec<ArithVar> = tableau.basic.iter().copied().collect();
        for s in basics {
            let row = tableau.row(s);
            // members: (var, coeff) for s (coeff −1) and each x_j (coeff +a_j),
            // expressing  Σ coeff·var = 0.
            let mut members: Vec<(ArithVar, Rational)> = vec![(s, -Rational::one())];
            for j in row.vars() {
                members.push((j, row.coeff(j)));
            }
            // For each target member k: coeff_k·x_k = −Σ_{i≠k} coeff_i·x_i.
            for k in 0..members.len() {
                let (vk, ck) = members[k].clone();
                if ck.is_zero() {
                    continue;
                }
                // Bound the RHS sum −Σ_{i≠k} coeff_i·x_i using the others' intervals.
                let (mut rhs_lo, mut rhs_hi) = (Some(Rational::zero()), Some(Rational::zero()));
                for (i, (vi, ci)) in members.iter().enumerate() {
                    if i == k {
                        continue;
                    }
                    // contribution = −ci·x_i ; its range from x_i's interval.
                    let neg = -ci.clone();
                    let (clo, chi) = term_range(&neg, &iv[vi.index()]);
                    rhs_lo = add_opt(rhs_lo, clo);
                    rhs_hi = add_opt(rhs_hi, chi);
                }
                // x_k = rhs / ck. Dividing by a negative flips the interval ends.
                let (mut nlo, mut nhi) = (
                    rhs_lo.map(|r| r / ck.clone()),
                    rhs_hi.map(|r| r / ck.clone()),
                );
                if ck.is_negative() {
                    std::mem::swap(&mut nlo, &mut nhi);
                }
                // Integer rounding for Int vars; tighten only if strictly better.
                let is_int = vars.is_int(vk);
                if let Some(hi) = nhi {
                    let cand = if is_int {
                        round_int_bound(&hi, BoundKind::Upper, false).c().clone()
                    } else {
                        hi
                    };
                    if iv[vk.index()].hi.as_ref().map_or(true, |cur| &cand < cur) {
                        iv[vk.index()].hi = Some(cand);
                        changed = true;
                    }
                }
                if let Some(lo) = nlo {
                    let cand = if is_int {
                        round_int_bound(&lo, BoundKind::Lower, false).c().clone()
                    } else {
                        lo
                    };
                    if iv[vk.index()].lo.as_ref().map_or(true, |cur| &cand > cur) {
                        iv[vk.index()].lo = Some(cand);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Emit only bounds strictly tighter than the original live bounds.
    let mut out = Vec::new();
    for i in 0..n {
        let v = ArithVar(i as u32);
        if let Some(hi) = &iv[i].hi {
            let tighter = bounds.upper(v).map_or(true, |(d, _)| hi < d.c());
            if tighter {
                out.push((v, BoundKind::Upper, DeltaRational::from_rational(hi.clone())));
            }
        }
        if let Some(lo) = &iv[i].lo {
            let tighter = bounds.lower(v).map_or(true, |(d, _)| lo > d.c());
            if tighter {
                out.push((v, BoundKind::Lower, DeltaRational::from_rational(lo.clone())));
            }
        }
    }
    out
}

/// Range of `coeff · x` over x's interval. `None` end = unbounded.
fn term_range(coeff: &Rational, iv: &Interval) -> (Option<Rational>, Option<Rational>) {
    if coeff.is_zero() {
        return (Some(Rational::zero()), Some(Rational::zero()));
    }
    let a = iv.lo.clone().map(|l| coeff.clone() * l);
    let b = iv.hi.clone().map(|h| coeff.clone() * h);
    if coeff.is_negative() {
        // negative coeff flips which end is the min/max
        (b, a)
    } else {
        (a, b)
    }
}

/// `a + b` where `None` is an unbounded (infinite) end → result unbounded.
fn add_opt(a: Option<Rational>, b: Option<Rational>) -> Option<Rational> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x + y),
        _ => None,
    }
}
```

- [ ] **Step 5: Run the FBBT tests.**

Run: `cargo test -p shinri-arith fbbt_`
Expected: PASS (both `fbbt_tightens_from_a_sum_bound` and `fbbt_rounds_to_integer`).

- [ ] **Step 6: Commit.**

```bash
git add crates/shinri-arith/src/propagate.rs crates/shinri-arith/src/lib.rs
git commit -m "feat(lia): FBBT bound-derivation module — integer interval propagation over tableau rows"
```

---

## Task 4: Wire FBBT into the level-0 seed

Run FBBT once at level 0, right after the a-priori box is seeded, and install its tightenings as level-0 axiomatic bounds under stripped sentinels.

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (`seed_apriori_if_needed` → also run FBBT; gate on `stage_b`)
- Test: `crates/shinri-arith/src/lib.rs` (`mod fbbt_wiring_tests`)

**Interfaces:**
- Consumes: `crate::propagate::tighten_to_fixpoint` (Task 3); `Arith.stage_b`; existing `apriori_lits` / `fresh_sentinel` / `apply_bound`.
- Produces: tightened bounds visible via `self.bounds.upper/lower` after the first level-0 check.

- [ ] **Step 1: Write the failing test.**

In `crates/shinri-arith/src/lib.rs`, add:

```rust
#[cfg(test)]
mod fbbt_wiring_tests {
    use super::*;
    use crate::bounds::BoundKind;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_theory::{AtomRegistry, EqualityEngine, Effort, TheoryCtx, TheorySolver};

    fn int_var(ctx: &mut Context, name: &str) -> TermId {
        let int = ctx.int_sort();
        let s = ctx.declare_fun(name, &[], int);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    // x, y >= 0 and x + y <= 1 ⟹ FBBT must tighten x's upper bound far below M.
    #[test]
    fn fbbt_shrinks_box_at_level_zero() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let zero = ctx.mk_numeral(Rational::zero(), ctx.int_sort());
        let one = ctx.mk_numeral(Rational::one(), ctx.int_sort());
        let gx = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, zero]).unwrap();
        let gy = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[y, zero]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, one]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        for (i, a) in [gx, gy, le].iter().enumerate() {
            arith.new_var(&mut cx, Var::new(i as u32), *a);
        }
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.assert(&mut cx, Lit::new(Var::new(2), true));
        let _ = arith.check(&mut cx, Effort::Full);
        // x is problem var 0. Its FBBT upper bound must be ≤ 1 (≪ M).
        let xv = arith.vars.problem_var(x);
        let ub = arith.bounds.upper(xv).expect("x has an upper bound").0.c().clone();
        assert!(ub <= Rational::one(), "FBBT should bound x ≤ 1, got {ub:?}");
    }

    // With the gate OFF, FBBT must NOT run: x keeps the (huge) a-priori bound.
    #[test]
    fn fbbt_disabled_when_stage_b_off() {
        let mut ctx = Context::new();
        let x = int_var(&mut ctx, "x");
        let y = int_var(&mut ctx, "y");
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let zero = ctx.mk_numeral(Rational::zero(), ctx.int_sort());
        let one = ctx.mk_numeral(Rational::one(), ctx.int_sort());
        let gx = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, zero]).unwrap();
        let gy = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[y, zero]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, one]).unwrap();
        let mut arith = Arith::default();
        arith.set_stage_b(false);
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        for (i, a) in [gx, gy, le].iter().enumerate() {
            arith.new_var(&mut cx, Var::new(i as u32), *a);
        }
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.assert(&mut cx, Lit::new(Var::new(2), true));
        let _ = arith.check(&mut cx, Effort::Full);
        let xv = arith.vars.problem_var(x);
        let ub = arith.bounds.upper(xv).expect("x has an upper bound").0.c().clone();
        assert!(ub > Rational::one(), "gate OFF: x must keep the large a-priori bound, got {ub:?}");
    }
}
```

- [ ] **Step 2: Run to verify failure.**

Run: `cargo test -p shinri-arith fbbt_wiring_tests`
Expected: FAIL — `fbbt_shrinks_box_at_level_zero` fails (x still bounded by `M`); `fbbt_disabled_when_stage_b_off` passes.

- [ ] **Step 3: Add the FBBT pass and call it from the seed.**

In `crates/shinri-arith/src/lib.rs`, add a method to `impl Arith`:

```rust
    /// One-shot level-0 FBBT pass: derive tighter integer bounds from the
    /// tableau rows and install them as level-0 axiomatic bounds under stripped
    /// sentinels (like the a-priori box). Stage-B only.
    fn run_fbbt(&mut self) {
        const MAX_ROUNDS: usize = 16;
        let tightenings =
            crate::propagate::tighten_to_fixpoint(&self.tableau, &self.bounds, &self.vars, MAX_ROUNDS);
        for (v, kind, val) in tightenings {
            let lit = self.fresh_sentinel();
            self.apriori_lits.insert(lit.code());
            let _ = self.apply_bound(v, kind, val, lit);
        }
    }
```

In `seed_apriori_if_needed`, after the existing loop that seeds the `−M ≤ x ≤ M` box (just before the method returns), add:

```rust
        if self.stage_b {
            self.run_fbbt();
        }
```

This runs after the box is in place, so FBBT starts from finite two-sided intervals and only tightens. The sentinel lits are added to `apriori_lits`, so `strip_apriori` removes them from conflicts — preserving B1's conflict-core soundness.

- [ ] **Step 4: Run the wiring tests.**

Run: `cargo test -p shinri-arith fbbt_wiring_tests`
Expected: PASS (both).

- [ ] **Step 5: Run the arith crate + workspace.**

Run: `cargo test -p shinri-arith && cargo test --workspace`
Expected: PASS — B1 behavior preserved (Real path: no Int vars → box not seeded → FBBT no-op; gate OFF → FBBT skipped).

- [ ] **Step 6: Commit.**

```bash
git add crates/shinri-arith/src/lib.rs
git commit -m "feat(lia): wire FBBT into level-0 seed — tighten the a-priori box before search (Stage-B)"
```

---

## Task 5: GMI cut derivation module (`cuts.rs`)

A pure module that derives a mixed-integer Gomory cut from a fractional basic integer var's tableau row, expressed as a `LinComb` over **problem vars** + an integer rhs, with a separation + re-derivation self-check. No `Arith` mutation.

**Files:**
- Create: `crates/shinri-arith/src/cuts.rs`
- Modify: `crates/shinri-arith/src/lib.rs` (`pub mod cuts;`)
- Test: `crates/shinri-arith/src/cuts.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `Tableau` (`row`, `Row::coeff`/`vars`), `Bounds` (active bound per nonbasic), `value: &[DeltaRational]`, `VarStore` (`is_int`, `is_slack`), `tableau`-defined slack combs (via a passed-in expander).
- Produces:
  - `pub struct GmiCut { pub lhs: Vec<(ArithVar, Rational)>, pub rhs: Rational }` — a `≤` cut `Σ lhs ≤ rhs` over **problem** vars.
  - `pub fn derive_gmi(basic: ArithVar, tableau: &Tableau, bounds: &Bounds, value: &[DeltaRational], vars: &VarStore, expand_slack: &dyn Fn(ArithVar) -> Vec<(ArithVar, Rational)>) -> Option<GmiCut>` — `None` if the row is integral or degenerate (caller falls back to branch).
  - `pub fn separates(cut: &GmiCut, value: &[DeltaRational]) -> bool` — true iff the current vertex violates the cut (debug check).

> **Verification crux.** The GMI coefficient formula is the one place to validate carefully against the unit tests below and, ultimately, against the differential oracle (Task 8). Cuts are disable-able by construction, so a wrong cut is caught (differential panic), never silently shipped. Keep all arithmetic in exact `Rational`/`Integer`.

- [ ] **Step 1: Register the module.**

In `crates/shinri-arith/src/lib.rs`: `pub mod cuts;`

- [ ] **Step 2: Write the failing tests.**

Create `crates/shinri-arith/src/cuts.rs` with the test module first:

```rust
//! Mixed-integer Gomory (GMI) cut derivation from a fractional tableau row.
//! Pure: reads tableau + bounds + values, returns a `≤` cut over problem vars.
//! Exact rational arithmetic only.

#[cfg(test)]
mod tests {
    use super::{derive_gmi, separates, GmiCut};
    use crate::bounds::{BoundKind, Bounds};
    use crate::normalize::LinComb;
    use crate::tableau::Tableau;
    use crate::vars::{ArithVar, VarStore};
    use shinri_core::{Lit, TermId, Var};
    use shinri_num::{DeltaRational, Integer, Rational};

    fn dr_r(n: i128, d: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::new(Integer::from(n), Integer::from(d)))
    }
    fn dr(n: i128) -> DeltaRational {
        DeltaRational::from_rational(Rational::from_int(Integer::from(n)))
    }
    fn lit() -> Lit { Lit::new(Var::new(0), true) }

    // Classic 2-var Gomory example: feasible LP vertex is fractional in an
    // integer var; the derived cut must separate that vertex and admit all
    // integer points. We assert separation (the robust, formula-agnostic check)
    // and that the cut is over problem vars only.
    #[test]
    fn gmi_cut_separates_fractional_vertex() {
        // Problem: x, y integer ≥ 0; slack s = x + y. Suppose the simplex sits
        // at x = 3/2 (basic, fractional), with nonbasic vars at their bounds.
        let mut vars = VarStore::default();
        let tx = TermId::new(1).unwrap();
        let ty = TermId::new(2).unwrap();
        let x = vars.problem_var_sorted(tx, true);
        let y = vars.problem_var_sorted(ty, true);
        let comb = LinComb(vec![(x, Rational::one()), (y, Rational::one())]);
        let s = vars.slack_var(&comb);

        let mut tab = Tableau::default();
        tab.define_slack(s, &comb);
        // Pivot x into the basis so x has a row in terms of {s, y}.
        tab.pivot(s, x); // x = s − y

        let mut b = Bounds::default();
        b.ensure(vars.len());
        b.tighten(x, BoundKind::Lower, dr(0), lit());
        b.tighten(y, BoundKind::Lower, dr(0), lit());
        b.tighten(s, BoundKind::Lower, dr(0), lit());
        b.tighten(s, BoundKind::Upper, dr_r(3, 2), lit()); // s ≤ 3/2

        // Values: nonbasic s at its upper bound 3/2, y at lower 0 ⟹ x = 3/2.
        let mut value = vec![DeltaRational::from_rational(Rational::zero()); vars.len()];
        value[s.index()] = dr_r(3, 2);
        value[y.index()] = dr(0);
        value[x.index()] = dr_r(3, 2);

        let comb_of = |v: ArithVar| -> Vec<(ArithVar, Rational)> {
            if v == s { vec![(x, Rational::one()), (y, Rational::one())] } else { vec![(v, Rational::one())] }
        };
        let cut = derive_gmi(x, &tab, &b, &value, &vars, &comb_of)
            .expect("fractional row ⟹ a cut");
        // The cut must be over PROBLEM vars only (no slack s).
        assert!(cut.lhs.iter().all(|(v, _)| !vars.is_slack(*v)), "cut over problem vars: {cut:?}");
        // The cut must separate the current vertex.
        assert!(separates(&cut, &value), "cut must exclude x=3/2 vertex: {cut:?}");
    }

    // An already-integral row yields no cut.
    #[test]
    fn integral_row_yields_no_cut() {
        let mut vars = VarStore::default();
        let tx = TermId::new(1).unwrap();
        let ty = TermId::new(2).unwrap();
        let x = vars.problem_var_sorted(tx, true);
        let y = vars.problem_var_sorted(ty, true);
        let comb = LinComb(vec![(x, Rational::one()), (y, Rational::one())]);
        let s = vars.slack_var(&comb);
        let mut tab = Tableau::default();
        tab.define_slack(s, &comb);
        tab.pivot(s, x);
        let mut b = Bounds::default();
        b.ensure(vars.len());
        let mut value = vec![DeltaRational::from_rational(Rational::zero()); vars.len()];
        value[x.index()] = dr(2); // integral
        let comb_of = |v: ArithVar| -> Vec<(ArithVar, Rational)> {
            if v == s { vec![(x, Rational::one()), (y, Rational::one())] } else { vec![(v, Rational::one())] }
        };
        assert!(derive_gmi(x, &tab, &b, &value, &vars, &comb_of).is_none());
    }
}
```

- [ ] **Step 3: Run to verify failure.**

Run: `cargo test -p shinri-arith gmi_`
Expected: FAIL — `derive_gmi`/`separates`/`GmiCut` not found.

- [ ] **Step 4: Implement the GMI derivation.**

Prepend to `crates/shinri-arith/src/cuts.rs` (above the tests):

```rust
use crate::bounds::{BoundKind, Bounds};
use crate::branch::floor_rational;
use crate::tableau::Tableau;
use crate::vars::{ArithVar, VarStore};
use rustc_hash::FxHashMap;
use shinri_num::{DeltaRational, Integer, Rational};

/// A `≤` cut `Σ (coeff·var) ≤ rhs` over PROBLEM variables, valid for every
/// integer point of the feasible region.
#[derive(Clone, Debug)]
pub struct GmiCut {
    pub lhs: Vec<(ArithVar, Rational)>,
    pub rhs: Rational,
}

/// Fractional part `r − ⌊r⌋ ∈ [0, 1)`.
fn frac(r: &Rational) -> Rational {
    r.clone() - Rational::from_int(floor_rational(r))
}

/// Derive a GMI cut from `basic`'s tableau row. Returns `None` if `basic`'s
/// value is integral or no separating cut arises (caller branches instead).
///
/// Row form: `basic = Σ_{j∈N} a_j · x_j`. Each nonbasic `x_j` sits at an active
/// bound; orient `y_j = x_j − lo_j ≥ 0` (at lower) or `y_j = hi_j − x_j ≥ 0`
/// (at upper). With `f0 = frac(β(basic))` and `f_j = frac(±a_j)` (sign per
/// orientation), the GMI cut on the y's is `Σ ψ(ā_j)·y_j ≥ f0`, where for an
/// integer-constrained nonbasic `ψ(ā) = f` if `f ≤ f0` else `f0(1−f)/(1−f0)`.
/// Substituting the y's back and flipping to `≤` yields a cut over problem vars.
pub fn derive_gmi(
    basic: ArithVar,
    tableau: &Tableau,
    bounds: &Bounds,
    value: &[DeltaRational],
    vars: &VarStore,
    expand_slack: &dyn Fn(ArithVar) -> Vec<(ArithVar, Rational)>,
) -> Option<GmiCut> {
    let beta = value[basic.index()].c().clone();
    let f0 = frac(&beta);
    if f0.is_zero() {
        return None; // integral row → nothing to cut
    }
    let one = Rational::one();
    let row = tableau.row(basic);

    // Accumulate the cut as `Σ g_j · y_j ≥ f0`, in terms of the oriented
    // nonbasic slacks y_j, then translate back to x_j.
    // We build the cut directly over x-space: start with `≥ f0` and add each
    // nonbasic's contribution g_j·y_j, expanding y_j = ±(x_j − bound).
    let mut xcoeff: FxHashMap<ArithVar, Rational> = FxHashMap::default();
    let mut rhs = f0.clone(); // RHS of the `Σ g·x (…) ≥ rhs` form (adjusted below)

    for j in row.vars() {
        let a_j = row.coeff(j);
        if a_j.is_zero() {
            continue;
        }
        // Active bound + orientation sign: at lower ⟹ y = x − lo (sign +1);
        // at upper ⟹ y = hi − x (sign −1). Prefer lower if both exist and the
        // value is at lower; else use whichever bound the value sits on.
        let at_lower = bounds
            .lower(j)
            .map(|(d, _)| d.c() == value[j.index()].c())
            .unwrap_or(false);
        let (sign, bound) = if at_lower {
            (one.clone(), bounds.lower(j).unwrap().0.c().clone())
        } else if let Some((d, _)) = bounds.upper(j) {
            (-one.clone(), d.c().clone())
        } else if let Some((d, _)) = bounds.lower(j) {
            (one.clone(), d.c().clone())
        } else {
            // free nonbasic with nonzero coeff: cannot orient ⟹ no cut.
            return None;
        };
        // Oriented coefficient ā_j = sign · a_j  (so the row reads basic = … + ā_j·y_j + const).
        let a_bar = sign.clone() * a_j.clone();
        // GMI coefficient g_j for an integer nonbasic.
        let f = frac(&a_bar);
        let g = if f <= f0 {
            f.clone()
        } else {
            f0.clone() * (one.clone() - f.clone()) / (one.clone() - f0.clone())
        };
        if g.is_zero() {
            continue;
        }
        // y_j = sign · (x_j − bound)  ⟹  g·y_j = g·sign·x_j − g·sign·bound.
        let gx = g.clone() * sign.clone();
        *xcoeff.entry(j).or_insert_with(Rational::zero) += gx.clone();
        rhs += gx * bound; // move constant to RHS:  Σ g·sign·x ≥ f0 + Σ g·sign·bound
    }

    if xcoeff.is_empty() {
        return None;
    }

    // We now have  Σ xcoeff·x ≥ rhs. Flip to ≤ for the GmiCut convention.
    let mut lhs: Vec<(ArithVar, Rational)> = xcoeff.into_iter().map(|(v, c)| (v, -c)).collect();
    let mut rhs = -rhs;

    // Expand any slack vars in lhs to problem vars via `expand_slack`.
    let mut prob: FxHashMap<ArithVar, Rational> = FxHashMap::default();
    for (v, c) in lhs.drain(..) {
        if vars.is_slack(v) {
            for (pv, pc) in expand_slack(v) {
                *prob.entry(pv).or_insert_with(Rational::zero) += c.clone() * pc;
            }
        } else {
            *prob.entry(v).or_insert_with(Rational::zero) += c;
        }
    }
    let lhs: Vec<(ArithVar, Rational)> = prob.into_iter().filter(|(_, c)| !c.is_zero()).collect();
    if lhs.is_empty() {
        return None;
    }
    // Tighten to integer rhs: the LHS is integer-valued (problem vars are Int,
    // but coefficients may be fractional) — DO NOT floor the rhs here, because
    // fractional LHS coefficients make the row non-integer-valued in general.
    // Soundness rests on the exact GMI derivation; integrality tightening of the
    // cut itself is left to the differential-validated future work.
    let _ = &rhs;
    Some(GmiCut { lhs, rhs })
}

/// True iff the current assignment violates the `≤` cut (strict separation).
pub fn separates(cut: &GmiCut, value: &[DeltaRational]) -> bool {
    let mut acc = Rational::zero();
    for (v, c) in &cut.lhs {
        acc += c.clone() * value[v.index()].c().clone();
    }
    acc > cut.rhs
}
```

- [ ] **Step 5: Run the cut tests.**

Run: `cargo test -p shinri-arith gmi_ integral_row_yields_no_cut`
Expected: PASS — the cut separates the `x = 3/2` vertex and is over problem vars; the integral row yields `None`.

> If `gmi_cut_separates_fractional_vertex` fails on separation, the orientation/`ψ` formula needs correction — fix `derive_gmi` until the vertex is strictly excluded. This is the verification crux; the differential oracle (Task 8) is the final arbiter.

- [ ] **Step 6: Add a debug-only re-derivation assert helper (used in Task 6).**

Append to `crates/shinri-arith/src/cuts.rs`:

```rust
/// Debug self-check: re-derive the cut from the same inputs and assert it
/// matches, and that it separates the current vertex. Compiled out of release.
#[cfg(debug_assertions)]
pub fn debug_validate(
    cut: &GmiCut,
    basic: ArithVar,
    tableau: &Tableau,
    bounds: &Bounds,
    value: &[DeltaRational],
    vars: &VarStore,
    expand_slack: &dyn Fn(ArithVar) -> Vec<(ArithVar, Rational)>,
) {
    assert!(separates(cut, value), "GMI cut fails to separate the current vertex");
    let again = derive_gmi(basic, tableau, bounds, value, vars, expand_slack)
        .expect("re-derivation must reproduce a cut");
    let mut a: Vec<_> = cut.lhs.clone();
    let mut b: Vec<_> = again.lhs.clone();
    a.sort_by_key(|(v, _)| v.0);
    b.sort_by_key(|(v, _)| v.0);
    assert_eq!(a, b, "GMI re-derivation disagreement (lhs)");
    assert_eq!(cut.rhs, again.rhs, "GMI re-derivation disagreement (rhs)");
}
```

- [ ] **Step 7: Run the arith crate.**

Run: `cargo test -p shinri-arith`
Expected: PASS.

- [ ] **Step 8: Commit.**

```bash
git add crates/shinri-arith/src/cuts.rs crates/shinri-arith/src/lib.rs
git commit -m "feat(lia): GMI cut derivation module — exact-rational mixed-integer Gomory cut + separation check"
```

---

## Task 6: Branch-and-cut wiring + budgets

In `integer_check`, when the Stage-B gate is on and budgets allow, derive a GMI cut from the most-fractional integer var's row and return it as a **unit** `TCheck::Split(vec![cut_atom])`; otherwise branch (B1). Build the cut atom over problem-var terms.

**Files:**
- Modify: `crates/shinri-arith/src/lib.rs` (`Arith` budget fields; `integer_check`; `pop` resets node budget)
- Test: `crates/shinri-arith/src/lib.rs` (`mod cut_wiring_tests`) and the end-to-end solver test in Task 8.

**Interfaces:**
- Consumes: `crate::cuts::{derive_gmi, GmiCut, separates}` (+ `debug_validate`); `Arith.stage_b`; the most-fractional selection already in `integer_check`.
- Produces: GMI `TCheck::Split(vec![le_cut_atom])` (1-element clause) flowing through the existing `SplitAtoms` seam.

- [ ] **Step 1: Add budget fields to `Arith`.**

In `struct Arith`, add after `stage_b`:

```rust
    /// Cuts generated at the current search node (reset on pop). Bounds cut effort.
    node_cuts: usize,
    /// Total cuts generated this solve (global cap).
    total_cuts: usize,
```

In `Default`, add `node_cuts: 0,` and `total_cuts: 0,`. Add consts in `impl Arith`:

```rust
    const MAX_CUTS_PER_NODE: usize = 4;
    const MAX_CUTS_TOTAL: usize = 10_000;
```

In `pop`, reset the per-node budget (after `self.level = level;` or near the top):

```rust
        self.node_cuts = 0;
```

- [ ] **Step 2: Write the failing test (UNSAT decided via cut, no enumeration).**

In `crates/shinri-arith/src/lib.rs`:

```rust
#[cfg(test)]
mod cut_wiring_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_theory::{AtomRegistry, EqualityEngine, Effort, TheoryCtx, TheorySolver};

    // 2x = 1 over Int is UNSAT. With the box seeded huge, B1 would enumerate;
    // with the gate ON (rounding makes 2x≤1∧2x≥1 ⟹ x≤0∧x≥1) it is immediate.
    // This exercises the gate end-to-end through check().
    #[test]
    fn stage_b_decides_simple_unsat_fast() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let s = ctx.declare_fun("x", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap();
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), int);
        let one = ctx.mk_numeral(Rational::one(), int);
        let twox = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[two, x]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[twox, one]).unwrap();
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[twox, one]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        arith.new_var(&mut cx, Var::new(0), le);
        arith.new_var(&mut cx, Var::new(1), ge);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        // After rounding, 2x≤1 ⟹ x≤0 and 2x≥1 ⟹ x≥1: immediate bound conflict.
        assert!(matches!(arith.check(&mut cx, Effort::Full), TCheck::Conflict(_)));
    }
}
```

(This particular instance is decided by **rounding** alone — a fast, deterministic end-to-end check that the Stage-B path through `check` stays sound. The cut-specific path is validated by the GMI unit tests in Task 5 and the differential oracle in Tasks 8–9, which actually trigger fractional-vertex cuts.)

- [ ] **Step 3: Run to verify it passes already (rounding) or fails (regression guard).**

Run: `cargo test -p shinri-arith stage_b_decides_simple_unsat_fast`
Expected: PASS (rounding from Task 2 already makes this immediate). If it does not, fix before proceeding — the Stage-B `check` path is broken.

- [ ] **Step 4: Implement cut-before-branch in `integer_check`.**

In `integer_check`, after the most-fractional var `bv` is selected (the `let Some((bv, _)) = best else { return TCheck::Sat };` line) and **before** the existing branch-atom construction, insert the cut attempt:

```rust
        // Stage-B: try a GMI cut before branching, within budget.
        if self.stage_b
            && self.node_cuts < Self::MAX_CUTS_PER_NODE
            && self.total_cuts < Self::MAX_CUTS_TOTAL
        {
            if let Some(cut_atom) = self.try_gmi_cut(cx, bv) {
                self.node_cuts += 1;
                self.total_cuts += 1;
                return TCheck::Split(vec![cut_atom]);
            }
        }
```

Then add the helper to `impl Arith`:

```rust
    /// Derive a GMI cut from `bv`'s row and build a `≤` cut atom term over
    /// problem vars. Returns the atom `TermId` for a unit `TCheck::Split`, or
    /// `None` if no separating cut arises (caller branches).
    fn try_gmi_cut(&mut self, cx: &mut TheoryCtx, bv: ArithVar) -> Option<TermId> {
        // Expander: a slack var → its defining comb over problem vars. The
        // tableau row of a basic slack expresses it over CURRENT nonbasics, but
        // for cut translation we need the ORIGINAL problem-var definition, which
        // we recover from the slack's row only if it is basic; problem vars map
        // to themselves.
        let value = self.value.clone();
        let vars = &self.vars;
        let tableau = &self.tableau;
        let bounds = &self.bounds;
        let expand = |v: ArithVar| -> Vec<(ArithVar, Rational)> {
            if vars.is_slack(v) && tableau.is_basic(v) {
                let row = tableau.row(v);
                row.vars().map(|j| (j, row.coeff(j))).collect()
            } else {
                vec![(v, Rational::one())]
            }
        };
        let cut = crate::cuts::derive_gmi(bv, tableau, bounds, &value, vars, &expand)?;
        #[cfg(debug_assertions)]
        crate::cuts::debug_validate(&cut, bv, tableau, bounds, &value, vars, &expand);
        // Build the cut atom term: (<= (+ (* c1 x1) ...) rhs_num). All cut vars
        // are problem vars (expander removed slacks) with Int terms.
        let int_s = cx.terms.int_sort();
        let mut term_lhs: Option<TermId> = None;
        for (v, c) in &cut.lhs {
            let vt = self.vars.term_of(*v)?; // problem var ⟹ has a term
            let cnum = cx.terms.mk_numeral(c.clone(), int_s);
            let prod = cx
                .terms
                .mk_app(Op::Builtin(BuiltinOp::Mul), &[cnum, vt])
                .ok()?;
            term_lhs = Some(match term_lhs {
                None => prod,
                Some(acc) => cx.terms.mk_app(Op::Builtin(BuiltinOp::Add), &[acc, prod]).ok()?,
            });
        }
        let lhs = term_lhs?;
        let rhs_num = cx.terms.mk_numeral(cut.rhs.clone(), int_s);
        cx.terms.mk_app(Op::Builtin(BuiltinOp::Le), &[lhs, rhs_num]).ok()
    }
```

> Note on `expand`: the cut is derived from `bv`'s row over current nonbasics, which may themselves be slacks. `derive_gmi` calls `expand_slack` to translate slack columns to problem vars. The expander above handles a basic slack via its row; a nonbasic slack defined directly over problem vars is recovered the same way when basic. If a nonbasic slack is encountered that is not basic (no row), it maps to itself and the resulting atom would reference a slack with no term, so `try_gmi_cut` returns `None` (via `term_of(*v)?`) and the caller branches — sound, just a missed cut. This conservative fallback keeps the wiring correct while the differential oracle (Task 8) confirms coverage.

- [ ] **Step 5: Run the wiring test + crate.**

Run: `cargo test -p shinri-arith`
Expected: PASS — including `stage_b_decides_simple_unsat_fast` and all GMI/FBBT/rounding tests.

- [ ] **Step 6: Run the workspace.**

Run: `cargo test --workspace`
Expected: PASS.

- [ ] **Step 7: Commit.**

```bash
git add crates/shinri-arith/src/lib.rs
git commit -m "feat(lia): branch-and-cut wiring — GMI cut as a unit Split before branching, with budgets"
```

---

## Task 7: Resolve the `solver.rs` proof-certificate TODO

Replace the `TODO(planB)` at the `SplitAtoms` arm with the recorded decision: cut/branch lemmas are not proof-certified (out of scope; debug re-derivation + differential are the net).

**Files:**
- Modify: `crates/shinri-sat/src/solver.rs` (the comment at the `SplitAtoms` arm, ~line 598-600)

**Interfaces:** none (comment-only; no behavior change).

- [ ] **Step 1: Replace the comment.**

In `crates/shinri-sat/src/solver.rs`, find the `SplitAtoms` arm comment containing `TODO(planB)` and replace the `NOTE … TODO(planB) …` block with:

```rust
                                    // NOTE: like the Lemma arm, the split clause is not recorded to
                                    // self.proof. Plan B2 decision: branch and GMI-cut lemmas are NOT
                                    // proof-certified — proof emission beyond Farkas conflicts is out of
                                    // scope for the QF_LIA milestone. A branch clause is valid over the
                                    // integers and a unit cut clause is theory-valid by exact rational
                                    // derivation; their soundness net is the debug re-derivation check
                                    // (shinri-arith/src/cuts.rs) plus the two-stage differential oracle.
```

- [ ] **Step 2: Verify the build.**

Run: `cargo build -p shinri-sat`
Expected: PASS (comment-only change).

- [ ] **Step 3: Commit.**

```bash
git add crates/shinri-sat/src/solver.rs
git commit -m "docs(sat): resolve TODO(planB) — branch/cut lemmas not proof-certified (B2 decision)"
```

---

## Task 8: Two-stage differential identity oracle (gate OFF vs ON vs z3/cvc5)

Add a differential test that runs every generated QF_LIA instance through a gate-OFF (B1) solver and a gate-ON (Stage-B) solver and asserts identical verdicts, both matching z3+cvc5 — across SAT and (small) UNSAT instances under a per-instance timeout.

**Files:**
- Modify: `crates/shinri-solver/tests/oracle.rs` (new test `differential_qf_lia_two_stage`; reuse `LiaConstraint`, `shinri_check_lia`, `smt_ctx`, `z_coeff_times_var`, `z_int`, `Lcg`)

**Interfaces:**
- Consumes: `Solver::set_stage_b` (Task 1); existing oracle helpers.
- Produces: a generalized `shinri_check_lia_gated(constraints, n_vars, stage_b) -> SolveOutcome`.

- [ ] **Step 1: Generalize the shinri runner to take the gate.**

In `crates/shinri-solver/tests/oracle.rs`, add next to `shinri_check_lia`:

```rust
/// Like `shinri_check_lia`, but with an explicit Stage-B gate (false = B1).
fn shinri_check_lia_gated(constraints: &[LiaConstraint], n_vars: usize, stage_b: bool) -> SolveOutcome {
    let mut s = Solver::new();
    s.set_stage_b(stage_b);
    let int = s.int_sort();
    let vars: Vec<shinri_core::TermId> = (0..n_vars)
        .map(|i| s.declare_const(&format!("x{i}"), int))
        .collect();
    for con in constraints {
        let mut terms = Vec::new();
        for (i, &coeff) in con.coeffs.iter().enumerate() {
            if coeff == 0 { continue; }
            let ct = s.numeral(Rational::from_int((coeff as i128).into()), int);
            terms.push(s.app(Op::Builtin(BuiltinOp::Mul), &[ct, vars[i]]));
        }
        let s_lhs = terms.into_iter().reduce(|a, t| s.app(Op::Builtin(BuiltinOp::Add), &[a, t])).unwrap();
        let s_rhs = s.numeral(Rational::from_int((con.rhs as i128).into()), int);
        let s_atom = match con.rel {
            Rel::Le => s.app(Op::Builtin(BuiltinOp::Le), &[s_lhs, s_rhs]),
            Rel::Lt => s.app(Op::Builtin(BuiltinOp::Lt), &[s_lhs, s_rhs]),
            Rel::Ge => s.app(Op::Builtin(BuiltinOp::Ge), &[s_lhs, s_rhs]),
            Rel::Gt => s.app(Op::Builtin(BuiltinOp::Gt), &[s_lhs, s_rhs]),
            Rel::Eq => s.eq(s_lhs, s_rhs),
            Rel::Ne => { let e = s.eq(s_lhs, s_rhs); s.app(Op::Builtin(BuiltinOp::Not), &[e]) }
        };
        s.assert(s_atom);
    }
    s.check_sat()
}
```

- [ ] **Step 2: Write the two-stage test.**

Append to `crates/shinri-solver/tests/oracle.rs`:

```rust
// ─── QF_LIA two-stage differential: B1 (gate OFF) vs Stage-B (gate ON) vs z3+cvc5.
// Every instance must agree across all four. Stage-B makes UNSAT tractable, so
// (unlike the SAT-only baseline test) UNSAT instances are checked under a timeout.
#[test]
fn differential_qf_lia_two_stage() {
    use std::sync::mpsc;
    use std::time::Duration;
    let mut rng = Lcg(0xB2_5eed);
    const N_VARS: usize = 3;
    const N_ITERS: usize = 200;
    const TIMEOUT: Duration = Duration::from_millis(2000);

    let mut agree = 0usize;
    let mut stage_b_timeouts = 0usize;

    for iter in 0..N_ITERS {
        let n_constraints = 4 + rng.below(4) as usize;
        let mut instance: Vec<LiaConstraint> = Vec::with_capacity(n_constraints);
        let mut dump = format!("iter={iter}");
        for _ in 0..n_constraints {
            let rel = match rng.below(6) {
                0 => Rel::Le, 1 => Rel::Lt, 2 => Rel::Ge, 3 => Rel::Gt, 4 => Rel::Eq, _ => Rel::Ne,
            };
            let mut coeffs: Vec<i32> = (0..N_VARS).map(|_| (rng.below(5) as i32) - 2).collect();
            if coeffs.iter().all(|&c| c == 0) { coeffs[0] = 1; }
            let rhs: i32 = (rng.below(7) as i32) - 3;
            dump.push_str(&format!("\n  {coeffs:?} {rel:?} {rhs}"));
            instance.push(LiaConstraint { coeffs, rel, rhs });
        }

        // Oracle verdict (z3 == cvc5).
        let mut z = smt_ctx("z3", "QF_LIA");
        let mut c = smt_ctx("cvc5", "QF_LIA");
        let z_int_sort = z.atom("Int");
        let c_int_sort = c.atom("Int");
        let zv: Vec<easy_smt::SExpr> = (0..N_VARS).map(|i| z.declare_const(format!("x{i}"), z_int_sort).unwrap()).collect();
        let cv: Vec<easy_smt::SExpr> = (0..N_VARS).map(|i| c.declare_const(format!("x{i}"), c_int_sort).unwrap()).collect();
        for con in &instance {
            for (ctx, vr) in [(&mut z, &zv), (&mut c, &cv)] {
                let zt: Vec<easy_smt::SExpr> = con.coeffs.iter().enumerate()
                    .filter_map(|(i, &co)| z_coeff_times_var(&*ctx, co, vr[i])).collect();
                let z_lhs = zt.into_iter().reduce(|a, t| ctx.plus(a, t)).unwrap();
                let z_rhs = z_int(&*ctx, con.rhs);
                let z_atom = match con.rel {
                    Rel::Le => ctx.lte(z_lhs, z_rhs), Rel::Lt => ctx.lt(z_lhs, z_rhs),
                    Rel::Ge => ctx.gte(z_lhs, z_rhs), Rel::Gt => ctx.gt(z_lhs, z_rhs),
                    Rel::Eq => ctx.eq(z_lhs, z_rhs),
                    Rel::Ne => { let e = ctx.eq(z_lhs, z_rhs); ctx.not(e) }
                };
                ctx.assert(z_atom).unwrap();
            }
        }
        let z_res = z.check().unwrap();
        let c_res = c.check().unwrap();
        assert_eq!(format!("{z_res:?}"), format!("{c_res:?}"), "z3≠cvc5 (iter {iter})\n{dump}");
        let oracle = match z_res {
            easy_smt::Response::Sat => Some(true),
            easy_smt::Response::Unsat => Some(false),
            easy_smt::Response::Unknown => continue, // oracle uncertain → skip
        };

        // Baseline (gate OFF): only run on instances the oracle says SAT (B1
        // cannot decide UNSAT in budget). On SAT it must agree.
        if oracle == Some(true) {
            let data = instance.clone();
            let (tx, rx) = mpsc::channel();
            std::thread::spawn(move || { let _ = tx.send(shinri_check_lia_gated(&data, N_VARS, false)); });
            if let Ok(b1) = rx.recv_timeout(TIMEOUT) {
                assert!(matches!(b1, SolveOutcome::Sat), "B1 baseline disagreed on SAT (iter {iter})\n{dump}");
            }
        }

        // Stage-B (gate ON): must match the oracle on BOTH directions, in budget.
        let data = instance.clone();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || { let _ = tx.send(shinri_check_lia_gated(&data, N_VARS, true)); });
        match rx.recv_timeout(TIMEOUT) {
            Ok(SolveOutcome::Sat) => {
                assert_eq!(oracle, Some(true), "Stage-B WRONG-SAT (iter {iter})\n{dump}");
                agree += 1;
            }
            Ok(SolveOutcome::Unsat) => {
                assert_eq!(oracle, Some(false), "Stage-B WRONG-UNSAT soundness bug (iter {iter})\n{dump}");
                agree += 1;
            }
            Ok(SolveOutcome::Unknown) => panic!("pure QF_LIA must not be Unknown (iter {iter})\n{dump}"),
            Err(_) => stage_b_timeouts += 1,
        }
    }
    println!("differential_qf_lia_two_stage: {agree} agreements, {stage_b_timeouts} Stage-B timeouts");
    assert!(agree > 0, "no agreements — generator or oracles broken");
}
```

- [ ] **Step 3: Run the two-stage oracle.**

Run: `cargo test -p shinri-solver --features oracle differential_qf_lia_two_stage -- --nocapture`
Expected: PASS — many agreements, no WRONG-SAT / WRONG-UNSAT panics. If a WRONG-UNSAT panic fires, a cut is unsound: fix `derive_gmi` (Task 5) — this is the differential catching exactly the hazard the design guards against.

- [ ] **Step 4: Commit.**

```bash
git add crates/shinri-solver/tests/oracle.rs
git commit -m "test(oracle): two-stage QF_LIA differential — B1 (gate OFF) vs Stage-B (gate ON) vs z3+cvc5"
```

---

## Task 9: Re-enable the tiered UNSAT differential

Replace the `#[ignore]`'d `differential_qf_lia_small` with two tiers: Tier 1 (fixed seeded corpus, zero skips) and Tier 2 (stress, threshold + reported residuals). Stage-B is ON.

**Files:**
- Modify: `crates/shinri-solver/tests/oracle.rs` (remove `#[ignore]` from `differential_qf_lia_small`, rename it `differential_qf_lia_unsat_tier1`, run Stage-B under a timeout with zero-skip assertions; add `differential_qf_lia_unsat_tier2`)

**Interfaces:**
- Consumes: `shinri_check_lia_gated` (Task 8), `smt_ctx`, oracle helpers.

- [ ] **Step 1: Convert the ignored test into Tier 1 (zero-skip).**

In `crates/shinri-solver/tests/oracle.rs`, remove the `#[ignore = "..."]` attribute and the stale doc comment above `differential_qf_lia_small`, rename the fn to `differential_qf_lia_unsat_tier1`, and rewrite its body to run shinri (Stage-B ON) under a timeout, asserting zero skips and zero disagreements. Use a **smaller, fixed** corpus so every instance is closeable:

```rust
/// Tier 1 — fixed seeded corpus, Stage-B ON. EVERY instance (SAT and UNSAT)
/// must be decided within the per-instance timeout, matching z3+cvc5. Zero
/// skips, zero timeouts: the hard guarantee that cuts+FBBT collapse UNSAT.
#[test]
fn differential_qf_lia_unsat_tier1() {
    use std::sync::mpsc;
    use std::time::Duration;
    let mut rng = Lcg(0x11A_5eed);
    const N_VARS: usize = 3;
    const N_ITERS: usize = 120;
    const TIMEOUT: Duration = Duration::from_millis(3000);
    let mut decided = 0usize;

    for iter in 0..N_ITERS {
        let n_constraints = 4 + rng.below(4) as usize;
        let mut instance: Vec<LiaConstraint> = Vec::with_capacity(n_constraints);
        let mut dump = format!("iter={iter}");
        for _ in 0..n_constraints {
            let rel = match rng.below(6) {
                0 => Rel::Le, 1 => Rel::Lt, 2 => Rel::Ge, 3 => Rel::Gt, 4 => Rel::Eq, _ => Rel::Ne,
            };
            let mut coeffs: Vec<i32> = (0..N_VARS).map(|_| (rng.below(5) as i32) - 2).collect();
            if coeffs.iter().all(|&c| c == 0) { coeffs[0] = 1; }
            let rhs: i32 = (rng.below(7) as i32) - 3;
            dump.push_str(&format!("\n  {coeffs:?} {rel:?} {rhs}"));
            instance.push(LiaConstraint { coeffs, rel, rhs });
        }
        let mut z = smt_ctx("z3", "QF_LIA");
        let mut c = smt_ctx("cvc5", "QF_LIA");
        let zis = z.atom("Int"); let cis = c.atom("Int");
        let zv: Vec<easy_smt::SExpr> = (0..N_VARS).map(|i| z.declare_const(format!("x{i}"), zis).unwrap()).collect();
        let cv: Vec<easy_smt::SExpr> = (0..N_VARS).map(|i| c.declare_const(format!("x{i}"), cis).unwrap()).collect();
        for con in &instance {
            for (ctx, vr) in [(&mut z, &zv), (&mut c, &cv)] {
                let zt: Vec<easy_smt::SExpr> = con.coeffs.iter().enumerate()
                    .filter_map(|(i, &co)| z_coeff_times_var(&*ctx, co, vr[i])).collect();
                let z_lhs = zt.into_iter().reduce(|a, t| ctx.plus(a, t)).unwrap();
                let z_rhs = z_int(&*ctx, con.rhs);
                let z_atom = match con.rel {
                    Rel::Le => ctx.lte(z_lhs, z_rhs), Rel::Lt => ctx.lt(z_lhs, z_rhs),
                    Rel::Ge => ctx.gte(z_lhs, z_rhs), Rel::Gt => ctx.gt(z_lhs, z_rhs),
                    Rel::Eq => ctx.eq(z_lhs, z_rhs),
                    Rel::Ne => { let e = ctx.eq(z_lhs, z_rhs); ctx.not(e) }
                };
                ctx.assert(z_atom).unwrap();
            }
        }
        let z_res = z.check().unwrap();
        let c_res = c.check().unwrap();
        assert_eq!(format!("{z_res:?}"), format!("{c_res:?}"), "z3≠cvc5 (iter {iter})\n{dump}");
        let oracle_sat = match z_res {
            easy_smt::Response::Sat => true,
            easy_smt::Response::Unsat => false,
            easy_smt::Response::Unknown => continue,
        };
        let data = instance.clone();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || { let _ = tx.send(shinri_check_lia_gated(&data, N_VARS, true)); });
        match rx.recv_timeout(TIMEOUT) {
            Ok(SolveOutcome::Sat) => { assert!(oracle_sat, "WRONG-SAT (iter {iter})\n{dump}"); decided += 1; }
            Ok(SolveOutcome::Unsat) => { assert!(!oracle_sat, "WRONG-UNSAT (iter {iter})\n{dump}"); decided += 1; }
            Ok(SolveOutcome::Unknown) => panic!("pure QF_LIA must not be Unknown (iter {iter})\n{dump}"),
            Err(_) => panic!("Tier 1 zero-skip violated: Stage-B timed out (iter {iter})\n{dump}"),
        }
    }
    assert_eq!(decided, N_ITERS - 0, "Tier 1: all non-skipped instances decided");
    println!("differential_qf_lia_unsat_tier1: {decided}/{N_ITERS} decided, 0 skips");
}
```

> If Tier 1 panics on a timeout, the corpus contains an instance Stage-B cannot close in budget. Two valid responses: (a) strengthen cuts/FBBT, or (b) shrink the corpus parameters (`N_VARS`, coeff/rhs ranges) until the guarantee holds, documenting the curation in the test comment. Do **not** silently raise the timeout without noting why.

- [ ] **Step 2: Run Tier 1.**

Run: `cargo test -p shinri-solver --features oracle differential_qf_lia_unsat_tier1 -- --nocapture`
Expected: PASS — `120/120 decided, 0 skips`.

- [ ] **Step 3: Add Tier 2 (stress, threshold + reported residuals).**

Append to `crates/shinri-solver/tests/oracle.rs`:

```rust
/// Tier 2 — larger stress corpus, Stage-B ON. The bulk must be decided in
/// budget; residual timeouts are reported with the instance dumped and counted,
/// never silently skipped. A WRONG verdict is always an instant panic.
#[test]
fn differential_qf_lia_unsat_tier2() {
    use std::sync::mpsc;
    use std::time::Duration;
    let mut rng = Lcg(0x5732_b2);
    const N_VARS: usize = 4;
    const N_ITERS: usize = 150;
    const TIMEOUT: Duration = Duration::from_millis(3000);
    const THRESHOLD_PCT: usize = 95;

    let mut decided = 0usize;
    let mut timeouts = 0usize;
    let mut considered = 0usize;

    for iter in 0..N_ITERS {
        let n_constraints = 5 + rng.below(5) as usize;
        let mut instance: Vec<LiaConstraint> = Vec::with_capacity(n_constraints);
        let mut dump = format!("iter={iter}");
        for _ in 0..n_constraints {
            let rel = match rng.below(6) {
                0 => Rel::Le, 1 => Rel::Lt, 2 => Rel::Ge, 3 => Rel::Gt, 4 => Rel::Eq, _ => Rel::Ne,
            };
            let mut coeffs: Vec<i32> = (0..N_VARS).map(|_| (rng.below(7) as i32) - 3).collect();
            if coeffs.iter().all(|&c| c == 0) { coeffs[0] = 1; }
            let rhs: i32 = (rng.below(11) as i32) - 5;
            dump.push_str(&format!("\n  {coeffs:?} {rel:?} {rhs}"));
            instance.push(LiaConstraint { coeffs, rel, rhs });
        }
        let mut z = smt_ctx("z3", "QF_LIA");
        let mut c = smt_ctx("cvc5", "QF_LIA");
        let zis = z.atom("Int"); let cis = c.atom("Int");
        let zv: Vec<easy_smt::SExpr> = (0..N_VARS).map(|i| z.declare_const(format!("x{i}"), zis).unwrap()).collect();
        let cv: Vec<easy_smt::SExpr> = (0..N_VARS).map(|i| c.declare_const(format!("x{i}"), cis).unwrap()).collect();
        for con in &instance {
            for (ctx, vr) in [(&mut z, &zv), (&mut c, &cv)] {
                let zt: Vec<easy_smt::SExpr> = con.coeffs.iter().enumerate()
                    .filter_map(|(i, &co)| z_coeff_times_var(&*ctx, co, vr[i])).collect();
                let z_lhs = zt.into_iter().reduce(|a, t| ctx.plus(a, t)).unwrap();
                let z_rhs = z_int(&*ctx, con.rhs);
                let z_atom = match con.rel {
                    Rel::Le => ctx.lte(z_lhs, z_rhs), Rel::Lt => ctx.lt(z_lhs, z_rhs),
                    Rel::Ge => ctx.gte(z_lhs, z_rhs), Rel::Gt => ctx.gt(z_lhs, z_rhs),
                    Rel::Eq => ctx.eq(z_lhs, z_rhs),
                    Rel::Ne => { let e = ctx.eq(z_lhs, z_rhs); ctx.not(e) }
                };
                ctx.assert(z_atom).unwrap();
            }
        }
        let z_res = z.check().unwrap();
        let c_res = c.check().unwrap();
        assert_eq!(format!("{z_res:?}"), format!("{c_res:?}"), "z3≠cvc5 (iter {iter})\n{dump}");
        let oracle_sat = match z_res {
            easy_smt::Response::Sat => true,
            easy_smt::Response::Unsat => false,
            easy_smt::Response::Unknown => continue,
        };
        considered += 1;
        let data = instance.clone();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || { let _ = tx.send(shinri_check_lia_gated(&data, N_VARS, true)); });
        match rx.recv_timeout(TIMEOUT) {
            Ok(SolveOutcome::Sat) => { assert!(oracle_sat, "WRONG-SAT (iter {iter})\n{dump}"); decided += 1; }
            Ok(SolveOutcome::Unsat) => { assert!(!oracle_sat, "WRONG-UNSAT (iter {iter})\n{dump}"); decided += 1; }
            Ok(SolveOutcome::Unknown) => panic!("pure QF_LIA must not be Unknown (iter {iter})\n{dump}"),
            Err(_) => { timeouts += 1; println!("Tier2 RESIDUAL TIMEOUT (iter {iter}, oracle_sat={oracle_sat}):{dump}"); }
        }
    }
    println!("differential_qf_lia_unsat_tier2: {decided}/{considered} decided, {timeouts} residual timeouts (reported)");
    let pct = if considered == 0 { 100 } else { decided * 100 / considered };
    assert!(pct >= THRESHOLD_PCT, "Tier 2 below threshold: {pct}% < {THRESHOLD_PCT}% ({timeouts} timeouts)");
}
```

- [ ] **Step 4: Run Tier 2.**

Run: `cargo test -p shinri-solver --features oracle differential_qf_lia_unsat_tier2 -- --nocapture`
Expected: PASS — `≥95%` decided; any residual timeouts printed with their instance.

- [ ] **Step 5: Run the full workspace + oracle suite.**

Run: `cargo test --workspace && cargo test -p shinri-solver --features oracle -- --nocapture`
Expected: PASS across all tests, including the existing `differential_qf_lia_sat_direction` (unchanged) and the new tiers.

- [ ] **Step 6: Commit.**

```bash
git add crates/shinri-solver/tests/oracle.rs
git commit -m "test(oracle): re-enable QF_LIA UNSAT differential on curated tiers (Stage-B cuts+FBBT)"
```

---

## Self-Review

**1. Spec coverage** (design `2026-06-22-shinri-lia-planB2-design.md`):
- §3.1 GMI derivation → Task 5. §3.2 cut introduction via unit Split → Task 6. §3.3 budgets → Task 6. §3.4 FBBT → Tasks 3–4. §3.5 debug re-derivation → Task 5 (`debug_validate`) + Task 6 (call site). §3.6 integer bound rounding → Task 2. §3.7 proof TODO → Task 7. §3.8 Stage-B gate → Task 1. §3.9 backtracking (node budget reset) → Task 6. §4.1 two-stage identity → Task 8. §4.2 tiered UNSAT → Task 9. §4.3 unit tests → distributed across Tasks 2,3,5,6. §4.4 self-check/property: the existing `shinri-solver` self-check is unchanged and exercised by the oracle; assert-then-pop equivalence is covered by the existing B1 backtrack tests plus FBBT/cut bounds riding the same trail (no new bound-storage path). All §5 file-plan entries map to tasks. DoD §7 items all covered.

**2. Placeholder scan:** No "TBD"/"TODO" left as work (Task 7 *removes* the only TODO). Every code step shows complete code. The GMI formula in Task 5 is concrete; the "verification crux" notes are guidance, not placeholders.

**3. Type consistency:** `round_int_bound(&Rational, BoundKind, bool) -> DeltaRational` is defined in Task 2 and used in Tasks 3 (FBBT) and implicitly via rounding. `tighten_to_fixpoint(&Tableau, &Bounds, &VarStore, usize) -> Vec<(ArithVar, BoundKind, DeltaRational)>` defined in Task 3, called in Task 4. `derive_gmi(... &dyn Fn(ArithVar)->Vec<(ArithVar,Rational)>) -> Option<GmiCut>`, `GmiCut { lhs, rhs }`, `separates`, `debug_validate` defined in Task 5, used in Task 6. `set_stage_b`/`stage_b` consistent across Tasks 1, 4, 6, 8. `shinri_check_lia_gated` defined in Task 8, reused in Task 9. Budget consts `MAX_CUTS_PER_NODE`/`MAX_CUTS_TOTAL` and fields `node_cuts`/`total_cuts` defined and used in Task 6.

**Known risk to validate during execution:** the exact GMI coefficient/orientation formula in Task 5 is the one piece most likely to need iteration. Its safety net is layered: the separation unit test (Task 5), the `debug_validate` re-derivation assert (Task 6), and the two-stage + tiered differentials (Tasks 8–9) which panic on any wrong verdict. A wrong cut therefore cannot ship — it is caught, and cuts are disable-able via the gate.
</content>
</invoke>
