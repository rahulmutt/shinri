# shinri-arith QF_LRA Simplex Theory Solver — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a new `shinri-arith` crate implementing a sound and complete Dutertre–de Moura simplex theory solver for QF_LRA, and plug it into the existing Nelson–Oppen `Combiner` as `Combiner<Euf, Arith>` in `shinri-solver`.

**Architecture:** `shinri-arith` implements `shinri_theory::TheorySolver`. Every atom is reduced to a *bound on a variable* (DdM style): a linear combination becomes a slack variable defined by a tableau row, and the atom becomes a simple bound on that slack. The tableau uses integer rows with a shared per-row denominator (design §7.5); solving runs only at `check(Full)` via pivot-and-update with Bland's rule; infeasible rows yield Farkas conflicts; arithmetic disequalities are repaired lemma-free inside `check`. Two enabling changes land first: a public numeral accessor in `shinri-core`, and an Int-sort fence in `shinri-theory::classify`. A mixed-theory fence in `shinri-solver` keeps QF_UFLRA conservatively `unknown`.

**Tech Stack:** Rust (edition 2021, rust-version 1.96.0), `rustc-hash` (FxHashMap/FxHashSet), `proptest` (dev), `easy-smt` + a `z3`/`cvc5` binary (dev oracle). Pure-Rust shipping build.

**Spec:** `docs/superpowers/specs/2026-06-20-shinri-arith-design.md`.

## Global Constraints

- **Edition:** `2021`; **rust-version floor:** `1.96.0` (set via `.workspace = true`).
- **License field:** new crate `Cargo.toml` sets `license = "MIT OR Apache-2.0"` and `edition`/`rust-version` via `.workspace = true`.
- **Pure-Rust shipping mandate:** no native-link deps in non-dev deps. New runtime deps limited to `shinri-*` path crates and `rustc-hash`. Oracle / `proptest` only as `[dev-dependencies]`. `shinri-arith` depends on `shinri-core` and `shinri-theory` only — **never** `shinri-sat` (except `Effort`, re-exported through `shinri-theory`) or `shinri-euf`.
- **Soundness is existential:** any unsupported construct or internal uncertainty yields `unknown`/refusal, never a guess. `debug_assert!` for hot invariants; never silent wrong answers.
- **Index/arena over smart pointers:** ids are small `Copy` newtypes; backtracking via trail + undo-log, never persistent data structures. The tableau basis persists across backtrack; only bounds, assignment, and disequalities are level-scoped.
- **CI gates (must stay green):** `cargo nextest run`, `cargo deny check`, `cargo clippy --all-targets -- -D warnings`, `cargo fmt --check`.
- **Workspace members live in `crates/`** and are registered in the root `Cargo.toml` `[workspace].members`.
- **Arithmetic backend:** only `shinri-num` (`Integer`, `Rational`, `DeltaRational`). No `num-bigint`/`num-rational` on the shipping path; they exist solely as the dev-only differential oracle.

---

## File Structure

**Modified (existing crates):**
- `crates/shinri-core/src/context.rs` — add `pub fn numeral_value(&self, t: TermId) -> Option<&Rational>`.
- `crates/shinri-theory/src/atom.rs` — fence Int-sorted arithmetic atoms to `Unsupported` in `classify`.
- `crates/shinri-solver/src/lib.rs` — swap `Combiner<Euf, EmptyTheory>` → `Combiner<Euf, Arith>`; add the mixed-theory (UFLRA) `unknown` fence.
- `Cargo.toml` (root) — add `shinri-arith` member.

**Created (new crate `crates/shinri-arith`):**
- `Cargo.toml`, `src/lib.rs` — `pub struct Arith` + module wiring + the `TheorySolver` impl.
- `src/vars.rs` — `ArithVar`, `VarStore` (intern problem vars by `TermId`, slacks by `LinComb`).
- `src/normalize.rs` — `LinComb`, `Rel`, `Normalized`; `TermId` atom → `Normalized`.
- `src/tableau.rs` — `Row` (integer shared-denominator), `Tableau` (basic/nonbasic split, pivot).
- `src/bounds.rs` — `BoundKind`, `Bounds` (lower/upper + trail).
- `src/encode.rs` — `AtomEncoding`; build it in `new_var`; apply it in `assert`.
- `src/simplex.rs` — the `check(Full)` loop, Bland's rule, `update`/`pivot_and_update`.
- `src/farkas.rs` — infeasible-row → `Vec<EqLeaf>`.
- `src/diseq.rs` — disequality store + lemma-free repair.
- `src/model.rs` — δ-elimination → `ModelVal::Num`.
- `tests/qflra_e2e.rs` — end-to-end QF_LRA tests through `shinri-solver`.
- `tests/oracle.rs` — differential `z3`/`cvc5` oracle (feature-gated).

---

## Shared Types (defined in Task 3 / Task 4, referenced throughout)

```rust
// vars.rs
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ArithVar(pub u32);
impl ArithVar { pub fn index(self) -> usize { self.0 as usize } }

// normalize.rs
/// Canonical linear combination: sorted by ArithVar, no zero coeffs, no constant
/// (the constant is moved to `rhs` during normalization).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LinComb(pub Vec<(ArithVar, Rational)>);   // sorted by .0

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rel { Le, Lt, Eq }   // Ge/Gt are normalized to Le/Lt by negating the comb

/// `comb (rel) rhs`. For Eq, `comb = lhs - rhs_term` and `rhs` is the folded constant.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Normalized { pub comb: LinComb, pub rel: Rel, pub rhs: Rational }

// bounds.rs
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BoundKind { Lower, Upper }
```

---

## Phase A — Enabling changes (existing crates)

### Task 1: numeral accessor in `shinri-core`

**Files:**
- Modify: `crates/shinri-core/src/context.rs`

**Interfaces:**
- Produces: `Context::numeral_value(&self, t: TermId) -> Option<&Rational>` — returns the `Rational` for a `Const { val: ConstVal::Num(_) }` term, else `None`.
- Consumes: existing `nums: Vec<Rational>`, `term_node`, `ConstVal::Num(RatId)`, `RatId::index`.

- [ ] **Step 1: Write the failing test.**

In `crates/shinri-core/src/context.rs` test module, add:

```rust
    #[test]
    fn numeral_value_reads_back_the_rational() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let r = shinri_num::Rational::new(3i128.into(), 4i128.into()); // 3/4
        let t = ctx.mk_numeral(r.clone(), real);
        assert_eq!(ctx.numeral_value(t), Some(&r));
        // A non-numeral term returns None.
        let x = ctx.declare_fun("x", &[], real);
        let xt = ctx.mk_app(crate::term::Op::Uninterpreted(x), &[]).unwrap();
        assert_eq!(ctx.numeral_value(xt), None);
    }
```

- [ ] **Step 2: Run it; confirm it fails to compile.**

Run: `cargo test -p shinri-core --lib numeral_value_reads_back -- --nocapture`
Expected: FAIL — `no method named numeral_value`.

- [ ] **Step 3: Implement the accessor.**

In `crates/shinri-core/src/context.rs`, add to `impl Context` (near `term_node`):

```rust
    /// The exact `Rational` of a numeral term, or `None` if `t` is not a numeral.
    pub fn numeral_value(&self, t: TermId) -> Option<&Rational> {
        match self.term_node(t) {
            TermNode::Const { val: ConstVal::Num(id), .. } => Some(&self.nums[id.index()]),
            _ => None,
        }
    }
```

Ensure `ConstVal` is in scope (it is via `use crate::term::{... ConstVal ...}` already present).

- [ ] **Step 4: Run the test; confirm it passes.**

Run: `cargo test -p shinri-core --lib numeral_value_reads_back -- --nocapture`
Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-core/src/context.rs
git commit -m "feat(core): public numeral_value accessor for the arith normalizer"
```

### Task 2: fence Int-sorted arithmetic in `classify`

**Files:**
- Modify: `crates/shinri-theory/src/atom.rs`

**Interfaces:**
- Produces: `classify` returns `Err(Unsupported(atom))` for any arithmetic atom whose arith args are **Int**-sorted (relations `Le/Lt/Ge/Gt` and arith equalities). Real-sorted arithmetic still returns `Ok(Owner::Arith)`. EUF and Shared paths unchanged.
- Consumes: existing `classify`, `int_sort`, `real_sort`, `sort_of`, `Unsupported`.

- [ ] **Step 1: Write the failing test.**

In `crates/shinri-theory/src/atom.rs` test module, add:

```rust
    #[test]
    fn int_sorted_arith_is_fenced_to_unsupported() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let xi = ctx.declare_fun("xi", &[], int);
        let yi = ctx.declare_fun("yi", &[], int);
        let x = ctx.mk_app(Op::Uninterpreted(xi), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yi), &[]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, y]).unwrap();
        assert_eq!(classify(&ctx, le), Err(Unsupported(le)));
        // Real-sorted still arith.
        let real = ctx.real_sort();
        let xr = ctx.declare_fun("xr", &[], real);
        let yr = ctx.declare_fun("yr", &[], real);
        let xrt = ctx.mk_app(Op::Uninterpreted(xr), &[]).unwrap();
        let yrt = ctx.mk_app(Op::Uninterpreted(yr), &[]).unwrap();
        let ler = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xrt, yrt]).unwrap();
        assert_eq!(classify(&ctx, ler), Ok(Owner::Arith));
    }
```

- [ ] **Step 2: Run it; confirm it fails.**

Run: `cargo test -p shinri-theory --lib int_sorted_arith_is_fenced -- --nocapture`
Expected: FAIL — currently returns `Ok(Owner::Arith)` for the Int relation.

- [ ] **Step 3: Add the Int fence.**

In `crates/shinri-theory/src/atom.rs`, add a helper and call it. After the existing `contains_nonlinear_mul` early-return at the top of `classify`, insert:

```rust
    // QF_LIA is out of scope this milestone: an LRA simplex solves only the real
    // relaxation, which is unsound for integers. Fence Int-sorted arithmetic to
    // `unknown` (spec §1.1). Real-sorted arithmetic is unaffected.
    if contains_int_arith(terms, atom) {
        return Err(Unsupported(atom));
    }
```

Then add the helper (module level):

```rust
/// True if `atom` is an arithmetic relation/equality with an Int-sorted operand.
fn contains_int_arith(terms: &Context, atom: TermId) -> bool {
    let int_s = terms.int_sort();
    if let TermNode::App { op, args, .. } = terms.term_node(atom) {
        let children = terms.children(*args);
        let touches_int = children.iter().any(|&c| terms.sort_of(c) == int_s);
        match op {
            Op::Builtin(BuiltinOp::Le | BuiltinOp::Lt | BuiltinOp::Ge | BuiltinOp::Gt) => {
                return touches_int;
            }
            Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct) => {
                return touches_int;
            }
            _ => {}
        }
    }
    false
}
```

- [ ] **Step 4: Run the test + full theory suite; confirm pass + no regressions.**

Run: `cargo test -p shinri-theory`
Expected: PASS (new test green; existing EUF/QF_UF classification tests still green — they use uninterpreted sorts, not Int).

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-theory/src/atom.rs
git commit -m "feat(theory): fence Int-sorted arithmetic to unknown (QF_LIA out of scope)"
```

---

## Phase B — Crate scaffold, variables, normalization

### Task 3: crate scaffold + `ArithVar`/`VarStore`

**Files:**
- Create: `crates/shinri-arith/Cargo.toml`, `crates/shinri-arith/src/lib.rs`, `crates/shinri-arith/src/vars.rs`
- Modify: `Cargo.toml` (root) — add member.

**Interfaces:**
- Produces:
  - `ArithVar(u32)` (`Copy`, `Ord`, `index()`).
  - `VarStore` with `problem_var(&mut self, t: TermId) -> ArithVar` (intern by `TermId`), `slack_var(&mut self, comb: &LinComb) -> ArithVar` (intern by canonical `LinComb`), `len(&self) -> usize`, `is_slack(&self, v: ArithVar) -> bool`, `term_of(&self, v: ArithVar) -> Option<TermId>` (problem vars only).
- Consumes: `shinri_core::TermId`, `normalize::LinComb` (forward-declared; this task can use a placeholder `LinComb` then Task 4 fills it — to avoid churn, do Task 4's `LinComb` definition first if implementing out of order).

- [ ] **Step 1: Create the crate manifest.**

`crates/shinri-arith/Cargo.toml`:

```toml
[package]
name = "shinri-arith"
version = "0.0.1"
edition.workspace = true
rust-version.workspace = true
license.workspace = true

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-theory = { path = "../shinri-theory" }
rustc-hash = "2"

[dev-dependencies]
proptest = "1"
```

Add `"crates/shinri-arith"` to the root `Cargo.toml` `[workspace].members` array.

- [ ] **Step 2: Write the failing test (interning dedup).**

`crates/shinri-arith/src/vars.rs`:

```rust
//! Dense interning of arithmetic variables: problem variables (by TermId) and
//! slack variables (by canonical LinComb). Append-only across a solve.

use crate::normalize::LinComb;
use rustc_hash::FxHashMap;
use shinri_core::TermId;

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ArithVar(pub u32);

impl ArithVar {
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Default)]
pub struct VarStore {
    by_term: FxHashMap<TermId, ArithVar>,
    by_comb: FxHashMap<LinComb, ArithVar>,
    term_of: Vec<Option<TermId>>,
    is_slack: Vec<bool>,
}

impl VarStore {
    fn fresh(&mut self, term: Option<TermId>, slack: bool) -> ArithVar {
        let v = ArithVar(self.term_of.len() as u32);
        self.term_of.push(term);
        self.is_slack.push(slack);
        v
    }

    pub fn problem_var(&mut self, t: TermId) -> ArithVar {
        if let Some(&v) = self.by_term.get(&t) {
            return v;
        }
        let v = self.fresh(Some(t), false);
        self.by_term.insert(t, v);
        v
    }

    pub fn slack_var(&mut self, comb: &LinComb) -> ArithVar {
        if let Some(&v) = self.by_comb.get(comb) {
            return v;
        }
        let v = self.fresh(None, true);
        self.by_comb.insert(comb.clone(), v);
        v
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.term_of.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.term_of.is_empty()
    }

    #[inline]
    pub fn is_slack(&self, v: ArithVar) -> bool {
        self.is_slack[v.index()]
    }

    #[inline]
    pub fn term_of(&self, v: ArithVar) -> Option<TermId> {
        self.term_of[v.index()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::normalize::LinComb;
    use shinri_num::Rational;

    #[test]
    fn problem_and_slack_vars_intern_by_identity() {
        let mut s = VarStore::default();
        let t0 = TermId::new(0).unwrap();
        let t1 = TermId::new(1).unwrap();
        let a = s.problem_var(t0);
        let b = s.problem_var(t0); // same term → same var
        let c = s.problem_var(t1);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert!(!s.is_slack(a));

        let comb = LinComb(vec![(a, Rational::one()), (c, Rational::one())]);
        let s1 = s.slack_var(&comb);
        let s2 = s.slack_var(&comb); // same comb → same slack
        assert_eq!(s1, s2);
        assert!(s.is_slack(s1));
        assert_eq!(s.term_of(s1), None);
    }
}
```

`crates/shinri-arith/src/lib.rs`:

```rust
//! shinri-arith: a Dutertre–de Moura simplex theory solver for QF_LRA.
//! Implements `shinri_theory::TheorySolver`; depends only on core + theory.

pub mod bounds;
pub mod diseq;
pub mod encode;
pub mod farkas;
pub mod model;
pub mod normalize;
pub mod simplex;
pub mod tableau;
pub mod vars;

pub use vars::ArithVar;
```

Create empty stub modules for the others so `lib.rs` compiles (each just a `//! TODO Task N` line plus the items added later). For this task, `normalize.rs` needs at least the `LinComb` type (define the full `normalize.rs` in Task 4; for ordering, you may stub `LinComb` here and let Task 4 extend it — but the simplest path is to implement Task 4's `normalize.rs` skeleton first). Keep `bounds/diseq/encode/farkas/model/simplex/tableau` as empty `//!`-only files for now.

- [ ] **Step 3: Run the test; confirm it fails then passes after the skeleton compiles.**

Run: `cargo test -p shinri-arith --lib vars::tests`
Expected: PASS once `LinComb` exists (from Task 4 skeleton) and modules compile.

- [ ] **Step 4: Verify the workspace builds.**

Run: `cargo build -p shinri-arith`
Expected: success.

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith Cargo.toml
git commit -m "feat(arith): crate scaffold + ArithVar/VarStore interning"
```

### Task 4: normalization — `TermId` atom → `Normalized`

**Files:**
- Create/extend: `crates/shinri-arith/src/normalize.rs`

**Interfaces:**
- Produces:
  - `LinComb(Vec<(ArithVar, Rational)>)` (sorted, no zero coeffs, no constant), `Rel`, `Normalized`.
  - `fn normalize_atom(terms: &Context, vars: &mut VarStore, atom: TermId) -> Normalized` — decodes an arithmetic relation/equality term into `comb (rel) rhs`. `Ge/Gt` are flipped to `Le/Lt` by negating both `comb` and `rhs`. `Eq` keeps `Rel::Eq` with `comb = lhs - rhs_term`.
  - Internal `fn linearize(terms, vars, t) -> (LinComb, Rational)` — a term → (variable part, constant part).
- Consumes: `Context::{term_node, children, numeral_value, sort_of, int_sort, real_sort}`, `BuiltinOp`, `Op`, `Rational`.

> **Note:** `classify` (Task 2) has already rejected nonlinear and Int-sorted atoms before any atom reaches `normalize_atom`, so this code may assume linear, Real-sorted input. It still `debug_assert!`s that assumption.

- [ ] **Step 1: Write failing tests.**

`crates/shinri-arith/src/normalize.rs`:

```rust
//! Decode an arithmetic atom term into a canonical `comb (rel) rhs`.

use crate::vars::{ArithVar, VarStore};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_num::Rational;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LinComb(pub Vec<(ArithVar, Rational)>);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rel {
    Le,
    Lt,
    Eq,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Normalized {
    pub comb: LinComb,
    pub rel: Rel,
    pub rhs: Rational,
}

// Hash impl so LinComb can key VarStore.by_comb (Vec<(ArithVar, Rational)> with
// canonical order makes this well-defined).
impl std::hash::Hash for LinComb {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for (v, c) in &self.0 {
            v.hash(state);
            c.numer().hash(state);
            c.denom().hash(state);
        }
    }
}
```

Add the test module at the bottom:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let sym = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }
    fn num(ctx: &mut Context, n: i128) -> TermId {
        let real = ctx.real_sort();
        ctx.mk_numeral(Rational::from_int(n.into()), real)
    }

    #[test]
    fn le_with_constant_folds_to_rhs() {
        // (<= (+ x 1) 3)  ==>  comb {x:1}, Le, rhs 2
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let one = num(&mut ctx, 1);
        let three = num(&mut ctx, 3);
        let lhs = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, one]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[lhs, three]).unwrap();
        let mut vs = VarStore::default();
        let n = normalize_atom(&ctx, &mut vs, le);
        let xv = vs.problem_var(x);
        assert_eq!(n.rel, Rel::Le);
        assert_eq!(n.comb.0, vec![(xv, Rational::one())]);
        assert_eq!(n.rhs, Rational::from_int(2i128.into()));
    }

    #[test]
    fn ge_is_flipped_to_le() {
        // (>= x 5)  ==>  comb {x:-1}, Le, rhs -5
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let five = num(&mut ctx, 5);
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, five]).unwrap();
        let mut vs = VarStore::default();
        let n = normalize_atom(&ctx, &mut vs, ge);
        let xv = vs.problem_var(x);
        assert_eq!(n.rel, Rel::Le);
        assert_eq!(n.comb.0, vec![(xv, -Rational::one())]);
        assert_eq!(n.rhs, Rational::from_int((-5i128).into()));
    }

    #[test]
    fn eq_subtracts_sides() {
        // (= (* 2 x) y)  ==>  comb {x:2, y:-1}, Eq, rhs 0
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let two = num(&mut ctx, 2);
        let twox = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[two, x]).unwrap();
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[twox, y]).unwrap();
        let mut vs = VarStore::default();
        let n = normalize_atom(&ctx, &mut vs, eq);
        let xv = vs.problem_var(x);
        let yv = vs.problem_var(y);
        assert_eq!(n.rel, Rel::Eq);
        let mut got = n.comb.0.clone();
        got.sort_by_key(|p| p.0);
        assert_eq!(
            got,
            vec![(xv, Rational::from_int(2i128.into())), (yv, -Rational::one())]
        );
        assert_eq!(n.rhs, Rational::zero());
    }
}
```

- [ ] **Step 2: Run; confirm failure.**

Run: `cargo test -p shinri-arith --lib normalize::tests`
Expected: FAIL — `normalize_atom`/`linearize` undefined.

- [ ] **Step 3: Implement `linearize` + `normalize_atom`.**

Append to `normalize.rs`:

```rust
/// Accumulate `t` into (variable part, constant part). Assumes linear, Real input.
fn linearize(terms: &Context, vars: &mut VarStore, t: TermId) -> (Vec<(ArithVar, Rational)>, Rational) {
    if let Some(r) = terms.numeral_value(t) {
        return (Vec::new(), r.clone());
    }
    match terms.term_node(t) {
        TermNode::App { op, args, .. } => {
            let kids: Vec<TermId> = terms.children(*args).to_vec();
            match op {
                Op::Builtin(BuiltinOp::Add) => {
                    let mut acc = (Vec::new(), Rational::zero());
                    for k in kids {
                        let (v, c) = linearize(terms, vars, k);
                        acc.0.extend(v);
                        acc.1 = &acc.1 + &c;
                    }
                    acc
                }
                Op::Builtin(BuiltinOp::Sub) => {
                    // (- a b ...) = a - b - ...   (binary in practice)
                    let mut it = kids.into_iter();
                    let (mut v, mut c) = linearize(terms, vars, it.next().unwrap());
                    for k in it {
                        let (vk, ck) = linearize(terms, vars, k);
                        v.extend(vk.into_iter().map(|(x, q)| (x, -q)));
                        c = &c - &ck;
                    }
                    (v, c)
                }
                Op::Builtin(BuiltinOp::Neg) => {
                    let (v, c) = linearize(terms, vars, kids[0]);
                    (v.into_iter().map(|(x, q)| (x, -q)).collect(), -c)
                }
                Op::Builtin(BuiltinOp::Mul) => {
                    // Linear: exactly one non-constant factor (classify rejected the rest).
                    let mut coeff = Rational::one();
                    let mut nonconst: Option<TermId> = None;
                    for k in &kids {
                        match terms.numeral_value(*k) {
                            Some(r) => coeff = &coeff * r,
                            None => {
                                debug_assert!(nonconst.is_none(), "nonlinear reached normalize");
                                nonconst = Some(*k);
                            }
                        }
                    }
                    match nonconst {
                        None => (Vec::new(), coeff), // all-constant product
                        Some(inner) => {
                            let (v, c) = linearize(terms, vars, inner);
                            (
                                v.into_iter().map(|(x, q)| (x, &q * &coeff)).collect(),
                                &c * &coeff,
                            )
                        }
                    }
                }
                Op::Uninterpreted(_) => {
                    // A leaf arithmetic variable (Real-sorted constant symbol).
                    (vec![(vars.problem_var(t), Rational::one())], Rational::zero())
                }
                _ => {
                    debug_assert!(false, "unexpected op in arith term");
                    (vec![(vars.problem_var(t), Rational::one())], Rational::zero())
                }
            }
        }
        TermNode::Const { .. } => {
            // Bool const cannot appear in an arith term; numerals handled above.
            (Vec::new(), Rational::zero())
        }
    }
}

/// Collapse a raw variable list into a canonical `LinComb` (sum duplicates,
/// drop zero coeffs, sort by var).
fn canonicalize(mut raw: Vec<(ArithVar, Rational)>) -> LinComb {
    raw.sort_by_key(|p| p.0);
    let mut out: Vec<(ArithVar, Rational)> = Vec::with_capacity(raw.len());
    for (v, c) in raw {
        if let Some(last) = out.last_mut() {
            if last.0 == v {
                last.1 = &last.1 + &c;
                continue;
            }
        }
        out.push((v, c));
    }
    out.retain(|(_, c)| !c.is_zero());
    LinComb(out)
}

/// `atom` is `(rel lhs rhs)`. Produce `comb (rel') rhs'` with Ge/Gt flipped to Le/Lt.
pub fn normalize_atom(terms: &Context, vars: &mut VarStore, atom: TermId) -> Normalized {
    let (op, kids) = match terms.term_node(atom) {
        TermNode::App { op, args, .. } => (*op, terms.children(*args).to_vec()),
        _ => unreachable!("non-app arith atom"),
    };
    debug_assert_eq!(kids.len(), 2, "binary arith relation expected");
    // lhs - rhs as (vars, const).
    let (lv, lc) = linearize(terms, vars, kids[0]);
    let (rv, rc) = linearize(terms, vars, kids[1]);
    let mut both = lv;
    both.extend(rv.into_iter().map(|(x, q)| (x, -q)));
    let comb_const = &lc - &rc; // (lhs - rhs) = comb_vars + comb_const
    // comb_vars (rel) -comb_const
    let comb = canonicalize(both);
    let rhs = -comb_const;
    match op {
        Op::Builtin(BuiltinOp::Le) => Normalized { comb, rel: Rel::Le, rhs },
        Op::Builtin(BuiltinOp::Lt) => Normalized { comb, rel: Rel::Lt, rhs },
        Op::Builtin(BuiltinOp::Ge) => Normalized {
            comb: negate(comb),
            rel: Rel::Le,
            rhs: -rhs,
        },
        Op::Builtin(BuiltinOp::Gt) => Normalized {
            comb: negate(comb),
            rel: Rel::Lt,
            rhs: -rhs,
        },
        Op::Builtin(BuiltinOp::Eq) => Normalized { comb, rel: Rel::Eq, rhs },
        _ => unreachable!("normalize_atom on non-relation"),
    }
}

fn negate(c: LinComb) -> LinComb {
    LinComb(c.0.into_iter().map(|(v, q)| (v, -q)).collect())
}
```

- [ ] **Step 4: Run the tests; confirm pass.**

Run: `cargo test -p shinri-arith --lib normalize::tests`
Expected: PASS (all three).

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src/normalize.rs
git commit -m "feat(arith): linear atom normalization (comb rel rhs)"
```

---

## Phase C — Tableau (integer rows, shared denominator)

### Task 5: `Row` — integer numerators + shared denominator

**Files:**
- Create/extend: `crates/shinri-arith/src/tableau.rs`

**Interfaces:**
- Produces:
  - `Row { num: FxHashMap<ArithVar, Integer>, den: Integer }` with invariant `den > 0` and `gcd(all num ∪ {den}) == 1`; semantics: `den · x_basic = Σ num[j] · x_j` over nonbasic `j`.
  - `Row::from_rationals(coeffs: &[(ArithVar, Rational)]) -> Row` — build a reduced row from rational coefficients `a_j` (so `x_basic = Σ a_j x_j`).
  - `Row::coeff(&self, v: ArithVar) -> Rational` — the rational `a_j = num[j]/den` (0 if absent).
  - `Row::reduce(&mut self)` — divide through by the gcd, keep `den > 0`.
  - `Row::vars(&self) -> impl Iterator<Item = ArithVar>`.
- Consumes: `shinri_num::{Integer, Rational}`, `ArithVar`.

- [ ] **Step 1: Write failing tests.**

In `crates/shinri-arith/src/tableau.rs`:

```rust
//! The simplex tableau: integer rows with a shared per-row denominator (spec §7.5).
//! Row i means `den_i · x_basic_i = Σ num_i[j] · x_j` over nonbasic j.

use crate::vars::ArithVar;
use rustc_hash::FxHashMap;
use shinri_num::{Integer, Rational};

#[derive(Clone, Debug, Default)]
pub struct Row {
    pub num: FxHashMap<ArithVar, Integer>,
    pub den: Integer,
}

#[cfg(test)]
mod row_tests {
    use super::*;

    fn av(n: u32) -> ArithVar { ArithVar(n) }

    #[test]
    fn from_rationals_reduces_to_shared_denominator() {
        // x_basic = (1/2) a + (1/3) b  ==>  6 x = 3 a + 2 b
        let r = Row::from_rationals(&[
            (av(1), Rational::new(1i128.into(), 2i128.into())),
            (av(2), Rational::new(1i128.into(), 3i128.into())),
        ]);
        assert_eq!(r.den, Integer::from(6i128));
        assert_eq!(r.num[&av(1)], Integer::from(3i128));
        assert_eq!(r.num[&av(2)], Integer::from(2i128));
        // coeff recovers the rationals.
        assert_eq!(r.coeff(av(1)), Rational::new(1i128.into(), 2i128.into()));
        assert_eq!(r.coeff(av(2)), Rational::new(1i128.into(), 3i128.into()));
        assert_eq!(r.coeff(av(9)), Rational::zero());
    }

    #[test]
    fn reduce_strips_common_factor_and_normalizes_sign() {
        // 4 x = 2 a  (den could come in negative) -> 2 x = 1 a
        let mut r = Row {
            num: [(av(1), Integer::from(-2i128))].into_iter().collect(),
            den: Integer::from(-4i128),
        };
        r.reduce();
        assert_eq!(r.den, Integer::from(2i128));
        assert_eq!(r.num[&av(1)], Integer::from(1i128));
    }
}
```

- [ ] **Step 2: Run; confirm failure.**

Run: `cargo test -p shinri-arith --lib row_tests`
Expected: FAIL — `from_rationals`/`coeff`/`reduce` undefined.

- [ ] **Step 3: Implement `Row`.**

Append to `tableau.rs`:

```rust
impl Row {
    /// Build `x_basic = Σ a_j x_j` as integer numerators over a shared denominator.
    pub fn from_rationals(coeffs: &[(ArithVar, Rational)]) -> Row {
        // Shared denominator = lcm of all a_j denominators.
        let mut den = Integer::one();
        for (_, a) in coeffs {
            den = lcm(&den, &a.denom());
        }
        let mut num = FxHashMap::default();
        for (v, a) in coeffs {
            // a_j = a.numer/a.denom ; numerator over shared den = a.numer * (den/a.denom)
            let scale = exact_div(&den, &a.denom());
            let n = &a.numer() * &scale;
            if !n.is_zero() {
                num.insert(*v, n);
            }
        }
        let mut r = Row { num, den };
        r.reduce();
        r
    }

    #[inline]
    pub fn coeff(&self, v: ArithVar) -> Rational {
        match self.num.get(&v) {
            Some(n) => Rational::new(n.clone(), self.den.clone()),
            None => Rational::zero(),
        }
    }

    pub fn vars(&self) -> impl Iterator<Item = ArithVar> + '_ {
        self.num.keys().copied()
    }

    /// Divide through by gcd(all numerators, den); force den > 0.
    pub fn reduce(&mut self) {
        if self.den.is_zero() {
            self.den = Integer::one();
        }
        let mut g = self.den.abs();
        for n in self.num.values() {
            g = g.gcd(n);
            if g == Integer::one() {
                break;
            }
        }
        if g != Integer::one() {
            self.den = exact_div(&self.den, &g);
            for n in self.num.values_mut() {
                *n = exact_div(n, &g);
            }
        }
        if self.den.is_negative() {
            self.den = -self.den.clone();
            for n in self.num.values_mut() {
                *n = -n.clone();
            }
        }
        self.num.retain(|_, n| !n.is_zero());
    }
}

fn exact_div(a: &Integer, b: &Integer) -> Integer {
    let (q, r) = a.div_rem(b);
    debug_assert!(r.is_zero(), "exact_div with remainder");
    q
}

fn lcm(a: &Integer, b: &Integer) -> Integer {
    if a.is_zero() || b.is_zero() {
        return Integer::zero();
    }
    let g = a.gcd(b);
    let q = exact_div(a, &g);
    (&q * b).abs()
}
```

- [ ] **Step 4: Run; confirm pass.**

Run: `cargo test -p shinri-arith --lib row_tests`
Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src/tableau.rs
git commit -m "feat(arith): integer shared-denominator tableau row"
```

### Task 6: `Tableau` — basic/nonbasic split + pivot

**Files:**
- Extend: `crates/shinri-arith/src/tableau.rs`

**Interfaces:**
- Produces:
  - `Tableau { rows: FxHashMap<ArithVar, Row>, basic: FxHashSet<ArithVar> }` where `rows[b]` is the solved form of basic var `b` over nonbasics.
  - `Tableau::define_slack(&mut self, slack: ArithVar, comb: &LinComb)` — install `slack = Σ c_j x_j` as a basic row (idempotent; no-op if already present).
  - `Tableau::is_basic(&self, v) -> bool`.
  - `Tableau::pivot(&mut self, basic: ArithVar, entering: ArithVar)` — swap `entering` into the basis and `basic` out, rewriting all rows. Precondition: `entering` is nonbasic and `rows[basic].coeff(entering) != 0`.
  - `Tableau::row(&self, basic) -> &Row`.
- Consumes: `Row`, `LinComb`, `Rational`.

- [ ] **Step 1: Write failing tests.**

Add to `tableau.rs`:

```rust
use crate::normalize::LinComb;
use rustc_hash::FxHashSet;

#[derive(Default)]
pub struct Tableau {
    pub rows: FxHashMap<ArithVar, Row>,
    pub basic: FxHashSet<ArithVar>,
}

#[cfg(test)]
mod tableau_tests {
    use super::*;
    fn av(n: u32) -> ArithVar { ArithVar(n) }

    #[test]
    fn define_slack_creates_a_basic_row() {
        // s = 2x + 3y
        let mut t = Tableau::default();
        let comb = LinComb(vec![
            (av(1), Rational::from_int(2i128.into())),
            (av(2), Rational::from_int(3i128.into())),
        ]);
        t.define_slack(av(0), &comb);
        assert!(t.is_basic(av(0)));
        assert_eq!(t.row(av(0)).coeff(av(1)), Rational::from_int(2i128.into()));
        assert_eq!(t.row(av(0)).coeff(av(2)), Rational::from_int(3i128.into()));
    }

    #[test]
    fn pivot_swaps_basis_and_rewrites() {
        // s = 2x + 3y ; pivot x in, s out  =>  x = (1/2) s - (3/2) y
        let mut t = Tableau::default();
        let comb = LinComb(vec![
            (av(1), Rational::from_int(2i128.into())),
            (av(2), Rational::from_int(3i128.into())),
        ]);
        t.define_slack(av(0), &comb);
        t.pivot(av(0), av(1));
        assert!(t.is_basic(av(1)));
        assert!(!t.is_basic(av(0)));
        assert_eq!(t.row(av(1)).coeff(av(0)), Rational::new(1i128.into(), 2i128.into()));
        assert_eq!(t.row(av(1)).coeff(av(2)), Rational::new((-3i128).into(), 2i128.into()));
    }
}
```

- [ ] **Step 2: Run; confirm failure.**

Run: `cargo test -p shinri-arith --lib tableau_tests`
Expected: FAIL — methods undefined.

- [ ] **Step 3: Implement `Tableau`.**

Add to `tableau.rs`:

```rust
impl Tableau {
    #[inline]
    pub fn is_basic(&self, v: ArithVar) -> bool {
        self.basic.contains(&v)
    }

    #[inline]
    pub fn row(&self, basic: ArithVar) -> &Row {
        &self.rows[&basic]
    }

    pub fn define_slack(&mut self, slack: ArithVar, comb: &LinComb) {
        if self.basic.contains(&slack) {
            return;
        }
        let row = Row::from_rationals(&comb.0);
        self.rows.insert(slack, row);
        self.basic.insert(slack);
    }

    /// Swap `entering` (nonbasic) into the basis; `basic` leaves. Gauss-Jordan
    /// over the rational coefficients, each row re-reduced to shared-denominator
    /// integer form afterward (spec §7.5).
    pub fn pivot(&mut self, basic: ArithVar, entering: ArithVar) {
        // Solve rows[basic]:  basic = Σ a_j x_j , with a_e = coeff(entering) ≠ 0.
        // => entering = (1/a_e) basic - Σ_{j≠e} (a_j/a_e) x_j
        let old = self.rows.remove(&basic).expect("pivot on non-basic row");
        let a_e = old.coeff(entering);
        debug_assert!(!a_e.is_zero(), "pivot on zero coefficient");
        let inv = a_e.recip();
        let mut solved: Vec<(ArithVar, Rational)> = Vec::new();
        // basic appears on the entering row with coeff 1/a_e.
        solved.push((basic, inv.clone()));
        for v in old.vars() {
            if v == entering {
                continue;
            }
            let a_j = old.coeff(v);
            solved.push((v, -(&a_j * &inv)));
        }
        let entering_row = Row::from_rationals(&solved);

        // Substitute `entering` out of every other row:
        //   row: b = Σ c_k x_k (+ c_e * entering)
        //   ->  b = Σ c_k x_k + c_e * entering_row
        let basics: Vec<ArithVar> = self.rows.keys().copied().collect();
        for b in basics {
            let c_e = self.rows[&b].coeff(entering);
            if c_e.is_zero() {
                continue;
            }
            let mut merged: FxHashMap<ArithVar, Rational> = FxHashMap::default();
            let r = &self.rows[&b];
            for v in r.vars() {
                if v == entering {
                    continue;
                }
                *merged.entry(v).or_insert_with(Rational::zero) =
                    &merged.get(&v).cloned().unwrap_or_else(Rational::zero) + &r.coeff(v);
            }
            for v in entering_row.vars() {
                let add = &c_e * &entering_row.coeff(v);
                let e = merged.entry(v).or_insert_with(Rational::zero);
                *e = &*e + &add;
            }
            let pairs: Vec<(ArithVar, Rational)> = merged.into_iter().collect();
            self.rows.insert(b, Row::from_rationals(&pairs));
        }

        self.rows.insert(entering, entering_row);
        self.basic.remove(&basic);
        self.basic.insert(entering);
    }
}
```

- [ ] **Step 4: Run; confirm pass.**

Run: `cargo test -p shinri-arith --lib tableau_tests`
Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src/tableau.rs
git commit -m "feat(arith): tableau define_slack + Gauss-Jordan pivot"
```

---

## Phase D — Bounds, assignment, assert, backtracking

### Task 7: `Bounds` store with trail

**Files:**
- Create/extend: `crates/shinri-arith/src/bounds.rs`

**Interfaces:**
- Produces:
  - `Bounds` holding per-`ArithVar` `lower: Option<(DeltaRational, Lit)>` and `upper: Option<(DeltaRational, Lit)>`, plus an undo trail keyed by level.
  - `Bounds::ensure(&mut self, n: usize)` — grow to `n` vars.
  - `Bounds::tighten(&mut self, v, kind, val: DeltaRational, lit) -> TightenResult` — install a tighter bound; returns `Redundant`, `Tightened`, or `Conflict { other: Lit }` if it crosses the opposite bound.
  - `Bounds::lower(&self, v)`, `Bounds::upper(&self, v)` — current `Option<&(DeltaRational, Lit)>`.
  - `Bounds::mark(&mut self)` (push a checkpoint) and `Bounds::undo_to(&mut self, checkpoints: usize)` — restore. (Level management lives in Task 9; here just the trail mechanics.)
- Consumes: `DeltaRational`, `Lit`, `BoundKind`.

- [ ] **Step 1: Write failing tests.**

`crates/shinri-arith/src/bounds.rs`:

```rust
//! Per-variable lower/upper bounds (as DeltaRational) with a trail for backtrack.

use crate::vars::ArithVar;
use shinri_core::Lit;
use shinri_num::{DeltaRational, Rational};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BoundKind {
    Lower,
    Upper,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TightenResult {
    Redundant,
    Tightened,
    Conflict { other: Lit },
}

#[derive(Clone, Default)]
struct VarBounds {
    lower: Option<(DeltaRational, Lit)>,
    upper: Option<(DeltaRational, Lit)>,
}

#[derive(Default)]
pub struct Bounds {
    vars: Vec<VarBounds>,
    // Undo trail: (var, kind, previous value). Checkpoints index into this.
    trail: Vec<(ArithVar, BoundKind, Option<(DeltaRational, Lit)>)>,
    marks: Vec<usize>,
}

#[cfg(test)]
mod tests {
    use super::*;
    fn dr(n: i128) -> DeltaRational { DeltaRational::from_rational(Rational::from_int(n.into())) }
    fn lit(n: u32) -> Lit { Lit::new(shinri_core::Var::new(n), true) }
    fn av(n: u32) -> ArithVar { ArithVar(n) }

    #[test]
    fn tighten_detects_crossing_conflict() {
        let mut b = Bounds::default();
        b.ensure(1);
        assert_eq!(b.tighten(av(0), BoundKind::Lower, dr(5), lit(1)), TightenResult::Tightened);
        // upper 3 < lower 5 -> conflict citing the lower's lit.
        assert_eq!(
            b.tighten(av(0), BoundKind::Upper, dr(3), lit(2)),
            TightenResult::Conflict { other: lit(1) }
        );
    }

    #[test]
    fn redundant_bound_is_ignored() {
        let mut b = Bounds::default();
        b.ensure(1);
        b.tighten(av(0), BoundKind::Upper, dr(10), lit(1));
        assert_eq!(b.tighten(av(0), BoundKind::Upper, dr(20), lit(2)), TightenResult::Redundant);
    }

    #[test]
    fn undo_restores_previous_bounds() {
        let mut b = Bounds::default();
        b.ensure(1);
        b.tighten(av(0), BoundKind::Upper, dr(10), lit(1));
        b.mark();
        b.tighten(av(0), BoundKind::Upper, dr(4), lit(2));
        assert_eq!(b.upper(av(0)).unwrap().0, dr(4));
        b.undo_to(0);
        assert_eq!(b.upper(av(0)).unwrap().0, dr(10));
    }
}
```

- [ ] **Step 2: Run; confirm failure.**

Run: `cargo test -p shinri-arith --lib bounds::tests`
Expected: FAIL — methods undefined.

- [ ] **Step 3: Implement `Bounds`.**

Append to `bounds.rs`:

```rust
impl Bounds {
    pub fn ensure(&mut self, n: usize) {
        if self.vars.len() < n {
            self.vars.resize(n, VarBounds::default());
        }
    }

    pub fn lower(&self, v: ArithVar) -> Option<&(DeltaRational, Lit)> {
        self.vars[v.index()].lower.as_ref()
    }
    pub fn upper(&self, v: ArithVar) -> Option<&(DeltaRational, Lit)> {
        self.vars[v.index()].upper.as_ref()
    }

    pub fn mark(&mut self) {
        self.marks.push(self.trail.len());
    }

    /// Undo down to `checkpoints` remaining marks (absolute count of marks kept).
    pub fn undo_to(&mut self, checkpoints: usize) {
        while self.marks.len() > checkpoints {
            let target = self.marks.pop().unwrap();
            while self.trail.len() > target {
                let (v, kind, prev) = self.trail.pop().unwrap();
                match kind {
                    BoundKind::Lower => self.vars[v.index()].lower = prev,
                    BoundKind::Upper => self.vars[v.index()].upper = prev,
                }
            }
        }
    }

    pub fn tighten(
        &mut self,
        v: ArithVar,
        kind: BoundKind,
        val: DeltaRational,
        lit: Lit,
    ) -> TightenResult {
        self.ensure(v.index() + 1);
        let vb = &self.vars[v.index()];
        match kind {
            BoundKind::Lower => {
                if let Some((cur, _)) = &vb.lower {
                    if &val <= cur {
                        return TightenResult::Redundant;
                    }
                }
                if let Some((ub, ulit)) = &vb.upper {
                    if &val > ub {
                        return TightenResult::Conflict { other: *ulit };
                    }
                }
                let prev = self.vars[v.index()].lower.take();
                self.trail.push((v, BoundKind::Lower, prev));
                self.vars[v.index()].lower = Some((val, lit));
                TightenResult::Tightened
            }
            BoundKind::Upper => {
                if let Some((cur, _)) = &vb.upper {
                    if &val >= cur {
                        return TightenResult::Redundant;
                    }
                }
                if let Some((lb, llit)) = &vb.lower {
                    if &val < lb {
                        return TightenResult::Conflict { other: *llit };
                    }
                }
                let prev = self.vars[v.index()].upper.take();
                self.trail.push((v, BoundKind::Upper, prev));
                self.vars[v.index()].upper = Some((val, lit));
                TightenResult::Tightened
            }
        }
    }
}
```

- [ ] **Step 4: Run; confirm pass.**

Run: `cargo test -p shinri-arith --lib bounds::tests`
Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src/bounds.rs
git commit -m "feat(arith): bounds store with crossing-conflict detection + trail"
```

### Task 8: atom encoding + `assert` + assignment

**Files:**
- Create: `crates/shinri-arith/src/encode.rs`
- Extend: `crates/shinri-arith/src/lib.rs` (the `Arith` struct + `new_var`/`assert`)

**Interfaces:**
- Produces:
  - `AtomEncoding` (per SAT `Var`): how asserting that var true/false maps to bound(s) or a disequality.
  - `Arith` struct fields: `vars: VarStore`, `tableau: Tableau`, `bounds: Bounds`, `value: Vec<DeltaRational>` (assignment per `ArithVar`), `enc: Vec<Option<AtomEncoding>>` (by SAT var index), `diseqs` (Task 12), `level: usize`.
  - `Arith::new_var(cx, v, atom)` — normalize the atom, intern its slack (defining a tableau row if the comb has ≥2 terms), precompute the `AtomEncoding`, and grow `value`/`bounds`.
  - `Arith::assert(cx, lit) -> Option<Vec<EqLeaf>>` — apply the encoding for `lit`'s polarity: `tighten` the bound (and if nonbasic var now violates the bound, `update` it). On a crossing conflict, return `Some(vec![EqLeaf::Asserted(lit), EqLeaf::Asserted(other)])`.
- Consumes: `normalize_atom`, `VarStore`, `Tableau`, `Bounds`, `DeltaRational`, `Lit`, `EqLeaf`.

> **Bound-value rules** (single source of truth; `comb (rel) rhs`, then for a single-variable comb the bound is placed directly on the variable, dividing by its coefficient and flipping on negative sign; for ≥2-term combs the bound is on the slack):
> - `Le` rhs, positive: `Upper (rhs, 0)`; negative ¬: `Lower (rhs, +1)`.
> - `Lt` rhs, positive: `Upper (rhs, −1)`; negative ¬: `Lower (rhs, 0)`.
> - `Eq` positive: `Lower (rhs,0)` **and** `Upper (rhs,0)`; negative ¬: disequality `slack ≠ rhs` (Task 12).
> δ encoding: `(c, +1)` = `> c`, `(c, −1)` = `< c`, `(c, 0)` = non-strict.

- [ ] **Step 1: Write failing test (assert produces the trivial conflict).**

In `crates/shinri-arith/src/encode.rs`:

```rust
//! Per-atom encoding: how asserting a SAT var (true/false) becomes a bound or
//! disequality on an ArithVar. Built in `new_var`, applied in `assert`.

use crate::bounds::BoundKind;
use crate::vars::ArithVar;
use shinri_num::DeltaRational;

#[derive(Clone, Debug)]
pub enum AtomEncoding {
    /// Inequality: one bound for the positive polarity, one for the negative.
    Ineq {
        var: ArithVar,
        pos: (BoundKind, DeltaRational),
        neg: (BoundKind, DeltaRational),
    },
    /// Equality `var ⋈ rhs`: positive installs both bounds at `rhs`; negative is
    /// a disequality `var ≠ rhs`.
    Eq { var: ArithVar, rhs: DeltaRational },
    /// A constant relation (empty comb), already decided true/false.
    Const(bool),
}
```

In `crates/shinri-arith/src/lib.rs`, add the test (integration-style, via the public trait); place under a `#[cfg(test)] mod assert_tests` once `Arith` exists:

```rust
#[cfg(test)]
mod assert_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Lit, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::types::EqLeaf;
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn real_var(ctx: &mut Context, name: &str) -> shinri_core::TermId {
        let real = ctx.real_sort();
        let s = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    #[test]
    fn contradictory_bounds_on_one_var_conflict_at_assert() {
        // x <= 1 (var A true) and x >= 2 (i.e. ¬(x <= 1)? no — use two atoms)
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let one = ctx.mk_numeral(Rational::one(), ctx.real_sort());
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), ctx.real_sort());
        let le1 = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, one]).unwrap(); // x <= 1
        let ge2 = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, two]).unwrap(); // x >= 2

        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let va = Var::new(0);
        let vb = Var::new(1);
        {
            let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
            arith.new_var(&mut cx, va, le1);
            arith.new_var(&mut cx, vb, ge2);
            // assert x <= 1
            assert!(arith.assert(&mut cx, Lit::new(va, true)).is_none());
            // assert x >= 2  -> crossing conflict
            let cf = arith.assert(&mut cx, Lit::new(vb, true));
            let leaves = cf.expect("expected conflict");
            assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(vb, true))));
            assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(va, true))));
        }
    }
}
```

- [ ] **Step 2: Run; confirm failure.**

Run: `cargo test -p shinri-arith --lib assert_tests`
Expected: FAIL — `Arith` not defined / methods missing.

- [ ] **Step 3: Implement the `Arith` struct, `new_var`, `assert`, and the assignment `update`.**

In `crates/shinri-arith/src/lib.rs`, add (above the test module):

```rust
use crate::bounds::{BoundKind, Bounds, TightenResult};
use crate::encode::AtomEncoding;
use crate::normalize::{normalize_atom, LinComb, Rel};
use crate::tableau::Tableau;
use crate::vars::{ArithVar, VarStore};
use rustc_hash::FxHashMap;
use shinri_core::{Lit, TermId, TheoryJust, Var};
use shinri_num::{DeltaRational, Rational};
use shinri_sat::Effort;
use shinri_theory::types::EqLeaf;
use shinri_theory::{Explainer, ModelBuilder, TCheck, TheoryCtx, TheorySolver};

#[derive(Default)]
pub struct Arith {
    vars: VarStore,
    tableau: Tableau,
    bounds: Bounds,
    /// Assignment β(v) for every ArithVar (DeltaRational).
    value: Vec<DeltaRational>,
    /// Per SAT-var encoding (indexed by Var::index()).
    enc: Vec<Option<AtomEncoding>>,
    /// Asserted disequalities `(var, rhs, lit)` — repaired in `check` (Task 12).
    diseqs: crate::diseq::DiseqStore,
    level: usize,
}

impl Arith {
    fn grow_value(&mut self) {
        while self.value.len() < self.vars.len() {
            self.value.push(DeltaRational::from_rational(Rational::zero()));
        }
        self.bounds.ensure(self.vars.len());
    }

    /// Reduce a normalized atom to a *bound on one variable*. For a single-term
    /// comb `{x:c}` the bound is on `x` (rhs divided by c, kind flipped if c<0);
    /// for ≥2-term combs a slack var is interned and defined as a tableau row.
    fn atom_var_and_rhs(&mut self, comb: &LinComb, rhs: &Rational) -> (ArithVar, Rational, bool) {
        // returns (var, scaled_rhs, flipped)  where flipped means c < 0.
        if comb.0.len() == 1 {
            let (x, c) = &comb.0[0];
            let scaled = rhs / c;
            (*x, scaled, c.is_negative())
        } else {
            let s = self.vars.slack_var(comb);
            self.tableau.define_slack(s, comb);
            (s, rhs.clone(), false)
        }
    }

    fn build_encoding(&mut self, n: &crate::normalize::Normalized) -> AtomEncoding {
        if n.comb.0.is_empty() {
            // Constant relation: 0 (rel) rhs is decided now.
            let truth = match n.rel {
                Rel::Le => Rational::zero() <= n.rhs,
                Rel::Lt => Rational::zero() < n.rhs,
                Rel::Eq => Rational::zero() == n.rhs,
            };
            return AtomEncoding::Const(truth);
        }
        let (var, rhs, flipped) = self.atom_var_and_rhs(&n.comb, &n.rhs);
        let zero = Rational::zero();
        let one = Rational::one();
        match n.rel {
            Rel::Eq => AtomEncoding::Eq { var, rhs: DeltaRational::new(rhs, zero) },
            Rel::Le | Rel::Lt => {
                // base (un-flipped) positive bound:
                let (pos_kind, pos_k, neg_kind, neg_k) = match n.rel {
                    // x <= rhs : pos Upper (rhs,0); neg Lower (rhs,+1)
                    Rel::Le => (BoundKind::Upper, zero.clone(), BoundKind::Lower, one.clone()),
                    // x < rhs : pos Upper (rhs,-1); neg Lower (rhs,0)
                    Rel::Lt => (BoundKind::Upper, -one.clone(), BoundKind::Lower, zero.clone()),
                    _ => unreachable!(),
                };
                let (mut pk, mut pkk, mut nk, mut nkk) = (pos_kind, pos_k, neg_kind, neg_k);
                if flipped {
                    // dividing by a negative coefficient flips ≤ into ≥: swap
                    // the kinds and negate the infinitesimals accordingly.
                    std::mem::swap(&mut pk, &mut nk);
                    std::mem::swap(&mut pkk, &mut nkk);
                    pkk = -pkk;
                    nkk = -nkk;
                }
                AtomEncoding::Ineq {
                    var,
                    pos: (pk, DeltaRational::new(rhs.clone(), pkk)),
                    neg: (nk, DeltaRational::new(rhs, nkk)),
                }
            }
        }
    }

    /// β-update: set nonbasic `v` to `val`, propagating the delta to all basics.
    fn update(&mut self, v: ArithVar, val: DeltaRational) {
        let delta = val.clone() - self.value[v.index()].clone();
        let affected: Vec<ArithVar> = self
            .tableau
            .basic
            .iter()
            .copied()
            .filter(|b| !self.tableau.row(*b).coeff(v).is_zero())
            .collect();
        for b in affected {
            let a = self.tableau.row(b).coeff(v);
            let cur = self.value[b.index()].clone();
            self.value[b.index()] = cur + delta.scale(&a);
        }
        self.value[v.index()] = val;
    }

    fn apply_bound(&mut self, var: ArithVar, kind: BoundKind, val: DeltaRational, lit: Lit) -> Option<Vec<EqLeaf>> {
        match self.bounds.tighten(var, kind, val.clone(), lit) {
            TightenResult::Redundant => None,
            TightenResult::Conflict { other } => {
                Some(vec![EqLeaf::Asserted(lit), EqLeaf::Asserted(other)])
            }
            TightenResult::Tightened => {
                // Maintain the DdM invariant for nonbasic vars: if the bound is
                // violated by the current value, move the value onto the bound.
                if !self.tableau.is_basic(var) {
                    let v = self.value[var.index()].clone();
                    let violated = match kind {
                        BoundKind::Lower => v < val,
                        BoundKind::Upper => v > val,
                    };
                    if violated {
                        self.update(var, val);
                    }
                }
                None
            }
        }
    }
}
```

Now the `TheorySolver` methods (`new_var`, `assert`); the remaining methods are filled in later tasks but add minimal versions now so the trait is satisfied:

```rust
impl TheorySolver for Arith {
    const THEORY_ID: u16 = 2;

    fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId) {
        let n = normalize_atom(cx.terms, &mut self.vars, atom);
        self.grow_value();
        let enc = self.build_encoding(&n);
        let idx = v.index();
        if idx >= self.enc.len() {
            self.enc.resize_with(idx + 1, || None);
        }
        self.enc[idx] = Some(enc);
        self.grow_value();
    }

    fn assert(&mut self, _cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
        let enc = self.enc[lit.var().index()].clone();
        match enc {
            None => None,
            Some(AtomEncoding::Const(truth)) => {
                // Asserting against a decided constant: conflict iff polarity disagrees.
                if truth == lit.is_positive() {
                    None
                } else {
                    Some(vec![EqLeaf::Asserted(lit)])
                }
            }
            Some(AtomEncoding::Ineq { var, pos, neg }) => {
                let (kind, val) = if lit.is_positive() { pos } else { neg };
                self.apply_bound(var, kind, val, lit)
            }
            Some(AtomEncoding::Eq { var, rhs }) => {
                if lit.is_positive() {
                    if let Some(cf) = self.apply_bound(var, BoundKind::Lower, rhs.clone(), lit) {
                        return Some(cf);
                    }
                    self.apply_bound(var, BoundKind::Upper, rhs, lit)
                } else {
                    self.diseqs.push(var, rhs, lit);
                    None
                }
            }
        }
    }

    fn propagate(&mut self, _cx: &mut TheoryCtx, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<EqLeaf>> {
        None // spec §1 decision 3: check-only; propagate is a no-op.
    }

    fn check(&mut self, _cx: &mut TheoryCtx, effort: Effort) -> TCheck {
        if effort != Effort::Full {
            return TCheck::Sat;
        }
        self.check_full() // Task 10
    }

    fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {
        unreachable!("arith emits conflicts directly as EqLeaf::Asserted; no lazy tags (spec §7)")
    }

    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        self.build_model(cx, m) // Task 13
    }

    fn push(&mut self) {
        self.level += 1;
        self.bounds.mark();
        self.diseqs.mark();
    }

    fn pop(&mut self, level: usize) {
        // absolute target level; restore bounds/diseqs/assignment (Task 9 refines).
        self.bounds.undo_to(level);
        self.diseqs.undo_to(level);
        self.recompute_basic_values();
        self.level = level;
    }
}
```

Add temporary stubs so it compiles before later tasks: `fn check_full(&mut self) -> TCheck { TCheck::Sat }`, `fn build_model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}`, and `fn recompute_basic_values(&mut self) {}` in `impl Arith`. Also create `crates/shinri-arith/src/diseq.rs` with a minimal `DiseqStore` (full version in Task 12):

```rust
//! Asserted arithmetic disequalities; repaired lemma-free in check (Task 12).
use crate::vars::ArithVar;
use shinri_core::Lit;
use shinri_num::DeltaRational;

#[derive(Default)]
pub struct DiseqStore {
    items: Vec<(ArithVar, DeltaRational, Lit)>,
    marks: Vec<usize>,
}
impl DiseqStore {
    pub fn push(&mut self, v: ArithVar, rhs: DeltaRational, lit: Lit) {
        self.items.push((v, rhs, lit));
    }
    pub fn mark(&mut self) { self.marks.push(self.items.len()); }
    pub fn undo_to(&mut self, level: usize) {
        while self.marks.len() > level {
            let t = self.marks.pop().unwrap();
            self.items.truncate(t);
        }
    }
    pub fn iter(&self) -> impl Iterator<Item = &(ArithVar, DeltaRational, Lit)> { self.items.iter() }
}
```

> **Note on `mark`/`undo_to` levels:** `push` pushes one mark per level, so after `push` from level L the mark count equals the new level. `pop(target)` calls `undo_to(target)` which pops marks until `marks.len() == target`. This makes the trail checkpoint count equal the decision level — matching the absolute-level contract. `recompute_basic_values` (Task 9) restores the assignment after bounds are rolled back.

- [ ] **Step 4: Run; confirm pass.**

Run: `cargo test -p shinri-arith --lib assert_tests`
Expected: PASS (the crossing conflict cites both lits).

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src
git commit -m "feat(arith): atom encoding, assert→bound, assignment update"
```

### Task 9: backtracking — restore assignment after `pop`

**Files:**
- Extend: `crates/shinri-arith/src/lib.rs` (`recompute_basic_values`)

**Interfaces:**
- Produces: `Arith::recompute_basic_values(&mut self)` — after bounds roll back, re-establish the DdM invariant: clamp each nonbasic var into its (restored) bounds, then set each basic var's value to `Σ a_ij · value[j]`.
- Consumes: `Tableau`, `Bounds`, `value`.

- [ ] **Step 1: Write failing test (assert+pop == never-asserted).**

In `crates/shinri-arith/src/lib.rs` test area, add:

```rust
#[cfg(test)]
mod backtrack_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let s = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    #[test]
    fn assert_then_pop_is_consistent_again() {
        // x <= 1 ; push ; x >= 2 (conflict at check) ; pop ; check sat
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let one = ctx.mk_numeral(Rational::one(), ctx.real_sort());
        let two = ctx.mk_numeral(Rational::from_int(2i128.into()), ctx.real_sort());
        let le1 = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, one]).unwrap();
        let ge2 = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, two]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
        arith.new_var(&mut cx, Var::new(0), le1);
        arith.new_var(&mut cx, Var::new(1), ge2);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.push();
        // the >= 2 conflicts directly at assert here (single var), so just exercise pop:
        let _ = arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.pop(0);
        assert!(matches!(arith.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}
```

- [ ] **Step 2: Run; confirm it fails or the assignment is wrong.**

Run: `cargo test -p shinri-arith --lib backtrack_tests`
Expected: FAIL — `recompute_basic_values` is a no-op stub, so a stale basic value may persist (or the test exposes the missing restore once Task 10 lands `check_full`). If it passes trivially now, keep the test; it guards Task 10.

- [ ] **Step 3: Implement `recompute_basic_values`.**

Replace the stub in `impl Arith`:

```rust
    fn recompute_basic_values(&mut self) {
        // 1. Clamp nonbasic vars into their bounds (prefer lower if present, else
        //    upper, else keep current — DdM keeps nonbasics at a bound).
        let n = self.vars.len();
        for i in 0..n {
            let v = ArithVar(i as u32);
            if self.tableau.is_basic(v) {
                continue;
            }
            if let Some((lo, _)) = self.bounds.lower(v).cloned() {
                if self.value[i] < lo {
                    self.value[i] = lo;
                    continue;
                }
            }
            if let Some((hi, _)) = self.bounds.upper(v).cloned() {
                if self.value[i] > hi {
                    self.value[i] = hi;
                }
            }
        }
        // 2. Recompute every basic var from its row.
        let basics: Vec<ArithVar> = self.tableau.basic.iter().copied().collect();
        for b in basics {
            let mut acc = DeltaRational::from_rational(Rational::zero());
            let row = self.tableau.row(b);
            for j in row.vars() {
                let a = row.coeff(j);
                acc = acc + self.value[j.index()].clone().scale(&a);
            }
            self.value[b.index()] = acc;
        }
    }
```

- [ ] **Step 4: Run; confirm pass.**

Run: `cargo test -p shinri-arith --lib backtrack_tests`
Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src/lib.rs
git commit -m "feat(arith): restore assignment invariant on pop"
```

---

## Phase E — Simplex check + Farkas

### Task 10: `check_full` — the DdM pivot loop with Bland's rule

**Files:**
- Create: `crates/shinri-arith/src/simplex.rs`
- Extend: `crates/shinri-arith/src/lib.rs` (replace the `check_full` stub; call into `simplex`)

**Interfaces:**
- Produces:
  - `Arith::check_full(&mut self) -> TCheck` — run pivot-and-update until either all basic vars are within bounds (→ run disequality repair, Task 12; for now return `TCheck::Sat`) or an infeasible basic var has no entering candidate (→ Farkas conflict, Task 11; for now return a placeholder conflict).
  - Helpers in `simplex.rs`: `first_violated_basic`, `entering_for`, both using Bland's smallest-index rule.
  - `Arith::pivot_and_update(&mut self, basic, entering, target: DeltaRational)` — set basic to `target` by moving entering, then swap the basis.
- Consumes: `Tableau`, `Bounds`, `value`, `DeltaRational`.

- [ ] **Step 1: Write failing tests (feasible + infeasible end-to-end via `check`).**

`crates/shinri-arith/src/simplex.rs`:

```rust
//! The Dutertre–de Moura check loop: find a violated basic, pivot in an entering
//! nonbasic that can repair it (Bland's rule), update, repeat. No candidate ⇒
//! the row is a Farkas witness of infeasibility.
```

In `crates/shinri-arith/src/lib.rs`, add a test exercising a 2-variable system:

```rust
#[cfg(test)]
mod check_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let s = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }
    fn num(ctx: &mut Context, n: i128) -> TermId {
        ctx.mk_numeral(Rational::from_int(n.into()), ctx.real_sort())
    }

    // Build: x + y <= 1 ; x >= 0 ; y >= 0  -> SAT
    //        plus  x + y >= 3              -> UNSAT
    fn setup(unsat: bool) -> bool {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let one = num(&mut ctx, 1);
        let zero = num(&mut ctx, 0);
        let three = num(&mut ctx, 3);
        let a = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, one]).unwrap();   // x+y<=1
        let b = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, zero]).unwrap();   // x>=0
        let c = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[y, zero]).unwrap();   // y>=0
        let d = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[xy, three]).unwrap(); // x+y>=3

        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
        for (i, atom) in [a, b, c, d].iter().enumerate() {
            arith.new_var(&mut cx, Var::new(i as u32), *atom);
        }
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.assert(&mut cx, Lit::new(Var::new(2), true));
        if unsat {
            arith.assert(&mut cx, Lit::new(Var::new(3), true));
        }
        matches!(arith.check(&mut cx, Effort::Full), TCheck::Sat)
    }

    #[test]
    fn feasible_system_is_sat() {
        assert!(setup(false));
    }

    #[test]
    fn infeasible_system_is_unsat() {
        assert!(!setup(true));
    }
}
```

- [ ] **Step 2: Run; confirm failure.**

Run: `cargo test -p shinri-arith --lib check_tests`
Expected: FAIL — `check_full` stub returns `Sat` for both (the unsat case fails).

- [ ] **Step 3: Implement the check loop.**

In `simplex.rs`, add free functions:

```rust
use crate::bounds::Bounds;
use crate::tableau::Tableau;
use crate::vars::ArithVar;
use shinri_num::DeltaRational;

/// The smallest-index basic var whose value is outside its bounds, with the
/// direction it must move. `None` ⇒ all basics feasible.
pub fn first_violated_basic(
    tableau: &Tableau,
    bounds: &Bounds,
    value: &[DeltaRational],
) -> Option<(ArithVar, Below)> {
    let mut best: Option<(ArithVar, Below)> = None;
    for &b in &tableau.basic {
        let v = &value[b.index()];
        if let Some((lo, _)) = bounds.lower(b) {
            if v < lo {
                best = pick(best, b, Below::Lower);
                continue;
            }
        }
        if let Some((hi, _)) = bounds.upper(b) {
            if v > hi {
                best = pick(best, b, Below::Upper);
            }
        }
    }
    best
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Below {
    Lower, // value < lower: must INCREASE basic
    Upper, // value > upper: must DECREASE basic
}

fn pick(cur: Option<(ArithVar, Below)>, b: ArithVar, dir: Below) -> Option<(ArithVar, Below)> {
    match cur {
        Some((c, _)) if c <= b => cur,
        _ => Some((b, dir)),
    }
}

/// A nonbasic var that can move `basic` in the needed direction, by Bland's rule
/// (smallest index). `increase` = basic must increase.
pub fn entering_for(
    tableau: &Tableau,
    bounds: &Bounds,
    value: &[DeltaRational],
    basic: ArithVar,
    increase: bool,
) -> Option<ArithVar> {
    let row = tableau.row(basic);
    let mut vars: Vec<ArithVar> = row.vars().collect();
    vars.sort();
    for j in vars {
        let a = row.coeff(j); // basic = ... + a * j + ...
        if a.is_zero() {
            continue;
        }
        // To increase basic: either a>0 and j can rise, or a<0 and j can fall.
        let a_pos = !a.is_negative();
        let want_rise = increase == a_pos;
        if want_rise && can_rise(bounds, value, j) {
            return Some(j);
        }
        if !want_rise && can_fall(bounds, value, j) {
            return Some(j);
        }
    }
    None
}

fn can_rise(bounds: &Bounds, value: &[DeltaRational], j: ArithVar) -> bool {
    match bounds.upper(j) {
        Some((hi, _)) => &value[j.index()] < hi,
        None => true,
    }
}
fn can_fall(bounds: &Bounds, value: &[DeltaRational], j: ArithVar) -> bool {
    match bounds.lower(j) {
        Some((lo, _)) => &value[j.index()] > lo,
        None => true,
    }
}
```

In `crates/shinri-arith/src/lib.rs`, replace the `check_full` stub and add `pivot_and_update`:

```rust
    fn check_full(&mut self) -> TCheck {
        use crate::simplex::{entering_for, first_violated_basic, Below};
        loop {
            let Some((basic, dir)) =
                first_violated_basic(&self.tableau, &self.bounds, &self.value)
            else {
                // Bounds feasible. Disequality repair (Task 12) runs here.
                return self.repair_diseqs();
            };
            let increase = dir == Below::Lower;
            match entering_for(&self.tableau, &self.bounds, &self.value, basic, increase) {
                Some(entering) => {
                    // Target = the violated bound of `basic`.
                    let target = match dir {
                        Below::Lower => self.bounds.lower(basic).unwrap().0.clone(),
                        Below::Upper => self.bounds.upper(basic).unwrap().0.clone(),
                    };
                    self.pivot_and_update(basic, entering, target);
                }
                None => {
                    // No candidate: Farkas conflict (Task 11).
                    return TCheck::Conflict(self.farkas_conflict(basic, dir));
                }
            }
        }
    }

    /// Move `entering` so that `basic` reaches `target`, then pivot the basis.
    fn pivot_and_update(&mut self, basic: ArithVar, entering: ArithVar, target: DeltaRational) {
        let a = self.tableau.row(basic).coeff(entering); // basic = ... + a*entering
        debug_assert!(!a.is_zero());
        // theta = (target - value[basic]) / a, applied to `entering`.
        let diff = target - self.value[basic.index()].clone();
        let theta = diff.scale(&a.recip());
        let new_entering = self.value[entering.index()].clone() + theta;
        self.update(entering, new_entering);
        self.tableau.pivot(basic, entering);
        debug_assert!(self.tableau_well_formed());
    }
```

Add a temporary `fn repair_diseqs(&mut self) -> TCheck { TCheck::Sat }` and `fn farkas_conflict(&mut self, _b: ArithVar, _d: crate::simplex::Below) -> Vec<EqLeaf> { Vec::new() }` and `fn tableau_well_formed(&self) -> bool { true }` stubs (Tasks 11/12 replace the first two; refine the invariant check as desired).

Add `pub mod simplex;` is already in `lib.rs`. Ensure `Below` is `pub`.

- [ ] **Step 4: Run; confirm pass.**

Run: `cargo test -p shinri-arith --lib check_tests`
Expected: PASS — feasible→Sat, infeasible→Conflict (non-`Sat`). (The conflict leaves are empty until Task 11, but `matches!(.., Sat)` is already false.)

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src
git commit -m "feat(arith): DdM check loop with Bland's rule pivoting"
```

### Task 11: Farkas conflict extraction

**Files:**
- Create: `crates/shinri-arith/src/farkas.rs`
- Extend: `crates/shinri-arith/src/lib.rs` (replace `farkas_conflict` stub)

**Interfaces:**
- Produces: `Arith::farkas_conflict(&mut self, basic: ArithVar, dir: Below) -> Vec<EqLeaf>` — the violated basic's bound literal plus, for each nonbasic in its row, the bound literal pinning it (the bound on the side that blocks repairing `basic`). Returns `EqLeaf::Asserted` leaves.
- Consumes: `Tableau`, `Bounds`, `Below`.

- [ ] **Step 1: Write failing test (conflict cites the right literals).**

Extend `check_tests` in `lib.rs` with a conflict-content assertion:

```rust
    #[test]
    fn unsat_conflict_cites_participating_literals() {
        // Reuse the infeasible setup but capture the conflict leaves.
        use shinri_core::{BuiltinOp, Context, Op, Var};
        use shinri_theory::types::EqLeaf;
        use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let xs = ctx.declare_fun("x", &[], real);
        let ys = ctx.declare_fun("y", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(ys), &[]).unwrap();
        let xy = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let one = ctx.mk_numeral(Rational::one(), real);
        let three = ctx.mk_numeral(Rational::from_int(3i128.into()), real);
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[xy, one]).unwrap();
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[xy, three]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
        arith.new_var(&mut cx, Var::new(0), le);
        arith.new_var(&mut cx, Var::new(1), ge);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        match arith.check(&mut cx, Effort::Full) {
            TCheck::Conflict(leaves) => {
                assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(0), true))));
                assert!(leaves.contains(&EqLeaf::Asserted(Lit::new(Var::new(1), true))));
            }
            TCheck::Sat => panic!("expected conflict"),
        }
    }
```

- [ ] **Step 2: Run; confirm failure.**

Run: `cargo test -p shinri-arith --lib check_tests::unsat_conflict_cites`
Expected: FAIL — `farkas_conflict` returns an empty Vec.

- [ ] **Step 3: Implement Farkas extraction.**

`crates/shinri-arith/src/farkas.rs`:

```rust
//! Build the conflict from an infeasible basic row: the basic's violated bound
//! plus the bound pinning each nonbasic that blocks its repair (spec §7).

use crate::bounds::Bounds;
use crate::simplex::Below;
use crate::tableau::Tableau;
use crate::vars::ArithVar;
use shinri_core::Lit;
use shinri_num::Rational;

/// Collect the literals of the Farkas core for infeasible `basic` (direction `dir`).
pub fn conflict_lits(
    tableau: &Tableau,
    bounds: &Bounds,
    basic: ArithVar,
    dir: Below,
) -> Vec<Lit> {
    let mut out = Vec::new();
    // The basic var's own violated bound.
    let basic_lit = match dir {
        Below::Lower => bounds.lower(basic),
        Below::Upper => bounds.upper(basic),
    };
    if let Some((_, l)) = basic_lit {
        out.push(*l);
    }
    // For each nonbasic in the row, the bound that pins it (blocking repair).
    // increase basic? then a>0 nonbasics are pinned at UPPER, a<0 at LOWER; the
    // opposite when decreasing.
    let increase = dir == Below::Lower;
    let row = tableau.row(basic);
    for j in row.vars() {
        let a = row.coeff(j);
        if a.is_zero() {
            continue;
        }
        let a_pos = !a.is_negative();
        // pinned-at-upper when (want basic to rise) and the nonbasic would have to
        // rise to help (a_pos == increase) but it's already at its upper bound.
        let want_rise = increase == a_pos;
        let pin = if want_rise { bounds.upper(j) } else { bounds.lower(j) };
        if let Some((_, l)) = pin {
            out.push(*l);
        }
        let _ = Rational::zero(); // keep imports tidy
    }
    out.sort_unstable_by_key(|l| l.code());
    out.dedup();
    out
}
```

In `crates/shinri-arith/src/lib.rs`, replace the stub:

```rust
    fn farkas_conflict(&mut self, basic: ArithVar, dir: crate::simplex::Below) -> Vec<EqLeaf> {
        crate::farkas::conflict_lits(&self.tableau, &self.bounds, basic, dir)
            .into_iter()
            .map(EqLeaf::Asserted)
            .collect()
    }
```

Add `pub mod farkas;` (already present). 

- [ ] **Step 4: Run; confirm pass + the broader suite.**

Run: `cargo test -p shinri-arith --lib`
Expected: PASS (check_tests including the conflict-content test).

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src
git commit -m "feat(arith): Farkas conflict extraction from infeasible row"
```

---

## Phase F — Disequality repair

### Task 12: lemma-free disequality repair in `check`

**Files:**
- Extend: `crates/shinri-arith/src/diseq.rs`, `crates/shinri-arith/src/lib.rs` (replace `repair_diseqs` stub)

**Interfaces:**
- Produces: `Arith::repair_diseqs(&mut self) -> TCheck` — called once bounds are feasible. For each asserted `var ≠ rhs` whose current value equals `rhs`, attempt a feasibility shift of `var`; if none exists (bounds entail `var = rhs`), return a conflict citing the disequality literal plus the bound literals fixing `var`. Iterates to a bounded fixpoint; on cap, returns `TCheck::Sat` only if no diseq is violated, else conservatively reports the conflict (never spins).
- Consumes: `DiseqStore`, `Bounds`, `Tableau`, `value`.

> **Shift mechanics:** a `var ≠ rhs` is violated when `value[var] == rhs` (as `DeltaRational`). Try to nudge `var`:
> - If `var` is **nonbasic**: pick a direction with slack (`can_rise`/`can_fall`); any nonzero feasible move separates it. If both directions are pinned to `rhs`, it's fixed.
> - If `var` is **basic**: look for a nonbasic `j` in `var`'s row with a nonzero coefficient that can move (rise or fall) while keeping all bounds satisfied; `pivot_and_update` `var` to a value just off `rhs`. If no such `j`, `var` is fixed at `rhs`.
> When fixed, the conflict is: the disequality lit + the bound lits that pin `var` to `rhs` (its own lower==upper==rhs, or, if basic, the pinning bounds of every nonbasic in its row — reuse `farkas::conflict_lits`-style collection with both bounds since equality pins both sides).

- [ ] **Step 1: Write failing tests (diseq sat + diseq forced-conflict).**

In `lib.rs`:

```rust
#[cfg(test)]
mod diseq_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

    fn rv(ctx: &mut Context, n: &str) -> TermId {
        let real = ctx.real_sort();
        let s = ctx.declare_fun(n, &[], real);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    // x = 0 forced by 0<=x<=0, plus x != 0  -> UNSAT
    #[test]
    fn forced_equality_violating_diseq_is_unsat() {
        let mut ctx = Context::new();
        let x = rv(&mut ctx, "x");
        let z = ctx.mk_numeral(Rational::zero(), ctx.real_sort());
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[x, z]).unwrap(); // x<=0
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, z]).unwrap(); // x>=0
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, z]).unwrap(); // x=0
        let mut arith = Arith::default();
        let mut e = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &ctx, eq: &mut e, atoms: &atoms };
        arith.new_var(&mut cx, Var::new(0), le);
        arith.new_var(&mut cx, Var::new(1), ge);
        arith.new_var(&mut cx, Var::new(2), eq);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), true));
        arith.assert(&mut cx, Lit::new(Var::new(2), false)); // x != 0
        assert!(matches!(arith.check(&mut cx, Effort::Full), TCheck::Conflict(_)));
    }

    // x>=0, x!=0 is SAT (x can be > 0).
    #[test]
    fn separable_diseq_is_sat() {
        let mut ctx = Context::new();
        let x = rv(&mut ctx, "x");
        let z = ctx.mk_numeral(Rational::zero(), ctx.real_sort());
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[x, z]).unwrap();
        let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, z]).unwrap();
        let mut arith = Arith::default();
        let mut e = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &ctx, eq: &mut e, atoms: &atoms };
        arith.new_var(&mut cx, Var::new(0), ge);
        arith.new_var(&mut cx, Var::new(1), eq);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        arith.assert(&mut cx, Lit::new(Var::new(1), false));
        assert!(matches!(arith.check(&mut cx, Effort::Full), TCheck::Sat));
    }
}
```

- [ ] **Step 2: Run; confirm failure.**

Run: `cargo test -p shinri-arith --lib diseq_tests`
Expected: FAIL — `repair_diseqs` stub returns `Sat`, so `forced_equality...` wrongly passes as Sat.

- [ ] **Step 3: Implement repair.**

Add to `crates/shinri-arith/src/lib.rs` (`impl Arith`):

```rust
    fn repair_diseqs(&mut self) -> TCheck {
        const MAX_ROUNDS: usize = 64;
        for _ in 0..MAX_ROUNDS {
            // Find a violated diseq: value[var] == rhs.
            let mut hit: Option<(ArithVar, DeltaRational, Lit)> = None;
            for (v, rhs, lit) in self.diseqs.iter() {
                if &self.value[v.index()] == rhs {
                    hit = Some((*v, rhs.clone(), *lit));
                    break;
                }
            }
            let Some((var, rhs, dlit)) = hit else {
                return TCheck::Sat; // no diseq violated
            };
            if self.try_separate(var, &rhs) {
                continue; // re-scan after the shift
            }
            // var is fixed at rhs -> conflict.
            let mut lits = vec![dlit];
            lits.extend(self.pinning_lits(var));
            lits.sort_unstable_by_key(|l| l.code());
            lits.dedup();
            return TCheck::Conflict(lits.into_iter().map(EqLeaf::Asserted).collect());
        }
        // Hit the round cap: re-scan; if still violated, report conflict for the
        // first one (sound: we never claim Sat with a violated diseq).
        for (v, rhs, dlit) in self.diseqs.iter() {
            if &self.value[v.index()] == rhs {
                let mut lits = vec![*dlit];
                // Conservative: cite the var's own bounds if present.
                if let Some((_, l)) = self.bounds.lower(*v) { lits.push(*l); }
                if let Some((_, l)) = self.bounds.upper(*v) { lits.push(*l); }
                lits.sort_unstable_by_key(|l| l.code());
                lits.dedup();
                return TCheck::Conflict(lits.into_iter().map(EqLeaf::Asserted).collect());
            }
        }
        TCheck::Sat
    }

    /// Try to move `var` off `rhs` while staying feasible. Returns true on success.
    fn try_separate(&mut self, var: ArithVar, rhs: &DeltaRational) -> bool {
        use crate::simplex::{Below};
        if !self.tableau.is_basic(var) {
            // Nudge nonbasic toward whichever bound has slack.
            if self.can_move(var, true) {
                let target = self.slack_target(var, true, rhs);
                self.update(var, target);
                return self.value[var.index()] != *rhs;
            }
            if self.can_move(var, false) {
                let target = self.slack_target(var, false, rhs);
                self.update(var, target);
                return self.value[var.index()] != *rhs;
            }
            return false;
        }
        // Basic: find a movable nonbasic in its row and pivot var off rhs.
        let row_vars: Vec<ArithVar> = {
            let mut vs: Vec<ArithVar> = self.tableau.row(var).vars().collect();
            vs.sort();
            vs
        };
        for j in row_vars {
            let a = self.tableau.row(var).coeff(j);
            if a.is_zero() {
                continue;
            }
            if self.can_move(j, true) || self.can_move(j, false) {
                // Move var to a feasible point strictly off rhs: aim at its own
                // bound if finite-and-different, else a unit step in a free dir.
                let dir = if self.bound_above(var, rhs) { Below::Lower } else { Below::Upper };
                let target = self.separation_target(var, rhs, dir);
                self.pivot_and_update(var, j, target);
                return self.value[var.index()] != *rhs;
            }
        }
        false
    }
```

Add the small helpers used above (all in `impl Arith`):

```rust
    fn can_move(&self, v: ArithVar, rise: bool) -> bool {
        if rise {
            match self.bounds.upper(v) { Some((hi, _)) => &self.value[v.index()] < hi, None => true }
        } else {
            match self.bounds.lower(v) { Some((lo, _)) => &self.value[v.index()] > lo, None => true }
        }
    }

    /// A feasible target for nonbasic `var` strictly away from `rhs`: step halfway
    /// to the bounding side, or a unit step if that side is unbounded.
    fn slack_target(&self, var: ArithVar, rise: bool, _rhs: &DeltaRational) -> DeltaRational {
        let cur = self.value[var.index()].clone();
        let unit = DeltaRational::from_rational(Rational::one());
        if rise {
            match self.bounds.upper(var) {
                Some((hi, _)) => midpoint(&cur, hi),
                None => cur + unit,
            }
        } else {
            match self.bounds.lower(var) {
                Some((lo, _)) => midpoint(&cur, lo),
                None => cur - unit,
            }
        }
    }

    fn bound_above(&self, var: ArithVar, _rhs: &DeltaRational) -> bool {
        // Prefer to push basic var DOWN toward its lower bound if it has one.
        self.bounds.lower(var).is_some()
    }

    fn separation_target(&self, var: ArithVar, rhs: &DeltaRational, dir: crate::simplex::Below) -> DeltaRational {
        let cur = self.value[var.index()].clone();
        let unit = DeltaRational::from_rational(Rational::one());
        match dir {
            crate::simplex::Below::Lower => match self.bounds.lower(var) {
                Some((lo, _)) if lo != rhs => midpoint(lo, &cur),
                _ => cur - unit,
            },
            crate::simplex::Below::Upper => match self.bounds.upper(var) {
                Some((hi, _)) if hi != rhs => midpoint(&cur, hi),
                _ => cur + unit,
            },
        }
    }

    /// The literals pinning `var` to a fixed value: its own coincident bounds, or
    /// if basic, the pinning bounds of every nonbasic in its row (both sides,
    /// since an equality pins both directions).
    fn pinning_lits(&self, var: ArithVar) -> Vec<Lit> {
        let mut out = Vec::new();
        if !self.tableau.is_basic(var) {
            if let Some((_, l)) = self.bounds.lower(var) { out.push(*l); }
            if let Some((_, l)) = self.bounds.upper(var) { out.push(*l); }
            return out;
        }
        for j in self.tableau.row(var).vars() {
            if self.tableau.row(var).coeff(j).is_zero() { continue; }
            if let Some((_, l)) = self.bounds.lower(j) { out.push(*l); }
            if let Some((_, l)) = self.bounds.upper(j) { out.push(*l); }
        }
        out
    }
```

And a module-level helper in `lib.rs`:

```rust
fn midpoint(a: &DeltaRational, b: &DeltaRational) -> DeltaRational {
    let half = Rational::new(1i128.into(), 2i128.into());
    a.clone() + (b.clone() - a.clone()).scale(&half)
}
```

> **Soundness note:** `try_separate` only ever moves variables within their bounds, so feasibility is preserved; it returns `true` only when `value[var] != rhs` afterward. If it cannot separate, `repair_diseqs` emits a conflict — never a lemma, never an unsound `Sat`.

- [ ] **Step 4: Run; confirm pass.**

Run: `cargo test -p shinri-arith --lib diseq_tests`
Expected: PASS (forced→Conflict, separable→Sat).

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src
git commit -m "feat(arith): lemma-free disequality repair in check"
```

---

## Phase G — Model

### Task 13: model construction with δ-elimination

**Files:**
- Extend: `crates/shinri-arith/src/model.rs`, `crates/shinri-arith/src/lib.rs` (replace `build_model` stub)

**Interfaces:**
- Produces: `Arith::build_model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder)` — choose one positive rational `δ*` making every assignment respect all active strict bounds, then emit `m.assign(term_of(var), ModelVal::Num(c + k·δ*))` for each **problem** variable.
- Helper in `model.rs`: `fn choose_delta(values, bounds) -> Rational` — the standard min-gap over active strict bounds (any positive value smaller than every finite gap; default `1` when there are no strict constraints).
- Consumes: `value`, `Bounds`, `VarStore`, `ModelBuilder`, `ModelVal::Num`.

- [ ] **Step 1: Write failing test (model satisfies a strict constraint).**

In `lib.rs`:

```rust
#[cfg(test)]
mod model_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, Var};
    use shinri_num::Rational;
    use shinri_theory::types::ModelVal;
    use shinri_theory::{AtomRegistry, EqualityEngine, ModelBuilder, TheoryCtx, TheorySolver};

    #[test]
    fn model_picks_concrete_value_for_strict_bound() {
        // x > 0  -> model must give x = c + k*delta with a concrete positive rational.
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let xs = ctx.declare_fun("x", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let z = ctx.mk_numeral(Rational::zero(), real);
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[x, z]).unwrap();
        let mut arith = Arith::default();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx { terms: &ctx, eq: &mut eq, atoms: &atoms };
        arith.new_var(&mut cx, Var::new(0), gt);
        arith.assert(&mut cx, Lit::new(Var::new(0), true));
        assert!(matches!(arith.check(&mut cx, Effort::Full), TCheck::Sat));
        let mut mb = ModelBuilder::default();
        arith.model(&mut cx, &mut mb);
        match mb.get(x) {
            Some(ModelVal::Num(r)) => assert!(*r > Rational::zero(), "x must be > 0, got {:?}", r),
            other => panic!("expected Num, got {:?}", other),
        }
    }
}
```

- [ ] **Step 2: Run; confirm failure.**

Run: `cargo test -p shinri-arith --lib model_tests`
Expected: FAIL — `build_model` stub assigns nothing.

- [ ] **Step 3: Implement model construction.**

`crates/shinri-arith/src/model.rs`:

```rust
//! Eliminate the δ-infinitesimal: pick δ* > 0 small enough that every variable's
//! (c, k) value respects all active strict bounds, then emit concrete rationals.

use crate::bounds::Bounds;
use crate::vars::ArithVar;
use shinri_num::{DeltaRational, Rational};

/// A positive δ* no larger than every finite positive gap between an assignment
/// and a strict bound it must respect. Returns 1 when no strict bound binds.
pub fn choose_delta(value: &[DeltaRational], bounds: &Bounds, n: usize) -> Rational {
    let mut delta = Rational::one();
    for i in 0..n {
        let v = ArithVar(i as u32);
        let val = &value[v.index()];
        // For each bound, if it differs only in the δ component, the real gap in
        // c must stay positive: require δ* * |k_gap| < |c_gap| when c_gap != 0.
        for b in [bounds.lower(v), bounds.upper(v)] {
            if let Some((bound, _)) = b {
                let c_gap = val.c().clone() - bound.c().clone();
                let k_gap = val.k().clone() - bound.k().clone();
                if !c_gap.is_zero() && !k_gap.is_zero() {
                    // need delta < |c_gap| / |k_gap|
                    let cand = (c_gap.clone() / k_gap.clone()).abs_value();
                    if cand < delta {
                        delta = cand;
                    }
                }
            }
        }
    }
    // Halve to stay strictly inside every gap.
    delta / Rational::from_int(2i128.into())
}
```

> If `Rational` lacks `abs_value`, compute it inline: `if r.is_negative() { -r } else { r }`. Adjust the call accordingly.

In `crates/shinri-arith/src/lib.rs`, replace the `build_model` stub:

```rust
    fn build_model(&mut self, _cx: &mut TheoryCtx, m: &mut ModelBuilder) {
        use shinri_theory::types::ModelVal;
        let n = self.vars.len();
        let delta = crate::model::choose_delta(&self.value, &self.bounds, n);
        for i in 0..n {
            let v = ArithVar(i as u32);
            if let Some(term) = self.vars.term_of(v) {
                let dv = &self.value[i];
                let concrete = dv.c().clone() + dv.k().clone() * delta.clone();
                m.assign(term, ModelVal::Num(concrete));
            }
        }
    }
```

- [ ] **Step 4: Run; confirm pass.**

Run: `cargo test -p shinri-arith --lib model_tests`
Expected: PASS — `x > 0`.

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/src
git commit -m "feat(arith): model construction with delta elimination"
```

---

## Phase H — Solver integration

### Task 14: swap in `Arith` + mixed-theory (UFLRA) fence + e2e tests

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs`
- Modify: `crates/shinri-solver/Cargo.toml` (add `shinri-arith` dep)
- Create: `crates/shinri-arith/tests/qflra_e2e.rs`

**Interfaces:**
- Produces: `shinri-solver` uses `Combiner<Euf, Arith>`; a registration-time fence returns `unknown` (`SolveOutcome::Unknown`) when both an EUF atom and an Arith atom (or any `Owner::Shared` atom) are present — keeping QF_UFLRA conservatively `unknown` (spec §1 decision 2).
- Consumes: `shinri_arith::Arith`, the existing `register_atom`/`classify` plumbing, `SolveOutcome`.

> **How to detect mixed-ness:** during atom encoding the solver already calls `register_atom(v, t)`; extend it to classify and count owners. `classify` is `pub` in `shinri-theory::atom`. Track `saw_euf`, `saw_arith`, `saw_shared` and, in `check_sat`, if `(saw_euf && saw_arith) || saw_shared`, set the existing `refused` path → `SolveOutcome::Unknown`.

- [ ] **Step 1: Add the dependency + the type swap.**

In `crates/shinri-solver/Cargo.toml` `[dependencies]`, add:

```toml
shinri-arith = { path = "../shinri-arith" }
```

In `crates/shinri-solver/src/lib.rs`, change both `type Sat = ...` aliases (lines ~84 and ~221):

```rust
type Sat = shinri_sat::Solver<Combiner<Euf, shinri_arith::Arith>, NoProof, Vmtf>;
```

Remove the now-unused `EmptyTheory` import in those functions (keep it imported only if still referenced elsewhere).

- [ ] **Step 2: Write the failing e2e tests.**

`crates/shinri-arith/tests/qflra_e2e.rs`:

```rust
//! End-to-end QF_LRA through the public shinri-solver API.
use shinri_core::{BuiltinOp, Op};
use shinri_num::Rational;
use shinri_solver::{SolveOutcome, Solver};

#[test]
fn pure_lra_sat_and_unsat() {
    // (declare-const x Real)(assert (> x 0))(assert (< x 1)) -> SAT
    let mut s = Solver::new();
    let real = s.real_sort();
    let x = s.declare_const("x", real);
    let zero = s.numeral(Rational::zero(), real);
    let one = s.numeral(Rational::one(), real);
    let gt = s.app(Op::Builtin(BuiltinOp::Gt), &[x, zero]);
    let lt = s.app(Op::Builtin(BuiltinOp::Lt), &[x, one]);
    s.assert(gt);
    s.assert(lt);
    assert_eq!(s.check_sat(), SolveOutcome::Sat);

    // add x > 2 -> UNSAT
    let two = s.numeral(Rational::from_int(2i128.into()), real);
    let gt2 = s.app(Op::Builtin(BuiltinOp::Gt), &[x, two]);
    s.assert(gt2);
    assert_eq!(s.check_sat(), SolveOutcome::Unsat);
}

#[test]
fn mixed_uf_and_lra_is_unknown() {
    // An EUF equality plus an arithmetic constraint -> fenced to Unknown.
    let mut s = Solver::new();
    let real = s.real_sort();
    let u = s.declare_sort("U");
    let a = s.declare_const("a", u);
    let b = s.declare_const("b", u);
    let x = s.declare_const("x", real);
    let zero = s.numeral(Rational::zero(), real);
    let eq = s.app(Op::Builtin(BuiltinOp::Eq), &[a, b]);
    let gt = s.app(Op::Builtin(BuiltinOp::Gt), &[x, zero]);
    s.assert(eq);
    s.assert(gt);
    assert_eq!(s.check_sat(), SolveOutcome::Unknown);
}
```

> Adapt the constructor/method names (`Solver::new`, `real_sort`, `declare_const`, `declare_sort`, `numeral`, `app`, `assert`, `check_sat`, `SolveOutcome`) to the actual `shinri-solver` public API — check `crates/shinri-solver/src/lib.rs` and the existing `tests/qfuf_e2e.rs` for the exact spellings, and mirror them.

- [ ] **Step 3: Run; confirm failure.**

Run: `cargo test -p shinri-arith --test qflra_e2e`
Expected: FAIL — mixed case not yet fenced (and/or compile errors until the fence + API names are correct).

- [ ] **Step 4: Implement the mixed-theory fence.**

In `crates/shinri-solver/src/lib.rs`, where atoms are registered (the `register_atom` call site around `tseitin.rs:144` / `lib.rs:132`), classify each registered atom's owner and accumulate flags on the `Solver`. Add fields `saw_euf: bool`, `saw_arith: bool`, `saw_shared: bool` (or compute on the fly during encoding). After encoding all atoms, before solving, add:

```rust
        // QF_UFLRA is out of scope this milestone (spec §1 decision 2): without
        // interface-equality propagation, combining EUF and arithmetic could be
        // unsound, so conservatively return Unknown when both appear.
        if self.saw_shared || (self.saw_euf && self.saw_arith) {
            return SolveOutcome::Unknown;
        }
```

Populate the flags using `shinri_theory::atom::classify(&self.ctx, atom_term)` per registered atom:

```rust
        match shinri_theory::atom::classify(&self.ctx, t) {
            Ok(shinri_theory::types::Owner::Euf) => self.saw_euf = true,
            Ok(shinri_theory::types::Owner::Arith) => self.saw_arith = true,
            Ok(shinri_theory::types::Owner::Shared) => self.saw_shared = true,
            Err(_) => { /* unsupported atom: existing refused path -> Unknown */ }
        }
```

Ensure `classify` and `Owner` are exported from `shinri-theory` (they are: `pub use atom::classify`, `Owner` via `types`). If `Owner` isn't re-exported at the crate root, use the full `shinri_theory::types::Owner` path as above.

- [ ] **Step 5: Run the e2e tests + the full workspace suite.**

Run: `cargo test -p shinri-arith --test qflra_e2e && cargo test --workspace`
Expected: PASS — pure LRA sat/unsat correct; mixed → Unknown; all prior QF_UF tests still green.

- [ ] **Step 6: Commit.**

```bash
git add crates/shinri-solver crates/shinri-arith/tests
git commit -m "feat(solver): wire Combiner<Euf, Arith>; fence QF_UFLRA to unknown"
```

### Task 15: differential oracle for random QF_LRA

**Files:**
- Create: `crates/shinri-arith/tests/oracle.rs`
- Modify: `crates/shinri-arith/Cargo.toml` (oracle deps + feature)

**Interfaces:**
- Produces: a feature-gated (`oracle`) property test that generates random small linear systems over Reals, solves them with `shinri-solver`, and compares `sat`/`unsat` against a `z3` (and, if present, `cvc5`) binary via `easy-smt` — mirroring the existing QF_UF oracle (`crates/shinri-solver/tests/oracle.rs`).
- Consumes: `easy-smt`, `proptest`, the `shinri-solver` API.

- [ ] **Step 1: Add oracle deps + feature.**

In `crates/shinri-arith/Cargo.toml`:

```toml
[features]
oracle = []

[dev-dependencies]
proptest = "1"
easy-smt = "0.2"
```

(Match the exact `easy-smt` version used by `crates/shinri-solver/Cargo.toml` to keep the lockfile clean.)

- [ ] **Step 2: Write the oracle test, modeled on the QF_UF one.**

First read the existing oracle to copy its harness shape:

Run: `sed -n '1,80p' crates/shinri-solver/tests/oracle.rs`

Then create `crates/shinri-arith/tests/oracle.rs`:

```rust
//! Differential QF_LRA oracle: random linear systems vs z3/cvc5.
#![cfg(feature = "oracle")]

use proptest::prelude::*;

// Reuse the same spawn/translate helpers as the QF_UF oracle (copy the small
// `spawn_z3`/`spawn_cvc5` and SMT-LIB emission helpers from
// crates/shinri-solver/tests/oracle.rs, specialized to (declare-const _ Real)
// and linear (<= (+ (* c x) ...) k) assertions).

proptest! {
    #![proptest_config(ProptestConfig { cases: 200, ..ProptestConfig::default() })]

    #[test]
    fn random_qflra_matches_oracle(system in arb_linear_system()) {
        let ours = solve_with_shinri(&system);        // SolveOutcome
        let theirs = solve_with_oracle(&system);      // "sat" | "unsat"
        // Only compare when shinri gives a definite answer (Unknown is always safe).
        match ours {
            shinri_solver::SolveOutcome::Sat => prop_assert_eq!(theirs, "sat"),
            shinri_solver::SolveOutcome::Unsat => prop_assert_eq!(theirs, "unsat"),
            shinri_solver::SolveOutcome::Unknown => {}
        }
    }
}

// arb_linear_system(): up to ~4 Real vars, ~6 constraints, integer coeffs in
// [-5,5], relations among <=,<,>=,>,=, and a few disequalities. Implement as a
// proptest strategy returning a small struct the two solver functions consume.
fn arb_linear_system() -> impl Strategy<Value = LinearSystem> { /* ... */ todo!() }
fn solve_with_shinri(s: &LinearSystem) -> shinri_solver::SolveOutcome { /* ... */ todo!() }
fn solve_with_oracle(s: &LinearSystem) -> String { /* ... */ todo!() }
struct LinearSystem { /* vars, constraints */ }
```

> Replace the three `todo!()`/`/* ... */` bodies with concrete code copied and adapted from `crates/shinri-solver/tests/oracle.rs` (the QF_UF oracle already implements process spawning, SMT-LIB emission, and result parsing). The `arb_linear_system` strategy emits both the `shinri-solver` term graph and the equivalent SMT-LIB; `solve_with_oracle` runs `z3 -in` (and `cvc5` if on PATH) and reads `sat`/`unsat`. Keep the generator small so `unknown` (e.g. from a disequality-repair cap) is rare; when it occurs the test simply skips the comparison.

- [ ] **Step 3: Run the oracle locally (requires `z3` on PATH).**

Run: `cargo test -p shinri-arith --test oracle --features oracle`
Expected: PASS (200 random systems agree with z3). If `z3` is absent the test is feature-gated off in normal CI; document that it runs in the oracle CI lane like the QF_UF oracle.

- [ ] **Step 4: Run the full default suite once more (oracle off).**

Run: `cargo test --workspace && cargo clippy --all-targets -- -D warnings && cargo fmt --check`
Expected: all green.

- [ ] **Step 5: Commit.**

```bash
git add crates/shinri-arith/tests/oracle.rs crates/shinri-arith/Cargo.toml Cargo.lock
git commit -m "test(arith): differential z3/cvc5 oracle for random QF_LRA"
```

---

## Self-Review

**Spec coverage:**
- §1 decision 1 (QF_LRA only) → Tasks 4–13. ✓
- §1 decision 2 (QF_UFLRA → unknown) → Task 14 fence + test. ✓
- §1 decision 3 (check-only; propagate no-op) → Task 8 `propagate` returns `None`. ✓
- §1 decision 4 (integer shared-denominator tableau) → Tasks 5–6. ✓
- §1 decision 5 (lemma-free disequality repair) → Task 12. ✓
- §1.1 (Int-sort fence) → Task 2 + Task 14 e2e. ✓
- §2 (crate layout, deps) → Task 3 manifest. ✓
- §3 (data structures: slack-per-comb, integer rows, trail-stamped bounds, assignment) → Tasks 3,5,6,7,8. ✓
- §4 (normalization) → Task 4. ✓
- §5 (check loop, Bland, assert no-solve) → Tasks 8,10. ✓
- §6 (disequality repair) → Task 12. ✓
- §7 (Farkas conflict; `explain` unreachable) → Tasks 8 (`explain` `unreachable!`), 11. ✓
- §8 (model δ-elimination) → Task 13. ✓
- §9 (backtracking; basis persists) → Tasks 8 (`push`/`pop`), 9 (`recompute_basic_values`). ✓
- §10 (tests: unit/property/differential/self-check/integration) → Tasks throughout + 14 (e2e) + 15 (oracle). ✓
- §11 (risks) → covered by debug_asserts (Task 10 `tableau_well_formed`), δ property tests, oracle. ✓
- §12 (definition of done) → Tasks 14–15 deliver the gate. ✓

**Placeholder scan:** the only deliberately-deferred bodies are the Task 15 oracle generator helpers, which point at the existing QF_UF oracle to copy — concrete source, not invention. All algorithmic tasks carry complete code.

**Type consistency:** `ArithVar`, `LinComb`, `Rel`, `Normalized`, `BoundKind`, `TightenResult`, `AtomEncoding`, `Below`, `Row`, `Tableau`, `Bounds`, `DiseqStore`, and the `Arith` methods (`update`, `apply_bound`, `pivot_and_update`, `check_full`, `farkas_conflict`, `repair_diseqs`, `build_model`, `recompute_basic_values`) are introduced once and referenced with consistent signatures across tasks. `EqLeaf::Asserted`, `TCheck::{Sat,Conflict}`, `TheoryCtx`, `ModelVal::Num` match the `shinri-theory` interfaces read during planning.

**One known adaptation point:** `Rational`/`Integer` operator ergonomics (`&a + &b` vs `a + b`, `recip`, `abs`) and the exact `shinri-solver` public method names (`declare_const`/`numeral`/`app`) must be matched to the real APIs while implementing — each such spot is flagged inline in the relevant task.
