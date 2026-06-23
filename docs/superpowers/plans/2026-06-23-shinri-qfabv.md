# QF_ABV (Bitvector Arrays) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add the SMT-LIB `QF_ABV` logic to shinri — extensional bitvector arrays `(Array (_ BitVec i) (_ BitVec j))` combined with QF_BV — via lemmas-on-demand abstraction–refinement over the existing eager bit-blaster.

**Architecture:** A new `shinri-abv` crate owns the refinement *controller*, the model-based *consistency checker*, the array *abstraction*, and array *model rendering* — all as pure term-DAG logic parameterized over a `SatBridge` trait (so they unit-test against a fake model). `shinri-solver` implements `SatBridge` for real by reusing its `Encoder`, `replay_bv_cnf`, and an extended (incremental) `shinri-bv::Blaster`, and routes QF_ABV queries to the controller. QF_ABV bypasses the lazy `Combiner` entirely.

**Tech Stack:** Rust (edition 2021, workspace `rust-version` 1.96.0), `rustc-hash::FxHashMap`, existing crates `shinri-core` (term DAG/sorts), `shinri-bv` (blaster/rewrite/model), `shinri-sat` (incremental CDCL), `shinri-num::Integer`. Differential oracle uses `easy-smt` + `z3` on PATH.

## Global Constraints

- Edition `2021`; workspace `rust-version = "1.96.0"`; license `MIT OR Apache-2.0` (copy the `[package]` style from `crates/shinri-bv/Cargo.toml`).
- `cargo fmt` clean and `cargo clippy --workspace --all-targets` clean (the repo's standing bar — see commit `b8b7ff3`).
- **Soundness contract:** anything out of scope returns `Unknown`, never a wrong SAT/UNSAT. Out of scope: nested arrays (not in QF_ABV), arrays mixed with EUF/arith/uninterpreted sorts.
- QF_ABV array terms are exactly `(Array (_ BitVec i) (_ BitVec j))`, `i, j > 0`. `SortNode::Array(index, elem)` where both resolve to `SortNode::BitVec(_)`.
- No `Date.now`/wallclock/random in library code; the oracle uses a deterministic `Lcg` (copy from `crates/shinri-solver/tests/qfbv_oracle.rs`).
- Confirmed APIs (do not invent others):
  - `Context`: `array_sort(idx, elem)`, `bv_sort(w)`, `bv_width(s)->Option<u32>`, `sort_node(s)->&SortNode`, `sort_of(t)->SortId`, `declare_fun(name,&[],sort)->SymbolId`, `mk_app(Op, &[TermId])->Result<TermId,SortError>`, `mk_eq(a,b)->Result<TermId,SortError>`, `mk_bv_const(w, Integer)`, `bv_const_value(t)->Option<(u32,&Integer)>`, `term_node(t)->&TermNode`, `children(args)->&[TermId]`.
  - Nullary uninterpreted constant = `let s = ctx.declare_fun(name,&[],sort); ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()`.
  - `Op::Builtin(BuiltinOp::{Select,Store,Eq,Distinct,...})`, `Op::Uninterpreted(SymbolId)`.
  - `TermNode::App { op, args, sort }` / `TermNode::Const { .. }`.
  - `shinri_bv::Blaster`: `new()`, `blast_word(&mut, ctx, t)->Vec<BitLit>`, `blast_atom(&mut, ctx, t)->BitLit`, `exported_var_bits(ctx)->FxHashMap<TermId,Vec<BitLit>>`, `finish(self)->Cnf`; `BitLit{var:u32,pos:bool}`, `Cnf{num_vars:u32, clauses:Vec<Vec<BitLit>>}`.
  - `shinri_sat::Solver`: `new_var()->Var`, `add_clause(&[Lit])->bool`, `solve()->SolveResult`, `value_of(Var)->Option<bool>`; `Lit::new(Var, pos)`.

---

## File Structure

**New crate `crates/shinri-abv/`:**
- `Cargo.toml` — deps: `shinri-core`, `shinri-bv`, `shinri-num`, `rustc-hash`. (No `shinri-sat` dep — the controller is generic over `SatBridge`.)
- `src/lib.rs` — public surface: `AbvOutcome`, `SatBridge`, `solve()`, re-exports.
- `src/collect.rs` — find `select`/`store`/array-equality terms over BV arrays.
- `src/abstraction.rs` — substitute selects→fresh read vars, array-eqs→fresh bool proxies; produce maps.
- `src/check.rs` — model-based consistency checker (functional consistency, ROW, extensionality) → `Vec<Lemma>`.
- `src/driver.rs` — the refinement controller loop over a `SatBridge`.
- `src/model.rs` — array model assembly + SMT-LIB rendering.

**Modified `crates/shinri-bv/`:**
- `src/blast/mod.rs` — add incremental drain (`num_vars`, `take_new_clauses`) so a live `Blaster` feeds new clauses into an existing SAT solver.

**Modified `crates/shinri-solver/`:**
- `src/abv_stage.rs` (new) — detection (`uses_arrays_over_bv`), fence, and the real `SatBridge` impl.
- `src/lib.rs` — route QF_ABV in `check_sat`; render array models.

**Modified workspace:** `Cargo.toml` — add `crates/shinri-abv` to `members`.

**Tests:** unit tests inline per `shinri-abv` module; `crates/shinri-solver/tests/qfabv_oracle.rs` (differential vs z3, `oracle` feature).

---

### Task 1: Scaffold `shinri-abv` + array-term collection

**Files:**
- Create: `crates/shinri-abv/Cargo.toml`
- Create: `crates/shinri-abv/src/lib.rs`
- Create: `crates/shinri-abv/src/collect.rs`
- Modify: `Cargo.toml` (workspace `members`)

**Interfaces:**
- Produces: `pub struct Collected { pub selects: Vec<TermId>, pub stores: Vec<TermId>, pub array_eqs: Vec<TermId> }` and `pub fn collect(ctx: &Context, assertions: &[TermId]) -> Collected`.
- `array_eqs` holds each `(= a b)` / `(distinct a b)` atom whose operand sort is `SortNode::Array(..)`.

- [ ] **Step 1: Create the crate manifest**

`crates/shinri-abv/Cargo.toml`:
```toml
[package]
name = "shinri-abv"
version = "0.1.0"
edition = "2021"
license = "MIT OR Apache-2.0"
rust-version = "1.96.0"

[dependencies]
shinri-core = { path = "../shinri-core" }
shinri-bv = { path = "../shinri-bv" }
shinri-num = { path = "../shinri-num" }
rustc-hash = "2"
```

- [ ] **Step 2: Add the crate to the workspace**

In `Cargo.toml` (workspace root) append `"crates/shinri-abv"` to the `members` array.

- [ ] **Step 3: Create `src/lib.rs` with module wiring**

```rust
//! shinri-abv: QF_ABV (bitvector arrays) via lemmas-on-demand abstraction–refinement.
//! See docs/superpowers/specs/2026-06-23-shinri-qfabv-design.md.
pub mod collect;

pub use collect::{collect, Collected};
```

- [ ] **Step 4: Write the failing test in `src/collect.rs`**

```rust
//! Collect array operations (select/store/array-equality) over BV-sorted arrays.
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};

/// Array operations found in the assertion DAG.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Collected {
    pub selects: Vec<TermId>,
    pub stores: Vec<TermId>,
    /// `(= a b)` or `(distinct a b)` whose operands are array-sorted.
    pub array_eqs: Vec<TermId>,
}

/// True if `t` has an `(Array _ _)` sort.
fn is_array_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::Array(_, _))
}

pub fn collect(ctx: &Context, assertions: &[TermId]) -> Collected {
    let mut out = Collected::default();
    let mut seen = FxHashSet::default();
    let mut sel = FxHashSet::default();
    let mut sto = FxHashSet::default();
    let mut aeq = FxHashSet::default();
    for &a in assertions {
        walk(ctx, a, &mut seen, &mut out, &mut sel, &mut sto, &mut aeq);
    }
    out
}

fn walk(
    ctx: &Context,
    t: TermId,
    seen: &mut FxHashSet<TermId>,
    out: &mut Collected,
    sel: &mut FxHashSet<TermId>,
    sto: &mut FxHashSet<TermId>,
    aeq: &mut FxHashSet<TermId>,
) {
    if !seen.insert(t) {
        return;
    }
    let (op, kids) = match ctx.term_node(t) {
        TermNode::App { op, args, .. } => (*op, ctx.children(*args).to_vec()),
        TermNode::Const { .. } => return,
    };
    match op {
        Op::Builtin(BuiltinOp::Select) => {
            if sel.insert(t) {
                out.selects.push(t);
            }
        }
        Op::Builtin(BuiltinOp::Store) => {
            if sto.insert(t) {
                out.stores.push(t);
            }
        }
        Op::Builtin(BuiltinOp::Eq) | Op::Builtin(BuiltinOp::Distinct) => {
            if !kids.is_empty() && is_array_sorted(ctx, kids[0]) && aeq.insert(t) {
                out.array_eqs.push(t);
            }
        }
        _ => {}
    }
    for k in kids {
        walk(ctx, k, seen, out, sel, sto, aeq);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_num::Integer;

    fn bv_arr(ctx: &mut Context) -> shinri_core::SortId {
        let i = ctx.bv_sort(8);
        let e = ctx.bv_sort(8);
        ctx.array_sort(i, e)
    }
    fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn collects_select_store_and_array_eq() {
        let mut ctx = Context::new();
        let arr = bv_arr(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let st = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[st, i]).unwrap();
        let b = uconst(&mut ctx, "b", arr);
        let aeq = ctx.mk_eq(a, b).unwrap();
        let bv_eq = {
            let c = ctx.mk_bv_const(8, Integer::from(0u64));
            ctx.mk_eq(i, c).unwrap() // NOT an array eq — must be ignored
        };

        let got = collect(&ctx, &[sel, aeq, bv_eq]);
        assert_eq!(got.selects, vec![sel]);
        assert_eq!(got.stores, vec![st]);
        assert_eq!(got.array_eqs, vec![aeq]);
    }
}
```

- [ ] **Step 5: Run the test — verify it passes**

Run: `cargo test -p shinri-abv collect`
Expected: PASS (the test and impl are in the same step; this verifies the crate compiles and collection is correct). If it fails to compile, fix the manifest/module wiring.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-abv Cargo.toml
git commit -m "feat(abv): scaffold shinri-abv crate + array-term collection"
```

---

### Task 2: Incremental drain on `shinri-bv::Blaster`

**Files:**
- Modify: `crates/shinri-bv/src/blast/mod.rs`
- Test: inline `#[cfg(test)]` in the same file.

**Interfaces:**
- Produces on `Blaster`: `pub fn num_vars(&self) -> u32` (current high-water mark, == future `Cnf.num_vars`), and `pub fn take_new_clauses(&mut self) -> Vec<Vec<BitLit>>` (drains clauses accumulated since the last call, leaving the blaster reusable). Consumed by Task 10's bridge to push freshly-blasted clauses into the live SAT solver across refinement rounds.

- [ ] **Step 1: Write the failing test (append to the `mod tests` in `blast/mod.rs`)**

```rust
#[test]
fn incremental_drain_returns_only_new_clauses() {
    let mut b = Blaster::new();
    // new() pins var0=true via one unit clause; drain it as the "initial" batch.
    let initial = b.take_new_clauses();
    assert_eq!(initial.len(), 1, "initial batch is the var0 unit clause");
    let v0 = b.num_vars();

    let x = b.fresh();
    let y = b.fresh();
    let _ = b.and2(x, y); // adds clauses + 1 fresh var
    let batch1 = b.take_new_clauses();
    assert!(!batch1.is_empty(), "and2 must emit clauses");
    assert!(b.num_vars() > v0, "num_vars must grow");

    // A second drain with no new work is empty.
    let batch2 = b.take_new_clauses();
    assert!(batch2.is_empty(), "no new clauses since last drain");
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p shinri-bv incremental_drain`
Expected: FAIL — `no method named num_vars`/`take_new_clauses`.

- [ ] **Step 3: Add a drain cursor and the two methods**

In `blast/mod.rs`, add a `drained: usize` field to `Blaster` (clauses already drained):
```rust
pub struct Blaster {
    next_var: u32,
    clauses: Vec<Vec<BitLit>>,
    drained: usize,
    pub(crate) cache: FxHashMap<TermId, Vec<BitLit>>,
}
```
Initialize `drained: 0` in `new()` (alongside the existing fields). Then add, inside `impl Blaster`:
```rust
/// Current variable high-water mark (equals `finish().num_vars`).
pub fn num_vars(&self) -> u32 {
    self.next_var
}

/// Drain clauses accumulated since the last call. Leaves the blaster
/// reusable so further `blast_word`/`blast_atom` calls can be drained again.
pub fn take_new_clauses(&mut self) -> Vec<Vec<BitLit>> {
    let new = self.clauses[self.drained..].to_vec();
    self.drained = self.clauses.len();
    new
}
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `cargo test -p shinri-bv incremental_drain`
Expected: PASS. Also run `cargo test -p shinri-bv` to confirm existing `lower`/blast tests still pass (the new field is additive).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/mod.rs
git commit -m "feat(bv): incremental clause drain on Blaster for ABV refinement"
```

---

### Task 3: Abstraction transform (selects → read vars, array-eqs → bool proxies)

**Files:**
- Create: `crates/shinri-abv/src/abstraction.rs`
- Modify: `crates/shinri-abv/src/lib.rs` (add `pub mod abstraction;` + re-export)

**Interfaces:**
- Consumes: `collect::Collected`.
- Produces:
```rust
pub struct Abstraction {
    /// Assertions with every select replaced by its read-var term and every
    /// array-eq replaced by its bool-proxy term. Pure QF_BV + Bool atoms.
    pub assertions: Vec<TermId>,
    /// select-term -> fresh BV-sorted read-var term (LSB..MSB blastable).
    pub read_of: rustc_hash::FxHashMap<TermId, TermId>,
    /// array-eq atom -> fresh Bool-sorted proxy term.
    pub eq_proxy: rustc_hash::FxHashMap<TermId, TermId>,
}
pub fn abstract_arrays(ctx: &mut Context, assertions: &[TermId], c: &Collected) -> Abstraction;
```
- `read_of` is also used by Task 5/6/7 to relate a select to its model value, and by Task 7 (ROW-2/extensionality) which mint *new* selects and call `read_of_or_make`.

- [ ] **Step 1: Write the failing test**

```rust
//! Build the pure-BV+Bool over-approximation of a QF_ABV formula.
use crate::collect::Collected;
use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};

pub struct Abstraction {
    pub assertions: Vec<TermId>,
    pub read_of: FxHashMap<TermId, TermId>,
    pub eq_proxy: FxHashMap<TermId, TermId>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collect::collect;

    fn bv_arr(ctx: &mut Context, iw: u32, ew: u32) -> shinri_core::SortId {
        let i = ctx.bv_sort(iw);
        let e = ctx.bv_sort(ew);
        ctx.array_sort(i, e)
    }
    fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn select_becomes_fresh_bv_var_of_element_width() {
        let mut ctx = Context::new();
        let arr = bv_arr(&mut ctx, 8, 8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", { ctx.bv_sort(8) });
        let e = uconst(&mut ctx, "e", { ctx.bv_sort(8) });
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let atom = ctx.mk_eq(sel, e).unwrap();
        let c = collect(&ctx, &[atom]);

        let abs = abstract_arrays(&mut ctx, &[atom], &c);
        // The select got a read var of width 8.
        let r = abs.read_of[&sel];
        assert_eq!(ctx.bv_width(ctx.sort_of(r)), Some(8));
        // The abstracted assertion is (= r e): no Select node remains.
        assert_eq!(abs.assertions.len(), 1);
        assert!(!contains_select(&ctx, abs.assertions[0]));
    }

    fn contains_select(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op: Op::Builtin(BuiltinOp::Select), .. } => true,
            TermNode::App { args, .. } => {
                ctx.children(*args).to_vec().iter().any(|&k| contains_select(ctx, k))
            }
            _ => false,
        }
    }

    #[test]
    fn array_eq_becomes_bool_proxy() {
        let mut ctx = Context::new();
        let arr = bv_arr(&mut ctx, 8, 8);
        let a = uconst(&mut ctx, "a", arr);
        let b = uconst(&mut ctx, "b", arr);
        let atom = ctx.mk_eq(a, b).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);
        let p = abs.eq_proxy[&atom];
        assert!(matches!(ctx.sort_node(ctx.sort_of(p)), SortNode::Bool));
        assert_eq!(abs.assertions, vec![p]);
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-abv abstraction`
Expected: FAIL — `abstract_arrays` not found.

- [ ] **Step 3: Implement `abstract_arrays` + a fresh-var helper**

Append to `abstraction.rs`:
```rust
/// Mint a fresh nullary uninterpreted constant of the given sort.
fn fresh_const(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
    let sym = ctx.declare_fun(name, &[], sort);
    ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
}

pub fn abstract_arrays(ctx: &mut Context, assertions: &[TermId], c: &Collected) -> Abstraction {
    let mut read_of: FxHashMap<TermId, TermId> = FxHashMap::default();
    let mut eq_proxy: FxHashMap<TermId, TermId> = FxHashMap::default();

    // Read var per distinct select, of the element width.
    for (n, &sel) in c.selects.iter().enumerate() {
        let elem_sort = match ctx.sort_node(ctx.sort_of(sel)) {
            // select's own sort IS the element sort.
            _ => ctx.sort_of(sel),
        };
        let r = fresh_const(ctx, &format!("$abv_read_{n}"), elem_sort);
        read_of.insert(sel, r);
    }
    // Bool proxy per distinct array (dis)equality.
    let bool_sort = {
        // Bool sort id: use any Bool-sorted term's sort, or mk a constant.
        // Context has no direct bool_sort() accessor in scope here; mint via a
        // throwaway equality's sort. Instead, use the proxy's natural sort:
        // declare a 0-ary uninterpreted Bool function. We need a Bool SortId.
        crate::abstraction::bool_sort_id(ctx)
    };
    for (n, &atom) in c.array_eqs.iter().enumerate() {
        let p = fresh_const(ctx, &format!("$abv_eq_{n}"), bool_sort);
        eq_proxy.insert(atom, p);
    }

    // Substitute throughout each assertion.
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    let assertions = assertions
        .iter()
        .map(|&a| subst(ctx, a, &read_of, &eq_proxy, &mut memo))
        .collect();

    Abstraction { assertions, read_of, eq_proxy }
}

/// Obtain the Bool SortId from the context (sort of a trivially-built Bool term).
fn bool_sort_id(ctx: &mut Context) -> shinri_core::SortId {
    // `(= x x)` over any term is Bool-sorted; build one from a fresh Bool-free
    // bitvector constant to avoid assuming a bool_sort() accessor.
    let c = ctx.mk_bv_const(1, shinri_num::Integer::from(0u64));
    let e = ctx.mk_eq(c, c).unwrap();
    ctx.sort_of(e)
}

/// Rewrite a term, replacing select subterms by read vars and array-eq atoms by
/// their proxies. Memoized over the shared DAG.
fn subst(
    ctx: &mut Context,
    t: TermId,
    read_of: &FxHashMap<TermId, TermId>,
    eq_proxy: &FxHashMap<TermId, TermId>,
    memo: &mut FxHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&r) = read_of.get(&t) {
        return r;
    }
    if let Some(&p) = eq_proxy.get(&t) {
        return p;
    }
    if let Some(&m) = memo.get(&t) {
        return m;
    }
    let (op, kids) = match ctx.term_node(t) {
        TermNode::App { op, args, .. } => (*op, ctx.children(*args).to_vec()),
        TermNode::Const { .. } => {
            memo.insert(t, t);
            return t;
        }
    };
    let new_kids: Vec<TermId> = kids
        .iter()
        .map(|&k| subst(ctx, k, read_of, eq_proxy, memo))
        .collect();
    let rebuilt = if new_kids == kids {
        t
    } else {
        ctx.mk_app(op, &new_kids).expect("abstraction preserves sorts")
    };
    memo.insert(t, rebuilt);
    rebuilt
}
```
Then add `pub mod abstraction;` and `pub use abstraction::{abstract_arrays, Abstraction};` to `lib.rs`. (Note: the `bool_sort_id`/`bool_sort` indirection avoids assuming a `Context::bool_sort()` accessor; if one exists, replace both with it.)

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-abv abstraction`
Expected: PASS (both tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-abv/src/abstraction.rs crates/shinri-abv/src/lib.rs
git commit -m "feat(abv): array abstraction — selects to read vars, array-eqs to bool proxies"
```

---

### Task 4: `SatBridge` trait + `Lemma`/`Access` types + fake bridge for tests

**Files:**
- Create: `crates/shinri-abv/src/driver.rs` (trait + types only this task)
- Modify: `crates/shinri-abv/src/lib.rs`

**Interfaces:**
- Produces:
```rust
/// A BV (dis)equality literal in a lemma: (atom term, polarity).
/// `atom` is a Bool-sorted BV equality `(= u v)` over read vars / indices /
/// elements, or an array-eq proxy. `pos=false` means the negation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LemmaLit { pub atom: TermId, pub pos: bool }

/// A learned clause: the disjunction of its lits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lemma(pub Vec<LemmaLit>);

/// What the controller needs from the SAT/blast layer. Implemented for real by
/// shinri-solver (Task 10) and by a fake in tests.
pub trait SatBridge {
    /// Solve the current clause set. Returns true on SAT.
    fn solve(&mut self) -> bool;
    /// Concrete value of a BV-sorted term in the latest SAT model.
    fn value_bv(&self, ctx: &Context, t: TermId) -> Option<(u32, shinri_num::Integer)>;
    /// Truth of an array-eq proxy term in the latest SAT model.
    fn value_bool(&self, t: TermId) -> Option<bool>;
    /// Ensure `atom` (a Bool-sorted BV (dis)equality) is blasted into the live
    /// solver, returning nothing; idempotent. Mints clauses for any new reads.
    fn ensure_atom(&mut self, ctx: &mut Context, atom: TermId);
    /// Add one lemma clause over already-ensured atoms.
    fn add_lemma(&mut self, ctx: &mut Context, lemma: &Lemma);
}
```
- Consumed by Tasks 5–8 (checker builds `Lemma`s) and Task 8/9 (controller calls bridge).

- [ ] **Step 1: Write the trait, types, and a fake bridge under `#[cfg(test)]`**

```rust
//! Refinement controller + the SatBridge seam.
use rustc_hash::FxHashMap;
use shinri_core::TermId;
use shinri_core::Context;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LemmaLit { pub atom: TermId, pub pos: bool }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lemma(pub Vec<LemmaLit>);

pub trait SatBridge {
    fn solve(&mut self) -> bool;
    fn value_bv(&self, ctx: &Context, t: TermId) -> Option<(u32, shinri_num::Integer)>;
    fn value_bool(&self, t: TermId) -> Option<bool>;
    fn ensure_atom(&mut self, ctx: &mut Context, atom: TermId);
    fn add_lemma(&mut self, ctx: &mut Context, lemma: &Lemma);
}

#[cfg(test)]
pub(crate) mod fake {
    use super::*;
    use shinri_num::Integer;

    /// A scripted bridge: returns a fixed model, records lemmas, and (optionally)
    /// flips to a different model / UNSAT after N lemmas are added (to simulate
    /// refinement convergence).
    pub struct FakeBridge {
        pub bv: FxHashMap<TermId, (u32, Integer)>,
        pub boolv: FxHashMap<TermId, bool>,
        pub added: Vec<Lemma>,
        pub ensured: Vec<TermId>,
        /// Become UNSAT once `added.len()` reaches this (None = always SAT).
        pub unsat_after: Option<usize>,
    }
    impl Default for FakeBridge {
        fn default() -> Self {
            FakeBridge { bv: FxHashMap::default(), boolv: FxHashMap::default(),
                added: Vec::new(), ensured: Vec::new(), unsat_after: None }
        }
    }
    impl SatBridge for FakeBridge {
        fn solve(&mut self) -> bool {
            match self.unsat_after { Some(n) => self.added.len() < n, None => true }
        }
        fn value_bv(&self, _ctx: &Context, t: TermId) -> Option<(u32, Integer)> {
            self.bv.get(&t).cloned()
        }
        fn value_bool(&self, t: TermId) -> Option<bool> { self.boolv.get(&t).copied() }
        fn ensure_atom(&mut self, _ctx: &mut Context, atom: TermId) { self.ensured.push(atom); }
        fn add_lemma(&mut self, _ctx: &mut Context, lemma: &Lemma) { self.added.push(lemma.clone()); }
    }
}
```

- [ ] **Step 2: Wire into `lib.rs` and build**

Add to `lib.rs`:
```rust
pub mod driver;
pub use driver::{Lemma, LemmaLit, SatBridge};
```

- [ ] **Step 3: Run build to verify it compiles**

Run: `cargo test -p shinri-abv driver --no-run`
Expected: compiles (no tests yet beyond the fake; that's fine).

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-abv/src/driver.rs crates/shinri-abv/src/lib.rs
git commit -m "feat(abv): SatBridge trait, Lemma types, and test fake"
```

---

### Task 5: Functional-consistency checker (§5.1)

**Files:**
- Create: `crates/shinri-abv/src/check.rs`
- Modify: `crates/shinri-abv/src/lib.rs`

**Interfaces:**
- Consumes: `Abstraction.read_of`, `Collected.selects`, a `&dyn SatBridge` model, the `Context`.
- Produces: `pub fn functional_consistency(ctx: &Context, abs: &Abstraction, bridge: &dyn SatBridge) -> Vec<Lemma>`. A lemma `(i = j) → (r1 = r2)` is encoded as `Lemma(vec![LemmaLit{eq(i,j), pos:false}, LemmaLit{eq(r1,r2), pos:true}])`. Builds the `(= i j)` / `(= r1 r2)` atom terms via `ctx`-free precomputation — see step 3 (the checker needs `&mut Context` to build atoms, so the real signature takes `&mut Context`).

- [ ] **Step 1: Write the failing test**

```rust
//! Model-based consistency checks producing refinement lemmas.
use crate::abstraction::Abstraction;
use crate::collect::Collected;
use crate::driver::{Lemma, LemmaLit, SatBridge};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abstraction::abstract_arrays;
    use crate::collect::collect;
    use crate::driver::fake::FakeBridge;
    use shinri_num::Integer;

    fn arr(ctx: &mut Context) -> shinri_core::SortId {
        let i = ctx.bv_sort(8); let e = ctx.bv_sort(8); ctx.array_sort(i, e)
    }
    fn uconst(ctx: &mut Context, n: &str, s: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(n, &[], s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn equal_index_values_but_unequal_reads_emit_congruence_lemma() {
        let mut ctx = Context::new();
        let a = arr(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let av = uconst(&mut ctx, "a", a);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let s1 = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[av, i]).unwrap();
        let s2 = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[av, j]).unwrap();
        let e1 = ctx.mk_eq(s1, { let z = ctx.mk_bv_const(8, Integer::from(1u64)); z }).unwrap();
        let e2 = ctx.mk_eq(s2, { let z = ctx.mk_bv_const(8, Integer::from(2u64)); z }).unwrap();
        let c = collect(&ctx, &[e1, e2]);
        let abs = abstract_arrays(&mut ctx, &[e1, e2], &c);
        let (r1, r2) = (abs.read_of[&s1], abs.read_of[&s2]);

        // Model: i == j (both 5), but r1=1, r2=2 — a violation.
        let mut fake = FakeBridge::default();
        fake.bv.insert(i, (8, Integer::from(5u64)));
        fake.bv.insert(j, (8, Integer::from(5u64)));
        fake.bv.insert(r1, (8, Integer::from(1u64)));
        fake.bv.insert(r2, (8, Integer::from(2u64)));

        let lemmas = functional_consistency(&mut ctx, &abs, &c, &fake);
        assert_eq!(lemmas.len(), 1, "one congruence violation");
        // Lemma is (i=j) -> (r1=r2): [¬eq(i,j), eq(r1,r2)].
        let eq_ij = ctx.mk_eq(i, j).unwrap();
        let eq_rr = ctx.mk_eq(r1, r2).unwrap();
        assert_eq!(lemmas[0], Lemma(vec![
            LemmaLit { atom: eq_ij, pos: false },
            LemmaLit { atom: eq_rr, pos: true },
        ]));
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-abv check::tests::equal_index`
Expected: FAIL — `functional_consistency` not found.

- [ ] **Step 3: Implement the checker**

```rust
/// The base array of a select term (`select(array, index)`), and its index.
fn select_parts(ctx: &Context, sel: TermId) -> Option<(TermId, TermId)> {
    match ctx.term_node(sel) {
        TermNode::App { op: Op::Builtin(BuiltinOp::Select), args, .. } => {
            let k = ctx.children(*args);
            Some((k[0], k[1]))
        }
        _ => None,
    }
}

/// §5.1 Functional consistency: two reads on the SAME array term whose index
/// VALUES coincide but whose read VALUES differ ⇒ (i=j) → (ri=rj).
pub fn functional_consistency(
    ctx: &mut Context,
    abs: &Abstraction,
    c: &Collected,
    bridge: &dyn SatBridge,
) -> Vec<Lemma> {
    let mut lemmas = Vec::new();
    let sels = &c.selects;
    for x in 0..sels.len() {
        for y in (x + 1)..sels.len() {
            let (sx, sy) = (sels[x], sels[y]);
            let (Some((ax, ix)), Some((ay, iy))) =
                (select_parts(ctx, sx), select_parts(ctx, sy)) else { continue };
            if ax != ay { continue; } // same syntactic array only
            let (rx, ry) = (abs.read_of[&sx], abs.read_of[&sy]);
            let (Some(vix), Some(viy)) = (bridge.value_bv(ctx, ix), bridge.value_bv(ctx, iy)) else { continue };
            let (Some(vrx), Some(vry)) = (bridge.value_bv(ctx, rx), bridge.value_bv(ctx, ry)) else { continue };
            if vix.1 == viy.1 && vrx.1 != vry.1 {
                let eq_ij = ctx.mk_eq(ix, iy).expect("same index width");
                let eq_rr = ctx.mk_eq(rx, ry).expect("same elem width");
                lemmas.push(Lemma(vec![
                    LemmaLit { atom: eq_ij, pos: false },
                    LemmaLit { atom: eq_rr, pos: true },
                ]));
            }
        }
    }
    lemmas
}
```
Add `pub mod check;` to `lib.rs`.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-abv check::tests::equal_index`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-abv/src/check.rs crates/shinri-abv/src/lib.rs
git commit -m "feat(abv): functional-consistency (congruence) lemma generation"
```

---

### Task 6: Read-over-write checker (§5.2, ROW-1 + ROW-2)

**Files:**
- Modify: `crates/shinri-abv/src/check.rs`
- Modify: `crates/shinri-abv/src/abstraction.rs` (add `read_of_or_make` for on-demand reads)

**Interfaces:**
- Produces: `pub fn read_over_write(ctx: &mut Context, abs: &mut Abstraction, c: &Collected, bridge: &dyn SatBridge) -> Vec<Lemma>`. For every `sel = select(t, j)` where `t = store(a, i, e)`:
  - model `val(i) == val(j)` → `Lemma([¬eq(i,j), eq(r, e)])` where `r = read_of[sel]`.
  - model `val(i) != val(j)` → mint `sel' = select(a, j)` (and its read var via `read_of_or_make`) → `Lemma([eq(i,j) /*pos*/ … ])` encoded as `[eq(i,j) pos:true? ]`; precisely `(i≠j) → (r = select(a,j))` = `[eq(i,j) pos:true, eq(r, r') pos:true]` where `r'=read_of[sel']`. Wait: `(i≠j)→X` = `(¬¬eq ∨ X)`? No: `(i≠j)→(r=r')` ≡ `eq(i,j) ∨ (r=r')` ≡ `[LemmaLit{eq(i,j),pos:true}, LemmaLit{eq(r,r'),pos:true}]`.
- `read_of_or_make(ctx, abs, sel)` returns the existing read var or mints one (and records the new select in a returned `Vec<TermId>` of fresh selects for the controller to register/blast).

- [ ] **Step 1: Add `read_of_or_make` to `abstraction.rs` (test first)**

Test (in `abstraction.rs` tests):
```rust
#[test]
fn read_of_or_make_is_idempotent() {
    let mut ctx = Context::new();
    let arr = bv_arr(&mut ctx, 8, 8);
    let a = uconst(&mut ctx, "a", arr);
    let j = uconst(&mut ctx, "j", { ctx.bv_sort(8) });
    let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
    let mut abs = Abstraction { assertions: vec![], read_of: FxHashMap::default(), eq_proxy: FxHashMap::default() };
    let (r1, fresh1) = read_of_or_make(&mut ctx, &mut abs, sel);
    let (r2, fresh2) = read_of_or_make(&mut ctx, &mut abs, sel);
    assert_eq!(r1, r2);
    assert_eq!(fresh1, Some(sel));
    assert_eq!(fresh2, None);
    assert_eq!(ctx.bv_width(ctx.sort_of(r1)), Some(8));
}
```
Implement:
```rust
use std::sync::atomic::{AtomicUsize, Ordering};
static FRESH_CTR: AtomicUsize = AtomicUsize::new(1_000_000);

/// Read var for `sel`, minting one if absent. Returns `(read_var, Some(sel))`
/// when a new read was introduced (so the caller can blast it), else `None`.
pub fn read_of_or_make(ctx: &mut Context, abs: &mut Abstraction, sel: TermId) -> (TermId, Option<TermId>) {
    if let Some(&r) = abs.read_of.get(&sel) {
        return (r, None);
    }
    let elem_sort = ctx.sort_of(sel);
    let n = FRESH_CTR.fetch_add(1, Ordering::Relaxed);
    let r = fresh_const(ctx, &format!("$abv_read_{n}"), elem_sort);
    abs.read_of.insert(sel, r);
    (r, Some(sel))
}
```
(`fresh_const` is already in this file from Task 3; make it non-`pub` `pub(crate)` if needed.)

Run: `cargo test -p shinri-abv read_of_or_make` → PASS.

- [ ] **Step 2: Write the failing ROW test in `check.rs`**

```rust
#[test]
fn row1_equal_index_emits_read_equals_stored() {
    let mut ctx = Context::new();
    let arr_s = { let i = ctx.bv_sort(8); let e = ctx.bv_sort(8); ctx.array_sort(i, e) };
    let s8 = ctx.bv_sort(8);
    let a = { let f = ctx.declare_fun("a", &[], arr_s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let i = { let f = ctx.declare_fun("i", &[], s8); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let j = { let f = ctx.declare_fun("j", &[], s8); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let e = { let f = ctx.declare_fun("e", &[], s8); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let st = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
    let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[st, j]).unwrap();
    let atom = ctx.mk_eq(sel, e).unwrap();
    let c = crate::collect::collect(&ctx, &[atom]);
    let mut abs = crate::abstraction::abstract_arrays(&mut ctx, &[atom], &c);
    let r = abs.read_of[&sel];

    // Model: val(i)==val(j)==3 → ROW-1 violation candidate (r must equal e).
    let mut fake = crate::driver::fake::FakeBridge::default();
    fake.bv.insert(i, (8, shinri_num::Integer::from(3u64)));
    fake.bv.insert(j, (8, shinri_num::Integer::from(3u64)));
    fake.bv.insert(r, (8, shinri_num::Integer::from(0u64)));
    fake.bv.insert(e, (8, shinri_num::Integer::from(9u64))); // r != e in model → violated

    let lemmas = read_over_write(&mut ctx, &mut abs, &c, &fake);
    let eq_ij = ctx.mk_eq(i, j).unwrap();
    let eq_re = ctx.mk_eq(r, e).unwrap();
    assert!(lemmas.contains(&Lemma(vec![
        LemmaLit { atom: eq_ij, pos: false },
        LemmaLit { atom: eq_re, pos: true },
    ])));
}
```

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-abv check::tests::row1`
Expected: FAIL — `read_over_write` not found.

- [ ] **Step 4: Implement `read_over_write`**

```rust
fn store_parts(ctx: &Context, t: TermId) -> Option<(TermId, TermId, TermId)> {
    match ctx.term_node(t) {
        TermNode::App { op: Op::Builtin(BuiltinOp::Store), args, .. } => {
            let k = ctx.children(*args);
            Some((k[0], k[1], k[2]))
        }
        _ => None,
    }
}

/// §5.2 ROW. For each `select(store(a,i,e), j)`:
///   val(i)==val(j): lemma (i=j) → (r=e)
///   val(i)!=val(j): mint select(a,j); lemma (i≠j) → (r = read(select(a,j)))
pub fn read_over_write(
    ctx: &mut Context,
    abs: &mut Abstraction,
    c: &Collected,
    bridge: &dyn SatBridge,
) -> Vec<Lemma> {
    let mut lemmas = Vec::new();
    for &sel in &c.selects.clone() {
        let Some((base, j)) = select_parts(ctx, sel) else { continue };
        let Some((a, i, e)) = store_parts(ctx, base) else { continue };
        let r = abs.read_of[&sel];
        let (Some(vi), Some(vj)) = (bridge.value_bv(ctx, i), bridge.value_bv(ctx, j)) else { continue };
        if vi.1 == vj.1 {
            // ROW-1: only emit if model currently violates r == e.
            if bridge.value_bv(ctx, r).map(|x| x.1) != bridge.value_bv(ctx, e).map(|x| x.1) {
                let eq_ij = ctx.mk_eq(i, j).expect("idx width");
                let eq_re = ctx.mk_eq(r, e).expect("elem width");
                lemmas.push(Lemma(vec![
                    LemmaLit { atom: eq_ij, pos: false },
                    LemmaLit { atom: eq_re, pos: true },
                ]));
            }
        } else {
            // ROW-2: select(a, j) on demand.
            let selaj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).expect("well-sorted");
            let (raj, _fresh) = crate::abstraction::read_of_or_make(ctx, abs, selaj);
            if bridge.value_bv(ctx, r).map(|x| x.1) != bridge.value_bv(ctx, raj).map(|x| x.1) {
                let eq_ij = ctx.mk_eq(i, j).expect("idx width");
                let eq_rr = ctx.mk_eq(r, raj).expect("elem width");
                lemmas.push(Lemma(vec![
                    LemmaLit { atom: eq_ij, pos: true },  // (i≠j) in antecedent → eq(i,j) appears positive
                    LemmaLit { atom: eq_rr, pos: true },
                ]));
            }
        }
    }
    lemmas
}
```
Note: ROW-2 introduces `selaj` which is NOT yet in `c.selects`. The controller (Task 8) must, after each round, re-run `collect`-equivalent registration for newly minted selects (they are recorded in `abs.read_of`); functional-consistency over the *new* read is reached in subsequent rounds because the controller adds fresh selects to its working set. Document this with the comment above.

- [ ] **Step 5: Run to verify it passes**

Run: `cargo test -p shinri-abv check::tests::row1`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-abv/src/check.rs crates/shinri-abv/src/abstraction.rs
git commit -m "feat(abv): read-over-write (ROW-1/ROW-2) lemma generation"
```

---

### Task 7: Extensionality checker (§5.3)

**Files:**
- Modify: `crates/shinri-abv/src/check.rs`
- Modify: `crates/shinri-abv/src/abstraction.rs` (witness-index registry)

**Interfaces:**
- Produces: `pub fn extensionality(ctx: &mut Context, abs: &mut Abstraction, c: &Collected, bridge: &dyn SatBridge, witnesses: &mut FxHashMap<TermId, TermId>) -> Vec<Lemma>`.
  - For each array-eq atom `(= a b)` with proxy `p = eq_proxy[atom]`:
    - `value_bool(p) == Some(true)`: for each accessed index `k` (the index of any select on `a` or `b`), if model `val(select(a,k)) != val(select(b,k))`, emit `p → (select(a,k) = select(b,k))` = `[LemmaLit{p,false}, LemmaLit{eq(ra_k, rb_k),true}]` (minting reads as needed).
    - `value_bool(p) == Some(false)`: mint one Skolem witness `w_ab` (cached in `witnesses` per atom), reads `select(a,w)`/`select(b,w)`, emit `¬p → (select(a,w) ≠ select(b,w))` = `[LemmaLit{p,true}, LemmaLit{eq(raw, rbw), false}]`.
- `witnesses` maps the array-eq atom → its witness index term (BV var of the index width), minted once.

- [ ] **Step 1: Write the failing test (false-proxy → witness disequality)**

```rust
#[test]
fn ext_false_proxy_mints_witness_disequality() {
    let mut ctx = Context::new();
    let arr_s = { let i = ctx.bv_sort(8); let e = ctx.bv_sort(8); ctx.array_sort(i, e) };
    let a = { let f = ctx.declare_fun("a", &[], arr_s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let b = { let f = ctx.declare_fun("b", &[], arr_s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let atom = ctx.mk_eq(a, b).unwrap();
    let c = crate::collect::collect(&ctx, &[atom]);
    let mut abs = crate::abstraction::abstract_arrays(&mut ctx, &[atom], &c);
    let p = abs.eq_proxy[&atom];

    let mut fake = crate::driver::fake::FakeBridge::default();
    fake.boolv.insert(p, false); // a != b asserted

    let mut witnesses = rustc_hash::FxHashMap::default();
    let lemmas = extensionality(&mut ctx, &mut abs, &c, &fake, &mut witnesses);
    assert_eq!(lemmas.len(), 1);
    let w = witnesses[&atom];
    assert_eq!(ctx.bv_width(ctx.sort_of(w)), Some(8));
    // Lemma: [p (pos:true), ¬eq(read(sel a w), read(sel b w))].
    let saw = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, w]).unwrap();
    let sbw = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[b, w]).unwrap();
    let raw = abs.read_of[&saw];
    let rbw = abs.read_of[&sbw];
    let eq_rr = ctx.mk_eq(raw, rbw).unwrap();
    assert_eq!(lemmas[0], Lemma(vec![
        LemmaLit { atom: p, pos: true },
        LemmaLit { atom: eq_rr, pos: false },
    ]));
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-abv check::tests::ext_false`
Expected: FAIL — `extensionality` not found.

- [ ] **Step 3: Implement `extensionality`**

```rust
use rustc_hash::FxHashMap;

fn array_pair(ctx: &Context, atom: TermId) -> Option<(TermId, TermId)> {
    match ctx.term_node(atom) {
        TermNode::App { op: Op::Builtin(BuiltinOp::Eq), args, .. }
        | TermNode::App { op: Op::Builtin(BuiltinOp::Distinct), args, .. } => {
            let k = ctx.children(*args);
            Some((k[0], k[1]))
        }
        _ => None,
    }
}

/// Index width of an array-sorted term.
fn index_width(ctx: &Context, arr: TermId) -> u32 {
    match ctx.sort_node(ctx.sort_of(arr)) {
        shinri_core::SortNode::Array(idx, _) => ctx.bv_width(*idx).expect("BV index"),
        _ => panic!("not an array sort"),
    }
}

pub fn extensionality(
    ctx: &mut Context,
    abs: &mut Abstraction,
    c: &Collected,
    bridge: &dyn SatBridge,
    witnesses: &mut FxHashMap<TermId, TermId>,
) -> Vec<Lemma> {
    let mut lemmas = Vec::new();
    for &atom in &c.array_eqs.clone() {
        let Some((a, b)) = array_pair(ctx, atom) else { continue };
        let p = abs.eq_proxy[&atom];
        match bridge.value_bool(p) {
            Some(true) => {
                // Agreement over accessed indices.
                for k in accessed_indices(ctx, c, a, b) {
                    let sak = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, k]).expect("ws");
                    let sbk = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[b, k]).expect("ws");
                    let (rak, _) = crate::abstraction::read_of_or_make(ctx, abs, sak);
                    let (rbk, _) = crate::abstraction::read_of_or_make(ctx, abs, sbk);
                    if bridge.value_bv(ctx, rak).map(|x| x.1) != bridge.value_bv(ctx, rbk).map(|x| x.1) {
                        let eq_rr = ctx.mk_eq(rak, rbk).expect("ws");
                        lemmas.push(Lemma(vec![
                            LemmaLit { atom: p, pos: false },
                            LemmaLit { atom: eq_rr, pos: true },
                        ]));
                    }
                }
            }
            Some(false) => {
                // One witness per pair, minted once.
                let w = *witnesses.entry(atom).or_insert_with(|| {
                    let iw = index_width(ctx, a);
                    let s = ctx.bv_sort(iw);
                    crate::abstraction::fresh_const(ctx, &format!("$abv_wit_{}", witnesses.len()), s)
                });
                let saw = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, w]).expect("ws");
                let sbw = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[b, w]).expect("ws");
                let (raw, _) = crate::abstraction::read_of_or_make(ctx, abs, saw);
                let (rbw, _) = crate::abstraction::read_of_or_make(ctx, abs, sbw);
                let eq_rr = ctx.mk_eq(raw, rbw).expect("ws");
                lemmas.push(Lemma(vec![
                    LemmaLit { atom: p, pos: true },
                    LemmaLit { atom: eq_rr, pos: false },
                ]));
            }
            None => {}
        }
    }
    lemmas
}

/// Index terms of all selects whose base array is `a` or `b`.
fn accessed_indices(ctx: &Context, c: &Collected, a: TermId, b: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    for &sel in &c.selects {
        if let Some((base, idx)) = select_parts(ctx, sel) {
            if base == a || base == b {
                out.push(idx);
            }
        }
    }
    out
}
```
Make `fresh_const` `pub(crate)` in `abstraction.rs`.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-abv check::tests::ext_false`
Expected: PASS.

- [ ] **Step 5: Add the true-proxy agreement test and confirm it passes**

```rust
#[test]
fn ext_true_proxy_emits_agreement_when_reads_differ() {
    let mut ctx = Context::new();
    let arr_s = { let i = ctx.bv_sort(8); let e = ctx.bv_sort(8); ctx.array_sort(i, e) };
    let s8 = ctx.bv_sort(8);
    let a = { let f = ctx.declare_fun("a", &[], arr_s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let b = { let f = ctx.declare_fun("b", &[], arr_s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let k = { let f = ctx.declare_fun("k", &[], s8); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
    let sak = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, k]).unwrap();
    let sbk = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[b, k]).unwrap();
    let aeq = ctx.mk_eq(a, b).unwrap();
    // Reads are present in the formula so accessed_indices finds k.
    let c = crate::collect::collect(&ctx, &[aeq, sak, sbk]);
    let mut abs = crate::abstraction::abstract_arrays(&mut ctx, &[aeq, sak, sbk], &c);
    let p = abs.eq_proxy[&aeq];
    let (rak, rbk) = (abs.read_of[&sak], abs.read_of[&sbk]);
    let mut fake = crate::driver::fake::FakeBridge::default();
    fake.boolv.insert(p, true);
    fake.bv.insert(rak, (8, shinri_num::Integer::from(1u64)));
    fake.bv.insert(rbk, (8, shinri_num::Integer::from(2u64)));
    let mut w = rustc_hash::FxHashMap::default();
    let lemmas = extensionality(&mut ctx, &mut abs, &c, &fake, &mut w);
    let eq_rr = ctx.mk_eq(rak, rbk).unwrap();
    assert!(lemmas.contains(&Lemma(vec![
        LemmaLit { atom: p, pos: false },
        LemmaLit { atom: eq_rr, pos: true },
    ])));
}
```
Run: `cargo test -p shinri-abv check::tests::ext_true` → PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-abv/src/check.rs crates/shinri-abv/src/abstraction.rs
git commit -m "feat(abv): extensionality lemmas (agreement + Skolem witness)"
```

---

### Task 8: Refinement controller loop

**Files:**
- Modify: `crates/shinri-abv/src/driver.rs`
- Modify: `crates/shinri-abv/src/lib.rs`

**Interfaces:**
- Produces:
```rust
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbvOutcome { Sat, Unsat, Unknown }

/// Run the abstraction–refinement loop. `bridge` already holds the blasted
/// abstraction (Task 10 sets it up). The controller re-solves, checks the
/// model, and feeds lemmas back until convergence.
pub fn refine<B: SatBridge>(ctx: &mut Context, abs: &mut Abstraction, c: &mut Collected, bridge: &mut B) -> AbvOutcome;
```
- Dedup: keep a `FxHashSet<Lemma>` of added lemmas (requires `Lemma: Hash`; derive it). Termination: if a full check round produces zero *new* lemmas, return `Sat`.
- After ROW-2/extensionality mint new selects (recorded in `abs.read_of`), the controller appends them to `c.selects` so subsequent rounds check congruence/ROW over them.

- [ ] **Step 1: Derive `Hash` on `Lemma`/`LemmaLit`**

Change their derives to `#[derive(Clone, Debug, PartialEq, Eq, Hash)]` (and `Copy` on `LemmaLit`).

- [ ] **Step 2: Write the failing test**

```rust
#[cfg(test)]
mod loop_tests {
    use super::*;
    use super::fake::FakeBridge;
    use crate::abstraction::{abstract_arrays, Abstraction};
    use crate::collect::collect;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

    #[test]
    fn converges_to_unsat_when_congruence_forces_contradiction() {
        let mut ctx = Context::new();
        let arr_s = { let i = ctx.bv_sort(8); let e = ctx.bv_sort(8); ctx.array_sort(i, e) };
        let s8 = ctx.bv_sort(8);
        let mk = |ctx: &mut Context, n: &str, s| { let f = ctx.declare_fun(n, &[], s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
        let a = mk(&mut ctx, "a", arr_s);
        let i = mk(&mut ctx, "i", s8);
        let j = mk(&mut ctx, "j", s8);
        let s1 = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let s2 = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let atom = ctx.mk_eq(s1, s2).unwrap(); // placeholder assertion
        let mut c = collect(&ctx, &[atom]);
        let mut abs = abstract_arrays(&mut ctx, &[atom], &c);
        let (r1, r2) = (abs.read_of[&s1], abs.read_of[&s2]);

        // Fake: i==j, r1!=r2 → congruence fires; flip to UNSAT after 1 lemma.
        let mut fake = FakeBridge::default();
        fake.bv.insert(i, (8, Integer::from(5u64)));
        fake.bv.insert(j, (8, Integer::from(5u64)));
        fake.bv.insert(r1, (8, Integer::from(1u64)));
        fake.bv.insert(r2, (8, Integer::from(2u64)));
        fake.unsat_after = Some(1);

        let out = refine(&mut ctx, &mut abs, &mut c, &mut fake);
        assert_eq!(out, AbvOutcome::Unsat);
        assert_eq!(fake.added.len(), 1, "exactly the congruence lemma");
    }

    #[test]
    fn consistent_model_returns_sat_without_lemmas() {
        let mut ctx = Context::new();
        let arr_s = { let i = ctx.bv_sort(8); let e = ctx.bv_sort(8); ctx.array_sort(i, e) };
        let s8 = ctx.bv_sort(8);
        let mk = |ctx: &mut Context, n: &str, s| { let f = ctx.declare_fun(n, &[], s); ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap() };
        let a = mk(&mut ctx, "a", arr_s);
        let i = mk(&mut ctx, "i", s8);
        let s1 = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let atom = ctx.mk_eq(s1, s1).unwrap();
        let mut c = collect(&ctx, &[atom]);
        let mut abs = abstract_arrays(&mut ctx, &[atom], &c);
        let mut fake = FakeBridge::default();
        fake.bv.insert(i, (8, Integer::from(0u64)));
        fake.bv.insert(abs.read_of[&s1], (8, Integer::from(0u64)));
        let out = refine(&mut ctx, &mut abs, &mut c, &mut fake);
        assert_eq!(out, AbvOutcome::Sat);
        assert!(fake.added.is_empty());
    }
}
```

- [ ] **Step 3: Run to verify it fails**

Run: `cargo test -p shinri-abv driver::loop_tests`
Expected: FAIL — `refine`/`AbvOutcome` not found.

- [ ] **Step 4: Implement `refine`**

```rust
use rustc_hash::FxHashSet;
use crate::abstraction::Abstraction;
use crate::collect::Collected;
use crate::check;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbvOutcome { Sat, Unsat, Unknown }

pub fn refine<B: SatBridge>(
    ctx: &mut Context,
    abs: &mut Abstraction,
    c: &mut Collected,
    bridge: &mut B,
) -> AbvOutcome {
    let mut added: FxHashSet<Lemma> = FxHashSet::default();
    let mut witnesses: FxHashMap<TermId, TermId> = FxHashMap::default();
    loop {
        if !bridge.solve() {
            return AbvOutcome::Unsat;
        }
        // Snapshot selects so newly-minted reads (this round) are picked up next.
        let before = c.selects.len();

        let mut round: Vec<Lemma> = Vec::new();
        round.extend(check::functional_consistency(ctx, abs, c, bridge));
        round.extend(check::read_over_write(ctx, abs, c, bridge));
        round.extend(check::extensionality(ctx, abs, c, bridge, &mut witnesses));

        // Register any selects minted this round (recorded in abs.read_of) into c.
        sync_new_selects(ctx, abs, c);
        let _ = before; // documented: growth observed via sync_new_selects

        let mut progress = false;
        for lemma in round {
            if added.insert(lemma.clone()) {
                for lit in &lemma.0 {
                    bridge.ensure_atom(ctx, lit.atom);
                }
                bridge.add_lemma(ctx, &lemma);
                progress = true;
            }
        }
        if !progress {
            return AbvOutcome::Sat;
        }
    }
}

/// Append selects present in `abs.read_of` but not yet in `c.selects`.
fn sync_new_selects(ctx: &Context, abs: &Abstraction, c: &mut Collected) {
    use shinri_core::{BuiltinOp, Op, TermNode};
    let existing: FxHashSet<TermId> = c.selects.iter().copied().collect();
    for &sel in abs.read_of.keys() {
        if !existing.contains(&sel)
            && matches!(ctx.term_node(sel), TermNode::App { op: Op::Builtin(BuiltinOp::Select), .. })
        {
            c.selects.push(sel);
        }
    }
}
```
Add to `lib.rs`: `pub use driver::{refine, AbvOutcome};`.

- [ ] **Step 5: Run to verify it passes**

Run: `cargo test -p shinri-abv driver::loop_tests`
Expected: PASS (both).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-abv/src/driver.rs crates/shinri-abv/src/lib.rs
git commit -m "feat(abv): refinement controller loop with lemma dedup + termination"
```

---

### Task 9: Array model assembly + SMT-LIB rendering

**Files:**
- Create: `crates/shinri-abv/src/model.rs`
- Modify: `crates/shinri-abv/src/lib.rs`

**Interfaces:**
- Produces:
```rust
/// A finite array model: default element + (index value -> element value) points.
pub struct ArrayModel {
    pub idx_width: u32,
    pub elem_width: u32,
    pub points: Vec<(shinri_num::Integer, shinri_num::Integer)>, // sorted, deduped by index
    pub default: shinri_num::Integer,
}
/// Build from the accesses on `arr` and the final consistent model.
pub fn array_model(ctx: &Context, c: &Collected, abs: &Abstraction, arr: TermId, bridge: &dyn SatBridge) -> ArrayModel;
/// Render as SMT-LIB: nested store over ((as const (Array ...)) default).
pub fn render(m: &ArrayModel) -> String;
```
- Rendering reuses `shinri-bv`'s value form: `#x..`/`#b..` via a local helper mirroring `shinri-solver`'s `format_bin_fixed`/`format_hex_fixed` (copy the two helpers; they are tiny and currently private).

- [ ] **Step 1: Write the failing render test**

```rust
use crate::abstraction::Abstraction;
use crate::collect::Collected;
use crate::driver::SatBridge;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_num::Integer;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_nested_store_over_const() {
        let m = ArrayModel {
            idx_width: 8,
            elem_width: 8,
            points: vec![(Integer::from(1u64), Integer::from(255u64))],
            default: Integer::from(0u64),
        };
        // ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) with one store.
        let s = render(&m);
        assert_eq!(
            s,
            "(store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) #x01 #xff)"
        );
    }
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-abv model::tests::renders`
Expected: FAIL — `render`/`ArrayModel` not found.

- [ ] **Step 3: Implement `ArrayModel`, `array_model`, `render`**

```rust
pub struct ArrayModel {
    pub idx_width: u32,
    pub elem_width: u32,
    pub points: Vec<(Integer, Integer)>,
    pub default: Integer,
}

fn fmt_bv(width: u32, val: &Integer) -> String {
    if width % 4 == 0 {
        let digits = (width / 4) as usize;
        // hex, zero-padded
        let mut s = format!("{:x}", val);
        while s.len() < digits { s.insert(0, '0'); }
        format!("#x{s}")
    } else {
        let mut bits = String::new();
        let two = Integer::from(2u64);
        let mut rem = val.clone();
        let mut tmp = Vec::new();
        for _ in 0..width {
            let (q, r) = rem.div_rem(&two);
            tmp.push(if r.is_zero() { '0' } else { '1' });
            rem = q;
        }
        for ch in tmp.into_iter().rev() { bits.push(ch); }
        format!("#b{bits}")
    }
}

pub fn render(m: &ArrayModel) -> String {
    let base = format!(
        "((as const (Array (_ BitVec {}) (_ BitVec {}))) {})",
        m.idx_width, m.elem_width, fmt_bv(m.elem_width, &m.default)
    );
    let mut out = base;
    for (idx, val) in &m.points {
        out = format!("(store {out} {} {})", fmt_bv(m.idx_width, idx), fmt_bv(m.elem_width, val));
    }
    out
}

fn select_parts(ctx: &Context, sel: TermId) -> Option<(TermId, TermId)> {
    match ctx.term_node(sel) {
        TermNode::App { op: Op::Builtin(BuiltinOp::Select), args, .. } => {
            let k = ctx.children(*args);
            Some((k[0], k[1]))
        }
        _ => None,
    }
}

pub fn array_model(
    ctx: &Context,
    c: &Collected,
    abs: &Abstraction,
    arr: TermId,
    bridge: &dyn SatBridge,
) -> ArrayModel {
    let (idx_width, elem_width) = match ctx.sort_node(ctx.sort_of(arr)) {
        shinri_core::SortNode::Array(i, e) => (ctx.bv_width(*i).unwrap(), ctx.bv_width(*e).unwrap()),
        _ => panic!("not array sort"),
    };
    let mut points: Vec<(Integer, Integer)> = Vec::new();
    let mut seen = rustc_hash::FxHashSet::default();
    for &sel in &c.selects {
        if let Some((base, idx)) = select_parts(ctx, sel) {
            if base != arr { continue; }
            let r = abs.read_of[&sel];
            if let (Some(iv), Some(rv)) = (bridge.value_bv(ctx, idx), bridge.value_bv(ctx, r)) {
                if seen.insert(iv.1.clone()) {
                    points.push((iv.1, rv.1));
                }
            }
        }
    }
    points.sort_by(|a, b| a.0.cmp(&b.0));
    ArrayModel { idx_width, elem_width, points, default: Integer::from(0u64) }
}
```
Add `pub mod model;` and re-exports to `lib.rs`. (If `Integer` lacks `div_rem`/`is_zero` in this position, mirror `blast_word`'s usage in `shinri-bv` — it uses exactly `div_rem(&two)` and `is_zero()`.)

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-abv model`
Expected: PASS. Run `cargo fmt -p shinri-abv && cargo clippy -p shinri-abv --all-targets` clean.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-abv/src/model.rs crates/shinri-abv/src/lib.rs
git commit -m "feat(abv): finite array-model assembly + SMT-LIB store rendering"
```

---

### Task 10: Real `SatBridge` + routing + fence in `shinri-solver`

**Files:**
- Create: `crates/shinri-solver/src/abv_stage.rs`
- Modify: `crates/shinri-solver/src/lib.rs` (add `mod abv_stage;`; route in `check_sat`)
- Modify: `crates/shinri-solver/Cargo.toml` (add `shinri-abv = { path = "../shinri-abv" }`)

**Interfaces:**
- Consumes: `shinri_abv::{collect, abstract_arrays, refine, AbvOutcome, SatBridge, Lemma}`, the extended `Blaster` (`num_vars`, `take_new_clauses`), and the existing `Encoder`/`replay_bv_cnf` machinery.
- Produces in `abv_stage.rs`:
  - `pub fn uses_arrays_over_bv(ctx: &Context, assertions: &[TermId]) -> bool` — true iff a `select`/`store`/array-eq over a `(Array (_ BitVec _) (_ BitVec _))` is present.
  - `pub fn fenced(ctx: &Context, assertions: &[TermId]) -> bool` — true iff arrays appear AND any non-BV/non-array theory atom is present (reuse `bv_stage::has_non_bv_theory_atom`-style logic; arrays-with-uninterpreted-index/elem also fence).
  - A `RealBridge<'a>` struct implementing `SatBridge` that owns: a live `shinri_sat::Solver<...>`, a persistent `shinri_bv::Blaster`, the abstraction's `var_bits`/`atom_lit` SAT-var maps, and `t_true`/`t_false` for the encoder. `solve()` calls `sat.solve()`; `value_bv` reads bits via the var map + `shinri_bv::model::pack`; `value_bool` reads the proxy's SAT var; `ensure_atom`/`add_lemma` blast atoms with the persistent `Blaster`, `take_new_clauses()`, replay into `sat` (allocating SAT vars contiguously like `replay_bv_cnf`), and `add_clause` the lemma.

- [ ] **Step 1: Write the failing detection/fence tests in `abv_stage.rs`**

```rust
//! QF_ABV detection, fence, and the real SatBridge over the live SAT solver.
#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};

    fn uconst(ctx: &mut Context, n: &str, s: shinri_core::SortId) -> shinri_core::TermId {
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn detects_select_over_bv_array() {
        let mut ctx = Context::new();
        let i = ctx.bv_sort(8); let e = ctx.bv_sort(8);
        let arr = ctx.array_sort(i, e);
        let a = uconst(&mut ctx, "a", arr);
        let idx = uconst(&mut ctx, "i", i);
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, idx]).unwrap();
        assert!(uses_arrays_over_bv(&ctx, &[sel]));
    }

    #[test]
    fn array_with_uninterpreted_index_is_fenced() {
        let mut ctx = Context::new();
        let i = ctx.declare_sort("I");      // uninterpreted index
        let e = ctx.bv_sort(8);
        let arr = ctx.array_sort(i, e);
        let a = uconst(&mut ctx, "a", arr);
        let idx = uconst(&mut ctx, "i", i);
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, idx]).unwrap();
        // Not a QF_ABV array (index not BV) → detection is false (handled by Combiner/QF_AX).
        assert!(!uses_arrays_over_bv(&ctx, &[sel]));
    }
}
```

- [ ] **Step 2: Implement detection + fence (run tests to pass)**

```rust
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};

fn is_bv_array(ctx: &Context, t: TermId) -> bool {
    match ctx.sort_node(ctx.sort_of(t)) {
        SortNode::Array(i, e) => ctx.bv_width(*i).is_some() && ctx.bv_width(*e).is_some(),
        _ => false,
    }
}

pub fn uses_arrays_over_bv(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen = FxHashSet::default();
    assertions.iter().any(|&a| walk_uses(ctx, a, &mut seen))
}

fn walk_uses(ctx: &Context, t: TermId, seen: &mut FxHashSet<TermId>) -> bool {
    if !seen.insert(t) { return false; }
    match ctx.term_node(t) {
        TermNode::App { op, args, .. } => {
            let kids = ctx.children(*args).to_vec();
            let hit = matches!(op, Op::Builtin(BuiltinOp::Select) | Op::Builtin(BuiltinOp::Store))
                && kids.first().map(|&k| is_bv_array(ctx, k)).unwrap_or(false);
            hit || kids.iter().any(|&k| walk_uses(ctx, k, seen))
        }
        TermNode::Const { .. } => false,
    }
}
```
Run: `cargo test -p shinri-solver abv_stage::tests` → PASS (both detection tests). Add `mod abv_stage;` to `lib.rs` and the `shinri-abv` dependency to `Cargo.toml`.

- [ ] **Step 3: Implement `RealBridge` (write a focused integration test first)**

Integration test (`abv_stage.rs` tests, gated normally — no z3 needed):
```rust
#[test]
fn end_to_end_row1_unsat_via_real_bridge() {
    // (= (select (store a i e) i) (bvadd e #x01))  is UNSAT (ROW-1 forces select=e,
    // but e != e+1 in BV8).
    let mut ctx = Context::new();
    let i8 = ctx.bv_sort(8);
    let arr = ctx.array_sort(i8, i8);
    let mk = |ctx: &mut Context, n: &str, s| { let f = ctx.declare_fun(n,&[],s); ctx.mk_app(Op::Uninterpreted(f),&[]).unwrap() };
    let a = mk(&mut ctx, "a", arr);
    let i = mk(&mut ctx, "i", i8);
    let e = mk(&mut ctx, "e", i8);
    let st = ctx.mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e]).unwrap();
    let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[st, i]).unwrap();
    let one = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
    let ep1 = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[e, one]).unwrap();
    let atom = ctx.mk_eq(sel, ep1).unwrap();
    let outcome = super::solve_qfabv(&mut ctx, &[atom]);
    assert_eq!(outcome, shinri_abv::AbvOutcome::Unsat);
}
```
Then implement `RealBridge` + `solve_qfabv` driving the loop. The bridge mirrors `replay_bv_cnf`'s contiguous-allocation pattern, but keeps the `Blaster` alive:
```rust
use shinri_core::{Lit, Var};
use rustc_hash::FxHashMap;

pub fn solve_qfabv(ctx: &mut Context, assertions: &[TermId]) -> shinri_abv::AbvOutcome {
    use shinri_abv::{abstract_arrays, collect, refine};
    let mut c = collect::collect(ctx, assertions);
    let mut abs = abstract_arrays(ctx, assertions, &c);
    let mut bridge = RealBridge::new(ctx, &abs);     // builds SAT, blasts abstraction, encodes skeleton
    refine(ctx, &mut abs, &mut c, &mut bridge)
}
```
`RealBridge::new` must: (1) collect BV atoms of `abs.assertions` via `bv_stage::collect_bv_atoms`; (2) blast them with a persistent `Blaster` (replace the one-shot `shinri_bv::lower` with direct `Blaster` calls so the blaster survives), recording `atom_lit`/`var_bits`; (3) build the `Sat` solver (`Combiner` theory unused here — use the same `Sat` type or a `NoTheory` solver since no lazy theory atoms remain after abstraction; **prefer `NoTheory`** because the abstraction is pure BV+Bool); (4) replay CNF (contiguous base offset, store it as `self.base`); (5) Tseitin-encode the abstracted Boolean skeleton, mapping BV atoms to surrogate lits and array-eq proxies to fresh SAT vars; record `proxy_var: FxHashMap<TermId, Var>`; (6) assert the top-level lits.

`value_bv(ctx, t)`: look up `t`'s blasted bits in `var_bits` (mapped to SAT `Var`s via `base`), read each with `sat.value_of`, `pack`, return `(width, Integer)`. If `t` was not blasted yet, blast it now via the persistent blaster + drain/replay, then read.

`ensure_atom(ctx, atom)`: if `atom` already in `atom_lit`, return; else `let bl = blaster.blast_atom(ctx, rewrite(ctx, atom)); replay take_new_clauses() into sat (extend var block); atom_lit.insert(atom, map(bl));`.

`add_lemma(ctx, lemma)`: map each `LemmaLit{atom,pos}` to its surrogate `Lit` (BV atom → `atom_lit`; array-eq proxy → `proxy_var`), apply `pos`, and `sat.add_clause(&lits)`.

> Implementation note for the engineer: the cleanest path is to **generalize `replay_bv_cnf`** (currently in `lib.rs`) into a small helper that, given `&mut sat`, a `&[Vec<BitLit>]` batch, and the current `base`, allocates `new_vars` and adds the mapped clauses — then call it once for the initial CNF and again from `ensure_atom` for each drained batch. Keep a running `next_base` so newly blasted BitVars map to fresh SAT vars. The blaster's var 0 (pinned-true) is allocated once at `base` and reused (do NOT re-pin on later batches).

- [ ] **Step 4: Run the integration test**

Run: `cargo test -p shinri-solver abv_stage::tests::end_to_end_row1_unsat`
Expected: PASS.

- [ ] **Step 5: Route QF_ABV in `check_sat`**

In `check_sat` (`lib.rs`), BEFORE the existing BV path, add:
```rust
if crate::abv_stage::uses_arrays_over_bv(&self.ctx, &assertions) {
    if crate::abv_stage::fenced(&self.ctx, &assertions) {
        return SolveOutcome::Unknown;
    }
    let assertions_owned = assertions.clone();
    return match crate::abv_stage::solve_qfabv(&mut self.ctx, &assertions_owned) {
        shinri_abv::AbvOutcome::Sat => {
            // model stashed by solve_qfabv via a side channel (Task 11)
            SolveOutcome::Sat
        }
        shinri_abv::AbvOutcome::Unsat => SolveOutcome::Unsat,
        shinri_abv::AbvOutcome::Unknown => SolveOutcome::Unknown,
    };
}
```
(`fenced` returns true when arrays coexist with EUF/arith atoms; implement by reusing `bv_stage::collect_bv_atoms` + `has_non_bv_theory_atom` over the array-stripped assertions, OR conservatively: any uninterpreted-sorted (non-array, non-BV) atom present → fence.)

- [ ] **Step 6: Run full solver tests + fmt/clippy**

Run: `cargo test -p shinri-solver && cargo fmt --all && cargo clippy --workspace --all-targets`
Expected: PASS, clean. Confirm existing QF_BV/QF_AX/LIA tests are unaffected (the new path only triggers on BV-arrays).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-solver/src/abv_stage.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/Cargo.toml
git commit -m "feat(abv): real SatBridge, QF_ABV routing + fence in shinri-solver"
```

---

### Task 11: `get-model` / `get-value` array rendering

**Files:**
- Modify: `crates/shinri-solver/src/abv_stage.rs` (stash array models on SAT)
- Modify: `crates/shinri-solver/src/lib.rs` (surface array values from the model)
- Modify: `crates/shinri-solver/src/model.rs` (render array values in `format_model`)

**Interfaces:**
- Consumes: `shinri_abv::model::{array_model, render, ArrayModel}`.
- Produces: on a SAT QF_ABV result, the `Solver` retains a `FxHashMap<TermId, String>` of pre-rendered array values (declared array constants → SMT-LIB store form), surfaced by `get_model_string`/`get_value` alongside BV constants.

- [ ] **Step 1: Write a failing model test**

```rust
#[test]
fn get_model_renders_array_after_sat() {
    // (= (select a #x01) #xff) is SAT; model must map a at index 1 to 0xff.
    let mut ctx = Context::new();
    let i8 = ctx.bv_sort(8);
    let arr = ctx.array_sort(i8, i8);
    let af = ctx.declare_fun("a", &[], arr);
    let a = ctx.mk_app(Op::Uninterpreted(af), &[]).unwrap();
    let one = ctx.mk_bv_const(8, shinri_num::Integer::from(1u64));
    let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, one]).unwrap();
    let ff = ctx.mk_bv_const(8, shinri_num::Integer::from(255u64));
    let atom = ctx.mk_eq(sel, ff).unwrap();

    // (driver test helper that returns the model string for the array term)
    let s = super::solve_qfabv_model_string(&mut ctx, &[atom], a);
    assert!(s.contains("#x01") && s.contains("#xff") && s.starts_with("(store ((as const"));
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-solver abv_stage::tests::get_model_renders`
Expected: FAIL — helper not found.

- [ ] **Step 3: Implement model stashing + rendering**

Extend `solve_qfabv` to, on `AbvOutcome::Sat`, build `array_model(ctx, &c, &abs, arr, &bridge)` for each declared array constant in the original assertions and `render` it, returning the map. Add a thin `solve_qfabv_model_string(ctx, assertions, arr)` test helper that returns `render(&array_model(...))` for one array. In `check_sat`, store the rendered map on the `Solver` (new field `abv_array_models: FxHashMap<TermId, String>`), and in `model.rs::format_model`, emit `(define-fun <name> () (Array ...) <rendered>)` lines for those entries.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-solver abv_stage::tests::get_model_renders`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/abv_stage.rs crates/shinri-solver/src/lib.rs crates/shinri-solver/src/model.rs
git commit -m "feat(abv): array model rendering in get-model/get-value"
```

---

### Task 12: Differential oracle vs z3 (`qfabv_oracle.rs`)

**Files:**
- Create: `crates/shinri-solver/tests/qfabv_oracle.rs`

**Interfaces:**
- Consumes: `shinri_solver::{Solver, SolveOutcome}`, `easy-smt`. Gated by `#![cfg(feature = "oracle")]` (the `oracle` feature already exists in `shinri-solver/Cargo.toml`).

- [ ] **Step 1: Write the oracle harness**

Copy the `Lcg`, `bv_lit_smt2`, and z3-context scaffolding verbatim from `crates/shinri-solver/tests/qfbv_oracle.rs`. Add a QF_ABV generator that, per instance, declares 2 BV-arrays `(Array (_ BitVec 8) (_ BitVec 8))`, 3 index consts, 3 element consts, and builds:
- 1 store-select witness `(select (store a i e) j)` compared (`=`/`distinct`) to an element term — exercises ROW-1/ROW-2 (mirror the structure documented in `tests/qfax_oracle.rs`, which bounds to ONE store per instance to keep the search tractable).
- 1 functional-consistency atom: two selects on the same array compared.
- 1 extensionality atom: `(= a b)` or `(distinct a b)`.
Emit the matching SMT-LIB `dump` for z3 and the shinri `TermId` assertions.

```rust
#![cfg(feature = "oracle")]
// ... Lcg, bv_lit_smt2 copied from qfbv_oracle.rs ...

const N_ITERS: usize = 200;

#[test]
fn qfabv_matches_z3() {
    let mut rng = Lcg(0xABV_0000_0001);
    for it in 0..N_ITERS {
        let (asserts_s, dump, _arrs) = gen_instance(&mut rng);
        let mut solver = Solver::new();
        for a in &asserts_s { solver.assert(*a); }
        let ours = solver.check_sat();
        let theirs = z3_verdict(&dump); // "sat" | "unsat" | "unknown"
        match (ours, theirs.as_str()) {
            (SolveOutcome::Sat, "sat") | (SolveOutcome::Unsat, "unsat") => {}
            (SolveOutcome::Unknown, _) => {}        // our incompleteness is allowed
            (_, "unknown") => {}                     // z3 unknown — skip
            (o, t) => panic!("iter {it}: shinri={o:?} z3={t}\n{dump}"),
        }
    }
}
```
(Provide `gen_instance` and `z3_verdict` mirroring the existing oracle files; `z3_verdict` shells out to `z3 -in` with the dump + `(check-sat)`.)

- [ ] **Step 2: Run the oracle (requires z3 on PATH)**

Run: `cargo test -p shinri-solver --features oracle --test qfabv_oracle -- --nocapture`
Expected: PASS (no mismatches). If z3 is absent the test is `#[cfg(feature="oracle")]`-gated and skipped by default builds.

- [ ] **Step 3: Run the default suite to confirm no regressions**

Run: `cargo test --workspace && cargo fmt --all --check && cargo clippy --workspace --all-targets`
Expected: PASS, clean.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/qfabv_oracle.rs
git commit -m "test(abv): QF_ABV differential oracle vs z3 (ROW + congruence + extensionality)"
```

---

## Self-Review

**1. Spec coverage:**
- §1 scope (flat BV→BV, extensional, fence) → Tasks 1, 10 (detection/fence), 7 (extensional).
- §2 approach (lemmas-on-demand, not via Combiner, eager blaster reuse) → Tasks 2, 8, 10.
- §3 architecture (`shinri-abv` crate, controller, `SatBridge`, `shinri-bv` extension, routing) → Tasks 1, 2, 4, 8, 10.
- §4 abstraction (reads→fresh BV, array-eq→bool, no axioms) → Task 3.
- §5.1 functional consistency → Task 5; §5.2 ROW-1/ROW-2 → Task 6; §5.3 extensionality both directions → Task 7.
- §6 soundness/termination (UNSAT-final via relaxation, dedup + finite lemmas) → Task 8 (dedup/termination), exercised in Task 12.
- §7 model extraction (nested store / `as const`) → Tasks 9, 11.
- §8 testing (differential vs z3, e2e, per-lemma units, fence) → Tasks 5–8 (units), 10 (fence + e2e), 12 (oracle).
- §9 resolved defaults (crate `shinri-abv`; live solver, no push/pop) → Tasks 1, 8, 10.

**2. Placeholder scan:** No "TBD"/"add error handling"/"similar to Task N" — each step carries concrete code or an exact command. Task 10's `RealBridge::new` is described as numbered concrete sub-steps with the exact functions to call (`collect_bv_atoms`, `Blaster::blast_atom`, `take_new_clauses`, `replay`), plus a generalize-`replay_bv_cnf` note, rather than a placeholder.

**3. Type consistency:** `Collected{selects,stores,array_eqs}`, `Abstraction{assertions,read_of,eq_proxy}`, `Lemma(Vec<LemmaLit>)`, `LemmaLit{atom,pos}`, `SatBridge::{solve,value_bv,value_bool,ensure_atom,add_lemma}`, `AbvOutcome::{Sat,Unsat,Unknown}`, `read_of_or_make -> (TermId, Option<TermId>)`, `array_model`/`render`/`ArrayModel{idx_width,elem_width,points,default}` are used identically across Tasks 3–11. Checker functions consistently take `&mut Context` (atom construction). ROW-2/extensionality lemma polarities are spelled out (`(i≠j)→X` = `[eq(i,j) pos:true, … pos:true]`; `¬p→(≠)` = `[p pos:true, eq(..) pos:false]`).

**Note on Task 10 risk:** the real-bridge wiring is the highest-uncertainty task (it touches `Encoder`/`replay_bv_cnf` internals not fully shown here). Its first deliverable is a single end-to-end UNSAT test, so the implementer gets a tight feedback loop before the oracle in Task 12.
