# QF_FP Slice 4a — BVFP Lowering Unification (plumbing) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Merge BV and FP bit-blasting onto one shared `Blaster` + one shared `TermId→bits` cache behind a minimal `WordSink` trait, with **zero new semantics** — the mixed BV+FP fence stays closed and no crossing conversion is admitted.

**Architecture:** `shinri-bv` gains a `WordSink` trait (owns the shared recursion + `Blaster`) and free functions `blast_bv_word`/`blast_bv_atom` generic over it; `shinri-fp` mirrors with `blast_fp_word`/`blast_fp_atom`. A new unified `Lowerer` in `shinri-fp` implements `WordSink`, dispatching each node to the BV or FP side through one shared cache. Gate-generation gadgets (which already take `&mut Blaster`) are untouched.

**Tech Stack:** Rust, `rustc_hash::FxHashMap`, the existing `shinri-bv` `Blaster`/`Cnf`, `shinri-num::Integer`.

## Global Constraints

- **Zero new semantics.** Every existing verdict (SAT/UNSAT/Unknown) and the full workspace test suite must stay green with no expected diffs. Regression *is* the oracle.
- **Mixed BV+FP stays fenced to `Unknown`.** The fence relocates conceptually but does not lift. No crossing op (`to_fp`-from-BV, 1-arg bitcast, `to_fp_unsigned`, `fp.to_ubv`, `fp.to_sbv`) is admitted.
- **Preserve variable-numbering order.** The unified recursion must visit atoms in the same sequence and children left-to-right, so `Blaster::fresh()` allocation order — and thus pure-path CNF var numbering — is unchanged. Assert semantic invariants (SAT/UNSAT, model value), not literal numbers, where order could drift.
- **Single-source the gate logic.** After this slice, BV word/atom blasting lives in exactly one place (`blast_bv_word`/`blast_bv_atom`); FP likewise. No duplicated dispatch.
- Spec: `docs/superpowers/specs/2026-07-01-shinri-qffp-slice4a-bvfp-unification-design.md`.
- Node classification helpers (use these, do not add new ones): `ctx.sort_of(t) -> SortId`; `ctx.bv_width(sort) -> Option<u32>` (Some ⟺ BV-sorted); `ctx.fp_widths(sort) -> Option<(u32,u32)>` (Some ⟺ Float-sorted).

---

## File Structure

- `crates/shinri-bv/src/blast/mod.rs` — **Modify.** Add `WordSink` trait; extract the `blast_word`/`blast_atom` match bodies into generic free fns `blast_bv_word`/`blast_bv_atom`; make `Blaster` implement `WordSink` and keep its inherent methods as thin delegators (cache stays in the trait `word` method).
- `crates/shinri-fp/src/blast/mod.rs` (or `crates/shinri-fp/src/lib.rs`) — **Modify.** Extract `FpBlaster::blast_word`/`blast_atom` bodies into generic free fns `blast_fp_word`/`blast_fp_atom` over `WordSink`; keep `FpBlaster` working as a `WordSink` so existing FP unit tests are unchanged.
- `crates/shinri-fp/src/lower.rs` — **Create.** The unified `Lowerer` (one `Blaster`, one shared cache, `impl WordSink`), its sort-dispatching `word`/`atom`, split-by-sort var export, and `finish_split`. `shinri_fp::lower` is rewired to delegate here.
- `crates/shinri-fp/src/lib.rs` — **Modify.** `pub mod lower;`, re-export, rewire `shinri_fp::lower`.
- Solver (`crates/shinri-solver/src/lib.rs`, `fp_stage.rs`, `bv_stage.rs`) — **Unchanged in 4a.** The mixed fence and the two-`Option<Lowered>` wiring stay exactly as they are; only `shinri_fp::lower`'s internals change, and it keeps returning a `shinri_bv::Lowered`.

---

### Task 1: `WordSink` trait + generic BV blasting in `shinri-bv`

Extract the BV dispatch out of the inherent `Blaster` methods into free functions generic over a new `WordSink` trait, with the cache/recursion centralized in the trait's `word` method. Behavior is byte-identical; `shinri-bv`'s own tests are the regression oracle.

**Files:**
- Modify: `crates/shinri-bv/src/blast/mod.rs`
- Test: `crates/shinri-bv/src/blast/mod.rs` (existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Produces:
  - `pub trait WordSink { fn word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit>; fn blaster(&mut self) -> &mut Blaster; }`
  - `pub fn blast_bv_word<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> Vec<BitLit>`
  - `pub fn blast_bv_atom<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> BitLit`
  - `impl WordSink for Blaster` (its `word` owns the cache check/insert; `blaster` returns `self`)
  - `Blaster::blast_word`/`Blaster::blast_atom` retained as inherent delegators (`WordSink::word(self, …)` / `blast_bv_atom(self, …)`), so all existing call sites and `shinri_bv::lower` compile unchanged.

- [ ] **Step 1: Add a failing test asserting the generic path equals the inherent path**

Add to the `#[cfg(test)] mod tests` in `crates/shinri-bv/src/blast/mod.rs`:

```rust
#[test]
fn wordsink_generic_matches_inherent_bvadd() {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;
    let mut ctx = Context::new();
    let s8 = ctx.bv_sort(8);
    let xf = ctx.declare_fun("x", &[], s8);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let c = ctx.mk_bv_const(8, Integer::from(5u64));
    let add = ctx.mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, c]).unwrap();

    // Inherent method (baseline).
    let mut b1 = Blaster::new();
    let bits_inherent = b1.blast_word(&ctx, add);
    // Generic free function via the trait (Blaster as its own sink).
    let mut b2 = Blaster::new();
    let bits_generic = blast_bv_word(&mut b2, &ctx, add);

    assert_eq!(bits_inherent.len(), 8);
    assert_eq!(bits_inherent.len(), bits_generic.len());
    assert_eq!(b1.num_vars(), b2.num_vars(), "identical var allocation order");
}
```

(Adjust `ctx.bv_sort`/`ctx.mk_bv_const` to the actual constructor names already used in this test module — copy from a neighboring test such as `blast_word_bvadd_of_consts`.)

- [ ] **Step 2: Run the test — expect a compile failure**

Run: `cargo test -p shinri-bv wordsink_generic_matches_inherent_bvadd`
Expected: FAIL to compile — `blast_bv_word` and `WordSink` do not exist yet.

- [ ] **Step 3: Add the trait and extract `blast_bv_word`/`blast_bv_atom`**

In `crates/shinri-bv/src/blast/mod.rs`, above `impl Blaster`:

```rust
/// The one recursion + cache seam shared by BV and FP lowering. Implemented by
/// the concrete driver (a `Blaster` for pure-BV, or shinri-fp's `Lowerer` for
/// the unified path). `word` dispatches a child of ANY sort and memoizes it;
/// `blaster` is the single gate/clause factory + variable namespace.
pub trait WordSink {
    fn word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit>;
    fn blaster(&mut self) -> &mut Blaster;
}
```

Move the **body of the current `Blaster::blast_word` match** (the `match node { … }` expression, NOT the surrounding cache check/insert) into:

```rust
/// BV word dispatch, generic over the sink. Assumes `t` is BV-sorted; callers
/// (the sink's `word`) pre-classify by sort. Recurses via `sink.word`, mints
/// gates via `sink.blaster()`. Does NOT touch the cache — the sink's `word` owns
/// memoization.
pub fn blast_bv_word<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> Vec<BitLit> {
    let node = ctx.term_node(t).clone();
    match node {
        // ... exact current arms, transformed mechanically:
        //   self.blast_word(ctx, kid)  ->  sink.word(ctx, kid)
        //   self.zero()/one()/fresh()  ->  sink.blaster().zero()/one()/fresh()
        //   gadget(self, &a, &b)       ->  gadget(sink.blaster(), &a, &b)
        // Keep the `unreachable!` fall-through arms verbatim (defensive).
        _ => unreachable!("blast_bv_word called on non-BV term"),
    }
}
```

Apply the **same three-rule mechanical transform** to the `Blaster::blast_atom` body → `pub fn blast_bv_atom<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> BitLit`. The transform is exhaustive: there are no other forms of `self` use in those two methods besides recursion, gate minting, and gadget calls.

Then implement the trait and reduce the inherent methods to delegators:

```rust
impl WordSink for Blaster {
    fn word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        if let Some(v) = self.cache.get(&t) {
            return v.clone();
        }
        let bits = blast_bv_word(self, ctx, t);
        self.cache.insert(t, bits.clone());
        bits
    }
    fn blaster(&mut self) -> &mut Blaster { self }
}

impl Blaster {
    pub fn blast_word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        <Self as WordSink>::word(self, ctx, t)
    }
    pub fn blast_atom(&mut self, ctx: &Context, t: TermId) -> BitLit {
        blast_bv_atom(self, ctx, t)
    }
}
```

Note: `blast_bv_atom` calls `sink.word(...)` for its operands, which routes through `Blaster::word` and so is memoized exactly as before.

- [ ] **Step 4: Run the whole `shinri-bv` suite**

Run: `cargo test -p shinri-bv`
Expected: PASS — all pre-existing BV blast/lower/model tests plus the new `wordsink_generic_matches_inherent_bvadd`. Any failure means the mechanical transform altered gate/var order; diff against the original method.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-bv/src/blast/mod.rs
git commit -m "refactor(bv): extract blast_bv_word/atom behind a WordSink seam (no behavior change)"
```

---

### Task 2: Generic FP blasting over `WordSink` in `shinri-fp`

Mirror Task 1 on the FP side: extract `FpBlaster::blast_word`/`blast_atom` into `blast_fp_word`/`blast_fp_atom` generic over `WordSink`, and keep `FpBlaster` itself a `WordSink` so the existing FP unit tests remain the regression oracle.

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` (or split into `crates/shinri-fp/src/blast/mod.rs` if that module already hosts blasting — follow the existing layout; `blast_word`/`blast_atom` are currently inherent methods on `FpBlaster` in `lib.rs`)
- Test: `crates/shinri-fp/src/lib.rs` (existing `#[cfg(test)] mod lower_tests`)

**Interfaces:**
- Consumes: `shinri_bv::WordSink`, `shinri_bv::blast_bv_word` (Task 1).
- Produces:
  - `pub fn blast_fp_word<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> Vec<BitLit>`
  - `pub fn blast_fp_atom<S: WordSink>(sink: &mut S, ctx: &Context, t: TermId) -> BitLit`
  - `impl WordSink for FpBlaster` (its `word` owns FP cache check/insert + RM handling stays as-is; `blaster` returns `&mut self.b`), inherent `FpBlaster::blast_word`/`blast_atom` retained as delegators.

- [ ] **Step 1: Add a failing test asserting generic FP path equals inherent**

Add to `#[cfg(test)] mod lower_tests` in `crates/shinri-fp/src/lib.rs`:

```rust
#[test]
fn wordsink_generic_matches_inherent_fp_isnan() {
    use shinri_core::{BuiltinOp, Op};
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();

    let mut fb1 = FpBlaster::new();
    let w_inherent = fb1.blast_word(&ctx, x);
    let mut fb2 = FpBlaster::new();
    let w_generic = shinri_fp::blast_fp_word(&mut fb2, &ctx, x);

    assert_eq!(w_inherent.len(), 32);
    assert_eq!(w_inherent.len(), w_generic.len());
    assert_eq!(fb1.b.num_vars(), fb2.b.num_vars(), "identical var allocation order");
}
```

(If the test module can't name the crate as `shinri_fp`, call the free fn as `super::blast_fp_word` / `crate::blast_fp_word` to match the module path.)

- [ ] **Step 2: Run the test — expect a compile failure**

Run: `cargo test -p shinri-fp wordsink_generic_matches_inherent_fp_isnan`
Expected: FAIL to compile — `blast_fp_word` does not exist yet.

- [ ] **Step 3: Extract `blast_fp_word`/`blast_fp_atom` and impl the trait**

Apply the same mechanical transform as Task 1 to the `FpBlaster::blast_word` and `FpBlaster::blast_atom` bodies:
- `self.blast_word(ctx, kid)` → `sink.word(ctx, kid)`
- `&mut self.b` (gadget/RM arg) → `sink.blaster()`
- `self.blast_rm(ctx, kid)` → keep RM handling inside `blast_fp_word` but source its bits via `sink.blaster()` (the RM cache moves onto the sink — see note below).

For the **word cache and RM cache**: today `FpBlaster` holds `cache`, `var_bits`, `rm_cache`. Centralize memoization in `impl WordSink for FpBlaster::word` (mirror of Task 1). Keep `rm_cache`/`var_bits` as `FpBlaster` fields for now; `blast_fp_word` reads/writes them via a small accessor on the sink is NOT required in this task — instead, keep `blast_rm` as a free fn `blast_rm<S: WordSink>(sink, ctx, t, rm_cache: &mut FxHashMap<TermId,[BitLit;5]>)` OR, simplest, leave RM caching inside `FpBlaster` and have `blast_fp_word` take the RM selector by calling a sink method. To keep this task mechanical and low-risk, **leave `blast_rm` as an inherent `FpBlaster` helper and pass the already-computed RM selector into the shared gadget calls**; the generic `blast_fp_word` receives `sink` and, for RM operands, calls `sink.blaster()` to mint symbolic RM bits, replicating `rm::literal`/`rm::symbolic` without a per-sink RM cache (RM operands are shallow; dropping the cache changes only var *count* on repeated symbolic-RM reuse — assert semantic invariants, not counts).

```rust
impl WordSink for FpBlaster {
    fn word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        if let Some(v) = self.cache.get(&t) { return v.clone(); }
        let bits = blast_fp_word(self, ctx, t);
        self.cache.insert(t, bits.clone());
        bits
    }
    fn blaster(&mut self) -> &mut Blaster { &mut self.b }
}
```

Retain inherent `FpBlaster::blast_word`/`blast_atom` as delegators (`<Self as WordSink>::word(self,…)` / `blast_fp_atom(self,…)`).

> If preserving the RM cache without churn proves cleaner, thread it through `WordSink` via a second method `fn rm_cache(&mut self) -> &mut FxHashMap<TermId,[BitLit;5]>`. Choose whichever keeps `cargo test -p shinri-fp` green with the fewest edits; both are acceptable since RM caching affects var count, not correctness.

- [ ] **Step 4: Run the whole `shinri-fp` suite**

Run: `cargo test -p shinri-fp`
Expected: PASS — all pre-existing FP tests plus the new equality test. A failure in a test that pins concrete literal indices (rather than values) indicates RM-cache-driven var renumbering; relax that test to assert the FP value, per Global Constraints.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/lib.rs
git commit -m "refactor(fp): extract blast_fp_word/atom over the WordSink seam (no behavior change)"
```

---

### Task 3: The unified `Lowerer` — one Blaster, one cache spanning both theories

Create the driver that dispatches BV and FP nodes through a single shared cache, exports variable bits split by sort, and proves the cross-theory capability with a directly-constructed mixed atom list (the solver still fences such queries — this is a unit test of the machinery 4b will unlock).

**Files:**
- Create: `crates/shinri-fp/src/lower.rs`
- Modify: `crates/shinri-fp/src/lib.rs` (add `pub mod lower;`)
- Test: `crates/shinri-fp/src/lower.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `shinri_bv::{WordSink, Blaster, BitLit, Cnf, blast_bv_word, blast_bv_atom}`; `crate::{blast_fp_word, blast_fp_atom}`.
- Produces:
  - `pub struct Lowerer { pub b: Blaster, cache: FxHashMap<TermId, Vec<BitLit>> }`
  - `impl WordSink for Lowerer` (`word` = cache-check → sort-dispatch → cache-insert; `blaster` = `&mut self.b`)
  - `impl Lowerer { pub fn new() -> Self; pub fn atom(&mut self, ctx, t) -> BitLit; pub fn var_bits_split(&self, ctx) -> (FxHashMap<TermId,Vec<BitLit>>, FxHashMap<TermId,Vec<BitLit>>) }` returning `(bv_var_bits, fp_var_bits)`.

- [ ] **Step 1: Write the failing cross-theory test**

Create `crates/shinri-fp/src/lower.rs` with:

```rust
//! Unified BV+FP lowering driver: one Blaster, one shared cache, dispatched by
//! sort. See docs/superpowers/specs/2026-07-01-shinri-qffp-slice4a-bvfp-unification-design.md.

use rustc_hash::FxHashMap;
use shinri_bv::{blast_bv_atom, blast_bv_word, BitLit, Blaster, WordSink};
use shinri_core::{Context, Op, TermId, TermNode};

pub struct Lowerer {
    pub b: Blaster,
    cache: FxHashMap<TermId, Vec<BitLit>>,
}

impl Lowerer {
    pub fn new() -> Self { Lowerer { b: Blaster::new(), cache: FxHashMap::default() } }
    // atom() and var_bits_split() added in Step 3.
}

impl Default for Lowerer { fn default() -> Self { Self::new() } }

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::BuiltinOp;

    #[test]
    fn mixed_bv_and_fp_atoms_share_one_cache_and_split_vars() {
        // A BV atom and an FP atom in ONE lowering pass. The solver fences such
        // mixed queries in 4a; this exercises the driver machinery directly.
        let mut ctx = Context::new();
        // BV side: (= x #x05) over an 8-bit var.
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let five = ctx.mk_bv_const(8, shinri_num::Integer::from(5u64));
        let bv_eq = ctx.mk_eq(x, five).unwrap();
        // FP side: (fp.isNaN y) over a Float32 var.
        let f32 = ctx.fp_sort(8, 24);
        let yf = ctx.declare_fun("y", &[], f32);
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[y]).unwrap();

        let mut lw = Lowerer::new();
        let _l_bv = lw.atom(&ctx, bv_eq);
        let _l_fp = lw.atom(&ctx, isnan);

        let (bv_vars, fp_vars) = lw.var_bits_split(&ctx);
        assert!(bv_vars.contains_key(&x) && bv_vars[&x].len() == 8, "x is an 8-bit BV var");
        assert!(fp_vars.contains_key(&y) && fp_vars[&y].len() == 32, "y is a 32-bit FP var");
        assert!(!bv_vars.contains_key(&y) && !fp_vars.contains_key(&x), "no sort cross-contamination");
    }
}
```

- [ ] **Step 2: Run the test — expect a compile failure**

Run: `cargo test -p shinri-fp mixed_bv_and_fp_atoms_share_one_cache`
Expected: FAIL to compile — `Lowerer::atom`/`var_bits_split` not defined; `pub mod lower;` not yet added.

- [ ] **Step 3: Implement the dispatcher, atom entry, and split export**

Add `pub mod lower;` to `crates/shinri-fp/src/lib.rs`. Then in `lower.rs`:

```rust
impl WordSink for Lowerer {
    fn word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit> {
        if let Some(v) = self.cache.get(&t) { return v.clone(); }
        let sort = ctx.sort_of(t);
        let bits = if ctx.bv_width(sort).is_some() {
            // BV-sorted node. (A BV-sorted FP op — fp.to_ubv/to_sbv — is a
            // crossing op fenced in 4a, so blast_bv_word's unreachable! arm is
            // not hit; 4b adds a crossing check before this dispatch.)
            blast_bv_word(self, ctx, t)
        } else if ctx.fp_widths(sort).is_some() {
            // FP-sorted node (incl. future to_fp-from-BV, fenced in 4a).
            crate::blast_fp_word(self, ctx, t)
        } else {
            unreachable!("Lowerer::word on non-BV/non-FP sort {sort:?}");
        };
        self.cache.insert(t, bits.clone());
        bits
    }
    fn blaster(&mut self) -> &mut Blaster { &mut self.b }
}

impl Lowerer {
    /// Blast a Bool-sorted atom (BV or FP predicate / (dis)equality) to a literal.
    pub fn atom(&mut self, ctx: &Context, t: TermId) -> BitLit {
        // Dispatch by the sort of the atom's first operand.
        let first_operand_sort = match ctx.term_node(t) {
            TermNode::App { args, .. } => {
                let kids = ctx.children(*args);
                ctx.sort_of(kids[0])
            }
            _ => unreachable!("atom must be an application"),
        };
        if ctx.bv_width(first_operand_sort).is_some() {
            blast_bv_atom(self, ctx, t)
        } else {
            crate::blast_fp_atom(self, ctx, t)
        }
    }

    /// Split the shared cache's variable words by sort for model read-back.
    /// Returns (bv_var_bits, fp_var_bits). A variable term is a nullary
    /// `Op::Uninterpreted` app; its sort decides the map.
    pub fn var_bits_split(
        &self,
        ctx: &Context,
    ) -> (FxHashMap<TermId, Vec<BitLit>>, FxHashMap<TermId, Vec<BitLit>>) {
        let mut bv = FxHashMap::default();
        let mut fp = FxHashMap::default();
        for (&tid, bits) in self.cache.iter() {
            if let TermNode::App { op: Op::Uninterpreted(_), args, sort } = ctx.term_node(tid) {
                if !ctx.children(*args).is_empty() { continue; }
                if ctx.bv_width(*sort).is_some() {
                    bv.insert(tid, bits.clone());
                } else if ctx.fp_widths(*sort).is_some() {
                    fp.insert(tid, bits.clone());
                }
            }
        }
        (bv, fp)
    }
}
```

- [ ] **Step 4: Run the test**

Run: `cargo test -p shinri-fp mixed_bv_and_fp_atoms_share_one_cache`
Expected: PASS — one `Lowerer` blasts a BV atom and an FP atom into one CNF, and `var_bits_split` routes `x`→BV, `y`→FP with no cross-contamination.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/lower.rs crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): unified Lowerer — one Blaster/cache across BV+FP, split var export"
```

---

### Task 4: Rewire `shinri_fp::lower` through the `Lowerer` (pure-FP path unchanged)

Replace `shinri_fp::lower`'s internal `FpBlaster` with the unified `Lowerer` so the solver's pure-FP path now runs through the merged driver — with byte-identical results (a pure-FP atom list has no BV subterms, so only the FP dispatch fires and only FP vars are exported).

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` (the `pub fn lower` body)
- Test: existing `crates/shinri-fp/src/lib.rs` `lower_tests` + `crates/shinri-solver/tests/fp_e2e.rs`

**Interfaces:**
- Consumes: `crate::lower::Lowerer` (Task 3).
- Produces: `pub fn lower(ctx: &mut Context, fp_atoms: &[TermId]) -> shinri_bv::Lowered` — unchanged signature; internals now use `Lowerer`.

- [ ] **Step 1: Confirm the existing `lower_tests` are the regression oracle**

Run: `cargo test -p shinri-fp lower_tests`
Expected: PASS (baseline before the rewire). These tests (`lower_isnan_atom_keys_and_vars`, `lower_core_eq_over_floats_is_an_atom`, `lower_fp_add_eq_atom`, `lower_fp_mul_eq_atom`) assert atom keying and FP var export — exactly what must stay invariant.

- [ ] **Step 2: Rewire `shinri_fp::lower`**

Replace the body of `pub fn lower` in `crates/shinri-fp/src/lib.rs`:

```rust
pub fn lower(ctx: &mut Context, fp_atoms: &[TermId]) -> shinri_bv::Lowered {
    let mut lw = crate::lower::Lowerer::new();
    let mut atom_lit: FxHashMap<TermId, BitLit> = FxHashMap::default();
    for &atom in fp_atoms {
        let lit = lw.atom(ctx, atom);
        atom_lit.insert(atom, lit);
    }
    // Pure-FP list: bv side is empty; take the FP map into Lowered.var_bits.
    let (_bv_vars, fp_vars) = lw.var_bits_split(ctx);
    debug_assert!(_bv_vars.is_empty(), "pure-FP lower produced no BV vars");
    shinri_bv::Lowered { cnf: lw.b.finish(), atom_lit, var_bits: fp_vars }
}
```

- [ ] **Step 3: Run FP unit + solver end-to-end suites**

Run: `cargo test -p shinri-fp lower_tests`
Expected: PASS — unchanged.

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS — every FP SAT/UNSAT/get-model script and every fence canary unchanged.

- [ ] **Step 4: Run the differential oracle (if `z3` is on PATH)**

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle`
Expected: PASS — no verdict disagreements vs z3. (If `z3` is not installed, note it and skip; do not treat absence as failure.)

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/lib.rs
git commit -m "refactor(fp): route shinri_fp::lower through the unified Lowerer (pure-FP unchanged)"
```

---

### Task 5: Full-workspace regression + fence-canary verification + docs

Prove zero behavior change across the whole repo, re-verify the mixed/crossing fences per the standing cross-slice-canary lesson, and mark slice-4a plumbing landed.

**Files:**
- Modify: `docs/superpowers/specs/2026-07-01-shinri-qffp-slice4a-bvfp-unification-design.md` (status line)
- No source changes expected; if the regression surfaces a drift, fix it in the owning task's file and re-run.

**Interfaces:** none.

- [ ] **Step 1: Full workspace test**

Run: `cargo test --workspace`
Expected: PASS — the entire suite green. This is the primary success criterion (Global Constraints: zero new semantics). Investigate ANY diff; a changed verdict is a 4a bug.

- [ ] **Step 2: Lint stays clean**

Run: `cargo clippy --workspace --all-targets -- -D warnings`
Expected: no new warnings (project runs zero-net-new-clippy — matches recent commit discipline).

- [ ] **Step 3: Re-verify the fence held — mixed + crossing still `Unknown`**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS.

Then audit that no canary silently flipped decidable (per the cross-slice lesson — a self-contained refactor looks clean while a *prior* slice's canary breaks):

Run: `grep -n "to_fp\|ToFp\|to_ubv\|ToUbv\|to_sbv\|ToSbv\|to_real\|ToReal" crates/shinri-solver/tests/fp_e2e.rs`
Expected: every hit is still inside an `Unknown`-asserting canary. 4a admits no new op, so all must remain `Unknown`. If any now returns SAT/UNSAT, that is a fence regression — stop and fix the dispatch before proceeding.

- [ ] **Step 4: Mark the slice landed**

Edit the spec's status line in `docs/superpowers/specs/2026-07-01-shinri-qffp-slice4a-bvfp-unification-design.md`:

```markdown
**Status:** Landed 2026-07-01 — plumbing merged; mixed fence still closed; 4b (crossing ops) next.
```

- [ ] **Step 5: Commit**

```bash
git add docs/superpowers/specs/2026-07-01-shinri-qffp-slice4a-bvfp-unification-design.md
git commit -m "docs(qffp): mark slice-4a landed — BVFP lowering unified behind WordSink"
```

---

## Self-Review

**Spec coverage:**
- Spec §3.1 `WordSink` trait in `shinri-bv` → Task 1. §3.2 `blast_fp_word` → Task 2. §3.3 unified `Lowerer` dispatcher → Task 3. §3.4 one `TermId`-keyed cache → Task 3 (`Lowerer.cache`).
- Spec §4 fence unchanged / crossing arms unreachable → Task 3 (dispatch comments + `unreachable!`), Task 5 Step 3 (canary audit).
- Spec §5 `var_bits` split-by-sort → Task 3 `var_bits_split`, consumed in Task 4.
- Spec §6 validation (regression oracle, CNF-shape sanity, canaries, no new differential corpus) → Task 1/2 equality tests, Task 4 fp_e2e/oracle, Task 5 workspace + canary grep.
- Spec §7 risks: variable-numbering drift → Global Constraints + `num_vars` assertions in Tasks 1–2 and value-not-index guidance; borrow friction → resolved by the `&mut self` trait shape; two-path lingering → single-sourced gate logic (`blast_bv_word`/`blast_fp_word`), Task 4 routes the solver's FP path through the one driver.
- Spec §8 decisions: (A) not a new crate — driver lives in `shinri-fp` (Task 3); no crossing op admitted (Task 3 comments, Task 5 audit); RM handling preserved (Task 2 note).

**Placeholder scan:** The large BV/FP match bodies in Tasks 1–2 are specified by an exhaustive three-rule mechanical transform plus retained `unreachable!` arms — a complete instruction, not a "TODO". The RM-cache handling in Task 2 offers two concrete acceptable implementations with a green-suite decision rule (not an open question). No "TBD"/"handle edge cases"/bare "write tests" remain.

**Type consistency:** `WordSink::word`/`blaster` names are used identically across Tasks 1–4. `blast_bv_word`/`blast_bv_atom`/`blast_fp_word`/`blast_fp_atom` signatures match between producer and consumer tasks. `Lowerer::{new, atom, var_bits_split, b}` as defined in Task 3 are exactly what Task 4 calls. `var_bits_split` returns `(bv, fp)` and Task 4 consumes the second element for the pure-FP `Lowered.var_bits`. `shinri_bv::Lowered { cnf, atom_lit, var_bits }` field names match the struct in `crates/shinri-bv/src/lib.rs`.
