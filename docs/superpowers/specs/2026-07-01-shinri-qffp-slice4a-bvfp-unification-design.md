# shinri QF_FP — Slice 4a: BVFP Lowering Unification (plumbing) Design

**Date:** 2026-07-01
**Status:** Landed 2026-07-01 — plumbing merged; mixed fence still closed; 4b (crossing ops) next.
**Parent:** `2026-06-24-shinri-qffp-design.md` (Plan 4, "QF_BVFP unification")
**Predecessor:** `2026-06-30-shinri-qffp-slice3a-conversions-design.md` (slice 3a landed)

## 1. Goal & Scope

Plan 4 unifies BV and FP lowering onto **one shared `Blaster`** so a value can
cross the FP↔BV boundary as a slice of the same bit word. This slice — **4a** —
lands the *plumbing only*, with **zero new semantics**:

- Route pure-BV, pure-FP, **and** mixed BV+FP queries through **one** unified
  lowering driver backed by a **single `Blaster` + single `TermId→bits` cache**.
- **Keep the BV+FP mixed fence to `Unknown` exactly where it is today.** The
  fence *moves* into the unified driver; it does **not** lift.
- Admit **no** crossing conversion: `to_fp`-from-BV (signed int), the 1-arg
  bitcast, `to_fp_unsigned`, `fp.to_ubv`, `fp.to_sbv` continue to fence.

**Success criterion:** identical SAT/UNSAT verdicts and a fully green workspace
suite on *every existing* BV and FP corpus. 4a is a pure refactor whose
regression oracle is the current test suite.

**Out of scope (→ slice 4b, separate spec):** lifting the mixed fence and
admitting the four BV-crossing conversions one at a time, each with its own z3
differential oracle and fence-canary repoint. `fp.to_real` and symbolic-Real
`to_fp` remain permanent v1 non-goals (need an FP↔Reals combination).

## 2. Why now / why this shape

After slice 3a, every remaining Plan 3 conversion crosses the BV↔FP boundary and
is blocked on a shared `Blaster`. Today `shinri-fp`'s `FpBlaster` *wraps* a
`shinri_bv::Blaster` but keeps its **own** `cache` (the `Blaster` cache is
`pub(crate)`), and `solver::lib.rs` runs the BV and FP paths **mutually
exclusively** — any BV+FP mix returns a sound `Unknown`.

The blocking structural fact is a **dependency cycle** introduced by the crossing
ops, which 4a must resolve *without yet admitting them*:

- `fp.to_ubv` / `fp.to_sbv` are **BV-sorted** ops with an **FP argument**
  (blasting needs FP unpack, but `shinri-bv` cannot depend on `shinri-fp`).
- `to_fp` / `to_fp_unsigned` from an int and the 1-arg bitcast are **FP-sorted**
  ops with a **BV argument** (the reverse direction).

A unified pass therefore needs one `Blaster` + one shared cache **and** a
recursion that can dispatch either way across the boundary — which cannot live
purely in either crate.

**Approaches considered.**

- **(A) Extend the existing `FpBlaster`/`Blaster` relationship into the driver.**
  Reuses the struct that already wraps a `Blaster` and owns a recursion + cache.
  Smallest blast radius; `shinri-fp` already depends on `shinri-bv`. **Chosen.**
- **(B) New `shinri-lower` driver crate** depending on both, owning the driver,
  with BV/FP reduced to stateless gadget libraries. Textbook-cleaner, but the
  cleanliness is marginal here (`shinri-fp` already sits atop `shinri-bv`) and it
  moves *both* lowering entry points at once → more risk. A new crate earns its
  keep only when a *third* eager theory appears; defer that extraction.
- **(C) Full `WordBlaster` trait ecosystem** with mutual callbacks in both
  crates. Over-engineered for two theories — but it contains the one good idea:
  the cycle needs exactly **one** injection point, not a framework.

**Decision:** (A), stealing (C)'s single injection point — a minimal `WordSink`
trait — and phased so the risky refactor (4a) carries no new semantics and the
new semantics (4b) land in small, individually-verified steps.

## 3. Architecture — the seam

The mechanics are already favorable (verified against
`crates/shinri-bv/src/blast/mod.rs`):

- `Blaster::blast_word` is `pub`, recurses via `self.blast_word`, memoizes in
  `self.cache` (`pub(crate) cache: FxHashMap<TermId, Vec<BitLit>>`), and its
  fall-through arms are `unreachable!("non-BV builtin reached blast_word")` and
  `unreachable!("blast_word called on non-BV term")`. **Those two arms are the
  injection point.**
- Every BV gadget (`bitwise::bvand`, `arith::bvadd`, `div::bvudiv`,
  `structural::concat`, …) is already a free function over `&mut Blaster` +
  pre-blasted kid bits. So the BV **gadgets need no change** — only the
  dispatcher's recursion does. The FP gadgets already take `&mut self.b`
  (e.g. `minmax::fp_min(&mut self.b, &xw, &yw, eb, sb)`), the same shape.

### 3.1 The `WordSink` trait (in `shinri-bv`)

```rust
// shinri-bv — names no FP type, so no dependency cycle is created.
pub trait WordSink {
    /// Shared recursion + shared cache. Dispatches a child of ANY sort.
    fn blast_word(&mut self, ctx: &Context, t: TermId) -> Vec<BitLit>;
    /// The one gate/clause factory + var namespace.
    fn blaster(&mut self) -> &mut Blaster;
}

/// Today's `Blaster::blast_word` body, made generic over the sink.
pub fn blast_bv_word(sink: &mut impl WordSink, ctx: &Context, t: TermId) -> Vec<BitLit>;
```

`blast_bv_word` is a mechanical transform of the current dispatcher: every
`self.blast_word(kid)` → `sink.blast_word(kid)`; every `self`-as-`Blaster`
(`self.fresh()`, `self.zero()`, gadget `self` args) → `sink.blaster()`. One
file, no gadget edits.

### 3.2 The FP mirror (in `shinri-fp`)

```rust
pub fn blast_fp_word(sink: &mut impl WordSink, ctx: &Context, t: TermId) -> Vec<BitLit>;
```

The current `FpBlaster::blast_word` body, likewise generic over the sink.

### 3.3 The driver

The renamed `FpBlaster` (e.g. `Lowerer`) holds the **one** `Blaster` and is the
sole cache owner. It implements `WordSink`:

```
impl WordSink for Lowerer {
    fn blast_word(&mut self, ctx, t) -> Vec<BitLit> {
        if let Some(v) = self.cache.get(&t) { return v.clone(); }
        let bits = match sort_and_op(ctx, t) {
            BvNode => blast_bv_word(self, ctx, t),
            FpNode => blast_fp_word(self, ctx, t),
            // crossing ops: still fenced in 4a (never reached — see §4)
        };
        self.cache.insert(t, bits.clone());
        bits
    }
    fn blaster(&mut self) -> &mut Blaster { &mut self.b }
}
```

Because both `blast_bv_word` and `blast_fp_word` are generic over `WordSink` and
recurse through `sink.blast_word`, a foreign-sorted child is dispatched by the
driver to the correct side and cached in the **one** map. The cycle is broken:
`shinri-bv` names no FP type; `shinri-fp` names no driver.

### 3.4 Cache & memoization note

The shared cache is keyed by `TermId`, which is unique across the whole term DAG
regardless of sort, so BV and FP words coexist without collision. The pinned
`var0 = true` invariant and the single monotonic `next_var` counter are already
`Blaster`-owned, so one namespace spans both theories for free.

## 4. Fence & soundness (unchanged behavior)

4a **preserves** today's verdicts. The mixed fence relocates into the unified
driver but stays closed:

- Detection (`solver_uses_bv` / `solver_uses_fp`) and atom collection
  (`collect_bv_atoms` / `collect_fp_atoms`) are unchanged.
- The **mixed BV+FP** guard that currently returns `Unknown` in `lib.rs` moves to
  the unified entry, still returning `Unknown`. No mixed query is lowered in 4a.
- The existing positive-support fences (`fp_atoms_fully_supported`,
  `has_non_fp_theory_atom`, `has_non_bv_theory_atom`) stay in force, so the four
  crossing ops still fence — the driver's crossing-op match arms are therefore
  **unreachable in 4a** and encode `unreachable!`/fence, not a circuit.
- Soundness contract is inherited verbatim: anything out of scope →
  `Unknown`, never a wrong SAT/UNSAT.

## 5. `var_bits` / model read-back (the one non-mechanical spot)

Today `Blaster::exported_var_bits` filters `self.cache` for nullary
`Op::Uninterpreted` apps of **BV** sort; `FpBlaster` exports FP variable words
from its **separate** cache. After the merge there is **one** cache holding both,
so export must classify each cached variable term by sort:

- BV-sorted variable → BV width, into the BV model map.
- FP-sorted variable → `eb+sb` word, into the FP model map (unchanged
  `shinri-fp` decode).
- RoundingMode variables retain their existing handling.

`model.rs` on both sides reads from the same underlying assignment; only the
split-by-sort in the exporter is new. Pure-BV and pure-FP model round-trips must
be byte-identical to today.

## 6. Validation

- **Regression is the oracle.** Full workspace `cargo test` stays green with
  **zero** expected diffs: `shinri-bv` unit + `fp_e2e` + `fp_oracle` (feature
  gated) + all solver integration corpora. Any verdict change is a bug in 4a.
- **CNF-shape sanity (pure paths):** a pure-BV and a pure-FP `lower` produce the
  same `num_vars`/clause count as before the refactor (the transform is
  mechanical; variable *numbering* must be preserved — see risk below), asserted
  on a couple of representative atoms.
- **Fence canaries hold:** every existing mixed-BV+FP and crossing-conversion
  canary still returns `Unknown`. Per the standing cross-slice lesson, run the
  **whole** `fp_e2e` suite, not just new tests, and `grep` the solver tests for
  any canary whose out-of-scope trigger is a mixed/crossing form — expected: all
  still `Unknown` (4a admits nothing new), but verify rather than assume.
- **No new differential corpus.** 4b adds crossing forms to `fp_oracle`; 4a adds
  none.

## 7. Risks

- **Variable-numbering drift.** If the merged recursion visits terms in a
  different order than the two separate passes did, `next_var` assignments shift.
  This does not affect satisfiability, but it can perturb var-count/CNF-shape
  assertions and any test that pins concrete literals. Mitigation: preserve
  visit order (atoms in the same sequence, children left-to-right) so pure-path
  numbering is unchanged; where a shape test is genuinely order-sensitive, assert
  the invariant (SAT/UNSAT, model value) rather than the literal numbering.
- **Borrow friction at the injection point.** The driver must hand `&mut self`
  (as `impl WordSink`) to `blast_bv_word`/`blast_fp_word` while they call back
  `sink.blast_word`/`sink.blaster()`. This is well-typed with the trait (no field
  aliasing, since the cache and `Blaster` are reached through `&mut self`), but
  the FP gadgets that currently borrow `self.b` directly must route through
  `sink.blaster()` inside `blast_fp_word`.
- **Two-path lingering.** `shinri_bv::lower` and `shinri_fp::lower` should become
  thin wrappers over the unified driver (or be retired) so there is exactly one
  lowering path; leaving both live would reintroduce the sync hazard the merge
  exists to remove.

## 8. Decisions locked for slice 4a

| Decision | Choice |
|---|---|
| Slice scope | Plumbing only — one shared `Blaster` + cache; **zero new semantics** |
| Structure | (A) extend `FpBlaster`→`Lowerer` driver; **not** a new crate (B); **not** a full trait ecosystem (C) |
| Injection point | One `WordSink` trait in `shinri-bv`; `blast_bv_word`/`blast_fp_word` generic over it |
| Shared cache | The existing `Blaster.cache`, keyed by `TermId`; `FpBlaster`'s separate cache is removed |
| Mixed BV+FP | **Still fenced to `Unknown`** — fence relocates, does not lift |
| Crossing ops | **None admitted** — driver's crossing arms are `unreachable`/fence in 4a |
| `var_bits` export | Split the one cache by sort (BV width vs. FP `eb+sb`); RM vars unchanged |
| Legacy `lower` fns | Become thin wrappers over the unified driver (or retired) — no parallel path |
| Success criterion | Byte-identical verdicts + fully green existing suite; regression *is* the oracle |
| Next slice (4b) | Lift the mixed fence + admit the four crossing conversions one at a time, each with z3 oracle + canary repoint |
