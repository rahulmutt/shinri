# QF_FP Slice 4b — Mixed BV+FP Fence-Lift Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Lift the mixed BV+FP fence so a query whose atoms are pure-BV and/or pure-FP (no BV↔FP crossing conversion) is lowered as one problem through the 4a `Lowerer` and returns a real SAT/UNSAT verdict instead of `Unknown`.

**Architecture:** The solver's two mutually-exclusive `Option<Lowered>` blocks are restructured: pure-BV keeps its own untouched `shinri_bv::lower` path; every FP-involving query (pure-FP or mixed) lowers the union `fp_atoms ∪ bv_atoms` through the one 4a `Lowerer`. A new `uses_crossing_conversion` predicate is the single authoritative gate that keeps the four crossing conversions (and the Real bridge) fenced to `Unknown` before lowering. Model read-back splits the one mixed `Lowered.var_bits` by sort into the solver's existing BV and FP decode maps. **Zero new blasting gadgets.**

**Tech Stack:** Rust; crates `shinri-solver` (dispatch + fences), `shinri-fp` (unified `Lowerer` + lowering entries), `shinri-bv` (BV blaster, reused). z3 4.16.0 on PATH for the differential oracle.

## Global Constraints

- **Zero new semantics beyond the fence-lift.** No int↔float gadget, no conversion op admitted. The four crossing conversions (1-arg BV bitcast `to_fp`, signed-BV→FP `to_fp`, `to_fp_unsigned`, `fp.to_ubv`/`fp.to_sbv`), `FpFromBits`, `fp.to_real`, and symbolic-Real `to_fp` MUST still return `Unknown`.
- **Pure-BV and pure-FP verdicts byte-identical.** Pure-BV keeps `shinri_bv::lower` untouched. Pure-FP is `lower_mixed(fp_atoms, &[])` — the empty BV set makes it identical to today. Preserve visit order (BV atoms then FP atoms, children left-to-right) so pure-path variable numbering is unchanged.
- **Soundness is never traded for a verdict.** Over-fencing to `Unknown` is always acceptable; a wrong SAT/UNSAT is never. The crossing gate and the third-theory fence run BEFORE any lowering, so `blast_bv_word`/`blast_fp_word`'s crossing `unreachable!` arms stay internal invariants.
- **Test-run discipline (carry-forward `[[shinri-long-tests-run-yourself]]`):** implementers run ONLY name-filtered tests. NEVER run unfiltered `cargo test -p shinri-fp --lib` (it pulls the ~15-min exhaustive gate). The controller owns the full-workspace regression, the exhaustive gate, and the z3 oracle runs.
- **z3 on PATH** for the `--features oracle` differential tests.

---

### Task 1: `uses_crossing_conversion` — the authoritative crossing gate

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs` (add a `pub fn` after `solver_uses_fp`, ~line 48; add a test in the `tests` module)

**Interfaces:**
- Consumes: `Context::{term_node, children, sort_node, sort_of, const_real_value}`; `BuiltinOp::{FpFromBits, FpToUbv, FpToSbv, ToFpUnsigned, FpToReal, ToFp}`; `SortNode::{BitVec, Real}`.
- Produces: `pub fn uses_crossing_conversion(ctx: &Context, assertions: &[TermId]) -> bool` — true iff any subterm is a BV↔FP crossing conversion (or the Real bridge). This is the single list later slices edit as each conversion is admitted.

- [ ] **Step 1: Write the failing test**

Add to the `#[cfg(test)] mod tests` block in `crates/shinri-solver/src/fp_stage.rs`:

```rust
#[test]
fn crossing_conversions_detected_supported_faces_not() {
    use shinri_num::Rational;
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let bvs = ctx.bv_sort(32);
    let bvf = ctx.declare_fun("bv", &[], bvs);
    let bv = ctx.mk_app(Op::Uninterpreted(bvf), &[]).unwrap();

    // fp.to_sbv (FP→BV) → crossing.
    let sbv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToSbv(32)), &[rne, x]).unwrap();
    assert!(uses_crossing_conversion(&ctx, &[sbv]), "fp.to_sbv is crossing");
    // to_fp from BV (2-arg, BV source) → crossing.
    let from_bv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
    assert!(uses_crossing_conversion(&ctx, &[from_bv]), "to_fp from BV is crossing");
    // 1-arg BV bitcast to_fp (width 32 == eb+sb) → crossing.
    let bitcast = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[bv]).unwrap();
    assert!(uses_crossing_conversion(&ctx, &[bitcast]), "1-arg bitcast to_fp is crossing");
    // to_fp_unsigned → crossing.
    let uns = ctx.mk_app(Op::Builtin(BuiltinOp::ToFpUnsigned { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
    assert!(uses_crossing_conversion(&ctx, &[uns]), "to_fp_unsigned is crossing");

    // to_fp FP→FP (3a-supported) → NOT crossing.
    let widen = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 11, sb: 53 }), &[rne, x]).unwrap();
    assert!(!uses_crossing_conversion(&ctx, &[widen]), "FP->FP to_fp is not crossing");
    // to_fp const-Real (3a-supported) → NOT crossing.
    let real = ctx.real_sort();
    let third = ctx.mk_numeral(Rational::new(1i128.into(), 3i128.into()), real);
    let creal = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, third]).unwrap();
    assert!(!uses_crossing_conversion(&ctx, &[creal]), "const-Real to_fp is not crossing");
    // symbolic-Real to_fp → crossing (durably fenced).
    let rf = ctx.declare_fun("r", &[], real);
    let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
    let sreal = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, r]).unwrap();
    assert!(uses_crossing_conversion(&ctx, &[sreal]), "symbolic-Real to_fp is crossing");
    // pure FP predicate → NOT crossing.
    let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
    assert!(!uses_crossing_conversion(&ctx, &[isnan]), "pure FP is not crossing");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver --lib crossing_conversions_detected`
Expected: FAIL to COMPILE — `uses_crossing_conversion` not found.

- [ ] **Step 3: Write the implementation**

Insert after `solver_uses_fp` (after line 48) in `crates/shinri-solver/src/fp_stage.rs`:

```rust
/// True if any subterm is a BV↔FP CROSSING conversion (or the Real bridge) —
/// the ops slice 4b does NOT yet admit. These must fence to `Unknown` BEFORE
/// lowering so `blast_bv_word`/`blast_fp_word`'s crossing `unreachable!` arms
/// stay internal invariants. This is the single authoritative crossing-op list:
/// later slices delete an entry here as each conversion is admitted.
///
/// Crossing set:
/// - `FpFromBits`, `FpToUbv`, `FpToSbv`, `ToFpUnsigned` — always crossing.
/// - `FpToReal` — the permanent Real bridge (v1 non-goal).
/// - `ToFp` — crossing ONLY in its 1-arg BV bitcast, signed-BV-source, or
///   symbolic-Real faces. The 3a-supported FP→FP and constant-Real faces are
///   NOT crossing (a Float-sorted operand, or a Real operand with a known
///   `const_real_value`).
pub fn uses_crossing_conversion(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) {
            return false;
        }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            let is_crossing = match op {
                Op::Builtin(BuiltinOp::FpFromBits)
                | Op::Builtin(BuiltinOp::FpToUbv(_))
                | Op::Builtin(BuiltinOp::FpToSbv(_))
                | Op::Builtin(BuiltinOp::ToFpUnsigned { .. })
                | Op::Builtin(BuiltinOp::FpToReal) => true,
                Op::Builtin(BuiltinOp::ToFp { .. }) => match kids.len() {
                    1 => true, // 1-arg BV bitcast
                    2 => match ctx.sort_node(ctx.sort_of(kids[1])) {
                        SortNode::BitVec(_) => true, // signed-BV → FP
                        // symbolic Real is crossing; a constant Real is 3a-supported.
                        SortNode::Real => ctx.const_real_value(kids[1]).is_none(),
                        _ => false, // Float → FP (3a-supported)
                    },
                    _ => true, // defensive: unexpected arity
                },
                _ => false,
            };
            if is_crossing {
                return true;
            }
            return kids.into_iter().any(|c| walk(ctx, c, seen));
        }
        false
    }
    assertions.iter().any(|&a| walk(ctx, a, &mut seen))
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-solver --lib crossing_conversions_detected`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(fp): uses_crossing_conversion — authoritative BV↔FP crossing gate (slice 4b)"
```

---

### Task 2: `has_non_bvfp_theory_atom` — third-theory fence over the BV∪FP union

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs` (add a `pub fn` after `has_non_fp_theory_atom`, ~line 107; add a test)

**Interfaces:**
- Consumes: the existing `has_non_fp_theory_atom(ctx, assertions, atom_set)` (its body already fences any Bool atom outside the given set that is not pure Boolean structure).
- Produces: `pub fn has_non_bvfp_theory_atom(ctx: &Context, assertions: &[TermId], fp_atoms: &[TermId], bv_atoms: &[TermId]) -> bool` — true iff a Bool atom is neither a collected BV atom nor a collected FP atom nor Boolean structure (arrays/LIA/EUF present ⇒ fence).

- [ ] **Step 1: Write the failing test**

Add to the `tests` module in `crates/shinri-solver/src/fp_stage.rs`:

```rust
#[test]
fn bvfp_union_passes_but_third_theory_fences() {
    let mut ctx = Context::new();
    // FP atom.
    let x = fp_var(&mut ctx, "x");
    let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
    // BV atom.
    let bvs = ctx.bv_sort(8);
    let bf = ctx.declare_fun("b", &[], bvs);
    let bvar = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
    let one = ctx.mk_bv_const(8, Integer::from(1u64));
    let ult = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[bvar, one]).unwrap();

    let fp_atoms = collect_fp_atoms(&ctx, &[isnan, ult]);
    let bv_atoms = crate::bv_stage::collect_bv_atoms(&ctx, &[isnan, ult]);
    // Mixed BV+FP (no crossing op) is NOT fenced by the union predicate.
    assert!(!has_non_bvfp_theory_atom(&ctx, &[isnan, ult], &fp_atoms, &bv_atoms),
            "pure-BV + pure-FP atoms are allowed together");

    // Add a Real (arith) atom → fenced.
    let real = ctx.real_sort();
    let rf = ctx.declare_fun("r", &[], real);
    let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
    let zero = ctx.mk_numeral(shinri_core::Rational::zero(), real);
    let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[r, zero]).unwrap();
    let asserts = vec![isnan, ult, gt];
    let fp2 = collect_fp_atoms(&ctx, &asserts);
    let bv2 = crate::bv_stage::collect_bv_atoms(&ctx, &asserts);
    assert!(has_non_bvfp_theory_atom(&ctx, &asserts, &fp2, &bv2),
            "a Real arith atom alongside BV+FP must fence");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver --lib bvfp_union_passes`
Expected: FAIL to COMPILE — `has_non_bvfp_theory_atom` not found.

- [ ] **Step 3: Write the implementation**

Insert after `has_non_fp_theory_atom` (after line 107) in `crates/shinri-solver/src/fp_stage.rs`:

```rust
/// Third-theory fence for the lifted mixed BV+FP path (slice 4b). Returns true
/// if any Bool-sorted atom is NEITHER a collected FP atom NOR a collected BV
/// atom NOR pure Boolean structure (i.e. an arrays/LIA/EUF atom) — such a query
/// still fences to `Unknown`. Generalizes `has_non_fp_theory_atom` from the FP
/// set to the BV∪FP allow-set by delegating to it with the union.
pub fn has_non_bvfp_theory_atom(
    ctx: &Context,
    assertions: &[TermId],
    fp_atoms: &[TermId],
    bv_atoms: &[TermId],
) -> bool {
    let mut union: Vec<TermId> = Vec::with_capacity(fp_atoms.len() + bv_atoms.len());
    union.extend_from_slice(fp_atoms);
    union.extend_from_slice(bv_atoms);
    has_non_fp_theory_atom(ctx, assertions, &union)
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-solver --lib bvfp_union_passes`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(fp): has_non_bvfp_theory_atom — third-theory fence over BV∪FP union (slice 4b)"
```

---

### Task 3: `shinri_fp::lower_mixed` — one Lowerer over `fp_atoms ∪ bv_atoms`

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` (replace the `lower` fn at lines 275-289; add a test in `lower_tests`)

**Interfaces:**
- Consumes: `crate::lower::Lowerer::{new, atom, var_bits_split, b}`; `shinri_bv::{rewrite, Lowered, BitLit}`; `Blaster::finish` (via `lw.b.finish()`).
- Produces:
  - `pub fn lower_mixed(ctx: &mut Context, fp_atoms: &[TermId], bv_atoms: &[TermId]) -> shinri_bv::Lowered` — blasts BV atoms (rewritten first) and FP atoms (not rewritten) through one `Lowerer`; `var_bits` holds BOTH theories' variable words; `atom_lit` keyed by each ORIGINAL atom id.
  - `pub fn lower(ctx: &mut Context, fp_atoms: &[TermId]) -> shinri_bv::Lowered` — now a thin wrapper `lower_mixed(ctx, fp_atoms, &[])`.

- [ ] **Step 1: Write the failing test**

Add to the `#[cfg(test)] mod lower_tests` block in `crates/shinri-fp/src/lib.rs`:

```rust
#[test]
fn lower_mixed_blasts_bv_and_fp_and_unions_vars() {
    let mut ctx = Context::new();
    // BV atom: (= x #x05) over an 8-bit var.
    let s8 = ctx.bv_sort(8);
    let xf = ctx.declare_fun("x", &[], s8);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let five = ctx.mk_bv_const(8, Integer::from(5u64));
    let bv_eq = ctx.mk_eq(x, five).unwrap();
    // FP atom: (fp.isNaN y) over a Float32 var.
    let f32 = ctx.fp_sort(8, 24);
    let yf = ctx.declare_fun("y", &[], f32);
    let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
    let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[y]).unwrap();

    let l = lower_mixed(&mut ctx, &[isnan], &[bv_eq]);
    // Both atoms are surrogated.
    assert!(l.atom_lit.contains_key(&bv_eq), "BV atom surrogated");
    assert!(l.atom_lit.contains_key(&isnan), "FP atom surrogated");
    // var_bits holds BOTH the 8-bit BV var and the 32-bit FP var.
    assert!(l.var_bits.contains_key(&x) && l.var_bits[&x].len() == 8, "BV var word present");
    assert!(l.var_bits.contains_key(&y) && l.var_bits[&y].len() == 32, "FP var word present");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp --lib lower_mixed_blasts_bv_and_fp`
Expected: FAIL to COMPILE — `lower_mixed` not found.
(Name-filtered: does NOT pull the exhaustive gate.)

- [ ] **Step 3: Write the implementation**

Replace the `lower` function (lines 275-289) in `crates/shinri-fp/src/lib.rs` with:

```rust
/// Blast FP atoms AND BV atoms through ONE unified `Lowerer` (shared `Blaster`
/// + cache) and return a `shinri_bv::Lowered` (reused so the solver's
/// `replay_bv_cnf` applies unchanged). `var_bits` carries BOTH theories'
/// variable words — the solver splits them by sort for model read-back. BV
/// atoms are rewritten first (matching `shinri_bv::lower`); FP atoms are not
/// (matching the pre-4b `shinri_fp::lower`). `atom_lit` is keyed by each
/// ORIGINAL atom TermId. Without a crossing conversion the BV and FP DAGs are
/// disjoint, so this is two independent blasting problems over one namespace.
pub fn lower_mixed(
    ctx: &mut Context,
    fp_atoms: &[TermId],
    bv_atoms: &[TermId],
) -> shinri_bv::Lowered {
    let mut lw = crate::lower::Lowerer::new();
    let mut atom_lit: FxHashMap<TermId, BitLit> = FxHashMap::default();
    // BV atoms FIRST (rewritten, as the pure-BV path does), keyed by ORIGINAL id.
    for &original in bv_atoms {
        let rewritten = shinri_bv::rewrite(ctx, original);
        let lit = lw.atom(ctx, rewritten);
        atom_lit.insert(original, lit);
    }
    // FP atoms next (no rewrite, as the pure-FP path does).
    for &atom in fp_atoms {
        let lit = lw.atom(ctx, atom);
        atom_lit.insert(atom, lit);
    }
    // One shared cache: union both sort-split var maps into Lowered.var_bits.
    let (bv_vars, fp_vars) = lw.var_bits_split(ctx);
    let mut var_bits = bv_vars;
    var_bits.extend(fp_vars);
    shinri_bv::Lowered { cnf: lw.b.finish(), atom_lit, var_bits }
}

/// Pure-FP lowering: `lower_mixed` with no BV atoms. Byte-identical to the
/// pre-4b pure-FP path — the BV set is empty, so `var_bits` is FP-only and the
/// blast order (FP atoms, in order) is unchanged.
pub fn lower(ctx: &mut Context, fp_atoms: &[TermId]) -> shinri_bv::Lowered {
    lower_mixed(ctx, fp_atoms, &[])
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp --lib lower_mixed_blasts_bv_and_fp`
Expected: PASS.

Run the existing pure-FP lowering tests to confirm byte-identical behavior (name-filtered — the `lower_tests` module is fast, no exhaustive gate):
Run: `cargo test -p shinri-fp --lib lower_tests`
Expected: PASS (all pre-existing pure-FP `lower_tests` still green).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): lower_mixed — one Lowerer over fp_atoms ∪ bv_atoms; lower() delegates (slice 4b)"
```

---

### Task 4: Rewire the solver dispatch + mixed e2e proof

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs:344-400` (the BV/FP dispatch blocks) and `:435-446` (the FP-path var_bits registration)
- Test: `crates/shinri-solver/tests/fp_e2e.rs` (add mixed positive tests; the existing crossing canary stays)

**Interfaces:**
- Consumes: `crate::fp_stage::{solver_uses_fp, collect_fp_atoms, uses_crossing_conversion, has_non_bvfp_theory_atom, fp_atoms_fully_supported}`; `crate::bv_stage::{solver_uses_bv, collect_bv_atoms, has_non_bv_theory_atom}`; `shinri_bv::lower`; `shinri_fp::lower_mixed`; `Context::{bv_width, sort_of}`.
- Produces: mixed non-crossing BV+FP queries now return Sat/Unsat with a model spanning both theories; crossing queries still `Unknown`.

- [ ] **Step 1: Write the failing tests**

Add to `crates/shinri-solver/tests/fp_e2e.rs` (the `run(src) -> (SolveOutcome, String)` helper already exists at the top of the file):

```rust
// ── Slice-4b: mixed BV+FP (no crossing op) now solves ──────────────────────
#[test]
fn mixed_bv_and_fp_sat_with_model() {
    // A pure-BV constraint AND a pure-FP constraint, no crossing conversion.
    // x = #x05 (BV8) and y is a NaN (FP32). Independent, jointly satisfiable.
    let src = "\
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= x #x05))
(assert (fp.isNaN y))
(check-sat)
(get-model)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "mixed BV+FP (no crossing) is SAT");
    assert!(model.contains("x"), "model surfaces the BV var");
    assert!(model.contains("y"), "model surfaces the FP var");
}

#[test]
fn mixed_bv_and_fp_unsat() {
    // BV side is self-contradictory; the whole conjunction is UNSAT regardless
    // of the (satisfiable) FP side — proves the two blast into one instance.
    let src = "\
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= x #x05))
(assert (= x #x06))
(assert (fp.isNaN y))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat, "contradictory BV side makes the mixed query UNSAT");
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-solver --test fp_e2e mixed_bv_and_fp`
Expected: FAIL — both currently return `Unknown` (the mixed fence), so `assert_eq!` fails (`Unknown != Sat` / `Unknown != Unsat`).

- [ ] **Step 3: Rewire the dispatch**

In `crates/shinri-solver/src/lib.rs`, replace the two blocks at lines 355-400 (the `lowered_bv` and `lowered_fp` `let` bindings, including their preceding comment banners at 344-354/376-381) with:

```rust
        // ── Crossing-conversion fence (slice 4b) ───────────────────────────────
        // The mixed BV+FP fence is LIFTED (pure-BV and pure-FP atoms may coexist
        // in one query), but BV↔FP crossing conversions are NOT yet admitted.
        // to_fp-from-BV / 1-arg bitcast / to_fp_unsigned / fp.to_ubv / fp.to_sbv /
        // fp.to_real / symbolic-Real to_fp still fence to Unknown, BEFORE any
        // lowering, so blast_*_word's crossing `unreachable!` arms stay internal
        // invariants. Each conversion is admitted in its own later slice.
        let uses_bv = crate::bv_stage::solver_uses_bv(&self.ctx, &assertions);
        let uses_fp = crate::fp_stage::solver_uses_fp(&self.ctx, &assertions);
        if uses_fp && crate::fp_stage::uses_crossing_conversion(&self.ctx, &assertions) {
            return SolveOutcome::Unknown;
        }

        // ── BV path (pure-BV only) ─────────────────────────────────────────────
        // A mixed BV+FP query is handled by the unified FP/mixed path below, so
        // the BV-only path runs only when NO FP is present. Non-BV theory atoms
        // (arrays/LIA/EUF) alongside BV still fence.
        let lowered_bv: Option<shinri_bv::Lowered> =
            if uses_bv && !uses_fp {
                let bv_atoms = crate::bv_stage::collect_bv_atoms(&self.ctx, &assertions);
                if crate::bv_stage::has_non_bv_theory_atom(&self.ctx, &assertions, &bv_atoms) {
                    return SolveOutcome::Unknown;
                }
                Some(shinri_bv::lower(&mut self.ctx, &bv_atoms))
            } else {
                None
            };

        // ── FP / mixed path (unified Lowerer over fp_atoms ∪ bv_atoms) ──────────
        // Slice 4b: lower BOTH the FP atoms and any BV atoms through the one 4a
        // Lowerer (shared Blaster + cache). Without a crossing op, BV and FP terms
        // are disjoint DAGs meeting only at the Boolean level, so this is two
        // independent blasting problems sharing one variable namespace. Pure-FP
        // takes an empty bv_atoms set and is byte-identical to the pre-4b path.
        let lowered_fp: Option<shinri_bv::Lowered> =
            if uses_fp {
                let fp_atoms = crate::fp_stage::collect_fp_atoms(&self.ctx, &assertions);
                let bv_atoms = crate::bv_stage::collect_bv_atoms(&self.ctx, &assertions);
                // Third-theory fence: any Bool atom outside (fp_atoms ∪ bv_atoms)
                // that is not pure Boolean structure (arrays/LIA/EUF) → Unknown.
                if crate::fp_stage::has_non_bvfp_theory_atom(
                    &self.ctx, &assertions, &fp_atoms, &bv_atoms,
                ) {
                    return SolveOutcome::Unknown;
                }
                // Positive-enumeration safety: every FP atom's word must be a
                // supported FP op (an FP-sorted ite, a not-yet-implemented FP op,
                // etc. still fence) so blast_fp_word's `unreachable!` arms stay
                // internal invariants. (BV atoms need no support check — the BV
                // blaster is total over BV ops once crossing ops are fenced.)
                if !crate::fp_stage::fp_atoms_fully_supported(&self.ctx, &fp_atoms) {
                    return SolveOutcome::Unknown;
                }
                Some(shinri_fp::lower_mixed(&mut self.ctx, &fp_atoms, &bv_atoms))
            } else {
                None
            };
```

- [ ] **Step 4: Split the mixed `var_bits` by sort at registration**

In `crates/shinri-solver/src/lib.rs`, replace the `lowered_fp` registration arm (lines 435-446) with:

```rust
        match lowered_fp {
            Some(lo) => {
                // Reuse replay_bv_cnf: it allocates a fresh contiguous var block,
                // so FP and BV namespaces never collide.
                let surrogates = self.replay_bv_cnf(&mut sat, lo);
                // Slice 4b: the mixed Lowered carries BOTH BV and FP variable
                // words in one map; split by sort into the two decode maps.
                // (Pure-FP: every entry is Float-sorted, so bv_var_bits stays
                // empty exactly as before. bv_var_bits was cleared by the
                // lowered_bv `None` arm above, since lowered_bv is None whenever
                // lowered_fp is Some.)
                self.fp_var_bits.clear();
                for (term, vars) in surrogates.var_bits {
                    if self.ctx.bv_width(self.ctx.sort_of(term)).is_some() {
                        self.bv_var_bits.insert(term, vars);
                    } else {
                        self.fp_var_bits.insert(term, vars);
                    }
                }
                surrogate_map.extend(surrogates.atom_to_lit);
            }
            None => {
                self.fp_var_bits.clear();
            }
        }
```

- [ ] **Step 5: Run the mixed e2e tests to verify they pass**

Run: `cargo test -p shinri-solver --test fp_e2e mixed_bv_and_fp`
Expected: PASS (both `mixed_bv_and_fp_sat_with_model` and `mixed_bv_and_fp_unsat`).

- [ ] **Step 6: Run the WHOLE fp_e2e suite — crossing canaries must still fence**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS — all pre-existing tests green, in particular `to_fp_bv_crossing_and_symbolic_real_are_unknown` (the 5-form crossing array still all `Unknown`) and the malformed-canary tests. This is the standing cross-slice guard: verify the crossing/malformed canaries did not flip.

- [ ] **Step 7: Run the BV e2e/witness suites — pure-BV unchanged**

Run: `cargo test -p shinri-solver --test qfbv_witnesses`
Expected: PASS (26/26) — the pure-BV path is untouched.

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/fp_e2e.rs
git commit -m "feat(solver): lift the mixed BV+FP fence — lower fp∪bv atoms through the Lowerer (slice 4b)"
```

---

### Task 5: Differential z3 oracle for mixed BV+FP

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (add `gen_mixed_script` + a `#[test]`)

**Interfaces:**
- Consumes: existing harness `Lcg`, `shinri_outcome(src)`, `z3_outcome_arith(src)`, `RMS`, and the `N_ITERS`/coverage-assert pattern from `differential_qf_fp_add_sub`.
- Produces: `differential_qf_bvfp_mixed` — a differential test over formulas mixing a BV predicate and an FP predicate with independently-declared BV and FP vars.

- [ ] **Step 1: Add the generator and test**

First read the existing `differential_qf_fp_add_sub` test and its helpers (`Lcg`, `shinri_outcome`, `z3_outcome_arith`, `RMS`, `N_ITERS`) in `crates/shinri-solver/tests/fp_oracle.rs` so the new generator matches their exact shapes (special-form FP32 constants, `declare-fun` lines forwarded verbatim to z3).

Add a generator that emits a conjunction of one BV predicate and one FP predicate over independently-declared vars, e.g.:

```rust
/// One mixed BV+FP script: a BV comparison AND an FP comparison over
/// independently-declared vars (no crossing conversion). Both sides are
/// forwarded to z3 verbatim by `z3_outcome_arith`.
fn gen_mixed_script(rng: &mut Lcg) -> String {
    // Reuse the FP32 special-form constant pool the other generators use for `a`,`b`.
    let a = fp32_special(rng); // <-- use the same constant helper the file already defines
    let b = fp32_special(rng);
    // BV side: an 8-bit unsigned comparison against a random constant.
    let k = (rng.next() & 0xff) as u8;
    let fp_rel = ["fp.lt", "fp.leq", "fp.gt", "fp.geq", "fp.eq"][(rng.next() % 5) as usize];
    let bv_rel = ["bvult", "bvule", "bvugt", "bvuge"][(rng.next() % 4) as usize];
    format!(
        "(declare-fun bx () (_ BitVec 8))\n\
         (declare-fun fa () (_ FloatingPoint 8 24))\n\
         (declare-fun fb () (_ FloatingPoint 8 24))\n\
         (assert (= fa {a}))\n\
         (assert (= fb {b}))\n\
         (assert (and ({bv_rel} bx #x{k:02x}) ({fp_rel} fa fb)))\n\
         (check-sat)\n"
    )
}

#[test]
fn differential_qf_bvfp_mixed() {
    let mut rng = Lcg::new(0xB0FE_1234);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0u32, 0u32, 0u32);
    for _ in 0..N_ITERS {
        let src = gen_mixed_script(&mut rng);
        let ours = shinri_outcome(&src);
        match ours {
            SolveOutcome::Unknown => { n_unknown += 1; continue; } // sound abstention
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
        }
        let theirs = z3_outcome_arith(&src);
        match (ours, theirs) {
            (SolveOutcome::Sat, Some(true)) | (SolveOutcome::Unsat, Some(false)) => {}
            (_, None) => {} // z3 unknown/timeout — skip
            (o, t) => panic!(
                "QF_BVFP MIXED SOUNDNESS DISAGREEMENT: shinri={o:?} z3={t:?}\nscript:\n{src}"
            ),
        }
    }
    assert!(n_sat > 0, "expected some SAT results ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)");
    assert!(n_unsat > 0, "expected some UNSAT results ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)");
}
```

Adapt the exact helper names (`fp32_special`, `RMS`, `N_ITERS`, the disagreement-detection tuple match, the coverage asserts) to whatever the file actually defines — mirror `differential_qf_fp_add_sub` precisely. If the file's FP-constant helper or `Sat`/`Unsat`/`Unknown` outcome checks differ, match them rather than the placeholders above.

- [ ] **Step 2: Run the new oracle test (z3 on PATH)**

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_bvfp_mixed -- --nocapture`
Expected: PASS — no soundness disagreement; both SAT and UNSAT witnessed. (Mixed non-crossing predicates are shallow circuits, so this runs in seconds-to-a-minute, not the fp.div deep-circuit timescale.)

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential z3 oracle for mixed BV+FP (slice 4b)"
```

---

### Task 6: Controller closeout — full-workspace regression, canary audit, clippy, docs

> **Controller-owned** per `[[shinri-long-tests-run-yourself]]`: this task runs the multi-minute exhaustive gate and the z3 oracle in the background directly, not through an implementer subagent.

**Files:**
- Modify: `docs/superpowers/specs/2026-07-01-shinri-qffp-slice4b-fence-lift-design.md` (Status → Landed)

- [ ] **Step 1: Full-workspace regression (background)**

Run (background): `cargo test --workspace` — must exit 0. Includes the `shinri-fp` exhaustive gate (~multi-minute) and every solver corpus. Confirm: shinri-bv, shinri-fp (exhaustive), fp_e2e (crossing canaries unflipped), qfbv_witnesses, and all other integration suites green with ZERO failures/panics.

- [ ] **Step 2: z3 differential oracle (background, feature-gated)**

Run (background): `cargo test -p shinri-solver --features oracle --test fp_oracle -- --nocapture` — ZERO disagreements across `differential_qf_fp_rounding_free`, `differential_qf_fp_add_sub`, and the new `differential_qf_bvfp_mixed`.

- [ ] **Step 3: Crossing-canary grep audit**

Run: `grep -n "Unknown" crates/shinri-solver/tests/fp_e2e.rs` and confirm the crossing/malformed canaries (`to_fp_bv_crossing_and_symbolic_real_are_unknown`, `fp_fma_malformed`, `fp_roundtointegral_malformed`, `fp_rem_malformed`) still assert `Unknown`. 4b admits nothing new; all five crossing forms and the malformed forms MUST remain `Unknown`.

- [ ] **Step 4: Clippy — zero net-new**

Run: `cargo clippy -p shinri-solver -p shinri-fp --all-targets` and confirm no net-new warnings in the touched files (`fp_stage.rs`, `lib.rs`, `shinri-fp/src/lib.rs`). Pre-existing warnings in untouched reference code are out of scope (2c-3a precedent).

- [ ] **Step 5: Mark the spec Landed and commit**

Edit the spec header `**Status:** Draft` → `**Status:** Landed 2026-07-01 — mixed BV+FP fence lifted; crossing conversions still fenced.`

```bash
git add docs/superpowers/specs/2026-07-01-shinri-qffp-slice4b-fence-lift-design.md
git commit -m "docs(qffp): mark slice-4b landed — mixed BV+FP fence lifted"
```

---

## Self-Review

**Spec coverage:**
- Spec §4.1 dispatch restructure → Task 4 (Steps 3-4). ✅
- Spec §4.2 `uses_crossing_conversion` single fence → Task 1; generalized third-theory guard → Task 2; both wired in Task 4. ✅ (Plan keeps `fp_atoms_fully_supported` for FP-word positive-enumeration/future-op safety — the spec noted it "can be simplified or retired"; the plan chooses to keep it, which is within the spec's latitude and strictly safer.)
- Spec §4.3 model read-back split by sort → Task 3 (union in `Lowered.var_bits`) + Task 4 Step 4 (solver split). ✅
- Spec §5 validation: regression → Task 6 Step 1; crossing canaries → Task 4 Step 6 + Task 6 Step 3; positive mixed canaries + get-model → Task 4 Step 1; differential oracle → Task 5. ✅
- Spec §6 risks: over-lifting → crossing gate before lowering (Task 4 Step 3) + canary guard; var-numbering → pure-BV untouched, pure-FP empty-bv wrapper (Tasks 3-4); `has_non_fp` inversion → Task 2 generalization. ✅

**Placeholder scan:** Task 5's generator uses adapt-to-file helper names by necessity (the harness's exact constant/`N_ITERS` names live in `fp_oracle.rs`); Step 1 explicitly instructs reading them first and mirroring `differential_qf_fp_add_sub`. All other steps contain complete, compilable code.

**Type consistency:** `uses_crossing_conversion(&Context, &[TermId]) -> bool`, `has_non_bvfp_theory_atom(&Context, &[TermId], &[TermId], &[TermId]) -> bool`, `lower_mixed(&mut Context, &[TermId], &[TermId]) -> shinri_bv::Lowered` are used identically in Task 4. `Lowered { cnf, atom_lit, var_bits }` matches `shinri-bv/src/lib.rs:13`. `bv_width`/`sort_of`/`sort_node`/`const_real_value` signatures match `shinri-core`.
