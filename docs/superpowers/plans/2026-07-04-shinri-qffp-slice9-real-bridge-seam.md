# QF_FP Slice 9 — the Real-bridge seam (`fp.to_real`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn `fp.to_real(x)` over Float16/32 from an unconditional `Unknown` fence into a decided verdict, solved jointly with LRA in one solve.

**Architecture:** Additive seam. `check_sat` already builds `Sat = Solver::with_theory(cfg, Combiner::with_context(ctx.clone()))` and blasts FP into it, so the Combiner (with Arith) is already co-resident — it is simply never fed arith atoms because the query fences first. We (1) add a recognizer for the admissible shape, (2) narrow the two fences that block it, and (3) inject bridge constraints: the Real `(fp.to_real x)` term becomes its own opaque arith variable (like `str.len`), pinned per exponent by guarded-linear rows — each row a normal `Le`/`Ge` atom plus a raw guard clause over the blasted FP bit `Var`s. No combined-solver surgery.

**Tech Stack:** Rust workspace `shinri`; crates `shinri-fp` (bridge math), `shinri-solver` (dispatch/emit), `shinri-arith` (LRA, unchanged), `shinri-core` (term/ctx). Exact-rational golden: `shinri_fp::reference::class_to_rational`. z3 differential via `easy_smt` under `--features oracle`.

## Global Constraints

- **Soundness contract:** anything out of scope returns `Unknown`, never a wrong Sat/Unsat. Every fence degrades to sound `Unknown`.
- **Scope line (this slice):** admit `fp.to_real` only; **symbolic `to_fp(rm, real)` stays fenced**; `fp.to_real` on `eb ≥ 11` (Float64/128) **stays fenced** (recognizer requires `eb ≤ 8`).
- **All bridge TermIds must be minted in `self.ctx` BEFORE the `self.ctx.clone()` into the Combiner** (`crates/shinri-solver/src/lib.rs:483`), else they are out of range for `classify`/`normalize`. Guard *clauses* are added after replay (when `fp_var_bits` holds the SAT `Var`s).
- **All bridge arith vars must be Real** (channel bits are 0/1-valued Reals). An Int arith var beside the Real bridge var trips the `lira` gate (`saw_int_arith && saw_real_arith` → Unknown, `lib.rs:603/606`).
- **Three NaN/±∞ constants must be DISTINCT unconstrained Real vars** (a single shared const would force `to_real(+∞)=to_real(−∞)` — a wrong-UNSAT).
- **FP bit layout** (`fp_var_bits[x]: Vec<Var>`, LSB→MSB, len `eb+sb`): significand `vars[0..sb-1]`, exponent `vars[sb-1 .. sb-1+eb]`, sign `vars[eb+sb-1]`. Literal for bit `i`: `Lit::new(vars[i], true)`.
- **Do NOT touch** the STAY canaries (symbolic-`to_fp` / bare-Real / other-theory): `fp_stage.rs:721,779,845,810-820`; `lib.rs:1903-1908`; `context.rs:1386`; `bv_stage.rs:298-313`; `abv_stage.rs:1066-1081`; `lia_e2e.rs:150-164`.
- Verified APIs: `ctx.mk_app(Op::Builtin(op), &[..]) -> Result<TermId,_>`; `ctx.mk_numeral(Rational, SortId) -> TermId`; `ctx.real_sort()`; `ctx.declare_fun(name,&[],sort) -> SymbolId` then `ctx.mk_app(Op::Uninterpreted(sym), &[])` for a fresh const; `ctx.fp_widths(ctx.sort_of(t)) -> Option<(eb,sb)>`; `Encoder::encode(&mut self, TermId) -> Lit`, `Encoder::assert_top(&mut self, Lit)`; `sat.add_clause(&[Lit]) -> bool`. Arith ops: `Add, Sub, Mul, Neg, Le, Lt, Ge, Gt` (`BuiltinOp`). `Rel` reaching Arith is only `Le`/`Lt` (Eq is split into `Le ∧ Ge` by `lower`).

---

### Task 1: Bridge-row math (`shinri-fp`)

Pure exact-rational helper: for a format and a concrete (sign, exponent-field), the finite `fp.to_real` value as `K + Σ coeffs[i]·bit_i`. Validated bit-identically against `class_to_rational`.

**Files:**
- Create: `crates/shinri-fp/src/bridge.rs`
- Modify: `crates/shinri-fp/src/lib.rs` (add `pub mod bridge;`)
- Test: in `crates/shinri-fp/src/bridge.rs` (`#[cfg(test)]`)

**Interfaces:**
- Produces: `shinri_fp::bridge::FiniteRow { pub k: Rational, pub coeffs: Vec<Rational> }`; `shinri_fp::bridge::to_real_finite_row(eb: u32, sb: u32, sign: bool, e: u64) -> Option<FiniteRow>` (returns `None` iff `e` is all-ones; `coeffs.len() == (sb-1) as usize`, LSB-first).

- [ ] **Step 1: Write the failing test**

Add to `crates/shinri-fp/src/bridge.rs`:
```rust
#[cfg(test)]
mod tests {
    use super::*;
    use shinri_num::Integer;
    use crate::reference::{decode, class_to_rational};

    // Reconstruct the (eb+sb)-bit integer from (sign, e, sig) and compare the
    // row's K + Σ coeffs[i]*bit_i against the golden class_to_rational.
    fn check(eb: u32, sb: u32, sign: bool, e: u64, sig: u64) {
        let w = eb + sb;
        let bits: Integer = (Integer::from(sign as u64) << (w - 1))
            + (Integer::from(e) << (sb - 1))
            + Integer::from(sig);
        let golden = class_to_rational(eb, sb, &decode(eb, sb, &bits));
        match to_real_finite_row(eb, sb, sign, e) {
            None => assert!(golden.is_none(), "all-ones must be NaN/Inf: {eb} {sb} {e}"),
            Some(row) => {
                assert_eq!(row.coeffs.len(), (sb - 1) as usize);
                let mut v = row.k.clone();
                for i in 0..(sb - 1) {
                    if (sig >> i) & 1 == 1 { v = v + row.coeffs[i as usize].clone(); }
                }
                assert_eq!(Some(v), golden, "mismatch eb={eb} sb={sb} s={sign} e={e} sig={sig}");
            }
        }
    }

    #[test]
    fn f16_rows_match_reference() {
        let (eb, sb) = (5u32, 11u32);
        for e in 0..(1u64 << eb) {
            for &sign in &[false, true] {
                for &sig in &[0u64, 1, 5, (1 << (sb - 1)) - 1] {
                    check(eb, sb, sign, e, sig);
                }
            }
        }
    }

    #[test]
    fn f32_normal_subnormal_zero_match_reference() {
        let (eb, sb) = (8u32, 24u32);
        for &e in &[0u64, 1, 127, 200, (1 << eb) - 2] {
            for &sign in &[false, true] {
                for &sig in &[0u64, 1, 12345, (1 << (sb - 1)) - 1] {
                    check(eb, sb, sign, e, sig);
                }
            }
        }
    }

    #[test]
    fn signed_zero_is_zero() {
        let row = to_real_finite_row(5, 11, true, 0).unwrap();
        assert_eq!(row.k, shinri_num::Rational::from(0i64)); // e=0,sig=0 ⇒ 0
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp bridge:: 2>&1 | head -30`
Expected: FAIL — `to_real_finite_row` / `FiniteRow` / `mod bridge` not found.

- [ ] **Step 3: Write minimal implementation**

Put at the top of `crates/shinri-fp/src/bridge.rs`:
```rust
//! Exact-rational rows for the fp.to_real bridge (QF_FP slice 9). For a format
//! (eb,sb) and a concrete (sign, biased-exponent-field e), the finite value is
//! `(-1)^sign * significand * 2^(e - bias - (sb-1))` (reference::class_to_rational),
//! re-expressed as a linear form `K + Σ coeffs[i]*bit_i` over the (sb-1)
//! significand bits so the solver can pin it under an exponent guard.

use shinri_num::{Integer, Rational};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteRow {
    pub k: Rational,
    pub coeffs: Vec<Rational>, // len == sb-1, LSB first
}

/// 2^k as a Rational (k may be negative).
fn pow2(k: i64) -> Rational {
    let mut acc = Integer::from(1u64);
    let two = Integer::from(2u64);
    for _ in 0..k.unsigned_abs() { acc = acc * two.clone(); }
    if k >= 0 { Rational::new(acc, Integer::from(1u64)) }
    else { Rational::new(Integer::from(1u64), acc) }
}

/// The finite fp.to_real row for (sign, exponent-field `e`); `None` iff `e` is
/// all-ones (NaN/Inf — the caller emits the special-constant rows instead).
pub fn to_real_finite_row(eb: u32, sb: u32, sign: bool, e: u64) -> Option<FiniteRow> {
    let all_ones = (1u64 << eb) - 1;
    if e == all_ones { return None; }
    let bias = (1i64 << (eb - 1)) - 1;
    let sgn = if sign { Rational::from(-1i64) } else { Rational::from(1i64) };
    // Normal: scale 2^(e-bias-(sb-1)), hidden bit 2^(sb-1).
    // Subnormal/zero (e==0): scale 2^(1-bias-(sb-1)), no hidden bit.
    let (scale, hidden) = if e == 0 {
        (pow2(1 - bias - (sb as i64 - 1)), Integer::from(0u64))
    } else {
        let mut h = Integer::from(1u64);
        for _ in 0..(sb - 1) { h = h * Integer::from(2u64); }
        (pow2(e as i64 - bias - (sb as i64 - 1)), h)
    };
    let k = sgn.clone() * Rational::new(hidden, Integer::from(1u64)) * scale.clone();
    let coeffs = (0..(sb - 1))
        .map(|i| sgn.clone() * pow2(i as i64) * scale.clone())
        .collect();
    Some(FiniteRow { k, coeffs })
}
```
Add to `crates/shinri-fp/src/lib.rs` (next to the other `pub mod` lines): `pub mod bridge;`

(If `Rational::from(i64)` / `Rational::new` names differ, mirror the exact calls already used in `reference.rs:220-227`.)

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp bridge:: 2>&1 | tail -20`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/bridge.rs crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): exact-rational fp.to_real bridge rows, bit-identical to class_to_rational (slice 9)"
```

---

### Task 2: Admissibility recognizer (`shinri-solver::fp_stage`)

A pure predicate identifying the exact shape this slice admits: FP present, the only crossing conversion is `fp.to_real` over `eb ≤ 8`, and every non-BVFP atom is a pure-LRA-Real arith atom. Not yet wired into dispatch — no behavior change.

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs` (add fns + tests)

**Interfaces:**
- Consumes: `shinri_fp` (none new); `Context`, `TermId`.
- Produces: `pub fn bridge_admissible(ctx: &Context, assertions: &[TermId]) -> bool`; helper `fn only_crossing_is_admitted_to_real(ctx, assertions) -> bool`; helper `fn is_lra_real_atom(ctx, t: TermId) -> bool`.

- [ ] **Step 1: Write the failing test**

Add to the `#[cfg(test)] mod tests` in `crates/shinri-solver/src/fp_stage.rs`:
```rust
#[test]
fn bridge_admissible_accepts_to_real_plus_lra() {
    let mut ctx = Context::new();
    let f32 = ctx.mk_float_sort(8, 24);
    let x = ctx.declare_const_for_test("x", f32); // see helper note below
    let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap();
    let real = ctx.real_sort();
    let c = ctx.mk_numeral(shinri_num::Rational::from(1i64), real);
    let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[toreal, c]).unwrap();
    assert!(super::bridge_admissible(&ctx, &[gt]), "to_real(F32)+LRA is admissible");
}

#[test]
fn bridge_admissible_rejects_symbolic_to_fp() {
    // symbolic-Real to_fp must NOT be admitted (stays fenced elsewhere).
    let mut ctx = Context::new();
    let real = ctx.real_sort();
    let r = ctx.declare_const_for_test("r", real);
    let z = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }),
                       &[ctx_rne(&mut ctx), r]).unwrap();
    assert!(!super::bridge_admissible(&ctx, &[z]));
}

#[test]
fn bridge_admissible_rejects_large_format() {
    let mut ctx = Context::new();
    let f64 = ctx.mk_float_sort(11, 53);
    let x = ctx.declare_const_for_test("x", f64);
    let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap();
    let real = ctx.real_sort();
    let c = ctx.mk_numeral(shinri_num::Rational::from(0i64), real);
    let eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[toreal, c]).unwrap();
    assert!(!super::bridge_admissible(&ctx, &[eq]), "eb>=11 stays fenced");
}
```
Use the SAME construction idioms already present in this test module (find how existing tests here mint a Float const and an `RNE` term — reuse those exact helpers rather than the placeholder `declare_const_for_test`/`ctx_rne`/`mk_float_sort` names; e.g. tests around `fp_stage.rs:635-720` already build `x` of a Float sort and RM constants).

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver --lib fp_stage::tests::bridge_admissible 2>&1 | head -20`
Expected: FAIL — `bridge_admissible` not found.

- [ ] **Step 3: Write minimal implementation**

Add to `crates/shinri-solver/src/fp_stage.rs` (near `uses_crossing_conversion`):
```rust
/// True iff every crossing conversion present is an admitted `fp.to_real`
/// (operand Float with eb ≤ 8) — i.e. NO symbolic-Real `to_fp`, and no
/// `fp.to_real` over a too-large format.
fn only_crossing_is_admitted_to_real(ctx: &Context, assertions: &[TermId]) -> bool {
    let mut seen: rustc_hash::FxHashSet<TermId> = rustc_hash::FxHashSet::default();
    fn walk(ctx: &Context, t: TermId, seen: &mut rustc_hash::FxHashSet<TermId>) -> bool {
        if !seen.insert(t) { return true; }
        if let TermNode::App { op, args, .. } = ctx.term_node(t) {
            let kids: Vec<TermId> = ctx.children(*args).to_vec();
            match op {
                Op::Builtin(BuiltinOp::FpToReal) => {
                    // admitted iff operand is Float with eb <= 8
                    match ctx.fp_widths(ctx.sort_of(kids[0])) {
                        Some((eb, _sb)) if eb <= 8 => {}
                        _ => return false,
                    }
                }
                Op::Builtin(BuiltinOp::ToFp { .. }) => {
                    // any symbolic-Real to_fp face is NOT admitted here.
                    if kids.len() == 2
                        && matches!(ctx.sort_node(ctx.sort_of(kids[1])), SortNode::Real)
                        && ctx.const_real_value(kids[1]).is_none()
                    {
                        return false;
                    }
                }
                _ => {}
            }
            return kids.into_iter().all(|c| walk(ctx, c, seen));
        }
        true
    }
    assertions.iter().all(|&a| walk(ctx, a, &mut seen))
}

/// A Bool atom that is a pure LRA (Real) arith relation: Le/Lt/Ge/Gt/Eq/Distinct
/// whose operands are Real-sorted (so it routes to Arith, not Int/EUF/arrays).
fn is_lra_real_atom(ctx: &Context, t: TermId) -> bool {
    if let TermNode::App { op, args, .. } = ctx.term_node(t) {
        use BuiltinOp::*;
        if matches!(op, Op::Builtin(Le | Lt | Ge | Gt | Eq | Distinct)) {
            let kids = ctx.children(*args);
            return kids.iter().all(|&k| matches!(ctx.sort_node(ctx.sort_of(k)), SortNode::Real));
        }
    }
    false
}

/// The exact shape QF_FP slice 9 admits for the fp.to_real bridge: FP present,
/// only crossing is an admitted fp.to_real, and every atom outside
/// (fp_atoms ∪ bv_atoms) is a pure-LRA-Real arith atom. Anything else → false
/// (caller keeps fencing to sound Unknown).
pub fn bridge_admissible(ctx: &Context, assertions: &[TermId]) -> bool {
    if !solver_uses_fp(ctx, assertions) { return false; }
    if !only_crossing_is_admitted_to_real(ctx, assertions) { return false; }
    let fp_atoms = collect_fp_atoms(ctx, assertions);
    let bv_atoms = crate::bv_stage::collect_bv_atoms(ctx, assertions);
    // Every non-BVFP Bool atom must be a pure-LRA-Real atom. Reuse the existing
    // atom-walk used by has_non_bvfp_theory_atom but accept is_lra_real_atom.
    non_bvfp_atoms(ctx, assertions, &fp_atoms, &bv_atoms)
        .into_iter()
        .all(|t| is_lra_real_atom(ctx, t))
}
```
If a private `non_bvfp_atoms`-style enumerator does not already exist, factor it out of `has_non_bvfp_theory_atom` (`fp_stage.rs:140-184`) so both share one walk (DRY). Its body is the same walk `has_non_bvfp_theory_atom` uses to find "third-theory" Bool atoms; return them as a `Vec<TermId>` instead of a bool.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-solver --lib fp_stage::tests::bridge_admissible 2>&1 | tail -20`
Expected: PASS (3 tests). Also run `cargo test -p shinri-solver --lib fp_stage 2>&1 | tail -5` — all existing fp_stage tests still green (no behavior change).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): bridge_admissible recognizer for fp.to_real+LRA (slice 9, not yet wired)"
```

---

### Task 3: Constant `fp.to_real` — dispatch, fences, canaries, first e2e

Wire the bridge path for the simplest case: `fp.to_real(<fp literal>)`. Emit one unconditional row `r_x = class_to_rational(x)` (no guards, no channel). This lands the dispatch branch, both fence narrowings, and the three canary flips.

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (dispatch + emitter scaffold)
- Modify: `crates/shinri-solver/src/fp_stage.rs:88` (narrow `uses_crossing_conversion`), `:659`, `:837-838` (canary flips A,B)
- Modify: `crates/shinri-solver/tests/fp_e2e.rs:639-650` (canary flip C)
- Test: `crates/shinri-solver/tests/fp_e2e.rs` (new e2e)

**Interfaces:**
- Consumes: `shinri_fp::bridge`, `fp_stage::bridge_admissible`, `class_to_rational`, `decode`.
- Produces: `impl Solver { fn emit_to_real_bridge(&mut self, enc: &mut Encoder, fp_to_real_terms: &[TermId]); }` (this task: constant arm only). A struct field or local to carry the fp.to_real term list from dispatch to the enc block.

- [ ] **Step 1: Write the failing test**

Add to `crates/shinri-solver/tests/fp_e2e.rs`:
```rust
#[test]
fn to_real_of_constant_plus_lra_sat() {
    // 1.5f32 to_real == 3/2; assert it's > 1 and < 2 ⇒ SAT.
    let (o, _) = run("(declare-fun x () Float32) \
        (assert (= x (fp #b0 #b01111111 #b10000000000000000000000))) \
        (assert (> (fp.to_real x) 1.0)) (assert (< (fp.to_real x) 2.0)) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn to_real_of_constant_contradiction_unsat() {
    let (o, _) = run("(declare-fun x () Float32) \
        (assert (= x (fp #b0 #b01111111 #b10000000000000000000000))) \
        (assert (> (fp.to_real x) 2.0)) (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver --test fp_e2e to_real_of_constant 2>&1 | tail -20`
Expected: FAIL — both return `Unknown` (still fenced).

- [ ] **Step 3a: Narrow `uses_crossing_conversion` + flip canaries A/B**

In `crates/shinri-solver/src/fp_stage.rs`, change the `FpToReal` arm (line 88) from `Op::Builtin(BuiltinOp::FpToReal) => true,` to:
```rust
// fp.to_real is admitted (slice 9) for eb<=8; larger formats stay crossing.
Op::Builtin(BuiltinOp::FpToReal) => match ctx.fp_widths(ctx.sort_of(kids[0])) {
    Some((eb, _)) if eb <= 8 => false,
    _ => true,
},
```
Flip canary A (`fp_stage.rs:659`), which builds `x: Float32`:
```rust
assert!(!super::uses_crossing_conversion(&ctx, &[toreal]),
        "fp.to_real over F32 is admitted (slice 9)");
```
Flip canary B (`fp_stage.rs:837-838`), same `x: Float32`: change the assertion to `assert!(!uses_crossing_conversion(&ctx, &[toreal]), "fp.to_real F32 admitted (slice 9)");`. **Leave line 845 (`nested symbolic-Real to_fp still crossing`) unchanged.** If either canary's `x` is not Float32, add a second Float64 `x` and assert it is STILL crossing, to pin the eb≤8 boundary.

- [ ] **Step 3b: Dispatch branch + constant emitter**

In `crates/shinri-solver/src/lib.rs`, just before the crossing fence (line ~410), compute admissibility and collect the fp.to_real terms:
```rust
let bridge = uses_fp && crate::fp_stage::bridge_admissible(&self.ctx, &assertions);
let to_real_terms: Vec<TermId> = if bridge {
    crate::fp_stage::collect_fp_to_real_terms(&self.ctx, &assertions) // add: walk collecting FpToReal apps
} else { Vec::new() };
```
Change the crossing fence (line 412) to skip when admissible:
```rust
if uses_fp && !bridge && crate::fp_stage::uses_crossing_conversion(&self.ctx, &assertions) {
    return SolveOutcome::Unknown;
}
```
Skip the third-theory fence when admissible (line 443): wrap `if !bridge && crate::fp_stage::has_non_bvfp_theory_atom(...) { return Unknown; }`.
The fp.to_real operand terms are Real-sorted, so `collect_fp_atoms` does not gather them — good; blasting proceeds on the FP words as before. Inside the `enc` block (after `enc.assert_top` for the top lits, `lib.rs:582`), before `atom_vars = enc.atom_vars.clone()`:
```rust
if bridge {
    self.emit_to_real_bridge(&mut enc, &to_real_terms);
}
```
Add the emitter (constant arm only this task) on `impl Solver`:
```rust
fn emit_to_real_bridge(&mut self, enc: &mut Encoder, terms: &[TermId]) {
    let real = self.ctx.real_sort();
    for &tr in terms {
        // tr == (fp.to_real x). Recover x and its format.
        let x = match self.ctx.term_node(tr) {
            TermNode::App { args, .. } => self.ctx.children(*args)[0],
            _ => continue,
        };
        let (eb, sb) = self.ctx.fp_widths(self.ctx.sort_of(x)).expect("Float operand");
        // CONSTANT ARM: x is an fp literal ⇒ pin r=value unconditionally.
        if let Some(bits) = self.ctx.fp_const_bits(x) {           // Some(Integer) iff x is a Float const
            let cls = shinri_fp::reference::decode(eb, sb, &bits);
            if let Some(q) = shinri_fp::reference::class_to_rational(eb, sb, &cls) {
                let num = self.ctx.mk_numeral(q, real);
                self.assert_eq_real(enc, tr, num);               // r = num  (two guarded-free ineqs)
            }
            // NaN/Inf constant ⇒ leave r unconstrained (sound). Symbolic handled in Task 4/5.
            continue;
        }
        // symbolic x: implemented in Task 4/5.
    }
}

// Assert `a == b` over Real by encoding (a<=b) and (a>=b) as top unit clauses.
fn assert_eq_real(&mut self, enc: &mut Encoder, a: TermId, b: TermId) {
    let le = self.ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[a, b]).unwrap();
    let ge = self.ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[a, b]).unwrap();
    let ll = enc.encode(le);
    let lg = enc.encode(ge);
    enc.assert_top(ll);
    enc.assert_top(lg);
}
```
**Ordering:** `mk_app`/`mk_numeral` above run inside the enc block, i.e. AFTER `self.ctx.clone()` into the Combiner (line 483) — so these terms are NOT in the Combiner's context and `register_atom` will index out of range. **Fix:** mint every bridge term in a pre-clone pass. Restructure: before line 483, when `bridge`, call `self.build_to_real_bridge_terms(&to_real_terms)` which mints the numerals/atom terms and returns a `Vec` of `(le_term, ge_term)` (and, in Task 4/5, channel/guard metadata); store it on `self`; the enc-block emitter only `enc.encode`s and `assert_top`s those pre-built terms (no `mk_app` after the clone). Implement `build_to_real_bridge_terms` accordingly and have `assert_eq_real` take pre-built `(le, ge)` term ids. Add `fp_const_bits(&self, TermId) -> Option<Integer>` to `Context` if absent (read `ConstVal::Float(id)` and the stored bits — see `context.rs:873,887`).

- [ ] **Step 3c: Flip canary C**

In `crates/shinri-solver/tests/fp_e2e.rs`, test `to_fp_bv_crossing_and_symbolic_real_are_unknown` (lines 632-651): remove the `fp.to_real` entry (`scripts[1]`) from the shared-`Unknown` array so only the symbolic-`to_fp` script remains under `assert_eq!(o, Unknown)`. Rename the test if its name implied fp.to_real. The fp.to_real→solves behavior is covered by the new tests in Step 1.

- [ ] **Step 4: Run tests**

Run: `cargo test -p shinri-solver --test fp_e2e to_real_of_constant 2>&1 | tail -20` → PASS (2).
Run: `cargo test -p shinri-solver --lib fp_stage 2>&1 | tail -5` and `cargo test -p shinri-solver --test fp_e2e 2>&1 | tail -10` → all green (canaries A/B/C updated).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/src/fp_stage.rs crates/shinri-solver/tests/fp_e2e.rs crates/shinri-core/src/context.rs
git commit -m "feat(solver): fp.to_real bridge dispatch + constant arm; narrow both fences; flip canaries A/B/C (slice 9)"
```

---

### Task 4: Symbolic finite rows (guarded-linear + significand channel)

Emit the guarded per-exponent rows for a symbolic FP variable: significand bit→{0,1} Real channel + one `(r ≤ L) ∧ (r ≥ L)` pair per (sign, exp) finite pattern, each gated by a raw guard clause over the blasted FP bits.

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (`build_to_real_bridge_terms` + `emit_to_real_bridge` symbolic arm; add `Encoder::add_clause`)
- Modify: `crates/shinri-solver/src/tseitin.rs` (expose `pub fn add_clause(&mut self, lits: &[Lit]) -> bool { self.sat.add_clause(lits) }`)
- Test: `crates/shinri-solver/tests/fp_e2e.rs`

**Interfaces:**
- Consumes: `shinri_fp::bridge::to_real_finite_row`, `fp_var_bits: FxHashMap<TermId, Vec<Var>>`, `Encoder::{encode,assert_top,add_clause}`.
- Produces: symbolic finite bridge rows. Guard clause for pattern (sign `s`, exp `e`) with atom literal `alit`: `[¬sign_match, ¬exp_bit_0_match, …, ¬exp_bit_{eb-1}_match, alit]`, where `bit_match` is the FP bit literal in the polarity equal to the pattern, so its negation is the opposite polarity.

- [ ] **Step 1: Write the failing test**
```rust
#[test]
fn to_real_symbolic_f16_range_sat() {
    // Some normal Float16 x with 2 < to_real(x) < 3 exists (e.g. 2.5).
    let (o, model) = run("(declare-fun x () Float16) \
        (assert (fp.isNormal x)) \
        (assert (> (fp.to_real x) 2.0)) (assert (< (fp.to_real x) 3.0)) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat, "model: {model}");
}

#[test]
fn to_real_symbolic_f16_impossible_unsat() {
    // A normal positive value cannot be both > 5 and < 4.
    let (o, _) = run("(declare-fun x () Float16) (assert (fp.isNormal x)) \
        (assert (> (fp.to_real x) 5.0)) (assert (< (fp.to_real x) 4.0)) (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn to_real_matches_classification_f16() {
    // isZero ⇒ to_real == 0; combined with to_real > 0 ⇒ UNSAT.
    let (o, _) = run("(declare-fun x () Float16) (assert (fp.isZero x)) \
        (assert (> (fp.to_real x) 0.0)) (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat);
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-solver --test fp_e2e to_real_symbolic 2>&1 | tail -20`
Expected: FAIL — symbolic arm unimplemented (returns Unknown or wrong verdict). `to_real_matches_classification_f16` also FAIL.

- [ ] **Step 3: Implement the symbolic arm**

Add `pub fn add_clause` to `Encoder` (tseitin.rs) as above. In the pre-clone `build_to_real_bridge_terms`, for a symbolic `x` of format (eb,sb) with `eb ≤ 8`:
1. Mint `sb-1` fresh Real channel consts `b_0..b_{sb-2}` (`fresh_real_const(name)` = `declare_fun` + nullary `mk_app`; unique names via a `u64` counter on `self`). Record `(x, i) -> b_i`.
2. Mint the two unconditional bound atoms per channel bit: `bge0 = (Ge b_i 0)`, `ble1 = (Le b_i 1)` — asserted top later.
3. Mint the two channel-tie atoms per bit: `bge1 = (Ge b_i 1)`, `ble0 = (Le b_i 0)`.
4. For each finite pattern `(s, e)` with `to_real_finite_row(eb,sb,s,e) = Some(FiniteRow{k, coeffs})`: build the linear RHS term `L = k + Σ coeffs[i]·b_i` via `mk_numeral(k)` folded with `Add`/`Mul(mk_numeral(coeffs[i]), b_i)` (drop zero coeffs), then `le=(Le tr L)`, `ge=(Ge tr L)`. Record `(le, ge, s, e)`.
Store all minted terms + metadata in a `Vec` on `self` (e.g. `self.pending_bridge`). All `mk_*` happen here — **before** the clone.

In the enc-block `emit_to_real_bridge` symbolic arm, for each recorded `x`:
```rust
let vars = self.fp_var_bits.get(&x).cloned().unwrap();   // LSB→MSB, len eb+sb
let sig_lit = |i: u32| Lit::new(vars[i as usize], true);          // significand bit i
let exp_lit = |j: u32| Lit::new(vars[(sb - 1 + j) as usize], true);
let sign_lit = Lit::new(vars[(eb + sb - 1) as usize], true);
// (a) channel bounds: b_i in [0,1] unconditionally.
for each bit i: enc.assert_top(enc.encode(bge0_i)); enc.assert_top(enc.encode(ble1_i));
// (b) channel tie: sigbit_i → b_i>=1 ; ¬sigbit_i → b_i<=0.
for each bit i {
    let l_ge1 = enc.encode(bge1_i); let l_le0 = enc.encode(ble0_i);
    enc.add_clause(&[!sig_lit(i), l_ge1]);   // sigbit_i → b_i>=1
    enc.add_clause(&[ sig_lit(i), l_le0]);   // ¬sigbit_i → b_i<=0
}
// (c) finite rows: guard(s,e) → r<=L and r>=L.
for (le, ge, s, e) in rows_for_x {
    let ll = enc.encode(le); let lg = enc.encode(ge);
    // guard literals = FP bits matching the pattern; clause carries their negations.
    let mut base = Vec::new();
    base.push(if s { !sign_lit } else { sign_lit }); // will be negated below
    for j in 0..eb { let want1 = (e >> j) & 1 == 1; base.push(if want1 { exp_lit(j) } else { !exp_lit(j) }); }
    let neg: Vec<Lit> = base.iter().map(|l| !*l).collect();
    let mut c1 = neg.clone(); c1.push(ll); enc.add_clause(&c1);
    let mut c2 = neg;         c2.push(lg); enc.add_clause(&c2);
}
```
(`e` ranges over `0..(1<<eb)` minus all-ones; `to_real_finite_row` returns `None` for all-ones so those are skipped here — the special constants are Task 5.) Keep the constant arm from Task 3 for literal `x`.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-solver --test fp_e2e to_real_symbolic 2>&1 | tail -20` and `... to_real_matches_classification 2>&1 | tail -5`
Expected: PASS. Then `cargo test -p shinri-solver --test fp_e2e 2>&1 | tail -10` → all green.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/src/tseitin.rs crates/shinri-solver/tests/fp_e2e.rs
git commit -m "feat(solver): symbolic fp.to_real guarded-linear rows + significand channel (slice 9)"
```

---

### Task 5: NaN/±∞ functionality — the three distinct special constants

Route `e = all-ones` to three distinct unconstrained Real constants per format (`+∞`, `−∞`, NaN) so `fp.to_real` stays a function (no wrong-SAT) while remaining unspecified (no wrong-UNSAT).

**Files:**
- Modify: `crates/shinri-solver/src/lib.rs` (special-constant arm of the emitter)
- Test: `crates/shinri-solver/tests/fp_e2e.rs`

**Interfaces:**
- Consumes: per-format special consts `pos_inf_c(eb,sb)`, `neg_inf_c(eb,sb)`, `nan_c(eb,sb)` — minted once per (eb,sb), memoized on `self`, shared across all fp.to_real terms of that format.
- Guard clauses (all-ones exponent): `+∞` = exp all-ones ∧ all sig bits 0 ∧ sign 0; `−∞` = same, sign 1; NaN = exp all-ones ∧ sig bit `j` set — one clause per `j`.

- [ ] **Step 1: Write the failing test**
```rust
#[test]
fn to_real_nan_is_functional_unsat() {
    // x=y, both NaN, but to_real(x) != to_real(y) ⇒ UNSAT (functionality).
    let (o, _) = run("(declare-fun x () Float16) (declare-fun y () Float16) \
        (assert (fp.isNaN x)) (assert (fp.isNaN y)) (assert (= x y)) \
        (assert (not (= (fp.to_real x) (fp.to_real y)))) (check-sat)");
    assert_eq!(o, SolveOutcome::Unsat, "fp.to_real must be a function over NaN");
}

#[test]
fn to_real_pos_neg_inf_may_differ_sat() {
    // +inf and -inf are distinct values; their unspecified reals may differ ⇒ SAT.
    let (o, _) = run("(declare-fun x () Float16) (declare-fun y () Float16) \
        (assert (fp.isInfinite x)) (assert (fp.isPositive x)) \
        (assert (fp.isInfinite y)) (assert (fp.isNegative y)) \
        (assert (not (= (fp.to_real x) (fp.to_real y)))) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat, "distinct-const specials must allow inequality");
}
```

- [ ] **Step 2: Run to verify it fails**

Run: `cargo test -p shinri-solver --test fp_e2e to_real_nan to_real_pos_neg 2>&1 | tail -20`
Expected: `to_real_nan_is_functional_unsat` FAILS (currently SAT — each all-ones r unconstrained/independent). `to_real_pos_neg_inf_may_differ_sat` may pass vacuously; keep it as a guard against over-sharing.

- [ ] **Step 3: Implement the special arm**

In `build_to_real_bridge_terms`, memoize per (eb,sb): `pos = fresh_real_const`, `neg = fresh_real_const`, `nan = fresh_real_const` (unconstrained). For each symbolic `x`, pre-build `(le,ge)` pairs pinning `tr` to each of the three (`assert_eq_real`-style term pairs), tagged with which special. In the enc-block emitter (all-ones handling), with `sig_lit/exp_lit/sign_lit` as in Task 4:
```rust
let all_exp_true: Vec<Lit> = (0..eb).map(|j| exp_lit(j)).collect(); // exp = all-ones guard
let all_sig_zero_neg: Vec<Lit> = (0..sb-1).map(|i| sig_lit(i)).collect(); // ∨ sigbit ⇒ "not all zero"
// +inf: (exp all-ones) ∧ (all sig 0) ∧ (sign=0) → r = pos
//   clause = [¬exp_j …] ∨ [sig_i …] ∨ [sign_lit] ∨ atom_lit
let neg_exp: Vec<Lit> = all_exp_true.iter().map(|l| !*l).collect();
for (le,ge) in pos_pairs {
    let (ll,lg)=(enc.encode(le),enc.encode(ge));
    let build = |atom: Lit| { let mut c=neg_exp.clone(); c.extend(all_sig_zero_neg.iter().cloned()); c.push(sign_lit); c.push(atom); c };
    enc.add_clause(&build(ll)); enc.add_clause(&build(lg));
}
// -inf: same but push ¬sign_lit (sign=1).
for (le,ge) in neg_pairs { /* ... c.push(!sign_lit) ... */ }
// NaN: (exp all-ones) ∧ (sig bit j set) → r = nan, one clause per j.
for (le,ge) in nan_pairs {
    let (ll,lg)=(enc.encode(le),enc.encode(ge));
    for j in 0..sb-1 {
        let g = |atom: Lit| { let mut c=neg_exp.clone(); c.push(!sig_lit(j)); c.push(atom); c };
        enc.add_clause(&g(ll)); enc.add_clause(&g(lg));
    }
}
```
Guard-clause soundness note (in a code comment): `¬exp_j` disjunction is false exactly when the exponent is all-ones; the sig disjunction/`¬sig_j` selects inf vs nan; sign selects ±∞. Exactly one special fires; each is a distinct unconstrained const ⇒ functional (same class same const) yet independent across classes.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-solver --test fp_e2e to_real 2>&1 | tail -20` → all PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/lib.rs crates/shinri-solver/tests/fp_e2e.rs
git commit -m "feat(solver): fp.to_real NaN/±inf functionality via three distinct per-format consts (slice 9)"
```

---

### Task 6: z3 differential oracle (constant-source, n_unknown == 0)

Add a seeded differential test pinning `fp.to_real` over F16/F32 against z3, including the functionality obligation. Constant-source (bind the FP var to a literal) so both solvers decide and zero Unknowns are allowed.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs`

**Interfaces:**
- Consumes: existing `Lcg`, `N_ITERS`, `shinri_outcome`, `z3_outcome_arith` (sets `QF_FP`, which includes the `Real` sort ⇒ `fp.to_real` is accepted). Follow the constant-source pattern of `differential_qf_bvfp_fp_to_bv` (fp_oracle.rs:1181,1214,1250).

- [ ] **Step 1: Write the failing test**
```rust
#[cfg(feature = "oracle")]
fn gen_to_real_script(rng: &mut Lcg) -> String {
    // constant-source: bind x to a random Float16 literal, constrain to_real via LRA.
    let bits = (rng.next() & 0xFFFF) as u16;
    let s = (bits >> 15) & 1; let e = (bits >> 10) & 0x1F; let sig = bits & 0x3FF;
    let bound = (rng.next() % 21) as i64 - 10; // integer bound in [-10,10]
    format!("(declare-fun x () Float16) \
        (assert (= x (fp #b{s:01b} #b{e:05b} #b{sig:010b}))) \
        (assert (<= (fp.to_real x) {bound}.0)) (check-sat)")
}

#[cfg(feature = "oracle")]
#[test]
fn differential_qf_fp_to_real() {
    let mut rng = Lcg(0xB000_0BEE_F001);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0, 0, 0);
    for _ in 0..N_ITERS {
        let s = gen_to_real_script(&mut rng);
        let ours = shinri_outcome(&s);
        if ours == SolveOutcome::Unknown { n_unknown += 1; }
        let theirs = z3_outcome_arith(&s);
        match (ours, theirs) {
            (SolveOutcome::Sat, _) => n_sat += 1,
            (SolveOutcome::Unsat, _) => n_unsat += 1,
            _ => {}
        }
        assert!(!matches!((ours, theirs),
            (SolveOutcome::Sat, Z3::Unsat) | (SolveOutcome::Unsat, Z3::Sat)),
            "DISAGREEMENT on: {s}");
    }
    assert!(n_sat > 0 && n_unsat > 0);
    assert_eq!(n_unknown, 0, "constant-source fp.to_real must never fence ({n_unknown})");
}
```
Match the exact `z3_outcome_arith` return type / disagreement idiom already in the file (`Z3::Unsat`/`Z3::Sat` are placeholders — use the file's actual enum/`match` shape from fp_oracle.rs:205-223).

- [ ] **Step 2: Run to verify it fails/builds**

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_to_real -- --nocapture 2>&1 | tail -25`
Expected: compiles; if any disagreement or `n_unknown>0`, it fails — fix the emitter, not the test. (Requires `z3` on PATH.)

- [ ] **Step 3: (only if it fails) debug via systematic-debugging**

If a disagreement fires, reproduce the single script, compare `shinri_outcome` vs z3, and trace to the offending guarded row / coeff. Do NOT weaken the test.

- [ ] **Step 4: Run to verify it passes**

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_to_real -- --nocapture 2>&1 | tail -8`
Expected: PASS, `n_sat>0 && n_unsat>0`, `n_unknown==0`.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(solver): z3 differential oracle for fp.to_real F16/F32 (constant-source, 0 unknown) (slice 9)"
```

---

### Task 7: Closeout — full regression, canary re-grep, clippy, docs

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs` / `lib.rs` doc comments only (mark fp.to_real admitted for eb≤8); optionally repoint the durable malformed-canary per `shinri-fence-canary-cross-slice`.

- [ ] **Step 1: Full workspace regression (the cross-slice net)**

Run: `cargo test --workspace 2>&1 | tail -25`
Expected: 0 failed. If a stale canary in another crate surfaces (per `shinri-fence-canary-cross-slice`), fix it in place and note it.

- [ ] **Step 2: Canary re-grep**

Run: `grep -rnE 'fp\.to_real|FpToReal' crates/*/src crates/*/tests | grep -iE 'crossing|fence|unknown|unsupported'`
Expected: only STAY sites (symbolic-to_fp / bare-Real / other-theory) and the updated doc comments remain; no live assertion pins fp.to_real (eb≤8) as crossing/Unknown.

- [ ] **Step 3: Clippy (0 net-new)**

Run: `cargo clippy --workspace --all-targets 2>&1 | grep -c warning`
Expected: no net-new warnings vs base (fix any introduced, e.g. `map_or`/`is_some_and`).

- [ ] **Step 4: Oracle sweep sanity (background)**

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle 2>&1 | tail -15`
Expected: all fp_oracle suites 0-disagreement (per memory, run long oracle suites yourself; this one is fast — constant-source).

- [ ] **Step 5: Update spec status + commit**

Edit the spec header `Status:` to `Implemented (slice 9 landed)`; update the design's §6 fence list note that fp.to_real eb≤8 is admitted.
```bash
git add -A
git commit -m "docs(qffp): mark slice-9 fp.to_real bridge landed; eb<=8 admitted, symbolic to_fp + eb>=11 still fenced (slice 9)"
```

---

## Self-Review

**Spec coverage:** §2.0 corrections → Tasks 2/3 (recognizer + both fences) ✓; §3 combined-solve → Task 3 dispatch ✓; §4 encoding → Task 1 (math) + Task 4 (guarded rows + channel) ✓; §5 NaN/∞ functionality → Task 5 (+ oracle pin Task 6) ✓; §6 scope fence (symbolic to_fp, eb≥11) → Task 2 recognizer + Task 3 fence arm ✓; §7 testing (oracle, e2e, canaries, workspace) → Tasks 4/5/6/7 ✓; §8 canary repoints A/B/C → Task 3 ✓; §10 model channel for r_x → automatic via `build_model` (opaque Real problem_var), exercised by the SAT e2e models.

**Placeholder scan:** the emitter code uses named placeholders (`declare_const_for_test`, `ctx_rne`, `Z3::Sat`) explicitly flagged to be replaced with the file's real idioms — each with a pointer to the exact existing site to copy. `fp_const_bits`/`collect_fp_to_real_terms`/`fresh_real_const` are small additions with stated bodies. No "TBD"/"handle edge cases" left.

**Type consistency:** `to_real_finite_row -> Option<FiniteRow>` with `coeffs: Vec<Rational>` (LSB-first) used identically in Tasks 1 and 4; `emit_to_real_bridge(&mut Encoder, &[TermId])` and `assert_eq_real`/`add_clause` consistent across Tasks 3–5; `fp_var_bits: FxHashMap<TermId, Vec<Var>>` and bit-index layout identical to the Global Constraints. Guard-clause polarity (negations of pattern-matching literals) consistent Tasks 4/5.

**Known risk carried forward:** the pre-clone term-minting vs post-replay clause-wiring split is the one integration hazard (per `shinri-fp-div-deep-circuits` — integration surprises). Task 3 lands the smallest version of it (constant arm) first to de-risk before Tasks 4/5 scale it.
