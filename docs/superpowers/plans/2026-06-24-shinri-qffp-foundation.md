# shinri QF_FP Foundation (core + parser) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make every QF_FP / QF_BVFP term — FP and `RoundingMode` sorts, FP literals/specials, the full FP operator set, and the conversion ops — parse and sort-check in `shinri-core` + `shinri-parser`, so later plans (circuits, solver wiring) have a complete term layer to build on.

**Architecture:** Add `Float(eb,sb)` and `RoundingMode` sorts, an FP-literal table mirroring the existing BV-literal table (`Context.bvs`), `RoundingMode` constants, and all FP `BuiltinOp` variants with result-sort checking in `check_builtin`. Extend the parser to recognize the `(_ FloatingPoint eb sb)` sort (plus `Float16/32/64/128` aliases), rounding-mode constants, the `(fp …)` constructor, the `(_ ±oo/±zero/NaN eb sb)` special literals, and the indexed conversion operators. No circuits, no solving — this plan ends at "well-sorted term DAG".

**Tech Stack:** Rust 2021, `shinri-core` (term/sort layer), `shinri-parser`, `shinri-num` (`Integer`/`Rational`), `rustc-hash`.

## Global Constraints

- Rust edition `2021`; workspace `rust-version = "1.96.0"`.
- `shinri-core` and `shinri-parser` keep their existing dependency sets — **do not add new runtime dependencies**.
- Out-of-scope / malformed input must surface as a recoverable `SortError` (core) or `Diagnostic` (parser) — **never a panic** on user input (`debug_assert!` for internal invariants only).
- FP sort layout is MSB→LSB `[ sign(1 bit) | exponent(eb bits) | trailing-significand(sb-1 bits) ]`; total width `W = eb + sb`. `sb` **includes** the hidden bit. Valid formats require `eb >= 2` and `sb >= 2`.
- Follow existing code patterns exactly: id types via the `u32_id!` macro (`ids.rs`), literal tables as `Vec` on `Context` indexed by a `u32_id`, sort-checking arms in `check_builtin`, parser dispatch in `parse_compound`/`parse_indexed_op`/`resolve_leaf`/`parse_sort`.

---

## File Structure

- `crates/shinri-core/src/ids.rs` — add `FpId` (index into the FP-literal table).
- `crates/shinri-core/src/term.rs` — add `RoundingMode` enum, `ConstVal::Float`/`ConstVal::Rm`, and all FP `BuiltinOp` variants.
- `crates/shinri-core/src/error.rs` — add `NotFloat`, `NotRoundingMode`, `FpIndex` to `SortError`.
- `crates/shinri-core/src/context.rs` — add the `fps` table, sort constructors/accessors, FP/RM constant constructors, and FP arms in `check_builtin`.
- `crates/shinri-parser/src/parser.rs` — FP sorts/aliases/RM sort, RM constants, `(fp …)`, special literals, conversion operators.

Tasks 1–4 are `shinri-core`; Tasks 5–9 are `shinri-parser`. Each task ends with a green test and a commit.

---

### Task 1: `Float` + `RoundingMode` sorts and the FP-literal table

**Files:**
- Modify: `crates/shinri-core/src/sort.rs` (add two `SortNode` variants)
- Modify: `crates/shinri-core/src/ids.rs` (add `FpId`)
- Modify: `crates/shinri-core/src/context.rs` (add `fps` field, sort constructors/accessors)
- Test: `crates/shinri-core/src/context.rs` (`#[cfg(test)] mod` at the bottom)

**Interfaces:**
- Produces: `SortNode::Float(u32, u32)`, `SortNode::RoundingMode`; `FpId` (via `u32_id!`); `Context.fp_sort(&mut self, eb: u32, sb: u32) -> SortId`; `Context.rm_sort(&mut self) -> SortId`; `Context.fp_widths(&self, s: SortId) -> Option<(u32, u32)>`.

- [ ] **Step 1: Write the failing test**

Add to the `#[cfg(test)] mod tests` block in `crates/shinri-core/src/context.rs`:

```rust
#[test]
fn fp_and_rm_sorts_intern_and_roundtrip() {
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let f32_again = ctx.fp_sort(8, 24);
    let f64 = ctx.fp_sort(11, 53);
    assert_eq!(f32, f32_again, "equal FP sorts must intern to the same SortId");
    assert_ne!(f32, f64, "different widths must be different sorts");
    assert_eq!(ctx.fp_widths(f32), Some((8, 24)));
    assert_eq!(ctx.fp_widths(f64), Some((11, 53)));
    assert_eq!(ctx.fp_widths(ctx.bool_sort()), None);

    let rm = ctx.rm_sort();
    let rm2 = ctx.rm_sort();
    assert_eq!(rm, rm2, "RoundingMode sort must be unique");
    assert_eq!(ctx.fp_widths(rm), None);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core fp_and_rm_sorts_intern_and_roundtrip`
Expected: FAIL — `no method named fp_sort`/`rm_sort`/`fp_widths`.

- [ ] **Step 3: Add the `SortNode` variants**

In `crates/shinri-core/src/sort.rs`, extend the enum (keep existing variants):

```rust
pub enum SortNode {
    Bool,
    Int,
    Real,
    String,
    Uninterpreted(SymbolId),
    Array(crate::ids::SortId, crate::ids::SortId),
    BitVec(u32),
    /// (_ FloatingPoint eb sb): eb = exponent bits, sb = significand bits
    /// (including the hidden bit). Total width eb + sb. Requires eb >= 2, sb >= 2.
    Float(u32, u32),
    /// The RoundingMode sort (5 enumerated values; see term::RoundingMode).
    RoundingMode,
}
```

- [ ] **Step 4: Add the `FpId` id type**

In `crates/shinri-core/src/ids.rs`, next to `u32_id!(BvId);`:

```rust
// Index into `Context.fps` (the FP literal table), analogous to `BvId`.
u32_id!(FpId);
```

- [ ] **Step 5: Add the `fps` table and sort constructors/accessors**

In `crates/shinri-core/src/context.rs`: add the field to the `Context` struct (next to `bvs`):

```rust
    /// FP literal table: (eb, sb, bits) where bits is the W = eb+sb bit pattern,
    /// laid out MSB->LSB as [sign | exponent | trailing-significand].
    fps: Vec<(u32, u32, Integer)>,
```

Initialize it in `Context::new()` (next to `bvs: Vec::new(),`): `fps: Vec::new(),`.

Add these methods in the same `impl Context` block as `bv_sort`:

```rust
    /// Intern the (_ FloatingPoint eb sb) sort. Requires eb >= 2 and sb >= 2.
    pub fn fp_sort(&mut self, eb: u32, sb: u32) -> SortId {
        debug_assert!(eb >= 2 && sb >= 2, "FloatingPoint requires eb>=2, sb>=2");
        self.intern_sort(SortNode::Float(eb, sb))
    }

    /// Intern the RoundingMode sort.
    pub fn rm_sort(&mut self) -> SortId {
        self.intern_sort(SortNode::RoundingMode)
    }

    /// (eb, sb) of a Float sort, or None if `s` is not a Float sort.
    pub fn fp_widths(&self, s: SortId) -> Option<(u32, u32)> {
        match self.sort_node(s) {
            SortNode::Float(eb, sb) => Some((*eb, *sb)),
            _ => None,
        }
    }
```

(Ensure `use shinri_num::Integer;` is already in scope in `context.rs` — it is, since `mk_bv_const` uses it.)

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo test -p shinri-core fp_and_rm_sorts_intern_and_roundtrip`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-core/src/sort.rs crates/shinri-core/src/ids.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): Float and RoundingMode sorts + FP literal table"
```

---

### Task 2: FP and RoundingMode constants

**Files:**
- Modify: `crates/shinri-core/src/term.rs` (add `RoundingMode` enum + `ConstVal` variants)
- Modify: `crates/shinri-core/src/context.rs` (constant constructors + accessors)
- Test: `crates/shinri-core/src/context.rs`

**Interfaces:**
- Consumes: `FpId`, `Context.fps`, `fp_sort`, `rm_sort` (Task 1).
- Produces:
  - `term::RoundingMode { Rne, Rna, Rtp, Rtn, Rtz }` (Copy).
  - `ConstVal::Float(FpId)`, `ConstVal::Rm(RoundingMode)`.
  - `Context.mk_fp_const(&mut self, eb: u32, sb: u32, bits: Integer) -> TermId`.
  - `Context.mk_rm_const(&mut self, rm: RoundingMode) -> TermId`.
  - `Context.fp_const_value(&self, t: TermId) -> Option<(u32, u32, &Integer)>`.
  - `Context.rm_const_value(&self, t: TermId) -> Option<RoundingMode>`.

- [ ] **Step 1: Write the failing test**

Add to the test module in `crates/shinri-core/src/context.rs`:

```rust
#[test]
fn fp_and_rm_constants_roundtrip() {
    use crate::term::RoundingMode;
    use shinri_num::Integer;
    let mut ctx = Context::new();

    // +zero in Float32 is all zero bits.
    let pz = ctx.mk_fp_const(8, 24, Integer::zero());
    let pz_again = ctx.mk_fp_const(8, 24, Integer::zero());
    assert_eq!(pz, pz_again, "identical FP consts must be interned equal");
    assert_eq!(ctx.sort_of(pz), ctx.fp_sort(8, 24));
    let (eb, sb, bits) = ctx.fp_const_value(pz).expect("fp const");
    assert_eq!((eb, sb), (8, 24));
    assert!(bits.is_zero());

    let r = ctx.mk_rm_const(RoundingMode::Rne);
    assert_eq!(ctx.sort_of(r), ctx.rm_sort());
    assert_eq!(ctx.rm_const_value(r), Some(RoundingMode::Rne));
    assert_eq!(ctx.rm_const_value(pz), None);
    assert_eq!(ctx.fp_const_value(r), None);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core fp_and_rm_constants_roundtrip`
Expected: FAIL — `RoundingMode` not found / `mk_fp_const` undefined.

- [ ] **Step 3: Add the `RoundingMode` enum and `ConstVal` variants**

In `crates/shinri-core/src/term.rs`, add (near `ConstVal`):

```rust
/// The five SMT-LIB rounding modes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum RoundingMode {
    /// roundNearestTiesToEven (RNE)
    Rne,
    /// roundNearestTiesToAway (RNA)
    Rna,
    /// roundTowardPositive (RTP)
    Rtp,
    /// roundTowardNegative (RTN)
    Rtn,
    /// roundTowardZero (RTZ)
    Rtz,
}
```

Extend `ConstVal` (keep existing variants), referencing the new `FpId`:

```rust
pub enum ConstVal {
    Bool(bool),
    Num(RatId),
    BitVec(BvId),
    String(StringId),
    /// An FP literal; references `Context.fps`.
    Float(FpId),
    /// A rounding-mode constant.
    Rm(RoundingMode),
}
```

Make sure `FpId` is imported in `term.rs` alongside `BvId` (e.g. `use crate::ids::{BvId, FpId, RatId, StringId, ...};`).

- [ ] **Step 4: Add the constant constructors and accessors**

In `crates/shinri-core/src/context.rs`, in the same `impl Context` block as `mk_bv_const`:

```rust
    /// Intern an FP literal of sort (eb, sb) with the given W = eb+sb bit pattern.
    pub fn mk_fp_const(&mut self, eb: u32, sb: u32, bits: Integer) -> TermId {
        let fp_id = match self
            .fps
            .iter()
            .position(|(e, s, v)| *e == eb && *s == sb && *v == bits)
        {
            Some(idx) => FpId::new(idx as u32),
            None => {
                let id = FpId::new(self.fps.len() as u32);
                self.fps.push((eb, sb, bits));
                id
            }
        };
        let sort = self.fp_sort(eb, sb);
        let val = ConstVal::Float(fp_id);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    /// Intern a rounding-mode constant.
    pub fn mk_rm_const(&mut self, rm: crate::term::RoundingMode) -> TermId {
        let sort = self.rm_sort();
        let val = ConstVal::Rm(rm);
        self.intern_with_key(TermKey::Const { val, sort }, TermNode::Const { val, sort })
    }

    /// (eb, sb, bits) of an FP literal term, or None.
    pub fn fp_const_value(&self, t: TermId) -> Option<(u32, u32, &Integer)> {
        match self.term_node(t) {
            TermNode::Const { val: ConstVal::Float(id), .. } => {
                let (e, s, v) = &self.fps[id.index()];
                Some((*e, *s, v))
            }
            _ => None,
        }
    }

    /// The rounding mode of an RM constant term, or None.
    pub fn rm_const_value(&self, t: TermId) -> Option<crate::term::RoundingMode> {
        match self.term_node(t) {
            TermNode::Const { val: ConstVal::Rm(rm), .. } => Some(*rm),
            _ => None,
        }
    }
```

Ensure `FpId` and `ConstVal` are imported in `context.rs` (extend the existing `use crate::ids::…` / `use crate::term::…` lines to include `FpId` and `ConstVal::Float`/`Rm` are reachable via `ConstVal`).

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-core fp_and_rm_constants_roundtrip`
Expected: PASS.

- [ ] **Step 6: Verify exhaustive `match ConstVal` sites still compile**

Run: `cargo build -p shinri-core`
Expected: builds. If any `match` on `ConstVal` is now non-exhaustive (e.g. a `Debug`/print helper), add `ConstVal::Float(_)`/`ConstVal::Rm(_)` arms that format as `"<fp>"`/`"<rm>"` for now (model/printing is a later plan).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-core/src/term.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): FP and RoundingMode constants + accessors"
```

---

### Task 3: FP arithmetic / comparison / classification ops + sort-checking

**Files:**
- Modify: `crates/shinri-core/src/term.rs` (add `BuiltinOp` variants)
- Modify: `crates/shinri-core/src/error.rs` (add `SortError` variants)
- Modify: `crates/shinri-core/src/context.rs` (`require_fp`, `require_rm`, `check_builtin` arms)
- Test: `crates/shinri-core/src/context.rs`

**Interfaces:**
- Consumes: `fp_sort`, `rm_sort`, `fp_widths`, `mk_app` (Tasks 1–2).
- Produces these `BuiltinOp` variants: `FpAbs, FpNeg, FpAdd, FpSub, FpMul, FpDiv, FpFma, FpSqrt, FpRem, FpRoundToIntegral, FpMin, FpMax, FpLeq, FpLt, FpGeq, FpGt, FpEq, FpIsNormal, FpIsSubnormal, FpIsZero, FpIsInfinite, FpIsNaN, FpIsNegative, FpIsPositive, FpFromBits`. Also `SortError::{NotFloat, NotRoundingMode, FpIndex}` and private `Context::require_fp`/`require_rm`.

- [ ] **Step 1: Write the failing test**

Add to the test module in `crates/shinri-core/src/context.rs`:

```rust
#[test]
fn fp_arith_compare_classify_sortcheck() {
    use crate::term::RoundingMode;
    use crate::{BuiltinOp, Op};
    use shinri_num::Integer;
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let xf = ctx.declare_fun("x", &[], f32);
    let yf = ctx.declare_fun("y", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
    let rne = ctx.mk_rm_const(RoundingMode::Rne);

    // fp.add : (RM, F, F) -> F
    let add = ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rne, x, y]).unwrap();
    assert_eq!(ctx.sort_of(add), f32);

    // fp.neg : (F) -> F ; fp.abs : (F) -> F
    let neg = ctx.mk_app(Op::Builtin(BuiltinOp::FpNeg), &[x]).unwrap();
    assert_eq!(ctx.sort_of(neg), f32);

    // fp.leq : (F, F) -> Bool ; fp.isNaN : (F) -> Bool
    let leq = ctx.mk_app(Op::Builtin(BuiltinOp::FpLeq), &[x, y]).unwrap();
    assert_eq!(ctx.sort_of(leq), ctx.bool_sort());
    let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[x]).unwrap();
    assert_eq!(ctx.sort_of(isnan), ctx.bool_sort());

    // fp : (BV1, BV8, BV23) -> Float(8,24)
    let b1 = ctx.mk_bv_const(1, Integer::zero());
    let b8 = ctx.mk_bv_const(8, Integer::zero());
    let b23 = ctx.mk_bv_const(23, Integer::zero());
    let ctor = ctx.mk_app(Op::Builtin(BuiltinOp::FpFromBits), &[b1, b8, b23]).unwrap();
    assert_eq!(ctx.sort_of(ctor), f32);

    // width mismatch on fp.add operands must be a SortError, not a panic
    let f64 = ctx.fp_sort(11, 53);
    let zf = ctx.declare_fun("z", &[], f64);
    let z = ctx.mk_app(Op::Uninterpreted(zf), &[]).unwrap();
    assert!(ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rne, x, z]).is_err());
    // missing rounding mode (passing a Float where RM expected) must error
    assert!(ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[x, x, y]).is_err());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core fp_arith_compare_classify_sortcheck`
Expected: FAIL — `FpAdd` etc. not found.

- [ ] **Step 3: Add the `BuiltinOp` variants**

In `crates/shinri-core/src/term.rs`, extend `BuiltinOp` (add after the String ops, keep all existing):

```rust
    // Floating-point — arithmetic. Rounded ops take a RoundingMode as arg 0.
    FpAbs, FpNeg,                 // (F) -> F
    FpAdd, FpSub, FpMul, FpDiv,   // (RM, F, F) -> F
    FpFma,                        // (RM, F, F, F) -> F
    FpSqrt, FpRoundToIntegral,    // (RM, F) -> F
    FpRem, FpMin, FpMax,          // (F, F) -> F
    // Floating-point — comparisons: (F, F) -> Bool
    FpLeq, FpLt, FpGeq, FpGt, FpEq,
    // Floating-point — classification: (F) -> Bool
    FpIsNormal, FpIsSubnormal, FpIsZero, FpIsInfinite, FpIsNaN, FpIsNegative, FpIsPositive,
    // Floating-point — bit constructor: (BV1, BVeb, BV(sb-1)) -> Float(eb, sb)
    FpFromBits,
```

- [ ] **Step 4: Add the `SortError` variants**

In `crates/shinri-core/src/error.rs`, extend `SortError` (keep existing):

```rust
    /// An argument was expected to be a FloatingPoint sort but was not.
    NotFloat,
    /// An argument was expected to be the RoundingMode sort but was not.
    NotRoundingMode,
    /// A floating-point indexed parameter (eb/sb/m) is out of range, or `fp`
    /// constructor operand widths are inconsistent.
    FpIndex,
```

- [ ] **Step 5: Add `require_fp` / `require_rm` helpers**

In `crates/shinri-core/src/context.rs`, next to `require_bv`:

```rust
    /// (eb, sb) of a Float-sorted term, or `SortError::NotFloat`.
    fn require_fp(&self, t: TermId) -> Result<(u32, u32), SortError> {
        self.fp_widths(self.sort_of(t)).ok_or(SortError::NotFloat)
    }

    /// Ok(()) iff `t` has the RoundingMode sort, else `SortError::NotRoundingMode`.
    fn require_rm(&mut self, t: TermId) -> Result<(), SortError> {
        let rm = self.rm_sort();
        if self.sort_of(t) == rm {
            Ok(())
        } else {
            Err(SortError::NotRoundingMode)
        }
    }
```

- [ ] **Step 6: Add the sort-checking arms**

In `check_builtin` (in `crates/shinri-core/src/context.rs`), add these match arms before the final closing brace of the `match b { … }` (alongside the existing `Bv*`/`Str*` arms). `bool_s` is already in scope as a parameter:

```rust
            // ── Floating-point: arithmetic ────────────────────────────────────
            FpAbs | FpNeg => {
                expect_arity(args, 1)?;
                let (eb, sb) = self.require_fp(args[0])?;
                Ok(self.fp_sort(eb, sb))
            }
            FpAdd | FpSub | FpMul | FpDiv => {
                expect_arity(args, 3)?;
                self.require_rm(args[0])?;
                let (eb, sb) = self.require_fp(args[1])?;
                let (eb2, sb2) = self.require_fp(args[2])?;
                if (eb, sb) != (eb2, sb2) {
                    return Err(SortError::Mismatch {
                        expected: self.sort_of(args[1]),
                        found: self.sort_of(args[2]),
                    });
                }
                Ok(self.fp_sort(eb, sb))
            }
            FpFma => {
                expect_arity(args, 4)?;
                self.require_rm(args[0])?;
                let (eb, sb) = self.require_fp(args[1])?;
                for &a in &args[2..4] {
                    let (e, s) = self.require_fp(a)?;
                    if (e, s) != (eb, sb) {
                        return Err(SortError::Mismatch {
                            expected: self.sort_of(args[1]),
                            found: self.sort_of(a),
                        });
                    }
                }
                Ok(self.fp_sort(eb, sb))
            }
            FpSqrt | FpRoundToIntegral => {
                expect_arity(args, 2)?;
                self.require_rm(args[0])?;
                let (eb, sb) = self.require_fp(args[1])?;
                Ok(self.fp_sort(eb, sb))
            }
            FpRem | FpMin | FpMax => {
                expect_arity(args, 2)?;
                let (eb, sb) = self.require_fp(args[0])?;
                let (eb2, sb2) = self.require_fp(args[1])?;
                if (eb, sb) != (eb2, sb2) {
                    return Err(SortError::Mismatch {
                        expected: self.sort_of(args[0]),
                        found: self.sort_of(args[1]),
                    });
                }
                Ok(self.fp_sort(eb, sb))
            }
            // ── Floating-point: comparisons → Bool ────────────────────────────
            FpLeq | FpLt | FpGeq | FpGt | FpEq => {
                expect_arity(args, 2)?;
                let (eb, sb) = self.require_fp(args[0])?;
                let (eb2, sb2) = self.require_fp(args[1])?;
                if (eb, sb) != (eb2, sb2) {
                    return Err(SortError::Mismatch {
                        expected: self.sort_of(args[0]),
                        found: self.sort_of(args[1]),
                    });
                }
                Ok(bool_s)
            }
            // ── Floating-point: classification → Bool ─────────────────────────
            FpIsNormal | FpIsSubnormal | FpIsZero | FpIsInfinite | FpIsNaN
            | FpIsNegative | FpIsPositive => {
                expect_arity(args, 1)?;
                self.require_fp(args[0])?;
                Ok(bool_s)
            }
            // ── Floating-point: bit constructor ───────────────────────────────
            FpFromBits => {
                expect_arity(args, 3)?;
                let w_sign = self.require_bv(args[0])?;
                let w_exp = self.require_bv(args[1])?;
                let w_sig = self.require_bv(args[2])?;
                if w_sign != 1 {
                    return Err(SortError::FpIndex);
                }
                let eb = w_exp;
                let sb = w_sig + 1;
                if eb < 2 || sb < 2 {
                    return Err(SortError::FpIndex);
                }
                Ok(self.fp_sort(eb, sb))
            }
```

- [ ] **Step 7: Run test to verify it passes**

Run: `cargo test -p shinri-core fp_arith_compare_classify_sortcheck`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add crates/shinri-core/src/term.rs crates/shinri-core/src/error.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): FP arithmetic/compare/classify ops + sort-checking"
```

---

### Task 4: FP conversion ops + sort-checking

**Files:**
- Modify: `crates/shinri-core/src/term.rs` (indexed conversion `BuiltinOp` variants)
- Modify: `crates/shinri-core/src/context.rs` (`check_builtin` arms)
- Test: `crates/shinri-core/src/context.rs`

**Interfaces:**
- Consumes: `require_fp`, `require_rm`, `require_bv`, `fp_sort`, `bv_sort`, `real_sort` (Tasks 1–3).
- Produces: `BuiltinOp::ToFp { eb: u32, sb: u32 }`, `BuiltinOp::ToFpUnsigned { eb: u32, sb: u32 }`, `BuiltinOp::FpToUbv(u32)`, `BuiltinOp::FpToSbv(u32)`, `BuiltinOp::FpToReal`. Sort rules:
  - `ToFp{eb,sb}` with **1 arg** (a `BitVec(eb+sb)`) → bitcast → `Float(eb,sb)`.
  - `ToFp{eb,sb}` with **2 args** `(RM, X)` where `X` is `Float(_,_)`, any `BitVec`, or `Real` → `Float(eb,sb)`.
  - `ToFpUnsigned{eb,sb}` = `(RM, BitVec)` → `Float(eb,sb)`.
  - `FpToUbv(m)` / `FpToSbv(m)` = `(RM, Float)` → `BitVec(m)`.
  - `FpToReal` = `(Float)` → `Real`.

- [ ] **Step 1: Write the failing test**

Add to the test module in `crates/shinri-core/src/context.rs`:

```rust
#[test]
fn fp_conversion_sortcheck() {
    use crate::term::RoundingMode;
    use crate::{BuiltinOp, Op};
    use shinri_num::Integer;
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let rne = ctx.mk_rm_const(RoundingMode::Rne);

    // bitcast: (_ to_fp 8 24) over a BV32 (1 arg, no RM) -> Float(8,24)
    let b32 = ctx.mk_bv_const(32, Integer::zero());
    let cast = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[b32]).unwrap();
    assert_eq!(ctx.sort_of(cast), f32);

    // FP->FP: (_ to_fp 11 53) RM Float32 -> Float64
    let f64 = ctx.fp_sort(11, 53);
    let widen = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 11, sb: 53 }), &[rne, x]).unwrap();
    assert_eq!(ctx.sort_of(widen), f64);

    // fp.to_sbv 16 : (RM, Float) -> BV16
    let tosbv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToSbv(16)), &[rne, x]).unwrap();
    assert_eq!(ctx.sort_of(tosbv), ctx.bv_sort(16));

    // fp.to_real : (Float) -> Real
    let toreal = ctx.mk_app(Op::Builtin(BuiltinOp::FpToReal), &[x]).unwrap();
    assert_eq!(ctx.sort_of(toreal), ctx.real_sort());

    // bitcast width mismatch (BV31 into Float(8,24)=32 bits) must error
    let b31 = ctx.mk_bv_const(31, Integer::zero());
    assert!(ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[b31]).is_err());
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-core fp_conversion_sortcheck`
Expected: FAIL — `ToFp` etc. not found.

- [ ] **Step 3: Add the conversion `BuiltinOp` variants**

In `crates/shinri-core/src/term.rs`, extend `BuiltinOp` (after `FpFromBits`):

```rust
    // Floating-point — conversions (indexed; parameters carried in the op).
    /// (_ to_fp eb sb): bitcast from BV(eb+sb) [1 arg], or RM-rounded from
    /// Float / signed-int BV / Real [2 args: (RM, X)].
    ToFp { eb: u32, sb: u32 },
    /// (_ to_fp_unsigned eb sb): (RM, BV) unsigned-int -> Float(eb, sb).
    ToFpUnsigned { eb: u32, sb: u32 },
    /// (_ fp.to_ubv m): (RM, Float) -> BV(m).
    FpToUbv(u32),
    /// (_ fp.to_sbv m): (RM, Float) -> BV(m).
    FpToSbv(u32),
    /// fp.to_real: (Float) -> Real.
    FpToReal,
```

- [ ] **Step 4: Add the sort-checking arms**

In `check_builtin`, add alongside the Task 3 FP arms. `real_s` is already bound near the top of `check_builtin` (`let real_s = self.real_sort();`):

```rust
            // ── Floating-point: conversions ───────────────────────────────────
            ToFp { eb, sb } => {
                match args.len() {
                    // bitcast: a single BV of width eb+sb
                    1 => {
                        let n = self.require_bv(args[0])?;
                        if n != eb + sb {
                            return Err(SortError::FpIndex);
                        }
                        Ok(self.fp_sort(eb, sb))
                    }
                    // (RM, X): X is Float, BV (signed int), or Real
                    2 => {
                        self.require_rm(args[0])?;
                        let s1 = self.sort_of(args[1]);
                        let ok = self.fp_widths(s1).is_some()
                            || self.bv_width(s1).is_some()
                            || s1 == real_s;
                        if !ok {
                            return Err(SortError::NotApplicable);
                        }
                        Ok(self.fp_sort(eb, sb))
                    }
                    n => Err(SortError::Arity { expected: 2, found: n }),
                }
            }
            ToFpUnsigned { eb, sb } => {
                expect_arity(args, 2)?;
                self.require_rm(args[0])?;
                self.require_bv(args[1])?;
                Ok(self.fp_sort(eb, sb))
            }
            FpToUbv(m) | FpToSbv(m) => {
                expect_arity(args, 2)?;
                if m < 1 {
                    return Err(SortError::FpIndex);
                }
                self.require_rm(args[0])?;
                self.require_fp(args[1])?;
                Ok(self.bv_sort(m))
            }
            FpToReal => {
                expect_arity(args, 1)?;
                self.require_fp(args[0])?;
                Ok(real_s)
            }
```

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-core fp_conversion_sortcheck`
Expected: PASS.

- [ ] **Step 6: Verify the whole crate (exhaustive matches over `BuiltinOp`)**

Run: `cargo build -p shinri-core && cargo test -p shinri-core`
Expected: builds and all tests pass. If a non-`check_builtin` `match` over `BuiltinOp` exists elsewhere in `shinri-core` and is now non-exhaustive, add the missing FP arms there (there should be none in core beyond `check_builtin`).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-core/src/term.rs crates/shinri-core/src/context.rs
git commit -m "feat(core): FP conversion ops + sort-checking"
```

---

### Task 5: Parse `(_ FloatingPoint eb sb)`, `FloatNN` aliases, and `RoundingMode` sort

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs` (`parse_sort`)
- Test: `crates/shinri-parser/src/parser.rs` (`#[cfg(test)] mod` — follow the existing test layout in this file)

**Interfaces:**
- Consumes: `Context::fp_sort`, `rm_sort` (Tasks 1–2).
- Produces: `parse_sort` recognizes `(_ FloatingPoint eb sb)`, `Float16/32/64/128`, `RoundingMode`.

- [ ] **Step 1: Write the failing test**

Add a parser sort test. Use the crate's existing test-helper pattern; if the file has no sort-parsing helper, add this self-contained one to the test module in `crates/shinri-parser/src/parser.rs`:

```rust
#[test]
fn parse_fp_and_rm_sorts() {
    use shinri_core::Context;
    fn sort_of_str(src: &str) -> (Context, shinri_core::SortId) {
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        let s = p.parse_sort(&mut ctx).expect("parse sort");
        (ctx, s)
    }
    let (ctx, s) = sort_of_str("(_ FloatingPoint 8 24)");
    assert_eq!(ctx.fp_widths(s), Some((8, 24)));

    let (ctx, s) = sort_of_str("Float64");
    assert_eq!(ctx.fp_widths(s), Some((11, 53)));

    let (ctx, s) = sort_of_str("Float16");
    assert_eq!(ctx.fp_widths(s), Some((5, 11)));

    let (mut ctx, s) = sort_of_str("RoundingMode");
    assert_eq!(s, ctx.rm_sort());
}
```

(If `Parser::new`/`parse_sort` are not `pub`, mirror however the existing sort tests in this file construct a parser; the assertions stay the same.)

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser parse_fp_and_rm_sorts`
Expected: FAIL — `FloatingPoint`/`Float64`/`RoundingMode` unsupported.

- [ ] **Step 3: Handle the indexed `(_ FloatingPoint eb sb)` sort**

In `parse_sort`, inside the `"_" =>` arm (which currently only handles `BitVec`), replace the single-keyword check with a dispatch:

```rust
            "_" => {
                let (kw, ksp) = self.expect_symbol()?;
                match kw.as_str() {
                    "BitVec" => {
                        let width = self.expect_numeral_u32()?;
                        if width == 0 {
                            return Err(Diagnostic::new(sp, "BitVec width must be >= 1"));
                        }
                        ctx.bv_sort(width)
                    }
                    "FloatingPoint" => {
                        let eb = self.expect_numeral_u32()?;
                        let sb = self.expect_numeral_u32()?;
                        if eb < 2 || sb < 2 {
                            return Err(Diagnostic::new(sp, "FloatingPoint requires eb>=2, sb>=2"));
                        }
                        ctx.fp_sort(eb, sb)
                    }
                    other => {
                        return Err(Diagnostic::new(
                            ksp,
                            format!("unsupported indexed sort identifier {other}"),
                        ));
                    }
                }
            }
```

- [ ] **Step 4: Handle the named aliases and `RoundingMode`**

In `parse_sort`, in the non-parenthesized name `match name.as_str()` (where `"Bool"`, `"Int"`, … are handled), add:

```rust
        "Float16" => Ok(ctx.fp_sort(5, 11)),
        "Float32" => Ok(ctx.fp_sort(8, 24)),
        "Float64" => Ok(ctx.fp_sort(11, 53)),
        "Float128" => Ok(ctx.fp_sort(15, 113)),
        "RoundingMode" => Ok(ctx.rm_sort()),
```

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-parser parse_fp_and_rm_sorts`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-parser/src/parser.rs
git commit -m "feat(parser): FloatingPoint/FloatNN/RoundingMode sorts"
```

---

### Task 6: Parse rounding-mode constants

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs` (`resolve_leaf`)
- Test: `crates/shinri-parser/src/parser.rs`

**Interfaces:**
- Consumes: `Context::mk_rm_const`, `term::RoundingMode` (Task 2).
- Produces: leaf symbols `RNE`/`roundNearestTiesToEven`, `RNA`/`roundNearestTiesToAway`, `RTP`/`roundTowardPositive`, `RTN`/`roundTowardNegative`, `RTZ`/`roundTowardZero` resolve to RM constants.

- [ ] **Step 1: Write the failing test**

Add to the parser test module:

```rust
#[test]
fn parse_rounding_mode_constants() {
    use shinri_core::{Context, term::RoundingMode};
    fn rm_of(src: &str) -> Option<RoundingMode> {
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        let t = p.parse_term_pub(&mut ctx).expect("parse term");
        ctx.rm_const_value(t)
    }
    assert_eq!(rm_of("RNE"), Some(RoundingMode::Rne));
    assert_eq!(rm_of("roundNearestTiesToEven"), Some(RoundingMode::Rne));
    assert_eq!(rm_of("RNA"), Some(RoundingMode::Rna));
    assert_eq!(rm_of("roundNearestTiesToAway"), Some(RoundingMode::Rna));
    assert_eq!(rm_of("RTP"), Some(RoundingMode::Rtp));
    assert_eq!(rm_of("roundTowardPositive"), Some(RoundingMode::Rtp));
    assert_eq!(rm_of("RTN"), Some(RoundingMode::Rtn));
    assert_eq!(rm_of("roundTowardNegative"), Some(RoundingMode::Rtn));
    assert_eq!(rm_of("RTZ"), Some(RoundingMode::Rtz));
    assert_eq!(rm_of("roundTowardZero"), Some(RoundingMode::Rtz));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser parse_rounding_mode_constants`
Expected: FAIL — `undeclared symbol RNE`.

- [ ] **Step 3: Resolve RM constants in `resolve_leaf`**

In `resolve_leaf`, extend the `match name { "true" => …, "false" => …, _ => {} }` block with the rounding-mode names (before the `lookup_fun` fallback):

```rust
        match name {
            "true" => return Ok(ctx.mk_const_bool(true)),
            "false" => return Ok(ctx.mk_const_bool(false)),
            "RNE" | "roundNearestTiesToEven" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rne));
            }
            "RNA" | "roundNearestTiesToAway" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rna));
            }
            "RTP" | "roundTowardPositive" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rtp));
            }
            "RTN" | "roundTowardNegative" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rtn));
            }
            "RTZ" | "roundTowardZero" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rtz));
            }
            _ => {}
        }
```

(If `term::RoundingMode` is not re-exported at the crate root, use the full path `shinri_core::term::RoundingMode` as shown.)

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-parser parse_rounding_mode_constants`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-parser/src/parser.rs
git commit -m "feat(parser): rounding-mode constants"
```

---

### Task 7: Parse the `(fp …)` constructor and `(_ ±oo/±zero/NaN eb sb)` special literals

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs` (`builtin_for` for `fp`; the `"_"` head branch in `parse_compound` for specials; a `fp_special_bits` helper)
- Test: `crates/shinri-parser/src/parser.rs`

**Interfaces:**
- Consumes: `BuiltinOp::FpFromBits` (Task 3), `Context::mk_fp_const` (Task 2), `Integer` arithmetic (`shinri-num`).
- Produces: `(fp s e m)` → `FpFromBits` application; `(_ +oo eb sb)`, `(_ -oo eb sb)`, `(_ +zero eb sb)`, `(_ -zero eb sb)`, `(_ NaN eb sb)` → interned FP constants with canonical bit patterns. Adds a free function `fp_special_bits(eb: u32, sb: u32, kind: FpSpecial) -> Integer` and `enum FpSpecial { PosInf, NegInf, PosZero, NegZero, Nan }`.

- [ ] **Step 1: Write the failing test**

Add to the parser test module:

```rust
#[test]
fn parse_fp_constructor_and_specials() {
    use shinri_core::Context;
    fn parse(src: &str) -> (Context, shinri_core::TermId) {
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        let t = p.parse_term_pub(&mut ctx).expect("parse term");
        (ctx, t)
    }

    // (fp #b0 #b00000000 #b00000000000000000000000) is +zero in Float32.
    let (ctx, t) = parse("(fp #b0 #b00000000 #b00000000000000000000000)");
    assert_eq!(ctx.fp_widths(ctx.sort_of(t)), Some((8, 24)));

    // (_ +zero 8 24): all bits zero.
    let (ctx, t) = parse("(_ +zero 8 24)");
    let (eb, sb, bits) = ctx.fp_const_value(t).expect("fp const");
    assert_eq!((eb, sb), (8, 24));
    assert!(bits.is_zero(), "+zero must be all-zero bits");

    // (_ -zero 8 24): only the sign bit (bit 31) set => 2^31.
    let (ctx, t) = parse("(_ -zero 8 24)");
    let (_, _, bits) = ctx.fp_const_value(t).unwrap();
    assert_eq!(bits.to_i128(), Some(1i128 << 31));

    // (_ +oo 8 24): exp all ones, sig 0 => 0xFF << 23 = 0x7F800000.
    let (ctx, t) = parse("(_ +oo 8 24)");
    let (_, _, bits) = ctx.fp_const_value(t).unwrap();
    assert_eq!(bits.to_i128(), Some(0x7F80_0000));

    // (_ -oo 8 24): sign + exp all ones => 0xFF800000.
    let (ctx, t) = parse("(_ -oo 8 24)");
    let (_, _, bits) = ctx.fp_const_value(t).unwrap();
    assert_eq!(bits.to_i128(), Some(0xFF80_0000));

    // (_ NaN 8 24): exp all ones, quiet bit (sig MSB, bit 22) set => 0x7FC00000.
    let (ctx, t) = parse("(_ NaN 8 24)");
    let (_, _, bits) = ctx.fp_const_value(t).unwrap();
    assert_eq!(bits.to_i128(), Some(0x7FC0_0000));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser parse_fp_constructor_and_specials`
Expected: FAIL — `fp` undeclared and `(_ +zero …)` unsupported.

- [ ] **Step 3: Add `fp` to `builtin_for`**

In `builtin_for`, add (next to the BV op mappings):

```rust
        "fp" => Fp,
```

…where `Fp` resolves to `BuiltinOp::FpFromBits`. Because the `use shinri_core::BuiltinOp::*;` glob is in scope, write it as the actual variant name: `"fp" => FpFromBits,`.

- [ ] **Step 4: Add the canonical-bits helper**

Add these free items near the top of `crates/shinri-parser/src/parser.rs` (module scope):

```rust
/// IEEE special-value kinds that the `(_ <kind> eb sb)` syntax can name.
#[derive(Clone, Copy)]
enum FpSpecial { PosInf, NegInf, PosZero, NegZero, Nan }

/// 2^k as an Integer (k may exceed 127, so build it generally).
fn pow2(k: u32) -> shinri_core::num::Integer {
    use shinri_core::num::Integer;
    let mut acc = Integer::one();
    let two = Integer::from(2u64);
    for _ in 0..k {
        acc = acc * two.clone();
    }
    acc
}

/// Canonical W = eb+sb bit pattern for an FP special value.
/// Layout MSB->LSB: [ sign(1) | exp(eb) | trailing-sig(sb-1) ].
fn fp_special_bits(eb: u32, sb: u32, kind: FpSpecial) -> shinri_core::num::Integer {
    use shinri_core::num::Integer;
    let w = eb + sb;
    let sign_bit = pow2(w - 1);                 // bit (W-1)
    let exp_all_ones = (pow2(eb) - Integer::one()) * pow2(sb - 1); // exp field set, sig 0
    let quiet_bit = pow2(sb - 2);               // MSB of the (sb-1)-bit trailing sig
    match kind {
        FpSpecial::PosZero => Integer::zero(),
        FpSpecial::NegZero => sign_bit,
        FpSpecial::PosInf => exp_all_ones,
        FpSpecial::NegInf => sign_bit + exp_all_ones,
        FpSpecial::Nan => exp_all_ones + quiet_bit, // sign 0, canonical quiet NaN
    }
}
```

> The path `shinri_core::num::Integer` assumes `shinri-core` re-exports `shinri-num` as `num` (it interns `Integer` for BV/Rational already). If that re-export does not exist, add `shinri-num` to `crates/shinri-parser/Cargo.toml` `[dependencies]` and use `shinri_num::Integer`; the parser already constructs `Integer` for BV literals, so the dependency path it currently uses is the one to reuse here.

- [ ] **Step 5: Dispatch the special literals in the `"_"` head branch**

In `parse_compound`, the `"_" =>` arm currently calls `parse_bv_numeral` then expects `)`. Replace it with a peek-based dispatch on the symbol after `_`:

```rust
            "_" => {
                // Peek the indexed identifier name to choose BV-numeral vs FP special.
                let (id, isp) = self.expect_symbol()?;
                let result = match id.as_str() {
                    "+oo" | "-oo" | "+zero" | "-zero" | "NaN" => {
                        let eb = self.expect_numeral_u32()?;
                        let sb = self.expect_numeral_u32()?;
                        if eb < 2 || sb < 2 {
                            return Err(Diagnostic::new(isp, "FloatingPoint requires eb>=2, sb>=2"));
                        }
                        let kind = match id.as_str() {
                            "+oo" => FpSpecial::PosInf,
                            "-oo" => FpSpecial::NegInf,
                            "+zero" => FpSpecial::PosZero,
                            "-zero" => FpSpecial::NegZero,
                            _ => FpSpecial::Nan,
                        };
                        ctx.mk_fp_const(eb, sb, fp_special_bits(eb, sb, kind))
                    }
                    sym if sym.starts_with("bv") => {
                        // (_ bvK n) BV numeral — preserve existing behavior.
                        let k_str = &sym[2..];
                        let k: u64 = k_str.parse().map_err(|_| {
                            Diagnostic::new(isp.clone(), format!("invalid BV numeral suffix `{k_str}`"))
                        })?;
                        let width = self.expect_numeral_u32()?;
                        if width == 0 {
                            return Err(Diagnostic::new(isp, "BV numeral width must be >= 1"));
                        }
                        ctx.mk_bv_const(width, shinri_core::num::Integer::from(k))
                    }
                    other => {
                        return Err(Diagnostic::new(isp, format!("unknown indexed literal `_ {other}`")));
                    }
                };
                self.expect_token(&Token::RParen)?;
                return Ok(result);
            }
```

> This inlines the body of the existing `parse_bv_numeral` for the `bv` case (because `parse_bv_numeral` re-reads the symbol that we have already consumed here). After this change, `parse_bv_numeral` may be unused — delete it if the compiler warns, or leave it and silence the warning consistent with the crate's lint policy.

- [ ] **Step 6: Run test to verify it passes**

Run: `cargo test -p shinri-parser parse_fp_constructor_and_specials`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-parser/src/parser.rs
git commit -m "feat(parser): (fp ...) constructor + special FP literals"
```

---

### Task 8: Parse FP operators and indexed conversions

**Files:**
- Modify: `crates/shinri-parser/src/parser.rs` (`builtin_for` for `fp.*`; `parse_indexed_op` for conversions)
- Test: `crates/shinri-parser/src/parser.rs`

**Interfaces:**
- Consumes: all FP `BuiltinOp` variants (Tasks 3–4).
- Produces: operator names `fp.abs/neg/add/sub/mul/div/fma/sqrt/rem/roundToIntegral/min/max/leq/lt/geq/gt/eq/isNormal/isSubnormal/isZero/isInfinite/isNaN/isNegative/isPositive/to_real` mapped in `builtin_for`; indexed `(_ to_fp eb sb)`, `(_ to_fp_unsigned eb sb)`, `(_ fp.to_ubv m)`, `(_ fp.to_sbv m)` mapped in `parse_indexed_op`.

- [ ] **Step 1: Write the failing test**

Add to the parser test module:

```rust
#[test]
fn parse_fp_operators_and_conversions() {
    use shinri_core::Context;
    fn parse_with_x(decl_sort: &str, expr: &str) -> (Context, shinri_core::TermId) {
        let mut ctx = Context::new();
        // declare x of the given sort, then parse the expression referencing it
        let src = format!("(declare-fun x () {decl_sort})");
        let mut p = Parser::new(&src);
        p.parse_command_pub(&mut ctx).expect("declare");
        let mut p2 = Parser::new(expr);
        // share the same env: re-declare via the same ctx by reusing parse over a fresh parser
        // (the env lives on the parser; use a single source instead — see note)
        let _ = &mut p2;
        let full = format!("(declare-fun x () {decl_sort}) {expr}");
        let mut p3 = Parser::new(&full);
        p3.parse_command_pub(&mut ctx).expect("declare again");
        let t = p3.parse_term_pub(&mut ctx).expect("parse expr");
        (ctx, t)
    }

    // fp.add RNE x x : Float32 -> Float32
    let (ctx, t) = parse_with_x("Float32", "(fp.add RNE x x)");
    assert_eq!(ctx.fp_widths(ctx.sort_of(t)), Some((8, 24)));

    // fp.isNaN x : Bool
    let (ctx, t) = parse_with_x("Float32", "(fp.isNaN x)");
    assert_eq!(ctx.sort_of(t), ctx.bool_sort());

    // ((_ to_fp 11 53) RNE x) : Float32 -> Float64
    let (ctx, t) = parse_with_x("Float32", "((_ to_fp 11 53) RNE x)");
    assert_eq!(ctx.fp_widths(ctx.sort_of(t)), Some((11, 53)));

    // ((_ fp.to_sbv 16) RNE x) : Float32 -> BV16
    let (ctx, t) = parse_with_x("Float32", "((_ fp.to_sbv 16) RNE x)");
    assert_eq!(ctx.bv_width(ctx.sort_of(t)), Some(16));
}
```

> If the parser's command/term entry points are named differently than `parse_command_pub`/`parse_term_pub`, adapt the harness to whatever the existing parser tests use to declare a symbol and parse a term against the same `Context`/env. The four assertions are the contract.

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser parse_fp_operators_and_conversions`
Expected: FAIL — `fp.add` undeclared / `to_fp` unknown indexed identifier.

- [ ] **Step 3: Map `fp.*` operator names in `builtin_for`**

In `builtin_for`, add (the `use shinri_core::BuiltinOp::*;` glob is in scope):

```rust
        "fp.abs" => FpAbs,
        "fp.neg" => FpNeg,
        "fp.add" => FpAdd,
        "fp.sub" => FpSub,
        "fp.mul" => FpMul,
        "fp.div" => FpDiv,
        "fp.fma" => FpFma,
        "fp.sqrt" => FpSqrt,
        "fp.rem" => FpRem,
        "fp.roundToIntegral" => FpRoundToIntegral,
        "fp.min" => FpMin,
        "fp.max" => FpMax,
        "fp.leq" => FpLeq,
        "fp.lt" => FpLt,
        "fp.geq" => FpGeq,
        "fp.gt" => FpGt,
        "fp.eq" => FpEq,
        "fp.isNormal" => FpIsNormal,
        "fp.isSubnormal" => FpIsSubnormal,
        "fp.isZero" => FpIsZero,
        "fp.isInfinite" => FpIsInfinite,
        "fp.isNaN" => FpIsNaN,
        "fp.isNegative" => FpIsNegative,
        "fp.isPositive" => FpIsPositive,
        "fp.to_real" => FpToReal,
```

- [ ] **Step 4: Map indexed conversions in `parse_indexed_op`**

In `parse_indexed_op`, add to the `match id.as_str()` (alongside `extract`/`zero_extend`/…):

```rust
        "to_fp" => {
            let eb = self.expect_numeral_u32()?;
            let sb = self.expect_numeral_u32()?;
            ToFp { eb, sb }
        }
        "to_fp_unsigned" => {
            let eb = self.expect_numeral_u32()?;
            let sb = self.expect_numeral_u32()?;
            ToFpUnsigned { eb, sb }
        }
        "fp.to_ubv" => FpToUbv(self.expect_numeral_u32()?),
        "fp.to_sbv" => FpToSbv(self.expect_numeral_u32()?),
```

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-parser parse_fp_operators_and_conversions`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-parser/src/parser.rs
git commit -m "feat(parser): fp.* operators + indexed conversions"
```

---

### Task 9: End-to-end QF_FP / QF_BVFP parse + sort-check integration test

**Files:**
- Create: `crates/shinri-parser/tests/fp_parse.rs`

**Interfaces:**
- Consumes: the parser's public script/command entry points and `Context` accessors from Tasks 1–8.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-parser/tests/fp_parse.rs`. Use the same top-level parsing entry the other `crates/shinri-parser/tests/*.rs` files use (check an existing test file in that directory for the exact API — e.g. a `parse_script(src, &mut ctx)` or `Parser::new(src).parse_all(&mut ctx)`). Mirror that API here:

```rust
use shinri_core::Context;

// A small QF_FP + QF_BVFP script exercising sorts, specials, arithmetic,
// comparisons, classification, the (fp ..) constructor, and conversions.
const SCRIPT: &str = r#"
(set-logic QF_FP)
(declare-fun x () Float32)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun r () RoundingMode)
(declare-fun b () (_ BitVec 32))
(assert (fp.leq (fp.add r x y) (fp.mul RNE x y)))
(assert (fp.isNaN (fp.div RNE x (_ +zero 8 24))))
(assert (= y (fp #b0 #b00000000 #b00000000000000000000000)))
(assert (fp.eq ((_ to_fp 8 24) RNE b) x))
(assert (fp.lt ((_ to_fp 11 53) r x) ((_ to_fp 11 53) r y)))
(assert (= b ((_ fp.to_sbv 32) RNE x)))
"#;

#[test]
fn qffp_script_parses_and_sortchecks() {
    let mut ctx = Context::new();
    // Replace `parse_script` with the actual top-level entry used by the
    // sibling test files in crates/shinri-parser/tests/.
    let result = shinri_parser::parse_script(SCRIPT, &mut ctx);
    assert!(result.is_ok(), "QF_FP script must parse and sort-check: {result:?}");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-parser --test fp_parse`
Expected: FAIL initially only if the entry-point name is wrong — fix the call to match the sibling tests, then it should fail/pass on parsing behavior. (If every prior task is done, this should pass once the entry point name is correct.)

- [ ] **Step 3: Make it pass**

No new production code should be required — Tasks 1–8 cover every construct in `SCRIPT`. If parsing fails, the diagnostic names the unsupported construct; fix the corresponding earlier task. Adjust only the test's entry-point call to match the crate's public API.

- [ ] **Step 4: Run the full core + parser suites**

Run: `cargo test -p shinri-core -p shinri-parser`
Expected: PASS (all FP tests + existing non-regression tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-parser/tests/fp_parse.rs
git commit -m "test(parser): end-to-end QF_FP/QF_BVFP parse + sort-check"
```

---

## Self-Review

**Spec coverage (against `2026-06-24-shinri-qffp-design.md` §6.1–6.2 — the only sections this foundation plan targets):**
- `SortNode::Float(eb,sb)` + `Float16/32/64/128` aliases — Task 1 (sort) + Task 5 (parser). ✓
- `SortNode::RoundingMode` + 5 constants — Task 1/2 (sort+consts) + Task 5/6 (parser). ✓
- FP specials + `(fp …)` constructor — Task 2 (consts) + Task 3 (`FpFromBits` sort-check) + Task 7 (parser). ✓
- All FP arithmetic/compare/classify `BuiltinOp`s with RoundingMode-first-arg shape — Task 3 + Task 8. ✓
- Indexed conversions (`ToFp`, `ToFpUnsigned`, `FpToUbv`, `FpToSbv`, `FpToReal`) with result-sort computation — Task 4 + Task 8. ✓
- Width/sort errors caught at sort-check, never panicking — Tasks 3–4 (error variants + `is_err()` assertions). ✓
- Deferred to later plans (NOT in this plan, by design): all bit-blasting circuits, the exact-rational oracle, solver wiring, model extraction, the symbolic-Real `unknown` fence. The fence lives in the solver (Plan 4), so `FpToReal`/`ToFp`-from-Real are only *parsed/sort-checked* here, never solved.

**Placeholder scan:** No `TBD`/`TODO`/"handle edge cases". Two explicit adapt-points (the parser test-harness entry-point name in Tasks 5–9, and the `shinri_core::num` vs `shinri_num` Integer path in Task 7) are flagged with the exact fallback to use — these are crate-API confirmations, not unspecified work.

**Type consistency:** `RoundingMode` variants (`Rne/Rna/Rtp/Rtn/Rtz`) identical across Tasks 2/3/6. `ToFp { eb, sb }`/`ToFpUnsigned { eb, sb }`/`FpToUbv(u32)`/`FpToSbv(u32)`/`FpToReal` identical across Tasks 4/8. `fp_sort`/`rm_sort`/`fp_widths`/`mk_fp_const`/`mk_rm_const`/`fp_const_value`/`rm_const_value`/`require_fp`/`require_rm` signatures consistent across all tasks. FP bit layout (`[sign|exp|trailing-sig]`, `W=eb+sb`, hidden bit included in `sb`) consistent between Task 2's table doc and Task 7's `fp_special_bits`. ✓
