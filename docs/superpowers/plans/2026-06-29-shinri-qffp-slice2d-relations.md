# QF-FP slice 2d — ordering relations + fp.min/fp.max Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add bit-blasted `fp.lt`/`fp.leq`/`fp.gt`/`fp.geq` and `fp.min`/`fp.max` to shinri's QF-FP path.

**Architecture:** One new comparison primitive `fp_lt` (an unsigned magnitude comparator plus a sign branch) carries all four relations; the existing `fp_eq` supplies the `≤`/`≥` equality half. `fp.min`/`fp.max` are per-bit muxes over `fp_lt` with NaN passthrough and a sign-canonical `±0` rule. Every op is rounding-free and shallow (no recursion). A reference implementation in `reference.rs` gives every circuit a bit-exact oracle; a soundness fence in `shinri-solver` admits the new ops by positive enumeration.

**Tech Stack:** Rust; `shinri-fp` (blaster), `shinri-bv` (`Blaster` gate factory), `shinri-num` (`Integer`, `Rational`), `shinri-solver` (driver + fence), `z3` via `easy_smt` for the differential oracle.

## Global Constraints

- Bit layout MSB→LSB is `[ sign(1) | exp(eb) | trailing-sig(sb-1) ]`, width `W = eb + sb`. `Unpacked.exp` and `Unpacked.sig` are stored **LSB→MSB**.
- `fp_lt`/`fp_eq` etc. take `(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32)` and return `BitLit`; min/max return `Vec<BitLit>`.
- min/max `±0` rule is **sign-canonical and order-independent**: `min(+0,-0)=min(-0,+0)=-0`, `max=+0`.
- NaN: all four relations are false on any NaN operand; min/max pass through the non-NaN operand (`minNum`/`maxNum`), both-NaN → return the second operand (a NaN).
- New FP ops must be admitted through the `shinri-solver` fence (`fp_stage.rs`); anything unhandled must fail closed (Unknown), never panic.
- Reference: `class_to_rational` returns `None` for **NaN and Inf**; handle Inf explicitly. `Rational` implements `Ord`.
- Spec: `docs/superpowers/specs/2026-06-29-shinri-qffp-slice2d-relations-design.md`.

---

### Task 1: Reference functions (`ref_lt/leq/gt/geq`, `ref_min/max`)

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (add after `ref_fp_eq` / the existing `ref_*` block; reuse the private `zero_pattern` helper already in the file)
- Test: `crates/shinri-fp/src/reference.rs` (`#[cfg(test)]` module at file end)

**Interfaces:**
- Consumes: `decode(eb,sb,&Integer) -> FpClass`, `class_to_rational(eb,sb,&FpClass) -> Option<Rational>`, `ref_fp_eq(&FpClass,&FpClass) -> bool`, private `fn zero_pattern(eb,sb,sign:bool) -> Integer`, `FpClass::{Nan, Inf{sign}, Zero{sign}, Subnormal, Normal}`.
- Produces: `ref_lt`, `ref_leq`, `ref_gt`, `ref_geq` (`(u32,u32,&Integer,&Integer)->bool`); `ref_min`, `ref_max` (`(u32,u32,&Integer,&Integer)->Integer`).

- [ ] **Step 1: Write the failing tests**

Add at the end of `reference.rs`:

```rust
#[cfg(test)]
mod slice2d_tests {
    use super::*;
    use shinri_num::Integer;

    // Float32 bit patterns.
    const P1: u64 = 0x3F80_0000;   // +1.0
    const N1: u64 = 0xBF80_0000;   // -1.0
    const P2: u64 = 0x4000_0000;   // +2.0
    const N2: u64 = 0xC000_0000;   // -2.0
    const PZ: u64 = 0x0000_0000;   // +0
    const NZ: u64 = 0x8000_0000;   // -0
    const PINF: u64 = 0x7F80_0000;
    const NINF: u64 = 0xFF80_0000;
    const QNAN: u64 = 0x7FC0_0000;
    const SUBN: u64 = 0x0000_0001; // smallest +subnormal

    fn i(v: u64) -> Integer { Integer::from(v) }

    #[test]
    fn ref_lt_matches_extended_order() {
        let (eb, sb) = (8, 24);
        let lt = |a, b| ref_lt(eb, sb, &i(a), &i(b));
        assert!(lt(P1, P2));
        assert!(!lt(P2, P1));
        assert!(lt(N1, P1));
        assert!(lt(N2, N1));        // -2 < -1
        assert!(!lt(N1, N2));
        assert!(!lt(PZ, NZ));       // +0 == -0
        assert!(!lt(NZ, PZ));
        assert!(lt(NINF, PINF));
        assert!(lt(NINF, N1));
        assert!(lt(P1, PINF));
        assert!(lt(PZ, SUBN));
        assert!(!lt(QNAN, P1));     // NaN unordered
        assert!(!lt(P1, QNAN));
        assert!(!lt(QNAN, QNAN));
    }

    #[test]
    fn ref_leq_gt_geq_derive_correctly() {
        let (eb, sb) = (8, 24);
        assert!(ref_leq(eb, sb, &i(P1), &i(P1)));    // equal
        assert!(ref_leq(eb, sb, &i(PZ), &i(NZ)));    // +0 <= -0
        assert!(!ref_leq(eb, sb, &i(QNAN), &i(P1))); // NaN
        assert!(ref_gt(eb, sb, &i(P2), &i(P1)));
        assert!(!ref_gt(eb, sb, &i(P1), &i(P1)));
        assert!(ref_geq(eb, sb, &i(P1), &i(P1)));
        assert!(ref_geq(eb, sb, &i(P2), &i(P1)));
        assert!(!ref_geq(eb, sb, &i(P1), &i(QNAN)));
    }

    #[test]
    fn ref_min_max_with_nan_and_zero_tie() {
        let (eb, sb) = (8, 24);
        assert_eq!(ref_min(eb, sb, &i(P1), &i(P2)), i(P1));
        assert_eq!(ref_max(eb, sb, &i(P1), &i(P2)), i(P2));
        // sign-canonical, order-independent ±0:
        assert_eq!(ref_min(eb, sb, &i(PZ), &i(NZ)), i(NZ));
        assert_eq!(ref_min(eb, sb, &i(NZ), &i(PZ)), i(NZ));
        assert_eq!(ref_max(eb, sb, &i(PZ), &i(NZ)), i(PZ));
        assert_eq!(ref_max(eb, sb, &i(NZ), &i(PZ)), i(PZ));
        // NaN passthrough:
        assert_eq!(ref_min(eb, sb, &i(QNAN), &i(P1)), i(P1));
        assert_eq!(ref_min(eb, sb, &i(P1), &i(QNAN)), i(P1));
        assert_eq!(ref_max(eb, sb, &i(QNAN), &i(P2)), i(P2));
        assert_eq!(ref_min(eb, sb, &i(QNAN), &i(QNAN)), i(QNAN)); // both NaN -> b
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp slice2d_tests`
Expected: FAIL — `cannot find function ref_lt`/`ref_min` … in this scope.

- [ ] **Step 3: Write the reference implementation**

Add to `reference.rs` (after the `ref_fp_eq` block; `zero_pattern` is already defined privately in this file):

```rust
/// Extended order key: -∞ < every finite rational < +∞. NaN has no key.
/// Derived `Ord` compares by variant order (NegInf < Fin < PosInf), then by the
/// contained `Rational` for the `Fin` arm.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Ord3 {
    NegInf,
    Fin(Rational),
    PosInf,
}

fn order_key(eb: u32, sb: u32, c: &FpClass) -> Option<Ord3> {
    match c {
        FpClass::Nan => None,
        FpClass::Inf { sign } => Some(if *sign { Ord3::NegInf } else { Ord3::PosInf }),
        // Zero / Subnormal / Normal all yield Some(_) from class_to_rational.
        other => Some(Ord3::Fin(class_to_rational(eb, sb, other).expect("finite -> rational"))),
    }
}

/// IEEE `fp.lt`: NaN on either side -> false; +0 == -0; else extended-real order.
pub fn ref_lt(eb: u32, sb: u32, a: &Integer, b: &Integer) -> bool {
    let ka = order_key(eb, sb, &decode(eb, sb, a));
    let kb = order_key(eb, sb, &decode(eb, sb, b));
    match (ka, kb) {
        (Some(x), Some(y)) => x < y,
        _ => false,
    }
}

pub fn ref_leq(eb: u32, sb: u32, a: &Integer, b: &Integer) -> bool {
    ref_lt(eb, sb, a, b) || ref_fp_eq(&decode(eb, sb, a), &decode(eb, sb, b))
}

pub fn ref_gt(eb: u32, sb: u32, a: &Integer, b: &Integer) -> bool {
    ref_lt(eb, sb, b, a)
}

pub fn ref_geq(eb: u32, sb: u32, a: &Integer, b: &Integer) -> bool {
    ref_lt(eb, sb, b, a) || ref_fp_eq(&decode(eb, sb, a), &decode(eb, sb, b))
}

/// `fp.min`: NaN passes through to the other operand; both-NaN -> b. The
/// SMT-LIB-unspecified (+0,-0) case is resolved sign-canonically to -0.
pub fn ref_min(eb: u32, sb: u32, a: &Integer, b: &Integer) -> Integer {
    let (ca, cb) = (decode(eb, sb, a), decode(eb, sb, b));
    if matches!(ca, FpClass::Nan) { return b.clone(); }
    if matches!(cb, FpClass::Nan) { return a.clone(); }
    if let (FpClass::Zero { sign: sa }, FpClass::Zero { sign: sbn }) = (&ca, &cb) {
        if sa != sbn { return zero_pattern(eb, sb, true); } // -0
    }
    if ref_lt(eb, sb, a, b) { a.clone() } else { b.clone() }
}

/// `fp.max`: symmetric to `ref_min`; the (+0,-0) tie resolves to +0.
pub fn ref_max(eb: u32, sb: u32, a: &Integer, b: &Integer) -> Integer {
    let (ca, cb) = (decode(eb, sb, a), decode(eb, sb, b));
    if matches!(ca, FpClass::Nan) { return b.clone(); }
    if matches!(cb, FpClass::Nan) { return a.clone(); }
    if let (FpClass::Zero { sign: sa }, FpClass::Zero { sign: sbn }) = (&ca, &cb) {
        if sa != sbn { return zero_pattern(eb, sb, false); } // +0
    }
    if ref_lt(eb, sb, a, b) { b.clone() } else { a.clone() }
}
```

Verify `Rational` is in scope in `reference.rs` (it is used by `class_to_rational`); if the `use` is local to a function, add `use shinri_num::Rational;` at the top.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp slice2d_tests`
Expected: PASS (3 tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): reference ref_lt/leq/gt/geq + ref_min/max for slice 2d"
```

---

### Task 2: `fp_lt` circuit + relation combinators (`compare.rs`)

**Files:**
- Modify: `crates/shinri-fp/src/blast/compare.rs` (add `ult`, `fp_lt`, `fp_leq`, `fp_gt`, `fp_geq`; extend the existing `#[cfg(test)]` module — it already defines `const_bits`, `eval_lit`, `eval_word`)
- Test: same file's test module

**Interfaces:**
- Consumes: `crate::unpack::unpack(b,&[BitLit],eb,sb) -> Unpacked{sign,exp,sig,is_nan,is_inf,is_zero}`; existing `fp_eq`; `Blaster::{not1,and2,or2,xor2,zero}`; `reference::{ref_lt,ref_leq,ref_gt,ref_geq,decode}`.
- Produces: `pub fn fp_lt/fp_leq/fp_gt/fp_geq(b:&mut Blaster, x:&[BitLit], y:&[BitLit], eb:u32, sb:u32) -> BitLit`.

- [ ] **Step 1: Write the failing test**

Add to the `tests` module in `compare.rs`:

```rust
#[test]
fn fp_lt_and_relations_match_reference() {
    use crate::reference::{ref_geq, ref_gt, ref_leq, ref_lt};
    let (eb, sb) = (8, 24);
    let pats = [
        0x3F80_0000u64, 0xBF80_0000, 0x4000_0000, 0xC000_0000,
        0x0000_0000, 0x8000_0000, 0x7F80_0000, 0xFF80_0000,
        0x7FC0_0000, 0x0000_0001,
    ];
    for &x in &pats {
        for &y in &pats {
            for (name, blast, reff) in [
                ("lt", fp_lt as fn(&mut Blaster, &[BitLit], &[BitLit], u32, u32) -> BitLit,
                 ref_lt as fn(u32, u32, &Integer, &Integer) -> bool),
                ("leq", fp_leq, ref_leq),
                ("gt", fp_gt, ref_gt),
                ("geq", fp_geq, ref_geq),
            ] {
                let mut b = Blaster::new();
                let xb = const_bits(&b, eb, sb, x);
                let yb = const_bits(&b, eb, sb, y);
                let lit = blast(&mut b, &xb, &yb, eb, sb);
                let got = eval_lit(b, lit);
                let want = reff(eb, sb, &Integer::from(x), &Integer::from(y));
                assert_eq!(got, want, "fp.{name}({x:#x},{y:#x})");
            }
        }
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp fp_lt_and_relations_match_reference`
Expected: FAIL — `cannot find function fp_lt`.

- [ ] **Step 3: Write the implementation**

Add to `compare.rs` (above the test module):

```rust
/// Unsigned `x < y` over equal-width LSB→MSB bit vectors. Rippled low→high so
/// the most-significant bit dominates.
fn ult(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    debug_assert_eq!(x.len(), y.len());
    let mut lt = b.zero();
    for i in 0..x.len() {
        let nx = b.not1(x[i]);
        let bit_lt = b.and2(nx, y[i]);          // x_i=0, y_i=1
        let xn = b.xor2(x[i], y[i]);
        let bit_eq = b.not1(xn);
        let keep = b.and2(bit_eq, lt);
        lt = b.or2(bit_lt, keep);               // higher bit wins
    }
    lt
}

/// IEEE `fp.lt`: NaN on either side -> false; +0 == -0; else real order.
/// Magnitude is `[sig ++ exp]` (LSB→MSB) so exp outranks sig and ±inf falls out
/// as the extreme magnitude.
pub fn fp_lt(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);

    let mut mag_x = ux.sig.clone();
    mag_x.extend_from_slice(&ux.exp);
    let mut mag_y = uy.sig.clone();
    mag_y.extend_from_slice(&uy.exp);
    let mlt = ult(b, &mag_x, &mag_y);          // |x| < |y|
    let mgt = ult(b, &mag_y, &mag_x);          // |x| > |y|

    let signs_diff = b.xor2(ux.sign, uy.sign);
    let signs_same = b.not1(signs_diff);
    // signs differ: x < y iff x is the negative one.
    let diff_case = b.and2(signs_diff, ux.sign);
    // both >= 0: |x| < |y|.
    let not_sx = b.not1(ux.sign);
    let pos_branch = b.and2(not_sx, mlt);
    // both < 0: |x| > |y|.
    let neg_branch = b.and2(ux.sign, mgt);
    let same_inner = b.or2(pos_branch, neg_branch);
    let same_case = b.and2(signs_same, same_inner);

    let raw = b.or2(diff_case, same_case);

    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let not_both_zero = b.not1(both_zero);
    let nx = b.not1(ux.is_nan);
    let ny = b.not1(uy.is_nan);
    let neither_nan = b.and2(nx, ny);

    let t1 = b.and2(raw, not_both_zero);
    b.and2(t1, neither_nan)
}

pub fn fp_leq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let lt = fp_lt(b, x, y, eb, sb);
    let eq = fp_eq(b, x, y, eb, sb);
    b.or2(lt, eq)
}

pub fn fp_gt(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    fp_lt(b, y, x, eb, sb)
}

pub fn fp_geq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let gt = fp_lt(b, y, x, eb, sb);
    let eq = fp_eq(b, x, y, eb, sb);
    b.or2(gt, eq)
}
```

If the test module does not already import `Integer`, add `use shinri_num::Integer;` to it (the existing `abs_neg_words_match_reference` test already uses `Integer`, so it is in scope).

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp fp_lt_and_relations_match_reference`
Expected: PASS (100 operand pairs × 4 relations).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/blast/compare.rs
git commit -m "feat(fp): fp.lt/leq/gt/geq circuits (magnitude comparator) for slice 2d"
```

---

### Task 3: `fp.min` / `fp.max` circuits (`minmax.rs`)

**Files:**
- Create: `crates/shinri-fp/src/blast/minmax.rs`
- Modify: `crates/shinri-fp/src/blast/mod.rs` (add `pub mod minmax;`)
- Test: `crates/shinri-fp/src/blast/minmax.rs` (`#[cfg(test)]` module)

**Interfaces:**
- Consumes: `crate::unpack::unpack`; `crate::blast::compare::fp_lt`; `Blaster::{mux2,xor2,and2,one,zero}`.
- Produces: `pub fn fp_min/fp_max(b:&mut Blaster, x:&[BitLit], y:&[BitLit], eb:u32, sb:u32) -> Vec<BitLit>`.

- [ ] **Step 1: Add the module declaration**

In `crates/shinri-fp/src/blast/mod.rs`, add (keep the list alphabetical — between `mul` and `normalize`):

```rust
pub mod minmax;
```

- [ ] **Step 2: Write the failing test**

Create `crates/shinri-fp/src/blast/minmax.rs` with only the test module first:

```rust
//! fp.min / fp.max: NaN-passthrough selectors with a sign-canonical ±0 rule.

use shinri_bv::{BitLit, Blaster};
use crate::unpack::unpack;
use crate::blast::compare::fp_lt;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{ref_max, ref_min};
    use shinri_num::Integer;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn const_bits(b: &Blaster, eb: u32, sb: u32, value: u64) -> Vec<BitLit> {
        (0..(eb + sb)).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    }
    fn eval_word(b: Blaster, word: &[BitLit]) -> u64 {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars { s.new_var(); }
        for c in &cnf.clauses {
            let ls: Vec<Lit> = c.iter().map(|bl| Lit::new(Var::new(bl.var), bl.pos)).collect();
            s.add_clause(&ls);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let mut v = 0u64;
        for (i, bl) in word.iter().enumerate() {
            let raw = s.value_of(Var::new(bl.var)).unwrap();
            if if bl.pos { raw } else { !raw } { v |= 1 << i; }
        }
        v
    }

    #[test]
    fn min_max_words_match_reference() {
        let (eb, sb) = (8, 24);
        let pats = [
            0x3F80_0000u64, 0xBF80_0000, 0x4000_0000, 0xC000_0000,
            0x0000_0000, 0x8000_0000, 0x7F80_0000, 0xFF80_0000,
            0x7FC0_0000, 0x0000_0001,
        ];
        for &x in &pats {
            for &y in &pats {
                let mut b = Blaster::new();
                let xb = const_bits(&b, eb, sb, x);
                let yb = const_bits(&b, eb, sb, y);
                let w = fp_min(&mut b, &xb, &yb, eb, sb);
                let got = eval_word(b, &w);
                let want = ref_min(eb, sb, &Integer::from(x), &Integer::from(y))
                    .to_i128().unwrap() as u64;
                assert_eq!(got, want, "fp.min({x:#x},{y:#x})");

                let mut b2 = Blaster::new();
                let xb2 = const_bits(&b2, eb, sb, x);
                let yb2 = const_bits(&b2, eb, sb, y);
                let w2 = fp_max(&mut b2, &xb2, &yb2, eb, sb);
                let got2 = eval_word(b2, &w2);
                let want2 = ref_max(eb, sb, &Integer::from(x), &Integer::from(y))
                    .to_i128().unwrap() as u64;
                assert_eq!(got2, want2, "fp.max({x:#x},{y:#x})");
            }
        }
    }
}
```

- [ ] **Step 3: Run test to verify it fails**

Run: `cargo test -p shinri-fp min_max_words_match_reference`
Expected: FAIL — `cannot find function fp_min`.

- [ ] **Step 4: Write the implementation**

Insert above the test module in `minmax.rs`:

```rust
/// Per-bit select: `sel ? a : c`, returning a fresh word.
fn mux_word(b: &mut Blaster, sel: BitLit, a: &[BitLit], c: &[BitLit]) -> Vec<BitLit> {
    debug_assert_eq!(a.len(), c.len());
    (0..a.len()).map(|i| b.mux2(sel, a[i], c[i])).collect()
}

/// Constant ±0 word (all zero, MSB sign bit set iff `neg`), LSB→MSB.
fn zero_word(b: &Blaster, eb: u32, sb: u32, neg: bool) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    (0..w).map(|i| if neg && i == w - 1 { b.one() } else { b.zero() }).collect()
}

/// `fp.min`: `minNum` semantics. NaN passes through to the other operand;
/// the (+0,-0) tie resolves to -0 (sign-canonical, order-independent).
pub fn fp_min(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit> {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let lt = fp_lt(b, x, y, eb, sb);
    let pick = mux_word(b, lt, x, y);                 // lt ? x : y (ties keep y)

    let opp = b.xor2(ux.sign, uy.sign);
    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let zero_tie = b.and2(both_zero, opp);
    let neg_zero = zero_word(b, eb, sb, true);
    let pick = mux_word(b, zero_tie, &neg_zero, &pick);

    let r = mux_word(b, uy.is_nan, x, &pick);         // y NaN -> x
    mux_word(b, ux.is_nan, y, &r)                     // x NaN -> y (outermost)
}

/// `fp.max`: symmetric to `fp_min`; the (+0,-0) tie resolves to +0.
pub fn fp_max(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit> {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let lt = fp_lt(b, x, y, eb, sb);
    let pick = mux_word(b, lt, y, x);                 // lt ? y : x (larger)

    let opp = b.xor2(ux.sign, uy.sign);
    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let zero_tie = b.and2(both_zero, opp);
    let pos_zero = zero_word(b, eb, sb, false);
    let pick = mux_word(b, zero_tie, &pos_zero, &pick);

    let r = mux_word(b, uy.is_nan, x, &pick);
    mux_word(b, ux.is_nan, y, &r)
}
```

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-fp min_max_words_match_reference`
Expected: PASS (100 operand pairs × 2 ops).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/blast/minmax.rs crates/shinri-fp/src/blast/mod.rs
git commit -m "feat(fp): fp.min/fp.max circuits (NaN passthrough, sign-canonical zero) for slice 2d"
```

---

### Task 4: Wire dispatch in the blaster (`lib.rs`)

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` (`blast_atom` — add relation arm; `blast_word` — add min/max arms)
- Test: `crates/shinri-fp/src/lib.rs` (`#[cfg(test)]` module — follow the existing `add`/`mul`/`div` term-node tests)

**Interfaces:**
- Consumes: `crate::blast::compare::{fp_lt,fp_leq,fp_gt,fp_geq}`, `crate::blast::minmax::{fp_min,fp_max}`; `ctx.fp_widths(SortId)`; `self.blast_word`.
- Produces: blasting `FpLt|FpLeq|FpGt|FpGeq` atoms and `FpMin|FpMax` words.

- [ ] **Step 1: Write the failing test**

This is a wiring/smoke test: it confirms dispatch routes the new ops without hitting the `unreachable!` arms. Behavioral correctness is already covered by the circuit unit tests (Tasks 2–3) and the e2e tests (Task 6), so this test only checks that `blast_atom` returns without panic and `blast_word` yields a `W = 32`-bit word. Add to the `blast_tests` module in `lib.rs` (it already imports `Context`, `Op`, `BuiltinOp`, `Integer`, and `FpBlaster`; add any missing `use` lines):

```rust
#[test]
fn blast_dispatch_relations_and_minmax_wired() {
    let mut ctx = Context::new();
    let one = ctx.mk_fp_const(8, 24, Integer::from(0x3F80_0000u64));
    let two = ctx.mk_fp_const(8, 24, Integer::from(0x4000_0000u64));
    let mut fb = FpBlaster::new();
    // Each relation atom must dispatch (no `unreachable!`):
    for rel in [BuiltinOp::FpLt, BuiltinOp::FpLeq, BuiltinOp::FpGt, BuiltinOp::FpGeq] {
        let a = ctx.mk_app(Op::Builtin(rel), &[one, two]).unwrap();
        let _lit = fb.blast_atom(&ctx, a); // must not panic
    }
    // min/max words must dispatch and yield a 32-bit word:
    let mn = ctx.mk_app(Op::Builtin(BuiltinOp::FpMin), &[one, two]).unwrap();
    let mx = ctx.mk_app(Op::Builtin(BuiltinOp::FpMax), &[one, two]).unwrap();
    assert_eq!(fb.blast_word(&ctx, mn).len(), 32);
    assert_eq!(fb.blast_word(&ctx, mx).len(), 32);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp blast_dispatch_relations_and_minmax_wired`
Expected: FAIL (panic) — `blast_atom: FP atom FpLt ... out of slice-1 scope` / `blast_word: FP op FpMin ... out of slice-1 scope`.

- [ ] **Step 3: Wire `blast_atom`**

In `blast_atom`, insert a new arm **before** the final `other =>` arm (after the `FpEq` arm):

```rust
Op::Builtin(rel @ (FpLt | FpLeq | FpGt | FpGeq)) => {
    let (eb, sb) = ctx.fp_widths(ctx.sort_of(kids[0])).expect("Float operands");
    let x = self.blast_word(ctx, kids[0]);
    let y = self.blast_word(ctx, kids[1]);
    use crate::blast::compare as cmp;
    match rel {
        FpLt => cmp::fp_lt(&mut self.b, &x, &y, eb, sb),
        FpLeq => cmp::fp_leq(&mut self.b, &x, &y, eb, sb),
        FpGt => cmp::fp_gt(&mut self.b, &x, &y, eb, sb),
        FpGeq => cmp::fp_geq(&mut self.b, &x, &y, eb, sb),
        _ => unreachable!(),
    }
}
```

- [ ] **Step 4: Wire `blast_word`**

In `blast_word`'s `Op::Builtin(op)` match, insert **before** the `other =>` arm (after `FpSqrt`):

```rust
FpMin => {
    let xw = self.blast_word(ctx, kids[0]);
    let yw = self.blast_word(ctx, kids[1]);
    crate::blast::minmax::fp_min(&mut self.b, &xw, &yw, eb, sb)
}
FpMax => {
    let xw = self.blast_word(ctx, kids[0]);
    let yw = self.blast_word(ctx, kids[1]);
    crate::blast::minmax::fp_max(&mut self.b, &xw, &yw, eb, sb)
}
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-fp blast_dispatch_relations_and_minmax_wired`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): dispatch fp.lt/leq/gt/geq and fp.min/max in blast_atom/blast_word"
```

---

### Task 5: Admit the new ops through the soundness fence (`fp_stage.rs`)

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs` (`is_supported_fp_word` — add `FpMin|FpMax`; `fp_atom_is_supported` — add `FpLt|FpLeq|FpGt|FpGeq`)
- Test: `crates/shinri-solver/src/fp_stage.rs` (`#[cfg(test)]` module)

**Interfaces:**
- Consumes: `is_supported_fp_word(ctx, TermId)`; `is_rounding_mode_term`; `BuiltinOp::{FpMin,FpMax,FpLt,FpLeq,FpGt,FpGeq}`.
- Produces: fence admits `fp.min`/`fp.max` words and the four relation atoms (each with two supported FP operands, **no** RM operand).

- [ ] **Step 1: Write the failing test**

Add to the `fp_stage.rs` test module:

```rust
#[test]
fn fence_admits_relations_and_minmax() {
    let mut ctx = Context::new();
    let x = fp_var(&mut ctx, "x");
    let y = fp_var(&mut ctx, "y");
    // relation atom
    let lt = ctx.mk_app(Op::Builtin(BuiltinOp::FpLt), &[x, y]).unwrap();
    assert!(fp_atoms_fully_supported(&ctx, &[lt]), "fp.lt admitted");
    // min/max nested inside fp.eq (word support)
    let mn = ctx.mk_app(Op::Builtin(BuiltinOp::FpMin), &[x, y]).unwrap();
    let eq = ctx.mk_app(Op::Builtin(BuiltinOp::FpEq), &[mn, x]).unwrap();
    assert!(fp_atoms_fully_supported(&ctx, &[eq]), "fp.min inside fp.eq admitted");
}
```

(`fp_var` already exists in this test module.)

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-solver --lib fence_admits_relations_and_minmax`
Expected: FAIL — assertion failed (`fp.lt` / `fp.min` not yet admitted).

- [ ] **Step 3: Add the min/max word arm**

In `is_supported_fp_word`, add a new arm before the catch-all `_ => false`:

```rust
// fp.min / fp.max: (F, F) -> F. No RM operand; both FP operands supported.
TermNode::App { op: Op::Builtin(BuiltinOp::FpMin | BuiltinOp::FpMax), args, .. } => {
    let kids = ctx.children(*args).to_vec();
    kids.len() == 2
        && is_supported_fp_word(ctx, kids[0])
        && is_supported_fp_word(ctx, kids[1])
}
```

- [ ] **Step 4: Add the relation atom arm**

In `fp_atom_is_supported`, add a new arm before the catch-all `_ => false`:

```rust
// fp.lt / fp.leq / fp.gt / fp.geq: two supported FP operands.
Op::Builtin(FpLt | FpLeq | FpGt | FpGeq) => {
    kids.len() == 2
        && is_supported_fp_word(ctx, kids[0])
        && is_supported_fp_word(ctx, kids[1])
}
```

- [ ] **Step 5: Run test to verify it passes**

Run: `cargo test -p shinri-solver --lib fence_admits_relations_and_minmax`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): admit fp.lt/leq/gt/geq + fp.min/max through the FP soundness fence"
```

---

### Task 6: End-to-end solver tests (`fp_e2e.rs`)

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` (add tests using the existing `run(src) -> (SolveOutcome, String)` helper)

**Interfaces:**
- Consumes: `run(&str) -> (SolveOutcome, String)`; `SolveOutcome::{Sat,Unsat}`.
- Note: use indexed constants `(_ +zero 8 24)` / `(_ +oo 8 24)` / `(_ NaN 8 24)` and declared `Float32` vars — NOT `(fp #b… …)` literals (those parse to `FpFromBits`, which the fence rejects → Unknown).

- [ ] **Step 1: Write the failing tests**

Append to `fp_e2e.rs`:

```rust
// ── Slice-2d end-to-end: ordering relations + fp.min/fp.max ───────────────────

#[test]
fn fp_lt_zero_lt_inf_is_sat() {
    let (o, _) = run("(assert (fp.lt (_ +zero 8 24) (_ +oo 8 24))) (check-sat)");
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_lt_antisymmetry_is_unsat() {
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) \
         (assert (fp.lt x y)) (assert (fp.lt y x)) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_leq_reflexive_fails_only_for_nan() {
    // (not (fp.leq x x)) is SAT only when x is NaN.
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (not (fp.leq x x))) (assert (fp.isNaN x)) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    let (o2, _) = run(
        "(declare-fun x () Float32) \
         (assert (not (fp.leq x x))) (assert (not (fp.isNaN x))) (check-sat)",
    );
    assert_eq!(o2, SolveOutcome::Unsat);
}

#[test]
fn fp_min_of_one_two_equals_one_sat_with_model() {
    let (o, model) = run(
        "(declare-fun x () Float32) \
         (assert (fp.eq x (fp.min (_ +oo 8 24) (_ +zero 8 24)))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat); // min(+oo,+0) = +0, so x fp.eq +0
    assert!(model.contains("(fp #b"), "model renders x: {model}");
}

#[test]
fn fp_max_picks_larger_unsat_when_contradicted() {
    // max(+0,+oo) = +oo, which is not fp.eq +0  => asserting equality is UNSAT.
    let (o, _) = run(
        "(assert (fp.eq (fp.max (_ +zero 8 24) (_ +oo 8 24)) (_ +zero 8 24))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}
```

- [ ] **Step 2: Run tests to verify they fail (then pass)**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: the five new tests PASS (Tasks 1–5 already make the machinery work end-to-end). If any returns `Unknown`, the fence (Task 5) or dispatch (Task 4) is mis-wired — fix there, not here.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): end-to-end fp.lt/leq/gt/geq + fp.min/max SAT/UNSAT + get-model"
```

---

### Task 7: Differential-vs-Z3 oracle (`fp_oracle.rs`)

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (add a `gen_rel_script` generator + a `differential_qf_fp_relations` test; reuse `Lcg`, `shinri_outcome`, `z3_outcome_arith`, `SolveOutcome`)
- Test: same file (gated behind `#[cfg(feature = "oracle")]`, needs `z3` on PATH)

**Interfaces:**
- Consumes: `Lcg`, `shinri_outcome(&str) -> SolveOutcome`, `z3_outcome_arith(&mut easy_smt::Context, &str) -> easy_smt::Response`, `FP32_SPECIALS`.
- Produces: a rounding-free generator emitting `fp.lt/leq/gt/geq` atoms and `fp.min/max` (folded into `fp.eq`), and a differential test asserting shinri ≡ z3 with SAT+UNSAT coverage.

- [ ] **Step 1: Write the generator + test**

Append to `fp_oracle.rs` (the `relations`/`selectors` choices below mirror the existing `gen_script` structure but declare two variables so the comparisons are non-trivial):

```rust
/// Rounding-free QF_FP over two vars, exercising fp.lt/leq/gt/geq and fp.min/max.
fn gen_rel_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n",
    );
    const RELS: &[&str] = &["fp.lt", "fp.leq", "fp.gt", "fp.geq"];
    let vars = ["x", "y"];
    let pick_operand = |rng: &mut Lcg| -> String {
        // 50% a variable, 50% a special constant.
        if rng.below(2) == 0 {
            vars[rng.below(2) as usize].to_string()
        } else {
            FP32_SPECIALS[rng.below(FP32_SPECIALS.len() as u64) as usize].to_string()
        }
    };

    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let kind = rng.below(2);
        let atom = if kind == 0 {
            // relation between two operands
            let rel = RELS[rng.below(RELS.len() as u64) as usize];
            let a = pick_operand(rng);
            let b = pick_operand(rng);
            format!("({rel} {a} {b})")
        } else {
            // min/max folded into an fp.eq so its word output is observable
            let mm = if rng.below(2) == 0 { "fp.min" } else { "fp.max" };
            let a = pick_operand(rng);
            let b = pick_operand(rng);
            let c = pick_operand(rng);
            format!("(fp.eq ({mm} {a} {b}) {c})")
        };
        if rng.below(2) == 0 {
            s.push_str(&format!("(assert (not {atom}))\n"));
        } else {
            s.push_str(&format!("(assert {atom})\n"));
        }
    }
    s.push_str("(check-sat)\n");
    s
}

// The file is gated at module level (`#![cfg(feature = "oracle")]`), so no
// per-test cfg is needed. `Lcg` is the tuple struct `Lcg(u64)`.
#[test]
fn differential_qf_fp_relations() {
    let mut rng = Lcg(0x002D_5EED_0001);
    let (mut n_sat, mut n_unsat) = (0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_rel_script(&mut rng);
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        let ours = shinri_outcome(&src);
        match (&ours, &theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (o, t) => panic!("QF_FP relations DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}
```

`N_ITERS`, `shinri_outcome`, `z3_outcome_arith`, `FP32_SPECIALS`, and `SolveOutcome` are all already defined/imported in this file and visible under the module-level `oracle` gate.

- [ ] **Step 2: Build the test target without running z3 (compile check)**

Run: `cargo test -p shinri-solver --test fp_oracle --features oracle --no-run`
Expected: compiles clean.

- [ ] **Step 3: Run the oracle in the background**

This suite is multi-minute and needs `z3` on PATH. Launch it in the background (standing practice for FP/SAT gate suites) and poll for completion:

Run: `cargo test -p shinri-solver --test fp_oracle --features oracle differential_qf_fp_relations -- --nocapture`
Expected: PASS with both SAT and UNSAT coverage; **no DISAGREEMENT panic**. A disagreement on a `±0` min/max case is a real signal — investigate the sign-canonical rule vs. z3, do not silence it.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential-vs-z3 oracle for fp relations + fp.min/max"
```

---

## Final verification

- [ ] Run the full FP unit suite: `cargo test -p shinri-fp`
- [ ] Run the solver e2e suite: `cargo test -p shinri-solver --test fp_e2e`
- [ ] Run `cargo clippy -p shinri-fp -p shinri-solver` and fix any new warnings.
- [ ] Confirm the oracle (Task 7) passed in the background with SAT+UNSAT coverage.

## Self-review notes (for the implementer)

- **Magnitude ordering depends on `[sig ++ exp]` (sig low, exp high).** If `fp_lt` disagrees with the reference only on same-sign pairs differing in exponent, the two halves were concatenated in the wrong order.
- **min/max NaN mux order matters:** `is_nan(x)` is the **outermost** select so `min(NaN, NaN)` returns `y` (a NaN), matching `ref_min`.
- These circuits are shallow (one comparator + muxes, no recursion), so the deep-circuit SAT-recursion issues from `fp.div`/`fp.sqrt` do not apply.
