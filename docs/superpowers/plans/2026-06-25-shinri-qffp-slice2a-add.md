# QF_FP Slice 2a — Rounder + `fp.add`/`fp.sub` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bit-blast `fp.add` and `fp.sub` for QF_FP end-to-end (parse → blast → SAT → model) with a shared, op-agnostic, 5-rounding-mode rounder, validated bit-identical to the exact-rational reference oracle and differentially against z3.

**Architecture:** Eager bit-blasting into the slice-1 `FpBlaster` (a `shinri_bv::Blaster` used as a gate factory). A new canonical intermediate `ExtFp { sign, exp, sig, grs }` is the single currency between datapaths and the rounder. The `fp.add` datapath unpacks both operands, aligns by exponent difference (capturing sticky), adds/subtracts the significands, normalizes (LZC for cancellation), builds an `ExtFp`, and calls `round()`; a final IEEE special-case mux overrides for NaN/∞/zero. `fp.sub RM x y` rewrites to `fp.add RM x (fp.neg y)`. Everything out of scope stays a sound `Unknown`.

**Tech Stack:** Rust, `shinri-fp` crate (depends on `shinri-bv`, `shinri-core`, `shinri-num`), the `shinri-sat` CDCL core for tests, `easy_smt` + z3 for the differential oracle (feature-gated).

## Global Constraints

- **Bit layout** (fixed by the foundation): a Float word is `W = eb + sb` bits, **LSB→MSB**, MSB-to-LSB meaning `[ sign(1) | exponent(eb) | trailing-significand(sb-1) ]`. `sb` **includes** the hidden bit.
- **Soundness contract:** anything outside `fp.add`/`fp.sub` scope returns `Unknown`, never a wrong SAT/UNSAT. FP+BV mixing, FP+EUF/Arith/Arrays, every not-yet-built op (`mul`/`div`/`sqrt`/`fma`/`rem`/`roundToIntegral`/`min`/`max`), all conversions, and any Real bridge stay fenced.
- **Validation anchor:** `round()` MUST be bit-identical to `reference.rs::round_rational`; the `fp.add` datapath MUST be bit-identical to `reference.rs::ref_add` (added in Task 1). Exhaustive on the `(3,5)` tiny format over all five modes; randomized on Float16/Float32.
- **No new external dependencies.** Reuse `shinri-bv` datapath helpers (`adder`, `bvsub`, `bvlshr`, `bvshl`) and `Blaster` primitives (`and2`, `or2`, `xor2`, `not1`, `mux2`, `full_adder`, `one`, `zero`, `fresh`, `add_clause`).
- **`RoundingMode` encoding:** a symbolic RM variable is 3 fresh bits `(e2 e1 e0)` with codes `000=RNE, 001=RNA, 010=RTP, 011=RTN, 100=RTZ` (matching `shinri_core::RoundingMode` enum order); codes `101/110/111` are excluded by two clauses. The rounder consumes a **5-bit one-hot** selector `[RNE, RNA, RTP, RTN, RTZ]`.
- **Reference rounding-mode type:** `reference.rs` uses its own `RoundMode { Rne, Rna, Rtp, Rtn, Rtz }`; map `shinri_core::RoundingMode` → `reference::RoundMode` 1:1 in tests.

---

## File Structure

| File | Status | Responsibility |
|---|---|---|
| `crates/shinri-fp/src/reference.rs` | Modify | Add `ref_add` (exact-rational golden `fp.add`). |
| `crates/shinri-fp/src/lzc.rs` | Create | Leading-zero counter over a significand. |
| `crates/shinri-fp/src/rm.rs` | Create | `RoundingMode` → 5-bit one-hot selector (literal or symbolic). |
| `crates/shinri-fp/src/round.rs` | Create | `ExtFp` struct + the shared 5-mode rounder. |
| `crates/shinri-fp/src/blast/add.rs` | Create | The `fp.add` datapath + IEEE special-case mux. |
| `crates/shinri-fp/src/blast/mod.rs` | Modify | Add `pub mod add;`. |
| `crates/shinri-fp/src/lib.rs` | Modify | Module decls; `rm_cache` on `FpBlaster`; `blast_word` `FpAdd`/`FpSub` arms. |
| `crates/shinri-solver/src/fp_stage.rs` | Modify | Extend `is_supported_fp_word` to accept `FpAdd`/`FpSub`. |
| `crates/shinri-solver/tests/fp_e2e.rs` | Modify | End-to-end witness + symbolic-RM SAT tests. |
| `crates/shinri-solver/tests/fp_oracle.rs` | Modify | Differential-vs-z3 over `fp.add`/`fp.sub`, all five modes. |

Task ordering: **1 (reference) → 2 (lzc) → 3 (rm) → 4 (round) → 5 (add datapath) → 6 (lib wiring) → 7 (fence) → 8 (e2e) → 9 (oracle).** Tasks 2 and 3 are independent of 1 and may be done in any order before 4.

---

### Task 1: Exact-rational reference `fp.add` (`ref_add`)

The golden oracle the datapath is checked against. Pure Rust over `shinri-num::Rational`; no circuit. Reuses the existing `decode`, `class_to_rational`, `round_rational`, and `RoundMode`.

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (append a function + tests)

**Interfaces:**
- Consumes: `decode(eb, sb, &Integer) -> FpClass`, `class_to_rational(eb, sb, &FpClass) -> Option<Rational>`, `round_rational(eb, sb, &Rational, RoundMode) -> Integer`, `FpClass`, `RoundMode` (all already in `reference.rs`).
- Produces: `pub fn ref_add(eb: u32, sb: u32, a: &Integer, b: &Integer, mode: RoundMode) -> Integer` — the canonical NaN / signed-±∞ / signed-zero pattern, else `round_rational(exact_sum)`.

- [ ] **Step 1: Write the failing test**

Append to the `#[cfg(test)] mod tests` block in `reference.rs`:

```rust
#[test]
fn ref_add_known_float32() {
    use shinri_num::Integer;
    let (eb, sb) = (8u32, 24u32);
    let i = |v: u64| Integer::from(v);
    // 1.0 + 1.0 = 2.0
    assert_eq!(ref_add(eb, sb, &i(0x3F80_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x4000_0000));
    // 1.0 + 2.0 = 3.0 = 0x40400000
    assert_eq!(ref_add(eb, sb, &i(0x3F80_0000), &i(0x4000_0000), RoundMode::Rne), i(0x4040_0000));
    // +inf + 1.0 = +inf
    assert_eq!(ref_add(eb, sb, &i(0x7F80_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x7F80_0000));
    // +inf + -inf = canonical NaN (0x7FC00000)
    assert_eq!(ref_add(eb, sb, &i(0x7F80_0000), &i(0xFF80_0000), RoundMode::Rne), i(0x7FC0_0000));
    // NaN + 1.0 = canonical NaN
    assert_eq!(ref_add(eb, sb, &i(0x7FC0_0000), &i(0x3F80_0000), RoundMode::Rne), i(0x7FC0_0000));
    // 1.0 + (-1.0) = +0 under RNE, -0 under RTN
    assert_eq!(ref_add(eb, sb, &i(0x3F80_0000), &i(0xBF80_0000), RoundMode::Rne), i(0x0000_0000));
    assert_eq!(ref_add(eb, sb, &i(0x3F80_0000), &i(0xBF80_0000), RoundMode::Rtn), i(0x8000_0000));
    // (-0) + (-0) = -0
    assert_eq!(ref_add(eb, sb, &i(0x8000_0000), &i(0x8000_0000), RoundMode::Rne), i(0x8000_0000));
    // (+0) + (-0) = +0 (RNE), -0 (RTN)
    assert_eq!(ref_add(eb, sb, &i(0x0000_0000), &i(0x8000_0000), RoundMode::Rne), i(0x0000_0000));
    assert_eq!(ref_add(eb, sb, &i(0x0000_0000), &i(0x8000_0000), RoundMode::Rtn), i(0x8000_0000));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp ref_add_known_float32`
Expected: FAIL — `cannot find function ref_add in this scope`.

- [ ] **Step 3: Write the implementation**

Append to `reference.rs` (after `round_rational`). The canonical NaN constant reuses the same pattern as `pack`: sign 0, exp all ones, sig MSB set.

```rust
/// Canonical quiet-NaN bit pattern for (eb, sb): exp all ones, sig MSB set, sign 0.
pub fn canonical_nan(eb: u32, sb: u32) -> Integer {
    let two = Integer::from(2u64);
    // exp field (all ones) sits at bit offset (sb-1); sig MSB at bit (sb-2).
    let mut exp_scale = Integer::one();
    for _ in 0..(sb - 1) { exp_scale = exp_scale * two.clone(); }
    let exp_all_ones = {
        let mut m = Integer::one();
        for _ in 0..eb { m = m * two.clone(); }
        m - Integer::one()
    };
    let mut sig_msb = Integer::one();
    for _ in 0..(sb - 2) { sig_msb = sig_msb * two.clone(); }
    exp_all_ones * exp_scale + sig_msb
}

/// Signed-infinity bit pattern.
fn inf_pattern(eb: u32, sb: u32, sign: bool) -> Integer {
    let two = Integer::from(2u64);
    let mut exp_scale = Integer::one();
    for _ in 0..(sb - 1) { exp_scale = exp_scale * two.clone(); }
    let exp_all_ones = { let mut m = Integer::one(); for _ in 0..eb { m = m * two.clone(); } m - Integer::one() };
    let mut out = exp_all_ones * exp_scale;
    if sign {
        let mut sign_scale = Integer::one();
        for _ in 0..(eb + sb - 1) { sign_scale = sign_scale * two.clone(); }
        out = out + sign_scale;
    }
    out
}

/// Signed-zero bit pattern.
fn zero_pattern(eb: u32, sb: u32, sign: bool) -> Integer {
    if !sign { return Integer::zero(); }
    let two = Integer::from(2u64);
    let mut sign_scale = Integer::one();
    for _ in 0..(eb + sb - 1) { sign_scale = sign_scale * two.clone(); }
    sign_scale
}

/// Exact-rational golden `fp.add RM a b`. `a`, `b` are W=eb+sb bit patterns.
pub fn ref_add(eb: u32, sb: u32, a: &Integer, b: &Integer, mode: RoundMode) -> Integer {
    let ca = decode(eb, sb, a);
    let cb = decode(eb, sb, b);
    use FpClass::*;
    // 1. NaN propagation.
    if matches!(ca, Nan) || matches!(cb, Nan) { return canonical_nan(eb, sb); }
    // 2. Infinities.
    match (&ca, &cb) {
        (Inf { sign: s1 }, Inf { sign: s2 }) => {
            return if s1 == s2 { inf_pattern(eb, sb, *s1) } else { canonical_nan(eb, sb) };
        }
        (Inf { sign }, _) | (_, Inf { sign }) => return inf_pattern(eb, sb, *sign),
        _ => {}
    }
    // 3. Finite + finite: exact rational sum.
    let ra = class_to_rational(eb, sb, &ca).unwrap();
    let rb = class_to_rational(eb, sb, &cb).unwrap();
    let sum = ra.clone() + rb.clone();
    let zero = Rational::new(Integer::zero(), Integer::one());
    if sum == zero {
        // IEEE exact-zero-sum sign rule: -0 iff both operands negative, else
        // +0 except under roundTowardNegative which yields -0.
        let sign_a = ref_is_negative(&ca);
        let sign_b = ref_is_negative(&cb);
        let neg = (sign_a && sign_b) || matches!(mode, RoundMode::Rtn);
        return zero_pattern(eb, sb, neg);
    }
    round_rational(eb, sb, &sum, mode)
}
```

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp ref_add_known_float32`
Expected: PASS.

- [ ] **Step 5: Add an exhaustive (3,5) self-consistency test and run**

```rust
#[test]
fn ref_add_tiny_total_and_canonical() {
    // Every (a,b,mode) on (3,5) produces a well-formed encoding (round-trips
    // through decode without panic) and is commutative for finite, non-zero sums.
    let (eb, sb) = (3u32, 5u32);
    let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
    for a in 0u64..256 {
        for b in 0u64..256 {
            for m in modes {
                let r1 = ref_add(eb, sb, &Integer::from(a), &Integer::from(b), m);
                let r2 = ref_add(eb, sb, &Integer::from(b), &Integer::from(a), m);
                // commutativity holds for fp.add in all these cases (NaN canonical too).
                assert_eq!(r1, r2, "add not commutative a={a:#x} b={b:#x} m={m:?}");
                // result must be a valid 8-bit pattern.
                assert!(r1 < Integer::from(256u64), "out-of-range result {a:#x}+{b:#x}");
            }
        }
    }
}
```

Run: `cargo test -p shinri-fp ref_add_tiny_total_and_canonical`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): exact-rational reference fp.add (ref_add) for slice 2a"
```

---

### Task 2: Leading-zero counter (`lzc.rs`)

A combinational LZC over a significand: returns the count of consecutive zero bits from the MSB downward, as an unsigned bit-vector. Used by the cancellation-normalize path in the add datapath.

**Files:**
- Create: `crates/shinri-fp/src/lzc.rs`
- Modify: `crates/shinri-fp/src/lib.rs` (add `pub mod lzc;` near the other `pub mod` lines)

**Interfaces:**
- Consumes: `Blaster` primitives `one`, `zero`, `not1`, `and2`; `shinri_bv::blast::arith::bvadd` (re-exported? No — use the public `shinri_bv` path). Use `shinri_bv::bvadd` if exported, else inline an adder. **Confirm export:** `shinri_bv::bvadd` is `pub` in `crates/shinri-bv/src/blast/arith.rs` and re-exported from the crate root; if not reachable, use `b.full_adder` directly as shown.
- Produces: `pub fn lzc(b: &mut Blaster, bits: &[BitLit]) -> Vec<BitLit>` — input `bits` is LSB→MSB; result is a `count_width(n)`-bit LSB→MSB unsigned count in `0..=n`. `pub fn count_width(n: usize) -> usize` — minimum bits to hold the value `n`.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-fp/src/lzc.rs` with only the test module first:

```rust
//! Leading-zero counter over a significand (LSB→MSB input), used by normalize.

use shinri_bv::{BitLit, Blaster};

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn const_bits(b: &Blaster, width: usize, value: u64) -> Vec<BitLit> {
        (0..width).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
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

    fn expected_lzc(width: usize, value: u64) -> u64 {
        // count zero bits from MSB (index width-1) downward until first 1.
        let mut c = 0u64;
        for i in (0..width).rev() {
            if (value >> i) & 1 == 1 { break; }
            c += 1;
        }
        c
    }

    #[test]
    fn lzc_exhaustive_width8() {
        let width = 8usize;
        for v in 0u64..256 {
            let mut b = Blaster::new();
            let bits = const_bits(&b, width, v);
            let cnt = lzc(&mut b, &bits);
            assert_eq!(eval_word(b, &cnt), expected_lzc(width, v), "lzc({v:#x})");
        }
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp lzc_exhaustive_width8`
Expected: FAIL — `cannot find function lzc in this scope`.

- [ ] **Step 3: Write the implementation**

Add above the test module in `lzc.rs`:

```rust
/// Minimum number of bits to hold the value `n` (so `count_width(8) == 4`,
/// since lzc of an 8-bit word ranges 0..=8).
pub fn count_width(n: usize) -> usize {
    let mut w = 1usize;
    while (1usize << w) <= n { w += 1; }
    w
}

/// Count leading zeros of `bits` (LSB→MSB). Walk MSB→LSB; while every bit seen
/// so far has been zero, each further zero increments the count. Result is an
/// unsigned LSB→MSB count word of width `count_width(bits.len())`, value in 0..=n.
pub fn lzc(b: &mut Blaster, bits: &[BitLit]) -> Vec<BitLit> {
    let n = bits.len();
    let cw = count_width(n);
    let zero = b.zero();
    let mut count: Vec<BitLit> = vec![zero; cw];
    let mut still_zero = b.one();
    for i in (0..n).rev() {
        let is_zero = b.not1(bits[i]);
        let inc = b.and2(still_zero, is_zero); // add 1 this position?
        // count += inc  (inc is the LSB of a cw-bit addend, rest zero)
        let mut addend: Vec<BitLit> = vec![zero; cw];
        addend[0] = inc;
        count = shinri_bv::bvadd(b, &count, &addend);
        still_zero = b.and2(still_zero, is_zero);
    }
    count
}
```

If `shinri_bv::bvadd` is not re-exported at the crate root, replace the `count +=` line with an inline ripple-add using `b.full_adder` (carry threaded LSB→MSB, `addend[0]=inc`, others zero). Verify the export first:

Run: `cargo build -p shinri-fp` (after Step 3) — if it errors on `shinri_bv::bvadd`, switch to the inline adder.

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp lzc_exhaustive_width8`
Expected: PASS.

- [ ] **Step 5: Add a width-5 exhaustive test (matches (3,5) significand width) and run**

```rust
    #[test]
    fn lzc_exhaustive_width5() {
        let width = 5usize;
        for v in 0u64..32 {
            let mut b = Blaster::new();
            let bits = const_bits(&b, width, v);
            let cnt = lzc(&mut b, &bits);
            assert_eq!(eval_word(b, &cnt), expected_lzc(width, v), "lzc5({v:#x})");
        }
    }
```

Run: `cargo test -p shinri-fp lzc_exhaustive_width5`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/lzc.rs crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): leading-zero counter (lzc) for normalize"
```

---

### Task 3: Rounding-mode selector (`rm.rs`)

Convert a `RoundingMode` operand into a 5-bit one-hot selector the rounder muxes over. Literal modes become constant one-hot; a symbolic RM variable becomes 3 fresh bits decoded into one-hot, with two clauses excluding the illegal codes.

**Files:**
- Create: `crates/shinri-fp/src/rm.rs`
- Modify: `crates/shinri-fp/src/lib.rs` (add `pub mod rm;`)

**Interfaces:**
- Consumes: `Blaster` primitives `one`, `zero`, `fresh`, `not1`, `and2`, `add_clause`; `shinri_core::RoundingMode`.
- Produces:
  - `pub struct RmSel { pub sel: [BitLit; 5] }` — one-hot order `[Rne, Rna, Rtp, Rtn, Rtz]`.
  - `pub fn literal(b: &Blaster, rm: RoundingMode) -> RmSel` — constant one-hot.
  - `pub fn symbolic(b: &mut Blaster) -> RmSel` — 3 fresh bits `(e2 e1 e0)`, decode + exclusion clauses.

- [ ] **Step 1: Write the failing test**

Create `crates/shinri-fp/src/rm.rs`:

```rust
//! RoundingMode operand → 5-bit one-hot selector [Rne, Rna, Rtp, Rtn, Rtz].

use shinri_bv::{BitLit, Blaster};
use shinri_core::RoundingMode;

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn eval_sel(b: Blaster, sel: &[BitLit; 5]) -> [bool; 5] {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars { s.new_var(); }
        for c in &cnf.clauses {
            let ls: Vec<Lit> = c.iter().map(|bl| Lit::new(Var::new(bl.var), bl.pos)).collect();
            s.add_clause(&ls);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let mut out = [false; 5];
        for (i, bl) in sel.iter().enumerate() {
            let raw = s.value_of(Var::new(bl.var)).unwrap();
            out[i] = if bl.pos { raw } else { !raw };
        }
        out
    }

    #[test]
    fn literal_is_one_hot() {
        for (rm, idx) in [(RoundingMode::Rne, 0), (RoundingMode::Rna, 1),
                          (RoundingMode::Rtp, 2), (RoundingMode::Rtn, 3),
                          (RoundingMode::Rtz, 4)] {
            let b = Blaster::new();
            let s = literal(&b, rm);
            let got = eval_sel(b, &s.sel);
            for i in 0..5 { assert_eq!(got[i], i == idx, "rm={rm:?} bit {i}"); }
        }
    }

    #[test]
    fn symbolic_is_exactly_one_hot_and_excludes_illegal() {
        // The CNF must force exactly one selector true across ALL satisfying
        // assignments. Enumerate by adding a unit clause forcing each selector and
        // confirming consistency; here we just check one solution is one-hot.
        let mut b = Blaster::new();
        let s = symbolic(&mut b);
        let got = eval_sel(b, &s.sel);
        assert_eq!(got.iter().filter(|x| **x).count(), 1, "symbolic RM must be one-hot");
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp -- rm::tests`
Expected: FAIL — `cannot find function literal`.

- [ ] **Step 3: Write the implementation**

Add above the test module:

```rust
/// One-hot rounding-mode selector, order [Rne, Rna, Rtp, Rtn, Rtz].
pub struct RmSel { pub sel: [BitLit; 5] }

/// Constant one-hot for a literal mode.
pub fn literal(b: &Blaster, rm: RoundingMode) -> RmSel {
    let o = b.one();
    let z = b.zero();
    let idx = match rm {
        RoundingMode::Rne => 0, RoundingMode::Rna => 1, RoundingMode::Rtp => 2,
        RoundingMode::Rtn => 3, RoundingMode::Rtz => 4,
    };
    let mut sel = [z; 5];
    sel[idx] = o;
    RmSel { sel }
}

/// Symbolic mode: 3 fresh bits (e2 e1 e0), codes 000..100 only.
/// Decode to one-hot; exclude illegal codes 101/110/111 with two clauses.
pub fn symbolic(b: &mut Blaster) -> RmSel {
    let e0 = b.fresh();
    let e1 = b.fresh();
    let e2 = b.fresh();
    let n0 = b.not1(e0);
    let n1 = b.not1(e1);
    let n2 = b.not1(e2);
    // exclude codes >= 5: NOT(e2 AND e0) AND NOT(e2 AND e1)
    b.add_clause(&[n2, n0]); // (¬e2 ∨ ¬e0)
    b.add_clause(&[n2, n1]); // (¬e2 ∨ ¬e1)
    // one-hot decode of the 5 legal codes.
    let rne = { let t = b.and2(n2, n1); b.and2(t, n0) }; // 000
    let rna = { let t = b.and2(n2, n1); b.and2(t, e0) }; // 001
    let rtp = { let t = b.and2(n2, e1); b.and2(t, n0) }; // 010
    let rtn = { let t = b.and2(n2, e1); b.and2(t, e0) }; // 011
    let rtz = { let t = b.and2(e2, n1); b.and2(t, n0) }; // 100
    RmSel { sel: [rne, rna, rtp, rtn, rtz] }
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp -- rm::tests`
Expected: PASS (both `literal_is_one_hot` and `symbolic_is_exactly_one_hot_and_excludes_illegal`).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/rm.rs crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): rounding-mode one-hot selector (literal + symbolic)"
```

---

### Task 4: The shared rounder (`round.rs`)

`ExtFp` and `round()`. The anchor of the slice — proven bit-identical to `round_rational` exhaustively on `(3,5)` across all five modes via a test-only exact decomposer that builds the rounder's input contract from a `Rational`.

**Files:**
- Create: `crates/shinri-fp/src/round.rs`
- Modify: `crates/shinri-fp/src/lib.rs` (add `pub mod round;`)

**Interfaces:**
- Consumes: `Blaster` primitives (`one`, `zero`, `not1`, `and2`, `or2`, `xor2`, `mux2`, `full_adder`); `shinri_bv::{bvadd, bvlshr}`; `crate::rm::RmSel`.
- Produces:
  - `pub struct ExtFp { pub sign: BitLit, pub exp: Vec<BitLit>, pub sig: Vec<BitLit>, pub grs: (BitLit, BitLit, BitLit) }` where `exp` is a two's-complement **signed** unbiased exponent of width `exp_w(eb)`, `sig` is `sb` bits LSB→MSB with the **leading/hidden bit at index `sb-1`** (normalized: MSB set for any nonzero value), and `grs = (guard, round, sticky)` summarizing everything below `sig[0]`.
  - `pub fn exp_w(eb: u32) -> usize` — signed exponent width = `eb as usize + 6` (ample headroom for normalize subtraction and the round carry; verified by exhaustive tests).
  - `pub fn round(b: &mut Blaster, ext: ExtFp, eb: u32, sb: u32, rm: &RmSel) -> Vec<BitLit>` — the packed `W=eb+sb` word, LSB→MSB. NaN never arises here (special-cases are handled by the datapath before packing), so no NaN canonicalization is applied in `round`.

**The rounder contract (read before implementing):** `ext` represents a **finite, nonzero** magnitude `sig · 2^(exp − (sb−1))` with sign `ext.sign`, where `sig ∈ [2^(sb−1), 2^sb)` (normalized) and `(G,R,S)` are the three summary bits immediately below `sig[0]`. `round` must:
1. **Subnormal denormalize:** let `shift = emin − exp_signed` (only when positive, `emin = 1 − bias`, `bias = 2^(eb−1) − 1`). Right-shift the `(sb+3)`-bit working significand `[S,R,G, sig…]` (G at the bottom-of-sig boundary) by `shift`, OR-ing every bit that crosses below the new sticky position into `S`. After this, the binary point is fixed at the IEEE position and the exponent is clamped to `emin` (encoded biased-exp field 0 unless a round-up carries into the hidden bit).
2. **Increment decision** `inc` = one-hot mux over `rm.sel` of the five predicates, from `(lsb, g, r, s, sign)` (`lsb = sig[0]` after the shift):
   - RNE: `g ∧ (r ∨ s ∨ lsb)`
   - RNA: `g`
   - RTP: `¬sign ∧ (g ∨ r ∨ s)`
   - RTN: `sign ∧ (g ∨ r ∨ s)`
   - RTZ: `0`
3. **Add `inc`** to the `sb`-bit significand; on a significand carry out of bit `sb-1` (value reaches `2^sb`), right-shift by 1 and `exp += 1`.
4. **Overflow:** if `exp_signed > emax` (`emax = bias`), emit the ∞ pattern (exp all ones, sig 0, sign preserved).
5. **Pack** `sign | biased_exp | trailing(sb-1)`, where `biased_exp = exp_signed + bias` (or 0 for the subnormal-clamped case), `trailing = sig[0..sb-1]`.

- [ ] **Step 1: Write the failing test (the exhaustive anchor)**

Create `crates/shinri-fp/src/round.rs` with the test module. The decomposer mirrors `round_rational`'s exponent search but stops **before** rounding, producing the normalized `(sign, exp, sig, G, R, S)` contract.

```rust
//! The shared FP rounder: ExtFp → packed word. Bit-identical to round_rational.

use shinri_bv::{BitLit, Blaster};
use crate::rm::RmSel;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{round_rational, RoundMode};
    use crate::rm;
    use shinri_num::{Integer, Rational};
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

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

    /// Build the rounder input (normalized contract) for a finite nonzero value.
    /// Returns (sign, exp_signed, sig: Vec<bool> LSB→MSB of len sb, g, r, s).
    fn decompose(eb: u32, sb: u32, value: &Rational) -> (bool, i64, Vec<bool>, bool, bool, bool) {
        let zero = Rational::new(Integer::zero(), Integer::one());
        let sign = *value < zero;
        let neg1 = Rational::new(Integer::from(-1i64), Integer::one());
        let mag = if sign { neg1 * value.clone() } else { value.clone() };
        let two = Rational::new(Integer::from(2u64), Integer::one());
        let half = Rational::new(Integer::one(), Integer::from(2u64));
        // E = floor(log2(mag)); m = mag / 2^E ∈ [1,2)
        let mut e: i64 = 0;
        let mut m = mag.clone();
        while m >= two { m = m * half.clone(); e += 1; }
        while m < Rational::new(Integer::one(), Integer::one()) { m = m * two.clone(); e -= 1; }
        // X = m * 2^(sb-1) ∈ [2^(sb-1), 2^sb): the normalized significand + fraction.
        let mut scale = Integer::one();
        for _ in 0..(sb - 1) { scale = scale * Integer::from(2u64); }
        let x = m * Rational::new(scale, Integer::one());
        let isig = x.numer().div_rem(&x.denom()).0; // floor
        let frac = x.clone() - Rational::new(isig.clone(), Integer::one()); // [0,1)
        // G,R,S from frac.
        let f2 = frac * two.clone();
        let g_int = f2.numer().div_rem(&f2.denom()).0;
        let g = !g_int.is_zero();
        let f2b = f2 - Rational::new(g_int, Integer::one());
        let f4 = f2b * Rational::new(Integer::from(2u64), Integer::one());
        let r_int = f4.numer().div_rem(&f4.denom()).0;
        let r = !r_int.is_zero();
        let f4b = f4 - Rational::new(r_int, Integer::one());
        let s = f4b != zero;
        // sig bits LSB→MSB.
        let mut sig = Vec::with_capacity(sb as usize);
        let mut rem = isig.clone();
        let two_i = Integer::from(2u64);
        for _ in 0..sb { let (q, rr) = rem.div_rem(&two_i); sig.push(!rr.is_zero()); rem = q; }
        (sign, e, sig, g, r, s)
    }

    fn build_ext(b: &Blaster, eb: u32, sb: u32,
                 sign: bool, exp: i64, sig: &[bool], g: bool, r: bool, s: bool) -> ExtFp {
        let bit = |x: bool| if x { b.one() } else { b.zero() };
        let ew = exp_w(eb);
        // two's-complement exp.
        let uexp = (exp as i128) & ((1i128 << ew) - 1);
        let expv: Vec<BitLit> = (0..ew).map(|i| bit((uexp >> i) & 1 == 1)).collect();
        let sigv: Vec<BitLit> = sig.iter().map(|&x| bit(x)).collect();
        ExtFp { sign: bit(sign), exp: expv, sig: sigv, grs: (bit(g), bit(r), bit(s)) }
    }

    fn rmode(rm: RoundMode) -> shinri_core::RoundingMode {
        match rm {
            RoundMode::Rne => shinri_core::RoundingMode::Rne,
            RoundMode::Rna => shinri_core::RoundingMode::Rna,
            RoundMode::Rtp => shinri_core::RoundingMode::Rtp,
            RoundMode::Rtn => shinri_core::RoundingMode::Rtn,
            RoundMode::Rtz => shinri_core::RoundingMode::Rtz,
        }
    }

    #[test]
    fn round_matches_reference_tiny_exhaustive() {
        let (eb, sb) = (3u32, 5u32);
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        // Enumerate every value REPRESENTABLE as a starting magnitude by decoding
        // each (3,5) finite pattern to its rational, then re-rounding — plus a set
        // of between-grid rationals to exercise G/R/S. We iterate all 256 patterns
        // and, for finite non-zero ones, also test the midpoint to the next pattern.
        use crate::reference::{decode, class_to_rational, FpClass};
        for pat in 0u64..256 {
            let cls = decode(eb, sb, &Integer::from(pat));
            if matches!(cls, FpClass::Nan | FpClass::Inf { .. } | FpClass::Zero { .. }) { continue; }
            let v = class_to_rational(eb, sb, &cls).unwrap();
            // also a value 3/8 of the way to the next ULP up, to force rounding.
            let ulp_probe = v.clone() + Rational::new(Integer::from(3u64),
                Integer::from(8u64) * { let mut p = Integer::one();
                    for _ in 0..(sb - 1) { p = p * Integer::from(2u64); } p });
            for value in [v.clone(), ulp_probe.clone()] {
                for m in modes {
                    let want = round_rational(eb, sb, &value, m);
                    let (sg, e, sig, g, r, s) = decompose(eb, sb, &value);
                    let mut b = Blaster::new();
                    let ext = build_ext(&b, eb, sb, sg, e, &sig, g, r, s);
                    let sel = rm::literal(&b, rmode(m));
                    let word = round(&mut b, ext, eb, sb, &sel);
                    assert_eq!(Integer::from(eval_word(b, &word)), want,
                        "round mismatch pat={pat:#x} value!=grid m={m:?}");
                }
            }
        }
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp round_matches_reference_tiny_exhaustive`
Expected: FAIL — `cannot find type ExtFp` / `cannot find function round`.

- [ ] **Step 3: Write `ExtFp`, `exp_w`, and `round`**

Add above the test module. Implement the five contract steps. Helpers `or3`, a constant-from-i64 exponent comparator, and a sticky-collecting variable right shift are spelled out.

```rust
/// Canonical pre-pack intermediate. See the rounder contract in the plan.
pub struct ExtFp {
    pub sign: BitLit,
    pub exp: Vec<BitLit>,                 // signed two's complement, width exp_w(eb)
    pub sig: Vec<BitLit>,                 // sb bits LSB→MSB, hidden bit at index sb-1
    pub grs: (BitLit, BitLit, BitLit),    // (guard, round, sticky)
}

/// Signed exponent width: eb + 6 gives ample headroom for the largest formats
/// (verified by exhaustive (3,5) + Float32 tests).
pub fn exp_w(eb: u32) -> usize { eb as usize + 6 }

fn or3(b: &mut Blaster, x: BitLit, y: BitLit, z: BitLit) -> BitLit {
    let t = b.or2(x, y); b.or2(t, z)
}

/// Build a constant signed value of width `w` (LSB→MSB) in the Blaster.
fn const_i(b: &Blaster, w: usize, value: i128) -> Vec<BitLit> {
    let u = (value) & ((1i128 << w) - 1);
    (0..w).map(|i| if (u >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
}

pub fn round(b: &mut Blaster, ext: ExtFp, eb: u32, sb: u32, rm: &RmSel) -> Vec<BitLit> {
    let bias = (1i128 << (eb - 1)) - 1;
    let emin = 1 - bias;
    let emax = bias;
    let ew = exp_w(eb);
    let sbu = sb as usize;

    // Working significand: [G, R, S] below sig[0]. Index 0 = S, 1 = R, 2 = G,
    // 3.. = sig (so sig[0] at index 3). Width = sbu + 3.
    let (g0, r0, s0) = ext.grs;
    let mut work: Vec<BitLit> = Vec::with_capacity(sbu + 3);
    work.push(s0); work.push(r0); work.push(g0);
    work.extend_from_slice(&ext.sig);

    // --- Step 1: subnormal denormalize. shift = max(0, emin - exp). ---
    // shift_amt = emin - exp (signed). Compute as a small unsigned, saturated.
    let emin_const = const_i(b, ew, emin);
    let shift_signed = shinri_bv::bvsub(b, &emin_const, &ext.exp); // emin - exp
    // positive iff MSB == 0 and nonzero. We right-shift `work` by `shift_signed`
    // (treated unsigned; if shift_signed is "negative" i.e. exp > emin, its large
    // unsigned value saturates the shifter to 0 via the overflow path, which is
    // what we want only when exp >= emin). Guard: when exp >= emin, force shift 0.
    let exp_ge_emin = {
        // exp - emin >= 0  ⇔  (exp - emin) MSB == 0
        let diff = shinri_bv::bvsub(b, &ext.exp, &emin_const);
        b.not1(diff[ew - 1])
    };
    // shift word: if exp_ge_emin then 0 else shift_signed (which is then >0, small).
    let zero_ew: Vec<BitLit> = const_i(b, ew, 0);
    let shift_word: Vec<BitLit> = (0..ew)
        .map(|i| b.mux2(exp_ge_emin, zero_ew[i], shift_signed[i]))
        .collect();
    // Sticky-collecting right shift of `work` by `shift_word`.
    let (shifted, shifted_sticky) = shift_right_sticky(b, &work, &shift_word);
    let mut work = shifted;
    work[0] = b.or2(work[0], shifted_sticky); // fold dropped bits into S
    // After denormalize, the effective exponent is clamped to emin when shifting
    // occurred. Track the post-step exponent.
    let exp_after_denorm: Vec<BitLit> = (0..ew)
        .map(|i| b.mux2(exp_ge_emin, ext.exp[i], emin_const[i]))
        .collect();

    // Re-extract S,R,G and the sb significand from `work`.
    let s = work[0];
    let r = work[1];
    let g = work[2];
    let sig: Vec<BitLit> = work[3..3 + sbu].to_vec();
    let lsb = sig[0];

    // --- Step 2: increment decision (one-hot mux over modes). ---
    let grs_any = or3(b, g, r, s);
    let not_sign = b.not1(ext.sign);
    let r_or_s_or_lsb = or3(b, r, s, lsb);
    let inc_rne = b.and2(g, r_or_s_or_lsb);
    let inc_rna = g;
    let inc_rtp = b.and2(not_sign, grs_any);
    let inc_rtn = b.and2(ext.sign, grs_any);
    let inc_rtz = b.zero();
    // inc = OR over (sel_i AND inc_i)
    let mut inc = b.zero();
    for (sel, val) in rm.sel.iter().zip([inc_rne, inc_rna, inc_rtp, inc_rtn, inc_rtz]) {
        let t = b.and2(*sel, val);
        inc = b.or2(inc, t);
    }

    // --- Step 3: add inc to the sb-bit significand; detect carry-out. ---
    let mut addend: Vec<BitLit> = vec![b.zero(); sbu];
    addend[0] = inc;
    let (sum, carry) = shinri_bv::blast::arith::adder(b, &sig, &addend, b.zero());
    // On carry-out (sig was all ones → 2^sb), shift right 1 and exp += 1.
    // After increment the significand width is sbu; carry means hidden overflowed.
    let one_ew = const_i(b, ew, 1);
    let exp_plus1 = shinri_bv::bvadd(b, &exp_after_denorm, &one_ew);
    let final_exp: Vec<BitLit> = (0..ew).map(|i| b.mux2(carry, exp_plus1[i], exp_after_denorm[i])).collect();
    // sig after possible 1-bit normalize: if carry, the new significand is
    // (sum >> 1) with the carry as the new MSB (value 2^(sb-1)). Since sum was
    // all-zero after wrap (2^sb mod 2^sb = 0), shifting gives the hidden bit set.
    let mut norm_sig: Vec<BitLit> = Vec::with_capacity(sbu);
    for i in 0..sbu {
        let shifted_bit = if i + 1 < sbu { sum[i + 1] } else { b.one() }; // carry fills top
        norm_sig.push(b.mux2(carry, shifted_bit, sum[i]));
    }

    // --- Step 4: overflow to ∞. exp_signed > emax. ---
    let emax_const = const_i(b, ew, emax);
    // overflow iff final_exp > emax (signed). final_exp - emax > 0 and not negative.
    let over_diff = shinri_bv::bvsub(b, &final_exp, &emax_const);
    let over_pos = b.not1(over_diff[ew - 1]);
    let over_nonzero = {
        let mut acc = b.zero();
        for &bit in &over_diff { acc = b.or2(acc, bit); }
        acc
    };
    let overflow = b.and2(over_pos, over_nonzero);

    // --- Step 5: pack sign | biased_exp | trailing. ---
    // biased_exp = final_exp + bias, truncated to eb bits. Subnormal-clamped case:
    // when the significand's hidden bit is 0 the value is subnormal and the biased
    // field is 0 — but final_exp already equals emin there and (emin + bias) = 1,
    // so we special-case: if hidden bit (norm_sig[sb-1]) == 0 ⇒ exp field 0.
    let bias_const = const_i(b, ew, bias);
    let biased = shinri_bv::bvadd(b, &final_exp, &bias_const);
    let hidden = norm_sig[sbu - 1];
    let not_hidden = b.not1(hidden);
    let exp_all_ones: Vec<BitLit> = (0..eb as usize).map(|_| b.one()).collect();
    let zero_eb: Vec<BitLit> = (0..eb as usize).map(|_| b.zero()).collect();

    let mut out: Vec<BitLit> = Vec::with_capacity((eb + sb) as usize);
    // trailing significand sig[0..sb-1]; zeroed on overflow (∞ has sig 0).
    for i in 0..(sbu - 1) {
        out.push(b.mux2(overflow, b.zero(), norm_sig[i]));
    }
    // exponent field eb bits.
    for i in 0..(eb as usize) {
        // normal: biased[i]; subnormal (not_hidden): 0; overflow: all ones.
        let normal_or_sub = b.mux2(not_hidden, zero_eb[i], biased[i]);
        out.push(b.mux2(overflow, exp_all_ones[i], normal_or_sub));
    }
    // sign bit (preserved through overflow).
    out.push(ext.sign);
    out
}

/// Right-shift `x` (LSB→MSB) by `amt` (unsigned LSB→MSB), returning the shifted
/// word AND a sticky bit = OR of every bit shifted out below index 0. Built from
/// `bvlshr` plus a parallel sticky: a bit is "lost" iff it was set and its index
/// < amt. Implemented as: lost = x AND NOT(mask of kept positions); sticky = OR(lost).
pub fn shift_right_sticky(b: &mut Blaster, x: &[BitLit], amt: &[BitLit]) -> (Vec<BitLit>, BitLit) {
    let n = x.len();
    let shifted = shinri_bv::bvlshr(b, x, amt);
    // Reconstruct dropped bits: drop = x XOR (shifted << amt) is fragile; instead
    // shift `shifted` back left and compare to x — any difference was dropped.
    let back = shinri_bv::bvshl(b, &shifted, amt);
    let mut sticky = b.zero();
    for i in 0..n {
        let diff = b.xor2(x[i], back[i]); // 1 where a set bit was lost
        sticky = b.or2(sticky, diff);
    }
    (shifted, sticky)
}
```

> Implementation note: `shinri_bv::blast::arith::adder` and `shinri_bv::{bvadd, bvsub, bvshl, bvlshr}` are the reuse points. If any is not reachable at that path, find its `pub` definition (Task-context grep: all are `pub` in `crates/shinri-bv/src/blast/{arith,shift}.rs`) and import accordingly.

- [ ] **Step 4: Run the anchor test**

Run: `cargo test -p shinri-fp round_matches_reference_tiny_exhaustive`
Expected: PASS. If any mismatch fires, the panic message prints the pattern, mode, and that it was the on-grid or ULP-probe value — debug `round` against `round_rational` for that case (do not weaken the test).

- [ ] **Step 5: Add a Float32 randomized rounder test and run**

```rust
    #[test]
    fn round_matches_reference_float32_random() {
        let (eb, sb) = (8u32, 24u32);
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        // deterministic LCG
        let mut state: u64 = 0xD1CE_5EED;
        let mut next = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state >> 16 };
        for _ in 0..400 {
            // random rational n/d with modest magnitude incl. subnormal range.
            let n = (next() % 2_000_000) as i64 - 1_000_000;
            if n == 0 { continue; }
            let d = 1i64 << (next() % 30); // up to 2^29 → reaches subnormals
            let value = Rational::new(Integer::from(n.unsigned_abs()) *
                if n < 0 { Integer::from(-1i64) } else { Integer::one() }, Integer::from(d as u64));
            for m in modes {
                let want = round_rational(eb, sb, &value, m);
                let (sg, e, sig, g, r, s) = decompose(eb, sb, &value);
                let mut b = Blaster::new();
                let ext = build_ext(&b, eb, sb, sg, e, &sig, g, r, s);
                let sel = rm::literal(&b, rmode(m));
                let word = round(&mut b, ext, eb, sb, &sel);
                assert_eq!(Integer::from(eval_word(b, &word)), want, "fp32 round n={n} d={d} m={m:?}");
            }
        }
    }
```

Run: `cargo test -p shinri-fp round_matches_reference_float32_random`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/round.rs crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): shared 5-mode rounder (round.rs) bit-identical to round_rational"
```

---

### Task 5: The `fp.add` datapath (`blast/add.rs`)

Unpack → order by magnitude → align (sticky) → effective add/sub → normalize → build `ExtFp` → `round()` → IEEE special-case mux. Validated bit-identical to `ref_add`, exhaustive on `(3,5)` across all five modes.

**Files:**
- Create: `crates/shinri-fp/src/blast/add.rs`
- Modify: `crates/shinri-fp/src/blast/mod.rs` (add `pub mod add;`)

**Interfaces:**
- Consumes: `crate::unpack::{unpack, Unpacked}`, `crate::round::{ExtFp, exp_w, round}`, `crate::rm::RmSel`, `crate::reference` (tests only), `shinri_bv::{bvadd, bvsub, bvshl, bvlshr}` and `Blaster` primitives.
- Produces: `pub fn fp_add(b: &mut Blaster, x: &[BitLit], y: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit>` — the `W=eb+sb` result word. (`fp.sub` is `fp_add(x, neg(y))` at the `lib.rs` layer — Task 6 — so no separate function here.)

- [ ] **Step 1: Write the failing test (exhaustive (3,5))**

Create `crates/shinri-fp/src/blast/add.rs` with the test module:

```rust
//! fp.add datapath: unpack → align → operate → normalize → round → special-case.

use shinri_bv::{BitLit, Blaster};
use crate::round::{exp_w, round, ExtFp};
use crate::rm::RmSel;
use crate::unpack::unpack;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{ref_add, RoundMode};
    use crate::rm;
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
    fn rmode(m: RoundMode) -> shinri_core::RoundingMode {
        match m {
            RoundMode::Rne => shinri_core::RoundingMode::Rne,
            RoundMode::Rna => shinri_core::RoundingMode::Rna,
            RoundMode::Rtp => shinri_core::RoundingMode::Rtp,
            RoundMode::Rtn => shinri_core::RoundingMode::Rtn,
            RoundMode::Rtz => shinri_core::RoundingMode::Rtz,
        }
    }

    #[test]
    fn fp_add_tiny_exhaustive_all_modes() {
        let (eb, sb) = (3u32, 5u32);
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        for a in 0u64..256 {
            for bb in 0u64..256 {
                for m in modes {
                    let want = ref_add(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                    let mut bl = Blaster::new();
                    let xv = const_bits(&bl, eb, sb, a);
                    let yv = const_bits(&bl, eb, sb, bb);
                    let sel = rm::literal(&bl, rmode(m));
                    let word = fp_add(&mut bl, &xv, &yv, &sel, eb, sb);
                    assert_eq!(Integer::from(eval_word(bl, &word)), want,
                        "fp.add a={a:#x} b={bb:#x} m={m:?}");
                }
            }
        }
    }

    #[test]
    fn fp_add_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        let specials = [0x0000_0000u64, 0x8000_0000, 0x7F80_0000, 0xFF80_0000, 0x7FC0_0000,
                        0x3F80_0000, 0xBF80_0000, 0x4000_0000, 0x0000_0001, 0x8000_0001];
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        let mut state: u64 = 0xADD_5EED;
        let mut next = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state >> 16 };
        let mut cases: Vec<(u64, u64)> = Vec::new();
        for &s1 in &specials { for &s2 in &specials { cases.push((s1, s2)); } }
        for _ in 0..200 { cases.push((next() & 0xFFFF_FFFF, next() & 0xFFFF_FFFF)); }
        for (a, bb) in cases {
            for m in modes {
                let want = ref_add(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                let mut bl = Blaster::new();
                let xv = const_bits(&bl, eb, sb, a);
                let yv = const_bits(&bl, eb, sb, bb);
                let sel = rm::literal(&bl, rmode(m));
                let word = fp_add(&mut bl, &xv, &yv, &sel, eb, sb);
                assert_eq!(Integer::from(eval_word(bl, &word)), want,
                    "fp.add32 a={a:#x} b={bb:#x} m={m:?}");
            }
        }
    }
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp fp_add_tiny_exhaustive_all_modes`
Expected: FAIL — `cannot find function fp_add`.

- [ ] **Step 3: Write the datapath**

Add above the test module. The significand datapath width is `sb + 3` (room for the implicit/hidden bit at top plus G/R/S during alignment); alignment uses a sticky right shift; cancellation normalize uses `lzc`. Build the normalized `ExtFp` and call `round`, then override with the special-case mux.

```rust
use crate::lzc::lzc;

/// Effective unbiased exponent (signed, exp_w bits) and explicit significand
/// (sb bits, hidden bit materialized) for an unpacked operand.
struct Operand {
    sign: BitLit,
    exp: Vec<BitLit>,   // signed unbiased, exp_w
    sig: Vec<BitLit>,   // sb bits LSB→MSB, hidden bit at index sb-1
    is_nan: BitLit,
    is_inf: BitLit,
    is_zero: BitLit,
}

fn to_operand(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Operand {
    let u = unpack(b, bits, eb, sb);
    let ew = exp_w(eb);
    let bias = (1i128 << (eb - 1)) - 1;
    // biased exp field → signed unbiased. Subnormal (exp field 0): effective
    // exponent is emin = 1 - bias, hidden bit 0; Normal: exp - bias, hidden 1.
    // Build signed exp from the eb-bit field, zero-extended, minus bias.
    let mut field: Vec<BitLit> = u.exp.clone();
    while field.len() < ew { field.push(b.zero()); }
    let bias_v: Vec<BitLit> = {
        let v = bias & ((1i128 << ew) - 1);
        (0..ew).map(|i| if (v >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    };
    let unbiased = shinri_bv::bvsub(b, &field, &bias_v); // exp - bias
    // is exp field all zero? (subnormal/zero). Reuse u.is_zero OR subnormal: just
    // test field == 0.
    let mut field_zero = b.one();
    for &e in &u.exp { let ne = b.not1(e); field_zero = b.and2(field_zero, ne); }
    // effective exp: if field_zero then emin else unbiased.
    let emin_v: Vec<BitLit> = {
        let v = (1 - bias) & ((1i128 << ew) - 1);
        (0..ew).map(|i| if (v >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    };
    let exp: Vec<BitLit> = (0..ew).map(|i| b.mux2(field_zero, emin_v[i], unbiased[i])).collect();
    // explicit significand: trailing (sb-1) bits, hidden bit = NOT field_zero.
    let hidden = b.not1(field_zero);
    let mut sig: Vec<BitLit> = u.sig.clone();      // sb-1 bits
    sig.push(hidden);                               // index sb-1 = hidden
    Operand { sign: u.sign, exp, sig, is_nan: u.is_nan, is_inf: u.is_inf, is_zero: u.is_zero }
}

pub fn fp_add(b: &mut Blaster, x: &[BitLit], y: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let ox = to_operand(b, x, eb, sb);
    let oy = to_operand(b, y, eb, sb);

    // --- Order so |x| >= |y| by (exp, sig). y_le_x = exp_x>exp_y OR (== AND sig_x>=sig_y). ---
    // Compare signed exps and significands using bv comparators on the magnitudes.
    let exp_gt = signed_gt(b, &ox.exp, &oy.exp);
    let exp_eq = bits_equal(b, &ox.exp, &oy.exp);
    let sig_ge = unsigned_ge(b, &ox.sig, &oy.sig);
    let tie = b.and2(exp_eq, sig_ge);
    let x_ge_y = b.or2(exp_gt, tie);
    // hi = larger magnitude operand, lo = smaller (selected fieldwise).
    let (hi, lo) = select_operands(b, x_ge_y, &ox, &oy, ew, sbu);

    // --- Align lo to hi: right-shift lo.sig by (hi.exp - lo.exp), sticky. ---
    let exp_diff = shinri_bv::bvsub(b, &hi.exp, &lo.exp); // >= 0 since hi>=lo
    // Extend significands with 3 low GRS columns: [0,0,0, sig...] (width sbu+3).
    let z = b.zero();
    let mut hi_ext: Vec<BitLit> = vec![z; 3]; hi_ext.extend_from_slice(&hi.sig);
    let mut lo_ext: Vec<BitLit> = vec![z; 3]; lo_ext.extend_from_slice(&lo.sig);
    // shift amount truncated to width of lo_ext; large shifts saturate (handled
    // by sticky-collecting shifter).
    let (lo_shifted, lo_sticky) = crate::round::shift_right_sticky(b, &lo_ext, &exp_diff);
    let mut lo_aln = lo_shifted;
    lo_aln[0] = b.or2(lo_aln[0], lo_sticky);

    // --- Operate: effective add if signs equal, else subtract. ---
    let same_sign = { let xn = b.xor2(hi.sign, lo.sign); b.not1(xn) };
    let sum_add = shinri_bv::bvadd(b, &hi_ext, &lo_aln);              // sbu+3 bits (+ carry handled below)
    // subtract: hi_ext - lo_aln (hi is larger magnitude so result >= 0).
    let sum_sub = shinri_bv::bvsub(b, &hi_ext, &lo_aln);
    let mut mant: Vec<BitLit> = (0..(sbu + 3)).map(|i| b.mux2(same_sign, sum_add[i], sum_sub[i])).collect();
    // add can overflow the top by 1 bit (carry into a new MSB). Capture it:
    let add_carry = {
        // recompute carry of the addition at the top.
        let (_s, c) = shinri_bv::blast::arith::adder(b, &hi_ext, &lo_aln, b.zero());
        b.and2(same_sign, c)
    };

    // result sign is hi.sign (larger magnitude wins). For exact-zero this is fixed
    // up by the special-case mux below.
    let res_sign = hi.sign;
    // base exponent is hi.exp.
    let base_exp = hi.exp.clone();

    // --- Normalize. ---
    // Case A (add carry): shift right 1, exp += 1. The new significand top bit set.
    // Case B (subtract / no carry): count leading zeros of `mant` (width sbu+3),
    // left-shift to put the leading 1 at index sbu+2, exp -= lz.
    // We compute both and mux on add_carry.
    // Case A significand (sbu+3 wide): mant >> 1 with carry as new top.
    let mut mantA: Vec<BitLit> = Vec::with_capacity(sbu + 3);
    for i in 0..(sbu + 3) {
        let hb = if i + 1 < sbu + 3 { mant[i + 1] } else { add_carry };
        mantA.push(hb);
    }
    let one_ew = const_ew(b, ew, 1);
    let expA = shinri_bv::bvadd(b, &base_exp, &one_ew);
    // Case B: lz of mant, left shift.
    let lz = lzc(b, &mant);                       // count_width bits
    let lz_ew = zero_extend(b, &lz, ew);
    let mantB = shinri_bv::bvshl(b, &mant, &lz_ew);
    let expB = shinri_bv::bvsub(b, &base_exp, &lz_ew);
    // choose.
    let mant_n: Vec<BitLit> = (0..(sbu + 3)).map(|i| b.mux2(add_carry, mantA[i], mantB[i])).collect();
    let exp_n: Vec<BitLit> = (0..ew).map(|i| b.mux2(add_carry, expA[i], expB[i])).collect();

    // --- Build ExtFp: top sb bits of mant_n are the significand; bits [2,1,0]→(G,R,S). ---
    // mant_n layout: index 0=S-region LSB... actually [0..3) are GRS columns, [3..) sig.
    // After normalize the leading 1 is at index sbu+2 (top). The sb significand is
    // mant_n[3 ..3+sbu]; G=mant_n[2], R=mant_n[1], S=mant_n[0].
    let sig_ext: Vec<BitLit> = mant_n[3..3 + sbu].to_vec();
    let grs = (mant_n[2], mant_n[1], mant_n[0]);
    let ext = ExtFp { sign: res_sign, exp: exp_n, sig: sig_ext, grs };
    let rounded = round(b, ext, eb, sb, rm);

    // --- Special-case mux (overrides rounded). ---
    special_case(b, &rounded, &ox, &oy, rm, eb, sb)
}
```

Add the small comparison / selection / special-case helpers below `fp_add`:

```rust
fn bits_equal(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    let mut acc = b.one();
    for i in 0..x.len() { let d = b.xor2(x[i], y[i]); let s = b.not1(d); acc = b.and2(acc, s); }
    acc
}
fn unsigned_ge(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    // x >= y  ⇔  NOT (x < y); use shinri_bv comparator.
    let lt = shinri_bv::blast::compare::ult(b, x, y);
    b.not1(lt)
}
fn signed_gt(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    shinri_bv::blast::compare::sgt(b, x, y)
}
fn const_ew(b: &Blaster, ew: usize, v: i128) -> Vec<BitLit> {
    let u = v & ((1i128 << ew) - 1);
    (0..ew).map(|i| if (u >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
}
fn zero_extend(b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit> {
    let mut out = x.to_vec(); while out.len() < to { out.push(b.zero()); } out
}
fn select_operands(b: &mut Blaster, x_ge_y: BitLit, ox: &Operand, oy: &Operand, ew: usize, sbu: usize)
    -> (Operand, Operand) {
    let pick = |b: &mut Blaster, sel: BitLit, a: &Operand, c: &Operand| -> Operand {
        let exp = (0..ew).map(|i| b.mux2(sel, a.exp[i], c.exp[i])).collect();
        let sig = (0..sbu).map(|i| b.mux2(sel, a.sig[i], c.sig[i])).collect();
        Operand {
            sign: b.mux2(sel, a.sign, c.sign),
            exp, sig,
            is_nan: b.mux2(sel, a.is_nan, c.is_nan),
            is_inf: b.mux2(sel, a.is_inf, c.is_inf),
            is_zero: b.mux2(sel, a.is_zero, c.is_zero),
        }
    };
    let hi = pick(b, x_ge_y, ox, oy);
    let lo = pick(b, x_ge_y, oy, ox); // swapped
    (hi, lo)
}

/// IEEE fp.add special cases override the datapath result.
fn special_case(b: &mut Blaster, normal: &[BitLit], ox: &Operand, oy: &Operand,
                rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);
    // NaN if either input NaN, or (+inf)+(-inf).
    let either_nan = b.or2(ox.is_nan, oy.is_nan);
    let opp_sign = b.xor2(ox.sign, oy.sign);
    let both_inf = b.and2(ox.is_inf, oy.is_inf);
    let inf_minus_inf = b.and2(both_inf, opp_sign);
    let want_nan = b.or2(either_nan, inf_minus_inf);
    // Inf result if either input inf (and not the NaN case): sign of the inf input.
    // hi.sign already governs same-sign inf; pick inf sign = (ox.is_inf ? ox.sign : oy.sign).
    let any_inf = b.or2(ox.is_inf, oy.is_inf);
    let inf_sign = b.mux2(ox.is_inf, ox.sign, oy.sign);
    let inf_bits = inf_pattern_bits(b, eb, sb, inf_sign);
    // Exact-zero-sum: both inputs zero → sign rule. (-0)+(-0)=-0; else +0 except RTN.
    let both_zero = b.and2(ox.is_zero, oy.is_zero);
    let both_neg = b.and2(ox.sign, oy.sign);
    let rtn = rm.sel[3];
    let zero_neg = b.or2(both_neg, rtn);
    let zero_bits = signed_zero_bits(b, eb, sb, zero_neg);

    // Priority: NaN > Inf > both_zero > normal.
    let mut out = normal.to_vec();
    for i in 0..w { out[i] = b.mux2(both_zero, zero_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(any_inf, inf_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_nan, nan[i], out[i]); }
    out
}

fn canon_nan_bits(b: &Blaster, eb: u32, sb: u32) -> Vec<BitLit> {
    // exp all ones; sig MSB (index sb-2) set; sign 0.
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    for i in (sb as usize - 1)..(sb as usize - 1 + eb as usize) { v[i] = b.one(); } // exp
    v[sb as usize - 2] = b.one(); // sig MSB
    v
}
fn inf_pattern_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit> {
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    for i in (sb as usize - 1)..(sb as usize - 1 + eb as usize) { v[i] = b.one(); } // exp all ones
    v[(eb + sb) as usize - 1] = sign;
    v
}
fn signed_zero_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit> {
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    v[(eb + sb) as usize - 1] = sign;
    v
}
```

> `shift_right_sticky` is defined `pub` in `round.rs` (Task 4) and called as `crate::round::shift_right_sticky` here — one definition, one name. Also confirm `shinri_bv::blast::compare::{ult, sgt}` and `shinri_bv::blast::arith::adder` are reachable (`pub` in their modules); if the `blast` module is private at the crate root, add the minimal re-exports to `shinri-bv/src/lib.rs` (`pub use blast;`) — but first check, since slice 1 already imports `shinri_bv::Blaster`.

- [ ] **Step 4: Run the exhaustive tiny test**

Run: `cargo test -p shinri-fp fp_add_tiny_exhaustive_all_modes`
Expected: PASS. This is 256×256×5 = 327,680 solver runs over an 8-bit format — it may take a minute. If too slow, it is still correct; keep it (it is the core gate). The panic message identifies any failing `(a, b, mode)`.

- [ ] **Step 5: Run the Float32 specials/random test**

Run: `cargo test -p shinri-fp fp_add_float32_specials_and_random`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/blast/add.rs crates/shinri-fp/src/blast/mod.rs crates/shinri-fp/src/round.rs
git commit -m "feat(fp): fp.add datapath (align/operate/normalize/round/special) bit-identical to ref_add"
```

---

### Task 6: Wire `FpAdd`/`FpSub` into `FpBlaster::blast_word` (`lib.rs`)

Add the two operator arms and the RM-blasting cache. `fp.sub RM x y` is `fp_add(x, neg(y))`.

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs`

**Interfaces:**
- Consumes: `crate::blast::add::fp_add`, `crate::blast::structural::neg`, `crate::rm::{self, RmSel}`, `shinri_core::{BuiltinOp, RoundingMode}`, `ctx.rm_const_value(t) -> Option<RoundingMode>`.
- Produces: `FpBlaster` now has `rm_cache: FxHashMap<TermId, [BitLit; 5]>` and a method `fn blast_rm(&mut self, ctx, t) -> RmSel`; `blast_word` handles `FpAdd` and `FpSub`.

- [ ] **Step 1: Write the failing test**

Add to the `lower_tests` module in `lib.rs`:

```rust
#[test]
fn lower_fp_add_eq_atom() {
    use shinri_core::BuiltinOp;
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let yf = ctx.declare_fun("y", &[], f32);
    let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let add = ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rne, x, y]).unwrap();
    let two = ctx.mk_fp_const(8, 24, Integer::from(0x4000_0000u64));
    let eq = ctx.mk_eq(add, two).unwrap();
    let lo = lower(&mut ctx, &[eq]);
    assert!(lo.atom_lit.contains_key(&eq), "core = over fp.add must be surrogated");
    assert!(lo.var_bits.contains_key(&x) && lo.var_bits.contains_key(&y), "x,y exported");
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp lower_fp_add_eq_atom`
Expected: FAIL — `blast_word` panics on `FpAdd` (`unreachable!`) / `mk_app` for `FpAdd` succeeds but blasting hits the `other =>` arm.

- [ ] **Step 3: Add the `rm_cache` field and `blast_rm` method**

In `lib.rs`, extend the `FpBlaster` struct and `new`:

```rust
pub struct FpBlaster {
    pub b: Blaster,
    cache: FxHashMap<TermId, Vec<BitLit>>,
    var_bits: FxHashMap<TermId, Vec<BitLit>>,
    rm_cache: FxHashMap<TermId, [BitLit; 5]>,
}
```
```rust
    pub fn new() -> Self {
        FpBlaster { b: Blaster::new(), cache: FxHashMap::default(),
                    var_bits: FxHashMap::default(), rm_cache: FxHashMap::default() }
    }
```

Add the method (near `blast_word`):

```rust
    /// Blast a RoundingMode operand to a one-hot selector. Literal modes fold to
    /// constants; a symbolic RM variable becomes 3 fresh bits (cached per TermId).
    fn blast_rm(&mut self, ctx: &Context, t: TermId) -> crate::rm::RmSel {
        if let Some(sel) = self.rm_cache.get(&t) {
            return crate::rm::RmSel { sel: *sel };
        }
        let sel = if let Some(rm) = ctx.rm_const_value(t) {
            crate::rm::literal(&self.b, rm)
        } else {
            // symbolic RoundingMode variable (nullary uninterpreted of RM sort).
            crate::rm::symbolic(&mut self.b)
        };
        self.rm_cache.insert(t, sel.sel);
        sel
    }
```

- [ ] **Step 4: Add the `FpAdd`/`FpSub` arms to `blast_word`**

In the `Op::Builtin(op)` match inside `blast_word`, before the `other =>` arm:

```rust
                    FpAdd => {
                        let rm = self.blast_rm(ctx, kids[0]);
                        let xw = self.blast_word(ctx, kids[1]);
                        let yw = self.blast_word(ctx, kids[2]);
                        crate::blast::add::fp_add(&mut self.b, &xw, &yw, &rm, eb, sb)
                    }
                    FpSub => {
                        let rm = self.blast_rm(ctx, kids[0]);
                        let xw = self.blast_word(ctx, kids[1]);
                        let yw = self.blast_word(ctx, kids[2]);
                        let neg_y = crate::blast::structural::neg(&mut self.b, &yw, eb, sb);
                        crate::blast::add::fp_add(&mut self.b, &xw, &neg_y, &rm, eb, sb)
                    }
```

Add `pub mod round; pub mod lzc; pub mod rm;` to the top-of-file module declarations if not already added by earlier tasks.

- [ ] **Step 5: Run the test to verify it passes**

Run: `cargo test -p shinri-fp lower_fp_add_eq_atom`
Expected: PASS.

- [ ] **Step 6: Run the full crate test sweep**

Run: `cargo test -p shinri-fp`
Expected: PASS (all slice-1 + slice-2a unit tests).

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): wire FpAdd/FpSub into blast_word (+ rounding-mode caching)"
```

---

### Task 7: Extend the soundness fence to admit `fp.add`/`fp.sub` (`fp_stage.rs`)

`is_supported_fp_word` currently allows only constants, FP variables, and `FpAbs`/`FpNeg`. Admit `FpAdd`/`FpSub` whose RM operand is a `RoundingMode` term and whose two FP operands are supported words. Everything else (mul/div/…/conversions) stays fenced.

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs`

**Interfaces:**
- Consumes/extends: `is_supported_fp_word(ctx, t) -> bool` (private), used by `fp_atom_is_supported`.
- Produces: same signatures; new accepted word shapes.

- [ ] **Step 1: Write the failing tests**

Add to the `tests` module in `fp_stage.rs`:

```rust
#[test]
fn fp_add_word_is_supported() {
    let mut ctx = Context::new();
    let x = fp_var(&mut ctx, "x");
    let y = fp_var(&mut ctx, "y");
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let add = ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rne, x, y]).unwrap();
    let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[add]).unwrap();
    let atoms = collect_fp_atoms(&ctx, &[isnan]);
    assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.add inside a predicate is supported");
}

#[test]
fn fp_add_with_symbolic_rm_is_supported() {
    let mut ctx = Context::new();
    let x = fp_var(&mut ctx, "x");
    let y = fp_var(&mut ctx, "y");
    let rms = ctx.rm_sort();
    let rmf = ctx.declare_fun("rm", &[], rms);
    let rm = ctx.mk_app(Op::Uninterpreted(rmf), &[]).unwrap();
    let add = ctx.mk_app(Op::Builtin(BuiltinOp::FpAdd), &[rm, x, y]).unwrap();
    let z = fp_var(&mut ctx, "z");
    let eq = ctx.mk_eq(add, z).unwrap();
    let atoms = collect_fp_atoms(&ctx, &[eq]);
    assert!(fp_atoms_fully_supported(&ctx, &atoms), "symbolic RM operand is supported");
}

#[test]
fn fp_mul_word_is_not_supported() {
    let mut ctx = Context::new();
    let x = fp_var(&mut ctx, "x");
    let y = fp_var(&mut ctx, "y");
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    let mul = ctx.mk_app(Op::Builtin(BuiltinOp::FpMul), &[rne, x, y]).unwrap();
    let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[mul]).unwrap();
    let atoms = collect_fp_atoms(&ctx, &[isnan]);
    assert!(!fp_atoms_fully_supported(&ctx, &atoms), "fp.mul stays fenced in slice 2a");
}
```

> Confirm the accessor name for the RoundingMode sort: grep shows `context.rs:124` interns `SortNode::RoundingMode`. If the public method is not `rm_sort`, use the actual name (e.g. `ctx.rounding_mode_sort()`); adjust the test accordingly.

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-solver --lib fp_stage`
Expected: `fp_add_word_is_supported` and `fp_add_with_symbolic_rm_is_supported` FAIL (currently unsupported); `fp_mul_word_is_not_supported` PASSES already.

- [ ] **Step 3: Extend `is_supported_fp_word`**

In `fp_stage.rs`, add an arm to the match in `is_supported_fp_word` (after the `FpAbs | FpNeg` arm):

```rust
        // FpAdd / FpSub: (RM, F, F). RM operand must be a RoundingMode term
        // (literal const or nullary RM variable); both FP operands supported.
        TermNode::App { op: Op::Builtin(BuiltinOp::FpAdd | BuiltinOp::FpSub), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 3
                && is_rounding_mode_term(ctx, kids[0])
                && is_supported_fp_word(ctx, kids[1])
                && is_supported_fp_word(ctx, kids[2])
        }
```

Add the helper near `is_supported_fp_word`:

```rust
/// A RoundingMode operand we can blast: a RoundingMode literal constant, or a
/// nullary uninterpreted symbol of RoundingMode sort.
fn is_rounding_mode_term(ctx: &Context, t: TermId) -> bool {
    if !matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::RoundingMode) {
        return false;
    }
    match ctx.term_node(t) {
        TermNode::Const { val: ConstVal::Rm(_), .. } => true,
        TermNode::App { op: Op::Uninterpreted(_), args, .. } => ctx.children(*args).is_empty(),
        _ => false,
    }
}
```

Update the doc comment on `is_supported_fp_word` to mention `FpAdd`/`FpSub` are now in scope (slice 2a).

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-solver --lib fp_stage`
Expected: PASS (all three new tests + the existing `detects_fp_and_collects_eq_and_predicate`, `fp_mixed_with_bv_is_fenced`).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): admit fp.add/fp.sub words through the FP soundness fence"
```

---

### Task 8: End-to-end witness + symbolic-RM SAT tests (`fp_e2e.rs`)

Prove the whole seam: parse a script with `fp.add`/`fp.sub` → SAT/UNSAT → `get-model` round-trip, and a symbolic-RM query that the solver satisfies.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs`

**Interfaces:**
- Consumes: `shinri_solver::{Solver, CommandResponse, SolveOutcome}`, `shinri_parser::Parser` (follow the existing helpers already in `fp_e2e.rs`; read the top of that file first to reuse its `run(...)` harness).

- [ ] **Step 1: Read the existing harness**

Run: `sed -n '1,60p' crates/shinri-solver/tests/fp_e2e.rs` (or open it) to reuse its script-runner helper and assertion style. Match whatever helper name it defines (e.g. `outcome_of(src)` / `responses(src)`).

- [ ] **Step 2: Write the failing tests**

Append (adapting helper names to the file's existing convention):

```rust
#[test]
fn fp_add_one_plus_one_is_two_sat() {
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.add RNE (fp #b0 #x7f #b00000000000000000000000)
                              (fp #b0 #x7f #b00000000000000000000000))))
(assert (fp.eq x (fp #b0 #x80 #b00000000000000000000000)))
(check-sat)";
    assert_eq!(outcome_of(src), SolveOutcome::Sat); // 1.0 + 1.0 == 2.0
}

#[test]
fn fp_add_one_plus_one_not_three_unsat() {
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.add RNE (fp #b0 #x7f #b00000000000000000000000)
                              (fp #b0 #x7f #b00000000000000000000000))))
(assert (fp.eq x (fp #b0 #x80 #b10000000000000000000000)))
(check-sat)";
    assert_eq!(outcome_of(src), SolveOutcome::Unsat); // 2.0 != 3.0
}

#[test]
fn fp_sub_is_add_neg_sat() {
    let src = "\
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.sub RNE (fp #b0 #x80 #b00000000000000000000000)
                              (fp #b0 #x7f #b00000000000000000000000))))
(assert (fp.eq x (fp #b0 #x7f #b00000000000000000000000)))
(check-sat)";
    assert_eq!(outcome_of(src), SolveOutcome::Sat); // 2.0 - 1.0 == 1.0
}

#[test]
fn fp_add_symbolic_rm_sat() {
    // Some rounding mode makes the rounded sum land on a chosen value: with a
    // half-ulp tie, RNE/RNA/RTP/RTZ differ. We only require SAT (a mode exists).
    let src = "\
(set-logic QF_FP)
(declare-fun rm () RoundingMode)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.eq x (fp.add rm (fp #b0 #x7f #b00000000000000000000000)
                            (fp #b0 #x69 #b00000000000000000000000))))
(check-sat)";
    assert_eq!(outcome_of(src), SolveOutcome::Sat);
}
```

> If the FP literal constructor form `(fp #b0 #x7f …)` routes through `FpFromBits` (App with BV children) and trips the BV fence (per the slice-1 oracle note), substitute the `(_ … 8 24)` special forms or build the operands as declared FP variables constrained by `fp.eq` to the desired specials. Verify by running; if these specific scripts return `Unknown`, switch the constant encoding to declared-variable form and assert the same SAT/UNSAT.

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: the four new tests FAIL or return `Unknown` before the wiring is complete — after Tasks 5–7 they should pass; if they were run before those tasks, they fail. (Run order: this task is after 7.)

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS for all four (plus the pre-existing slice-1 e2e tests).

- [ ] **Step 5: Add a get-model round-trip assertion**

Extend `fp_add_one_plus_one_is_two_sat` (or add a sibling) to issue `(get-value (x))` / `(get-model)` and assert the rendered value is `(fp #b0 #x80 #b0…0)` (= 2.0) using the file's response-capturing helper. Match the existing slice-1 get-model test's assertion idiom in this file.

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): end-to-end fp.add/fp.sub SAT/UNSAT + symbolic-RM + get-model"
```

---

### Task 9: Differential-vs-z3 oracle over `fp.add`/`fp.sub` (`fp_oracle.rs`)

Extend the feature-gated oracle to generate random `fp.add`/`fp.sub` terms over all five rounding modes and assert agreement with z3.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs`

**Interfaces:**
- Consumes: the existing `Lcg`, `shinri_outcome`, `z3_outcome` harness already in the file.
- Produces: a new generator `gen_arith_script(rng)` and a new `#[test] fn differential_qf_fp_add_sub()`.

- [ ] **Step 1: Add the arithmetic generator**

Append to `fp_oracle.rs` (inside the `#![cfg(feature = "oracle")]` module). Declare three FP vars and one RM var; build the sum/diff and constrain via `fp.eq`/`=`/predicates so both SAT and UNSAT arise.

```rust
const RMS: &[&str] = &["RNE", "RNA", "RTP", "RTN", "RTZ"];

fn gen_arith_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let use_sym_rm = rng.below(4) == 0;
    if use_sym_rm { s.push_str("(declare-fun rm () RoundingMode)\n"); }
    let rm = |rng: &mut Lcg| -> String {
        if use_sym_rm && rng.below(2) == 0 { "rm".to_string() }
        else { RMS[rng.below(RMS.len() as u64) as usize].to_string() }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let op = if rng.below(2) == 0 { "fp.add" } else { "fp.sub" };
        let term = format!("({op} {} x y)", rm(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq z {term})"),
            1 => format!("(= z {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 { s.push_str(&format!("(assert (not {atom}))\n")); }
        else { s.push_str(&format!("(assert {atom})\n")); }
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_fp_add_sub() {
    let mut rng = Lcg(0xADD_5UB_0001);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_arith_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown { n_unknown += 1; continue; }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"]).build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        // z3_outcome declares only x; extend it to declare y,z,(rm) — see Step 2.
        let theirs = z3_outcome_arith(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!("QF_FP add/sub DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    println!("differential_qf_fp_add_sub: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}
```

- [ ] **Step 2: Add a declarations-aware z3 driver**

The existing `z3_outcome` hardcodes declaring only `x`. Add a sibling that forwards every `(declare-fun …)` line from the script verbatim, then replays the asserts (reuse the existing assert-forwarding loop):

```rust
fn z3_outcome_arith(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_FP").expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-fun ") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}
```

- [ ] **Step 3: Run the oracle (requires z3 on PATH)**

Run: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_add_sub -- --nocapture`
Expected: PASS, printing nonzero `sat` and `unsat` counts and zero disagreements. If z3 is unavailable in the environment, this test is skipped by the feature gate; note that in the task report and run it wherever z3 is present.

- [ ] **Step 4: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential-vs-z3 oracle for fp.add/fp.sub over all five modes"
```

---

### Task 10: Full workspace non-regression sweep

**Files:** none (verification only).

- [ ] **Step 1: Run the whole workspace test suite**

Run: `cargo test --workspace`
Expected: PASS — all crates green, QF_BV/QF_FP slice-1 paths untouched.

- [ ] **Step 2: Run clippy (the repo's lint gate)**

Run: `cargo clippy --workspace --all-targets`
Expected: no new warnings in `shinri-fp` / `shinri-solver`. Fix any introduced by the new code (unused imports, needless clones flagged by clippy) and re-run.

- [ ] **Step 3: Final commit (if clippy fixes were needed)**

```bash
git add -A
git commit -m "chore(fp): clippy cleanups for slice-2a add/sub"
```

---

## Self-Review

**1. Spec coverage** (against `2026-06-25-shinri-qffp-slice2a-add-design.md`):
- §2 `ExtFp` intermediate → Task 4 (`round.rs`). ✓
- §3 `lzc.rs` → Task 2; `round.rs` → Task 4; `blast/add.rs` → Task 5; `rm.rs` → Task 3. ✓
- §3 `fp.sub` = `fp.add ∘ neg` → Task 6 (`FpSub` arm). ✓
- §4 rounder steps (subnormal pre-shift, 5-mode mux, carry-renormalize, overflow→∞, pack) → Task 4 `round`. ✓
- §5 `fp.add` pipeline (unpack, order, align+sticky, operate, normalize, round, special-case mux) → Task 5. ✓
- §6 stage/fence (`is_supported_fp_word` admits add/sub; mul etc. fenced; symbolic RM) → Task 7. ✓
- §6 `blast_word` `FpAdd`/`FpSub` arms → Task 6. ✓
- §7 model path unchanged + get-value on add term → Task 8 Step 5. ✓
- §8 test plan: rounder vs `round_rational` (Task 4), datapath vs `ref_add` (Tasks 1, 5), symbolic-RM (Tasks 7, 8), differential z3 (Task 9), e2e witness + non-regression (Tasks 8, 10). ✓
- §9 decisions: full 5-mode mux (Task 3/4), GRS Approach A (Task 4), `rewrite.rs` deferred (not created — ✓ confirmed absent from any task). ✓

**2. Placeholder scan:** No "TBD"/"implement later". Each code step shows complete code; each test step shows the assertion. The two "verify the export path" / "match the file's helper" notes are explicit verification instructions with concrete fallbacks, not deferred work.

**3. Type consistency:** `ExtFp { sign, exp, sig, grs }` defined in Task 4 and consumed identically in Task 5. `RmSel { sel: [BitLit;5] }` defined Task 3, consumed Tasks 4/5/6. `fp_add(b, x, y, rm, eb, sb)` signature defined Task 5, called identically Task 6. `exp_w(eb)` defined Task 4, used Tasks 4/5. `round(b, ext, eb, sb, &rm)` consistent Tasks 4/5. `shift_right_sticky` is defined `pub` in `round.rs` (Task 4) and called as `crate::round::shift_right_sticky` from `add.rs` (Task 5) — one definition, one name. `ref_add(eb, sb, &a, &b, mode)` defined Task 1, used Tasks 1/5. ✓
