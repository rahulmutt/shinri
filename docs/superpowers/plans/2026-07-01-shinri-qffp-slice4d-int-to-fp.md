# QF_FP Slice 4d — int→FP (`to_fp` signed-BV + `to_fp_unsigned`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit the two integer→FP conversion faces — `((_ to_fp eb sb) RM x)` with a signed-BV source and `((_ to_fp_unsigned eb sb) RM x)` — as a real rounding datapath through the unified `Lowerer`.

**Architecture:** One new gadget `to_fp_int` in `crates/shinri-fp/src/convert.rs` (sign+magnitude → shared `prenormalize` → exponent clamp → static significand split → shared `round()` → zero mux), mirroring the shape of the existing `to_fp_fp`. `blast_fp_word` routes the 2-arg BV-source `ToFp` face and a new `ToFpUnsigned` arm to it; the BV child blasts through the sort-dispatched `Lowerer::word` (slice-4c seam). The soundness fence in `fp_stage.rs` un-crosses these two faces. Golden reference: thin wrappers over the existing `round_rational`.

**Tech Stack:** Rust workspace (`shinri-*` crates), `shinri-bv` `Blaster`/`WordSink` seam, `shinri-num::{Integer, Rational}`, z3 via `easy_smt` for the differential oracle.

## Global Constraints

- **Soundness first:** anything out of scope returns `Unknown`, never a wrong SAT/UNSAT. The only faces admitted this slice are `ToFp`-2-arg-BV (signed) and `ToFpUnsigned` (unsigned). `FpToUbv` / `FpToSbv` / `FpToReal` / symbolic-Real `to_fp` stay fenced.
- **`x = 0` → `+0`** under every rounding mode (matches `round_rational` on exact zero).
- **INT_MIN:** after the m-bit negate the magnitude is read **unsigned** (`|INT_MIN| = 2^(m-1)` fits in m bits unsigned) — exact by construction.
- **Crossing-canary cross-slice lesson:** pre-flight canary hunt BEFORE the fence edit; after admitting the ops run the **whole** `fp_e2e` suite and the whole `fp_stage` unit-test module; repoint stale `Unknown`-canaries at `fp.to_ubv`/`fp.to_sbv`. Do not run partial suites.
- **Long runs (z3 oracle, exhaustive gates, full workspace):** run them in the background yourself and poll; do not block, do not dispatch a subagent to babysit them.
- Follow existing file patterns; no unrelated refactoring.

---

### Task 1: Reference wrappers — `ref_to_fp_sbv` / `ref_to_fp_ubv`

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (two functions near `round_rational`; one test in the existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `round_rational(eb, sb, &Rational, RoundMode) -> Integer` (reference.rs:253), `field(bits, lo, width)` (reference.rs:18), `Rational::from_int(Integer)`.
- Produces: `pub fn ref_to_fp_sbv(eb: u32, sb: u32, m: u32, x: &Integer, mode: RoundMode) -> Integer` and `pub fn ref_to_fp_ubv(eb: u32, sb: u32, m: u32, x: &Integer, mode: RoundMode) -> Integer` — `x` is the m-bit pattern as a non-negative Integer; result is the packed `(eb+sb)`-bit FP value. Trusted golden for Tasks 2 and 6.

- [ ] **Step 1: Write the failing test**

Add to the `#[cfg(test)] mod tests` block in `crates/shinri-fp/src/reference.rs`:

```rust
#[test]
fn ref_int_to_fp_pins_known_values() {
    // Signed read: 8-bit 0xFF = -1 → f32 0xBF800000; 0x80 = -128 → 0xC3000000.
    let f = |v: u64| Integer::from(v);
    assert_eq!(ref_to_fp_sbv(8, 24, 8, &f(0xFF), RoundMode::Rne), f(0xBF80_0000));
    assert_eq!(ref_to_fp_sbv(8, 24, 8, &f(0x80), RoundMode::Rne), f(0xC300_0000));
    // Unsigned read of the same pattern: 255 → 0x437F0000.
    assert_eq!(ref_to_fp_ubv(8, 24, 8, &f(0xFF), RoundMode::Rne), f(0x437F_0000));
    // Zero → +0 under every mode (incl. RTN — conversions have no -0 source).
    for mode in [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz] {
        assert_eq!(ref_to_fp_sbv(8, 24, 8, &Integer::zero(), mode), Integer::zero());
        assert_eq!(ref_to_fp_ubv(8, 24, 8, &Integer::zero(), mode), Integer::zero());
    }
    // Rounding is real: u32::MAX → f32 is 2^32 under RNE (0x4F800000),
    // 2^32-256 under RTZ (0x4F7FFFFF).
    assert_eq!(ref_to_fp_ubv(8, 24, 32, &f(0xFFFF_FFFF), RoundMode::Rne), f(0x4F80_0000));
    assert_eq!(ref_to_fp_ubv(8, 24, 32, &f(0xFFFF_FFFF), RoundMode::Rtz), f(0x4F7F_FFFF));
    // Overflow is real: 255 into (3,5) (max finite 15.5) → +oo (0x70) under RNE,
    // max finite (0x6F) under RTZ.
    assert_eq!(ref_to_fp_ubv(3, 5, 8, &f(0xFF), RoundMode::Rne), f(0x70));
    assert_eq!(ref_to_fp_ubv(3, 5, 8, &f(0xFF), RoundMode::Rtz), f(0x6F));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `cargo test -p shinri-fp --lib ref_int_to_fp_pins_known_values`
Expected: FAIL — `cannot find function ref_to_fp_sbv in this scope`.

- [ ] **Step 3: Write minimal implementation**

Add just after `round_rational` in `crates/shinri-fp/src/reference.rs`:

```rust
/// `((_ to_fp eb sb) rm x)` for `x` an m-bit BV read as a SIGNED two's-complement
/// integer. An integer is an exact rational, so this is a thin wrapper over
/// `round_rational`: signed value = x - 2^m when the sign bit (bit m-1) is set.
pub fn ref_to_fp_sbv(eb: u32, sb: u32, m: u32, x: &Integer, mode: RoundMode) -> Integer {
    let neg = !field(x, m - 1, 1).is_zero();
    let v = if neg {
        let two = Integer::from(2u64);
        let mut pow_m = Integer::one();
        for _ in 0..m { pow_m = pow_m * two.clone(); }
        x.clone() - pow_m
    } else {
        x.clone()
    };
    round_rational(eb, sb, &Rational::from_int(v), mode)
}

/// `((_ to_fp_unsigned eb sb) rm x)`: the m-bit pattern read UNSIGNED. `x` is
/// already the non-negative value; the width `m` is kept for signature symmetry.
pub fn ref_to_fp_ubv(eb: u32, sb: u32, _m: u32, x: &Integer, mode: RoundMode) -> Integer {
    round_rational(eb, sb, &Rational::from_int(x.clone()), mode)
}
```

(`Rational` is already imported at the top of `reference.rs` for `round_rational`; if not, add `use shinri_num::Rational;`.)

- [ ] **Step 4: Run test to verify it passes**

Run: `cargo test -p shinri-fp --lib ref_int_to_fp_pins_known_values`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): ref_to_fp_sbv/ref_to_fp_ubv — exact int→FP golden over round_rational (slice 4d)"
```

---

### Task 2: The `to_fp_int` gadget

**Files:**
- Modify: `crates/shinri-fp/src/convert.rs` — add `to_fp_int` after `to_fp_fp`; add three tests in the existing `#[cfg(test)] mod tests` (helpers `const_bits`, `eval_word`, `MODES` already exist there).

**Interfaces:**
- Consumes: `prenormalize(b, sig, exp, sbu, ew)` (blast/normalize.rs:23 — width-generic), `const_n` (blast/normalize.rs:8), `round`/`exp_w`/`ExtFp` (round.rs), `signed_zero_bits` (blast/operand.rs:64), `bvneg`/`bvsub` (shinri_bv::blast::arith), `RmSel` (rm.rs), Task 1's `ref_to_fp_sbv`/`ref_to_fp_ubv`.
- Produces: `pub fn to_fp_int(b: &mut Blaster, x: &[BitLit], signed: bool, eb_t: u32, sb_t: u32, rm: &RmSel) -> Vec<BitLit>` — the rounded `(eb_t+sb_t)`-bit FP word. Consumed by Task 3's dispatch.

- [ ] **Step 1: Write the failing tests**

Add to `#[cfg(test)] mod tests` in `crates/shinri-fp/src/convert.rs`. Add the import `use crate::convert::to_fp_int;` next to the existing `use crate::convert::{to_fp_fp, to_fp_real_const};`, and `use crate::reference::{ref_to_fp_sbv, ref_to_fp_ubv};` next to the existing reference imports. Add one helper next to `const_bits`:

```rust
    fn const_bv(b: &Blaster, w: u32, value: u64) -> Vec<BitLit> {
        (0..w).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    }
```

Then the tests:

```rust
    #[test]
    fn to_fp_int_8bit_exhaustive_both_faces() {
        // Every 8-bit pattern, signed AND unsigned, into (3,5) (narrow: rounding,
        // overflow→±inf/max-finite by mode) and (5,11) (widen: exact), all five
        // modes, bit-identical vs the golden.
        for &(core_rm, ref_rm) in &MODES {
            for (eb, sb) in [(3u32, 5u32), (5, 11)] {
                for a in 0u64..256 {
                    for signed in [true, false] {
                        let want = if signed {
                            ref_to_fp_sbv(eb, sb, 8, &Integer::from(a), ref_rm)
                        } else {
                            ref_to_fp_ubv(eb, sb, 8, &Integer::from(a), ref_rm)
                        };
                        let mut b = Blaster::new();
                        let xw = const_bv(&b, 8, a);
                        let sel = rm::literal(&b, core_rm);
                        let got_w = to_fp_int(&mut b, &xw, signed, eb, sb, &sel);
                        let got = eval_word(b, &got_w);
                        assert_eq!(Integer::from(got), want,
                            "int→({eb},{sb}) signed={signed} mode {ref_rm:?} a={a:#x}: got {got:#x} want {want}");
                    }
                }
            }
        }
    }

    #[test]
    fn to_fp_int_tiny_width_edges() {
        // m = 1 and m = 2: the LZC/negate edge widths. Signed m=1 covers {0, -1};
        // signed m=2 covers INT_MIN = -2 (negate wraps, magnitude read unsigned).
        for &(core_rm, ref_rm) in &MODES {
            for m in [1u32, 2] {
                for a in 0u64..(1 << m) {
                    for signed in [true, false] {
                        let want = if signed {
                            ref_to_fp_sbv(8, 24, m, &Integer::from(a), ref_rm)
                        } else {
                            ref_to_fp_ubv(8, 24, m, &Integer::from(a), ref_rm)
                        };
                        let mut b = Blaster::new();
                        let xw = const_bv(&b, m, a);
                        let sel = rm::literal(&b, core_rm);
                        let got_w = to_fp_int(&mut b, &xw, signed, 8, 24, &sel);
                        let got = eval_word(b, &got_w);
                        assert_eq!(Integer::from(got), want,
                            "int{m}→f32 signed={signed} mode {ref_rm:?} a={a}: got {got:#x} want {want}");
                    }
                }
            }
        }
    }

    #[test]
    fn to_fp_int_64bit_random_into_f32() {
        // 64-bit sources into Float32: deep narrowing (drop = 40 bits) exercises
        // the sticky collapse. Seeded specials: 0, ±1, INT_MIN/MAX, u64::MAX,
        // powers of two ± 1 (tie and just-off-tie patterns).
        let cases: &[u64] = &[
            0, 1, u64::MAX,                       // 0, 1, -1 signed / max unsigned
            0x8000_0000_0000_0000,                // i64::MIN
            0x7FFF_FFFF_FFFF_FFFF,                // i64::MAX
            (1u64 << 25), (1u64 << 25) + 1, (1u64 << 25) - 1, // around the f32 tie boundary
            (1u64 << 63) + 1,
        ];
        let mut state = 0x0DD5_EED5_1234_5678u64;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state };
        for &(core_rm, ref_rm) in &MODES {
            for iter in 0..100 {
                let a = if iter < cases.len() { cases[iter] } else { rand() };
                for signed in [true, false] {
                    let want = if signed {
                        ref_to_fp_sbv(8, 24, 64, &Integer::from(a), ref_rm)
                    } else {
                        ref_to_fp_ubv(8, 24, 64, &Integer::from(a), ref_rm)
                    };
                    let mut b = Blaster::new();
                    let xw = const_bv(&b, 64, a);
                    let sel = rm::literal(&b, core_rm);
                    let got_w = to_fp_int(&mut b, &xw, signed, 8, 24, &sel);
                    let got = eval_word(b, &got_w);
                    assert_eq!(Integer::from(got), want,
                        "int64→f32 signed={signed} mode {ref_rm:?} a={a:#x}: got {got:#x} want {want}");
                }
            }
        }
    }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp --lib to_fp_int`
Expected: FAIL — `cannot find function to_fp_int in this scope` (compile error).

- [ ] **Step 3: Write the gadget**

Add to `crates/shinri-fp/src/convert.rs` after `to_fp_fp`. Extend the existing arith import to `use shinri_bv::blast::arith::{bvneg, bvsub};`:

```rust
/// `((_ to_fp eb_t sb_t) rm x)` for a BV source read SIGNED (`signed = true`) and
/// `((_ to_fp_unsigned eb_t sb_t) rm x)` (`signed = false`): round the integer
/// value of the m-bit word `x` into the target format.
/// sign+magnitude → prenormalize (LZC) → exponent clamp → static significand
/// split → shared rounder → zero mux. No NaN/Inf inputs exist; `x = 0` → `+0`
/// under every mode (matches `round_rational`).
#[allow(clippy::needless_range_loop)] // indices are load-bearing: parallel-indexed words
pub fn to_fp_int(
    b: &mut Blaster, x: &[BitLit], signed: bool, eb_t: u32, sb_t: u32, rm: &RmSel,
) -> Vec<BitLit> {
    let m = x.len();
    let sbt = sb_t as usize;
    let w = (eb_t + sb_t) as usize;
    let ew_t = exp_w(eb_t);

    // --- 1. sign + magnitude. The m-bit negate is exact: the only value whose
    //     negation doesn't fit signed is INT_MIN, and |INT_MIN| = 2^(m-1) fits
    //     UNSIGNED in m bits — mag is read unsigned from here on. ---
    let sign = if signed { *x.last().unwrap() } else { b.zero() };
    let mag: Vec<BitLit> = if signed {
        let neg = bvneg(b, x);
        (0..m).map(|i| b.mux2(sign, neg[i], x[i])).collect()
    } else {
        x.to_vec()
    };

    // --- 2. prenormalize: value = (mag / 2^(m-1)) · 2^(m-1), i.e. hidden bit at
    //     index m-1, unbiased exponent m-1. The working exponent width wc must
    //     hold [0, m-1] and the clamp compares without wrap:
    //     bits_for(m) = smallest width holding m-1 as a signed value. ---
    let bits_for_m = (64 - (m as u64).leading_zeros()) as usize + 1;
    let wc = ew_t.max(bits_for_m) + 1;
    let e0 = const_n(b, wc, m as i128 - 1);
    let (m_n, e_n) = prenormalize(b, &mag, &e0, m, wc);

    // --- 3. exponent clamp into round()'s range (same shape as to_fp_fp: the
    //     low-saturate is unreachable here — a nonzero integer has exp ≥ 0 —
    //     but keeping the block identical keeps one shared shape). ---
    let bias_t = (1i128 << (eb_t - 1)) - 1;
    let emax_t = bias_t;
    let emin_t = 1 - bias_t;
    let hi = emax_t + 1;                    // round(): exp > emax_t → overflow → ±inf
    let lo = emin_t - (sbt as i128 + 2);    // round(): deep denormalize → ±0
    let hi_w = const_n(b, wc, hi);
    let lo_w = const_n(b, wc, lo);
    // gt_hi = e_n > hi (signed): (e_n - hi) positive and nonzero.
    let d_hi = bvsub(b, &e_n, &hi_w);
    let gt_hi = {
        let pos = b.not1(d_hi[wc - 1]);
        let mut nz = b.zero();
        for &bit in &d_hi { nz = b.or2(nz, bit); }
        b.and2(pos, nz)
    };
    // lt_lo = e_n < lo (signed): (e_n - lo) negative.
    let d_lo = bvsub(b, &e_n, &lo_w);
    let lt_lo = d_lo[wc - 1];
    let clamped: Vec<BitLit> = (0..wc).map(|i| {
        let hi_or_x = b.mux2(gt_hi, hi_w[i], e_n[i]);
        b.mux2(lt_lo, lo_w[i], hi_or_x)
    }).collect();
    let e_t: Vec<BitLit> = clamped[..ew_t].to_vec(); // clamped fits → low ew_t bits exact

    // --- 4. significand: static split, m in the role of sb_s (same as to_fp_fp). ---
    let (sig_t, grs): (Vec<BitLit>, (BitLit, BitLit, BitLit)) = if sbt >= m {
        // widen: exact — pad (sb_t - m) low zeros; GRS = 0.
        let pad = sbt - m;
        let mut s = vec![b.zero(); pad];
        s.extend_from_slice(&m_n); // len sbt, leading 1 at index sbt-1
        (s, (b.zero(), b.zero(), b.zero()))
    } else {
        // narrow: keep top sb_t bits; dropped low bits form guard/round/sticky.
        let drop = m - sbt;
        let s = m_n[drop..m].to_vec(); // len sbt, leading 1 at index sbt-1
        let g = m_n[drop - 1];
        let r = if drop >= 2 { m_n[drop - 2] } else { b.zero() };
        let mut st = b.zero();
        for i in 0..drop.saturating_sub(2) { st = b.or2(st, m_n[i]); }
        (s, (g, r, st))
    };

    let ext = ExtFp { sign, exp: e_t, sig: sig_t, grs };
    let mut out = round(b, ext, eb_t, sb_t, rm);

    // --- 5. zero mux: x = 0 → +0 (all modes). ---
    let mut is_zero = b.one();
    for &bit in x {
        let nb = b.not1(bit);
        is_zero = b.and2(is_zero, nb);
    }
    let plus = b.zero();
    let pz = signed_zero_bits(b, eb_t, sb_t, plus);
    for i in 0..w { out[i] = b.mux2(is_zero, pz[i], out[i]); }
    out
}
```

- [ ] **Step 4: Run tests to verify they pass** *(the 8-bit exhaustive is 5120 tiny solver calls — minutes, run in background and poll)*

Run (background): `cargo test -p shinri-fp --lib to_fp_int`
Expected: PASS (all three tests).

- [ ] **Step 5: Confirm no pure-FP regression**

Run (background): `cargo test -p shinri-fp`
Expected: PASS — existing FP unit tests untouched.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/convert.rs
git commit -m "feat(fp): to_fp_int gadget — int→FP via prenormalize + shared rounder (slice 4d)"
```

---

### Task 3: Dispatch arms in `blast_fp_word`

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` — extend the 2-arg `ToFp` branch and add a `ToFpUnsigned` arm in `blast_fp_word` (lib.rs:210-228); add two tests in the existing `#[cfg(test)] mod lower_tests`.

**Interfaces:**
- Consumes: `to_fp_int` (Task 2), `WordSink::word` (routes the BV child to `blast_bv_word` under a `Lowerer`), `blast_rm`, `ctx.bv_width(sort) -> Option<u32>`.
- Produces: `blast_fp_word` returns a rounded FP word for `ToFp`-2-arg-BV and `ToFpUnsigned`. Consumed end-to-end by Task 4's fence lift.

- [ ] **Step 1: Write the failing tests**

Add to `#[cfg(test)] mod lower_tests` in `crates/shinri-fp/src/lib.rs` (same module as `to_fp_1arg_bitcast_is_identity`; it already has `Lowerer`, `WordSink`, `Context`, `Op`, `BuiltinOp` in scope):

```rust
    #[test]
    fn to_fp_2arg_bv_source_blasts_to_fp_width() {
        // Signed int→FP: routes the BV child through the sort-dispatched sink and
        // returns an eb+sb word. (Value correctness is pinned by the convert.rs
        // exhaustive gates and the e2e tests — this drives the dispatch arm.)
        let mut ctx = Context::new();
        let bv8 = ctx.bv_sort(8);
        let bf = ctx.declare_fun("b", &[], bv8);
        let b = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let conv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, b]).unwrap();

        let mut lw = Lowerer::new();
        let bw = lw.word(&ctx, b);
        let fw = lw.word(&ctx, conv);
        assert_eq!(bw.len(), 8, "BV child is 8 bits");
        assert_eq!(fw.len(), 32, "signed int→FP result is eb+sb bits");
    }

    #[test]
    fn to_fp_unsigned_blasts_to_fp_width() {
        let mut ctx = Context::new();
        let bv8 = ctx.bv_sort(8);
        let bf = ctx.declare_fun("b", &[], bv8);
        let b = ctx.mk_app(Op::Uninterpreted(bf), &[]).unwrap();
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let conv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFpUnsigned { eb: 8, sb: 24 }), &[rne, b]).unwrap();

        let mut lw = Lowerer::new();
        let fw = lw.word(&ctx, conv);
        assert_eq!(fw.len(), 32, "unsigned int→FP result is eb+sb bits");
    }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp --lib to_fp_2arg_bv_source_blasts_to_fp_width to_fp_unsigned_blasts_to_fp_width`
Expected: FAIL — the first panics in the `ToFp` else-branch (`ctx.fp_widths(...).expect("FP source operand")` on a BV-sorted child); the second hits `other => unreachable!("blast_word: FP op ToFpUnsigned …")`.

- [ ] **Step 3: Write the dispatch**

In `crates/shinri-fp/src/lib.rs`, `blast_fp_word`, replace the 2-arg else-branch of the `ToFp { .. }` arm (lib.rs:216-227). Current:

```rust
                    } else {
                        // 2-arg (RM, X), X = Float (FP→FP re-round) | const Real (fold).
                        // BV / symbolic-Real sources stay fenced (later slices).
                        let rm = blast_rm(sink, ctx, kids[0]);
                        if let Some(q) = ctx.const_real_value(kids[1]) {
                            crate::convert::to_fp_real_const(sink.blaster(), &q, eb, sb, &rm)
                        } else {
                            let (eb_s, sb_s) = ctx.fp_widths(ctx.sort_of(kids[1])).expect("FP source operand");
                            let xw = sink.word(ctx, kids[1]);
                            crate::convert::to_fp_fp(sink.blaster(), &xw, eb_s, sb_s, eb, sb, &rm)
                        }
                    }
```

New:

```rust
                    } else {
                        // 2-arg (RM, X), X = Float (FP→FP re-round) | const Real (fold)
                        // | BV (signed int→FP, slice 4d). Symbolic-Real stays fenced.
                        let rm = blast_rm(sink, ctx, kids[0]);
                        if let Some(q) = ctx.const_real_value(kids[1]) {
                            crate::convert::to_fp_real_const(sink.blaster(), &q, eb, sb, &rm)
                        } else if ctx.bv_width(ctx.sort_of(kids[1])).is_some() {
                            // Signed int→FP: the BV child blasts through the
                            // sort-dispatched sink (requires the unified Lowerer).
                            let xw = sink.word(ctx, kids[1]);
                            crate::convert::to_fp_int(sink.blaster(), &xw, true, eb, sb, &rm)
                        } else {
                            let (eb_s, sb_s) = ctx.fp_widths(ctx.sort_of(kids[1])).expect("FP source operand");
                            let xw = sink.word(ctx, kids[1]);
                            crate::convert::to_fp_fp(sink.blaster(), &xw, eb_s, sb_s, eb, sb, &rm)
                        }
                    }
```

And add a `ToFpUnsigned` arm directly after the whole `ToFp { .. }` arm:

```rust
                ToFpUnsigned { .. } => {
                    // Unsigned int→FP (slice 4d): (RM, bv) — same gadget, no sign step.
                    let rm = blast_rm(sink, ctx, kids[0]);
                    let xw = sink.word(ctx, kids[1]);
                    crate::convert::to_fp_int(sink.blaster(), &xw, false, eb, sb, &rm)
                }
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp --lib to_fp_2arg_bv_source_blasts_to_fp_width to_fp_unsigned_blasts_to_fp_width`
Expected: PASS.

- [ ] **Step 5: Confirm no pure-FP regression**

Run (background): `cargo test -p shinri-fp`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): blast_fp_word dispatch for int→FP (ToFp 2-arg BV + ToFpUnsigned) (slice 4d)"
```

---

### Task 4: Lift the fence + repoint the unit canaries

**Files:**
- Modify: `crates/shinri-solver/src/fp_stage.rs` — `uses_crossing_conversion` (un-cross the two faces + doc comment), `is_supported_fp_word` (extend `ToFp` 2-arg, add `ToFpUnsigned` arm + doc comment), repoint the two flipped asserts in `crossing_conversions_detected_supported_faces_not` (fp_stage.rs:593, :599), add one new test.

**Interfaces:**
- Consumes: `is_rounding_mode_term`, `SortNode::BitVec` sort checks, the total-BV-blaster invariant (4c argument: no recursive support check on BV children).
- Produces: `uses_crossing_conversion` returns `false` for `ToFp`-2-arg-BV and `ToFpUnsigned`; `is_supported_fp_word` returns `true` for both. End-to-end int→FP solving now works.

- [ ] **Step 1: Pre-flight canary hunt** *(standing cross-slice lesson — BEFORE editing the fence)*

Run: `rg -n "ToFpUnsigned|to_fp_unsigned" crates/ --type rust`
Run: `rg -n "to_fp 8 24\) RNE b|to_fp from BV|signed-int" crates/shinri-solver/tests crates/shinri-solver/src/fp_stage.rs`

Expected known flips (verify, and note anything additional for Steps 4-5 / Task 5):
- `crates/shinri-solver/src/fp_stage.rs:593` — `assert!(uses_crossing_conversion(...), "to_fp from BV is crossing")`
- `crates/shinri-solver/src/fp_stage.rs:599` — `assert!(uses_crossing_conversion(...), "to_fp_unsigned is crossing")`
- `crates/shinri-solver/tests/fp_e2e.rs:641-643` — the "signed-int BV → FP" entry in `to_fp_bv_crossing_and_symbolic_real_are_unknown` (repointed in Task 5)

If the hunt surfaces canaries beyond these three, repoint them in the same pattern (unit ones this task, e2e ones in Task 5).

- [ ] **Step 2: Write the failing test**

Add to `#[cfg(test)] mod tests` in `crates/shinri-solver/src/fp_stage.rs`:

```rust
    #[test]
    fn int_to_fp_faces_admitted_nested_crossing_still_caught() {
        let mut ctx = Context::new();
        let f32s = ctx.fp_sort(8, 24);
        let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
        let bvs = ctx.bv_sort(32);
        let bvf = ctx.declare_fun("bv", &[], bvs);
        let bv = ctx.mk_app(Op::Uninterpreted(bvf), &[]).unwrap();

        // Both int→FP faces: NOT crossing, supported (slice 4d).
        let signed = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
        let unsigned =
            ctx.mk_app(Op::Builtin(BuiltinOp::ToFpUnsigned { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[signed]), "signed int→FP admitted");
        assert!(!uses_crossing_conversion(&ctx, &[unsigned]), "unsigned int→FP admitted");
        assert!(super::is_supported_fp_word(&ctx, signed), "signed int→FP word supported");
        assert!(super::is_supported_fp_word(&ctx, unsigned), "unsigned int→FP word supported");

        // Safety net: a still-crossing op nested INSIDE the BV child is caught
        // by the same DAG walk.
        let xf = ctx.declare_fun("x", &[], f32s);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let ubv = ctx.mk_app(Op::Builtin(BuiltinOp::FpToUbv(32)), &[rne, x]).unwrap();
        let nested = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, ubv]).unwrap();
        assert!(uses_crossing_conversion(&ctx, &[nested]), "nested fp.to_ubv still crossing");
    }
```

- [ ] **Step 3: Run test to verify it fails**

Run: `cargo test -p shinri-solver --lib fp_stage::tests::int_to_fp_faces_admitted_nested_crossing_still_caught`
Expected: FAIL — `uses_crossing_conversion` still returns `true` for both faces.

- [ ] **Step 4: Edit the fence**

In `uses_crossing_conversion` (fp_stage.rs:73-89): remove `ToFpUnsigned` from the always-crossing list and flip the `BitVec` arm:

```rust
            let is_crossing = match op {
                Op::Builtin(BuiltinOp::FpToUbv(_))
                | Op::Builtin(BuiltinOp::FpToSbv(_))
                | Op::Builtin(BuiltinOp::FpToReal) => true,
                Op::Builtin(BuiltinOp::ToFp { .. }) => match kids.len() {
                    1 => false, // 1-arg BV bitcast — admitted in slice 4c
                    2 => match ctx.sort_node(ctx.sort_of(kids[1])) {
                        SortNode::BitVec(_) => false, // signed int→FP — admitted in slice 4d
                        // symbolic Real is crossing; a constant Real is 3a-supported.
                        SortNode::Real => ctx.const_real_value(kids[1]).is_none(),
                        _ => false, // Float → FP (3a-supported)
                    },
                    _ => true, // defensive: unexpected arity
                },
                _ => false,
            };
```

Update the doc comment above the function (fp_stage.rs:55-64): the crossing set is now `FpToUbv` / `FpToSbv` / `FpToReal` / symbolic-Real `ToFp`; note `ToFpUnsigned` and the `ToFp` BV-source face were admitted in slice 4d.

In `is_supported_fp_word`, extend the `ToFp` 2-arg arm (fp_stage.rs:265-266) to accept a BV-sorted operand:

```rust
                // 2-arg faces: FP→FP re-round / constant-Real fold (3a), or
                // signed int→FP from a BV source (4d). BV children need only a
                // sort check — the BV blaster is total, nested crossings are
                // caught by `uses_crossing_conversion` (same argument as 4c).
                2 => is_rounding_mode_term(ctx, kids[0])
                    && (is_supported_fp_word(ctx, kids[1])
                        || ctx.const_real_value(kids[1]).is_some()
                        || matches!(ctx.sort_node(ctx.sort_of(kids[1])), SortNode::BitVec(_))),
```

and add a `ToFpUnsigned` arm just after the whole `ToFp` arm:

```rust
        // to_fp_unsigned: (RM, bv) — unsigned int→FP (slice 4d). BV-sort check
        // only, per the 4c total-BV-blaster argument.
        TermNode::App { op: Op::Builtin(BuiltinOp::ToFpUnsigned { .. }), args, .. } => {
            let kids = ctx.children(*args).to_vec();
            kids.len() == 2
                && is_rounding_mode_term(ctx, kids[0])
                && matches!(ctx.sort_node(ctx.sort_of(kids[1])), SortNode::BitVec(_))
        }
```

Also update the `is_supported_fp_word` doc comment (fp_stage.rs:176-194) to mention the two 4d faces.

- [ ] **Step 5: Repoint the flipped unit canaries**

In `crossing_conversions_detected_supported_faces_not` (fp_stage.rs:591-599), flip the two stale asserts — the crossing role is already covered by the `fp.to_sbv` assert at :590:

```rust
        // to_fp from BV (2-arg, BV source) → NOT crossing (admitted in slice 4d).
        let from_bv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[from_bv]), "signed int→FP admitted (slice 4d)");
```

```rust
        // to_fp_unsigned → NOT crossing (admitted in slice 4d).
        let uns = ctx.mk_app(Op::Builtin(BuiltinOp::ToFpUnsigned { eb: 8, sb: 24 }), &[rne, bv]).unwrap();
        assert!(!uses_crossing_conversion(&ctx, &[uns]), "unsigned int→FP admitted (slice 4d)");
```

Plus any additional unit canaries surfaced by Step 1's hunt.

- [ ] **Step 6: Run the whole fp_stage module** *(no partial runs)*

Run: `cargo test -p shinri-solver --lib fp_stage`
Expected: PASS — the new test green, both repointed asserts green, every other fence test (symbolic-Real, `fp.to_sbv`, `fp.to_real`, arity rejections) unchanged.

- [ ] **Step 7: Commit**

```bash
git add crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): lift the fence for int→FP (ToFp 2-arg BV + ToFpUnsigned) (slice 4d)"
```

---

### Task 5: End-to-end SAT/UNSAT + get-model, and repoint the e2e canary

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` — add a slice-4d block; remove the now-solvable signed-int entry from `to_fp_bv_crossing_and_symbolic_real_are_unknown` (fp_e2e.rs:641-643).

**Interfaces:**
- Consumes: `run(src) -> (SolveOutcome, String)` (already in the file).

- [ ] **Step 1: Write the e2e tests**

Add a new block near the slice-4c block in `crates/shinri-solver/tests/fp_e2e.rs`:

```rust
// ── Slice-4d end-to-end: int→FP (to_fp 2-arg BV + to_fp_unsigned) ───────────
#[test]
fn to_fp_signed_bv_sat_with_model() {
    // The only 8-bit signed b with value -1 is 0xFF; -1.0f32 is
    // (fp #b1 #b01111111 #b0…0). Pins the signed read end-to-end.
    let src = "\
(declare-fun b () (_ BitVec 8))
(assert (fp.eq ((_ to_fp 8 24) RNE b) (fp #b1 #b01111111 #b00000000000000000000000)))
(check-sat)
(get-model)";
    let (o, model) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "b = 0xFF reads as -1 signed");
    assert!(model.contains("b"), "model surfaces the BV source var");
}

#[test]
fn to_fp_unsigned_never_negative_unsat() {
    // An unsigned read is ≥ 0, and fp.lt equates ±0 — so strictly-below -0 is
    // impossible. Distinguishes the unsigned face from the signed one.
    let src = "\
(declare-fun b () (_ BitVec 8))
(assert (fp.lt ((_ to_fp_unsigned 8 24) RNE b) (_ -zero 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Unsat, "unsigned int→FP is never negative");
}

#[test]
fn to_fp_signed_bv_negative_sat() {
    // The signed counterpart of the test above IS satisfiable (any b ≥ 0x80).
    let src = "\
(declare-fun b () (_ BitVec 8))
(assert (fp.lt ((_ to_fp 8 24) RNE b) (_ -zero 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "signed int→FP can be negative");
}

#[test]
fn to_fp_unsigned_rounding_pin_sat() {
    // u32::MAX = 4294967295 is not f32-representable; RNE rounds up to 2^32.
    // The right-hand side goes through the (independent) const-Real face.
    let src = "\
(declare-fun b () (_ BitVec 32))
(assert (= b #xffffffff))
(assert (fp.eq ((_ to_fp_unsigned 8 24) RNE b) ((_ to_fp 8 24) RNE 4294967296.0)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "u32::MAX rounds to 2^32 under RNE");
}

#[test]
fn to_fp_zero_is_plus_zero_sat() {
    // Core = distinguishes ±0: the conversion of integer 0 must be exactly +0.
    let src = "\
(declare-fun b () (_ BitVec 8))
(assert (= b #x00))
(assert (= ((_ to_fp 8 24) RTN b) (_ +zero 8 24)))
(check-sat)";
    let (o, _) = run(src);
    assert_eq!(o, SolveOutcome::Sat, "int 0 → +0 even under RTN");
}
```

- [ ] **Step 2: Run to verify they pass** (gadget + fence already in place from Tasks 2-4)

Run: `cargo test -p shinri-solver --test fp_e2e to_fp_signed to_fp_unsigned to_fp_zero`
Expected: PASS. (An `Unknown` means Task 4's fence lift is incomplete; an inverted SAT/UNSAT points at Task 2's gadget — the sign mux or the split.)

- [ ] **Step 3: Repoint the stale e2e crossing canary**

In `to_fp_bv_crossing_and_symbolic_real_are_unknown` (fp_e2e.rs:632), **remove** the now-solvable entry:

```rust
        // signed-int BV → FP (2-arg to_fp with BV operand)
        "(declare-fun b () (_ BitVec 32)) (declare-fun z () Float32) \
         (assert (fp.eq z ((_ to_fp 8 24) RNE b))) (check-sat)",
```

Leave the other three (symbolic-Real `to_fp`, `fp.to_sbv`, `fp.to_real`). Update the test's doc comment: int→FP is admitted as of slice 4d; the remaining fence is FP→BV + the Real bridge.

- [ ] **Step 4: Run the WHOLE fp_e2e suite + grep-audit** *(cross-slice lesson — no partial run)*

Run (background): `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS — every test, all remaining crossing canaries still `Unknown`.

Run: `rg -n 'SolveOutcome::Unknown' crates/shinri-solver/tests/fp_e2e.rs`
Expected: the three remaining crossing entries plus other legitimately-`Unknown` canaries; confirm none is an int→FP form.

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): e2e int→FP SAT/UNSAT + get-model; repoint the signed-int crossing canary (slice 4d)"
```

---

### Task 6: Differential z3 oracle for int→FP

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` — add `gen_int_to_fp_script` and `differential_qf_bvfp_int_to_fp`, mirroring `gen_bitcast_script` / `differential_qf_bvfp_bitcast` (fp_oracle.rs:1035-1120).

**Interfaces:**
- Consumes: `Lcg`, `shinri_outcome`, `z3_outcome_mixed` (QF_BVFP logic), `N_ITERS` — all already in the file.

- [ ] **Step 1: Write the generator + differential test**

Add to `crates/shinri-solver/tests/fp_oracle.rs`, after the bitcast oracle:

```rust
/// One int→FP script: a constant BV converted BOTH ways — signed 2-arg `to_fp`
/// and `to_fp_unsigned` — under a random rounding mode and target format, then
/// related with a random FP relation. Signed and unsigned reads agree exactly
/// when the top bit is clear and diverge otherwise, so the relation verdict is
/// mode-, format- and sign-sensitive. Verdicts are decidable (constant source).
fn gen_int_to_fp_script(rng: &mut Lcg) -> String {
    const WIDTHS: &[u32] = &[8, 16, 32];
    let mw = WIDTHS[rng.below(WIDTHS.len() as u64) as usize];
    let word = rng.next() & ((1u64 << mw) - 1);
    // Half Float32, half Float16 — Float16 overflows on large 16/32-bit values
    // (mode-dependent: RNE→+oo, RTZ→max finite), which is exactly the boundary
    // we want cross-checked.
    let (eb, sb) = if rng.below(2) == 0 { (8u32, 24u32) } else { (5, 11) };
    const FP_RELS: &[&str] = &["fp.lt", "fp.leq", "fp.gt", "fp.geq", "fp.eq"];
    let rel = FP_RELS[rng.below(FP_RELS.len() as u64) as usize];
    const RMS: &[&str] = &["RNE", "RNA", "RTP", "RTN", "RTZ"];
    let rm = RMS[rng.below(RMS.len() as u64) as usize];
    format!(
        "(declare-fun b () (_ BitVec {mw}))\n\
         (declare-fun p () (_ FloatingPoint {eb} {sb}))\n\
         (declare-fun q () (_ FloatingPoint {eb} {sb}))\n\
         (assert (= b (_ bv{word} {mw})))\n\
         (assert (= p ((_ to_fp {eb} {sb}) {rm} b)))\n\
         (assert (= q ((_ to_fp_unsigned {eb} {sb}) {rm} b)))\n\
         (assert ({rel} p q))\n\
         (check-sat)\n"
    )
}

#[test]
fn differential_qf_bvfp_int_to_fp() {
    let mut rng = Lcg(0x1_2FE_4D4D);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_int_to_fp_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_mixed(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_BVFP INT→FP SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_bvfp_int_to_fp: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(n_z3_checked > 0, "z3 never returned a concrete verdict — check the logic/harness");
}
```

- [ ] **Step 2: Run the oracle in the background** *(long-running — shells out to z3 per iteration)*

Run (background): `cargo test -p shinri-solver --test fp_oracle differential_qf_bvfp_int_to_fp -- --nocapture`
Expected: PASS with `sat>0 unsat>0 z3_checked>0` printed, `unknown=0`, no SOUNDNESS DISAGREEMENT panic. Poll for completion; do not block.

If z3 disagrees: the printed script isolates it — a signed/unsigned flip shows on top-bit-set words, a rounder mismatch on Float16 overflow words.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential z3 oracle for int→FP (slice 4d)"
```

---

### Task 7: Full workspace green + mark the design landed

**Files:**
- Modify: `docs/superpowers/specs/2026-07-01-shinri-qffp-slice4d-int-to-fp-design.md` (status → landed).

- [ ] **Step 1: Full workspace test** *(multi-minute — background, poll)*

Run (background): `cargo test --workspace`
Expected: PASS — no regressions in pure-BV, pure-FP, or mixed paths; prior-slice verdicts byte-identical.

- [ ] **Step 2: Clippy**

Run: `cargo clippy --workspace --all-targets -- -D warnings`
Expected: no new warnings.

- [ ] **Step 3: Mark the design landed**

Change the design doc's `**Status:**` line to `Landed` with a one-line verification summary (suite counts, oracle sat/unsat/z3_checked numbers, canaries repointed), matching the convention of the 3a/4c docs.

- [ ] **Step 4: Commit**

```bash
git add docs/superpowers/specs/2026-07-01-shinri-qffp-slice4d-int-to-fp-design.md
git commit -m "docs(qffp): mark slice-4d landed — int→FP admitted"
```

---

## Self-Review

**Spec coverage:**
- §2 semantics (round_rational anchor, zero→+0, overflow, rounding) → Task 1 pins + Task 2 gates. ✓
- §3 gadget steps 1-5 (sign+mag, prenormalize, clamp, split, round+zero-mux) → Task 2 Step 3, structure mirrors the spec section-by-section. ✓
- §3 dispatch (ToFp 2-arg BV branch + ToFpUnsigned arm, sink-routed BV child) → Task 3. ✓
- §3 constants-not-special-cased → Task 5's constant-source e2e tests + Task 6's constant-source oracle exercise the fold. ✓
- §4 fence lift (both edits + no-recursive-BV-check argument + doc comments) → Task 4. ✓
- §5 exhaustive/random per-gadget gates → Task 2; e2e + get-model both faces → Task 5; z3 differential → Task 6; canary pre-flight + repoints (fp_stage.rs:593/:599, fp_e2e.rs:641) → Task 4 Steps 1/5 + Task 5 Step 3; full-workspace net → Task 7. ✓
- §6 risks: exponent wrap → wc formula in Task 2 + tiny-format overflow tests; INT_MIN → seeded vectors + m=2 edge sweep; canary breakage → hunt steps; depth → no action needed. ✓

**Placeholder scan:** no TBD/TODO; every code step shows complete code and exact commands.

**Type consistency:** `to_fp_int(b, x, signed, eb_t, sb_t, rm)` defined in Task 2, called with the same shape in Task 3 (`to_fp_int(sink.blaster(), &xw, true/false, eb, sb, &rm)`). `ref_to_fp_sbv/ubv(eb, sb, m, &Integer, RoundMode) -> Integer` defined in Task 1, used identically in Task 2's tests. `gen_int_to_fp_script`/`differential_qf_bvfp_int_to_fp` match the existing oracle harness signatures.
