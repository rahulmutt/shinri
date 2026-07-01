# QF_FP slice 3a — non-BV `to_fp` conversions + symbolic-Real fence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit the two **non-BV** faces of `to_fp` — `((_ to_fp eb sb) RM x)` with `x` a **Float** (re-round across formats) and with `x` a **constant Real** (fold the exact rational at blast time) — through the QF_FP soundness fence, and refine the slice-1 stand-in into the real **symbolic-Real → `Unknown`** boundary. Opens Plan 3.

**Architecture:** Mirror every prior FP-op slice: a shared `const_real_value` oracle in `shinri-core` (so the fence and the folder admit the *identical* set), an exact `ref_to_fp_fp` golden in `reference.rs`, a gate-level datapath in the new `convert.rs`, a `blast_word` dispatch arm, a fence admission in `fp_stage.rs`, and the standard test trio (in-circuit reference cross-check, differential-vs-z3 oracle, end-to-end). The FP→FP circuit is **unpack → prenormalize → saturate-exponent-into-target-width → static significand split (widen: zero-pad; narrow: drop-to-GRS) → the existing `round.rs` rounder → special-case mux** — reusing trusted gadgets, adding no new rounding logic. The const-Real path is a **fold**: compute `round_rational(eb, sb, q, mode)` for each of the five modes and one-hot-select by the `RmSel` (literal RM constant-folds to a single pattern; symbolic RM stays a 5-way mux). All **BV-crossing** conversions (bitcast, int→FP, `to_ubv`/`to_sbv`) and `fp.to_real`/symbolic-Real `to_fp` remain fenced to `Unknown` (Plan 4+).

**Tech Stack:** Rust, `shinri-fp` (depends on `shinri-bv` `Blaster`, `shinri-core`, `shinri-num`), `shinri-sat` for the in-test SAT eval, `z3` + `easy_smt` for the oracle.

## Global Constraints

- **Soundness contract:** anything out of scope returns `Unknown`, never a wrong SAT/UNSAT verdict. The fence (`is_supported_fp_word`) positively enumerates supported ops; an unhandled shape fails closed (the `blast_word` `unreachable!` arm is an internal invariant, never user-reachable).
- **Scope is exactly two `to_fp` forms.** `ToFp{eb,sb}` with **2 args** `(RM, X)` where **X is Float** (FP→FP) *or* **X is a constant Real** (`const_real_value` returns `Some`). Every other conversion — `ToFp` 1-arg bitcast, `ToFp` with a **BV** operand, `ToFpUnsigned`, `FpToUbv`, `FpToSbv`, `FpToReal`, and `ToFp` with a **symbolic** Real operand — stays fenced. Operand-kind disambiguation is fixed by core sort-checking (`shinri-core/src/context.rs:560`): 1-arg = bitcast; 2-arg `(RM,X)`, X ∈ {Float, BV, Real}.
- **Fence ⇄ folder agreement is soundness-critical.** Both consult the **same** `Context::const_real_value`. If they disagreed, an admitted-but-unfoldable term would hit the `blast_word` `unreachable!` (a user-triggered panic). Single source by construction.
- **Rounding is the existing rounder.** Do **not** write new rounding logic. FP→FP feeds `round.rs`; const-Real feeds `reference::round_rational`. Both are already exhaustively trusted by every arithmetic slice.
- **Significand/exponent conventions:** `sb` bits LSB→MSB, hidden/leading bit at index `sb-1`; exponent signed unbiased, `exp_w(eb) = eb + 6` bits. `to_operand` materializes the hidden bit and the unbiased exponent; `prenormalize` shifts the leading 1 to index `sb-1` and adjusts the exponent. The unbiased exponent is **format-independent** — FP→FP resizes it by **saturation** into the target `exp_w`, never bare truncation (a deep-underflow/overflow source would otherwise wrap and yield a wrong normal/∞).
- **Mode order is fixed:** `RmSel.sel == [RNE, RNA, RTP, RTN, RTZ]` (`rm.rs`), matching `reference::RoundMode { Rne, Rna, Rtp, Rtn, Rtz }`. The const-Real fold iterates modes in this order so `sel[m]` selects `round_rational(…, modes[m])`.
- **Formats:** must work for arbitrary `(eb, sb)`. Tests cover the tiny pair `(3,5)↔(5,11)` **exhaustively both directions**, plus Float16↔Float32↔Float64 randomized. `exp_w(eb) = eb + 6`.
- **Constant-Real breadth:** `const_real_value` = a Real numeral (literals and parser-folded `(/ lit lit)` both arrive as numerals) **plus** a unary-`Neg` of a constant Real. Anything else — a Real variable, `(* recip x)` from `(/ … x)`, nested arithmetic — returns `None` → `Unknown`.
- **No new dependencies. No SAT/Tseitin/model changes. No persistent/incremental blasting.**
- **Standing canary stays valid.** Slice 2g repointed the malformed canaries to `((_ to_fp 8 24) RNE r)` with a **symbolic** Real `r` — which this slice leaves fenced. No pre-emptive repoint is needed; Task 7 **verifies** this rather than assuming it.

---

### Task 1: Shared `const_real_value` oracle in `shinri-core`

The single source of truth for "is this `to_fp` operand a constant Real, and if so what exact rational?" — consumed by both the fence (`shinri-solver`) and the folder (`shinri-fp`).

**Files:**
- Modify: `crates/shinri-core/src/context.rs` (add `const_real_value` next to `numeral_value` ~line 744; add tests to the existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `numeral_value`, `term_node`, `children` (all existing `Context` methods); `Op`, `BuiltinOp`, `TermNode`, `shinri_num::{Integer, Rational}` (all in scope in `context.rs`).
- Produces: `pub fn const_real_value(&self, t: TermId) -> Option<Rational>`.

- [ ] **Step 1: Write the failing tests**

Add to `mod tests` in `context.rs`:

```rust
#[test]
fn const_real_value_folds_literals_and_neg() {
    use shinri_num::Rational;
    let mut ctx = Context::new();
    let real = ctx.real_sort();
    // plain numeral 5/1
    let five = ctx.mk_numeral(Rational::from_int(5i128.into()), real);
    assert_eq!(ctx.const_real_value(five), Some(Rational::from_int(5i128.into())));
    // parser already folds (/ 1 3) to a single numeral; emulate that numeral 1/3
    let third = ctx.mk_numeral(Rational::new(1i128.into(), 3i128.into()), real);
    assert_eq!(ctx.const_real_value(third), Some(Rational::new(1i128.into(), 3i128.into())));
    // unary negation (- 5/2) -> -5/2
    let fivehalf = ctx.mk_numeral(Rational::new(5i128.into(), 2i128.into()), real);
    let neg = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[fivehalf]).unwrap();
    assert_eq!(ctx.const_real_value(neg),
               Some(Rational::new((-5i128).into(), 2i128.into())));
}

#[test]
fn const_real_value_rejects_symbolic() {
    let mut ctx = Context::new();
    let real = ctx.real_sort();
    // a Real variable is not constant
    let r = ctx.declare_fun("r", &[], real);
    let rt = ctx.mk_app(Op::Uninterpreted(r), &[]).unwrap();
    assert_eq!(ctx.const_real_value(rt), None);
    // (* recip r) — the shape (/ 1 r) desugars to — is not constant
    let recip = ctx.mk_numeral(shinri_num::Rational::new(1i128.into(), 2i128.into()), real);
    let prod = ctx.mk_app(Op::Builtin(BuiltinOp::Mul), &[recip, rt]).unwrap();
    assert_eq!(ctx.const_real_value(prod), None);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-core const_real_value -- --nocapture`
Expected: FAIL — `no method named const_real_value`.

- [ ] **Step 3: Write the implementation**

Add to `context.rs` immediately after `numeral_value` (~line 758):

```rust
/// The exact `Rational` of a **constant** Real term — a numeral (literals and
/// parser-folded `(/ lit lit)` both intern as numerals) or a unary `(- c)` of a
/// constant Real — or `None` if `t` is symbolic (a Real variable, `(* recip x)`,
/// nested arithmetic). SHARED by the FP `to_fp` fence (shinri-solver) and folder
/// (shinri-fp) so they admit exactly the same set — a soundness invariant.
pub fn const_real_value(&self, t: TermId) -> Option<Rational> {
    if let Some(r) = self.numeral_value(t) {
        return Some(r.clone());
    }
    if let TermNode::App { op: Op::Builtin(BuiltinOp::Neg), args, .. } = self.term_node(t) {
        let kids = self.children(*args);
        if kids.len() == 1 {
            let inner = self.const_real_value(kids[0])?;
            return Some(Rational::new(Integer::from(-1i64), Integer::one()) * inner);
        }
    }
    None
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-core const_real_value -- --nocapture`
Expected: PASS (both tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-core/src/context.rs
git commit -m "feat(core): const_real_value helper (shared to_fp const-Real fence/folder oracle)"
```

---

### Task 2: Reference golden `ref_to_fp_fp`

The exact-rational golden for the FP→FP direction: specials mapped by table, finite values via `class_to_rational → round_rational`. (The const-Real golden **is** `round_rational` directly — no new function needed.)

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (add `ref_to_fp_fp` after `round_rational`; add tests to `mod tests`)

**Interfaces:**
- Consumes: `decode`, `FpClass`, `class_to_rational`, `round_rational`, `RoundMode`, and the private `canonical_nan` / `inf_pattern` / `zero_pattern` (all in `reference.rs`); `shinri_num::Integer`.
- Produces: `pub fn ref_to_fp_fp(eb_s: u32, sb_s: u32, eb_t: u32, sb_t: u32, x: &Integer, mode: RoundMode) -> Integer`.

- [ ] **Step 1: Write the failing tests**

Add to `mod tests` in `reference.rs`. (Float32: `1.0=0x3F80_0000`; Float64: `1.0=0x3FF0_0000_0000_0000`, `+inf=0x7FF0…0`, `NaN=0x7FF8…0`, `-0=0x8000…0`.)

```rust
#[test]
fn ref_to_fp_fp_widen_and_narrow() {
    use RoundMode::Rne;
    // widen 1.0 f32 -> f64 : exact.
    assert_eq!(
        ref_to_fp_fp(8, 24, 11, 53, &Integer::from(0x3F80_0000u64), Rne),
        Integer::from(0x3FF0_0000_0000_0000u64));
    // narrow 1.0 f64 -> f32 : exact.
    assert_eq!(
        ref_to_fp_fp(11, 53, 8, 24, &Integer::from(0x3FF0_0000_0000_0000u64), Rne),
        Integer::from(0x3F80_0000u64));
    // narrow 1/3 f64 -> f32 : round to nearest -> 0x3EAA_AAAB.
    let third_f64 = round_rational(11, 53, &Rational::new(1i128.into(), 3i128.into()), Rne);
    assert_eq!(
        ref_to_fp_fp(11, 53, 8, 24, &third_f64, Rne),
        Integer::from(0x3EAA_AAABu64));
}

#[test]
fn ref_to_fp_fp_specials() {
    use RoundMode::Rne;
    // NaN f64 -> canonical NaN f32.
    assert_eq!(
        ref_to_fp_fp(11, 53, 8, 24, &Integer::from(0x7FF8_0000_0000_0000u64), Rne),
        canonical_nan(8, 24));
    // +inf f64 -> +inf f32.
    assert_eq!(
        ref_to_fp_fp(11, 53, 8, 24, &Integer::from(0x7FF0_0000_0000_0000u64), Rne),
        inf_pattern(8, 24, false));
    // -0 f64 -> -0 f32 (sign preserved).
    assert_eq!(
        ref_to_fp_fp(11, 53, 8, 24, &Integer::from(0x8000_0000_0000_0000u64), Rne),
        zero_pattern(8, 24, true));
    // overflow: max-normal f32 widened is exact, but a huge f64 narrowed to f16
    // overflows -> +inf. 2.0^100 in f64 = exponent 1123 biased = 0x4630…; -> f16 inf.
    let big = round_rational(11, 53, &{
        let mut acc = Integer::one(); for _ in 0..100 { acc = acc * Integer::from(2u64); }
        Rational::new(acc, Integer::one())
    }, Rne);
    assert_eq!(ref_to_fp_fp(11, 53, 5, 11, &big, Rne), inf_pattern(5, 11, false));
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp ref_to_fp_fp -- --nocapture`
Expected: FAIL — `cannot find function ref_to_fp_fp`.

- [ ] **Step 3: Write the implementation**

Add to `reference.rs` after `round_rational`:

```rust
/// Exact-rational golden `((_ to_fp eb_t sb_t) mode x)` for an FP source `x` of
/// format (eb_s, sb_s). Specials map by table; finite values round the exact
/// rational into the target under `mode`. Trusted reference for `convert::to_fp_fp`.
pub fn ref_to_fp_fp(eb_s: u32, sb_s: u32, eb_t: u32, sb_t: u32, x: &Integer, mode: RoundMode)
    -> Integer {
    let c = decode(eb_s, sb_s, x);
    match c {
        FpClass::Nan => canonical_nan(eb_t, sb_t),
        FpClass::Inf { sign } => inf_pattern(eb_t, sb_t, sign),
        FpClass::Zero { sign } => zero_pattern(eb_t, sb_t, sign),
        _ => {
            let q = class_to_rational(eb_s, sb_s, &c).unwrap(); // finite: always Some
            round_rational(eb_t, sb_t, &q, mode)
        }
    }
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp ref_to_fp_fp -- --nocapture`
Expected: PASS (both tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): ref_to_fp_fp exact-rational golden for slice 3a"
```

---

### Task 3: `convert.rs` — FP→FP circuit + const-Real fold

The datapath. **The exhaustive `(5,11)↔(3,5)` cross-check (Step 1) is the definitive correctness gate** — bit-for-bit against `ref_to_fp_fp` over all values, both directions. The algorithm below is the intended structure; the test, not the prose, is the spec.

**Files:**
- Create: `crates/shinri-fp/src/convert.rs`
- Modify: `crates/shinri-fp/src/lib.rs` (add `mod convert;` near the other module declarations, ~line 10)

**Interfaces:**
- Consumes: `to_operand`, `canon_nan_bits`, `inf_pattern_bits`, `signed_zero_bits` from `crate::blast::operand`; `const_n`, `prenormalize` from `crate::blast::normalize`; `round`, `ExtFp`, `exp_w` from `crate::round`; `RmSel` from `crate::rm`; `round_rational`, `RoundMode`, `field` from `crate::reference`; `shinri_bv::blast::arith::bvsub`; `shinri_num::{Integer, Rational}`.
- Produces:
  - `pub fn to_fp_fp(b: &mut Blaster, x: &[BitLit], eb_s: u32, sb_s: u32, eb_t: u32, sb_t: u32, rm: &RmSel) -> Vec<BitLit>`
  - `pub fn to_fp_real_const(b: &mut Blaster, q: &Rational, eb: u32, sb: u32, rm: &RmSel) -> Vec<BitLit>`

- [ ] **Step 1: Write the failing cross-check tests (the correctness gate)**

Create `crates/shinri-fp/src/convert.rs` with ONLY the test module first (the fns come in Step 3). Reuse the `const_bits`/`eval_word` SAT-eval harness from `blast/rem.rs`:

```rust
//! FP conversions (non-BV faces of to_fp): FP→FP re-round + constant-Real fold.
//! FP→FP: unpack → prenormalize → saturate exponent → static significand split →
//! shared rounder → special mux. const-Real: fold round_rational, one-hot by RM.

#[cfg(test)]
mod tests {
    use crate::convert::{to_fp_fp, to_fp_real_const};
    use crate::reference::{ref_to_fp_fp, round_rational, RoundMode};
    use crate::rm;
    use shinri_bv::{BitLit, Blaster};
    use shinri_core::RoundingMode;
    use shinri_num::{Integer, Rational};
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
    const MODES: [(RoundingMode, RoundMode); 5] = [
        (RoundingMode::Rne, RoundMode::Rne), (RoundingMode::Rna, RoundMode::Rna),
        (RoundingMode::Rtp, RoundMode::Rtp), (RoundingMode::Rtn, RoundMode::Rtn),
        (RoundingMode::Rtz, RoundMode::Rtz),
    ];

    #[test]
    fn to_fp_fp_tiny_exhaustive_both_directions() {
        // (5,11) <-> (3,5), every source value, all five modes, bit-identical vs golden.
        for &(core_rm, ref_rm) in &MODES {
            for (eb_s, sb_s, eb_t, sb_t) in [(5u32, 11u32, 3u32, 5u32), (3, 5, 5, 11)] {
                for a in 0u64..(1 << (eb_s + sb_s)) {
                    let want = ref_to_fp_fp(eb_s, sb_s, eb_t, sb_t, &Integer::from(a), ref_rm);
                    let mut b = Blaster::new();
                    let xw = const_bits(&b, eb_s, sb_s, a);
                    let sel = rm::literal(&b, core_rm);
                    let got_w = to_fp_fp(&mut b, &xw, eb_s, sb_s, eb_t, sb_t, &sel);
                    let got = eval_word(b, &got_w);
                    assert_eq!(Integer::from(got), want,
                        "to_fp ({eb_s},{sb_s})->({eb_t},{sb_t}) mode {ref_rm:?} a={a:#x}: got {got:#x} want {want}");
                }
            }
        }
    }

    #[test]
    fn to_fp_fp_f64_f32_specials_and_random() {
        let (eb_s, sb_s, eb_t, sb_t) = (11u32, 53u32, 8u32, 24u32);
        let cases: &[u64] = &[
            0x3FF0_0000_0000_0000, // 1.0
            0x7FF8_0000_0000_0000, // NaN
            0x7FF0_0000_0000_0000, // +inf
            0xFFF0_0000_0000_0000, // -inf
            0x8000_0000_0000_0000, // -0
            0x0000_0000_0000_0001, // min subnormal (underflows f32 -> 0)
            0x7FEF_FFFF_FFFF_FFFF, // max normal (overflows f32 -> +inf)
        ];
        let mut state = 0x1234_5678_9ABC_DEF0u64;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state };
        for &ref_rm in &[RoundMode::Rne, RoundMode::Rtz, RoundMode::Rtp] {
            let core_rm = match ref_rm {
                RoundMode::Rne => RoundingMode::Rne, RoundMode::Rtz => RoundingMode::Rtz,
                _ => RoundingMode::Rtp,
            };
            for iter in 0..200 {
                let a = if iter < cases.len() { cases[iter] } else { rand() };
                let want = ref_to_fp_fp(eb_s, sb_s, eb_t, sb_t, &Integer::from(a), ref_rm);
                let mut b = Blaster::new();
                let xw = const_bits(&b, eb_s, sb_s, a);
                let sel = rm::literal(&b, core_rm);
                let got_w = to_fp_fp(&mut b, &xw, eb_s, sb_s, eb_t, sb_t, &sel);
                let got = eval_word(b, &got_w);
                assert_eq!(Integer::from(got), want,
                    "f64->f32 mode {ref_rm:?} a={a:#x}: got {got:#x} want {want}");
            }
        }
    }

    #[test]
    fn to_fp_real_const_folds_all_modes() {
        // 1/3 -> f32 under each mode equals round_rational; literal RM folds to one pattern.
        let (eb, sb) = (8u32, 24u32);
        let q = Rational::new(1i128.into(), 3i128.into());
        for &(core_rm, ref_rm) in &MODES {
            let want = round_rational(eb, sb, &q, ref_rm);
            let mut b = Blaster::new();
            let sel = rm::literal(&b, core_rm);
            let got_w = to_fp_real_const(&mut b, &q, eb, sb, &sel);
            let got = eval_word(b, &got_w);
            assert_eq!(Integer::from(got), want, "to_fp 1/3 mode {ref_rm:?}: got {got:#x} want {want}");
        }
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp to_fp_fp_tiny -- --nocapture`
Expected: FAIL — `cannot find function to_fp_fp` (module has no impl yet).

- [ ] **Step 3: Write the implementation**

Prepend to `convert.rs` (above the test module):

```rust
use shinri_bv::{BitLit, Blaster};
use shinri_bv::blast::arith::bvsub;
use crate::blast::operand::{to_operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};
use crate::blast::normalize::{const_n, prenormalize};
use crate::round::{exp_w, round, ExtFp};
use crate::rm::RmSel;
use crate::reference::{field, round_rational, RoundMode};
use shinri_num::Rational;

/// Sign-extend a signed word `x` (LSB→MSB) to width `to` by replicating its MSB.
fn sign_extend(b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit> {
    let msb = *x.last().unwrap();
    let mut out = x.to_vec();
    while out.len() < to { out.push(msb); }
    out
}

/// `((_ to_fp eb_t sb_t) rm x)` for an FP source `x` of format (eb_s, sb_s).
/// Unpack → prenormalize → saturate the (format-independent) unbiased exponent
/// into the target width → static significand split → shared rounder → special mux.
pub fn to_fp_fp(
    b: &mut Blaster, x: &[BitLit],
    eb_s: u32, sb_s: u32, eb_t: u32, sb_t: u32, rm: &RmSel,
) -> Vec<BitLit> {
    let ew_s = exp_w(eb_s);
    let ew_t = exp_w(eb_t);
    let sbs = sb_s as usize;
    let sbt = sb_t as usize;
    let w = (eb_t + sb_t) as usize;

    let ox = to_operand(b, x, eb_s, sb_s);
    // Normalize the source significand: leading 1 at index sb_s-1, exponent adjusted.
    let (m_s, e_s) = prenormalize(b, &ox.sig, &ox.exp, sbs, ew_s);

    // --- exponent: saturate the unbiased exponent into ew_t so round() sees a
    //     faithful signed value (bare truncation would wrap on extreme narrowing). ---
    let bias_t = (1i128 << (eb_t - 1)) - 1;
    let emax_t = bias_t;
    let emin_t = 1 - bias_t;
    let hi = emax_t + 1;                    // round(): exp > emax_t → overflow → ±inf
    let lo = emin_t - (sbt as i128 + 2);    // round(): deep denormalize → ±0
    let wc = ew_s.max(ew_t) + 1;            // wide enough that the compares can't wrap
    let e_wide = sign_extend(b, &e_s, wc);
    let hi_w = const_n(b, wc, hi);
    let lo_w = const_n(b, wc, lo);
    // gt_hi = e_wide > hi (signed): (e_wide - hi) positive and nonzero.
    let d_hi = bvsub(b, &e_wide, &hi_w);
    let gt_hi = {
        let pos = b.not1(d_hi[wc - 1]);
        let mut nz = b.zero();
        for &bit in &d_hi { nz = b.or2(nz, bit); }
        b.and2(pos, nz)
    };
    // lt_lo = e_wide < lo (signed): (e_wide - lo) negative.
    let d_lo = bvsub(b, &e_wide, &lo_w);
    let lt_lo = d_lo[wc - 1];
    let clamped: Vec<BitLit> = (0..wc).map(|i| {
        let hi_or_x = b.mux2(gt_hi, hi_w[i], e_wide[i]);
        b.mux2(lt_lo, lo_w[i], hi_or_x)
    }).collect();
    let e_t: Vec<BitLit> = clamped[..ew_t].to_vec(); // clamped fits → low ew_t bits exact

    // --- significand: static split (sb_s, sb_t are blast-time constants) ---
    let (sig_t, grs): (Vec<BitLit>, (BitLit, BitLit, BitLit)) = if sbt >= sbs {
        // widen: leading 1 stays at top; pad (sb_t - sb_s) low zeros; exact (GRS = 0).
        let pad = sbt - sbs;
        let mut s = vec![b.zero(); pad];
        s.extend_from_slice(&m_s); // len sbt, leading 1 at index sbt-1
        (s, (b.zero(), b.zero(), b.zero()))
    } else {
        // narrow: keep top sb_t bits; dropped low bits form guard/round/sticky.
        let drop = sbs - sbt;
        let s = m_s[drop..sbs].to_vec(); // len sbt, leading 1 at index sbt-1
        let g = m_s[drop - 1];
        let r = if drop >= 2 { m_s[drop - 2] } else { b.zero() };
        let mut st = b.zero();
        for i in 0..drop.saturating_sub(2) { st = b.or2(st, m_s[i]); }
        (s, (g, r, st))
    };

    let ext = ExtFp { sign: ox.sign, exp: e_t, sig: sig_t, grs };
    let mut out = round(b, ext, eb_t, sb_t, rm);

    // --- special-case mux: source NaN/±inf/±0 override the datapath ---
    let nan = canon_nan_bits(b, eb_t, sb_t);
    let inf = inf_pattern_bits(b, eb_t, sb_t, ox.sign);
    let zero = signed_zero_bits(b, eb_t, sb_t, ox.sign);
    for i in 0..w { out[i] = b.mux2(ox.is_zero, zero[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(ox.is_inf, inf[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(ox.is_nan, nan[i], out[i]); }
    out
}

/// `((_ to_fp eb sb) rm q)` for a constant Real `q`: fold `round_rational` under
/// each mode and one-hot-select by `rm.sel`. Literal RM constant-folds to a single
/// pattern; symbolic RM stays a 5-way mux over five precomputed literals.
pub fn to_fp_real_const(b: &mut Blaster, q: &Rational, eb: u32, sb: u32, rm: &RmSel) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
    let mut out = vec![b.zero(); w];
    for (m, &mode) in modes.iter().enumerate() {
        let pat = round_rational(eb, sb, q, mode); // Integer bit pattern
        for i in 0..w {
            if !field(&pat, i as u32, 1).is_zero() {
                out[i] = b.or2(out[i], rm.sel[m]); // set bit i when the selected mode has it
            }
        }
    }
    out
}
```

- [ ] **Step 4: Wire the module**

In `crates/shinri-fp/src/lib.rs`, add alongside the other module declarations (~line 10):

```rust
mod convert;
```

- [ ] **Step 5: Run the cross-check gate**

Run: `cargo test -p shinri-fp to_fp -- --nocapture`
Expected: PASS — `to_fp_fp_tiny_exhaustive_both_directions`, `to_fp_fp_f64_f32_specials_and_random`, and `to_fp_real_const_folds_all_modes` all match the golden.

> **Implementation notes for the executor.**
> - The `to_operand`/`prenormalize`/`round` contract is exactly as `div.rs`/`rem.rs` use it: `round()` expects a **normalized** significand (leading 1 at `sb-1`) with the true unbiased exponent, then handles subnormal denormalize (via `emin_t`) and overflow→∞ (via `emax_t`) itself. FP→FP's only new work is the **exponent saturation** and the **static significand split**.
> - **Most error-prone spots** (iterate against the exhaustive `(5,11)↔(3,5)` gate): the `hi`/`lo` saturation bounds, the `drop`/GRS indexing on the narrow path, and the `sign_extend` width `wc`. The exhaustive test exercises overflow, deep underflow, subnormal source, and ties in both directions — fix against it.
> - `field(&pat, i, 1)` extracts bit `i` of the Integer pattern (verified: `pub fn field(bits: &Integer, lo: u32, width: u32) -> Integer`, `reference.rs:18`).

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/convert.rs crates/shinri-fp/src/lib.rs
git commit -m "feat(fp): to_fp FP->FP circuit + const-Real fold (convert.rs) for slice 3a"
```

---

### Task 4: Dispatch + fence admission

Wire the two non-BV `to_fp` forms into `blast_word` and admit them through the soundness fence. Every other conversion stays fenced.

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` (add a `ToFp { .. }` arm in `blast_word`'s `match op`, before `other => unreachable!(...)` ~line 145)
- Modify: `crates/shinri-solver/src/fp_stage.rs` (add a `ToFp` arm to `is_supported_fp_word` ~line 178; update the "anything else … conversions …" fall-through comment ~line 179 and the slice doc-comment)

**Interfaces:**
- Consumes: `crate::convert::{to_fp_fp, to_fp_real_const}` (Task 3); `self.blast_rm` (lib.rs:36) → `RmSel`; `ctx.fp_widths`, `ctx.sort_of`, `ctx.const_real_value` (Task 1); `is_rounding_mode_term`, `is_supported_fp_word` recursion (existing).
- Produces: `ToFp{eb,sb}` 2-arg `(RM, X)` reaching `convert` when X is FP or const-Real; `is_supported_fp_word` returning `true` for exactly those two shapes.

- [ ] **Step 1: Write the failing wiring tests**

Add to `lib.rs`'s `mod lower_tests` (mirrors `lower_fp_div_eq_atom`):

```rust
#[test]
fn lower_to_fp_fp_and_const_real_atoms() {
    use shinri_core::BuiltinOp;
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let f64 = ctx.fp_sort(11, 53);
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    // FP->FP: widen a Float32 var to Float64.
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let widen = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 11, sb: 53 }), &[rne, x]).unwrap();
    let yf = ctx.declare_fun("y", &[], f64);
    let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
    let eq1 = ctx.mk_eq(widen, y).unwrap();
    // const-Real: to_fp of numeral 1/3 into Float32.
    let real = ctx.real_sort();
    let third = ctx.mk_numeral(shinri_core::Rational::new(1i128.into(), 3i128.into()), real);
    let conv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, third]).unwrap();
    let zf = ctx.declare_fun("z", &[], f32);
    let z = ctx.mk_app(Op::Uninterpreted(zf), &[]).unwrap();
    let eq2 = ctx.mk_app(Op::Builtin(BuiltinOp::FpEq), &[conv, z]).unwrap();
    let lo = lower(&mut ctx, &[eq1, eq2]);
    assert!(lo.atom_lit.contains_key(&eq1), "core = over to_fp FP->FP must be surrogated");
    assert!(lo.atom_lit.contains_key(&eq2), "fp.eq over const-Real to_fp must be surrogated");
}
```

Add to `fp_stage.rs`'s test module (mirrors `fp_sqrt_word_is_supported`):

```rust
#[test]
fn to_fp_non_bv_faces_supported_bv_and_symbolic_real_not() {
    use shinri_num::Rational;
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let rne = ctx.mk_rm_const(shinri_core::RoundingMode::Rne);
    // FP->FP widen supported.
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let widen = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 11, sb: 53 }), &[rne, x]).unwrap();
    let isn1 = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[widen]).unwrap();
    assert!(fp_atoms_fully_supported(&ctx, &collect_fp_atoms(&ctx, &[isn1])),
            "to_fp FP->FP is in scope as of slice 3a");
    // const-Real supported.
    let real = ctx.real_sort();
    let third = ctx.mk_numeral(Rational::new(1i128.into(), 3i128.into()), real);
    let conv = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, third]).unwrap();
    let isn2 = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[conv]).unwrap();
    assert!(fp_atoms_fully_supported(&ctx, &collect_fp_atoms(&ctx, &[isn2])),
            "const-Real to_fp is in scope as of slice 3a");
    // symbolic-Real to_fp NOT supported (durably fenced).
    let rf = ctx.declare_fun("r", &[], real);
    let r = ctx.mk_app(Op::Uninterpreted(rf), &[]).unwrap();
    let sym = ctx.mk_app(Op::Builtin(BuiltinOp::ToFp { eb: 8, sb: 24 }), &[rne, r]).unwrap();
    let isn3 = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[sym]).unwrap();
    assert!(!fp_atoms_fully_supported(&ctx, &collect_fp_atoms(&ctx, &[isn3])),
            "symbolic-Real to_fp must stay fenced");
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp lower_to_fp; cargo test -p shinri-solver to_fp_non_bv_faces`
Expected: FAIL — `lower_to_fp_fp_and_const_real_atoms` panics at the `blast_word` `unreachable!` (ToFp not dispatched); `to_fp_non_bv_faces_…` fails the supported asserts (ToFp hits `_ => false`).

- [ ] **Step 3: Add the `blast_word` dispatch arm**

In `lib.rs`, in `blast_word`'s `match op`, before `other => unreachable!(...)`:

```rust
ToFp { .. } => {
    // Non-BV faces only (fence guarantees this): 2 args (RM, X), X = Float | const Real.
    // `eb`/`sb` here are the outer target widths (result sort); source is X's sort.
    let rm = self.blast_rm(ctx, kids[0]);
    if let Some(q) = ctx.const_real_value(kids[1]) {
        crate::convert::to_fp_real_const(&mut self.b, &q, eb, sb, &rm)
    } else {
        let (eb_s, sb_s) = ctx.fp_widths(ctx.sort_of(kids[1])).expect("FP source operand");
        let xw = self.blast_word(ctx, kids[1]);
        crate::convert::to_fp_fp(&mut self.b, &xw, eb_s, sb_s, eb, sb, &rm)
    }
}
```

- [ ] **Step 4: Add the `is_supported_fp_word` arm + update docs**

In `fp_stage.rs`, before the final `_ => false` arm:

```rust
// to_fp: (RM, X). Non-BV faces only — X is a supported FP word (FP->FP re-round)
// or a constant Real (fold). BV operand / 1-arg bitcast / symbolic Real stay
// unsupported (Plan 4+ / later Real combination). Fence and folder share
// Context::const_real_value so the admit-set is identical (soundness).
TermNode::App { op: Op::Builtin(BuiltinOp::ToFp { .. }), args, .. } => {
    let kids = ctx.children(*args).to_vec();
    kids.len() == 2
        && is_rounding_mode_term(ctx, kids[0])
        && (is_supported_fp_word(ctx, kids[1]) || ctx.const_real_value(kids[1]).is_some())
}
```

Update the fall-through comment (~line 179) to drop `conversions` from the still-unsupported list only for the two admitted `ToFp` faces, and bump the slice enumeration:

```rust
// Anything else (Ite over FP, non-nullary UF, BV-crossing conversions, symbolic-Real
// to_fp, fp.to_real, etc.) is not in scope for slices 1–3a.
_ => false,
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-fp lower_to_fp; cargo test -p shinri-solver to_fp_non_bv_faces`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/lib.rs crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): admit non-BV to_fp through the FP soundness fence + dispatch"
```

---

### Task 5: End-to-end tests

Prove the two forms answer SAT/UNSAT with model round-trips, and that every fenced conversion returns `Unknown`. Mirrors the established `fp_e2e.rs` blocks.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` (new `── Slice-3a …` block at end)

**Interfaces:**
- Consumes: the `run(script) -> (SolveOutcome, String)` harness and `SolveOutcome` (existing).
- Produces: five `#[test]` fns.

- [ ] **Step 1: Write the end-to-end tests**

```rust
// ── Slice-3a end-to-end: non-BV to_fp (FP→FP + const-Real) + fence canaries ──

#[test]
fn to_fp_fp_widen_sat_get_model() {
    // y (Float64) = widen(x : Float32). SAT; model renders fp triples.
    let (o, model) = run(
        "(declare-fun x () Float32) (declare-fun y () Float64) \
         (assert (fp.eq y ((_ to_fp 11 53) RNE x))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triples: {model}");
}

#[test]
fn to_fp_fp_widen_injective_unsat() {
    // Widening Float32→Float64 is exact: widen(1.0f32) == 1.0f64. Asserting it
    // differs (core =) is UNSAT. Ground → constant-folds, fast.
    let (o, _) = run(
        "(assert (not (= ((_ to_fp 11 53) RNE (fp #b0 #x7f #b00000000000000000000000)) \
                         (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))) \
         (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn to_fp_const_real_known_value_sat() {
    // to_fp of 1/3 into Float32 (RNE) = 0x3EAA_AAAB; assert fp.eq with z and read model.
    let (o, model) = run(
        "(declare-fun z () Float32) \
         (assert (fp.eq z ((_ to_fp 8 24) RNE (/ 1.0 3.0)))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triple for z: {model}");
}

#[test]
fn to_fp_const_real_reflexive_unsat() {
    // to_fp(1/3) equals itself under fp.eq (non-NaN); asserting the negation is UNSAT.
    let (o, _) = run(
        "(assert (not (fp.eq ((_ to_fp 8 24) RNE (/ 1.0 3.0)) \
                             ((_ to_fp 8 24) RNE (/ 1.0 3.0))))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn to_fp_bv_crossing_and_symbolic_real_are_unknown() {
    // Every still-fenced conversion → Unknown (soundness: BV-crossing waits for Plan 4;
    // symbolic-Real / fp.to_real are the deferred Real bridge).
    let scripts = [
        // symbolic-Real to_fp
        "(declare-fun r () Real) (declare-fun z () Float32) \
         (assert (fp.eq z ((_ to_fp 8 24) RNE r))) (check-sat)",
        // bitcast from BV (1-arg to_fp)
        "(declare-fun b () (_ BitVec 32)) (declare-fun z () Float32) \
         (assert (fp.eq z ((_ to_fp 8 24) b))) (check-sat)",
        // signed-int BV → FP (2-arg to_fp with BV operand)
        "(declare-fun b () (_ BitVec 32)) (declare-fun z () Float32) \
         (assert (fp.eq z ((_ to_fp 8 24) RNE b))) (check-sat)",
        // FP → int (fp.to_sbv)
        "(declare-fun x () Float32) \
         (assert (= ((_ fp.to_sbv 32) RNE x) (_ bv0 32))) (check-sat)",
        // fp.to_real
        "(declare-fun x () Float32) \
         (assert (= (fp.to_real x) 0.0)) (check-sat)",
    ];
    for s in scripts {
        let (o, _) = run(s);
        assert_eq!(o, SolveOutcome::Unknown, "must fence to Unknown: {s}");
    }
}
```

- [ ] **Step 2: Run the end-to-end tests**

Run: `cargo test -p shinri-solver --test fp_e2e to_fp -- --nocapture`
Expected: PASS (all five).

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): end-to-end to_fp FP->FP / const-Real SAT/UNSAT + get-model + fence"
```

---

### Task 6: Differential-vs-z3 oracle

Extend the feature-gated oracle with FP→FP and const-Real `to_fp` generators. BV-crossing forms stay out of the corpus (Plan 4).

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (add `gen_to_fp_script` + `differential_qf_fp_to_fp` after the last op oracle)

**Interfaces:**
- Consumes: `Lcg`, `shinri_outcome`, `z3_outcome_arith`, `SolveOutcome`, `easy_smt` (all existing). z3 4.16.0 on PATH.
- Produces: `fn gen_to_fp_script(rng: &mut Lcg) -> String` and `#[test] fn differential_qf_fp_to_fp()`.

- [ ] **Step 1: Add the generator and test**

```rust
/// Random QF_FP script exercising the two non-BV to_fp faces: widen/narrow between
/// Float32 and Float64, and to_fp of a constant Real (a ratio of small integers).
/// Mixes with fp.eq / = / fp.isNaN atoms, some negated, so SAT and UNSAT both arise.
fn gen_to_fp_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun w () (_ FloatingPoint 11 53))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let modes = ["RNE", "RNA", "RTP", "RTN", "RTZ"];
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let rm = modes[rng.below(5) as usize];
        // pick a conversion term of Float32 sort so it composes with z / fp.isNaN.
        let term = match rng.below(3) {
            0 => format!("((_ to_fp 8 24) {rm} w)"),              // narrow Float64→Float32
            1 => {
                let num = 1 + rng.below(9);
                let den = 1 + rng.below(9);
                format!("((_ to_fp 8 24) {rm} (/ {num}.0 {den}.0))") // const-Real→Float32
            }
            _ => format!("((_ to_fp 8 24) {rm} ((_ to_fp 11 53) {rm} x))"), // round-trip via Float64
        };
        let atom = match rng.below(3) {
            0 => format!("(fp.eq z {term})"),
            1 => format!("(= z {term})"),
            _ => format!("(fp.isNaN {term})"),
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

const TO_FP_ITERS: usize = 60;

#[test]
fn differential_qf_fp_to_fp() {
    let mut rng = Lcg(0x0A_11_3E_5C_07_D1);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..TO_FP_ITERS {
        let src = gen_to_fp_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown { n_unknown += 1; continue; }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_FP to_fp DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    println!("differential_qf_fp_to_fp: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no SAT/UNSAT coverage");
}
```

- [ ] **Step 2: Run the oracle (background; feature-gated; requires z3 on PATH)**

Run in the background: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_to_fp -- --nocapture`
Expected: PASS — prints non-zero `sat=` and `unsat=`, zero disagreements.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential-vs-z3 oracle for non-BV to_fp conversions"
```

---

### Task 7: Full-suite verification + canary sweep + docs

The slice-completion gate. Per the cross-slice-canary lesson, run the WHOLE `fp_e2e` suite (not just the new tests) and grep for any canary that nested a now-admitted `to_fp` form.

**Files:**
- Modify: `docs/superpowers/specs/2026-06-30-shinri-qffp-slice3a-conversions-design.md` (flip Status to landed)

- [ ] **Step 1: Cross-slice canary sweep**

Run: `grep -rn 'to_fp\|ToFp' crates/shinri-solver/tests/ crates/shinri-fp/`
Expected: every existing `*_malformed_is_unknown` / fence canary that nests `to_fp` uses a **symbolic** Real operand (`((_ to_fp 8 24) RNE r)` with `(declare-fun r () Real)`), which slice 3a leaves fenced → still `Unknown`, unbroken. If any canary instead nests a `to_fp` **FP→FP** or **constant-Real** form (now decidable), repoint it to the symbolic-Real form and note it in the commit. (Expected: none — 2g chose the durable trigger deliberately.)

- [ ] **Step 2: Full FP end-to-end suite (the canary catch-net)**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS — all FP e2e tests, including every prior slice's canary, are green.

- [ ] **Step 3: Full workspace non-regression (background; long)**

Run in the background: `cargo test --workspace`
Expected: PASS — the entire workspace stays green; the QF_BV path and the FP-private `Blaster` are untouched.

- [ ] **Step 4: Clippy + fmt**

Run: `cargo clippy --workspace --all-targets -- -D warnings && cargo fmt --check`
Expected: clean. (If `convert.rs`'s index-arithmetic muxes trip `needless_range_loop`, add the same `#[allow(clippy::needless_range_loop)]` with the load-bearing-index rationale used in `operand.rs`/`round.rs`.)

- [ ] **Step 5: Final commit**

```bash
git add -A
git commit -m "docs(fp): mark slice 3a landed — non-BV to_fp conversions + Real fence"
```

---

## Self-Review

**Spec coverage** (against `2026-06-30-shinri-qffp-slice3a-conversions-design.md`):
- §1 Semantics (FP→FP specials + finite rounding; const-Real fold; symbolic RM) → `ref_to_fp_fp` (Task 2) + `to_fp_fp`/`to_fp_real_const` (Task 3), all five modes tested.
- §2.1 FP→FP circuit (unpack → prenormalize → saturate exp → static split → rounder → special mux) → Task 3 `to_fp_fp`; §2.2 const-Real fold → Task 3 `to_fp_real_const`; §2.3 oracle reuse → Tasks 2/3 use `decode`/`class_to_rational`/`round_rational`/`field`.
- §3 Fence + folder share `const_real_value` → Task 1 (helper in shinri-core) + Task 4 (both call sites); dispatch arm + `is_supported_fp_word` arm → Task 4.
- §4 Canary (standing `fp.to_real`/symbolic-Real canary stays valid; verify, no repoint) → Task 7 Steps 1–2.
- §5 Validation (exhaustive `(3,5)↔(5,11)` both directions, randomized Float32/64, const-fold all modes, fence/Unknown set, z3 differential, e2e, non-regression) → Tasks 3/5/6/7.
- §6 Soundness contract → fence is positive-enumeration; every BV-crossing conversion + symbolic-Real + `fp.to_real` stays `_ => false` (Task 4) and is asserted `Unknown` (Task 5).

**Placeholder scan:** no TBD/TODO. The judgement-dependent spot — the `to_fp_fp` exponent-saturation and significand-split — is shipped as complete code with the exhaustive `(5,11)↔(3,5)` both-directions test as its definitive gate and explicit "most error-prone spots" guidance, consistent with how prior FP datapaths were landed.

**Type consistency:** `const_real_value(&self, TermId) -> Option<Rational>` used identically in Tasks 1/4. `ref_to_fp_fp(eb_s,sb_s,eb_t,sb_t,&Integer,RoundMode) -> Integer` in Tasks 2/3. `to_fp_fp(&mut Blaster,&[BitLit],eb_s,sb_s,eb_t,sb_t,&RmSel) -> Vec<BitLit>` and `to_fp_real_const(&mut Blaster,&Rational,eb,sb,&RmSel) -> Vec<BitLit>` in Tasks 3/4. Mode order `[Rne,Rna,Rtp,Rtn,Rtz]` matches `RmSel.sel` in the fold and the tests. `blast_rm` returns `RmSel`; `ctx.fp_widths` returns `(u32,u32)`; all verified against source.

**Known risk (called out, not hidden):** the FP→FP exponent saturation for extreme format reductions (e.g. Float128→Float16) is the subtle part — it is what keeps narrowing **sound** (bare truncation would wrap). The exhaustive `(5,11)→(3,5)` narrowing test exercises overflow→∞ and deep-underflow→0 and pins it. All referenced symbols verified to exist: `numeral_value`/`term_node`/`children`/`fp_widths`/`sort_of` (context.rs), `to_operand`/`canon_nan_bits`/`inf_pattern_bits`/`signed_zero_bits` (operand.rs), `prenormalize`/`const_n` (normalize.rs), `round`/`ExtFp`/`exp_w` (round.rs), `blast_rm`/`RmSel` (lib.rs/rm.rs), `round_rational`/`class_to_rational`/`decode`/`field`/`canonical_nan`/`inf_pattern`/`zero_pattern`/`RoundMode` (reference.rs), `is_rounding_mode_term`/`is_supported_fp_word`/`fp_atoms_fully_supported`/`collect_fp_atoms` (fp_stage.rs), `run -> (SolveOutcome, String)` (fp_e2e.rs).
```
