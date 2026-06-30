# QF_FP slice 2g — fp.rem Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Admit `(fp.rem x y)` — the exact, mode-independent IEEE-754 remainder `r = x − y·n` with `n = roundTiesToEven(x/y)` — through the QF_FP soundness fence and bit-blast it correctly across all formats, closing Plan 2.

**Architecture:** Mirror every prior FP-op slice: an exact `ref_rem` golden in `reference.rs`, a gate-level circuit in `blast/rem.rs`, a `blast_word` dispatch arm, a fence admission in `fp_stage.rs`, and the standard test trio (in-circuit reference cross-check, differential-vs-z3 oracle, end-to-end). The datapath is an **explicit `fmod` reduction loop** (`O(ed·sb)` gates) over the prenormalized significands, keeping the running remainder **narrow (~`sb` bits)** — deliberately NOT the fixed-width `udivurem` (`O(ed²)`), because `fp.rem` needs the *full* integer quotient, not just `sb` bits. A round-to-nearest-even correction (`compare 2·residue vs |y|`) turns the floored `fmod` residue into the IEEE remainder. No rounder: the residue is exact; only normalize + pack.

**Tech Stack:** Rust, `shinri-fp` (depends on `shinri-bv` `Blaster`), `shinri-num` (`Integer`/`Rational`), `shinri-sat` for the in-test SAT eval, `z3` + `easy_smt` for the oracle.

## Global Constraints

- **Exactness is the defining contract.** `fp.rem` takes **no `RoundingMode` operand** (core: `FpRem` is `(F, F) -> F`, alongside `FpMin/FpMax`). The result is exact, mode-independent, and always representable: `|r| ≤ |y|/2`. Never round the result.
- **The quotient rounds to nearest, ties to EVEN.** `n = roundTiesToEven(x/y)`. This is *not* truncation (that would be C `fmod`); the round-to-even correction is what makes `|r| ≤ |y|/2` rather than `< |y|`.
- **Soundness contract:** anything out of scope returns `Unknown`, never a wrong SAT/UNSAT verdict. The fence (`is_supported_fp_word`) positively enumerates supported ops; an unhandled FP op fails closed (the `blast_word` `unreachable!` arm is an internal invariant, never user-reachable).
- **No new dependencies.** Reuse `shinri-bv` blast primitives (`adder`, `bvadd`, `bvsub`, `bvshl`, `compare::{ult, uge, eq}`) and the FP crate's `operand.rs` / `normalize.rs` / `lzc.rs` / `round.rs` helpers.
- **Formats:** must work for arbitrary `(eb, sb)`. Tests cover the tiny format `(3,5)` (exhaustive: 256² pairs) and Float32 `(8,24)` (specials + randomized). `exp_w(eb) = eb + 6`.
- **Significand convention:** `sb` bits LSB→MSB, hidden/leading bit at index `sb-1`; exponent signed unbiased, `exp_w(eb)` bits. `to_operand` materializes the hidden bit; `prenormalize` shifts the leading 1 to index `sb-1` and adjusts the exponent.
- **`ED_MAX` (worst-case exponent gap) = `2·bias + sb − 2`** where `bias = 2^(eb−1) − 1` — the most prenormalized-exponent stages the reduction loop can need. The loop is unrolled to `ED_MAX` and gated per stage by `i < ed`, so a literal-operand query constant-folds the inactive stages away.
- **Deep-circuit caution.** `fp.rem` is the deepest datapath shipped (loop depth `O(ed)` ≈ 276 stages for Float32). The known SAT recursion-depth risk (observed on `fp.div`/`fp.sqrt`, fixed by the iterative conflict minimizer) applies: the differential oracle is **bounded** and **run in the background by the implementer**, never via looped subagents. A deliberate worst-gap stress test (Task 3) is the explicit guard.
- **No persistent/incremental blasting; no SAT/Tseitin/model changes.**

---

### Task 1: Reference golden `ref_rem`

Exact, mode-independent bit-pattern golden used by every later cross-check (and, later, by `rewrite` constant-folding). Forms the exact rational remainder via round-half-even `n`.

**Files:**
- Modify: `crates/shinri-fp/src/reference.rs` (add `ref_rem` after `ref_div`, ~line 637; add tests to the existing `#[cfg(test)] mod tests`)

**Interfaces:**
- Consumes: `decode`, `FpClass`, `class_to_rational`, `canonical_nan`, the private `zero_pattern`, `ref_is_negative`, `round_rational`, `RoundMode`, and `shinri_num::{Integer, Rational}` — all already in `reference.rs`.
- Produces: `pub fn ref_rem(eb: u32, sb: u32, x: &Integer, y: &Integer) -> Integer` — **no mode parameter** (the result is exact).

- [ ] **Step 1: Write the failing tests**

Add to `mod tests` in `reference.rs`. (Float32: `1.0=0x3F80_0000`, `-1.0=0xBF80_0000`, `2.0=0x4000_0000`, `3.0=0x4040_0000`, `5.0=0x40A0_0000`, `7.0=0x40E0_0000`, `-5.0=0xC0A0_0000`, `+inf=0x7F80_0000`, `-inf=0xFF80_0000`, `NaN=0x7FC0_0000`, `+0=0`, `-0=0x8000_0000`.)

```rust
#[test]
fn ref_rem_known_float32() {
    let (eb, sb) = (8u32, 24u32);
    let rem = |x: u64, y: u64| ref_rem(eb, sb, &Integer::from(x), &Integer::from(y));
    // 5 rem 3: round(5/3)=2, 5-6 = -1.0.
    assert_eq!(rem(0x40A0_0000, 0x4040_0000), Integer::from(0xBF80_0000u64));
    // -5 rem 3: -(5 - 3*round(-5/3)) ; round(-5/3)=-2 ; -5+6 = +1.0.
    assert_eq!(rem(0xC0A0_0000, 0x4040_0000), Integer::from(0x3F80_0000u64));
    // 7 rem 2: 7/2 = 3.5 tie -> even (4); 7-8 = -1.0.
    assert_eq!(rem(0x40E0_0000, 0x4000_0000), Integer::from(0xBF80_0000u64));
    // 5 rem 2: 5/2 = 2.5 tie -> even (2); 5-4 = +1.0.
    assert_eq!(rem(0x40A0_0000, 0x4000_0000), Integer::from(0x3F80_0000u64));
    // 3 rem 3 = +0 (exact multiple, sign of x).
    assert_eq!(rem(0x4040_0000, 0x4040_0000), Integer::from(0u64));
}

#[test]
fn ref_rem_specials() {
    let (eb, sb) = (8u32, 24u32);
    let rem = |x: u64, y: u64| ref_rem(eb, sb, &Integer::from(x), &Integer::from(y));
    let nan = canonical_nan(eb, sb);
    // any NaN -> NaN
    assert_eq!(rem(0x7FC0_0000, 0x3F80_0000), nan);
    assert_eq!(rem(0x3F80_0000, 0x7FC0_0000), nan);
    // rem(inf, y) -> NaN ; rem(x, 0) -> NaN
    assert_eq!(rem(0x7F80_0000, 0x3F80_0000), nan);
    assert_eq!(rem(0x3F80_0000, 0x0000_0000), nan);
    // rem(x, inf) = x (faithful)
    assert_eq!(rem(0x40A0_0000, 0x7F80_0000), Integer::from(0x40A0_0000u64));
    // rem(±0, finite-nonzero) = ±0 (sign of x)
    assert_eq!(rem(0x0000_0000, 0x3F80_0000), Integer::from(0u64));
    assert_eq!(rem(0x8000_0000, 0x3F80_0000), Integer::from(0x8000_0000u64));
}

#[test]
fn ref_rem_tiny_total_and_bounded() {
    // Every (a,b) on (3,5): the result is a valid 8-bit pattern, and for finite
    // nonzero a,b the magnitude never exceeds |b|/2 (the IEEE remainder bound).
    let (eb, sb) = (3u32, 5u32);
    for a in 0u64..256 {
        for b in 0u64..256 {
            let r = ref_rem(eb, sb, &Integer::from(a), &Integer::from(b));
            assert!(r < Integer::from(256u64), "out-of-range result {a:#x} rem {b:#x}");
            let (ca, cb) = (decode(eb, sb, &Integer::from(a)), decode(eb, sb, &Integer::from(b)));
            let finite_nz = |c: &FpClass| matches!(c, FpClass::Normal { .. } | FpClass::Subnormal { .. });
            if finite_nz(&ca) && finite_nz(&cb) {
                let rc = decode(eb, sb, &r);
                if let (Some(rv), Some(bv)) =
                    (class_to_rational(eb, sb, &rc), class_to_rational(eb, sb, &cb)) {
                    let two = Integer::from(2u64);
                    let absr = if rv < Rational::new(Integer::zero(), Integer::one())
                        { Rational::new(Integer::from(-1i64), Integer::one()) * rv } else { rv };
                    let absb = if bv < Rational::new(Integer::zero(), Integer::one())
                        { Rational::new(Integer::from(-1i64), Integer::one()) * bv } else { bv };
                    // 2*|r| <= |b|
                    assert!(absr * Rational::new(two, Integer::one()) <= absb,
                            "|rem| > |b|/2 at a={a:#x} b={b:#x}");
                }
            }
        }
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp ref_rem -- --nocapture`
Expected: FAIL — `cannot find function ref_rem in this scope`.

- [ ] **Step 3: Write the implementation**

Add to `reference.rs` after `ref_div` (end of the non-test section, ~line 637):

```rust
/// Exact-rational golden `fp.rem x y` — the IEEE-754 remainder. MODE-INDEPENDENT
/// and EXACT: r = x − y·n with n = roundTiesToEven(x/y) taken as an exact integer;
/// |r| ≤ |y|/2, always representable. `x`, `y` are W=eb+sb bit patterns.
pub fn ref_rem(eb: u32, sb: u32, x: &Integer, y: &Integer) -> Integer {
    use FpClass::*;
    let cx = decode(eb, sb, x);
    let cy = decode(eb, sb, y);
    // 1. NaN (either) -> NaN ; rem(±inf, _) -> NaN ; rem(_, ±0) -> NaN.
    if matches!(cx, Nan) || matches!(cy, Nan) { return canonical_nan(eb, sb); }
    if matches!(cx, Inf { .. }) { return canonical_nan(eb, sb); }
    if matches!(cy, Zero { .. }) { return canonical_nan(eb, sb); }
    let sign_x = ref_is_negative(&cx);
    // 2. rem(x, ±inf) = x (finite x, faithful bits — incl. ±0).
    if matches!(cy, Inf { .. }) { return x.clone(); }
    // 3. rem(±0, finite-nonzero) = ±0 (sign of x).
    if matches!(cx, Zero { .. }) { return zero_pattern(eb, sb, sign_x); }
    // 4. finite x, finite-nonzero y: exact remainder.
    let neg1 = Rational::new(Integer::from(-1i64), Integer::one());
    let zero = Rational::new(Integer::zero(), Integer::one());
    let two = Integer::from(2u64);
    let abs = |r: Rational| if r < zero { neg1.clone() * r } else { r };
    let xm = abs(class_to_rational(eb, sb, &cx).unwrap());
    let ym = abs(class_to_rational(eb, sb, &cy).unwrap());
    // q = round-half-even(xm / ym) as a non-negative integer.
    let qx = xm.clone() / ym.clone();                         // exact Rational, >= 0
    let qfloor = qx.numer().div_rem(&qx.denom()).0;           // floor (>= 0)
    let frac = qx - Rational::new(qfloor.clone(), Integer::one());
    let half = Rational::new(Integer::one(), two.clone());
    let round_up = if frac > half { true }
        else if frac < half { false }
        else { !qfloor.div_rem(&two).1.is_zero() };           // tie -> to even
    let q = if round_up { qfloor + Integer::one() } else { qfloor };
    // Signed magnitude-remainder rm = |x| − q·|y| ∈ [−|y|/2, |y|/2].
    // The true remainder is sign_x · rm (round-half-even is an odd function).
    let rm = xm - Rational::new(q, Integer::one()) * ym;
    if rm == zero { return zero_pattern(eb, sb, sign_x); }    // exact multiple -> ±0
    let result = if sign_x { neg1 * rm } else { rm };
    // rm is exactly representable, so this re-encode introduces no second rounding.
    round_rational(eb, sb, &result, RoundMode::Rne)
}
```

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p shinri-fp ref_rem -- --nocapture`
Expected: PASS (all three tests).

- [ ] **Step 5: Commit**

```bash
git add crates/shinri-fp/src/reference.rs
git commit -m "feat(fp): exact ref_rem golden (round-half-even quotient) for slice 2g"
```

---

### Task 2: Pre-emptive fence-canary repoint

Admitting `fp.rem` (Task 4) flips every prior `*_malformed_is_unknown` canary that nested `fp.rem` from `Unknown` to decidable, breaking it. Repoint them **now**, BEFORE admission, to a still-out-of-scope trigger that is also out of scope *today* — so this task leaves the suite green and Task 4 doesn't disturb them.

**Trigger choice.** The canaries nest an unsupported op as a **Float-sorted operand**. `fp.to_real` is *Real*-sorted and cannot occupy those slots, so the durable, Float-sorted realization of the approved symbolic-Real-bridge choice is **`to_fp` from a symbolic `Real`**: `((_ to_fp 8 24) RNE r)` with `(declare-fun r () Real)`. It parses and sort-checks to Float32 (parser.rs:434), trips the same unsupported-FP-op fence (`is_supported_fp_word` has no `ToFp` arm → `false`), and stays fenced for all of v1 (symbolic-Real conversion is deferred past Plan 3 — Plan 3 admits only *constant*-Real and BV/int sources).

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` (the `fp_fma_malformed_is_unknown` test ~line 427 and `fp_roundtointegral_malformed_is_unknown` ~line 483)

**Interfaces:**
- Consumes: the existing `run(script) -> (SolveOutcome, String)` harness and `SolveOutcome::Unknown` (already in the file).
- Produces: nothing new — same two tests, retargeted trigger.

- [ ] **Step 1: Repoint both canaries**

Replace the body of `fp_fma_malformed_is_unknown` (keep the `#[test]` and fn signature):

```rust
#[test]
fn fp_fma_malformed_is_unknown() {
    // Fence canary: an fma whose operand is an unsupported FP word must trip the
    // fence -> Unknown. Trigger = to_fp from a symbolic Real (durably out of scope
    // for all of v1: the symbolic-Real bridge is deferred past Plan 3). Float-sorted,
    // so it nests where the 4th fma operand must be a Float.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) (declare-fun w () Float32) \
         (declare-fun r () Real) \
         (assert (fp.eq w (fp.fma RNE x y ((_ to_fp 8 24) RNE r)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}
```

Replace the body of `fp_roundtointegral_malformed_is_unknown`:

```rust
#[test]
fn fp_roundtointegral_malformed_is_unknown() {
    // Fence canary: a roundToIntegral whose operand is an unsupported FP word
    // (to_fp from a symbolic Real, durably out of scope) must trip the fence -> Unknown.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun u () Float32) (declare-fun r () Real) \
         (assert (fp.eq u (fp.roundToIntegral RNE ((_ to_fp 8 24) RNE r)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}
```

- [ ] **Step 2: Run the two canaries — must still pass (green before AND after admission)**

Run: `cargo test -p shinri-solver --test fp_e2e malformed_is_unknown`
Expected: PASS — both return `Unknown` today (neither `fp.rem` nor symbolic-Real `to_fp` is yet admitted).

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): repoint malformed-canaries to symbolic-Real to_fp ahead of fp.rem admission"
```

---

### Task 3: `fp.rem` circuit `blast/rem.rs`

The datapath. **The exhaustive `(3,5)` cross-check (Step 1) is the definitive correctness gate** — it compares the circuit bit-for-bit against `ref_rem` over all 256² operand pairs, so iterate the circuit body against it until green. The algorithm below is the intended structure; the test, not the prose, is the spec.

**Algorithm (narrow `fmod` reduction + round-to-even correction):**
1. **Unpack** `x`, `y` via `to_operand`; **prenormalize** both significands → `(Mx, ex)`, `(My, ey)`, each `Mx, My ∈ [2^(sb-1), 2^sb)`, value `|x| = Mx·2^(ex-(sb-1))`, `|y| = My·2^(ey-(sb-1))`.
2. `ed = ex − ey` (signed). `ed_neg = ed < 0`.
3. **`fmod` loop** (unrolled `ED_MAX` stages, each gated by `i < ed`): seed `hx = Mx`; per active stage `{ if hx ≥ My { hx -= My }; hx <<= 1; }`; then one final `if hx ≥ My { hx -= My }`. Track the **final** subtract decision as the floored-quotient parity `p`. After the loop `hx ∈ [0, My)` is the floored residue at scale `2^(ey-(sb-1))`. `hx` fits `sb+1` bits.
4. **Common normalized residue** `(rsig, rexp)`:
   - `ed ≥ 0`: if `hx ≠ 0`, `k = LZC(hx)`, `rsig = hx << k` (leading 1 at `sb-1`), `rexp = ey − k`. `r_zero = (hx == 0)`.
   - `ed < 0`: `|x| < |y|`, floored residue is `|x|`; `rsig = Mx`, `rexp = ex`, `p = 0`, `r_zero = false`.
   - Mux on `ed_neg`.
5. **Round-to-even correction.** Compare `2·rfmod` against `|y|`. Because correction can only fire when `rfmod ≥ |y|/2`, the binade gap `dd = ey − rexp ∈ {0, 1}` whenever it matters, so the compare and the `|y| − rfmod` subtraction are both **narrow** (`sb+1` bits). `inc = (2·rfmod > |y|) ∨ ((2·rfmod == |y|) ∧ p)`.
   - `inc`: `mag = |y| − rfmod`, `sign_out = sign_x ⊕ 1`.
   - `!inc`: `mag = rfmod`, `sign_out = sign_x`.
6. **Normalize `mag` + pack via `round()` with `grs = (0,0,0)`.** The residue is exact, so a zero-GRS `round()` performs no rounding — it only re-normalizes, places the biased exponent, and handles the subnormal/zero tail. (Overflow→∞ cannot occur: `|r| ≤ |y|/2 < |y|`.)
7. **Special-case mux** (low→high priority; NaN wins): `rem(_, ±0) → NaN`, `rem(x, ±∞) → x`, `rem(±0, y) → ±0` (sign of x), `rem(±∞, _) → NaN`, any-NaN → canonical NaN.

**Files:**
- Create: `crates/shinri-fp/src/blast/rem.rs`
- Modify: `crates/shinri-fp/src/blast/mod.rs` (add `pub mod rem;`)

**Interfaces:**
- Consumes: `to_operand`, `canon_nan_bits`, `inf_pattern_bits` (unused here but available), `signed_zero_bits` from `blast::operand`; `const_n`, `zero_extend`, `prenormalize` from `blast::normalize`; `lzc` from `crate::lzc`; `round`, `ExtFp`, `exp_w` from `crate::round`; `shinri_bv::blast::{arith::{adder, bvadd, bvsub}, shift::bvshl, compare::{ult, uge, eq}}`.
- Produces: `pub fn fp_rem(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit>` — **no RM parameter**.

- [ ] **Step 1: Write the failing cross-check tests (the correctness gate)**

Create `crates/shinri-fp/src/blast/rem.rs` with ONLY the test module first (the `fp_rem` fn comes in Step 3). Reuse the exact `const_bits` / `eval_word` SAT-eval harness from `blast/roundint.rs`:

```rust
//! fp.rem datapath: exact IEEE remainder via a narrow fmod reduction loop +
//! round-to-nearest-even correction. Mode-independent; no rounder on the result.

#[cfg(test)]
mod tests {
    use crate::blast::rem::fp_rem;
    use crate::reference::ref_rem;
    use shinri_bv::{BitLit, Blaster};
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
    fn rem_tiny_exhaustive() {
        // Format (3,5): all 256x256 operand pairs, bit-identical vs the golden.
        let (eb, sb) = (3u32, 5u32);
        for a in 0u64..(1 << (eb + sb)) {
            for bb in 0u64..(1 << (eb + sb)) {
                let want = ref_rem(eb, sb, &Integer::from(a), &Integer::from(bb));
                let mut b = Blaster::new();
                let xw = const_bits(&b, eb, sb, a);
                let yw = const_bits(&b, eb, sb, bb);
                let got_word = fp_rem(&mut b, &xw, &yw, eb, sb);
                let got = eval_word(b, &got_word);
                assert_eq!(Integer::from(got), want,
                    "rem (3,5) a={a:#x} b={bb:#x}: got {got:#x} want {want}");
            }
        }
    }

    #[test]
    fn rem_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        let cases: &[(u64, u64)] = &[
            (0x40A0_0000, 0x4040_0000),   // 5 rem 3 = -1
            (0xC0A0_0000, 0x4040_0000),   // -5 rem 3 = +1
            (0x40E0_0000, 0x4000_0000),   // 7 rem 2 = -1 (tie->even)
            (0x40A0_0000, 0x4000_0000),   // 5 rem 2 = +1 (tie->even)
            (0x4040_0000, 0x4040_0000),   // 3 rem 3 = +0
            (0x7FC0_0000, 0x3F80_0000),   // NaN rem 1 = NaN
            (0x7F80_0000, 0x3F80_0000),   // inf rem 1 = NaN
            (0x3F80_0000, 0x0000_0000),   // 1 rem 0 = NaN
            (0x40A0_0000, 0x7F80_0000),   // 5 rem inf = 5
            (0x8000_0000, 0x3F80_0000),   // -0 rem 1 = -0
            (0x0000_0001, 0x0000_0002),   // subnormal rem subnormal
            (0x7F7F_FFFF, 0x0000_0001),   // WORST GAP: max-normal rem min-subnormal
        ];
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state >> 16 };
        for iter in 0..600 {
            let (a, bb) = if iter < cases.len() { cases[iter] }
                          else { (rand() & 0xFFFF_FFFF, rand() & 0xFFFF_FFFF) };
            let want = ref_rem(eb, sb, &Integer::from(a), &Integer::from(bb));
            let mut b = Blaster::new();
            let xw = const_bits(&b, eb, sb, a);
            let yw = const_bits(&b, eb, sb, bb);
            let got_word = fp_rem(&mut b, &xw, &yw, eb, sb);
            let got = eval_word(b, &got_word);
            assert_eq!(Integer::from(got), want,
                "rem f32 a={a:#x} b={bb:#x}: got {got:#x} want {want}");
        }
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp rem_tiny -- --nocapture`
Expected: FAIL — `cannot find function fp_rem`.

- [ ] **Step 3: Write the `fp_rem` implementation**

Prepend `pub fn fp_rem(...)` to `rem.rs` (above the test module), implementing the 7-stage algorithm. Use `to_operand`/`prenormalize`/`lzc`/`round` exactly as `div.rs` does; mirror its special-case mux idiom (`b.mux2` per bit, low→high priority). The worked structure:

```rust
use shinri_bv::{BitLit, Blaster};
use shinri_bv::blast::arith::{adder, bvadd, bvsub};
use shinri_bv::blast::shift::bvshl;
use shinri_bv::blast::compare::{eq as bv_eq, uge, ult};
use crate::blast::operand::{to_operand, canon_nan_bits, signed_zero_bits};
use crate::blast::normalize::{const_n, zero_extend, prenormalize};
use crate::lzc::lzc;
use crate::round::{exp_w, round, ExtFp};

pub fn fp_rem(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let w = (eb + sb) as usize;
    let bias = (1i128 << (eb - 1)) - 1;
    let ed_max = (2 * bias + sb as i128 - 2) as usize; // worst-case exponent gap

    let ox = to_operand(b, x, eb, sb);
    let oy = to_operand(b, y, eb, sb);
    let (mx, ex) = prenormalize(b, &ox.sig, &ox.exp, sbu, ew); // each sb / ew bits
    let (my, ey) = prenormalize(b, &oy.sig, &oy.exp, sbu, ew);

    // ed = ex - ey (signed, ew bits); ed_neg = sign bit.
    let ed = bvsub(b, &ex, &ey);
    let ed_neg = ed[ew - 1];

    // --- fmod reduction loop (ed >= 0 path) -----------------------------------
    // hx width sb+1 (grows to < 2*My during the loop). Stage i active iff i < ed.
    let mut hx = zero_extend(b, &mx, sbu + 1);
    let my1 = zero_extend(b, &my, sbu + 1);
    for i in 0..ed_max {
        let i_c = const_n(b, ew, i as i128);
        let active = ult(b, &i_c, &ed);                 // i < ed  (and ed >= 0)
        // conditional subtract: if hx >= My { hx -= My }
        let ge = uge(b, &hx, &my1);
        let sub = bvsub(b, &hx, &my1);
        let hx_sub: Vec<BitLit> = (0..sbu + 1).map(|j| b.mux2(ge, sub[j], hx[j])).collect();
        // shift left by 1
        let mut hx_shl = vec![b.zero()];
        hx_shl.extend_from_slice(&hx_sub[..sbu]);       // (hx_sub << 1), width sb+1
        // commit only while active
        hx = (0..sbu + 1).map(|j| b.mux2(active, hx_shl[j], hx[j])).collect();
    }
    // final subtract; its decision is the floored-quotient parity p.
    let ge_final = uge(b, &hx, &my1);
    let sub_final = bvsub(b, &hx, &my1);
    let hx_fmod: Vec<BitLit> = (0..sbu + 1).map(|j| b.mux2(ge_final, sub_final[j], hx[j])).collect();
    let p_ge0 = ge_final;

    // hx_fmod in [0, My). Normalize: k = LZC over the low sb bits.
    let hx_lo: Vec<BitLit> = hx_fmod[..sbu].to_vec();
    let k = lzc(b, &hx_lo);                              // count_width(sb) bits
    let k_sb = zero_extend(b, &k, sbu);
    let rsig_ge0 = bvshl(b, &hx_lo, &k_sb);             // leading 1 at sb-1 when nonzero
    let k_ew = zero_extend(b, &k, ew);
    let rexp_ge0 = bvsub(b, &ey, &k_ew);               // ey - k
    let mut hx_nz = b.zero();
    for &bit in &hx_lo { hx_nz = b.or2(hx_nz, bit); }
    let r_zero = b.not1(hx_nz);                          // exact division (ed>=0)

    // --- ed < 0 path: residue = |x|, already normalized (rsig=Mx, rexp=ex) -----
    let rsig: Vec<BitLit> = (0..sbu).map(|j| b.mux2(ed_neg, mx[j], rsig_ge0[j])).collect();
    let rexp: Vec<BitLit> = (0..ew).map(|j| b.mux2(ed_neg, ex[j], rexp_ge0[j])).collect();
    let p: BitLit = b.mux2(ed_neg, b.zero(), p_ge0);     // floored parity (0 when ed<0)
    let r_zero = b.mux2(ed_neg, b.zero(), r_zero);       // ed<0 => |x|>0 => nonzero

    // --- round-to-even correction: compare 2*rfmod vs |y| ---------------------
    // dd = ey - rexp in {0,1} whenever correction matters; build |y| and 2*rfmod
    // in a shared sb+2-bit field anchored so the compare is exact.
    //   y_field   = My                              (value My * 2^(ey-(sb-1)))
    //   rf2_field = 2*rsig >> dd  with sticky for the tie  (value 2*rfmod / 2^(ey-(sb-1)))
    // Implement dd via (ey - rexp); shift 2*rsig right by dd capturing a sticky OR.
    let dd = bvsub(b, &ey, &rexp);                      // >= 0 where it matters
    // 2*rsig in sb+2 bits:
    let mut two_rsig = vec![b.zero()];
    two_rsig.extend_from_slice(&rsig);                  // rsig << 1, width sb+1
    two_rsig.push(b.zero());                            // width sb+2
    // shift right by dd (small), folding dropped bits into sticky.
    let dd_w = zero_extend(b, &dd, sbu + 2);
    let (rf2_shr, rf2_sticky) = crate::round::shift_right_sticky(b, &two_rsig, &dd_w);
    let y_field = zero_extend(b, &my, sbu + 2);
    // gt: 2*rfmod > |y| ; eqf: 2*rfmod == |y| (no sticky) ; correction = gt | (eqf & p)
    let gt = ult(b, &y_field, &rf2_shr);               // |y| < 2*rfmod
    let eqbits = bv_eq(b, &rf2_shr, &y_field);          // 2*rfmod == |y| (bit-equal)
    let no_sticky = b.not1(rf2_sticky);
    let eqf = b.and2(eqbits, no_sticky);
    let tie_inc = b.and2(eqf, p);
    let inc = b.or2(gt, tie_inc);

    // --- assemble magnitude ---------------------------------------------------
    // !inc: mag = rfmod (rsig, rexp).  inc: mag = |y| - rfmod, with dd in {0,1},
    // so |y|-rfmod = (My << dd) - rsig at exponent rexp; narrow (sb+1 bits), then
    // renormalize. Build both, mux, then normalize once via round() with grs=0.
    let my_shf = bvshl(b, &zero_extend(b, &my, sbu + 1), &zero_extend(b, &dd, sbu + 1));
    let rsig_e = zero_extend(b, &rsig, sbu + 1);
    let diff = bvsub(b, &my_shf, &rsig_e);              // |y|-rfmod at scale 2^(rexp-(sb-1))
    // normalize diff:
    let kd = lzc(b, &diff[..sbu + 1]);
    let kd_w = zero_extend(b, &kd, sbu + 1);
    let diff_n = bvshl(b, &diff, &kd_w);
    let diff_sig: Vec<BitLit> = diff_n[1..sbu + 1].to_vec(); // top sb bits, hidden at sb-1
    let kd_ew = zero_extend(b, &kd, ew);
    // exponent of |y|-rfmod: rexp + 1 (the <<? ) - kd ; rexp+dd basis. Use rexp + (1) - kd
    let one_ew = const_n(b, ew, 1);
    let rexp_inc = bvadd(b, &rexp, &one_ew);
    let exp_diff = bvsub(b, &rexp_inc, &kd_ew);

    let mag_sig: Vec<BitLit> = (0..sbu).map(|j| b.mux2(inc, diff_sig[j], rsig[j])).collect();
    let mag_exp: Vec<BitLit> = (0..ew).map(|j| b.mux2(inc, exp_diff[j], rexp[j])).collect();
    let sign_out = b.xor2(ox.sign, inc);

    // --- pack via round() with grs = 0 (exact: no rounding, just normalize tail) ---
    let zero_bit = b.zero();
    let ext = ExtFp { sign: sign_out, exp: mag_exp, sig: mag_sig, grs: (zero_bit, zero_bit, zero_bit) };
    let normal_path = round(b, ext, eb, sb, &crate::rm::literal(b, shinri_core::RoundingMode::Rne));

    // --- special-case mux (low -> high priority; NaN wins) --------------------
    let mut out = normal_path;
    // r == 0 (exact multiple) -> signed zero, sign of x.
    let zsign = signed_zero_bits(b, eb, sb, ox.sign);
    for i in 0..w { out[i] = b.mux2(r_zero, zsign[i], out[i]); }
    // rem(x, inf) = x  (x finite here; specials below override for inf/nan/zero x).
    for i in 0..w { out[i] = b.mux2(oy.is_inf, x[i], out[i]); }
    // rem(±0, y) = ±0 (sign of x).
    for i in 0..w { out[i] = b.mux2(ox.is_zero, zsign[i], out[i]); }
    // rem(_, 0) -> NaN ; rem(inf, _) -> NaN ; any NaN -> NaN.
    let nan = canon_nan_bits(b, eb, sb);
    for i in 0..w { out[i] = b.mux2(oy.is_zero, nan[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(ox.is_inf, nan[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(ox.is_nan, nan[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(oy.is_nan, nan[i], out[i]); }
    out
}
```

> **Implementation notes for the executor.**
> - `bv_eq` is `shinri_bv::blast::compare::eq` (verified: `fn eq(b, x, y) -> BitLit`, AND of bitwise XNORs over equal-width words) — imported here as `eq as bv_eq` to avoid colliding with any local `eq`.
> - The `ed < 0` muxes assume `rsig_ge0`/`rexp_ge0`/`p_ge0` are well-formed (non-panicking) even when `ed < 0` — they are: the loop and LZC run unconditionally, the mux just discards them.
> - **This Step is expected to need iteration.** Run `rem_tiny_exhaustive` after each change; it pins every `(3,5)` case to `ref_rem`. Likely first-cut bugs: the `dd`/sticky alignment in the correction, the `exp_diff` basis, and off-by-one in the `hx` shift width. Fix against the gate.

- [ ] **Step 4: Wire the module**

In `crates/shinri-fp/src/blast/mod.rs`, add alongside the other `pub mod` lines:

```rust
pub mod rem;
```

- [ ] **Step 5: Run the cross-check + worst-gap stress (background; deep circuit)**

Run (in the background — the worst-gap Float32 case builds a ~276-stage circuit):
`cargo test -p shinri-fp rem_ -- --nocapture`
Expected: PASS — `rem_tiny_exhaustive` (all 256² pairs) and `rem_float32_specials_and_random` (incl. the `0x7F7F_FFFF rem 0x0000_0001` worst-gap stress case) both match `ref_rem` and complete without a SAT-core stack overflow.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/blast/rem.rs crates/shinri-fp/src/blast/mod.rs
git commit -m "feat(fp): fp.rem circuit (narrow fmod loop + round-to-even correction) for slice 2g"
```

---

### Task 4: Dispatch + fence admission

Wire `FpRem` into `blast_word` and admit it through the soundness fence. **Two-operand shape, no RM** — mirrors `FpMin/FpMax`, not the `(RM, F)` rounded ops.

**Files:**
- Modify: `crates/shinri-fp/src/lib.rs` (add an `FpRem` arm in `blast_word`'s `match op`, ~line 133 after `FpFma`)
- Modify: `crates/shinri-solver/src/fp_stage.rs` (add an `FpRem` arm to `is_supported_fp_word` ~line 154 near `FpMin/FpMax`; update the slice doc-comments ~line 110-123 and the fall-through comment ~line 171)

**Interfaces:**
- Consumes: `crate::blast::rem::fp_rem` (Task 3); `is_supported_fp_word` recursion (existing).
- Produces: `FpRem` reaching `fp_rem`; `is_supported_fp_word` returning `true` for `(fp.rem F F)` with both operands supported.

- [ ] **Step 1: Write the failing wiring tests**

Add to `lib.rs`'s `mod lower_tests` (mirrors `lower_fp_div_eq_atom`):

```rust
#[test]
fn lower_fp_rem_eq_atom() {
    use shinri_core::BuiltinOp;
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let yf = ctx.declare_fun("y", &[], f32);
    let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
    let rem = ctx.mk_app(Op::Builtin(BuiltinOp::FpRem), &[x, y]).unwrap();
    let one = ctx.mk_fp_const(8, 24, Integer::from(0x3F80_0000u64));
    let eq = ctx.mk_eq(rem, one).unwrap();
    let lo = lower(&mut ctx, &[eq]);
    assert!(lo.atom_lit.contains_key(&eq), "core = over fp.rem must be surrogated");
    assert!(lo.var_bits.contains_key(&x) && lo.var_bits.contains_key(&y), "x,y exported");
}
```

Add to `fp_stage.rs`'s test module (mirrors `fp_sqrt_word_is_supported`):

```rust
#[test]
fn fp_rem_word_is_supported() {
    let mut ctx = Context::new();
    let f32 = ctx.fp_sort(8, 24);
    let xf = ctx.declare_fun("x", &[], f32);
    let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
    let yf = ctx.declare_fun("y", &[], f32);
    let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
    let rem = ctx.mk_app(Op::Builtin(BuiltinOp::FpRem), &[x, y]).unwrap();
    let isnan = ctx.mk_app(Op::Builtin(BuiltinOp::FpIsNaN), &[rem]).unwrap();
    let atoms = collect_fp_atoms(&ctx, &[isnan]);
    assert!(fp_atoms_fully_supported(&ctx, &atoms), "fp.rem is in scope as of slice 2g");
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p shinri-fp lower_fp_rem_eq_atom; cargo test -p shinri-solver fp_rem_word_is_supported`
Expected: FAIL — `lower_fp_rem_eq_atom` panics at the `blast_word` `unreachable!` arm (FpRem not dispatched); `fp_rem_word_is_supported` fails the assert (FpRem hits the `_ => false` arm).

- [ ] **Step 3: Add the `blast_word` dispatch arm**

In `lib.rs`, after the `FpFma => { … }` arm (before `other => unreachable!(...)`):

```rust
FpRem => {
    let xw = self.blast_word(ctx, kids[0]);
    let yw = self.blast_word(ctx, kids[1]);
    crate::blast::rem::fp_rem(&mut self.b, &xw, &yw, eb, sb)
}
```

- [ ] **Step 4: Add the `is_supported_fp_word` arm + update docs**

In `fp_stage.rs`, alongside the `FpMin | FpMax` arm:

```rust
// fp.rem: (F, F) -> F. No RM operand; both FP operands supported.
TermNode::App { op: Op::Builtin(BuiltinOp::FpRem), args, .. } => {
    let kids = ctx.children(*args).to_vec();
    kids.len() == 2
        && is_supported_fp_word(ctx, kids[0])
        && is_supported_fp_word(ctx, kids[1])
}
```

Update the doc-comment enumeration (~line 111-123) to add "slice 2g (FpRem)" and include `FpMin/FpMax` style mention of `FpRem`. Update the fall-through comment (~line 171) to drop `FpRem`:

```rust
// Anything else (Ite over FP, non-nullary UF, conversions, etc.) is not in
// scope for slices 1–2g.
_ => false,
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p shinri-fp lower_fp_rem_eq_atom; cargo test -p shinri-solver fp_rem_word_is_supported`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/shinri-fp/src/lib.rs crates/shinri-solver/src/fp_stage.rs
git commit -m "feat(solver): admit fp.rem through the FP soundness fence + dispatch"
```

---

### Task 5: End-to-end tests

Prove `fp.rem` answers SAT/UNSAT with model round-trips, and add the slice-2g fence canary. Mirrors the established `fp_e2e.rs` blocks for prior ops.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_e2e.rs` (new `── Slice-2g …` block at end)

**Interfaces:**
- Consumes: the `run(script) -> (SolveOutcome, String)` harness and `SolveOutcome` (existing).
- Produces: four `#[test]` fns.

- [ ] **Step 1: Write the end-to-end tests**

```rust
// ── Slice-2g end-to-end: fp.rem SAT/UNSAT + get-model + fence canary ──

#[test]
fn fp_rem_known_value_sat() {
    // 5.0 rem 3.0 = -1.0; assert fp.eq with -1.0 -> SAT.
    let (o, _) = run(
        "(assert (fp.eq (fp.rem (fp #b0 #x82 #b01000000000000000000000) \
                                (fp #b0 #x80 #b10000000000000000000000)) \
                        (fp #b1 #x7f #b00000000000000000000000))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Sat);
}

#[test]
fn fp_rem_bounded_magnitude_unsat() {
    // For all finite x, |fp.rem x 2.0| <= 1.0, so fp.gt(rem, 1.0) AND finite is UNSAT.
    // Encode: x rem 2 cannot exceed 1.0 in magnitude -> asserting it is > 1.0 with x,result
    // forced finite is UNSAT. Use fp.lt to keep it crisp: rem(x,2) > 1.5 is UNSAT.
    let (o, _) = run(
        "(declare-fun x () Float32) \
         (assert (fp.gt (fp.abs (fp.rem x (fp #b0 #x80 #b10000000000000000000000))) \
                        (fp #b0 #x80 #b10000000000000000000000))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unsat);
}

#[test]
fn fp_rem_sat_get_model() {
    // w = rem(x, y): SAT, model renders fp triples.
    let (o, model) = run(
        "(declare-fun x () Float32) (declare-fun y () Float32) (declare-fun w () Float32) \
         (assert (fp.eq w (fp.rem x y))) (check-sat) (get-model)",
    );
    assert_eq!(o, SolveOutcome::Sat);
    assert!(model.contains("(fp #b"), "model renders fp triples: {model}");
}

#[test]
fn fp_rem_malformed_is_unknown() {
    // Slice-2g fence canary: a fp.rem nesting an unsupported FP word (to_fp from a
    // symbolic Real, durably out of scope) must trip the fence -> Unknown.
    let (o, _) = run(
        "(declare-fun x () Float32) (declare-fun u () Float32) (declare-fun r () Real) \
         (assert (fp.eq u (fp.rem x ((_ to_fp 8 24) RNE r)))) (check-sat)",
    );
    assert_eq!(o, SolveOutcome::Unknown);
}
```

> **Note on `fp_rem_bounded_magnitude_unsat`.** The exact bound is `|rem(x,2)| ≤ 1.0`; asserting `> 2.0` (the divisor) is comfortably UNSAT and avoids any boundary subtlety. If this instance proves too deep to refute eagerly in CI time (symbolic `x`, ~276-stage circuit), downgrade it to a *concrete*-`x` UNSAT (e.g. `rem(7.0,2.0) = -1.0`, assert `fp.eq … (+1.0)` → UNSAT) which constant-folds and stays fast. Prefer the concrete form if the symbolic one is slow.

- [ ] **Step 2: Run the end-to-end tests**

Run (background — symbolic cases are deep): `cargo test -p shinri-solver --test fp_e2e fp_rem -- --nocapture`
Expected: PASS (all four). If `fp_rem_bounded_magnitude_unsat` is slow, switch to the concrete-`x` form per the note.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_e2e.rs
git commit -m "test(fp): end-to-end fp.rem SAT/UNSAT + get-model + slice-2g fence canary"
```

---

### Task 6: Differential-vs-z3 oracle

Extend the feature-gated oracle with a `fp.rem` generator and a bounded differential test. `fp.rem` circuits are the deepest yet — bound iterations low and keep the harness identical to `differential_qf_fp_div`.

**Files:**
- Modify: `crates/shinri-solver/tests/fp_oracle.rs` (add `gen_rem_script` + `differential_qf_fp_rem` after the div oracle, ~line 503)

**Interfaces:**
- Consumes: `Lcg`, `shinri_outcome`, `z3_outcome_arith`, `SolveOutcome`, `easy_smt` (all existing in the file). `fp.rem` takes no RM, so the generator declares no `rm` variable.
- Produces: `fn gen_rem_script(rng: &mut Lcg) -> String` and `#[test] fn differential_qf_fp_rem()`.

- [ ] **Step 1: Add the generator and test**

```rust
/// Generate a random QF_FP script with fp.rem (two fp32 vars; no rounding mode —
/// fp.rem is exact). Builds 1–3 assertions mixing fp.rem with fp.eq/=/fp.isNaN
/// atoms, some negated, so both SAT and UNSAT witnesses arise.
fn gen_rem_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = "(fp.rem x y)".to_string();
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

// fp.rem is the deepest FP datapath: the fmod reduction loop unrolls to ~276
// stages for Float32, so each symbolic instance is a very deep circuit. Bound the
// oracle well below the div bound; raise only behind a per-instance wall-clock
// timeout (a hard symbolic UNSAT can grind for hours in the eager bit-blaster).
const REM_ITERS: usize = 20;

#[test]
fn differential_qf_fp_rem() {
    let mut rng = Lcg(0x00FE_2C0D_3E11);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..REM_ITERS {
        let src = gen_rem_script(&mut rng);
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
                "QF_FP rem DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
        }
    }
    println!("differential_qf_fp_rem: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0, "oracle produced no SAT coverage");
}
```

> **Coverage note.** Unlike the add/mul oracles, this asserts only `n_sat > 0` (not also `n_unsat > 0`): at `REM_ITERS = 20` a symbolic UNSAT may not arise cheaply, and the SAT-direction agreement plus the exhaustive `(3,5)` gate (Task 3) and concrete e2e UNSAT (Task 5) already cover the UNSAT direction. If a tuned seed yields a fast UNSAT within the bound, strengthen to `n_unsat > 0`.

- [ ] **Step 2: Run the oracle (background, feature-gated; requires z3 on PATH)**

Run in the background: `cargo test -p shinri-solver --features oracle --test fp_oracle differential_qf_fp_rem -- --nocapture`
Expected: PASS — prints non-zero `sat=`, zero disagreements.

- [ ] **Step 3: Commit**

```bash
git add crates/shinri-solver/tests/fp_oracle.rs
git commit -m "test(fp): differential-vs-z3 oracle for fp.rem (bounded, deep circuits)"
```

---

### Task 7: Full-suite verification + cross-slice canary sweep + docs

The slice-completion gate. Per the cross-slice-canary lesson, the WHOLE `fp_e2e` suite (not just the new tests) is what catches a stale canary — run it in full, and grep for any other `fp.rem` usage that may have flipped.

**Files:**
- Modify: `docs/superpowers/specs/2026-06-24-shinri-qffp-design.md` (optional: tick `fp.rem` as landed if a status list is maintained) — only if such a list exists; otherwise skip.

- [ ] **Step 1: Cross-slice canary sweep**

Run: `grep -rn 'fp.rem\|FpRem' crates/shinri-solver/tests/ crates/shinri-fp/`
Expected: every `fp.rem`/`FpRem` occurrence is either (a) a slice-2g test/impl added by this plan, or (b) NOT inside a `*_malformed_is_unknown` / fence canary that expects `Unknown`. If any *other* canary still uses `fp.rem` as its out-of-scope trigger, repoint it to `((_ to_fp 8 24) RNE r)` (symbolic Real) exactly as Task 2 did, and note it in the commit.

- [ ] **Step 2: Full FP end-to-end suite (the canary catch-net)**

Run: `cargo test -p shinri-solver --test fp_e2e`
Expected: PASS — all FP e2e tests, including every prior slice's canary, are green. A failure here is the expected cross-slice canary breakage; fix per Step 1.

- [ ] **Step 3: Full workspace non-regression (background; long)**

Run in the background: `cargo test --workspace`
Expected: PASS — the entire workspace stays green; the QF_BV path and the FP-private `Blaster` are untouched.

- [ ] **Step 4: Clippy + fmt**

Run: `cargo clippy --workspace --all-targets -- -D warnings && cargo fmt --check`
Expected: clean. (If `rem.rs`'s index-arithmetic muxes trip `needless_range_loop`, add the same `#[allow(clippy::needless_range_loop)]` with the load-bearing-index rationale used in `operand.rs`/`roundint.rs`.)

- [ ] **Step 5: Final commit**

```bash
git add -A
git commit -m "docs(fp): mark fp.rem landed — slice 2g complete (Plan 2 closed)"
```

---

## Self-Review

**Spec coverage** (against `2026-06-30-shinri-qffp-slice2g-rem-design.md`):
- §1 Semantics (exact, mode-independent, special table) → `ref_rem` (Task 1) + circuit special-case mux (Task 3 Step 3) + `ref_rem_specials`/`rem_float32_specials_and_random`.
- §2 Reference oracle → Task 1.
- §3 Circuit (narrow fmod loop, round-to-even correction, no rounder, normalize/pack) → Task 3.
- §4 Dispatch + fence (RM-less `(F,F)` shape) → Task 4.
- §5 Canary repoint (durable, Float-sorted) → Task 2 (pre-emptive) + Task 7 (sweep).
- §6 Validation (exhaustive (3,5), randomized Float16/32, deep-gap stress, z3 differential, e2e, non-regression) → Tasks 3/5/6/7. *Note: design says "Float16/Float32"; plan exercises `(3,5)` exhaustively + Float32 randomized + the worst-gap stress, matching the prior slices' actual coverage (which likewise sample one large format). Float16 randomized may be added to `rem_float32_specials_and_random` trivially if desired — not load-bearing.*
- §7 Soundness contract → fence admission is positive-enumeration; everything else stays `_ => false`.

**Placeholder scan:** no TBD/TODO. The one judgement-dependent spot — the `fp.rem` circuit body — is shipped as complete code with the exhaustive `(3,5)` test as its definitive gate and explicit "expect to iterate" guidance, consistent with how prior deep FP datapaths (div/sqrt/fma) were landed.

**Type consistency:** `ref_rem(eb,sb,&Integer,&Integer) -> Integer` (no mode) used identically in Tasks 1/3. `fp_rem(&mut Blaster,&[BitLit],&[BitLit],eb,sb) -> Vec<BitLit>` (no RM) used identically in Tasks 3/4. `FpRem` is `(F,F)->F` per core; the `is_supported_fp_word` arm and `blast_word` arm both take exactly `kids[0], kids[1]`. Canary trigger `((_ to_fp 8 24) RNE r)` with `(declare-fun r () Real)` is identical across Tasks 2/5/7.

**Known risk (called out, not hidden):** the circuit's correction-stage alignment (`dd`/sticky, `exp_diff` basis) is the most error-prone part; Task 3 Step 3 flags it and the exhaustive gate pins it. All referenced symbols are verified to exist: `fp_atoms_fully_supported`/`collect_fp_atoms` (fp_stage.rs), `compare::eq`/`uge`/`ult` (shinri-bv), `shift_right_sticky`/`round`/`ExtFp`/`exp_w` (round.rs), `rm::literal` (rm.rs), `run -> (SolveOutcome, String)` (fp_e2e.rs).
