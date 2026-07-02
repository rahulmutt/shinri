//! FP conversions: FP→FP re-round, constant-Real fold, BV→FP, and FP→BV
//! (`fp.to_ubv`/`fp.to_sbv`) via a single shift+sticky register.
//! FP→FP: unpack → prenormalize → saturate exponent → static significand split →
//! shared rounder → special mux. const-Real: fold round_rational, one-hot by RM.

use shinri_bv::{BitLit, Blaster};
use shinri_bv::blast::arith::{bvadd, bvneg, bvsub};
use crate::blast::operand::{to_operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};
use crate::blast::normalize::{const_n, prenormalize};
use crate::round::{exp_w, round, rounding_increment, shift_right_sticky, ExtFp};
use crate::rm::RmSel;
use crate::reference::{field, round_rational, RoundMode};
use shinri_num::Rational;

/// Sign-extend a signed word `x` (LSB→MSB) to width `to` by replicating its MSB.
fn sign_extend(_b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit> {
    let msb = *x.last().unwrap();
    let mut out = x.to_vec();
    while out.len() < to { out.push(msb); }
    out
}

/// `((_ to_fp eb_t sb_t) rm x)` for an FP source `x` of format (eb_s, sb_s).
/// Unpack → prenormalize → saturate the (format-independent) unbiased exponent
/// into the target width → static significand split → shared rounder → special mux.
#[allow(clippy::needless_range_loop)] // indices are load-bearing: parallel-indexed words
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
    let hi = emax_t + 1;                    // round(): exp > emax_t → overflow (mode-dep. ±inf/±max-finite)
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
    let hi = emax_t + 1;                    // round(): exp > emax_t → overflow (mode-dep. ±inf/±max-finite)
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

/// `((_ fp.to_ubv m) rm x)` (`signed_face = false`) and `((_ fp.to_sbv m) rm x)`
/// (`signed_face = true`): round the real value of `x` to an integer per `rm`,
/// THEN range-check the rounded integer (SMT-LIB; z3-verified in the slice-4e
/// spec). Returns `(m-bit word, ok)`: `ok = 0` on NaN/±inf/out-of-range, in
/// which case the word is FRESH UNCONSTRAINED bits (the SMT-LIB "unspecified
/// value"; cross-application congruence is the dispatch layer's job, not ours).
#[allow(clippy::needless_range_loop)] // indices are load-bearing: parallel-indexed words
pub fn fp_to_int(
    b: &mut Blaster, x: &[BitLit], eb: u32, sb: u32, m: u32, signed_face: bool, rm: &RmSel,
) -> (Vec<BitLit>, BitLit) {
    let mu = m as usize;
    let sbu = sb as usize;
    let ew = exp_w(eb);
    let o = to_operand(b, x, eb, sb);

    // --- 1. shift amount: amt = m - e (signed, width wa). Every in-range case
    //     has e <= m-1 so amt >= 1; amt <= 0 (e >= m ⇒ |value| >= 2^m) is the
    //     out-of-range short-circuit. wa holds m and e without wrap (same
    //     width argument as to_fp_int's clamp). ---
    let bits_for_m = (64 - (m as u64).leading_zeros()) as usize + 1;
    let wa = ew.max(bits_for_m) + 1;
    let e_wide = sign_extend(b, &o.exp, wa);
    let m_const = const_n(b, wa, m as i128);
    let amt = bvsub(b, &m_const, &e_wide);
    let amt_neg = amt[wa - 1];
    let mut amt_zero = b.one();
    for &bit in &amt { let nb = b.not1(bit); amt_zero = b.and2(amt_zero, nb); }
    let oor_high = b.or2(amt_neg, amt_zero);
    // (amt < 0 reads as huge-unsigned in bvlshr → register drains to 0 with full
    // sticky; harmless — oor_high overrides everything downstream.)

    // --- 2. fixed-point register R = |value| · 2^P: [P = sb+1 fraction | m+1
    //     integer] bits. sig placed at the top corresponds to e = m; shifting
    //     right by amt = m - e aligns exactly, bits below R[0] fold into the
    //     shift sticky. ---
    let p = sbu + 1;
    let wr = (mu + 1) + p;
    let mut r0 = vec![b.zero(); wr];
    for i in 0..sbu { r0[wr - sbu + i] = o.sig[i]; }
    let (r, sticky_shift) = shift_right_sticky(b, &r0, &amt);

    // --- 3. GRS + shared rounding increment on the magnitude. ---
    let g = r[p - 1];
    let rd = r[p - 2]; // p = sb+1 >= 3 for every real format
    let mut s = sticky_shift;
    for i in 0..(p - 2) { s = b.or2(s, r[i]); }
    let int_part: Vec<BitLit> = r[p..].to_vec(); // m+1 bits
    let inc = rounding_increment(b, o.sign, g, rd, s, int_part[0], rm);
    let mut inc_w = vec![b.zero(); mu + 1];
    inc_w[0] = inc;
    let mag = bvadd(b, &int_part, &inc_w); // rounded |result|, m+1 bits (2^m visible)

    // --- 4. range check per face + sign application. ---
    let mag_top = mag[mu]; // the 2^m bit
    let mut mag_zero = b.one();
    for &bit in &mag { let nb = b.not1(bit); mag_zero = b.and2(mag_zero, nb); }
    let low: Vec<BitLit> = mag[..mu].to_vec();
    let (fits, res): (BitLit, Vec<BitLit>) = if !signed_face {
        // ubv: 0 <= mag <= 2^m - 1, and a negative value only if it rounded to 0.
        let not_top = b.not1(mag_top);
        let not_sign = b.not1(o.sign);
        let sign_ok = b.or2(not_sign, mag_zero);
        (b.and2(not_top, sign_ok), low)
    } else {
        // sbv: positive needs mag <= 2^(m-1)-1; negative admits mag = 2^(m-1)
        // (INT_MIN). Result is the two's-complement of the magnitude when negative.
        let mag_msb = mag[mu - 1];
        let not_top = b.not1(mag_top);
        let not_msb = b.not1(mag_msb);
        let mut rest_zero = b.one();
        for i in 0..(mu - 1) { let nb = b.not1(mag[i]); rest_zero = b.and2(rest_zero, nb); }
        let pos_ok = b.and2(not_top, not_msb);
        let neg_bound = b.or2(not_msb, rest_zero); // mag <= 2^(m-1)
        let neg_ok = b.and2(not_top, neg_bound);
        let fits = b.mux2(o.sign, neg_ok, pos_ok);
        let neg = bvneg(b, &low);
        let res: Vec<BitLit> = (0..mu).map(|i| b.mux2(o.sign, neg[i], low[i])).collect();
        (fits, res)
    };

    // --- 5. ok + unspecified mux: fresh unconstrained bits on ¬ok. ---
    let not_nan = b.not1(o.is_nan);
    let not_inf = b.not1(o.is_inf);
    let not_oor = b.not1(oor_high);
    let finite = b.and2(not_nan, not_inf);
    let in_rng = b.and2(not_oor, fits);
    let ok = b.and2(finite, in_rng);
    let out: Vec<BitLit> = (0..mu).map(|i| {
        let fresh = b.fresh();
        b.mux2(ok, res[i], fresh)
    }).collect();
    (out, ok)
}

/// `((_ to_fp eb sb) rm q)` for a constant Real `q`: fold `round_rational` under
/// each mode and one-hot-select by `rm.sel`. Literal RM constant-folds to a single
/// pattern; symbolic RM stays a 5-way mux over five precomputed literals.
#[allow(clippy::needless_range_loop)] // indices are load-bearing: parallel-indexed words
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

#[cfg(test)]
mod tests {
    use crate::convert::{fp_to_int, to_fp_fp, to_fp_int, to_fp_real_const};
    use crate::reference::{
        ref_to_fp_fp, ref_to_fp_sbv, ref_to_fp_ubv, ref_to_sbv, ref_to_ubv, round_rational, RoundMode,
    };
    use crate::rm;
    use shinri_bv::{BitLit, Blaster};
    use shinri_core::RoundingMode;
    use shinri_num::{Integer, Rational};
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn const_bits(b: &Blaster, eb: u32, sb: u32, value: u64) -> Vec<BitLit> {
        (0..(eb + sb)).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    }
    fn const_bv(b: &Blaster, w: u32, value: u64) -> Vec<BitLit> {
        (0..w).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
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
    /// Evaluate a gadget's `(word, ok)` pair in one solve. Own harness (not a
    /// wrapper over `eval_word`): `eval_word` folds bits into a `u64` and is
    /// hard-capped at 64 bits, so for `word.len() == 64` appending `ok` as a
    /// 65th bit would panic. Read `word` into `v` and `ok` separately instead.
    fn eval_word_and_ok(b: Blaster, word: &[BitLit], ok: BitLit) -> (u64, bool) {
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
        let raw_ok = s.value_of(Var::new(ok.var)).unwrap();
        let ok_val = if ok.pos { raw_ok } else { !raw_ok };
        (v, ok_val)
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

    #[test]
    fn fp_to_int_tiny_exhaustive_both_faces() {
        // Every (3,5) pattern (8 bits), both faces, all five modes, m ∈ {1, 4, 8}:
        // bit-exact vs golden on Some; circuit ok ≡ golden is_some() on EVERY input.
        for &(core_rm, ref_rm) in &MODES {
            for m in [1u32, 4, 8] {
                for a in 0u64..256 {
                    for signed in [true, false] {
                        let want = if signed {
                            ref_to_sbv(3, 5, m, &Integer::from(a), ref_rm)
                        } else {
                            ref_to_ubv(3, 5, m, &Integer::from(a), ref_rm)
                        };
                        let mut b = Blaster::new();
                        let xw = const_bits(&b, 3, 5, a);
                        let sel = rm::literal(&b, core_rm);
                        let (got_w, ok_l) = fp_to_int(&mut b, &xw, 3, 5, m, signed, &sel);
                        let (got, ok) = eval_word_and_ok(b, &got_w, ok_l);
                        assert_eq!(ok, want.is_some(),
                            "(3,5)→{}bv{m} mode {ref_rm:?} a={a:#x}: ok={ok} want_some={}",
                            if signed { "s" } else { "u" }, want.is_some());
                        if let Some(w) = want {
                            assert_eq!(Integer::from(got), w,
                                "(3,5)→{}bv{m} mode {ref_rm:?} a={a:#x}: got {got:#x} want {w}",
                                if signed { "s" } else { "u" });
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn fp_to_int_f16_f32_specials_and_random() {
        // (5,11) and (8,24) sources into m ∈ {8, 32, 64}; seeded specials + PRNG.
        let mut state = 0xDEAD_BEEF_0123_4567u64;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state };
        for (eb, sb) in [(5u32, 11u32), (8, 24)] {
            let w = eb + sb;
            // Specials: NaN, ±inf, ±0, ±1, max-finite, min-subnormal, and values
            // straddling the m-bit range edges (derived via round_rational — exact).
            let f = |v: i64, d: i64| Rational::new(Integer::from(v), Integer::from(d));
            let enc = |q: Rational| {
                let bits = crate::reference::round_rational(eb, sb, &q, RoundMode::Rne);
                // Integer → u64 via the test-side field helper.
                let mut v = 0u64;
                for i in 0..w { if !crate::reference::field(&bits, i, 1).is_zero() { v |= 1 << i; } }
                v
            };
            let mut cases: Vec<u64> = vec![
                enc(f(1_000_000_000, 1)),        // overflows f16 → +inf; huge for f32
                enc(f(-1_000_000_000, 1)),
                1 << (w - 1),                     // -0
                0,                                // +0
                1,                                // min subnormal
                enc(f(1, 1)), enc(f(-1, 1)),
                enc(f(255, 1)), enc(f(256, 1)), enc(f(511, 2)),      // ubv8 edges
                enc(f(-128, 1)), enc(f(-129, 1)), enc(f(-257, 2)),   // sbv8 edges
            ];
            for _ in 0..120 { cases.push(rand() & ((1u64 << w) - 1)); }
            for &(core_rm, ref_rm) in &MODES {
                for m in [8u32, 32, 64] {
                    for &a in &cases {
                        for signed in [true, false] {
                            let want = if signed {
                                ref_to_sbv(eb, sb, m, &Integer::from(a), ref_rm)
                            } else {
                                ref_to_ubv(eb, sb, m, &Integer::from(a), ref_rm)
                            };
                            let mut b = Blaster::new();
                            let xw = const_bits(&b, eb, sb, a);
                            let sel = rm::literal(&b, core_rm);
                            let (got_w, ok_l) = fp_to_int(&mut b, &xw, eb, sb, m, signed, &sel);
                            let (got, ok) = eval_word_and_ok(b, &got_w, ok_l);
                            assert_eq!(ok, want.is_some(),
                                "({eb},{sb})→bv{m} signed={signed} mode {ref_rm:?} a={a:#x}");
                            if let Some(wv) = want {
                                assert_eq!(Integer::from(got), wv,
                                    "({eb},{sb})→bv{m} signed={signed} mode {ref_rm:?} a={a:#x}: got {got:#x}");
                            }
                        }
                    }
                }
            }
        }
    }
}
