//! FP conversions (non-BV faces of to_fp): FP→FP re-round + constant-Real fold.
//! FP→FP: unpack → prenormalize → saturate exponent → static significand split →
//! shared rounder → special mux. const-Real: fold round_rational, one-hot by RM.

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
