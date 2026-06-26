//! fp.div datapath: unpack → pre-normalize → divide → normalize → round → special-case.

use shinri_bv::{BitLit, Blaster};
use crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};
use crate::round::{exp_w, round, ExtFp};
use crate::rm::RmSel;
use crate::lzc::lzc;

fn const_n(b: &Blaster, n: usize, v: i128) -> Vec<BitLit> {
    // Total mask: for n >= 128 the `1 << n` form would overflow i128 (debug panic,
    // release wrap). Widths here reach 2*sb+2 = 228 for binary128, so guard it.
    let mask = if n >= 128 { -1i128 } else { (1i128 << n) - 1 };
    let u = v & mask;
    (0..n).map(|i| if (u >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
}
fn zero_extend(b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit> {
    let mut out = x.to_vec(); while out.len() < to { out.push(b.zero()); } out
}

/// Pre-normalize `sig` (sb bits) so its leading 1 sits at index sb-1, returning
/// (sig_norm, exp_n) with exp_n = exp - shift (signed, ew bits). For a nonzero
/// significand sig_norm lands in [2^(sb-1), 2^sb).
fn prenormalize(b: &mut Blaster, sig: &[BitLit], exp: &[BitLit], sbu: usize, ew: usize)
    -> (Vec<BitLit>, Vec<BitLit>) {
    let k = lzc(b, sig);                                 // count_width(sb) bits
    let k_sb = zero_extend(b, &k, sbu);
    let sig_norm = shinri_bv::blast::shift::bvshl(b, sig, &k_sb);
    let k_ew = zero_extend(b, &k, ew);
    let exp_n = shinri_bv::blast::arith::bvsub(b, exp, &k_ew);
    (sig_norm, exp_n)
}

pub fn fp_div(b: &mut Blaster, x: &[BitLit], y: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let w = 2 * sbu + 2;              // divide width
    let f = sbu + 2;                  // quotient fractional bits
    let ox = to_operand(b, x, eb, sb);
    let oy = to_operand(b, y, eb, sb);

    // --- Sign: XOR. ---
    let res_sign = b.xor2(ox.sign, oy.sign);

    // --- Pre-normalize both significands into [2^(sb-1), 2^sb). ---
    let (xsig_n, exp_x_n) = prenormalize(b, &ox.sig, &ox.exp, sbu, ew);
    let (ysig_n, exp_y_n) = prenormalize(b, &oy.sig, &oy.exp, sbu, ew);

    // --- Divide: dividend = xsig_n << F, divisor = ysig_n, both width W. ---
    let xz = zero_extend(b, &xsig_n, w);
    let shift_f = const_n(b, w, f as i128);
    let dividend = shinri_bv::blast::shift::bvshl(b, &xz, &shift_f);
    let divisor = zero_extend(b, &ysig_n, w);
    let (quot, rem) = shinri_bv::blast::div::udivurem(b, &dividend, &divisor);  // W bits each

    // --- Normalize quotient: leading 1 to index W-1. ---
    let lz = lzc(b, &quot);                              // count_width(W) bits
    let lz_w = zero_extend(b, &lz, w);
    let quot_n = shinri_bv::blast::shift::bvshl(b, &quot, &lz_w);

    // --- Exponent: norm_exp = exp_x_n - exp_y_n + (sb-1) - lz. ---
    let lz_ew = zero_extend(b, &lz, ew);
    let diff = shinri_bv::blast::arith::bvsub(b, &exp_x_n, &exp_y_n);
    let corr = const_n(b, ew, (sb as i128) - 1);
    let with_corr = shinri_bv::blast::arith::bvadd(b, &diff, &corr);
    let norm_exp = shinri_bv::blast::arith::bvsub(b, &with_corr, &lz_ew);

    // --- Build ExtFp from quot_n. Top sb bits = sig (hidden at index W-1);
    //     next bit = G, next = R, OR of the rest (+ rem != 0) = S. ---
    let sig: Vec<BitLit> = quot_n[(w - sbu)..w].to_vec();
    let g = quot_n[w - sbu - 1];
    let r = quot_n[w - sbu - 2];
    let mut s_acc = b.zero();
    for bit in quot_n.iter().take(w - sbu - 2) { s_acc = b.or2(s_acc, *bit); }
    // Fold a nonzero division remainder into the sticky bit.
    let mut rem_nz = b.zero();
    for bit in &rem { rem_nz = b.or2(rem_nz, *bit); }
    let s = b.or2(s_acc, rem_nz);

    let ext = ExtFp { sign: res_sign, exp: norm_exp, sig, grs: (g, r, s) };
    let rounded = round(b, ext, eb, sb, rm);

    // --- Special-case mux (overrides rounded). ---
    special_case(b, &rounded, &ox, &oy, res_sign, eb, sb)
}

/// IEEE fp.div special cases override the datapath result.
/// Priority NaN > Inf > Zero > normal. `res_sign` = sign_x XOR sign_y.
fn special_case(b: &mut Blaster, normal: &[BitLit], ox: &Operand, oy: &Operand,
                res_sign: BitLit, eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);
    let not_x_inf = b.not1(ox.is_inf);
    let not_y_inf = b.not1(oy.is_inf);
    let not_x_zero = b.not1(ox.is_zero);
    let not_y_zero = b.not1(oy.is_zero);

    // NaN if either input NaN, or 0/0, or inf/inf.
    let either_nan = b.or2(ox.is_nan, oy.is_nan);
    let zero_over_zero = b.and2(ox.is_zero, oy.is_zero);
    let inf_over_inf = b.and2(ox.is_inf, oy.is_inf);
    let nan_pair = b.or2(zero_over_zero, inf_over_inf);
    let want_nan = b.or2(either_nan, nan_pair);

    // Inf result: (x_inf AND NOT y_inf) OR (y_zero AND NOT x_zero).  [x/0 -> ±inf]
    let inf_a = b.and2(ox.is_inf, not_y_inf);
    let inf_c = b.and2(oy.is_zero, not_x_zero);
    let want_inf = b.or2(inf_a, inf_c);
    let inf_bits = inf_pattern_bits(b, eb, sb, res_sign);

    // Zero result: (x_zero AND NOT y_zero) OR (y_inf AND NOT x_inf).
    let zero_d = b.and2(ox.is_zero, not_y_zero);
    let zero_e = b.and2(oy.is_inf, not_x_inf);
    let want_zero = b.or2(zero_d, zero_e);
    let zero_bits = signed_zero_bits(b, eb, sb, res_sign);

    let mut out = normal.to_vec();
    for i in 0..w { out[i] = b.mux2(want_zero, zero_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_inf, inf_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_nan, nan[i], out[i]); }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{ref_div, RoundMode};
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
    fn fp_div_tiny_exhaustive_all_modes() {
        let (eb, sb) = (3u32, 5u32);
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        for a in 0u64..256 {
            for bb in 0u64..256 {
                for m in modes {
                    let want = ref_div(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                    let mut bl = Blaster::new();
                    let xv = const_bits(&bl, eb, sb, a);
                    let yv = const_bits(&bl, eb, sb, bb);
                    let sel = rm::literal(&bl, rmode(m));
                    let word = fp_div(&mut bl, &xv, &yv, &sel, eb, sb);
                    assert_eq!(Integer::from(eval_word(bl, &word)), want,
                        "fp.div a={a:#x} b={bb:#x} m={m:?}");
                }
            }
        }
    }

    #[test]
    fn fp_div_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        let specials = [0x0000_0000u64, 0x8000_0000, 0x7F80_0000, 0xFF80_0000, 0x7FC0_0000,
                        0x3F80_0000, 0xBF80_0000, 0x4000_0000, 0x0000_0001, 0x8000_0001,
                        0x7F7F_FFFF, 0x0080_0000];
        let modes = [RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];
        let mut state: u64 = 0x51C0_1A5E;
        let mut next = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state >> 16 };
        let mut cases: Vec<(u64, u64)> = Vec::new();
        for &s1 in &specials { for &s2 in &specials { cases.push((s1, s2)); } }
        for _ in 0..200 { cases.push((next() & 0xFFFF_FFFF, next() & 0xFFFF_FFFF)); }
        for (a, bb) in cases {
            for m in modes {
                let want = ref_div(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                let mut bl = Blaster::new();
                let xv = const_bits(&bl, eb, sb, a);
                let yv = const_bits(&bl, eb, sb, bb);
                let sel = rm::literal(&bl, rmode(m));
                let word = fp_div(&mut bl, &xv, &yv, &sel, eb, sb);
                assert_eq!(Integer::from(eval_word(bl, &word)), want,
                    "fp.div32 a={a:#x} b={bb:#x} m={m:?}");
            }
        }
    }
}
