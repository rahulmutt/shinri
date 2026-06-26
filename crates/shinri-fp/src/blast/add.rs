//! fp.add datapath: unpack → align → operate → normalize → round → special-case.

use shinri_bv::{BitLit, Blaster};
use crate::round::{exp_w, round, ExtFp};
use crate::rm::RmSel;
use crate::lzc::lzc;
use crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};

pub fn fp_add(b: &mut Blaster, x: &[BitLit], y: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let ox = to_operand(b, x, eb, sb);
    let oy = to_operand(b, y, eb, sb);

    // --- Order so |x| >= |y| by (exp, sig). ---
    let exp_gt = signed_gt(b, &ox.exp, &oy.exp);
    let exp_eq = bits_equal(b, &ox.exp, &oy.exp);
    let sig_ge = unsigned_ge(b, &ox.sig, &oy.sig);
    let tie = b.and2(exp_eq, sig_ge);
    let x_ge_y = b.or2(exp_gt, tie);
    // hi = larger magnitude operand, lo = smaller (selected fieldwise).
    let (hi, lo) = select_operands(b, x_ge_y, &ox, &oy, ew, sbu);

    // --- Align lo to hi: right-shift lo.sig by (hi.exp - lo.exp), sticky. ---
    let exp_diff = shinri_bv::blast::arith::bvsub(b, &hi.exp, &lo.exp); // >= 0 since hi>=lo
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
    let sum_add = shinri_bv::blast::arith::bvadd(b, &hi_ext, &lo_aln);  // sbu+3 bits
    // subtract: hi_ext - lo_aln (hi is larger magnitude so result >= 0).
    let sum_sub = shinri_bv::blast::arith::bvsub(b, &hi_ext, &lo_aln);
    let mant: Vec<BitLit> = (0..(sbu + 3)).map(|i| b.mux2(same_sign, sum_add[i], sum_sub[i])).collect();
    // add can overflow the top by 1 bit (carry into a new MSB). Capture it:
    let add_carry = {
        let (_s, c) = shinri_bv::blast::arith::adder(b, &hi_ext, &lo_aln, b.zero());
        b.and2(same_sign, c)
    };

    // Exact-zero finite result (cancellation): the post-operate mantissa is all
    // zero AND there is no add carry. Covers (+x)+(-x), (+0)+(-0), (-0)+(+0), and
    // (+0)+(+0)/(-0)+(-0) (all reduce to a zero magnitude here). The IEEE sign of
    // such a zero is governed by the original operand signs, NOT hi.sign — handled
    // in the special-case mux below.
    let cancel_zero = {
        let mut all_zero = b.one();
        for &m in &mant { let nm = b.not1(m); all_zero = b.and2(all_zero, nm); }
        let no_carry = b.not1(add_carry);
        b.and2(all_zero, no_carry)
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
    let mut mant_a: Vec<BitLit> = Vec::with_capacity(sbu + 3);
    for i in 0..(sbu + 3) {
        let hb = if i + 1 < sbu + 3 { mant[i + 1] } else { add_carry };
        mant_a.push(hb);
    }
    // The right-shift-by-1 drops mant[0] (the old sticky column); merge it back
    // into the new sticky bit so no residue is lost (else round-up/sticky-driven
    // modes underround, e.g. Rtp on a barely-inexact carry sum).
    mant_a[0] = b.or2(mant_a[0], mant[0]);
    let one_ew = const_ew(b, ew, 1);
    let exp_a = shinri_bv::blast::arith::bvadd(b, &base_exp, &one_ew);
    // Case B: lz of mant, left shift.
    let lz = lzc(b, &mant);                       // count_width bits
    let lz_ew = zero_extend(b, &lz, ew);
    let mant_b = shinri_bv::blast::shift::bvshl(b, &mant, &lz_ew);
    let exp_b = shinri_bv::blast::arith::bvsub(b, &base_exp, &lz_ew);
    // choose.
    let mant_n: Vec<BitLit> = (0..(sbu + 3)).map(|i| b.mux2(add_carry, mant_a[i], mant_b[i])).collect();
    let exp_n: Vec<BitLit> = (0..ew).map(|i| b.mux2(add_carry, exp_a[i], exp_b[i])).collect();

    // --- Build ExtFp: top sb bits of mant_n are the significand; bits [2,1,0]→(G,R,S). ---
    // mant_n layout: [0..3) are GRS columns, [3..) sig. After normalize the leading
    // 1 is at index sbu+2 (top). The sb significand is mant_n[3 .. 3+sbu];
    // G=mant_n[2], R=mant_n[1], S=mant_n[0].
    let sig_ext: Vec<BitLit> = mant_n[3..3 + sbu].to_vec();
    let grs = (mant_n[2], mant_n[1], mant_n[0]);
    let ext = ExtFp { sign: res_sign, exp: exp_n, sig: sig_ext, grs };
    let rounded = round(b, ext, eb, sb, rm);

    // --- Special-case mux (overrides rounded). ---
    special_case(b, &rounded, &ox, &oy, cancel_zero, rm, eb, sb)
}

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
    fn pick(b: &mut Blaster, sel: BitLit, a: &Operand, c: &Operand, ew: usize, sbu: usize) -> Operand {
        let exp = (0..ew).map(|i| b.mux2(sel, a.exp[i], c.exp[i])).collect();
        let sig = (0..sbu).map(|i| b.mux2(sel, a.sig[i], c.sig[i])).collect();
        Operand {
            sign: b.mux2(sel, a.sign, c.sign),
            exp, sig,
            is_nan: b.mux2(sel, a.is_nan, c.is_nan),
            is_inf: b.mux2(sel, a.is_inf, c.is_inf),
            is_zero: b.mux2(sel, a.is_zero, c.is_zero),
        }
    }
    let hi = pick(b, x_ge_y, ox, oy, ew, sbu);
    let lo = pick(b, x_ge_y, oy, ox, ew, sbu); // swapped
    (hi, lo)
}

/// IEEE fp.add special cases override the datapath result.
#[allow(clippy::too_many_arguments)]
fn special_case(b: &mut Blaster, normal: &[BitLit], ox: &Operand, oy: &Operand,
                cancel_zero: BitLit, rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);
    // NaN if either input NaN, or (+inf)+(-inf).
    let either_nan = b.or2(ox.is_nan, oy.is_nan);
    let opp_sign = b.xor2(ox.sign, oy.sign);
    let both_inf = b.and2(ox.is_inf, oy.is_inf);
    let inf_minus_inf = b.and2(both_inf, opp_sign);
    let want_nan = b.or2(either_nan, inf_minus_inf);
    // Inf result if either input inf (and not the NaN case): sign of the inf input.
    let any_inf = b.or2(ox.is_inf, oy.is_inf);
    let inf_sign = b.mux2(ox.is_inf, ox.sign, oy.sign);
    let inf_bits = inf_pattern_bits(b, eb, sb, inf_sign);
    // Exact-zero finite result (cancellation, incl. both inputs zero) → IEEE sign
    // rule, matching ref_add: neg iff (sign_a AND sign_b) OR roundTowardNegative.
    let both_neg = b.and2(ox.sign, oy.sign);
    let rtn = rm.sel[3];
    let zero_neg = b.or2(both_neg, rtn);
    let zero_bits = signed_zero_bits(b, eb, sb, zero_neg);

    // Priority: NaN > Inf > cancel_zero > normal.
    let mut out = normal.to_vec();
    for i in 0..w { out[i] = b.mux2(cancel_zero, zero_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(any_inf, inf_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_nan, nan[i], out[i]); }
    out
}

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
