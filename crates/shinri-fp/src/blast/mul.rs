//! fp.mul datapath: unpack → sign/exp → multiply → normalize → round → special-case.

use crate::blast::operand::{
    canon_nan_bits, inf_pattern_bits, signed_zero_bits, to_operand, Operand,
};
use crate::lzc::lzc;
use crate::rm::RmSel;
use crate::round::{exp_w, round, ExtFp};
use shinri_bv::{BitLit, Blaster};

fn const_ew(b: &Blaster, ew: usize, v: i128) -> Vec<BitLit> {
    let u = v & ((1i128 << ew) - 1);
    (0..ew)
        .map(|i| if (u >> i) & 1 == 1 { b.one() } else { b.zero() })
        .collect()
}
fn zero_extend(b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit> {
    let mut out = x.to_vec();
    while out.len() < to {
        out.push(b.zero());
    }
    out
}

/// Exact normalized significand product, shared by `fp.mul` and `fp.fma`.
/// Returns (prod_n, norm_exp): `prod_n` is the 2·sb-bit product left-shifted so
/// its leading 1 sits at index 2·sb-1; `norm_exp` (signed, exp_w bits) is the
/// exponent of that leading bit, so the product value = prod_n · 2^(norm_exp -
/// (2·sb-1)). No rounding. (Garbage norm_exp when the product is 0 — the caller
/// special-cases a zero product.)
pub(crate) fn significand_product(
    b: &mut Blaster,
    ox: &Operand,
    oy: &Operand,
    eb: u32,
    sb: u32,
) -> (Vec<BitLit>, Vec<BitLit>) {
    let ew = exp_w(eb);
    let pw = 2 * sb as usize;
    let exp_sum = shinri_bv::blast::arith::bvadd(b, &ox.exp, &oy.exp);
    let xe = zero_extend(b, &ox.sig, pw);
    let ye = zero_extend(b, &oy.sig, pw);
    let prod = shinri_bv::blast::arith::bvmul(b, &xe, &ye);
    let lz = lzc(b, &prod);
    let lz_ew = zero_extend(b, &lz, ew);
    let prod_n = shinri_bv::blast::shift::bvshl(b, &prod, &lz_ew);
    let corr = const_ew(b, ew, 1i128);
    let exp_corr = shinri_bv::blast::arith::bvadd(b, &exp_sum, &corr);
    let norm_exp = shinri_bv::blast::arith::bvsub(b, &exp_corr, &lz_ew);
    (prod_n, norm_exp)
}

pub fn fp_mul(
    b: &mut Blaster,
    x: &[BitLit],
    y: &[BitLit],
    rm: &RmSel,
    eb: u32,
    sb: u32,
) -> Vec<BitLit> {
    let sbu = sb as usize;
    let pw = 2 * sbu; // product width
    let ox = to_operand(b, x, eb, sb);
    let oy = to_operand(b, y, eb, sb);

    // --- Sign: XOR. ---
    let res_sign = b.xor2(ox.sign, oy.sign);

    // --- Significand product + normalize (shared with fp.fma). ---
    let (prod_n, norm_exp) = significand_product(b, &ox, &oy, eb, sb);

    // --- Build ExtFp from prod_n. Top sb bits = sig (hidden at index pw-1);
    //     next bit = G, next = R, OR of the rest = S. ---
    // prod_n indices: [pw-1] hidden ... [pw-sb] sig LSB ... down to [0].
    // sig (LSB→MSB) = prod_n[pw-sb .. pw].
    let sig: Vec<BitLit> = prod_n[(pw - sbu)..pw].to_vec();
    // G = prod_n[pw-sb-1], R = prod_n[pw-sb-2] (guard against tiny widths: pw-sb = sb >= 2).
    let g = prod_n[pw - sbu - 1];
    let r = if pw - sbu >= 2 {
        prod_n[pw - sbu - 2]
    } else {
        b.zero()
    };
    // S = OR of all remaining low bits below R, i.e. prod_n[0 .. pw-sb-2].
    let mut s = b.zero();
    let s_hi = (pw - sbu).saturating_sub(2);
    for bit in prod_n.iter().take(s_hi) {
        s = b.or2(s, *bit);
    }

    let ext = ExtFp {
        sign: res_sign,
        exp: norm_exp,
        sig,
        grs: (g, r, s),
    };
    let rounded = round(b, ext, eb, sb, rm);

    // --- Special-case mux (overrides rounded). ---
    special_case(b, &rounded, &ox, &oy, res_sign, eb, sb)
}

/// IEEE fp.mul special cases override the datapath result.
/// Priority NaN > Inf > Zero > normal. `res_sign` = sign_x XOR sign_y.
fn special_case(
    b: &mut Blaster,
    normal: &[BitLit],
    ox: &Operand,
    oy: &Operand,
    res_sign: BitLit,
    eb: u32,
    sb: u32,
) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);
    // NaN if either input NaN, or (0 * inf) in either order.
    let either_nan = b.or2(ox.is_nan, oy.is_nan);
    let zero_times_inf = {
        let a = b.and2(ox.is_zero, oy.is_inf);
        let c = b.and2(ox.is_inf, oy.is_zero);
        b.or2(a, c)
    };
    let want_nan = b.or2(either_nan, zero_times_inf);
    // Inf result if either input inf (and not the NaN case): sign = res_sign.
    let any_inf = b.or2(ox.is_inf, oy.is_inf);
    let inf_bits = inf_pattern_bits(b, eb, sb, res_sign);
    // Zero result if either input zero (finite * 0): sign = res_sign.
    let any_zero = b.or2(ox.is_zero, oy.is_zero);
    let zero_bits = signed_zero_bits(b, eb, sb, res_sign);

    let mut out = normal.to_vec();
    for i in 0..w {
        out[i] = b.mux2(any_zero, zero_bits[i], out[i]);
    }
    for i in 0..w {
        out[i] = b.mux2(any_inf, inf_bits[i], out[i]);
    }
    for i in 0..w {
        out[i] = b.mux2(want_nan, nan[i], out[i]);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{ref_mul, RoundMode};
    use crate::rm;
    use shinri_num::Integer;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn const_bits(b: &Blaster, eb: u32, sb: u32, value: u64) -> Vec<BitLit> {
        (0..(eb + sb))
            .map(|i| {
                if (value >> i) & 1 == 1 {
                    b.one()
                } else {
                    b.zero()
                }
            })
            .collect()
    }
    fn eval_word(b: Blaster, word: &[BitLit]) -> u64 {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars {
            s.new_var();
        }
        for c in &cnf.clauses {
            let ls: Vec<Lit> = c
                .iter()
                .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
                .collect();
            s.add_clause(&ls);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let mut v = 0u64;
        for (i, bl) in word.iter().enumerate() {
            let raw = s.value_of(Var::new(bl.var)).unwrap();
            if if bl.pos { raw } else { !raw } {
                v |= 1 << i;
            }
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
    #[ignore = "exhaustive: nightly tier (~36 min in CI)"]
    fn fp_mul_tiny_exhaustive_all_modes() {
        let (eb, sb) = (3u32, 5u32);
        let modes = [
            RoundMode::Rne,
            RoundMode::Rna,
            RoundMode::Rtp,
            RoundMode::Rtn,
            RoundMode::Rtz,
        ];
        for a in 0u64..256 {
            for bb in 0u64..256 {
                for m in modes {
                    let want = ref_mul(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                    let mut bl = Blaster::new();
                    let xv = const_bits(&bl, eb, sb, a);
                    let yv = const_bits(&bl, eb, sb, bb);
                    let sel = rm::literal(&bl, rmode(m));
                    let word = fp_mul(&mut bl, &xv, &yv, &sel, eb, sb);
                    assert_eq!(
                        Integer::from(eval_word(bl, &word)),
                        want,
                        "fp.mul a={a:#x} b={bb:#x} m={m:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn fp_mul_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        let specials = [
            0x0000_0000u64,
            0x8000_0000,
            0x7F80_0000,
            0xFF80_0000,
            0x7FC0_0000,
            0x3F80_0000,
            0xBF80_0000,
            0x4000_0000,
            0x0000_0001,
            0x8000_0001,
            0x7F7F_FFFF,
            0x0080_0000,
        ];
        let modes = [
            RoundMode::Rne,
            RoundMode::Rna,
            RoundMode::Rtp,
            RoundMode::Rtn,
            RoundMode::Rtz,
        ];
        let mut state: u64 = 0x6D17_5EED;
        let mut next = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            state >> 16
        };
        let mut cases: Vec<(u64, u64)> = Vec::new();
        for &s1 in &specials {
            for &s2 in &specials {
                cases.push((s1, s2));
            }
        }
        for _ in 0..200 {
            cases.push((next() & 0xFFFF_FFFF, next() & 0xFFFF_FFFF));
        }
        for (a, bb) in cases {
            for m in modes {
                let want = ref_mul(eb, sb, &Integer::from(a), &Integer::from(bb), m);
                let mut bl = Blaster::new();
                let xv = const_bits(&bl, eb, sb, a);
                let yv = const_bits(&bl, eb, sb, bb);
                let sel = rm::literal(&bl, rmode(m));
                let word = fp_mul(&mut bl, &xv, &yv, &sel, eb, sb);
                assert_eq!(
                    Integer::from(eval_word(bl, &word)),
                    want,
                    "fp.mul32 a={a:#x} b={bb:#x} m={m:?}"
                );
            }
        }
    }
}
