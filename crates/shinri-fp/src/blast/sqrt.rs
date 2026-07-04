//! fp.sqrt datapath: unpack → prenormalize → integer sqrt → normalize → round → special-case.

use crate::blast::normalize::{const_n, prenormalize, zero_extend};
use crate::blast::operand::{
    canon_nan_bits, inf_pattern_bits, signed_zero_bits, to_operand, Operand,
};
use crate::rm::RmSel;
use crate::round::{exp_w, round, ExtFp};
use shinri_bv::{BitLit, Blaster};

/// Restoring digit-recurrence integer square root.
/// `radicand` is `2*m` bits (LSB→MSB). Returns `(q, rem)` with `q` = `m` bits =
/// floor(sqrt(radicand)) and `rem` = radicand - q*q (width m+2).
fn usqrt_rem(b: &mut Blaster, radicand: &[BitLit], m: usize) -> (Vec<BitLit>, Vec<BitLit>) {
    let rw = m + 2; // partial-remainder width
    let mut rem: Vec<BitLit> = vec![b.zero(); rw];
    let mut q: Vec<BitLit> = Vec::with_capacity(m); // built MSB-first, reversed at end
    for i in (0..m).rev() {
        // bring down the next radicand pair: rem = (rem << 2) | (R[2i+1], R[2i])
        let mut nr = vec![radicand[2 * i], radicand[2 * i + 1]];
        nr.extend_from_slice(&rem[..rw - 2]); // keep width rw
                                              // trial t = (q_sofar << 2) | 1  (q_sofar currently holds the high bits, MSB-first)
                                              // Build q_sofar as an integer LSB→MSB of the bits accumulated so far.
        let mut t = vec![b.one(), b.zero()];
        for bit in q.iter().rev() {
            t.push(*bit);
        } // q.rev() = LSB→MSB
        while t.len() < rw {
            t.push(b.zero());
        }
        let t = t[..rw].to_vec();
        let ge = shinri_bv::blast::compare::uge(b, &nr, &t);
        let sub = shinri_bv::blast::arith::bvsub(b, &nr, &t);
        rem = (0..rw).map(|k| b.mux2(ge, sub[k], nr[k])).collect();
        q.push(ge); // new high bit of the root
    }
    q.reverse(); // now LSB→MSB, m bits
    (q, rem)
}

pub fn fp_sqrt(b: &mut Blaster, x: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let m = sbu + 2; // result bits from the root: sig(sb) + G + R
    let wr = 2 * m; // radicand width
    let ox = to_operand(b, x, eb, sb);

    // --- Prenormalize significand into [2^(sb-1), 2^sb). ---
    let (sig_n, exp_n) = prenormalize(b, &ox.sig, &ox.exp, sbu, ew);

    // --- Exponent parity: exp_n = 2*h + c, c = exp_n & 1 (LSB), h = exp_n >> 1 (arith). ---
    let c = exp_n[0];
    let h = shinri_bv::blast::shift::bvashr(b, &exp_n, &const_n(b, ew, 1));

    // --- Radicand mantissa B = sig_n << c, then left-align into wr bits. ---
    let sig_w = zero_extend(b, &sig_n, wr);
    let c_w = {
        let mut v = vec![c];
        while v.len() < wr {
            v.push(b.zero());
        }
        v
    }; // shift amount = c (0 or 1)
    let b_shifted = shinri_bv::blast::shift::bvshl(b, &sig_w, &c_w);
    // Align so the root yields m bits with a fixed leading 1. ALIGN pinned by the
    // exhaustive test to 2*m - (sb + 1) (= 8 at eb=3,sb=5): an even radicand scale
    // (2^align) keeps √ exact in powers of two, giving q ∈ [2^(m-1), 2^m).
    let align = (2 * m) - (sbu + 1);
    let radicand = shinri_bv::blast::shift::bvshl(b, &b_shifted, &const_n(b, wr, align as i128));

    // --- Integer square root. ---
    let (q, rem) = usqrt_rem(b, &radicand, m); // q: m bits, leading 1 fixed at index m-1

    // --- GRS extraction: sig = top sb bits of q, G = q[m-1-sb]=q[1], R = q[0]. ---
    // q is m = sb+2 bits; q[m-1] is the fixed leading 1. sig = q[2..m] (sb bits),
    // G = q[1], R = q[0], S = OR(none here) OR (rem != 0).
    let sig: Vec<BitLit> = q[2..m].to_vec(); // sb bits, hidden at index sb-1
    let g = q[1];
    let r = q[0];
    let mut s = b.zero();
    for bit in &rem {
        s = b.or2(s, *bit);
    } // remainder folds into sticky

    // --- Exponent out: norm_exp = h + corr. CORR pinned by the exhaustive test
    //     to 0 (the (sb-1)/2, (m-sb) and align/2 offsets cancel in round()'s
    //     ExtFp convention). ---
    let corr = const_n(b, ew, 0);
    let norm_exp = shinri_bv::blast::arith::bvadd(b, &h, &corr);

    let ext = ExtFp {
        sign: ox.sign,
        exp: norm_exp,
        sig,
        grs: (g, r, s),
    };
    let rounded = round(b, ext, eb, sb, rm);

    special_case(b, &rounded, &ox, eb, sb)
}

/// IEEE fp.sqrt special cases. Priority NaN > Inf > Zero.
fn special_case(b: &mut Blaster, normal: &[BitLit], ox: &Operand, eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);

    // NaN if input NaN, or input negative & nonzero (incl -inf, -normal, -subnormal).
    let not_zero = b.not1(ox.is_zero);
    let neg_nonzero = b.and2(ox.sign, not_zero);
    let want_nan = b.or2(ox.is_nan, neg_nonzero);

    // +inf if +inf input.
    let not_sign = b.not1(ox.sign);
    let want_inf = b.and2(ox.is_inf, not_sign);
    let inf_bits = inf_pattern_bits(b, eb, sb, b.zero());

    // signed zero if zero input (sign preserved).
    let want_zero = ox.is_zero;
    let zero_bits = signed_zero_bits(b, eb, sb, ox.sign);

    let mut out = normal.to_vec();
    for i in 0..w {
        out[i] = b.mux2(want_zero, zero_bits[i], out[i]);
    }
    for i in 0..w {
        out[i] = b.mux2(want_inf, inf_bits[i], out[i]);
    }
    for i in 0..w {
        out[i] = b.mux2(want_nan, nan[i], out[i]);
    }
    out
}

#[cfg(test)]
mod tests {
    use crate::blast::sqrt::fp_sqrt;
    use crate::reference::{ref_sqrt, RoundMode};
    use crate::rm;
    use shinri_bv::{BitLit, Blaster};
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
    fn fp_sqrt_float32_specials_and_random() {
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
        let mut state: u64 = 0x5172_7100;
        let mut next = || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            state >> 16
        };
        let mut cases: Vec<u64> = specials.to_vec();
        for _ in 0..200 {
            cases.push(next() & 0xFFFF_FFFF);
        }
        for a in cases {
            for m in modes {
                let want = ref_sqrt(eb, sb, &Integer::from(a), m);
                let mut bl = Blaster::new();
                let xv = const_bits(&bl, eb, sb, a);
                let sel = rm::literal(&bl, rmode(m));
                let word = fp_sqrt(&mut bl, &xv, &sel, eb, sb);
                assert_eq!(
                    Integer::from(eval_word(bl, &word)),
                    want,
                    "fp.sqrt32 a={a:#x} m={m:?}"
                );
            }
        }
    }

    #[test]
    fn fp_sqrt_tiny_exhaustive_all_modes() {
        let (eb, sb) = (3u32, 5u32);
        let modes = [
            RoundMode::Rne,
            RoundMode::Rna,
            RoundMode::Rtp,
            RoundMode::Rtn,
            RoundMode::Rtz,
        ];
        for a in 0u64..256 {
            for m in modes {
                let want = ref_sqrt(eb, sb, &Integer::from(a), m);
                let mut bl = Blaster::new();
                let xv = const_bits(&bl, eb, sb, a);
                let sel = rm::literal(&bl, rmode(m));
                let word = fp_sqrt(&mut bl, &xv, &sel, eb, sb);
                assert_eq!(
                    Integer::from(eval_word(bl, &word)),
                    want,
                    "fp.sqrt a={a:#x} m={m:?}"
                );
            }
        }
    }
}
