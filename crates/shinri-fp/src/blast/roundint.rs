//! fp.roundToIntegral datapath: unpack → fraction-mask round → repack, with a
//! sign-preserving ±0/±1 path for |x| < 1. No LZC, no denormalize, no overflow-∞.

use shinri_bv::{BitLit, Blaster};
use shinri_bv::blast::arith::{adder, bvadd};
use shinri_bv::blast::shift::bvshl;
use crate::blast::operand::{
    to_operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits, signed_one_bits,
};
use crate::blast::normalize::const_n;
use crate::round::{exp_w, shift_right_sticky, rounding_increment};
use crate::rm::RmSel;

pub fn fp_round_to_integral(b: &mut Blaster, x: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let w = (eb + sb) as usize;
    let ox = to_operand(b, x, eb, sb);

    // f = number of fractional bits = (sb-1) - exp, saturated at 0 (already integral).
    let sbm1 = const_n(b, ew, (sb as i128) - 1);
    let f_full = shinri_bv::blast::arith::bvsub(b, &sbm1, &ox.exp); // signed
    let f_neg = f_full[ew - 1];                                     // exp > sb-1 ⇒ already integral
    let zero_ew = const_n(b, ew, 0);
    let f_sat: Vec<BitLit> = (0..ew).map(|i| b.mux2(f_neg, zero_ew[i], f_full[i])).collect();

    // GRS extraction at the integer boundary: prepend [S,R,G]=0 below sig, shift
    // right by f_sat, fold dropped bits into sticky. Mirrors round()'s Step 1.
    let mut work: Vec<BitLit> = vec![b.zero(), b.zero(), b.zero()];
    work.extend_from_slice(&ox.sig);                                // width sbu+3
    let (shifted, st) = shift_right_sticky(b, &work, &f_sat);
    let mut work = shifted;
    work[0] = b.or2(work[0], st);
    let s = work[0];
    let r = work[1];
    let g = work[2];
    let int_part: Vec<BitLit> = work[3..3 + sbu].to_vec();          // integer part, right-aligned
    let lsb = int_part[0];

    // Shared rounding increment, added at the integer LSB.
    let inc = rounding_increment(b, ox.sign, g, r, s, lsb, rm);
    let mut addend: Vec<BitLit> = vec![b.zero(); sbu];
    addend[0] = inc;
    let (int_rounded, _carry) = adder(b, &int_part, &addend, b.zero());

    // Shift the rounded integer back left by f to restore the normalized position.
    // Width sbu+1 captures the at-most-one carry into bit `sb` (value bumped to a
    // higher power of two ⇒ exp+1, significand = leading bit only).
    let mut ir_ext = int_rounded.clone();
    ir_ext.push(b.zero());                                          // sbu+1 bits
    // Resize f_sat to sbu+1 (truncate high bits / zero-extend); f < 2^(sb+1) always.
    let f_shl: Vec<BitLit> = (0..(sbu + 1)).map(|i| if i < ew { f_sat[i] } else { b.zero() }).collect();
    let shifted_back = bvshl(b, &ir_ext, &f_shl);                   // sbu+1 bits
    let overflow = shifted_back[sbu];
    let norm_sig: Vec<BitLit> = (0..sbu).map(|i| {
        let lead = if i == sbu - 1 { b.one() } else { b.zero() };   // 1.000… on carry
        b.mux2(overflow, lead, shifted_back[i])
    }).collect();
    let one_ew = const_n(b, ew, 1);
    let exp_p1 = bvadd(b, &ox.exp, &one_ew);
    let exp_out: Vec<BitLit> = (0..ew).map(|i| b.mux2(overflow, exp_p1[i], ox.exp[i])).collect();

    // Pack the normal result: trailing sig | biased exp | sign. norm_sig's hidden
    // bit (index sb-1) is always 1 here, and exp_out stays in normal range.
    let bias_v = const_n(b, ew, (1i128 << (eb - 1)) - 1);
    let biased = bvadd(b, &exp_out, &bias_v);
    let mut out: Vec<BitLit> = Vec::with_capacity(w);
    for i in 0..(sbu - 1) { out.push(norm_sig[i]); }                // trailing significand
    for i in 0..(eb as usize) { out.push(biased[i]); }             // exponent field
    out.push(ox.sign);                                             // sign

    // Special cases (low → high priority; NaN wins).
    // |x| < 1  ⇔  exp < 0  (covers subnormals and ±0). Result is sign-preserving
    // ±1 when the increment fired, else ±0.
    let is_lt1 = ox.exp[ew - 1];
    let one_bits = signed_one_bits(b, eb, sb, ox.sign);
    let zero_bits = signed_zero_bits(b, eb, sb, ox.sign);
    let lt1: Vec<BitLit> = (0..w).map(|i| b.mux2(inc, one_bits[i], zero_bits[i])).collect();
    for i in 0..w { out[i] = b.mux2(is_lt1, lt1[i], out[i]); }
    let inf = inf_pattern_bits(b, eb, sb, ox.sign);
    for i in 0..w { out[i] = b.mux2(ox.is_inf, inf[i], out[i]); }
    let nan = canon_nan_bits(b, eb, sb);
    for i in 0..w { out[i] = b.mux2(ox.is_nan, nan[i], out[i]); }
    out
}

#[cfg(test)]
mod tests {
    use crate::blast::roundint::fp_round_to_integral;
    use crate::reference::{ref_round_to_integral, RoundMode};
    use crate::rm;
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
    fn rmode(m: RoundMode) -> shinri_core::RoundingMode {
        match m {
            RoundMode::Rne => shinri_core::RoundingMode::Rne,
            RoundMode::Rna => shinri_core::RoundingMode::Rna,
            RoundMode::Rtp => shinri_core::RoundingMode::Rtp,
            RoundMode::Rtn => shinri_core::RoundingMode::Rtn,
            RoundMode::Rtz => shinri_core::RoundingMode::Rtz,
        }
    }

    const MODES: &[RoundMode] = &[RoundMode::Rne, RoundMode::Rna, RoundMode::Rtp, RoundMode::Rtn, RoundMode::Rtz];

    #[test]
    fn roundint_tiny_exhaustive() {
        // Format (3,5): 256 patterns × 5 modes, full cross-check vs the golden.
        let (eb, sb) = (3u32, 5u32);
        for bits in 0..(1u64 << (eb + sb)) {
            for &m in MODES {
                let want = ref_round_to_integral(eb, sb, &Integer::from(bits), m);
                let mut b = Blaster::new();
                let x = const_bits(&b, eb, sb, bits);
                let sel = rm::literal(&b, rmode(m));
                let got_word = fp_round_to_integral(&mut b, &x, &sel, eb, sb);
                let got = eval_word(b, &got_word);
                assert_eq!(
                    Integer::from(got), want,
                    "roundint (3,5) bits={bits:#x} mode={m:?}: got {got:#x} want {want}"
                );
            }
        }
    }

    #[test]
    fn roundint_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        let cases: &[u64] = &[
            0x0000_0000, 0x8000_0000,           // ±0
            0x7F80_0000, 0xFF80_0000,           // ±inf
            0x7FC0_0000,                        // NaN
            0x3F80_0000, 0x4000_0000,           // 1.0, 2.0 (integral)
            0x3FC0_0000, 0x4020_0000,           // 1.5, 2.5
            0x3F00_0000, 0xBF00_0000,           // ±0.5
            0x3E80_0000, 0xBE80_0000,           // ±0.25
            0x3FFF_FFFF,                        // ~1.9999998 (carry-renormalize)
            0x4B7F_FFFF, 0x4C00_0000,           // large integral magnitudes
        ];
        // Deterministic LCG for extra coverage.
        let mut state = 0x1234_5678_9abc_def0u64;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); state >> 16 };
        for iter in 0..2000 {
            let bits = if iter < cases.len() as u64 { cases[iter as usize] } else { rand() & 0xFFFF_FFFF };
            for &m in MODES {
                let want = ref_round_to_integral(eb, sb, &Integer::from(bits), m);
                let mut b = Blaster::new();
                let x = const_bits(&b, eb, sb, bits);
                let sel = rm::literal(&b, rmode(m));
                let got_word = fp_round_to_integral(&mut b, &x, &sel, eb, sb);
                let got = eval_word(b, &got_word);
                assert_eq!(
                    Integer::from(got), want,
                    "roundint f32 bits={bits:#x} mode={m:?}: got {got:#x} want {want}"
                );
            }
        }
    }
}
