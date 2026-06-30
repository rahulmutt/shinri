//! fp.rem datapath: exact IEEE remainder via a narrow fmod reduction loop +
//! round-to-nearest-even correction. Mode-independent; no rounder on the result.

use shinri_bv::{BitLit, Blaster};
use shinri_bv::blast::arith::{bvadd, bvsub};
use shinri_bv::blast::shift::bvshl;
use shinri_bv::blast::compare::{eq as bv_eq, uge, ult};
use crate::blast::operand::{to_operand, canon_nan_bits, signed_zero_bits};
use crate::blast::normalize::{const_n, zero_extend, prenormalize};
use crate::lzc::lzc;
use crate::round::{exp_w, round, shift_right_sticky, ExtFp};

/// IEEE-754 `fp.rem x y` — the remainder. Mode-independent and exact:
/// r = x − y·n with n = roundTiesToEven(x/y) as an exact integer; |r| ≤ |y|/2.
#[allow(clippy::needless_range_loop)] // per-bit special-case muxes index several
                                      // load-bearing words (out/x/zsign/nan) in lockstep
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
    let zero_bit0 = b.zero();
    let p: BitLit = b.mux2(ed_neg, zero_bit0, p_ge0);    // floored parity (0 when ed<0)
    let r_zero = b.mux2(ed_neg, zero_bit0, r_zero);      // ed<0 => |x|>0 => nonzero

    // --- round-to-even correction: compare 2*rfmod vs |y| ---------------------
    // dd = ey - rexp in {0,1} whenever correction matters; build |y| and 2*rfmod
    // in a shared sb+2-bit field anchored so the compare is exact.
    let dd = bvsub(b, &ey, &rexp);                      // >= 0 where it matters
    // 2*rsig in sb+2 bits:
    let mut two_rsig = vec![b.zero()];
    two_rsig.extend_from_slice(&rsig);                  // rsig << 1, width sb+1
    two_rsig.push(b.zero());                            // width sb+2
    // shift right by dd (small), folding dropped bits into sticky.
    let dd_w = zero_extend(b, &dd, sbu + 2);
    let (rf2_shr, rf2_sticky) = shift_right_sticky(b, &two_rsig, &dd_w);
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
    let my_e = zero_extend(b, &my, sbu + 1);
    let dd_e = zero_extend(b, &dd, sbu + 1);
    let my_shf = bvshl(b, &my_e, &dd_e);
    let rsig_e = zero_extend(b, &rsig, sbu + 1);
    let diff = bvsub(b, &my_shf, &rsig_e);             // |y|-rfmod at scale 2^(rexp-(sb-1))
    // normalize diff:
    let diff_top = diff[..sbu + 1].to_vec();
    let kd = lzc(b, &diff_top);
    let kd_w = zero_extend(b, &kd, sbu + 1);
    let diff_n = bvshl(b, &diff, &kd_w);
    let diff_sig: Vec<BitLit> = diff_n[1..sbu + 1].to_vec(); // top sb bits, hidden at sb-1
    let kd_ew = zero_extend(b, &kd, ew);
    // exponent of |y|-rfmod: rexp + 1 - kd.
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
