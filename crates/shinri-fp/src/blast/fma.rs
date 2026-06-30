//! fp.fma datapath: exact 2·sb product → z aligned at the same scale → effective
//! add/sub → normalize → SINGLE round → special-case. Generalizes fp_add to
//! significand width 2·sb. No double rounding.

use shinri_bv::{BitLit, Blaster};
use shinri_bv::blast::arith::{adder, bvadd, bvsub};
use shinri_bv::blast::shift::bvshl;
use shinri_bv::blast::compare::{sgt, ult};
use crate::blast::operand::{to_operand, Operand, canon_nan_bits, inf_pattern_bits, signed_zero_bits};
use crate::blast::mul::significand_product;
use crate::blast::normalize::{const_n, zero_extend};
use crate::lzc::lzc;
use crate::round::{exp_w, shift_right_sticky, round, ExtFp};
use crate::rm::RmSel;

pub fn fp_fma(b: &mut Blaster, x: &[BitLit], y: &[BitLit], z: &[BitLit], rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let ew = exp_w(eb);
    let sbu = sb as usize;
    let pw = 2 * sbu;            // product / addend significand width
    let mw = pw + 3;             // mantissa width with 3 GRS columns below
    let ox = to_operand(b, x, eb, sb);
    let oy = to_operand(b, y, eb, sb);
    let oz = to_operand(b, z, eb, sb);

    // ---- Exact product (no rounding). prod_n: pw bits, leading at pw-1. ----
    let prod_sign = b.xor2(ox.sign, oy.sign);
    let (prod_n, norm_exp0) = significand_product(b, &ox, &oy, eb, sb);
    let prod_zero = b.or2(ox.is_zero, oy.is_zero);

    // ---- z as a pw-significand addend at the same scale (hidden bit at pw-1). ----
    // Build pw-bit significand for z: oz.sig in the high half, zeros below.
    // For normal z: oz.sig[sb-1]=1 → raw leading 1 already at pw-1; lz_z=0.
    // For subnormal z: leading 1 is below pw-1; we normalize by shifting left so that
    // the exponent comparison with the product (always normalized at pw-1) is correct.
    // Without normalization a subnormal z has decoded exp=emin but its significand
    // leading bit is below pw-1, so a subnormal product with a smaller exponent can
    // have larger actual magnitude yet lose the "hi" election — causing wrong results.
    // For zero z: lzc=pw, z_sig_norm=0, z_exp goes very negative (product wins tie).
    let mut z_sig_raw: Vec<BitLit> = vec![b.zero(); sbu];
    z_sig_raw.extend_from_slice(&oz.sig);
    let lz_z = lzc(b, &z_sig_raw);           // count_width(pw) bits
    let lz_z_ew = zero_extend(b, &lz_z, ew);
    let z_sig = bvshl(b, &z_sig_raw, &lz_z_ew); // normalized: leading 1 at pw-1
    let z_exp = bvsub(b, &oz.exp, &lz_z_ew);    // adjusted exponent
    let z_sign = oz.sign;

    // When the product is zero, norm_exp0 is garbage. Clamp prod_exp to z_exp so that:
    //   • the zero product correctly loses the exp comparison when z is non-zero (z_exp
    //     for subnormal z can be well below emin after normalization above, but it will
    //     still be >= the minimum z_exp in the format — and the sig tie-break prod_n=0
    //     vs z_sig correctly elects z as "hi" when z is non-zero), and
    //   • exp_diff = hi_exp − lo_exp is 0 (not a huge negative), preserving alignment
    //     correctness since the zero-product sig contributes nothing anyway.
    let prod_exp: Vec<BitLit> = (0..ew)
        .map(|i| b.mux2(prod_zero, z_exp[i], norm_exp0[i]))
        .collect();

    // ---- Magnitude-order the two pw-significand addends into hi/lo (by exp, then sig). ----
    let exp_gt = sgt(b, &prod_exp, &z_exp);
    let exp_eq = bits_equal(b, &prod_exp, &z_exp);
    let sig_ge = { let lt = ult(b, &prod_n, &z_sig); b.not1(lt) };
    let tie = b.and2(exp_eq, sig_ge);
    let p_ge_z = b.or2(exp_gt, tie);
    let (hi_sign, hi_exp, hi_sig) =
        select3(b, p_ge_z, (prod_sign, &prod_exp, &prod_n), (z_sign, &z_exp, &z_sig), ew, pw);
    let (lo_sign, lo_exp, lo_sig) =
        select3(b, p_ge_z, (z_sign, &z_exp, &z_sig), (prod_sign, &prod_exp, &prod_n), ew, pw);

    // ---- Align lo to hi: right-shift lo by (hi_exp - lo_exp), collecting sticky. ----
    let exp_diff = bvsub(b, &hi_exp, &lo_exp); // >= 0 since hi >= lo
    let zb = b.zero();
    let mut hi_ext: Vec<BitLit> = vec![zb; 3]; hi_ext.extend_from_slice(&hi_sig); // mw
    let mut lo_ext: Vec<BitLit> = vec![zb; 3]; lo_ext.extend_from_slice(&lo_sig); // mw
    let (lo_shifted, lo_sticky) = shift_right_sticky(b, &lo_ext, &exp_diff);
    let mut lo_aln = lo_shifted;
    lo_aln[0] = b.or2(lo_aln[0], lo_sticky);

    // ---- Operate: effective add if signs equal, else subtract (hi >= lo). ----
    let same_sign = { let xs = b.xor2(hi_sign, lo_sign); b.not1(xs) };
    let sum_add = bvadd(b, &hi_ext, &lo_aln);
    let sum_sub = bvsub(b, &hi_ext, &lo_aln);
    let mant: Vec<BitLit> = (0..mw).map(|i| b.mux2(same_sign, sum_add[i], sum_sub[i])).collect();
    let add_carry = { let (_s, c) = adder(b, &hi_ext, &lo_aln, b.zero()); b.and2(same_sign, c) };

    // Exact-zero finite result (full cancellation, incl. both addends zero).
    let cancel_zero = {
        let mut az = b.one();
        for &m in &mant { let nm = b.not1(m); az = b.and2(az, nm); }
        let nc = b.not1(add_carry);
        b.and2(az, nc)
    };
    let res_sign = hi_sign;
    let base_exp = hi_exp.clone();

    // ---- Normalize. Case A (add carry): >>1, exp+1. Case B: LZC left-shift. ----
    let mut mant_a: Vec<BitLit> = Vec::with_capacity(mw);
    for i in 0..mw { let hb = if i + 1 < mw { mant[i + 1] } else { add_carry }; mant_a.push(hb); }
    mant_a[0] = b.or2(mant_a[0], mant[0]); // preserve dropped sticky on >>1
    let one_ew = const_n(b, ew, 1);
    let exp_a = bvadd(b, &base_exp, &one_ew);
    let lz = lzc(b, &mant);                 // count_width(mw) bits
    let lz_ew = zero_extend(b, &lz, ew);
    let mant_b = bvshl(b, &mant, &lz_ew);
    let exp_b = bvsub(b, &base_exp, &lz_ew);
    let mant_n: Vec<BitLit> = (0..mw).map(|i| b.mux2(add_carry, mant_a[i], mant_b[i])).collect();
    let exp_n: Vec<BitLit> = (0..ew).map(|i| b.mux2(add_carry, exp_a[i], exp_b[i])).collect();

    // ---- Single round: top sb bits as significand; (G,R,S) = mul-style. ----
    // Leading bit at index mw-1; top sb bits = mant_n[mw-sb .. mw].
    let sig: Vec<BitLit> = mant_n[(mw - sbu)..mw].to_vec();
    let g = mant_n[mw - sbu - 1];
    // mw = 2*sbu+3 ⇒ mw-sbu-2 = sbu+1 >= 2 always, so this index never underflows.
    let r = mant_n[mw - sbu - 2];
    let mut s = b.zero();
    for bit in mant_n.iter().take(mw - sbu - 2) { s = b.or2(s, *bit); }
    let ext = ExtFp { sign: res_sign, exp: exp_n, sig, grs: (g, r, s) };
    let rounded = round(b, ext, eb, sb, rm);

    // ---- Special-case mux (priority NaN > Inf > cancel-zero > normal). ----
    special_case(b, &rounded, &ox, &oy, &oz, prod_sign, cancel_zero, rm, eb, sb)
}

fn bits_equal(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    let mut acc = b.one();
    for i in 0..x.len() { let d = b.xor2(x[i], y[i]); let s = b.not1(d); acc = b.and2(acc, s); }
    acc
}

/// Field-select a (sign, exp, sig) triple: `sel` ? a : c. `exp` width ew, `sig` width pw.
fn select3(b: &mut Blaster, sel: BitLit,
           a: (BitLit, &[BitLit], &[BitLit]), c: (BitLit, &[BitLit], &[BitLit]),
           ew: usize, pw: usize) -> (BitLit, Vec<BitLit>, Vec<BitLit>) {
    let sign = b.mux2(sel, a.0, c.0);
    let exp = (0..ew).map(|i| b.mux2(sel, a.1[i], c.1[i])).collect();
    let sig = (0..pw).map(|i| b.mux2(sel, a.2[i], c.2[i])).collect();
    (sign, exp, sig)
}

/// IEEE fp.fma special cases override the datapath result.
#[allow(clippy::too_many_arguments)]
fn special_case(b: &mut Blaster, normal: &[BitLit], ox: &Operand, oy: &Operand, oz: &Operand,
                prod_sign: BitLit, cancel_zero: BitLit, rm: &RmSel, eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    let nan = canon_nan_bits(b, eb, sb);
    // Invalid product 0·∞ (either order).
    let invalid = {
        let a = b.and2(ox.is_zero, oy.is_inf);
        let c = b.and2(ox.is_inf, oy.is_zero);
        b.or2(a, c)
    };
    let any_nan = { let t = b.or2(ox.is_nan, oy.is_nan); b.or2(t, oz.is_nan) };
    // prod_inf = (x or y inf) and not invalid.
    let any_xy_inf = b.or2(ox.is_inf, oy.is_inf);
    let not_invalid = b.not1(invalid);
    let prod_inf = b.and2(any_xy_inf, not_invalid);
    // ∞ + (∓∞): product ∞ and z ∞ with opposite sign.
    let inf_sign_clash = {
        let opp = b.xor2(prod_sign, oz.sign);
        let both = b.and2(prod_inf, oz.is_inf);
        b.and2(both, opp)
    };
    let want_nan = { let t = b.or2(any_nan, invalid); b.or2(t, inf_sign_clash) };
    // Inf result: product ∞ (sign = prod_sign) or z ∞ (sign = z.sign).
    let any_inf = b.or2(prod_inf, oz.is_inf);
    let inf_sign = b.mux2(prod_inf, prod_sign, oz.sign);
    let inf_bits = inf_pattern_bits(b, eb, sb, inf_sign);
    // Exact-zero sum sign rule (IEEE 754 §6.3 corrected):
    // -0 iff (prod_sign ∧ z.sign) ∨ ((prod_sign ≠ z.sign) ∧ RTN).
    // The RTN override applies ONLY when the two addends have OPPOSITE signs.
    let both_neg = b.and2(prod_sign, oz.sign);
    let rtn = rm.sel[3];
    let opp_sign = b.xor2(prod_sign, oz.sign);
    let opp_rtn = b.and2(opp_sign, rtn);
    let zero_neg = b.or2(both_neg, opp_rtn);
    let zero_bits = signed_zero_bits(b, eb, sb, zero_neg);

    let mut out = normal.to_vec();
    for i in 0..w { out[i] = b.mux2(cancel_zero, zero_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(any_inf, inf_bits[i], out[i]); }
    for i in 0..w { out[i] = b.mux2(want_nan, nan[i], out[i]); }
    out
}

#[cfg(test)]
mod tests {
    use crate::blast::fma::fp_fma;
    use crate::reference::{ref_fma, RoundMode};
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

    fn check(eb: u32, sb: u32, a: u64, b2: u64, c: u64, m: RoundMode) {
        let want = ref_fma(eb, sb, &Integer::from(a), &Integer::from(b2), &Integer::from(c), m);
        let mut bl = Blaster::new();
        let xv = const_bits(&bl, eb, sb, a);
        let yv = const_bits(&bl, eb, sb, b2);
        let zv = const_bits(&bl, eb, sb, c);
        let sel = rm::literal(&bl, rmode(m));
        let word = fp_fma(&mut bl, &xv, &yv, &zv, &sel, eb, sb);
        assert_eq!(Integer::from(eval_word(bl, &word)), want,
            "fp.fma a={a:#x} b={b2:#x} c={c:#x} m={m:?}");
    }

    #[test]
    fn fp_fma_tiny_sampled_all_modes() {
        // Format (3,5): full triple space is 256^3 (too large to enumerate), so
        // cross-product a curated set of "interesting" patterns and add random
        // triples. Each tiny-format SAT solve is pure constant propagation (fast).
        let (eb, sb) = (3u32, 5u32);
        // Layout: sign(bit7) | exp(bits4-6) | trailing-sig(bits0-3). bias=3.
        // ±0, ±inf, NaN, ±1.0, ±2.0, ±0.5, smallest subnormal, max normal.
        let pats: &[u64] = &[
            0x00, 0x80,             // ±0
            0x70, 0xF0,             // ±inf  (exp=0b111, trailing 0)
            0x78,                   // NaN   (exp=0b111, trailing nonzero)
            0x30, 0xB0,             // ±1.0  (exp field = bias = 3)
            0x40, 0xC0,             // ±2.0  (exp field 4)
            0x20, 0xA0,             // ±0.5  (exp field 2)
            0x01, 0x81,             // ± smallest subnormal (exp 0, trailing 1)
            0x6F, 0xEF,             // ± max normal (exp 6, trailing 0xF)
        ];
        for &a in pats {
            for &bb in pats {
                for &c in pats {
                    for &m in MODES { check(eb, sb, a, bb, c, m); }
                }
            }
        }
        // Random triples over the full 8-bit space.
        let mut state = 0xFEED_F00D_1234_5678u64;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); (state >> 24) & 0xFF };
        for _ in 0..600 {
            let (a, bb, c) = (rand(), rand(), rand());
            for &m in MODES { check(eb, sb, a, bb, c, m); }
        }
    }

    #[test]
    fn fp_fma_float32_specials_and_random() {
        let (eb, sb) = (8u32, 24u32);
        // Curated triples incl. the single-rounding witness and specials.
        let curated: &[(u64, u64, u64)] = &[
            (0x4000_0000, 0x4040_0000, 0x3F80_0000),   // 2*3+1 = 7
            (0x3F80_0001, 0x3F80_0001, 0xBF80_0002),   // single-rounding witness -> 2^-46
            (0x3F80_0000, 0x3F80_0000, 0xBF80_0000),   // 1*1-1 = 0
            (0x7FC0_0000, 0x3F80_0000, 0x3F80_0000),   // NaN propagation
            (0x0000_0000, 0x7F80_0000, 0x3F80_0000),   // 0*inf -> NaN
            (0x7F80_0000, 0x3F80_0000, 0xFF80_0000),   // +inf + (-inf) -> NaN
            (0x7F80_0000, 0x4000_0000, 0x3F80_0000),   // +inf product, finite z -> +inf
            (0x3F80_0000, 0x3F80_0000, 0x7F80_0000),   // finite product, z=+inf -> +inf
            (0x0080_0000, 0x0080_0000, 0x0000_0001),   // subnormal-scale product + tiny z
        ];
        // SEED LITERAL FIX: 0x0FMA_5EED is not valid hex; use 0x0F_A5_EE_D0 instead.
        let mut state = 0x0F_A5_EE_D0_u64 ^ 0x1234_5678;
        let mut rand = || { state = state.wrapping_mul(6364136223846793005).wrapping_add(1); (state >> 16) & 0xFFFF_FFFF };
        for iter in 0..500u64 {
            let (a, bb, c) = if (iter as usize) < curated.len() {
                curated[iter as usize]
            } else {
                (rand(), rand(), rand())
            };
            for &m in MODES { check(eb, sb, a, bb, c, m); }
        }
    }
}
