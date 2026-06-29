//! fp.eq and NaN-aware core `=` over two FP bit words.

use shinri_bv::{BitLit, Blaster};
use crate::unpack::unpack;

/// Bitwise equality of two equal-length words.
fn bits_eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    debug_assert_eq!(x.len(), y.len());
    let mut acc = b.one();
    for i in 0..x.len() {
        let xn = b.xor2(x[i], y[i]);   // 1 if differ
        let same = b.not1(xn);
        acc = b.and2(acc, same);
    }
    acc
}

/// IEEE `fp.eq`: false if either is NaN; +0 == -0; else bit-equal among finite/inf.
/// Since +0 and -0 differ only in the sign bit and all-other-bits-zero, comparing
/// the magnitude (all bits except sign) handles zeros, BUT two different non-zero
/// values with equal magnitude and opposite sign (e.g. +1 vs -1) must compare
/// UNEQUAL. So: equal iff (both zero) OR (not NaN AND full-bit-equal).
pub fn fp_eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let neither_nan = {
        let nx = b.not1(ux.is_nan);
        let ny = b.not1(uy.is_nan);
        b.and2(nx, ny)
    };
    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let full_eq = bits_eq(b, x, y);
    let finite_eq = b.and2(neither_nan, full_eq);
    // (both_zero) OR (neither_nan AND full_eq); both_zero already implies neither_nan.
    let eq = b.or2(both_zero, finite_eq);
    // ensure NaN forces false even if full_eq held (NaN==NaN bit-equal): mask by neither_nan.
    b.and2(eq, neither_nan)
}

/// Theory core `=`: NaN == NaN (any NaN payloads), +0 != -0, else bit-equal.
pub fn core_eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let both_nan = b.and2(ux.is_nan, uy.is_nan);
    let neither_nan = {
        let nx = b.not1(ux.is_nan);
        let ny = b.not1(uy.is_nan);
        b.and2(nx, ny)
    };
    let full_eq = bits_eq(b, x, y);
    let finite_eq = b.and2(neither_nan, full_eq);
    b.or2(both_nan, finite_eq)
}

/// Unsigned `x < y` over equal-width LSB→MSB bit vectors. Rippled low→high so
/// the most-significant bit dominates.
fn ult(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    debug_assert_eq!(x.len(), y.len());
    let mut lt = b.zero();
    for i in 0..x.len() {
        let nx = b.not1(x[i]);
        let bit_lt = b.and2(nx, y[i]);          // x_i=0, y_i=1
        let xn = b.xor2(x[i], y[i]);
        let bit_eq = b.not1(xn);
        let keep = b.and2(bit_eq, lt);
        lt = b.or2(bit_lt, keep);               // higher bit wins
    }
    lt
}

/// IEEE `fp.lt`: NaN on either side -> false; +0 == -0; else real order.
/// Magnitude is `[sig ++ exp]` (LSB→MSB) so exp outranks sig and ±inf falls out
/// as the extreme magnitude.
pub fn fp_lt(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);

    let mut mag_x = ux.sig.clone();
    mag_x.extend_from_slice(&ux.exp);
    let mut mag_y = uy.sig.clone();
    mag_y.extend_from_slice(&uy.exp);
    let mlt = ult(b, &mag_x, &mag_y);          // |x| < |y|
    let mgt = ult(b, &mag_y, &mag_x);          // |x| > |y|

    let signs_diff = b.xor2(ux.sign, uy.sign);
    let signs_same = b.not1(signs_diff);
    // signs differ: x < y iff x is the negative one.
    let diff_case = b.and2(signs_diff, ux.sign);
    // both >= 0: |x| < |y|.
    let not_sx = b.not1(ux.sign);
    let pos_branch = b.and2(not_sx, mlt);
    // both < 0: |x| > |y|.
    let neg_branch = b.and2(ux.sign, mgt);
    let same_inner = b.or2(pos_branch, neg_branch);
    let same_case = b.and2(signs_same, same_inner);

    let raw = b.or2(diff_case, same_case);

    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let not_both_zero = b.not1(both_zero);
    let nx = b.not1(ux.is_nan);
    let ny = b.not1(uy.is_nan);
    let neither_nan = b.and2(nx, ny);

    let t1 = b.and2(raw, not_both_zero);
    b.and2(t1, neither_nan)
}

pub fn fp_leq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let lt = fp_lt(b, x, y, eb, sb);
    let eq = fp_eq(b, x, y, eb, sb);
    b.or2(lt, eq)
}

pub fn fp_gt(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    fp_lt(b, y, x, eb, sb)
}

pub fn fp_geq(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> BitLit {
    let gt = fp_lt(b, y, x, eb, sb);
    let eq = fp_eq(b, x, y, eb, sb);
    b.or2(gt, eq)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::structural::{abs, neg};
    use crate::reference::{decode, ref_abs, ref_core_eq, ref_fp_eq, ref_neg};
    use shinri_num::Integer;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn const_bits(b: &Blaster, eb: u32, sb: u32, value: u64) -> Vec<BitLit> {
        (0..(eb + sb)).map(|i| if (value >> i) & 1 == 1 { b.one() } else { b.zero() }).collect()
    }
    fn eval_lit(b: Blaster, lit: BitLit) -> bool {
        let cnf = b.finish();
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..cnf.num_vars { s.new_var(); }
        for c in &cnf.clauses {
            let ls: Vec<Lit> = c.iter().map(|bl| Lit::new(Var::new(bl.var), bl.pos)).collect();
            s.add_clause(&ls);
        }
        assert_eq!(s.solve(), SolveResult::Sat);
        let raw = s.value_of(Var::new(lit.var)).unwrap();
        if lit.pos { raw } else { !raw }
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
    fn abs_neg_words_match_reference() {
        let (eb, sb) = (8, 24);
        for v in [0x3F80_0000u64, 0xBF80_0000, 0x7FC0_0000, 0x8000_0000] {
            let mut b = Blaster::new();
            let bits = const_bits(&b, eb, sb, v);
            let a = abs(&mut b, &bits, eb, sb);
            assert_eq!(eval_word(b, &a), ref_abs(eb, sb, &Integer::from(v)).to_i128().unwrap() as u64);
            let mut b2 = Blaster::new();
            let bits2 = const_bits(&b2, eb, sb, v);
            let n = neg(&mut b2, &bits2, eb, sb);
            assert_eq!(eval_word(b2, &n), ref_neg(eb, sb, &Integer::from(v)).to_i128().unwrap() as u64);
        }
    }

    #[test]
    fn fp_eq_and_core_eq_match_reference() {
        let (eb, sb) = (8, 24);
        let cases = [
            (0x0000_0000u64, 0x8000_0000u64), // +0 vs -0
            (0x7FC0_0000, 0x7FC0_0000),       // NaN vs NaN
            (0x7F80_0001, 0x7FC0_0000),       // sNaN vs qNaN (both NaN)
            (0x3F80_0000, 0x3F80_0000),       // 1.0 vs 1.0
            (0x3F80_0000, 0x4000_0000),       // 1.0 vs 2.0
        ];
        for (x, y) in cases {
            let mut b = Blaster::new();
            let xb = const_bits(&b, eb, sb, x);
            let yb = const_bits(&b, eb, sb, y);
            let lit = fp_eq(&mut b, &xb, &yb, eb, sb);
            let want = ref_fp_eq(&decode(eb, sb, &Integer::from(x)), &decode(eb, sb, &Integer::from(y)));
            assert_eq!(eval_lit(b, lit), want, "fp_eq({x:#x},{y:#x})");

            let mut b2 = Blaster::new();
            let xb2 = const_bits(&b2, eb, sb, x);
            let yb2 = const_bits(&b2, eb, sb, y);
            let lit2 = core_eq(&mut b2, &xb2, &yb2, eb, sb);
            let want2 = ref_core_eq(eb, sb, &Integer::from(x), &Integer::from(y));
            assert_eq!(eval_lit(b2, lit2), want2, "core_eq({x:#x},{y:#x})");
        }
    }

    #[test]
    fn fp_lt_and_relations_match_reference() {
        use crate::reference::{ref_geq, ref_gt, ref_leq, ref_lt};
        let (eb, sb) = (8, 24);
        let pats = [
            0x3F80_0000u64, 0xBF80_0000, 0x4000_0000, 0xC000_0000,
            0x0000_0000, 0x8000_0000, 0x7F80_0000, 0xFF80_0000,
            0x7FC0_0000, 0xFFC0_0000, 0x0000_0001,
        ];
        for &x in &pats {
            for &y in &pats {
                for (name, blast, reff) in [
                    ("lt", fp_lt as fn(&mut Blaster, &[BitLit], &[BitLit], u32, u32) -> BitLit,
                     ref_lt as fn(u32, u32, &Integer, &Integer) -> bool),
                    ("leq", fp_leq, ref_leq),
                    ("gt", fp_gt, ref_gt),
                    ("geq", fp_geq, ref_geq),
                ] {
                    let mut b = Blaster::new();
                    let xb = const_bits(&b, eb, sb, x);
                    let yb = const_bits(&b, eb, sb, y);
                    let lit = blast(&mut b, &xb, &yb, eb, sb);
                    let got = eval_lit(b, lit);
                    let want = reff(eb, sb, &Integer::from(x), &Integer::from(y));
                    assert_eq!(got, want, "fp.{name}({x:#x},{y:#x})");
                }
            }
        }
    }
}
