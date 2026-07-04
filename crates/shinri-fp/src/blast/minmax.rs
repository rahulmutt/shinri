//! fp.min / fp.max: NaN-passthrough selectors with a sign-canonical ±0 rule.

use crate::blast::compare::fp_lt;
use crate::unpack::unpack;
use shinri_bv::{BitLit, Blaster};

/// Per-bit select: `sel ? a : c`, returning a fresh word.
fn mux_word(b: &mut Blaster, sel: BitLit, a: &[BitLit], c: &[BitLit]) -> Vec<BitLit> {
    debug_assert_eq!(a.len(), c.len());
    (0..a.len()).map(|i| b.mux2(sel, a[i], c[i])).collect()
}

/// Constant ±0 word (all zero, MSB sign bit set iff `neg`), LSB→MSB.
fn zero_word(b: &Blaster, eb: u32, sb: u32, neg: bool) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    (0..w)
        .map(|i| if neg && i == w - 1 { b.one() } else { b.zero() })
        .collect()
}

/// `fp.min`: `minNum` semantics. NaN passes through to the other operand;
/// the (+0,-0) tie resolves to -0 (sign-canonical, order-independent).
pub fn fp_min(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit> {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let lt = fp_lt(b, x, y, eb, sb);
    let pick = mux_word(b, lt, x, y); // lt ? x : y (ties keep y)

    let opp = b.xor2(ux.sign, uy.sign);
    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let zero_tie = b.and2(both_zero, opp);
    let neg_zero = zero_word(b, eb, sb, true);
    let pick = mux_word(b, zero_tie, &neg_zero, &pick);

    let r = mux_word(b, uy.is_nan, x, &pick); // y NaN -> x
    mux_word(b, ux.is_nan, y, &r) // x NaN -> y (outermost)
}

/// `fp.max`: symmetric to `fp_min`; the (+0,-0) tie resolves to +0.
pub fn fp_max(b: &mut Blaster, x: &[BitLit], y: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit> {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let lt = fp_lt(b, x, y, eb, sb);
    let pick = mux_word(b, lt, y, x); // lt ? y : x (larger)

    let opp = b.xor2(ux.sign, uy.sign);
    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let zero_tie = b.and2(both_zero, opp);
    let pos_zero = zero_word(b, eb, sb, false);
    let pick = mux_word(b, zero_tie, &pos_zero, &pick);

    let r = mux_word(b, uy.is_nan, x, &pick);
    mux_word(b, ux.is_nan, y, &r)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::reference::{ref_max, ref_min};
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

    #[test]
    fn min_max_words_match_reference() {
        let (eb, sb) = (8, 24);
        let pats = [
            0x3F80_0000u64,
            0xBF80_0000,
            0x4000_0000,
            0xC000_0000,
            0x0000_0000,
            0x8000_0000,
            0x7F80_0000,
            0xFF80_0000,
            0x7FC0_0000,
            0xFFC0_0000,
            0x0000_0001,
        ];
        for &x in &pats {
            for &y in &pats {
                let mut b = Blaster::new();
                let xb = const_bits(&b, eb, sb, x);
                let yb = const_bits(&b, eb, sb, y);
                let w = fp_min(&mut b, &xb, &yb, eb, sb);
                let got = eval_word(b, &w);
                let want = ref_min(eb, sb, &Integer::from(x), &Integer::from(y))
                    .to_i128()
                    .unwrap() as u64;
                assert_eq!(got, want, "fp.min({x:#x},{y:#x})");

                let mut b2 = Blaster::new();
                let xb2 = const_bits(&b2, eb, sb, x);
                let yb2 = const_bits(&b2, eb, sb, y);
                let w2 = fp_max(&mut b2, &xb2, &yb2, eb, sb);
                let got2 = eval_word(b2, &w2);
                let want2 = ref_max(eb, sb, &Integer::from(x), &Integer::from(y))
                    .to_i128()
                    .unwrap() as u64;
                assert_eq!(got2, want2, "fp.max({x:#x},{y:#x})");
            }
        }
    }
}
