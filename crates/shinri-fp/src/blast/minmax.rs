//! fp.min / fp.max: NaN-passthrough selectors with a ±0 tie resolved by a shared choice bit (amendment A).

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

/// The ±0 tie result: `+0` when the order's choice bit is true, else `−0`.
/// `x_sign` selects the order: `x = +0` uses `tie_pn`, `x = −0` uses `tie_np`.
/// SMT-LIB leaves the tie unspecified; the bits are shared per format and
/// order by the caller, so the operator stays a function (amendment A).
fn tie_word(
    b: &mut Blaster,
    x_sign: BitLit,
    tie_pn: BitLit,
    tie_np: BitLit,
    eb: u32,
    sb: u32,
) -> Vec<BitLit> {
    let choose_pos = b.mux2(x_sign, tie_np, tie_pn);
    let mut w = zero_word(b, eb, sb, false);
    let last = w.len() - 1;
    w[last] = b.not1(choose_pos);
    w
}

/// `fp.min`: `minNum` semantics. NaN passes through to the other operand;
/// the (+0,-0) tie resolves to the shared choice bit for its argument order.
pub fn fp_min(
    b: &mut Blaster,
    x: &[BitLit],
    y: &[BitLit],
    eb: u32,
    sb: u32,
    tie_pn: BitLit,
    tie_np: BitLit,
) -> Vec<BitLit> {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let lt = fp_lt(b, x, y, eb, sb);
    let pick = mux_word(b, lt, x, y); // lt ? x : y (ties keep y)

    let opp = b.xor2(ux.sign, uy.sign);
    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let zero_tie = b.and2(both_zero, opp);
    let tie = tie_word(b, ux.sign, tie_pn, tie_np, eb, sb);
    let pick = mux_word(b, zero_tie, &tie, &pick);

    let r = mux_word(b, uy.is_nan, x, &pick); // y NaN -> x
    mux_word(b, ux.is_nan, y, &r) // x NaN -> y (outermost)
}

/// `fp.max`: symmetric to `fp_min`; the (+0,-0) tie resolves to the shared choice bit.
pub fn fp_max(
    b: &mut Blaster,
    x: &[BitLit],
    y: &[BitLit],
    eb: u32,
    sb: u32,
    tie_pn: BitLit,
    tie_np: BitLit,
) -> Vec<BitLit> {
    let ux = unpack(b, x, eb, sb);
    let uy = unpack(b, y, eb, sb);
    let lt = fp_lt(b, x, y, eb, sb);
    let pick = mux_word(b, lt, y, x); // lt ? y : x (larger)

    let opp = b.xor2(ux.sign, uy.sign);
    let both_zero = b.and2(ux.is_zero, uy.is_zero);
    let zero_tie = b.and2(both_zero, opp);
    let tie = tie_word(b, ux.sign, tie_pn, tie_np, eb, sb);
    let pick = mux_word(b, zero_tie, &tie, &pick);

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
                let w = {
                    let z = b.zero();
                    fp_min(&mut b, &xb, &yb, eb, sb, z, z)
                };
                let got = eval_word(b, &w);
                let want = ref_min(eb, sb, &Integer::from(x), &Integer::from(y))
                    .to_i128()
                    .unwrap() as u64;
                assert_eq!(got, want, "fp.min({x:#x},{y:#x})");

                let mut b2 = Blaster::new();
                let xb2 = const_bits(&b2, eb, sb, x);
                let yb2 = const_bits(&b2, eb, sb, y);
                let w2 = {
                    let o = b2.one();
                    fp_max(&mut b2, &xb2, &yb2, eb, sb, o, o)
                };
                let got2 = eval_word(b2, &w2);
                let want2 = ref_max(eb, sb, &Integer::from(x), &Integer::from(y))
                    .to_i128()
                    .unwrap() as u64;
                assert_eq!(got2, want2, "fp.max({x:#x},{y:#x})");
            }
        }
    }

    /// Amendment A (spec §3.5.1): a ±0 tie returns the choice bit for its
    /// argument order — true ⇒ +0, false ⇒ −0 — for both fp.min and fp.max.
    #[test]
    fn zero_tie_follows_choice_bit() {
        let (eb, sb) = (8, 24);
        let (pz, nz) = (0x0000_0000u64, 0x8000_0000u64);
        for (x, y, is_pn) in [(pz, nz, true), (nz, pz, false)] {
            for choose_pos in [false, true] {
                for is_max in [false, true] {
                    let mut b = Blaster::new();
                    let xb = const_bits(&b, eb, sb, x);
                    let yb = const_bits(&b, eb, sb, y);
                    let (c, other) = if choose_pos {
                        (b.one(), b.zero())
                    } else {
                        (b.zero(), b.one())
                    };
                    let (pn, np) = if is_pn { (c, other) } else { (other, c) };
                    let w = if is_max {
                        fp_max(&mut b, &xb, &yb, eb, sb, pn, np)
                    } else {
                        fp_min(&mut b, &xb, &yb, eb, sb, pn, np)
                    };
                    let want = if choose_pos { pz } else { nz };
                    assert_eq!(
                        eval_word(b, &w),
                        want,
                        "max={is_max} x={x:#x} y={y:#x} choose_pos={choose_pos}"
                    );
                }
            }
        }
    }
}
