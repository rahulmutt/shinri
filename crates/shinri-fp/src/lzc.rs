//! Leading-zero counter over a significand (LSB→MSB input), used by normalize.

use shinri_bv::{BitLit, Blaster};

/// Minimum number of bits to hold the value `n` (so `count_width(8) == 4`,
/// since lzc of an 8-bit word ranges 0..=8).
pub fn count_width(n: usize) -> usize {
    let mut w = 1usize;
    while (1usize << w) <= n {
        w += 1;
    }
    w
}

/// Count leading zeros of `bits` (LSB→MSB). Walk MSB→LSB; while every bit seen
/// so far has been zero, each further zero increments the count. Result is an
/// unsigned LSB→MSB count word of width `count_width(bits.len())`, value in 0..=n.
pub fn lzc(b: &mut Blaster, bits: &[BitLit]) -> Vec<BitLit> {
    let n = bits.len();
    let cw = count_width(n);
    let zero = b.zero();
    let mut count: Vec<BitLit> = vec![zero; cw];
    let mut still_zero = b.one();
    for i in (0..n).rev() {
        let is_zero = b.not1(bits[i]);
        let inc = b.and2(still_zero, is_zero); // add 1 this position?
                                               // count += inc  (inline ripple-add: inc is bit 0 of a cw-bit addend, rest zero)
                                               // addend = [inc, 0, 0, ...] with carry-in = 0
        let cin = b.zero();
        let (s0, c0) = b.full_adder(count[0], inc, cin);
        count[0] = s0;
        let mut carry = c0;
        for bit in count[1..].iter_mut() {
            let (s, c) = b.full_adder(*bit, zero, carry);
            *bit = s;
            carry = c;
        }
        still_zero = b.and2(still_zero, is_zero);
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

    fn const_bits(b: &Blaster, width: usize, value: u64) -> Vec<BitLit> {
        (0..width)
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

    fn expected_lzc(width: usize, value: u64) -> u64 {
        // count zero bits from MSB (index width-1) downward until first 1.
        let mut c = 0u64;
        for i in (0..width).rev() {
            if (value >> i) & 1 == 1 {
                break;
            }
            c += 1;
        }
        c
    }

    #[test]
    fn lzc_exhaustive_width8() {
        let width = 8usize;
        for v in 0u64..256 {
            let mut b = Blaster::new();
            let bits = const_bits(&b, width, v);
            let cnt = lzc(&mut b, &bits);
            assert_eq!(eval_word(b, &cnt), expected_lzc(width, v), "lzc({v:#x})");
        }
    }

    #[test]
    fn lzc_exhaustive_width5() {
        let width = 5usize;
        for v in 0u64..32 {
            let mut b = Blaster::new();
            let bits = const_bits(&b, width, v);
            let cnt = lzc(&mut b, &bits);
            assert_eq!(eval_word(b, &cnt), expected_lzc(width, v), "lzc5({v:#x})");
        }
    }
}
