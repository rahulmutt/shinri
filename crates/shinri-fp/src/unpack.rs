//! Decompose an FP bit word into sign / exponent / explicit significand / flags.

use shinri_bv::{BitLit, Blaster};

/// Unpacked FP operand. `sig` is the (sb-1)-bit trailing significand (LSB→MSB);
/// the hidden bit is implicit (1 for normal, 0 for subnormal) and recomputed by
/// consumers as needed. Flags are derived from the exponent/significand fields.
pub struct Unpacked {
    pub sign: BitLit,
    pub exp: Vec<BitLit>, // eb bits, LSB→MSB
    pub sig: Vec<BitLit>, // sb-1 bits, LSB→MSB
    pub is_nan: BitLit,
    pub is_inf: BitLit,
    pub is_zero: BitLit,
}

/// `bits` is the W=eb+sb word, LSB→MSB.
pub fn unpack(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Unpacked {
    let w = (eb + sb) as usize;
    debug_assert_eq!(bits.len(), w);
    let sign = bits[w - 1];
    let exp: Vec<BitLit> = bits[(sb as usize - 1)..(sb as usize - 1 + eb as usize)].to_vec();
    let sig: Vec<BitLit> = bits[0..(sb as usize - 1)].to_vec();

    // exp_all_ones = AND of all exp bits ; exp_all_zero = AND of all (NOT exp bits)
    let and_all = |b: &mut Blaster, lits: &[BitLit]| -> BitLit {
        let mut acc = b.one();
        for &l in lits {
            acc = b.and2(acc, l);
        }
        acc
    };
    let nor_all = |b: &mut Blaster, lits: &[BitLit]| -> BitLit {
        // true iff all lits are false
        let mut acc = b.one();
        for &l in lits {
            let nl = b.not1(l);
            acc = b.and2(acc, nl);
        }
        acc
    };
    let exp_all_ones = and_all(b, &exp);
    let exp_all_zero = nor_all(b, &exp);
    let sig_all_zero = nor_all(b, &sig);
    let sig_nonzero = b.not1(sig_all_zero);

    let is_inf = b.and2(exp_all_ones, sig_all_zero);
    let is_nan = b.and2(exp_all_ones, sig_nonzero);
    let is_zero = b.and2(exp_all_zero, sig_all_zero);

    Unpacked {
        sign,
        exp,
        sig,
        is_nan,
        is_inf,
        is_zero,
    }
}
