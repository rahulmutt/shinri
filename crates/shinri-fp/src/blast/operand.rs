//! Shared unpacked-operand form and IEEE result-pattern builders for the FP
//! arithmetic datapaths (fp.add, fp.mul, …).

use crate::round::exp_w;
use crate::unpack::unpack;
use shinri_bv::{BitLit, Blaster};

/// Effective unbiased exponent (signed, exp_w bits) and explicit significand
/// (sb bits, hidden bit materialized) for an unpacked operand.
pub(crate) struct Operand {
    pub sign: BitLit,
    pub exp: Vec<BitLit>, // signed unbiased, exp_w
    pub sig: Vec<BitLit>, // sb bits LSB→MSB, hidden bit at index sb-1
    pub is_nan: BitLit,
    pub is_inf: BitLit,
    pub is_zero: BitLit,
}

pub(crate) fn to_operand(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Operand {
    let u = unpack(b, bits, eb, sb);
    let ew = exp_w(eb);
    let bias = (1i128 << (eb - 1)) - 1;
    // biased exp field → signed unbiased. Subnormal (exp field 0): effective
    // exponent is emin = 1 - bias, hidden bit 0; Normal: exp - bias, hidden 1.
    // Build signed exp from the eb-bit field, zero-extended, minus bias.
    let mut field: Vec<BitLit> = u.exp.clone();
    while field.len() < ew {
        field.push(b.zero());
    }
    let bias_v: Vec<BitLit> = {
        let v = bias & ((1i128 << ew) - 1);
        (0..ew)
            .map(|i| if (v >> i) & 1 == 1 { b.one() } else { b.zero() })
            .collect()
    };
    let unbiased = shinri_bv::blast::arith::bvsub(b, &field, &bias_v); // exp - bias
                                                                       // is exp field all zero? (subnormal/zero). Just test field == 0.
    let mut field_zero = b.one();
    for &e in &u.exp {
        let ne = b.not1(e);
        field_zero = b.and2(field_zero, ne);
    }
    // effective exp: if field_zero then emin else unbiased.
    let emin_v: Vec<BitLit> = {
        let v = (1 - bias) & ((1i128 << ew) - 1);
        (0..ew)
            .map(|i| if (v >> i) & 1 == 1 { b.one() } else { b.zero() })
            .collect()
    };
    let exp: Vec<BitLit> = (0..ew)
        .map(|i| b.mux2(field_zero, emin_v[i], unbiased[i]))
        .collect();
    // explicit significand: trailing (sb-1) bits, hidden bit = NOT field_zero.
    let hidden = b.not1(field_zero);
    let mut sig: Vec<BitLit> = u.sig.clone(); // sb-1 bits
    sig.push(hidden); // index sb-1 = hidden
    Operand {
        sign: u.sign,
        exp,
        sig,
        is_nan: u.is_nan,
        is_inf: u.is_inf,
        is_zero: u.is_zero,
    }
}

#[allow(clippy::needless_range_loop)] // index arithmetic bounds are load-bearing; iterator skip/take harder to verify
pub(crate) fn canon_nan_bits(b: &Blaster, eb: u32, sb: u32) -> Vec<BitLit> {
    // exp all ones; sig MSB (index sb-2) set; sign 0.
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    for i in (sb as usize - 1)..(sb as usize - 1 + eb as usize) {
        v[i] = b.one();
    } // exp
    v[sb as usize - 2] = b.one(); // sig MSB
    v
}
#[allow(clippy::needless_range_loop)] // index arithmetic bounds are load-bearing; iterator skip/take harder to verify
pub(crate) fn inf_pattern_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit> {
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    for i in (sb as usize - 1)..(sb as usize - 1 + eb as usize) {
        v[i] = b.one();
    } // exp all ones
    v[(eb + sb) as usize - 1] = sign;
    v
}
pub(crate) fn signed_zero_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit> {
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    v[(eb + sb) as usize - 1] = sign;
    v
}
#[allow(clippy::needless_range_loop)] // index arithmetic bounds are load-bearing
pub(crate) fn signed_one_bits(b: &Blaster, eb: u32, sb: u32, sign: BitLit) -> Vec<BitLit> {
    // 1.0: trailing sig 0, biased exponent = bias (2^(eb-1)-1), given sign.
    let bias: u64 = (1u64 << (eb - 1)) - 1;
    let mut v: Vec<BitLit> = (0..(eb + sb)).map(|_| b.zero()).collect();
    for i in 0..(eb as usize) {
        if (bias >> i) & 1 == 1 {
            v[(sb as usize - 1) + i] = b.one();
        }
    }
    v[(eb + sb) as usize - 1] = sign;
    v
}
