//! Shared FP datapath normalization helpers (used by div and sqrt).

use crate::lzc::lzc;
use shinri_bv::{BitLit, Blaster};

/// Constant of width `n` (LSB→MSB) with value `v`. Total-mask guard: for `n >= 128`
/// the `1 << n` form overflows i128, so mask with all-ones instead.
pub(crate) fn const_n(b: &Blaster, n: usize, v: i128) -> Vec<BitLit> {
    let mask = if n >= 128 { -1i128 } else { (1i128 << n) - 1 };
    let u = v & mask;
    (0..n)
        .map(|i| if (u >> i) & 1 == 1 { b.one() } else { b.zero() })
        .collect()
}

pub(crate) fn zero_extend(b: &Blaster, x: &[BitLit], to: usize) -> Vec<BitLit> {
    let mut out = x.to_vec();
    while out.len() < to {
        out.push(b.zero());
    }
    out
}

/// Pre-normalize `sig` (sb bits) so its leading 1 sits at index sb-1, returning
/// (sig_norm, exp_n) with exp_n = exp - shift (signed, ew bits). For a nonzero
/// significand sig_norm lands in [2^(sb-1), 2^sb).
pub(crate) fn prenormalize(
    b: &mut Blaster,
    sig: &[BitLit],
    exp: &[BitLit],
    sbu: usize,
    ew: usize,
) -> (Vec<BitLit>, Vec<BitLit>) {
    let k = lzc(b, sig);
    let k_sb = zero_extend(b, &k, sbu);
    let sig_norm = shinri_bv::blast::shift::bvshl(b, sig, &k_sb);
    let k_ew = zero_extend(b, &k, ew);
    let exp_n = shinri_bv::blast::arith::bvsub(b, exp, &k_ew);
    (sig_norm, exp_n)
}
