//! Reassemble an FP bit word from an Unpacked form, canonicalizing NaN.

use crate::unpack::Unpacked;
use shinri_bv::{BitLit, Blaster};

/// Pack sign|exp|sig back to W=eb+sb bits (LSB→MSB). If `u.is_nan` is set, emit
/// the canonical quiet NaN pattern (sign 0, exp all ones, sig MSB = 1, rest 0).
pub fn pack(b: &mut Blaster, u: &Unpacked, eb: u32, sb: u32) -> Vec<BitLit> {
    debug_assert_eq!(u.exp.len(), eb as usize);
    debug_assert_eq!(u.sig.len(), sb as usize - 1);
    let one = b.one();
    let zero = b.zero();

    // Canonical NaN fields.
    // exp: all ones ; sig: only MSB set ; sign: 0.
    let mut out: Vec<BitLit> = Vec::with_capacity((eb + sb) as usize);
    // trailing significand bits [0 .. sb-1)
    for i in 0..(sb as usize - 1) {
        // canonical NaN sig: MSB (index sb-2) = 1, others 0.
        let canon = if i == (sb as usize - 2) { one } else { zero };
        out.push(b.mux2(u.is_nan, canon, u.sig[i]));
    }
    // exponent bits
    for i in 0..(eb as usize) {
        out.push(b.mux2(u.is_nan, one, u.exp[i]));
    }
    // sign bit: 0 for canonical NaN
    out.push(b.mux2(u.is_nan, zero, u.sign));
    out
}
