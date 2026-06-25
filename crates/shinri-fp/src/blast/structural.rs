//! Sign-only FP word ops: fp.abs (clear sign), fp.neg (flip sign).

use shinri_bv::{BitLit, Blaster};

pub fn abs(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    debug_assert_eq!(bits.len(), w);
    let mut out = bits.to_vec();
    out[w - 1] = b.zero(); // sign bit := 0
    out
}

pub fn neg(b: &mut Blaster, bits: &[BitLit], eb: u32, sb: u32) -> Vec<BitLit> {
    let w = (eb + sb) as usize;
    debug_assert_eq!(bits.len(), w);
    let mut out = bits.to_vec();
    out[w - 1] = b.not1(bits[w - 1]); // sign bit := NOT sign
    out
}
