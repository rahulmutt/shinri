//! Model extraction for BV: pack a bit-vector from SAT assignment bits.

use shinri_num::Integer;

/// Pack `width` SAT assignment booleans (LSB→MSB order) into an `Integer`.
///
/// Bit index `i` has value `2^i` when true.  `bits.len()` must equal `width`.
/// Width-general: works for any bitvector width, including >64.
pub fn pack(width: u32, bits: &[bool]) -> Integer {
    debug_assert_eq!(
        bits.len(),
        width as usize,
        "pack: bits.len()={} != width={}",
        bits.len(),
        width
    );
    // Accumulate in 64-bit chunks, then combine chunks with multiplication.
    // Process bits in groups of up to 64.
    let mut result = Integer::zero();
    // Track the current power-of-2 multiplier for the start of each chunk.
    // chunk_base = 2^(chunk_idx * 64)
    let mut chunk_base = Integer::one();
    let two_64 = Integer::from(1u64 << 32) * Integer::from(1u64 << 32); // 2^64

    let mut i = 0usize;
    while i < bits.len() {
        let end = (i + 64).min(bits.len());
        // Pack up to 64 bits into a u64.
        let mut chunk_val: u64 = 0;
        for j in i..end {
            if bits[j] {
                chunk_val |= 1u64 << (j - i);
            }
        }
        if chunk_val != 0 {
            result = result + chunk_base.clone() * Integer::from(chunk_val);
        }
        i = end;
        if i < bits.len() {
            chunk_base = chunk_base * two_64.clone();
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pack_zero() {
        let bits = vec![false; 8];
        let v = pack(8, &bits);
        assert_eq!(v, Integer::zero());
    }

    #[test]
    fn pack_five() {
        // 5 = 0b00000101: bit0=1, bit1=0, bit2=1, rest=0
        let bits = vec![true, false, true, false, false, false, false, false];
        let v = pack(8, &bits);
        assert_eq!(v, Integer::from(5u64));
    }

    #[test]
    fn pack_two_hundred() {
        // 200 = 0b11001000: bit3=1, bit6=1, bit7=1
        let bits = vec![false, false, false, true, false, false, true, true];
        let v = pack(8, &bits);
        assert_eq!(v, Integer::from(200u64));
    }

    #[test]
    fn pack_wide_beyond_64() {
        // width=65, value = 2^64 = 1 in bit 64
        let mut bits = vec![false; 65];
        bits[64] = true;
        let v = pack(65, &bits);
        // 2^64 = Integer::from(1u64) * 2^64
        let two_64 = Integer::from(1u64 << 32) * Integer::from(1u64 << 32);
        assert_eq!(v, two_64);
    }
}
