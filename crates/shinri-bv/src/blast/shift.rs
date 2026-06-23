//! Barrel-shifter gadgets: bvshl, bvlshr, bvashr (shift amount is a BV word),
//! and constant-amount rotate_left / rotate_right (pure index permutation, no clauses).
//!
//! Bit order: index 0 = LSB, index n-1 = MSB (same convention as all blast gadgets).
//!
//! ## Barrel-shifter algorithm
//!
//! Let `n = x.len()`, `stages = ceil(log2(n))` (0 for n == 1).
//! For each stage `s` in `0..stages`:
//!   - If `y[s]` is set, shift the running word by `2^s` positions; otherwise pass through.
//!   - mux2(y[s], shifted_bit, unshifted_bit) per output bit.
//!
//! For out-of-range amounts (y has a set bit at index >= stages, meaning shift >= 2^stages >= n):
//!   - Compute `overflow = OR of y[stages..]`.
//!   - Mux the entire word to the fill value (zero for shl/lshr, sign-bit for ashr).
//!
//! ## Rotate algorithm
//!
//! k is reduced mod n first.  Result is a pure index permutation (no SAT clauses).
//! rotate_left by k:  result[i] = x[(i + n - k) % n]
//! rotate_right by k: result[i] = x[(i + k) % n]

use crate::blast::{BitLit, Blaster};

// ─── helpers ────────────────────────────────────────────────────────────────

/// ceil(log2(n)); returns 0 for n == 0 or n == 1.
fn log2_ceil(n: usize) -> usize {
    if n <= 1 {
        return 0;
    }
    let bits = usize::BITS as usize;
    bits - (n - 1).leading_zeros() as usize
}

/// OR-reduce a slice of BitLits into a single gate (tree-fold).
/// Returns `b.zero()` for an empty slice.
fn or_reduce(b: &mut Blaster, lits: &[BitLit]) -> BitLit {
    if lits.is_empty() {
        return b.zero();
    }
    let mut acc = lits[0];
    for &l in &lits[1..] {
        acc = b.or2(acc, l);
    }
    acc
}

// ─── core barrel-shifter ─────────────────────────────────────────────────────

/// Run one barrel-shifter stage: conditionally shift `cur` left (toward MSB) by `amount`
/// bits if `sel` is set.  `fill` is the bit inserted when the shifted position is out of range.
///
/// bvshl: fill = zero, direction = +left  (high j reads low source)
/// bvlshr/bvashr: fill per-bit provided by caller, direction = +right (low j reads high source)
fn barrel_stage_shl(
    b: &mut Blaster,
    cur: &[BitLit],
    sel: BitLit,
    amount: usize,
    fill: BitLit,
) -> Vec<BitLit> {
    let n = cur.len();
    (0..n)
        .map(|j| {
            // Shifted: bit j comes from position j - amount (left shift moves bits up).
            let shifted = if j >= amount { cur[j - amount] } else { fill };
            b.mux2(sel, shifted, cur[j])
        })
        .collect()
}

fn barrel_stage_lshr(
    b: &mut Blaster,
    cur: &[BitLit],
    sel: BitLit,
    amount: usize,
    fill: BitLit,
) -> Vec<BitLit> {
    let n = cur.len();
    (0..n)
        .map(|j| {
            // Shifted: bit j comes from position j + amount (right shift moves bits down).
            let shifted = if j + amount < n { cur[j + amount] } else { fill };
            b.mux2(sel, shifted, cur[j])
        })
        .collect()
}

// ─── public API ──────────────────────────────────────────────────────────────

/// Left shift: result = x << y (saturates to 0 when y >= n).
pub fn bvshl(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let n = x.len();
    debug_assert!(n > 0, "bvshl: zero-width operand");
    let stages = log2_ceil(n);
    let fill = b.zero();

    // Per-stage muxes.
    let mut cur = x.to_vec();
    for s in 0..stages {
        let sel = y[s]; // y[s] is valid since y.len() == n >= 2^stages (for n >= 2)
        cur = barrel_stage_shl(b, &cur, sel, 1 << s, fill);
    }

    // Overflow: any y bit at index >= stages forces result to fill.
    if stages < y.len() {
        let overflow = or_reduce(b, &y[stages..]);
        cur = cur.iter().map(|&bit| b.mux2(overflow, fill, bit)).collect();
    }

    cur
}

/// Logical right shift: result = x >> y (saturates to 0 when y >= n).
pub fn bvlshr(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let n = x.len();
    debug_assert!(n > 0, "bvlshr: zero-width operand");
    let stages = log2_ceil(n);
    let fill = b.zero();

    let mut cur = x.to_vec();
    for s in 0..stages {
        let sel = y[s];
        cur = barrel_stage_lshr(b, &cur, sel, 1 << s, fill);
    }

    if stages < y.len() {
        let overflow = or_reduce(b, &y[stages..]);
        cur = cur.iter().map(|&bit| b.mux2(overflow, fill, bit)).collect();
    }

    cur
}

/// Arithmetic right shift: result = x >>_a y (saturates to sign-fill when y >= n).
pub fn bvashr(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let n = x.len();
    debug_assert!(n > 0, "bvashr: zero-width operand");
    let stages = log2_ceil(n);
    let sign = x[n - 1]; // MSB = sign bit; this is a BitLit, not a gate

    let mut cur = x.to_vec();
    for s in 0..stages {
        let sel = y[s];
        // Fill for arith-right is the ORIGINAL sign bit (x[n-1], captured before any stage).
        cur = barrel_stage_lshr(b, &cur, sel, 1 << s, sign);
    }

    if stages < y.len() {
        let overflow = or_reduce(b, &y[stages..]);
        // Mux entire word: if overflow, each bit = sign.
        cur = cur.iter().map(|&bit| b.mux2(overflow, sign, bit)).collect();
    }

    cur
}

// ─── constant rotates (pure index permutation) ───────────────────────────────

/// Left rotate by constant k.
///
/// SMT-LIB `(_ rotate_left k)` on a value v: `((v << k) | (v >> (n-k))) & mask`.
/// In LSB→MSB bit order: result[i] = x[(i + n - k) % n].
/// Verify: rotate_left by 1 moves bit 0 to position 1 (bit 0 of v → bit 1 of result), i.e.
///   result[1] = x[0], result[0] = x[n-1].  ((v<<1) | (v>>(n-1))): bit 1 of result is bit 0 of v.  ✓
pub fn rotate_left(x: &[BitLit], k: u32) -> Vec<BitLit> {
    let n = x.len();
    if n == 0 {
        return Vec::new();
    }
    let k = (k as usize) % n;
    (0..n).map(|i| x[(i + n - k) % n]).collect()
}

/// Right rotate by constant k.
///
/// SMT-LIB `(_ rotate_right k)` on a value v: `((v >> k) | (v << (n-k))) & mask`.
/// In LSB→MSB bit order: result[i] = x[(i + k) % n].
pub fn rotate_right(x: &[BitLit], k: u32) -> Vec<BitLit> {
    let n = x.len();
    if n == 0 {
        return Vec::new();
    }
    let k = (k as usize) % n;
    (0..n).map(|i| x[(i + k) % n]).collect()
}

// ─── tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testkit::{pin_const, solve_value};

    // ── bvshl ────────────────────────────────────────────────────────────────

    #[test]
    fn shifts_match_native() {
        let n = 8u32;
        for x in [0u64, 1, 0x80, 0xFF, 0x3C] {
            for sh in 0u64..=9 {
                // include sh >= width
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, n);
                let yv = pin_const(&mut b, sh, n);
                let r = bvshl(&mut b, &xv, &yv);
                let expect = if sh >= 8 { 0 } else { (x << sh) & 0xFF };
                assert_eq!(solve_value(b, &r), expect, "shl x={x:#x} sh={sh}");
            }
        }
    }

    #[test]
    fn lshr_matches_native() {
        let n = 8u32;
        for x in [0u64, 1, 0x80, 0xFF, 0x3C] {
            for sh in 0u64..=9 {
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, n);
                let yv = pin_const(&mut b, sh, n);
                let r = bvlshr(&mut b, &xv, &yv);
                let expect = if sh >= 8 { 0 } else { x >> sh };
                assert_eq!(solve_value(b, &r), expect, "lshr x={x:#x} sh={sh}");
            }
        }
    }

    #[test]
    fn ashr_sign_fills() {
        let mut b = Blaster::new();
        let xv = pin_const(&mut b, 0x80, 8); // -128
        let yv = pin_const(&mut b, 3, 8);
        let r = bvashr(&mut b, &xv, &yv);
        assert_eq!(solve_value(b, &r), 0xF0); // arithmetic shift keeps sign
    }

    #[test]
    fn ashr_matches_native() {
        let n = 8u32;
        // Test cases: (x, sh, expected)
        // Native ref: ((x as i8) >> min(sh, 7)) as u8, but for sh >= 8 use sign-fill
        let cases: &[(u64, u64)] = &[
            // positive values
            (0x7F, 3), // 0111_1111 >> 3 = 0x0F
            (0x7F, 8), // positive, sh>=8 => 0x00
            (0x3C, 2),
            // negative values (MSB=1)
            (0x80, 3), // -128 >> 3 = 0xF0
            (0xFF, 4), // -1 >> 4 = 0xFF (all sign)
            (0x80, 8), // sh>=8, negative => 0xFF
            (0x80, 9), // sh>=8, negative => 0xFF
            (0x7F, 9), // sh>=8, positive => 0x00
            (0x00, 5),
        ];
        for &(x, sh) in cases {
            let expected = if sh >= 8 {
                // sign-fill
                if (x >> 7) & 1 == 1 { 0xFF } else { 0x00 }
            } else {
                // arithmetic shift: treat x as i8
                let xsigned = x as u8 as i8;
                (xsigned >> sh) as u8 as u64
            };
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, x, n);
            let yv = pin_const(&mut b, sh, n);
            let r = bvashr(&mut b, &xv, &yv);
            assert_eq!(solve_value(b, &r), expected, "ashr x={x:#x} sh={sh}");
        }
    }

    // ── rotate_left ──────────────────────────────────────────────────────────

    #[test]
    fn rotate_left_matches_native() {
        // rotate_left(x, k) = x.rotate_left(k) for u8
        for x in [0u8, 1, 0x80, 0xFF, 0x3C, 0xAB] {
            for k in [0u32, 1, 3, 7, 8, 11] {
                let expected = x.rotate_left(k) as u64;
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x as u64, 8);
                let r = rotate_left(&xv, k);
                assert_eq!(solve_value(b, &r), expected, "rotate_left x={x:#x} k={k}");
            }
        }
    }

    #[test]
    fn rotate_right_matches_native() {
        for x in [0u8, 1, 0x80, 0xFF, 0x3C, 0xAB] {
            for k in [0u32, 1, 3, 7, 8, 11] {
                let expected = x.rotate_right(k) as u64;
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x as u64, 8);
                let r = rotate_right(&xv, k);
                assert_eq!(solve_value(b, &r), expected, "rotate_right x={x:#x} k={k}");
            }
        }
    }

    // ── edge cases ───────────────────────────────────────────────────────────

    #[test]
    fn rotate_k_eq_n_is_identity() {
        // k == n means k % n == 0, should be identity
        for x in [0u8, 1, 0x80, 0xFF, 0x3C] {
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, x as u64, 8);
            let rl = rotate_left(&xv, 8);
            assert_eq!(solve_value(b, &rl), x as u64, "rotate_left(k=8) identity x={x:#x}");
        }
    }

    #[test]
    fn shl_zero_is_identity() {
        for x in [0u64, 1, 0x80, 0xFF, 0x3C] {
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, x, 8);
            let yv = pin_const(&mut b, 0, 8);
            let r = bvshl(&mut b, &xv, &yv);
            assert_eq!(solve_value(b, &r), x, "shl by 0 identity x={x:#x}");
        }
    }

    #[test]
    fn lshr_zero_is_identity() {
        for x in [0u64, 1, 0x80, 0xFF, 0x3C] {
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, x, 8);
            let yv = pin_const(&mut b, 0, 8);
            let r = bvlshr(&mut b, &xv, &yv);
            assert_eq!(solve_value(b, &r), x, "lshr by 0 identity x={x:#x}");
        }
    }
}
