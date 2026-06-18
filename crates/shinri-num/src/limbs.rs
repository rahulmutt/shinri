//! Little-endian magnitude limb routines. A "magnitude" is a `&[u64]` /
//! `Vec<u64>` with the least-significant limb first and NO trailing zero limbs
//! (so the empty slice is the unique representation of zero).

use core::cmp::Ordering;

/// Remove trailing zero limbs so the magnitude is canonical.
pub fn trim(v: &mut Vec<u64>) {
    while v.last() == Some(&0) {
        v.pop();
    }
}

/// Compare two canonical magnitudes.
pub fn cmp(a: &[u64], b: &[u64]) -> Ordering {
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    Ordering::Equal
}

/// Add two canonical magnitudes.
pub fn add(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut out = Vec::with_capacity(long.len() + 1);
    let mut carry: u128 = 0;
    for i in 0..long.len() {
        let bv = if i < short.len() { short[i] as u128 } else { 0 };
        let sum = long[i] as u128 + bv + carry;
        out.push(sum as u64);
        carry = sum >> 64;
    }
    if carry != 0 {
        out.push(carry as u64);
    }
    out
}

/// Subtract `b` from `a`. Precondition: `cmp(a, b) != Less`. Result is canonical.
pub fn sub(a: &[u64], b: &[u64]) -> Vec<u64> {
    debug_assert!(cmp(a, b) != Ordering::Less, "limbs::sub requires a >= b");
    let mut out = Vec::with_capacity(a.len());
    let mut borrow: i128 = 0;
    for i in 0..a.len() {
        let bv = if i < b.len() { b[i] as i128 } else { 0 };
        let mut diff = a[i] as i128 - bv - borrow;
        if diff < 0 {
            diff += 1i128 << 64;
            borrow = 1;
        } else {
            borrow = 0;
        }
        out.push(diff as u64);
    }
    trim(&mut out);
    out
}

fn shl1(v: &mut Vec<u64>) {
    let mut carry = 0u64;
    for x in v.iter_mut() {
        let new_carry = *x >> 63;
        *x = (*x << 1) | carry;
        carry = new_carry;
    }
    if carry != 0 {
        v.push(carry);
    }
}

/// Divide canonical magnitude `a` by canonical magnitude `b` (b non-empty),
/// returning (quotient, remainder), both canonical. Binary long division.
pub fn divrem(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    debug_assert!(!b.is_empty(), "divrem by zero magnitude");
    if cmp(a, b) == Ordering::Less {
        return (Vec::new(), a.to_vec());
    }
    let bits = a.len() * 64;
    let mut q = vec![0u64; a.len()];
    let mut r: Vec<u64> = Vec::new();
    for i in (0..bits).rev() {
        shl1(&mut r);
        let bit = (a[i / 64] >> (i % 64)) & 1;
        if bit == 1 {
            if r.is_empty() {
                r.push(1);
            } else {
                r[0] |= 1;
            }
        }
        if cmp(&r, b) != Ordering::Less {
            r = sub(&r, b);
            q[i / 64] |= 1u64 << (i % 64);
        }
    }
    trim(&mut q);
    trim(&mut r);
    (q, r)
}

/// Schoolbook multiply of two canonical magnitudes.
pub fn mul_schoolbook(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![0u64; a.len() + b.len()];
    for i in 0..a.len() {
        let ai = a[i] as u128;
        let mut carry: u128 = 0;
        for j in 0..b.len() {
            let cur = out[i + j] as u128 + ai * b[j] as u128 + carry;
            out[i + j] = cur as u64;
            carry = cur >> 64;
        }
        out[i + b.len()] = carry as u64;
    }
    trim(&mut out);
    out
}

const KARATSUBA_THRESHOLD: usize = 32;

fn add_shifted(dst: &mut Vec<u64>, src: &[u64], shift: usize) {
    if src.is_empty() {
        return;
    }
    if dst.len() < src.len() + shift {
        dst.resize(src.len() + shift, 0);
    }
    let mut carry: u128 = 0;
    for i in 0..src.len() {
        let cur = dst[i + shift] as u128 + src[i] as u128 + carry;
        dst[i + shift] = cur as u64;
        carry = cur >> 64;
    }
    let mut idx = src.len() + shift;
    while carry != 0 {
        if idx >= dst.len() {
            dst.push(0);
        }
        let cur = dst[idx] as u128 + carry;
        dst[idx] = cur as u64;
        carry = cur >> 64;
        idx += 1;
    }
}

pub fn karatsuba(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    if a.len() < KARATSUBA_THRESHOLD || b.len() < KARATSUBA_THRESHOLD {
        return mul_schoolbook(a, b);
    }
    let half = a.len().max(b.len()) / 2;
    let split = |x: &[u64]| -> (Vec<u64>, Vec<u64>) {
        if x.len() <= half {
            (x.to_vec(), Vec::new())
        } else {
            let mut lo = x[..half].to_vec();
            let mut hi = x[half..].to_vec();
            trim(&mut lo);
            trim(&mut hi);
            (lo, hi)
        }
    };
    let (a0, a1) = split(a);
    let (b0, b1) = split(b);

    let z0 = karatsuba(&a0, &b0);
    let z2 = karatsuba(&a1, &b1);
    let asum = add(&a0, &a1);
    let bsum = add(&b0, &b1);
    let z1full = karatsuba(&asum, &bsum);
    // z1 = z1full - z2 - z0  (both subtractions are valid: z1full >= z0 + z2)
    let z1 = sub(&sub(&z1full, &z2), &z0);

    let mut result = z0;
    add_shifted(&mut result, &z1, half);
    add_shifted(&mut result, &z2, 2 * half);
    trim(&mut result);
    result
}

/// Public multiply entry point: dispatches schoolbook ↔ Karatsuba by size.
pub fn mul(a: &[u64], b: &[u64]) -> Vec<u64> {
    karatsuba(a, b)
}

#[cfg(test)]
mod karatsuba_tests {
    use super::*;

    #[test]
    fn karatsuba_matches_schoolbook_large() {
        // Build two ~40-limb magnitudes and check the two algorithms agree.
        let a: Vec<u64> = (0..40).map(|i| 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i + 1)).collect();
        let b: Vec<u64> = (0..40).map(|i| 0xD1B5_4A32_D192_ED03u64.wrapping_mul(i + 3)).collect();
        let mut a = a; trim(&mut a);
        let mut b = b; trim(&mut b);
        assert_eq!(mul_schoolbook(&a, &b), karatsuba(&a, &b));
    }
}
