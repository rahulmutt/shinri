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

/// Schoolbook multiply of two canonical magnitudes.
pub fn mul(a: &[u64], b: &[u64]) -> Vec<u64> {
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
