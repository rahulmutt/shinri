use crate::blast::{BitLit, Blaster};

pub fn concat(hi: &[BitLit], lo: &[BitLit]) -> Vec<BitLit> {
    let mut v = Vec::with_capacity(hi.len() + lo.len());
    v.extend_from_slice(lo);
    v.extend_from_slice(hi);
    v
}

pub fn extract(a: &[BitLit], hi: u32, lo: u32) -> Vec<BitLit> {
    a[lo as usize..=hi as usize].to_vec()
}

pub fn zero_extend(a: &[BitLit], k: u32, b: &Blaster) -> Vec<BitLit> {
    let mut v = a.to_vec();
    v.extend(std::iter::repeat_n(b.zero(), k as usize));
    v
}

pub fn sign_extend(a: &[BitLit], k: u32) -> Vec<BitLit> {
    let msb = *a.last().expect("nonzero width");
    let mut v = a.to_vec();
    v.extend(std::iter::repeat_n(msb, k as usize));
    v
}

pub fn repeat(a: &[BitLit], k: u32) -> Vec<BitLit> {
    let mut v = Vec::with_capacity(a.len() * k as usize);
    for _ in 0..k {
        v.extend_from_slice(a);
    }
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::Blaster;

    fn vars(b: &mut Blaster, n: usize) -> Vec<crate::blast::BitLit> {
        (0..n).map(|_| b.fresh()).collect()
    }

    #[test]
    fn concat_orders_first_arg_high() {
        let mut b = Blaster::new();
        let hi = vars(&mut b, 2); // [h0,h1]
        let lo = vars(&mut b, 3); // [l0,l1,l2]
        let c = concat(&hi, &lo); // width 5, LSB..MSB = l0,l1,l2,h0,h1
        assert_eq!(c.len(), 5);
        assert_eq!(c[0], lo[0]);
        assert_eq!(c[3], hi[0]);
    }

    #[test]
    fn extract_slices_inclusive() {
        let mut b = Blaster::new();
        let a = vars(&mut b, 8);
        let e = extract(&a, 3, 1); // bits 1,2,3
        assert_eq!(e, vec![a[1], a[2], a[3]]);
    }

    #[test]
    fn sign_extend_copies_msb() {
        let mut b = Blaster::new();
        let a = vars(&mut b, 4);
        let s = sign_extend(&a, 2);
        assert_eq!(s.len(), 6);
        assert_eq!(s[4], a[3]);
        assert_eq!(s[5], a[3]);
    }

    #[test]
    fn zero_extend_pads_zero() {
        let mut b = Blaster::new();
        let a = vars(&mut b, 4);
        let z = zero_extend(&a, 2, &b);
        assert_eq!(z.len(), 6);
        assert_eq!(z[4], b.zero());
    }
}
