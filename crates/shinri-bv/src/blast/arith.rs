use crate::blast::{BitLit, Blaster};
use crate::blast::bitwise::bvnot;

pub fn adder(b: &mut Blaster, x: &[BitLit], y: &[BitLit], cin: BitLit) -> (Vec<BitLit>, BitLit) {
    debug_assert_eq!(x.len(), y.len());
    let mut carry = cin;
    let mut sum = Vec::with_capacity(x.len());
    for i in 0..x.len() {
        let (s, c) = b.full_adder(x[i], y[i], carry);
        sum.push(s);
        carry = c;
    }
    (sum, carry)
}

pub fn bvadd(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let z = b.zero();
    adder(b, x, y, z).0
}

pub fn bvneg(b: &mut Blaster, x: &[BitLit]) -> Vec<BitLit> {
    let nx = bvnot(b, x);
    let ones: Vec<BitLit> = (0..x.len())
        .map(|i| if i == 0 { b.one() } else { b.zero() })
        .collect();
    let z = b.zero();
    adder(b, &nx, &ones, z).0
}

pub fn bvsub(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let ny = bvnot(b, y);
    let one = b.one();
    adder(b, x, &ny, one).0
}

#[cfg(test)]
mod tests {
    use crate::blast::Blaster;
    use crate::testkit::{pin_const, solve_value};

    #[test]
    fn bvadd_wraps_mod_2pow_w() {
        for (x, y) in [(0u64, 0u64), (1, 1), (255, 1), (200, 100), (123, 77)] {
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, x, 8);
            let yv = pin_const(&mut b, y, 8);
            let r = super::bvadd(&mut b, &xv, &yv);
            assert_eq!(solve_value(b, &r), (x + y) & 0xFF, "x={x} y={y}");
        }
    }

    #[test]
    fn bvsub_and_neg() {
        let mut b = Blaster::new();
        let xv = pin_const(&mut b, 5, 8);
        let yv = pin_const(&mut b, 9, 8);
        let r = super::bvsub(&mut b, &xv, &yv); // 5-9 = -4 = 252 mod 256
        assert_eq!(solve_value(b, &r), 252);
    }
}
