use crate::blast::{BitLit, Blaster};

pub fn eq(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    let mut acc = b.one();
    for i in 0..x.len() {
        let xn = b.xor2(x[i], y[i]);     // 1 if differ
        let same = b.not1(xn);
        acc = b.and2(acc, same);
    }
    acc
}

fn ult_core(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    // borrow-out of x - y  ==  x <_u y
    let ny: Vec<BitLit> = y.iter().map(|&v| b.not1(v)).collect();
    let one = b.one();
    let mut carry = one;
    for i in 0..x.len() {
        let (_, c) = b.full_adder(x[i], ny[i], carry);
        carry = c;
    }
    b.not1(carry) // borrow == !carry_out
}

pub fn ult(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { ult_core(b, x, y) }
pub fn ugt(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { ult(b, y, x) }
pub fn ule(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { let g = ugt(b,x,y); b.not1(g) }
pub fn uge(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { let l = ult(b,x,y); b.not1(l) }

pub fn slt(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit {
    let n = x.len();
    let mx = x[n-1]; let my = y[n-1];
    let u = ult_core(b, x, y);
    // (mx ∧ ¬my) ∨ ((mx = my) ∧ u)
    let nmy = b.not1(my);
    let neg_only = b.and2(mx, nmy);
    let same_sign = { let d = b.xor2(mx, my); b.not1(d) };
    let same_and_u = b.and2(same_sign, u);
    b.or2(neg_only, same_and_u)
}

pub fn sgt(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { slt(b, y, x) }
pub fn sle(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { let g = sgt(b,x,y); b.not1(g) }
pub fn sge(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> BitLit { let l = slt(b,x,y); b.not1(l) }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testkit::{pin_const, solve_value};

    #[test]
    fn unsigned_and_signed_compares() {
        // Test eq
        {
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, 5, 8);
            let yv = pin_const(&mut b, 5, 8);
            let l = eq(&mut b, &xv, &yv);
            assert_eq!(solve_value(b, std::slice::from_ref(&l)), 1, "eq(5,5) should be 1");
        }
        {
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, 5, 8);
            let yv = pin_const(&mut b, 6, 8);
            let l = eq(&mut b, &xv, &yv);
            assert_eq!(solve_value(b, std::slice::from_ref(&l)), 0, "eq(5,6) should be 0");
        }

        // Test unsigned comparators: ult, ule, ugt, uge
        let unsigned_cases = vec![(3, 5), (5, 3), (5, 5)];
        for &(x, y) in &unsigned_cases {
            // ult: x < y (unsigned)
            {
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, 8);
                let yv = pin_const(&mut b, y, 8);
                let l = ult(&mut b, &xv, &yv);
                let expected = (x < y) as u64;
                let got = solve_value(b, std::slice::from_ref(&l));
                assert_eq!(got, expected, "ult({},{}) expected {} got {}", x, y, expected, got);
            }
            // ule: x <= y (unsigned)
            {
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, 8);
                let yv = pin_const(&mut b, y, 8);
                let l = ule(&mut b, &xv, &yv);
                let expected = (x <= y) as u64;
                let got = solve_value(b, std::slice::from_ref(&l));
                assert_eq!(got, expected, "ule({},{}) expected {} got {}", x, y, expected, got);
            }
            // ugt: x > y (unsigned)
            {
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, 8);
                let yv = pin_const(&mut b, y, 8);
                let l = ugt(&mut b, &xv, &yv);
                let expected = (x > y) as u64;
                let got = solve_value(b, std::slice::from_ref(&l));
                assert_eq!(got, expected, "ugt({},{}) expected {} got {}", x, y, expected, got);
            }
            // uge: x >= y (unsigned)
            {
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, 8);
                let yv = pin_const(&mut b, y, 8);
                let l = uge(&mut b, &xv, &yv);
                let expected = (x >= y) as u64;
                let got = solve_value(b, std::slice::from_ref(&l));
                assert_eq!(got, expected, "uge({},{}) expected {} got {}", x, y, expected, got);
            }
        }

        // Test signed comparators: slt, sle, sgt, sge
        // Convert to signed 8-bit for comparison
        let as_i8 = |u: u64| u as i8;

        // Case 1: x=0x80 (=-128), y=0x01 (=1) — signed -128 < 1 but unsigned 128 > 1
        let signed_cases = vec![
            (0x80u64, 0x01u64),  // -128 vs 1
            (0xFEu64, 0xFFu64),  // -2 vs -1
            (0x03u64, 0x05u64),  // 3 vs 5
        ];

        for &(x, y) in &signed_cases {
            let xi = as_i8(x);
            let yi = as_i8(y);

            // slt: x < y (signed)
            {
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, 8);
                let yv = pin_const(&mut b, y, 8);
                let l = slt(&mut b, &xv, &yv);
                let expected = (xi < yi) as u64;
                let got = solve_value(b, std::slice::from_ref(&l));
                assert_eq!(got, expected, "slt({:02x},{:02x}) = slt({},{}) expected {} got {}", x, y, xi, yi, expected, got);
            }
            // sle: x <= y (signed)
            {
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, 8);
                let yv = pin_const(&mut b, y, 8);
                let l = sle(&mut b, &xv, &yv);
                let expected = (xi <= yi) as u64;
                let got = solve_value(b, std::slice::from_ref(&l));
                assert_eq!(got, expected, "sle({:02x},{:02x}) = sle({},{}) expected {} got {}", x, y, xi, yi, expected, got);
            }
            // sgt: x > y (signed)
            {
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, 8);
                let yv = pin_const(&mut b, y, 8);
                let l = sgt(&mut b, &xv, &yv);
                let expected = (xi > yi) as u64;
                let got = solve_value(b, std::slice::from_ref(&l));
                assert_eq!(got, expected, "sgt({:02x},{:02x}) = sgt({},{}) expected {} got {}", x, y, xi, yi, expected, got);
            }
            // sge: x >= y (signed)
            {
                let mut b = Blaster::new();
                let xv = pin_const(&mut b, x, 8);
                let yv = pin_const(&mut b, y, 8);
                let l = sge(&mut b, &xv, &yv);
                let expected = (xi >= yi) as u64;
                let got = solve_value(b, std::slice::from_ref(&l));
                assert_eq!(got, expected, "sge({:02x},{:02x}) = sge({},{}) expected {} got {}", x, y, xi, yi, expected, got);
            }
        }
    }
}
