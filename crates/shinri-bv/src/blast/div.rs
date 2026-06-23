use crate::blast::{BitLit, Blaster};
use crate::blast::arith::{adder, bvadd, bvneg};

fn is_zero(b: &mut Blaster, x: &[BitLit]) -> BitLit {
    let mut acc = x[0];
    for &bit in &x[1..] {
        acc = b.or2(acc, bit);
    }
    b.not1(acc)
}

/// Trial-subtract: returns (a - d, borrow_out).
/// borrow_out = 1 iff a < d (unsigned).
fn sub_borrow(b: &mut Blaster, a: &[BitLit], d: &[BitLit]) -> (Vec<BitLit>, BitLit) {
    // a - d = a + (~d) + 1; carry_out == 1 means a >= d (no borrow).
    let nd: Vec<BitLit> = d.iter().map(|&x| b.not1(x)).collect();
    let one = b.one();
    let (diff, carry) = adder(b, a, &nd, one);
    (diff, b.not1(carry))
}

/// Unsigned restoring division. Returns (quotient, remainder).
/// SMT-LIB zero-divisor semantics: if y == 0, quot = all-ones, rem = x.
pub fn udivurem(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> (Vec<BitLit>, Vec<BitLit>) {
    let n = x.len();
    let zero = b.zero();
    let mut rem: Vec<BitLit> = vec![zero; n];
    let mut quot: Vec<BitLit> = vec![zero; n];

    for i in (0..n).rev() {
        // rem = (rem << 1) | x[i]  (shift left, bring in MSB-first dividend bit)
        let mut shifted = vec![x[i]];
        shifted.extend_from_slice(&rem[..n - 1]);
        rem = shifted;

        // Trial-subtract divisor from partial remainder
        let (diff, borrow) = sub_borrow(b, &rem, y);
        // keep = !borrow  (1 if rem >= y, i.e. subtraction succeeded)
        let keep = b.not1(borrow);
        // If keep: rem = diff, quot bit = 1; else rem unchanged, quot bit = 0
        let new_rem: Vec<BitLit> = (0..n).map(|j| b.mux2(keep, diff[j], rem[j])).collect();
        rem = new_rem;
        quot[i] = keep;
    }

    // Zero-divisor fixup
    let yz = is_zero(b, y);
    let all_ones: Vec<BitLit> = (0..n).map(|_| b.one()).collect();
    let q = (0..n).map(|j| b.mux2(yz, all_ones[j], quot[j])).collect::<Vec<_>>();
    let r = (0..n).map(|j| b.mux2(yz, x[j], rem[j])).collect::<Vec<_>>();
    (q, r)
}

pub fn bvudiv(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    udivurem(b, x, y).0
}

pub fn bvurem(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    udivurem(b, x, y).1
}

/// Signed division, truncating toward zero (SMT-LIB bvsdiv).
pub fn bvsdiv(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let sx = *x.last().unwrap();
    let sy = *y.last().unwrap();
    // ux = if sx then bvneg(x) else x
    let negx = bvneg(b, x);
    let n = x.len();
    let ux: Vec<BitLit> = (0..n).map(|j| b.mux2(sx, negx[j], x[j])).collect();
    // uy = if sy then bvneg(y) else y
    let negy = bvneg(b, y);
    let uy: Vec<BitLit> = (0..n).map(|j| b.mux2(sy, negy[j], y[j])).collect();

    let u = bvudiv(b, &ux, &uy);
    // result sign = sx XOR sy; if different, negate
    let sign_diff = b.xor2(sx, sy);
    let negu = bvneg(b, &u);
    (0..n).map(|j| b.mux2(sign_diff, negu[j], u[j])).collect()
}

/// Signed remainder (sign follows dividend) — SMT-LIB bvsrem.
pub fn bvsrem(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let sx = *x.last().unwrap();
    let sy = *y.last().unwrap();
    let negx = bvneg(b, x);
    let n = x.len();
    let ux: Vec<BitLit> = (0..n).map(|j| b.mux2(sx, negx[j], x[j])).collect();
    let negy = bvneg(b, y);
    let uy: Vec<BitLit> = (0..n).map(|j| b.mux2(sy, negy[j], y[j])).collect();

    let u = bvurem(b, &ux, &uy);
    let negu = bvneg(b, &u);
    // result = if sx then bvneg(u) else u
    (0..n).map(|j| b.mux2(sx, negu[j], u[j])).collect()
}

/// Signed modulo (sign follows divisor) — SMT-LIB bvsmod.
pub fn bvsmod(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let sx = *x.last().unwrap();
    let sy = *y.last().unwrap();
    let negx = bvneg(b, x);
    let n = x.len();
    let ux: Vec<BitLit> = (0..n).map(|j| b.mux2(sx, negx[j], x[j])).collect();
    let negy = bvneg(b, y);
    let uy: Vec<BitLit> = (0..n).map(|j| b.mux2(sy, negy[j], y[j])).collect();

    let u = bvurem(b, &ux, &uy);
    let uz = is_zero(b, &u);
    let negu = bvneg(b, &u);

    // Four cases by (sx, sy):
    //   (0,0): u
    //   (1,0): bvadd(bvneg(u), y), unless u==0 -> 0
    //   (0,1): bvadd(u, y),        unless u==0 -> 0
    //   (1,1): bvneg(u)
    //
    // When u==0: negu==0, bvadd(negu, y)=y but should be 0, bvadd(u, y)=y but should be 0.
    // So for the two mixed-sign branches, we gate by !uz.
    let zero_vec: Vec<BitLit> = (0..n).map(|_| b.zero()).collect();

    // (sx=1, sy=0) branch: bvadd(negu, y), or 0 if u==0
    let negu_plus_y = bvadd(b, &negu, y);
    let not_uz = b.not1(uz);
    // gate by !uz: if uz, give 0; else negu_plus_y
    let case_10: Vec<BitLit> = (0..n).map(|j| b.mux2(not_uz, negu_plus_y[j], zero_vec[j])).collect();

    // (sx=0, sy=1) branch: bvadd(u, y), or 0 if u==0
    let u_plus_y = bvadd(b, &u, y);
    let case_01: Vec<BitLit> = (0..n).map(|j| b.mux2(not_uz, u_plus_y[j], zero_vec[j])).collect();

    // (sx=0, sy=0): u
    // (sx=1, sy=1): negu
    // Build mux tree:
    //   outer_sel = sy
    //   if sy=0: inner = mux(sx, case_10, u)      [sx=1 -> case_10, sx=0 -> u]
    //   if sy=1: inner = mux(sx, negu, case_01)   [sx=1 -> negu, sx=0 -> case_01]
    let when_sy0: Vec<BitLit> = (0..n).map(|j| b.mux2(sx, case_10[j], u[j])).collect();
    let when_sy1: Vec<BitLit> = (0..n).map(|j| b.mux2(sx, negu[j], case_01[j])).collect();
    (0..n).map(|j| b.mux2(sy, when_sy1[j], when_sy0[j])).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blast::Blaster;
    use crate::testkit::{pin_const, solve_value, solve_value_pair};

    // -------------------------------------------------------------------------
    // Unsigned division including zero-divisor cases
    // -------------------------------------------------------------------------
    #[test]
    fn udiv_urem_including_zero_divisor() {
        let cases: &[(u64, u64)] = &[(17, 5), (255, 16), (0, 3), (7, 7), (10, 0), (255, 0)];
        for &(x, y) in cases {
            let (eq, er) = if y == 0 { (0xFF, x) } else { (x / y, x % y) };
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, x, 8);
            let yv = pin_const(&mut b, y, 8);
            let (q, r) = udivurem(&mut b, &xv, &yv);
            let (gq, gr) = solve_value_pair(b, &q, &r);
            assert_eq!(gq, eq, "udiv x={x} y={y}: expected quot={eq} got {gq}");
            assert_eq!(gr, er, "urem x={x} y={y}: expected rem={er} got {gr}");
        }
    }

    // -------------------------------------------------------------------------
    // Signed division (truncate toward zero)
    // -------------------------------------------------------------------------
    #[test]
    fn sdiv_all_sign_combos() {
        // (x_i8, y_i8, expected_i8): native i8 `/` truncates toward zero
        let cases: &[(i8, i8, i8)] = &[
            (-7, 2, -3),
            (7, -2, -3),
            (-7, -2, 3),
            (7, 2, 3),
            (-128, 1, -128),
            (-1, -1, 1),
        ];
        for &(xi, yi, expected) in cases {
            assert_eq!(xi / yi, expected, "native sdiv reference mismatch");
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, xi as u8 as u64, 8);
            let yv = pin_const(&mut b, yi as u8 as u64, 8);
            let d = bvsdiv(&mut b, &xv, &yv);
            let got = solve_value(b, &d) as u8 as i8;
            assert_eq!(got, expected, "bvsdiv({xi},{yi}): expected {expected} got {got}");
        }
    }

    // -------------------------------------------------------------------------
    // Signed remainder (sign follows dividend)
    // -------------------------------------------------------------------------
    #[test]
    fn srem_sign_follows_dividend() {
        let cases: &[(i8, i8, i8)] = &[
            (-7, 2, -1),
            (7, -2, 1),
            (-7, -2, -1),
            (7, 2, 1),
        ];
        for &(xi, yi, expected) in cases {
            assert_eq!(xi % yi, expected, "native srem reference mismatch");
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, xi as u8 as u64, 8);
            let yv = pin_const(&mut b, yi as u8 as u64, 8);
            let r = bvsrem(&mut b, &xv, &yv);
            let got = solve_value(b, &r) as u8 as i8;
            assert_eq!(got, expected, "bvsrem({xi},{yi}): expected {expected} got {got}");
        }
    }

    // -------------------------------------------------------------------------
    // Signed modulo (sign follows divisor) — SMT-LIB bvsmod
    // Reference: u = unsigned_abs(x) % unsigned_abs(y);
    //   if u==0 => 0
    //   else (x<0, y<0):
    //     (F,F) => u
    //     (T,F) => y - u       (= y + bvneg(u) as i16)
    //     (F,T) => u + y       (since y is negative)
    //     (T,T) => -u
    // -------------------------------------------------------------------------
    fn smod_ref(xi: i8, yi: i8) -> i8 {
        let u = ((xi as i16).unsigned_abs() % (yi as i16).unsigned_abs()) as i16;
        if u == 0 {
            return 0;
        }
        let result = match (xi < 0, yi < 0) {
            (false, false) => u,
            (true, false) => (yi as i16) - u,
            (false, true) => u + (yi as i16),
            (true, true) => -u,
        };
        result as i8
    }

    #[test]
    fn smod_sign_follows_divisor() {
        // Cross-check reference against known values first
        assert_eq!(smod_ref(-7, 2), 1,  "smod_ref(-7,2)");
        assert_eq!(smod_ref(7, -2), -1, "smod_ref(7,-2)");
        assert_eq!(smod_ref(-7, -2), -1, "smod_ref(-7,-2)");
        assert_eq!(smod_ref(7, 2), 1,   "smod_ref(7,2)");
        assert_eq!(smod_ref(4, 2), 0,   "smod_ref(4,2)");
        assert_eq!(smod_ref(-4, 2), 0,  "smod_ref(-4,2)");

        let cases: &[(i8, i8)] = &[
            (-7, 2),
            (7, -2),
            (-7, -2),
            (7, 2),
            (4, 2),
            (-4, 2),
        ];
        for &(xi, yi) in cases {
            let expected = smod_ref(xi, yi);
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, xi as u8 as u64, 8);
            let yv = pin_const(&mut b, yi as u8 as u64, 8);
            let r = bvsmod(&mut b, &xv, &yv);
            let got = solve_value(b, &r) as u8 as i8;
            assert_eq!(got, expected, "bvsmod({xi},{yi}): expected {expected} got {got}");
        }
    }

    // -------------------------------------------------------------------------
    // Signed div/rem/mod by zero — SMT-LIB compositional semantics confirmed against z3.
    // Note: bvsdiv(neg, 0) = 1 (not all-ones); bvsrem/bvsmod(x, 0) = x.
    // -------------------------------------------------------------------------
    #[test]
    fn signed_div_by_zero() {
        // 8-bit signed div-by-zero cases. Encode negatives as u8 two's-complement.
        // (-7 as u8 = 249 = 0xF9)
        let cases = vec![
            // (op, x_i8, expected_u8)
            ("bvsdiv", -7i8, 1u8),        // bvsdiv(-7, 0) = 1
            ("bvsdiv", 7i8, 255u8),       // bvsdiv(7, 0) = 255 (0xFF)
            ("bvsrem", -7i8, 249u8),      // bvsrem(-7, 0) = -7 = 249
            ("bvsrem", 7i8, 7u8),         // bvsrem(7, 0) = 7
            ("bvsmod", -7i8, 249u8),      // bvsmod(-7, 0) = -7 = 249
            ("bvsmod", 7i8, 7u8),         // bvsmod(7, 0) = 7
        ];

        for (op, xi, expected) in cases {
            let mut b = Blaster::new();
            let xv = pin_const(&mut b, xi as u8 as u64, 8);
            let yv = pin_const(&mut b, 0u64, 8);

            let result = match op {
                "bvsdiv" => bvsdiv(&mut b, &xv, &yv),
                "bvsrem" => bvsrem(&mut b, &xv, &yv),
                "bvsmod" => bvsmod(&mut b, &xv, &yv),
                _ => panic!("unknown op: {}", op),
            };

            let got = solve_value(b, &result) as u8;
            assert_eq!(
                got, expected,
                "{op}({xi}, 0): expected {expected} got {got}"
            );
        }
    }
}
