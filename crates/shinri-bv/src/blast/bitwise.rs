use crate::blast::{BitLit, Blaster};

fn zip_map(
    b: &mut Blaster,
    x: &[BitLit],
    y: &[BitLit],
    mut f: impl FnMut(&mut Blaster, BitLit, BitLit) -> BitLit,
) -> Vec<BitLit> {
    debug_assert_eq!(x.len(), y.len());
    x.iter().zip(y).map(|(&a, &c)| f(b, a, c)).collect()
}

pub fn bvand(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    zip_map(b, x, y, Blaster::and2)
}
pub fn bvor(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    zip_map(b, x, y, Blaster::or2)
}
pub fn bvxor(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    zip_map(b, x, y, Blaster::xor2)
}
pub fn bvnot(b: &mut Blaster, x: &[BitLit]) -> Vec<BitLit> {
    x.iter().map(|&a| b.not1(a)).collect()
}
pub fn bvnand(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let t = bvand(b, x, y);
    bvnot(b, &t)
}
pub fn bvnor(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let t = bvor(b, x, y);
    bvnot(b, &t)
}
pub fn bvxnor(b: &mut Blaster, x: &[BitLit], y: &[BitLit]) -> Vec<BitLit> {
    let t = bvxor(b, x, y);
    bvnot(b, &t)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testkit::{pin_const, solve_value};

    // --- bvand ---

    #[test]
    fn bvand_basic() {
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b1100, 4);
        let y = pin_const(&mut b, 0b1010, 4);
        let r = bvand(&mut b, &x, &y);
        assert_eq!(solve_value(b, &r), 0b1000);
    }

    #[test]
    fn bvand_exhaustive_4bit() {
        for xv in 0u64..16 {
            for yv in 0u64..16 {
                let mut b = Blaster::new();
                let x = pin_const(&mut b, xv, 4);
                let y = pin_const(&mut b, yv, 4);
                let r = bvand(&mut b, &x, &y);
                assert_eq!(solve_value(b, &r), xv & yv, "bvand({xv:#06b}, {yv:#06b})");
            }
        }
    }

    // --- bvor ---

    #[test]
    fn bvor_basic() {
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b1100, 4);
        let y = pin_const(&mut b, 0b1010, 4);
        let r = bvor(&mut b, &x, &y);
        assert_eq!(solve_value(b, &r), 0b1110);
    }

    #[test]
    fn bvor_exhaustive_4bit() {
        for xv in 0u64..16 {
            for yv in 0u64..16 {
                let mut b = Blaster::new();
                let x = pin_const(&mut b, xv, 4);
                let y = pin_const(&mut b, yv, 4);
                let r = bvor(&mut b, &x, &y);
                assert_eq!(solve_value(b, &r), xv | yv, "bvor({xv:#06b}, {yv:#06b})");
            }
        }
    }

    // --- bvxor ---

    #[test]
    fn bvxor_basic() {
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b1100, 4);
        let y = pin_const(&mut b, 0b1010, 4);
        let r = bvxor(&mut b, &x, &y);
        assert_eq!(solve_value(b, &r), 0b0110);
    }

    #[test]
    fn bvxor_exhaustive_4bit() {
        for xv in 0u64..16 {
            for yv in 0u64..16 {
                let mut b = Blaster::new();
                let x = pin_const(&mut b, xv, 4);
                let y = pin_const(&mut b, yv, 4);
                let r = bvxor(&mut b, &x, &y);
                assert_eq!(solve_value(b, &r), xv ^ yv, "bvxor({xv:#06b}, {yv:#06b})");
            }
        }
    }

    // --- bvnot ---

    #[test]
    fn bvnot_basic() {
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b1010, 4);
        let r = bvnot(&mut b, &x);
        assert_eq!(solve_value(b, &r), 0b0101);
    }

    #[test]
    fn bvnot_all_ones() {
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b1111, 4);
        let r = bvnot(&mut b, &x);
        assert_eq!(solve_value(b, &r), 0b0000);
    }

    #[test]
    fn bvnot_zero() {
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b0000, 4);
        let r = bvnot(&mut b, &x);
        assert_eq!(solve_value(b, &r), 0b1111);
    }

    // --- bvnand ---

    #[test]
    fn bvnand_basic() {
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b1100, 4);
        let y = pin_const(&mut b, 0b1010, 4);
        let r = bvnand(&mut b, &x, &y);
        // NOT (1100 AND 1010) = NOT 1000 = 0111
        assert_eq!(solve_value(b, &r), 0b0111);
    }

    #[test]
    fn bvnand_spot_checks() {
        for (xv, yv) in [(0b0000u64, 0b1111u64), (0b1111, 0b1111), (0b1010, 0b0101)] {
            let mut b = Blaster::new();
            let x = pin_const(&mut b, xv, 4);
            let y = pin_const(&mut b, yv, 4);
            let r = bvnand(&mut b, &x, &y);
            let expected = (!(xv & yv)) & 0b1111;
            assert_eq!(solve_value(b, &r), expected, "bvnand({xv:#06b}, {yv:#06b})");
        }
    }

    // --- bvnor ---

    #[test]
    fn bvnor_basic() {
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b1100, 4);
        let y = pin_const(&mut b, 0b1010, 4);
        let r = bvnor(&mut b, &x, &y);
        // NOT (1100 OR 1010) = NOT 1110 = 0001
        assert_eq!(solve_value(b, &r), 0b0001);
    }

    #[test]
    fn bvnor_spot_checks() {
        for (xv, yv) in [(0b0000u64, 0b0000u64), (0b1111, 0b0000), (0b1010, 0b0101)] {
            let mut b = Blaster::new();
            let x = pin_const(&mut b, xv, 4);
            let y = pin_const(&mut b, yv, 4);
            let r = bvnor(&mut b, &x, &y);
            let expected = (!(xv | yv)) & 0b1111;
            assert_eq!(solve_value(b, &r), expected, "bvnor({xv:#06b}, {yv:#06b})");
        }
    }

    // --- bvxnor ---

    #[test]
    fn bvxnor_basic() {
        let mut b = Blaster::new();
        let x = pin_const(&mut b, 0b1100, 4);
        let y = pin_const(&mut b, 0b1010, 4);
        let r = bvxnor(&mut b, &x, &y);
        // NOT (1100 XOR 1010) = NOT 0110 = 1001
        assert_eq!(solve_value(b, &r), 0b1001);
    }

    #[test]
    fn bvxnor_spot_checks() {
        for (xv, yv) in [(0b0000u64, 0b0000u64), (0b1111, 0b1111), (0b1010, 0b1010)] {
            let mut b = Blaster::new();
            let x = pin_const(&mut b, xv, 4);
            let y = pin_const(&mut b, yv, 4);
            let r = bvxnor(&mut b, &x, &y);
            let expected = (!(xv ^ yv)) & 0b1111;
            assert_eq!(solve_value(b, &r), expected, "bvxnor({xv:#06b}, {yv:#06b})");
        }
    }
}
