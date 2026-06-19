use shinri_core::Rational;
use shinri_num::Integer;

#[test]
fn core_reexports_rational_with_fast_path() {
    let half = Rational::new(Integer::from(1i128), Integer::from(2i128));
    let third = Rational::new(Integer::from(1i128), Integer::from(3i128));
    assert_eq!(
        half + third,
        Rational::new(Integer::from(5i128), Integer::from(6i128))
    );
}
