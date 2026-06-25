use shinri_core::Context;
use shinri_parser::Parser;

// A small QF_FP + QF_BVFP script exercising sorts, specials, arithmetic,
// comparisons, classification, the (fp ..) constructor, and conversions.
const SCRIPT: &str = r#"
(set-logic QF_FP)
(declare-fun x () Float32)
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun r () RoundingMode)
(declare-fun b () (_ BitVec 32))
(assert (fp.leq (fp.add r x y) (fp.mul RNE x y)))
(assert (fp.isNaN (fp.div RNE x (_ +zero 8 24))))
(assert (= y (fp #b0 #b00000000 #b00000000000000000000000)))
(assert (fp.eq ((_ to_fp 8 24) RNE b) x))
(assert (fp.lt ((_ to_fp 11 53) r x) ((_ to_fp 11 53) r y)))
(assert (= b ((_ fp.to_sbv 32) RNE x)))
"#;

#[test]
fn qffp_script_parses_and_sortchecks() {
    let mut ctx = Context::new();
    let mut p = Parser::new(SCRIPT);
    let mut errors = Vec::new();
    loop {
        match p.next_command(&mut ctx) {
            Some(Ok(_cmd)) => {}
            Some(Err(e)) => errors.push(format!("{e:?}")),
            None => break,
        }
    }
    assert!(
        errors.is_empty(),
        "QF_FP script must parse and sort-check without errors:\n{}",
        errors.join("\n")
    );
}
