use shinri_core::Context;
use shinri_parser::{print_term, Parser};

/// Parse `src` as a single term, print it, re-parse, and require identical ids.
fn roundtrip(src: &str, seed: impl Fn(&mut Context, &mut Parser)) {
    let mut ctx = Context::new();
    let mut p1 = Parser::new(src);
    seed(&mut ctx, &mut p1);
    let t1 = p1.parse_term_pub(&mut ctx).expect("parse 1");
    let printed = print_term(&ctx, t1);
    let mut p2 = Parser::new(&printed);
    seed(&mut ctx, &mut p2);
    let t2 = p2.parse_term_pub(&mut ctx).expect("parse 2");
    assert_eq!(t1, t2, "roundtrip changed the term: {src:?} -> {printed:?}");
}

#[test]
fn roundtrips_core_terms() {
    roundtrip("(and true false)", |_, _| {});
    roundtrip("(+ 1.0 (* 2.0 3.0))", |_, _| {});
    roundtrip("(ite true 1.0 2.0)", |_, _| {});
    roundtrip("(= 1.0 1.0)", |_, _| {});
}

#[test]
fn roundtrips_string_literals_with_escapes() {
    // Slice 51: print must re-encode so that re-parse yields the same TermId.
    roundtrip(r#""plain""#, |_, _| {});
    roundtrip(r#""a""b""#, |_, _| {});
    roundtrip(r#""\u{0}\u{a}\u{7f}é""#, |_, _| {});
    // A decoded backslash followed by `u{61}` must NOT re-parse as "a".
    roundtrip(r#""\u{5c}u{61}""#, |_, _| {});
    roundtrip(r#""\u{2FFFF}""#, |_, _| {});
}
