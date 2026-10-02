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
    roundtrip(r#""\u{22}""""#, |_, _| {});
}

/// Like `roundtrip`, but each parser first consumes `n_decls` declaration
/// commands from `decls` (the parser's symbol environment is per-`Parser`).
fn roundtrip_declared(decls: &str, n_decls: usize, term: &str) {
    let mut ctx = Context::new();
    let src1 = format!("{decls} {term}");
    let mut p1 = Parser::new(&src1);
    for _ in 0..n_decls {
        p1.next_command(&mut ctx).unwrap().expect("decl 1");
    }
    let t1 = p1.parse_term_pub(&mut ctx).expect("parse 1");
    let printed = print_term(&ctx, t1);
    let src2 = format!("{decls} {printed}");
    let mut p2 = Parser::new(&src2);
    for _ in 0..n_decls {
        p2.next_command(&mut ctx).unwrap().expect("decl 2");
    }
    let t2 = p2.parse_term_pub(&mut ctx).expect("parse 2");
    assert_eq!(
        t1, t2,
        "roundtrip changed the term: {term:?} -> {printed:?}"
    );
}

#[test]
fn roundtrips_quoted_symbols_and_nullary_builtins() {
    let decls = "(declare-sort |my sort| 0)(declare-fun |a#b| () |my sort|)\
                 (declare-fun |let| () Int)(declare-fun |f g| (Int) Int)\
                 (declare-fun s () String)";
    for term in [
        "|a#b|",
        "(|f g| |let|)",
        "(+ (|f g| 1) (- 3))",
        "(str.in_re s re.none)",
        "(str.in_re s (re.++ re.allchar re.all))",
    ] {
        roundtrip_declared(decls, 5, term);
    }
}
