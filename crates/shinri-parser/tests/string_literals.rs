//! Slice 51: string literals decode SMT-LIB 2.6 `\u` escapes (spec §3).
use shinri_core::Context;
use shinri_parser::Parser;

/// Parse `src` as one term; return its string-constant value or the
/// diagnostic message.
fn lit(src: &str) -> Result<String, String> {
    let mut ctx = Context::new();
    let mut p = Parser::new(src);
    p.parse_term_pub(&mut ctx)
        .map(|t| {
            ctx.string_const_value(t)
                .expect("a string constant")
                .to_owned()
        })
        .map_err(|d| d.message)
}

#[test]
fn parser_decodes_escapes() {
    assert_eq!(lit(r#""\u{61}bc""#), Ok("abc".to_owned()));
    assert_eq!(lit(r#""\u{a}""#), Ok("\n".to_owned()));
}

#[test]
fn parser_escaped_and_plain_spellings_are_one_term() {
    let mut ctx = Context::new();
    let a = Parser::new(r#""a""#).parse_term_pub(&mut ctx).unwrap();
    let esc = Parser::new(r#""\u{61}""#).parse_term_pub(&mut ctx).unwrap();
    assert_eq!(a, esc, "hash-consing must see one literal");
}

#[test]
fn parser_decodes_escape_next_to_doubled_quote() {
    // Review Focus 2.
    assert_eq!(lit(r#""\u{22}""""#), Ok("\"\"".to_owned()));
}

#[test]
fn parser_keeps_invalid_escape_literally() {
    assert_eq!(lit(r#""\u{30000}""#), Ok(r"\u{30000}".to_owned()));
}

#[test]
fn parser_rejects_surrogate_escape() {
    assert_eq!(
        lit(r#""\u{d800}""#),
        Err("unsupported: surrogate code point in string literal".to_owned())
    );
}

#[test]
fn set_info_with_surrogate_escape_is_not_an_error() {
    // Review Focus 4: attribute values are metadata, not string terms.
    let mut ctx = Context::new();
    let mut p = Parser::new(r#"(set-info :notes "\u{d800}")"#);
    let cmd = p.next_command(&mut ctx).expect("one command");
    assert!(cmd.is_ok(), "set-info must not decode: {cmd:?}");
}
