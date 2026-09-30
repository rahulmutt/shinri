//! SMT-LIB 2.6 string-literal syntax (theory of Unicode strings): decoding a
//! literal's body, `\u` escapes included, and encoding a value back into a
//! literal. Both directions live here so the parser and the model printers
//! agree on one rule set.

/// The largest code point an escape may denote: the top of the SMT-LIB
/// string alphabet. `\u{d₄d₃d₂d₁d₀}` requires `d₄ ∈ [0-2]`, which is exactly
/// this bound.
const MAX_ESCAPE: u32 = 0x2FFFF;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiteralError {
    /// A well-formed escape denotes a surrogate (U+D800..=U+DFFF). The SMT-LIB
    /// alphabet includes these, but `str` cannot hold them. `offset` is the
    /// byte offset of the escape's `\` within the body.
    Surrogate { offset: usize },
}

/// Parse an escape whose leading `\` has already been consumed. On success,
/// return its code point and how many bytes of `s` it spans. `None` means the
/// sequence is not a well-formed 2.6 escape and must be kept literally.
fn parse_escape(s: &str) -> Option<(u32, usize)> {
    let after_u = s.strip_prefix('u')?;
    if let Some(inner) = after_u.strip_prefix('{') {
        // At most 5 digits, so the `}` is within the first 6 bytes. Bounding
        // the search keeps decoding linear on hostile input (Review Focus 3).
        let close = inner.bytes().take(6).position(|b| b == b'}')?;
        let digits = &inner[..close];
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_hexdigit()) {
            return None;
        }
        let code = u32::from_str_radix(digits, 16).ok()?;
        // Only a 5-digit escape can exceed MAX_ESCAPE, and it does so exactly
        // when d₄ > 2.
        if code > MAX_ESCAPE {
            return None;
        }
        return Some((code, "u{".len() + close + "}".len()));
    }
    let digits = after_u.get(..4)?;
    if !digits.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    Some((u32::from_str_radix(digits, 16).ok()?, "u".len() + 4))
}

/// Decode the body of a string literal (the text between the outer quotes):
/// `""` → `"`, and every well-formed `\ud₃d₂d₁d₀` / `\u{d…}` escape → its
/// character. Any other sequence is kept literally, as the standard requires.
pub fn decode_literal(body: &str) -> Result<String, LiteralError> {
    let mut out = String::with_capacity(body.len());
    let mut rest = body;
    while let Some(ch) = rest.chars().next() {
        let offset = body.len() - rest.len();
        if ch == '"' && rest[1..].starts_with('"') {
            out.push('"');
            rest = &rest[2..];
            continue;
        }
        if ch == '\\' {
            if let Some((code, len)) = parse_escape(&rest[1..]) {
                if (0xD800..=0xDFFF).contains(&code) {
                    return Err(LiteralError::Surrogate { offset });
                }
                out.push(char::from_u32(code).expect("non-surrogate code ≤ U+2FFFF is a char"));
                rest = &rest[1 + len..];
                continue;
            }
        }
        out.push(ch);
        rest = &rest[ch.len_utf8()..];
    }
    Ok(out)
}

/// Encode `s` as a full SMT-LIB literal, outer quotes included. `"` → `""`;
/// `\` → `\u{5c}`, so no accidental `\u…` can re-parse as an escape; printable
/// ASCII is written as itself; any other char ≤ U+2FFFF → `\u{hex}`. Chars
/// above U+2FFFF have no escape, so they are written raw, and
/// `decode_literal` passes them through unchanged.
pub fn encode_literal(s: &str) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\"\""),
            '\\' => out.push_str(r"\u{5c}"),
            ' '..='~' => out.push(c),
            c if (c as u32) <= MAX_ESCAPE => {
                write!(out, "\\u{{{:x}}}", c as u32).expect("writing to a String cannot fail");
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn dec(body: &str) -> String {
        decode_literal(body).expect("no surrogate")
    }

    #[test]
    fn decode_plain_and_doubled_quote() {
        assert_eq!(dec("abc"), "abc");
        assert_eq!(dec(r#"a""b"#), "a\"b");
        assert_eq!(dec(""), "");
    }

    #[test]
    fn decode_every_escape_form() {
        assert_eq!(dec("\\u0061"), "a");
        assert_eq!(dec(r"\u{61}"), "a");
        assert_eq!(dec(r"\u{061}"), "a");
        assert_eq!(dec(r"\u{0061}"), "a");
        assert_eq!(dec(r"\u{00061}"), "a");
        assert_eq!(dec(r"\u{0}"), "\u{0}");
        assert_eq!(dec(r"\u{A}\u{a}\u000A\u000a"), "\n\n\n\n");
        assert_eq!(dec(r"x\u{5c}y"), "x\\y");
    }

    #[test]
    fn decode_alphabet_boundaries() {
        assert_eq!(dec(r"\u{2FFFF}"), "\u{2FFFF}");
        assert_eq!(dec("\\uD7FF"), "\u{D7FF}");
        assert_eq!(dec(r"\u{d7ff}"), "\u{D7FF}");
        assert_eq!(dec(r"\u{E000}"), "\u{E000}");
        // d₄ = 3: not an escape; kept literally (9 chars).
        assert_eq!(dec(r"\u{30000}"), r"\u{30000}");
    }

    #[test]
    fn decode_keeps_malformed_sequences_literally() {
        for s in [
            r"\u{}",
            r"\u{123456}",
            r"\u12",
            r"\u{12",
            r"\n",
            r"\",
            r"\u",
            r"\u{g}",
            r"\uFFFg",
        ] {
            assert_eq!(dec(s), s, "{s:?} must stay literal");
        }
    }

    #[test]
    fn decode_rescans_after_a_literal_backslash() {
        // The first `\` is literal; the second starts a valid escape.
        assert_eq!(dec(r"\\u{61}"), r"\a");
    }

    #[test]
    fn decode_escape_next_to_doubled_quote() {
        // Review Focus 2: \u{22} is `"`, then `""` is another `"`.
        assert_eq!(dec(r#"\u{22}"""#), "\"\"");
    }

    #[test]
    fn decode_rejects_surrogates_in_both_forms() {
        assert_eq!(
            decode_literal(r"\uD800"),
            Err(LiteralError::Surrogate { offset: 0 })
        );
        assert_eq!(
            decode_literal(r"ab\u{d800}"),
            Err(LiteralError::Surrogate { offset: 2 })
        );
        assert_eq!(
            decode_literal(r"\u{DFFF}"),
            Err(LiteralError::Surrogate { offset: 0 })
        );
        assert_eq!(
            decode_literal(r"é\udbff"),
            Err(LiteralError::Surrogate { offset: 2 })
        );
    }

    #[test]
    fn decode_many_unterminated_escapes_is_linear() {
        // Review Focus 3: a quadratic scan for `}` would hang here.
        let body = r"\u{".repeat(200_000);
        assert_eq!(dec(&body), body);
    }

    #[test]
    fn encode_rules() {
        assert_eq!(encode_literal("ab ~"), r#""ab ~""#);
        assert_eq!(encode_literal("a\"b"), r#""a""b""#);
        assert_eq!(encode_literal("\\"), r#""\u{5c}""#);
        assert_eq!(
            encode_literal("\u{0}\n\u{7f}é"),
            r#""\u{0}\u{a}\u{7f}\u{e9}""#
        );
        assert_eq!(encode_literal("\u{2FFFF}"), r#""\u{2ffff}""#);
        assert_eq!(encode_literal("\u{30000}"), "\"\u{30000}\"");
        assert_eq!(encode_literal(""), r#""""#);
    }

    fn body(lit: &str) -> &str {
        &lit[1..lit.len() - 1]
    }

    proptest! {
        #[test]
        fn encode_then_decode_roundtrips(s in any::<String>()) {
            prop_assert_eq!(decode_literal(body(&encode_literal(&s))), Ok(s));
        }

        #[test]
        fn encode_emits_printable_ascii_or_out_of_alphabet_chars(s in any::<String>()) {
            for c in encode_literal(&s).chars() {
                prop_assert!((' '..='~').contains(&c) || (c as u32) > MAX_ESCAPE, "{:?}", c);
            }
        }
    }
}
