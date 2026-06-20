use logos::Logos;

/// Byte-range span into the source, used for diagnostics.
pub type Span = core::ops::Range<usize>;

/// SMT-LIB 2.6 lexical tokens. `#x`/`#b` are lexed but rejected by the parser
/// (no bit-vectors in Phase 1). Unrecognized input yields a lexer error, which
/// the parser turns into a `Diagnostic` (never a panic).
#[derive(Logos, Clone, Debug, PartialEq, Eq)]
#[logos(skip r"[ \t\r\n]+")] // whitespace
#[logos(skip r";[^\n]*")] // line comments
pub enum Token {
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[regex(r"[0-9]+", |lex| lex.slice().to_owned())]
    Numeral(String),
    #[regex(r"[0-9]+\.[0-9]+", |lex| lex.slice().to_owned())]
    Decimal(String),
    #[regex(r"#x[0-9a-fA-F]+", |lex| lex.slice().to_owned())]
    Hex(String),
    #[regex(r"#b[01]+", |lex| lex.slice().to_owned())]
    Bin(String),
    #[regex(r#""([^"]|"")*""#, |lex| lex.slice().to_owned())]
    Str(String),
    #[regex(r":[a-zA-Z0-9~!@$%^&*_+=<>.?/-]+", |lex| lex.slice().to_owned())]
    Keyword(String),
    // Simple symbols and quoted |...| symbols.
    #[regex(r"[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]*", |lex| lex.slice().to_owned())]
    #[regex(r"\|[^|\\]*\|", |lex| { let s = lex.slice(); s[1..s.len()-1].to_owned() })]
    Symbol(String),
}

/// Thin wrapper over `logos::Lexer` yielding `(Result<Token, ()>, Span)`.
pub struct Lexer<'a> {
    inner: logos::Lexer<'a, Token>,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Lexer {
            inner: Token::lexer(src),
        }
    }
    /// Next token with its span, or `None` at end of input.
    pub fn next_spanned(&mut self) -> Option<(Result<Token, ()>, Span)> {
        let tok = self.inner.next()?;
        let span = self.inner.span();
        Some((tok.map_err(|_| ()), span))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(src: &str) -> Vec<Token> {
        let mut lx = Lexer::new(src);
        let mut out = Vec::new();
        while let Some((t, _)) = lx.next_spanned() {
            out.push(t.expect("lexes cleanly"));
        }
        out
    }

    #[test]
    fn lexes_basic_forms() {
        assert_eq!(
            toks("(assert (= x 1.5)) ; comment\n"),
            vec![
                Token::LParen,
                Token::Symbol("assert".into()),
                Token::LParen,
                Token::Symbol("=".into()),
                Token::Symbol("x".into()),
                Token::Decimal("1.5".into()),
                Token::RParen,
                Token::RParen,
            ]
        );
        assert_eq!(
            toks(":produce-models"),
            vec![Token::Keyword(":produce-models".into())]
        );
        assert_eq!(
            toks("|quoted sym|"),
            vec![Token::Symbol("quoted sym".into())]
        );
    }

    #[test]
    fn unrecognized_byte_is_error_not_panic() {
        let mut lx = Lexer::new("\u{0}");
        assert!(matches!(lx.next_spanned(), Some((Err(()), _))));
    }
}
