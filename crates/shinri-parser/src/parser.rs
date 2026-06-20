use crate::env::Env;
use crate::lexer::{Lexer, Span, Token};
use shinri_core::{Context, Rational, SortId, TermId};
use shinri_num::Integer;

/// A recoverable parse / well-sortedness error (design §8). Never panicked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Span,
    pub message: String,
}

impl Diagnostic {
    fn new(span: Span, msg: impl Into<String>) -> Self {
        Diagnostic {
            span,
            message: msg.into(),
        }
    }
}

pub struct Parser<'a> {
    #[allow(dead_code)]
    lx: Lexer<'a>,
    #[allow(dead_code)]
    peeked: Option<(Result<Token, ()>, Span)>,
    /// Resolution context. Lives across commands (declarations persist).
    #[allow(dead_code)]
    env: Env,
    #[allow(dead_code)]
    eof: usize,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str) -> Self {
        Parser {
            lx: Lexer::new(src),
            peeked: None,
            env: Env::new(),
            eof: src.len(),
        }
    }

    #[allow(dead_code)]
    fn peek(&mut self) -> Option<&(Result<Token, ()>, Span)> {
        if self.peeked.is_none() {
            self.peeked = self.lx.next_spanned();
        }
        self.peeked.as_ref()
    }

    #[allow(dead_code)]
    fn bump(&mut self) -> Option<(Result<Token, ()>, Span)> {
        if let Some(t) = self.peeked.take() {
            return Some(t);
        }
        self.lx.next_spanned()
    }

    #[allow(dead_code)]
    fn here(&mut self) -> Span {
        match self.peek() {
            Some((_, sp)) => sp.clone(),
            None => self.eof..self.eof,
        }
    }

    #[allow(dead_code)]
    fn expect_token(&mut self, want: &Token) -> Result<Span, Diagnostic> {
        match self.bump() {
            Some((Ok(t), sp)) if &t == want => Ok(sp),
            Some((_, sp)) => Err(Diagnostic::new(sp, format!("expected {want:?}"))),
            None => Err(Diagnostic::new(
                self.eof..self.eof,
                format!("expected {want:?}, found EOF"),
            )),
        }
    }

    #[allow(dead_code)]
    fn expect_symbol(&mut self) -> Result<(String, Span), Diagnostic> {
        match self.bump() {
            Some((Ok(Token::Symbol(s)), sp)) => Ok((s, sp)),
            Some((_, sp)) => Err(Diagnostic::new(sp, "expected symbol")),
            None => Err(Diagnostic::new(
                self.eof..self.eof,
                "expected symbol, found EOF",
            )),
        }
    }

    /// Parse a sort: `Bool`/`Int`/`Real`/user-declared. Indexed/parameterized
    /// sorts (`(_ BitVec n)`, `(Array …)`) are out of scope → diagnostic.
    #[allow(dead_code)]
    fn parse_sort(&mut self, ctx: &mut Context) -> Result<SortId, Diagnostic> {
        let (name, sp) = self.expect_symbol()?;
        match name.as_str() {
            "Bool" => Ok(ctx.bool_sort()),
            "Int" => Ok(ctx.int_sort()),
            "Real" => Ok(ctx.real_sort()),
            other => self
                .env
                .lookup_sort(other)
                .ok_or_else(|| Diagnostic::new(sp, format!("unknown sort {other}"))),
        }
    }

    /// Build a numeral term from literal text. `is_decimal` selects Real;
    /// integer literals default to Int (caller may re-coerce to Real later).
    #[allow(dead_code)]
    fn parse_atom_numeral(
        &mut self,
        ctx: &mut Context,
        text: &str,
        is_decimal: bool,
        sp: Span,
    ) -> Result<TermId, Diagnostic> {
        if is_decimal {
            let (int_part, frac_part) = text.split_once('.').unwrap();
            let mut numer = Integer::from_str_radix(int_part, 10)
                .map_err(|_| Diagnostic::new(sp.clone(), "bad decimal"))?;
            let mut denom = Integer::one();
            for ch in frac_part.chars() {
                let d = ch
                    .to_digit(10)
                    .ok_or_else(|| Diagnostic::new(sp.clone(), "bad decimal"))?;
                numer = numer * Integer::from(10i128) + Integer::from(d as i128);
                denom *= Integer::from(10i128);
            }
            let val = Rational::new(numer, denom);
            let sort = ctx.real_sort();
            Ok(ctx.mk_numeral(val, sort))
        } else {
            let n = Integer::from_str_radix(text, 10)
                .map_err(|_| Diagnostic::new(sp, "bad numeral"))?;
            let val = Rational::from_int(n);
            let sort = ctx.int_sort();
            Ok(ctx.mk_numeral(val, sort))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_real_decimal_to_rational() {
        let mut ctx = Context::new();
        let mut p = Parser::new("");
        let t = p.parse_atom_numeral(&mut ctx, "1.5", true, 0..3).unwrap();
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
        assert_eq!(
            ctx.numeral_value(t).unwrap().clone(),
            Rational::new(Integer::from(3i128), Integer::from(2i128))
        );
    }

    #[test]
    fn parses_integer_literal_to_int() {
        let mut ctx = Context::new();
        let mut p = Parser::new("");
        let t = p.parse_atom_numeral(&mut ctx, "42", false, 0..2).unwrap();
        assert_eq!(ctx.sort_of(t), ctx.int_sort());
        assert_eq!(
            ctx.numeral_value(t).unwrap().clone(),
            Rational::from_int(Integer::from(42i128))
        );
    }
}
