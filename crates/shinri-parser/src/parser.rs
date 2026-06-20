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

    /// Test-only: seed a declared function/constant name → symbol.
    #[cfg(test)]
    pub fn bind_fun(&mut self, name: &str, sym: shinri_core::SymbolId) {
        self.env.add_fun(name, sym);
    }

    fn builtin_for(name: &str) -> Option<shinri_core::BuiltinOp> {
        use shinri_core::BuiltinOp::*;
        Some(match name {
            "not" => Not,
            "and" => And,
            "or" => Or,
            "=>" => Implies,
            "xor" => Xor,
            "=" => Eq,
            "distinct" => Distinct,
            "ite" => Ite,
            "+" => Add,
            "-" => Sub,
            "*" => Mul,
            "<=" => Le,
            "<" => Lt,
            ">=" => Ge,
            ">" => Gt,
            _ => return None,
        })
    }

    /// Coerce integer-literal operands to Real when the application is Real-typed.
    /// Returns the unified arithmetic sort.
    fn unify_arith(ctx: &mut Context, args: &mut [TermId]) -> SortId {
        let real = ctx.real_sort();
        let int = ctx.int_sort();
        let any_real = args.iter().any(|&a| ctx.sort_of(a) == real);
        if any_real {
            for a in args.iter_mut() {
                if ctx.sort_of(*a) == int {
                    if let Some(v) = ctx.numeral_value(*a).cloned() {
                        *a = ctx.mk_numeral(v, real);
                    }
                }
            }
            real
        } else {
            int
        }
    }

    fn mk(
        ctx: &mut Context,
        op: shinri_core::Op,
        args: &[TermId],
        sp: &Span,
    ) -> Result<TermId, Diagnostic> {
        ctx.mk_app(op, args)
            .map_err(|e| Diagnostic::new(sp.clone(), format!("sort error: {e:?}")))
    }

    /// Parse one s-expression term, interning bottom-up.
    pub fn parse_term(&mut self, ctx: &mut Context) -> Result<TermId, Diagnostic> {
        let (tok, sp) = self
            .bump()
            .ok_or_else(|| Diagnostic::new(self.eof..self.eof, "expected term, found EOF"))?;
        let tok = tok.map_err(|_| Diagnostic::new(sp.clone(), "invalid token"))?;
        match tok {
            Token::Numeral(s) => self.parse_atom_numeral(ctx, &s, false, sp),
            Token::Decimal(s) => self.parse_atom_numeral(ctx, &s, true, sp),
            Token::Symbol(name) => self.resolve_leaf(ctx, &name, sp),
            Token::LParen => self.parse_compound(ctx, sp),
            other => Err(Diagnostic::new(sp, format!("unexpected token {other:?}"))),
        }
    }

    fn resolve_leaf(
        &mut self,
        ctx: &mut Context,
        name: &str,
        sp: Span,
    ) -> Result<TermId, Diagnostic> {
        use shinri_core::Op;
        if let Some(t) = self.env.lookup_let(name) {
            return Ok(t);
        }
        match name {
            "true" => return Ok(ctx.mk_const_bool(true)),
            "false" => return Ok(ctx.mk_const_bool(false)),
            _ => {}
        }
        if let Some(sym) = self.env.lookup_fun(name) {
            return Self::mk(ctx, Op::Uninterpreted(sym), &[], &sp);
        }
        Err(Diagnostic::new(sp, format!("undeclared symbol {name}")))
    }

    fn parse_compound(&mut self, ctx: &mut Context, open: Span) -> Result<TermId, Diagnostic> {
        // Head must be a symbol (Phase 1: no higher-order heads).
        let (head, hsp) = match self.bump() {
            Some((Ok(Token::Symbol(s)), sp)) => (s, sp),
            Some((_, sp)) => {
                return Err(Diagnostic::new(sp, "expected an operator symbol after '('"))
            }
            None => {
                return Err(Diagnostic::new(
                    self.eof..self.eof,
                    "unexpected EOF after '('",
                ))
            }
        };

        match head.as_str() {
            "let" => return self.parse_let(ctx),
            "forall" | "exists" | "_" | "as" | "match" => {
                return Err(Diagnostic::new(
                    hsp,
                    format!("unsupported construct: {head}"),
                ));
            }
            _ => {}
        }

        // define-fun macro call?
        if let Some(m) = self.env.lookup_macro(&head).cloned() {
            let args = self.parse_arg_list(ctx)?;
            if args.len() != m.formals.len() {
                return Err(Diagnostic::new(hsp, "macro arity mismatch"));
            }
            return Ok(ctx.substitute(m.body, &m.formals, &args));
        }

        // Uninterpreted function application?
        if let Some(sym) = self.env.lookup_fun(&head) {
            let args = self.parse_arg_list(ctx)?;
            return Self::mk(ctx, shinri_core::Op::Uninterpreted(sym), &args, &open);
        }

        // Built-in operator (with desugaring).
        if head == "/" {
            let args = self.parse_arg_list(ctx)?;
            return self.apply_division(ctx, args, open);
        }
        if Self::builtin_for(&head).is_some() {
            let args = self.parse_arg_list(ctx)?;
            return self.apply_builtin(ctx, &head, args, open);
        }

        Err(Diagnostic::new(hsp, format!("unknown operator {head}")))
    }

    /// Parse terms until the matching ')'.
    fn parse_arg_list(&mut self, ctx: &mut Context) -> Result<Vec<TermId>, Diagnostic> {
        let mut args = Vec::new();
        loop {
            match self.peek() {
                Some((Ok(Token::RParen), _)) => {
                    self.bump();
                    break;
                }
                None => {
                    return Err(Diagnostic::new(
                        self.eof..self.eof,
                        "unexpected EOF in argument list",
                    ))
                }
                _ => args.push(self.parse_term(ctx)?),
            }
        }
        Ok(args)
    }

    fn parse_let(&mut self, ctx: &mut Context) -> Result<TermId, Diagnostic> {
        self.expect_token(&Token::LParen)?; // bindings list
        let mut bindings = Vec::new();
        loop {
            match self.peek() {
                Some((Ok(Token::RParen), _)) => {
                    self.bump();
                    break;
                }
                _ => {
                    self.expect_token(&Token::LParen)?;
                    let (name, _) = self.expect_symbol()?;
                    let value = self.parse_term(ctx)?; // evaluated in OUTER scope
                    self.expect_token(&Token::RParen)?;
                    bindings.push((name, value));
                }
            }
        }
        self.env.push_let(bindings);
        let body = self.parse_term(ctx);
        self.env.pop_let();
        let body = body?;
        self.expect_token(&Token::RParen)?; // close the (let ...)
        Ok(body)
    }

    fn apply_division(
        &mut self,
        ctx: &mut Context,
        args: Vec<TermId>,
        sp: Span,
    ) -> Result<TermId, Diagnostic> {
        use shinri_core::{BuiltinOp, Op};
        if args.len() < 2 {
            return Err(Diagnostic::new(sp, "/ needs >= 2 args"));
        }
        // Left-fold pairwise.
        let mut acc = args[0];
        for &divisor in &args[1..] {
            let dv = ctx.numeral_value(divisor).cloned();
            match (ctx.numeral_value(acc).cloned(), dv) {
                (Some(n), Some(d)) => {
                    // constant / constant -> fold
                    // Borrow fix: bind real_sort first to avoid nested &ctx/&mut ctx borrow.
                    let rs = ctx.real_sort();
                    acc = ctx.mk_numeral(n * d.recip(), rs);
                }
                (None, Some(d)) => {
                    // x / const -> (* recip(d) x)
                    // Borrow fix: bind real_sort first.
                    let rs = ctx.real_sort();
                    let recip = ctx.mk_numeral(d.recip(), rs);
                    let mut operands = vec![recip, acc];
                    Self::unify_arith(ctx, &mut operands);
                    acc = Self::mk(ctx, Op::Builtin(BuiltinOp::Mul), &operands, &sp)?;
                }
                (_, None) => {
                    return Err(Diagnostic::new(
                        sp,
                        "non-linear division (non-constant divisor)",
                    ))
                }
            }
        }
        Ok(acc)
    }

    fn apply_builtin(
        &mut self,
        ctx: &mut Context,
        head: &str,
        mut args: Vec<TermId>,
        sp: Span,
    ) -> Result<TermId, Diagnostic> {
        use shinri_core::{BuiltinOp, Op};
        let op = Self::builtin_for(head).unwrap();
        match op {
            BuiltinOp::And | BuiltinOp::Or => {
                let unit = matches!(op, BuiltinOp::And);
                match args.len() {
                    0 => Ok(ctx.mk_const_bool(unit)),
                    1 => Ok(args[0]),
                    _ => Self::mk(ctx, Op::Builtin(op), &args, &sp),
                }
            }
            BuiltinOp::Implies => {
                if args.len() < 2 {
                    return Err(Diagnostic::new(sp, "=> needs >= 2 args"));
                }
                // right-assoc fold
                let mut acc = *args.last().unwrap();
                for &a in args[..args.len() - 1].iter().rev() {
                    acc = Self::mk(ctx, Op::Builtin(BuiltinOp::Implies), &[a, acc], &sp)?;
                }
                Ok(acc)
            }
            BuiltinOp::Xor => {
                if args.len() < 2 {
                    return Err(Diagnostic::new(sp, "xor needs >= 2 args"));
                }
                let mut acc = args[0];
                for &a in &args[1..] {
                    acc = Self::mk(ctx, Op::Builtin(BuiltinOp::Xor), &[acc, a], &sp)?;
                }
                Ok(acc)
            }
            BuiltinOp::Add | BuiltinOp::Mul => match args.len() {
                0 => Err(Diagnostic::new(sp, "arith op needs >= 1 arg")),
                1 => Ok(args[0]),
                _ => {
                    Self::unify_arith(ctx, &mut args);
                    Self::mk(ctx, Op::Builtin(op), &args, &sp)
                }
            },
            BuiltinOp::Sub => match args.len() {
                0 => Err(Diagnostic::new(sp, "- needs >= 1 arg")),
                1 => {
                    Self::unify_arith(ctx, &mut args);
                    Self::mk(ctx, Op::Builtin(BuiltinOp::Neg), &args, &sp)
                }
                _ => {
                    Self::unify_arith(ctx, &mut args);
                    let mut acc = args[0];
                    for &a in &args[1..] {
                        acc = Self::mk(ctx, Op::Builtin(BuiltinOp::Sub), &[acc, a], &sp)?;
                    }
                    Ok(acc)
                }
            },
            BuiltinOp::Le | BuiltinOp::Lt | BuiltinOp::Ge | BuiltinOp::Gt => {
                if args.len() < 2 {
                    return Err(Diagnostic::new(sp, "relation needs >= 2 args"));
                }
                Self::unify_arith(ctx, &mut args);
                // chain: (and (rel a b) (rel b c) ...)
                let mut conj = Vec::new();
                for w in args.windows(2) {
                    conj.push(Self::mk(ctx, Op::Builtin(op), &[w[0], w[1]], &sp)?);
                }
                if conj.len() == 1 {
                    Ok(conj[0])
                } else {
                    Self::mk(ctx, Op::Builtin(BuiltinOp::And), &conj, &sp)
                }
            }
            BuiltinOp::Eq | BuiltinOp::Distinct => {
                if args.len() < 2 {
                    return Err(Diagnostic::new(sp, "needs >= 2 args"));
                }
                Self::unify_arith(ctx, &mut args); // harmless for non-arith (no int literals)
                Self::mk(ctx, Op::Builtin(op), &args, &sp)
            }
            BuiltinOp::Not => {
                if args.len() != 1 {
                    return Err(Diagnostic::new(sp, "not needs 1 arg"));
                }
                Self::mk(ctx, Op::Builtin(BuiltinOp::Not), &args, &sp)
            }
            BuiltinOp::Ite => {
                if args.len() != 3 {
                    return Err(Diagnostic::new(sp, "ite needs 3 args"));
                }
                Self::unify_arith(ctx, &mut args[1..]); // unify the two branches
                Self::mk(ctx, Op::Builtin(BuiltinOp::Ite), &args, &sp)
            }
            BuiltinOp::Neg => unreachable!("Neg is produced only via unary '-'"),
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

    // Helper: parse a single term from `src` against a context seeded with decls.
    fn parse_one(src: &str, seed: impl FnOnce(&mut Context, &mut Parser)) -> (Context, TermId) {
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        seed(&mut ctx, &mut p);
        let t = p.parse_term(&mut ctx).expect("parses");
        (ctx, t)
    }

    #[test]
    fn folds_constant_division() {
        let (ctx, t) = parse_one("(/ 1 3)", |_, _| {});
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
        assert_eq!(
            ctx.numeral_value(t).unwrap().clone(),
            Rational::new(Integer::from(1i128), Integer::from(3i128))
        );
    }

    #[test]
    fn linear_division_by_constant_becomes_mul() {
        let (ctx, t) = parse_one("(/ x 2)", |ctx, p| {
            let r = ctx.real_sort();
            let sym = ctx.declare_fun("x", &[], r);
            p.bind_fun("x", sym); // test-only accessor (Step 3)
        });
        // (* (1/2) x)
        use shinri_core::{BuiltinOp, Op, TermNode};
        match ctx.term_node(t) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Mul),
                ..
            } => {}
            other => panic!("expected Mul, got {other:?}"),
        }
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
    }

    #[test]
    fn coerces_int_literal_to_real_in_real_context() {
        // (+ x 1) where x : Real  ->  literal 1 coerced to Real, app is Real.
        let (ctx, t) = parse_one("(+ x 1)", |ctx, p| {
            let r = ctx.real_sort();
            let sym = ctx.declare_fun("x", &[], r);
            p.bind_fun("x", sym);
        });
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
    }

    #[test]
    fn let_binding_resolves() {
        let (ctx, t) = parse_one("(let ((y 1.0)) (+ y y))", |_, _| {});
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
    }

    #[test]
    fn chained_relation_desugars_to_and() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let (ctx, t) = parse_one("(< 1.0 2.0 3.0)", |_, _| {});
        match ctx.term_node(t) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::And),
                ..
            } => {}
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn unsupported_quantifier_is_error() {
        let mut ctx = Context::new();
        let mut p = Parser::new("(forall ((x Int)) true)");
        assert!(p.parse_term(&mut ctx).is_err());
    }
}
