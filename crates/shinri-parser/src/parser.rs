use crate::env::Env;
use crate::lexer::{Lexer, Span, Token};
use shinri_core::{Context, Rational, SortId, TermId};
use shinri_frontend::Command;
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
    /// Set to `true` after `(exit)` is processed; subsequent `next_command`
    /// calls return `None` immediately.
    stopped: bool,
}

impl<'a> Parser<'a> {
    pub fn new(src: &'a str) -> Self {
        Parser {
            lx: Lexer::new(src),
            peeked: None,
            env: Env::new(),
            eof: src.len(),
            stopped: false,
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

    /// Parse the next top-level command, interning into `ctx`. Returns `None`
    /// at EOF or after `(exit)`. On error, skips to the end of the current
    /// command so the next call resumes cleanly (design §8 recovery).
    ///
    /// Recovery runs exactly once per command: `parse_command_body` returns
    /// `Ok(None)` for `define-fun` (no IR command emitted), and this loop
    /// simply continues — no recursion, no double-recovery.
    pub fn next_command(&mut self, ctx: &mut Context) -> Option<Result<Command, Diagnostic>> {
        loop {
            if self.stopped {
                return None;
            }
            // Skip to the next '(' (tolerate stray tokens); None at EOF.
            loop {
                match self.peek() {
                    None => return None,
                    Some((Ok(Token::LParen), _)) => {
                        self.bump();
                        break;
                    }
                    Some(_) => {
                        self.bump(); // stray token before a command
                    }
                }
            }
            match self.parse_command_body(ctx) {
                Ok(None) => continue, // define-fun: no IR command, fetch next
                Ok(Some(cmd)) => {
                    if matches!(cmd, Command::Exit) {
                        self.stopped = true;
                    }
                    return Some(Ok(cmd));
                }
                Err(d) => {
                    self.recover_to_command_end();
                    return Some(Err(d));
                }
            }
        }
    }

    /// After the opening '(' is consumed, parse the command head + body,
    /// including the closing ')'.
    ///
    /// Returns `Ok(None)` for `define-fun` (no IR command emitted); the caller
    /// loops to fetch the next real command. Returns `Ok(Some(cmd))` for every
    /// other command. Returns `Err` on parse/sort errors — the caller is
    /// responsible for calling `recover_to_command_end` exactly once.
    fn parse_command_body(&mut self, ctx: &mut Context) -> Result<Option<Command>, Diagnostic> {
        let (head, hsp) = self.expect_symbol()?;
        let cmd = match head.as_str() {
            "set-logic" => {
                let (l, _) = self.expect_symbol()?;
                Command::SetLogic(l)
            }
            "declare-sort" => {
                let (name, _) = self.expect_symbol()?;
                let arity = self.expect_numeral_u32()?;
                if arity != 0 {
                    return Err(Diagnostic::new(hsp, "declare-sort arity > 0 unsupported"));
                }
                let s = ctx.declare_sort(&name);
                self.env.add_sort(&name, s);
                Command::DeclareSort { name, arity }
            }
            "declare-const" => {
                let (name, _) = self.expect_symbol()?;
                let result = self.parse_sort(ctx)?;
                let sym = ctx.declare_fun(&name, &[], result);
                self.env.add_fun(&name, sym);
                Command::DeclareFun {
                    name,
                    sym,
                    params: Vec::new(),
                    result,
                }
            }
            "declare-fun" => {
                let (name, _) = self.expect_symbol()?;
                self.expect_token(&Token::LParen)?;
                let mut params = Vec::new();
                while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
                    params.push(self.parse_sort(ctx)?);
                }
                self.bump(); // ')'
                let result = self.parse_sort(ctx)?;
                let sym = ctx.declare_fun(&name, &params, result);
                self.env.add_fun(&name, sym);
                Command::DeclareFun {
                    name,
                    sym,
                    params,
                    result,
                }
            }
            "define-fun" => {
                // parse_define_fun already consumes the define-fun's own closing ')'.
                self.parse_define_fun(ctx)?;
                return Ok(None); // no IR command emitted; caller loops
            }
            "assert" => {
                let t = self.parse_term(ctx)?;
                Command::Assert(t)
            }
            "check-sat" => Command::CheckSat,
            "check-sat-assuming" => {
                self.expect_token(&Token::LParen)?;
                let mut lits = Vec::new();
                while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
                    lits.push(self.parse_term(ctx)?);
                }
                self.bump();
                Command::CheckSatAssuming(lits)
            }
            "push" => Command::Push(self.opt_numeral_u32(1)?),
            "pop" => Command::Pop(self.opt_numeral_u32(1)?),
            "get-model" => Command::GetModel,
            "get-value" => {
                self.expect_token(&Token::LParen)?;
                let mut ts = Vec::new();
                while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
                    ts.push(self.parse_term(ctx)?);
                }
                self.bump();
                Command::GetValue(ts)
            }
            "get-unsat-core" => Command::GetUnsatCore,
            "set-option" => {
                let (k, v) = self.parse_attr()?;
                Command::SetOption {
                    keyword: k,
                    value: v,
                }
            }
            "set-info" => {
                let (k, v) = self.parse_attr()?;
                Command::SetInfo {
                    keyword: k,
                    value: v,
                }
            }
            "get-info" => {
                let (k, _) = self.expect_keyword()?;
                Command::GetInfo(k)
            }
            "echo" => match self.bump() {
                Some((Ok(Token::Str(s)), _)) => Command::Echo(s),
                Some((_, sp)) => return Err(Diagnostic::new(sp, "echo expects a string")),
                None => return Err(Diagnostic::new(self.eof..self.eof, "echo expects a string")),
            },
            "reset" => Command::Reset,
            "exit" => Command::Exit,
            other => {
                return Err(Diagnostic::new(
                    hsp,
                    format!("unsupported command: {other}"),
                ))
            }
        };
        self.expect_token(&Token::RParen)?; // close the command
        Ok(Some(cmd))
    }

    /// `(define-fun f ((x S)…) R body)` — intern body against fresh formal
    /// placeholder consts and store as a macro; emits no command.
    fn parse_define_fun(&mut self, ctx: &mut Context) -> Result<(), Diagnostic> {
        let (name, _) = self.expect_symbol()?;
        self.expect_token(&Token::LParen)?;
        let mut formal_names = Vec::new();
        let mut formals = Vec::new();
        while !matches!(self.peek(), Some((Ok(Token::RParen), _))) {
            self.expect_token(&Token::LParen)?;
            let (pname, _) = self.expect_symbol()?;
            let psort = self.parse_sort(ctx)?;
            // Fresh placeholder const, unique per definition to avoid clashes.
            let fresh = ctx.declare_fun(&format!("@{name}!{pname}"), &[], psort);
            let fresh_t = ctx
                .mk_app(shinri_core::Op::Uninterpreted(fresh), &[])
                .map_err(|e| Diagnostic::new(0..0, format!("{e:?}")))?;
            formal_names.push(pname);
            formals.push(fresh_t);
            self.expect_token(&Token::RParen)?;
        }
        self.bump(); // consume ')'
        let _result_sort = self.parse_sort(ctx)?;
        // Bind formals as let-style names while parsing the body.
        self.env.push_let(
            formal_names
                .into_iter()
                .zip(formals.iter().copied())
                .collect(),
        );
        let body = self.parse_term(ctx);
        self.env.pop_let();
        let body = body?;
        self.expect_token(&Token::RParen)?; // close (define-fun …)
        self.env.add_macro(&name, formals, body);
        Ok(())
    }

    /// Skip to the end of the current command. Called after a parse error to
    /// re-synchronise at the next command boundary. Depth starts at 1 because
    /// the command's opening '(' was already consumed.
    fn recover_to_command_end(&mut self) {
        let mut depth: i32 = 1;
        while depth > 0 {
            match self.bump() {
                None => break,
                Some((Ok(Token::LParen), _)) => depth += 1,
                Some((Ok(Token::RParen), _)) => depth -= 1,
                _ => {}
            }
        }
    }

    fn expect_numeral_u32(&mut self) -> Result<u32, Diagnostic> {
        match self.bump() {
            Some((Ok(Token::Numeral(s)), sp)) => {
                s.parse().map_err(|_| Diagnostic::new(sp, "expected u32"))
            }
            Some((_, sp)) => Err(Diagnostic::new(sp, "expected numeral")),
            None => Err(Diagnostic::new(
                self.eof..self.eof,
                "expected numeral, found EOF",
            )),
        }
    }

    /// Optional trailing numeral (for `push`/`pop`); returns `default` when absent.
    fn opt_numeral_u32(&mut self, default: u32) -> Result<u32, Diagnostic> {
        if let Some((Ok(Token::Numeral(_)), _)) = self.peek() {
            if let Some((Ok(Token::Numeral(s)), sp)) = self.bump() {
                return s.parse().map_err(|_| Diagnostic::new(sp, "expected u32"));
            }
        }
        Ok(default)
    }

    fn expect_keyword(&mut self) -> Result<(String, Span), Diagnostic> {
        match self.bump() {
            Some((Ok(Token::Keyword(k)), sp)) => Ok((k, sp)),
            Some((_, sp)) => Err(Diagnostic::new(sp, "expected :keyword")),
            None => Err(Diagnostic::new(
                self.eof..self.eof,
                "expected :keyword, found EOF",
            )),
        }
    }

    /// `:keyword [value-token]` — capture the value as raw text (Phase 1).
    fn parse_attr(&mut self) -> Result<(String, shinri_frontend::AttrValue), Diagnostic> {
        use shinri_frontend::AttrValue;
        let (k, _) = self.expect_keyword()?;
        // A value is present unless the next token closes the command.
        let val = match self.peek() {
            Some((Ok(Token::RParen), _)) | None => AttrValue::Token(None),
            Some((Ok(tok), _)) => {
                let text = format!("{tok:?}");
                self.bump();
                AttrValue::Token(Some(text))
            }
            Some((Err(()), sp)) => {
                return Err(Diagnostic::new(sp.clone(), "invalid attribute value"))
            }
        };
        Ok((k, val))
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
        use shinri_core::TermNode;
        let (ctx, t) = parse_one("(/ 1 3)", |_, _| {});
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
        assert_eq!(
            ctx.numeral_value(t).unwrap().clone(),
            Rational::new(Integer::from(1i128), Integer::from(3i128))
        );
        // Must be a single Const node — not a deferred Mul App.
        assert!(
            matches!(ctx.term_node(t), TermNode::Const { .. }),
            "expected Const (constant-folded), got {:?}",
            ctx.term_node(t)
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
        use shinri_core::{BuiltinOp, Op, TermNode};
        let (ctx, t) = parse_one("(+ x 1)", |ctx, p| {
            let r = ctx.real_sort();
            let sym = ctx.declare_fun("x", &[], r);
            p.bind_fun("x", sym);
        });
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
        // Both children of the Add must be Real-sorted (integer literal was re-minted).
        let kids = match ctx.term_node(t).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Add),
                args,
                ..
            } => ctx.children(args).to_vec(),
            other => panic!("expected Add App, got {other:?}"),
        };
        for kid in &kids {
            assert_eq!(
                ctx.sort_of(*kid),
                ctx.real_sort(),
                "child {kid:?} should be Real-sorted after coercion"
            );
        }
    }

    #[test]
    fn let_binding_resolves() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let (ctx, t) = parse_one("(let ((y 1.0)) (+ y y))", |_, _| {});
        assert_eq!(ctx.sort_of(t), ctx.real_sort());
        // Body must be an Add with exactly 2 children, both the SAME term id
        // (let substituted the same binding for both uses of y).
        let kids = match ctx.term_node(t).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Add),
                args,
                ..
            } => ctx.children(args).to_vec(),
            other => panic!("expected Add App, got {other:?}"),
        };
        assert_eq!(kids.len(), 2, "Add should have exactly 2 children");
        assert_eq!(
            kids[0], kids[1],
            "both children should be the same TermId (same y binding)"
        );
        // Each child must be the numeral 1.0 (Rational 1/1).
        let expected = Rational::from_int(Integer::from(1i128));
        for kid in &kids {
            assert_eq!(
                ctx.numeral_value(*kid).cloned(),
                Some(expected.clone()),
                "child {kid:?} should have value 1.0"
            );
        }
    }

    #[test]
    fn chained_relation_desugars_to_and() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let (ctx, t) = parse_one("(< 1.0 2.0 3.0)", |_, _| {});
        // Top level must be And.
        let and_args = match ctx.term_node(t).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::And),
                args,
                ..
            } => ctx.children(args).to_vec(),
            other => panic!("expected And, got {other:?}"),
        };
        // Must have exactly 2 conjuncts.
        assert_eq!(
            and_args.len(),
            2,
            "And should have exactly 2 children for (< a b c)"
        );
        // Each conjunct must be a Lt App.
        for child in &and_args {
            assert!(
                matches!(
                    ctx.term_node(*child),
                    TermNode::App {
                        op: Op::Builtin(BuiltinOp::Lt),
                        ..
                    }
                ),
                "each conjunct should be Lt, got {:?}",
                ctx.term_node(*child)
            );
        }
    }

    #[test]
    fn unsupported_quantifier_is_error() {
        let mut ctx = Context::new();
        let mut p = Parser::new("(forall ((x Int)) true)");
        assert!(p.parse_term(&mut ctx).is_err());
    }

    // ── Command-loop + error-recovery tests ────────────────────────────────

    use shinri_frontend::Command;

    fn commands(src: &str) -> Vec<Result<Command, Diagnostic>> {
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        let mut out = Vec::new();
        while let Some(c) = p.next_command(&mut ctx) {
            out.push(c);
        }
        out
    }

    /// Resolution: `(exit)` DOES emit `Command::Exit` before stopping the
    /// stream, so the script has 5 commands, not 4.
    #[test]
    fn parses_a_small_script() {
        let cs = commands(
            "(set-logic QF_LRA)\n(declare-fun x () Real)\n(assert (< x 1.0))\n(check-sat)\n(exit)",
        );
        assert!(matches!(cs[0], Ok(Command::SetLogic(_))));
        assert!(matches!(cs[1], Ok(Command::DeclareFun { .. })));
        assert!(matches!(cs[2], Ok(Command::Assert(_))));
        assert!(matches!(cs[3], Ok(Command::CheckSat)));
        assert!(matches!(cs[4], Ok(Command::Exit)));
        assert_eq!(cs.len(), 5);
    }

    #[test]
    fn exit_emits_then_stops() {
        let cs = commands("(check-sat)\n(exit)\n(check-sat)");
        assert!(matches!(cs[0], Ok(Command::CheckSat)));
        assert!(matches!(cs[1], Ok(Command::Exit)));
        assert_eq!(cs.len(), 2); // nothing after (exit)
    }

    #[test]
    fn error_recovers_to_next_command() {
        // Second command has a sort error; the third must still parse.
        let cs = commands("(declare-fun x () Real)\n(assert (and x x))\n(check-sat)");
        assert!(matches!(cs[0], Ok(Command::DeclareFun { .. })));
        assert!(cs[1].is_err()); // (and x x): x is Real, not Bool
        assert!(matches!(cs[2], Ok(Command::CheckSat)));
    }

    #[test]
    fn define_fun_expands_and_emits_no_command() {
        let cs = commands(
            "(define-fun dbl ((a Real)) Real (+ a a))\n(declare-fun y () Real)\n(assert (= (dbl y) 0.0))\n(check-sat)",
        );
        // define-fun emits nothing; declare/assert/check-sat remain.
        assert!(matches!(cs[0], Ok(Command::DeclareFun { .. })));
        assert!(matches!(cs[1], Ok(Command::Assert(_))));
        assert!(matches!(cs[2], Ok(Command::CheckSat)));
        assert_eq!(cs.len(), 3);
    }

    #[test]
    fn error_recovers_and_continues() {
        // Unknown command; following check-sat must still parse.
        let cs = commands("(bad-command foo bar)\n(check-sat)");
        assert!(cs[0].is_err());
        assert!(matches!(cs[1], Ok(Command::CheckSat)));
    }

    /// Regression: define-fun followed by a bad command must NOT drop the
    /// command after the bad one. Before the fix, double error-recovery caused
    /// `(check-sat)` to be silently consumed.
    #[test]
    fn error_after_define_fun_recovers_to_next_command() {
        let cs = commands("(define-fun f () Bool true)\n(bad-cmd arg)\n(check-sat)");
        assert_eq!(cs.len(), 2, "expected exactly 2 results (err + check-sat)");
        assert!(cs[0].is_err(), "bad-cmd should produce an error");
        assert!(
            matches!(cs[1], Ok(Command::CheckSat)),
            "check-sat should be the second result, got {:?}",
            cs[1]
        );
    }
}
