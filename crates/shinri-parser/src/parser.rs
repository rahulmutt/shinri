use crate::env::Env;
use crate::lexer::{Lexer, Span, Token};
use shinri_core::{Context, Rational, SortId, TermId};
use shinri_frontend::Command;
use shinri_num::Integer;

/// IEEE special-value kinds that the `(_ <kind> eb sb)` syntax can name.
#[derive(Clone, Copy)]
enum FpSpecial {
    PosInf,
    NegInf,
    PosZero,
    NegZero,
    Nan,
}

/// 2^k as an Integer (k may exceed 127, so build it generally via a loop).
fn pow2(k: u32) -> Integer {
    let mut acc = Integer::one();
    let two = Integer::from(2u64);
    for _ in 0..k {
        acc *= two.clone();
    }
    acc
}

/// Canonical W = eb+sb bit pattern for an FP special value.
/// Layout MSB->LSB: [ sign(1) | exp(eb) | trailing-sig(sb-1) ].
fn fp_special_bits(eb: u32, sb: u32, kind: FpSpecial) -> Integer {
    let w = eb + sb;
    let sign_bit = pow2(w - 1); // bit (W-1)
    let exp_all_ones = (pow2(eb) - Integer::one()) * pow2(sb - 1); // exp field set, sig 0
    let quiet_bit = pow2(sb - 2); // MSB of the (sb-1)-bit trailing sig
    match kind {
        FpSpecial::PosZero => Integer::zero(),
        FpSpecial::NegZero => sign_bit,
        FpSpecial::PosInf => exp_all_ones,
        FpSpecial::NegInf => sign_bit + exp_all_ones,
        FpSpecial::Nan => exp_all_ones + quiet_bit, // sign=0, canonical quiet NaN
    }
}

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

/// Reject a user `declare-fun`/`declare-const` that names a solver-internal
/// (reserved) symbol. Without this, the user's nullary app would hash-cons to
/// the same TermId as the internal symbol (e.g. word_norm's `ite!<n>`) and
/// silently inherit its definition — a wrong-UNSAT (slice 5 final review).
fn reject_reserved(ctx: &Context, name: &str, sp: &Span) -> Result<(), Diagnostic> {
    if let Some(sym) = ctx.lookup_symbol(name) {
        if ctx.is_reserved(sym) {
            return Err(Diagnostic::new(
                sp.clone(),
                format!("cannot declare '{name}': name is reserved for solver-internal use"),
            ));
        }
    }
    Ok(())
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

/// The semantic text of an attribute-value token: the inner string for
/// symbols/numerals/decimals/keywords/hex/bin, and the quote-stripped,
/// `""`-unescaped contents for string literals.
fn token_value_text(tok: &Token) -> String {
    match tok {
        Token::Symbol(s)
        | Token::Numeral(s)
        | Token::Decimal(s)
        | Token::Keyword(s)
        | Token::Hex(s)
        | Token::Bin(s) => s.clone(),
        Token::Str(s) => s[1..s.len() - 1].replace("\"\"", "\""),
        Token::LParen => "(".to_string(),
        Token::RParen => ")".to_string(),
    }
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

    /// Build a parser over `src` seeded with an existing resolution `env`.
    /// Used by `StreamingParser` to parse one command slice at a time while
    /// keeping declarations alive across commands.
    pub(crate) fn with_env(src: &'a str, env: Env) -> Self {
        Parser {
            lx: Lexer::new(src),
            peeked: None,
            env,
            eof: src.len(),
            stopped: false,
        }
    }

    /// Recover the resolution environment after parsing a command slice.
    pub(crate) fn into_env(self) -> Env {
        self.env
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

    /// Consume a `(` if present; returns `true` if consumed, `false` otherwise.
    fn eat_lparen(&mut self) -> bool {
        if matches!(self.peek(), Some((Ok(Token::LParen), _))) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// Parse a sort: `Bool`/`Int`/`Real`/user-declared, or the compound
    /// `(Array <index> <element>)` or `(_ BitVec n)` sort.
    #[allow(dead_code)]
    fn parse_sort(&mut self, ctx: &mut Context) -> Result<SortId, Diagnostic> {
        // Compound sort: (Array <index> <element>) or (_ BitVec n)
        if self.eat_lparen() {
            let (head, sp) = self.expect_symbol()?;
            let s = match head.as_str() {
                "Array" => {
                    let index = self.parse_sort(ctx)?;
                    let elem = self.parse_sort(ctx)?;
                    ctx.array_sort(index, elem)
                }
                "_" => {
                    // (_ BitVec n) or (_ FloatingPoint eb sb) — SMT-LIB indexed sorts
                    let (kw, ksp) = self.expect_symbol()?;
                    match kw.as_str() {
                        "BitVec" => {
                            let width = self.expect_numeral_u32()?;
                            if width == 0 {
                                return Err(Diagnostic::new(sp, "BitVec width must be >= 1"));
                            }
                            ctx.bv_sort(width)
                        }
                        "FloatingPoint" => {
                            let eb = self.expect_numeral_u32()?;
                            let sb = self.expect_numeral_u32()?;
                            if eb < 2 || sb < 2 {
                                return Err(Diagnostic::new(
                                    sp,
                                    "FloatingPoint requires eb>=2, sb>=2",
                                ));
                            }
                            ctx.fp_sort(eb, sb)
                        }
                        other => {
                            return Err(Diagnostic::new(
                                ksp,
                                format!("unsupported indexed sort identifier {other}"),
                            ));
                        }
                    }
                }
                other => {
                    return Err(Diagnostic::new(
                        sp,
                        format!("unsupported parameterized sort {other}"),
                    ));
                }
            };
            self.expect_token(&Token::RParen)?;
            return Ok(s);
        }
        let (name, sp) = self.expect_symbol()?;
        match name.as_str() {
            "Bool" => Ok(ctx.bool_sort()),
            "Int" => Ok(ctx.int_sort()),
            "Real" => Ok(ctx.real_sort()),
            "String" => Ok(ctx.string_sort()),
            "Float16" => Ok(ctx.fp_sort(5, 11)),
            "Float32" => Ok(ctx.fp_sort(8, 24)),
            "Float64" => Ok(ctx.fp_sort(11, 53)),
            "Float128" => Ok(ctx.fp_sort(15, 113)),
            "RoundingMode" => Ok(ctx.rm_sort()),
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
            "select" => Select,
            "store" => Store,
            // BV non-indexed operators (SMT-LIB QF_BV)
            "bvnot" => BvNot,
            "bvand" => BvAnd,
            "bvor" => BvOr,
            "bvxor" => BvXor,
            "bvnand" => BvNand,
            "bvnor" => BvNor,
            "bvxnor" => BvXnor,
            "bvneg" => BvNeg,
            "bvadd" => BvAdd,
            "bvsub" => BvSub,
            "bvmul" => BvMul,
            "bvudiv" => BvUdiv,
            "bvurem" => BvUrem,
            "bvsdiv" => BvSdiv,
            "bvsrem" => BvSrem,
            "bvsmod" => BvSmod,
            "bvshl" => BvShl,
            "bvlshr" => BvLshr,
            "bvashr" => BvAshr,
            "bvult" => BvUlt,
            "bvule" => BvUle,
            "bvugt" => BvUgt,
            "bvuge" => BvUge,
            "bvslt" => BvSlt,
            "bvsle" => BvSle,
            "bvsgt" => BvSgt,
            "bvsge" => BvSge,
            "concat" => BvConcat,
            // String operators (QF_S / SLIA)
            "str.++" => StrConcat,
            "str.len" => StrLen,
            "str.at" => StrAt,
            "str.substr" => StrSubstr,
            "str.prefixof" => StrPrefixOf,
            "str.suffixof" => StrSuffixOf,
            "str.contains" => StrContains,
            // Floating-point bit constructor (SMT-LIB QF_FP)
            "fp" => FpFromBits,
            // Floating-point arithmetic and classification operators (QF_FP)
            "fp.abs" => FpAbs,
            "fp.neg" => FpNeg,
            "fp.add" => FpAdd,
            "fp.sub" => FpSub,
            "fp.mul" => FpMul,
            "fp.div" => FpDiv,
            "fp.fma" => FpFma,
            "fp.sqrt" => FpSqrt,
            "fp.rem" => FpRem,
            "fp.roundToIntegral" => FpRoundToIntegral,
            "fp.min" => FpMin,
            "fp.max" => FpMax,
            "fp.leq" => FpLeq,
            "fp.lt" => FpLt,
            "fp.geq" => FpGeq,
            "fp.gt" => FpGt,
            "fp.eq" => FpEq,
            "fp.isNormal" => FpIsNormal,
            "fp.isSubnormal" => FpIsSubnormal,
            "fp.isZero" => FpIsZero,
            "fp.isInfinite" => FpIsInfinite,
            "fp.isNaN" => FpIsNaN,
            "fp.isNegative" => FpIsNegative,
            "fp.isPositive" => FpIsPositive,
            // Floating-point non-indexed conversion
            "fp.to_real" => FpToReal,
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

    /// Public single-term entry point (used by the round-trip test).
    pub fn parse_term_pub(&mut self, ctx: &mut Context) -> Result<TermId, Diagnostic> {
        self.parse_term(ctx)
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
            Token::Hex(s) => {
                // #xHH... — hex digits after "#x"; width = 4 * number_of_digits
                let digits = &s[2..]; // strip "#x"
                let width = (digits.len() as u32) * 4;
                let value = Integer::from_str_radix(digits, 16)
                    .map_err(|_| Diagnostic::new(sp, "invalid hex literal"))?;
                Ok(ctx.mk_bv_const(width, value))
            }
            Token::Bin(s) => {
                // #bBB... — binary digits after "#b"; width = number_of_digits
                let digits = &s[2..]; // strip "#b"
                let width = digits.len() as u32;
                let value = Integer::from_str_radix(digits, 2)
                    .map_err(|_| Diagnostic::new(sp, "invalid binary literal"))?;
                Ok(ctx.mk_bv_const(width, value))
            }
            Token::Str(s) => {
                // Strip outer quotes and unescape "" -> " (SMT-LIB string literal syntax).
                let raw = &s[1..s.len() - 1];
                let val = raw.replace("\"\"", "\"");
                Ok(ctx.mk_string_const(&val))
            }
            Token::Symbol(name) => self.resolve_leaf(ctx, &name, sp),
            Token::LParen => self.parse_compound(ctx, sp),
            other => Err(Diagnostic::new(sp, format!("unexpected token {other:?}"))),
        }
    }

    /// Parse the body of an indexed identifier `(_ <id> <nums...>)` where the
    /// `_` has already been consumed.  Returns the corresponding `BuiltinOp`.
    ///
    /// Handles: `extract i j`, `zero_extend k`, `sign_extend k`,
    /// `rotate_left k`, `rotate_right k`, `repeat k`.
    fn parse_indexed_op(&mut self, usp: Span) -> Result<shinri_core::BuiltinOp, Diagnostic> {
        use shinri_core::BuiltinOp::*;
        let (id, isp) = self.expect_symbol()?;
        let op = match id.as_str() {
            "extract" => {
                let hi = self.expect_numeral_u32()?;
                let lo = self.expect_numeral_u32()?;
                BvExtract { hi, lo }
            }
            "zero_extend" => BvZeroExtend(self.expect_numeral_u32()?),
            "sign_extend" => BvSignExtend(self.expect_numeral_u32()?),
            "rotate_left" => BvRotateLeft(self.expect_numeral_u32()?),
            "rotate_right" => BvRotateRight(self.expect_numeral_u32()?),
            "repeat" => BvRepeat(self.expect_numeral_u32()?),
            // Floating-point indexed conversions
            "to_fp" => {
                let eb = self.expect_numeral_u32()?;
                let sb = self.expect_numeral_u32()?;
                ToFp { eb, sb }
            }
            "to_fp_unsigned" => {
                let eb = self.expect_numeral_u32()?;
                let sb = self.expect_numeral_u32()?;
                ToFpUnsigned { eb, sb }
            }
            "fp.to_ubv" => FpToUbv(self.expect_numeral_u32()?),
            "fp.to_sbv" => FpToSbv(self.expect_numeral_u32()?),
            other => {
                return Err(Diagnostic::new(
                    isp,
                    format!("unknown indexed identifier '_{other}'"),
                ));
            }
        };
        let _ = usp;
        Ok(op)
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
            "RNE" | "roundNearestTiesToEven" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rne));
            }
            "RNA" | "roundNearestTiesToAway" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rna));
            }
            "RTP" | "roundTowardPositive" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rtp));
            }
            "RTN" | "roundTowardNegative" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rtn));
            }
            "RTZ" | "roundTowardZero" => {
                return Ok(ctx.mk_rm_const(shinri_core::term::RoundingMode::Rtz));
            }
            _ => {}
        }
        // define-fun macro used as a bare symbol: a 0-ary macro expands to its
        // body (SMT-LIB conformance — slice 6); a non-nullary macro needs
        // application form. Checked after the builtin literals (true/false/RM
        // can't be shadowed) and before lookup_fun, honoring the documented
        // let → macro → fun order (env.rs).
        if let Some(m) = self.env.lookup_macro(name) {
            if m.formals.is_empty() {
                return Ok(m.body);
            }
            let n = m.formals.len();
            return Err(Diagnostic::new(
                sp,
                format!("macro {name} expects {n} argument(s)"),
            ));
        }
        if let Some(sym) = self.env.lookup_fun(name) {
            return Self::mk(ctx, Op::Uninterpreted(sym), &[], &sp);
        }
        Err(Diagnostic::new(sp, format!("undeclared symbol {name}")))
    }

    fn parse_compound(&mut self, ctx: &mut Context, open: Span) -> Result<TermId, Diagnostic> {
        // Peek: if the head is '(' it may be an indexed operator `((_ id nums...) args...)`.
        if matches!(self.peek(), Some((Ok(Token::LParen), _))) {
            self.bump(); // consume inner '('
                         // Expect '_' to start an indexed identifier used as an operator.
            let (under, usp) = self.expect_symbol()?;
            if under != "_" {
                return Err(Diagnostic::new(usp, "expected '_' in indexed identifier"));
            }
            let op = self.parse_indexed_op(usp.clone())?;
            // consume closing ')' of the indexed identifier
            self.expect_token(&Token::RParen)?;
            // now parse the argument(s) and the outer closing ')'
            let args = self.parse_arg_list(ctx)?;
            return Self::mk(ctx, shinri_core::Op::Builtin(op), &args, &open);
        }

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
            "forall" | "exists" | "as" | "match" => {
                return Err(Diagnostic::new(
                    hsp,
                    format!("unsupported construct: {head}"),
                ));
            }
            // `(_ id nums...)` in term position: `(_ bvK n)` is a BV literal;
            // `(_ +oo eb sb)` / `(_ -oo eb sb)` / `(_ +zero eb sb)` /
            // `(_ -zero eb sb)` / `(_ NaN eb sb)` are FP special literals.
            "_" => {
                let (id, isp) = self.expect_symbol()?;
                let result = match id.as_str() {
                    "+oo" | "-oo" | "+zero" | "-zero" | "NaN" => {
                        let eb = self.expect_numeral_u32()?;
                        let sb = self.expect_numeral_u32()?;
                        if eb < 2 || sb < 2 {
                            return Err(Diagnostic::new(
                                isp,
                                "FloatingPoint requires eb>=2, sb>=2",
                            ));
                        }
                        let kind = match id.as_str() {
                            "+oo" => FpSpecial::PosInf,
                            "-oo" => FpSpecial::NegInf,
                            "+zero" => FpSpecial::PosZero,
                            "-zero" => FpSpecial::NegZero,
                            _ => FpSpecial::Nan,
                        };
                        ctx.mk_fp_const(eb, sb, fp_special_bits(eb, sb, kind))
                    }
                    sym if sym.starts_with("bv") => {
                        // (_ bvK n) BV numeral — preserve existing behavior.
                        let k_str = &sym[2..];
                        let k: u64 = k_str.parse().map_err(|_| {
                            Diagnostic::new(
                                isp.clone(),
                                format!("invalid BV numeral suffix `{k_str}`"),
                            )
                        })?;
                        let width = self.expect_numeral_u32()?;
                        if width == 0 {
                            return Err(Diagnostic::new(isp, "BV numeral width must be >= 1"));
                        }
                        ctx.mk_bv_const(width, Integer::from(k))
                    }
                    other => {
                        return Err(Diagnostic::new(
                            isp,
                            format!("unknown indexed literal `_ {other}`"),
                        ));
                    }
                };
                self.expect_token(&Token::RParen)?;
                return Ok(result);
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
            BuiltinOp::Select => {
                if args.len() != 2 {
                    return Err(Diagnostic::new(sp, "select expects 2 arguments"));
                }
                Self::mk(ctx, Op::Builtin(BuiltinOp::Select), &args, &sp)
            }
            BuiltinOp::Store => {
                if args.len() != 3 {
                    return Err(Diagnostic::new(sp, "store expects 3 arguments"));
                }
                Self::mk(ctx, Op::Builtin(BuiltinOp::Store), &args, &sp)
            }
            // BV non-indexed binary/unary ops: delegate directly to mk_app
            // (sort-checking is in Context::sort_of_app).
            BuiltinOp::BvNot
            | BuiltinOp::BvNeg
            | BuiltinOp::BvAnd
            | BuiltinOp::BvOr
            | BuiltinOp::BvXor
            | BuiltinOp::BvNand
            | BuiltinOp::BvNor
            | BuiltinOp::BvXnor
            | BuiltinOp::BvAdd
            | BuiltinOp::BvSub
            | BuiltinOp::BvMul
            | BuiltinOp::BvUdiv
            | BuiltinOp::BvUrem
            | BuiltinOp::BvSdiv
            | BuiltinOp::BvSrem
            | BuiltinOp::BvSmod
            | BuiltinOp::BvShl
            | BuiltinOp::BvLshr
            | BuiltinOp::BvAshr
            | BuiltinOp::BvUlt
            | BuiltinOp::BvUle
            | BuiltinOp::BvUgt
            | BuiltinOp::BvUge
            | BuiltinOp::BvSlt
            | BuiltinOp::BvSle
            | BuiltinOp::BvSgt
            | BuiltinOp::BvSge
            | BuiltinOp::BvConcat
            | BuiltinOp::BvExtract { .. }
            | BuiltinOp::BvZeroExtend(_)
            | BuiltinOp::BvSignExtend(_)
            | BuiltinOp::BvRotateLeft(_)
            | BuiltinOp::BvRotateRight(_)
            | BuiltinOp::BvRepeat(_) => Self::mk(ctx, Op::Builtin(op), &args, &sp),
            // String ops: delegate directly to mk_app (sort-checking in Context).
            BuiltinOp::StrConcat | BuiltinOp::StrLen | BuiltinOp::StrAt | BuiltinOp::StrSubstr => {
                Self::mk(ctx, Op::Builtin(op), &args, &sp)
            }
            // String predicates (slice 12): delegate directly to mk_app (sort-checking
            // in Context). Not yet reachable via `builtin_for` — parser wiring is Task 3.
            BuiltinOp::StrPrefixOf | BuiltinOp::StrSuffixOf | BuiltinOp::StrContains => {
                Self::mk(ctx, Op::Builtin(op), &args, &sp)
            }
            // Floating-point ops: delegate directly to mk_app (sort-checking in Context).
            BuiltinOp::FpAbs
            | BuiltinOp::FpNeg
            | BuiltinOp::FpAdd
            | BuiltinOp::FpSub
            | BuiltinOp::FpMul
            | BuiltinOp::FpDiv
            | BuiltinOp::FpFma
            | BuiltinOp::FpSqrt
            | BuiltinOp::FpRoundToIntegral
            | BuiltinOp::FpRem
            | BuiltinOp::FpMin
            | BuiltinOp::FpMax
            | BuiltinOp::FpLeq
            | BuiltinOp::FpLt
            | BuiltinOp::FpGeq
            | BuiltinOp::FpGt
            | BuiltinOp::FpEq
            | BuiltinOp::FpIsNormal
            | BuiltinOp::FpIsSubnormal
            | BuiltinOp::FpIsZero
            | BuiltinOp::FpIsInfinite
            | BuiltinOp::FpIsNaN
            | BuiltinOp::FpIsNegative
            | BuiltinOp::FpIsPositive
            | BuiltinOp::FpFromBits => Self::mk(ctx, Op::Builtin(op), &args, &sp),
            // Floating-point conversion ops: delegate directly to mk_app.
            // Indexed variants (ToFp/ToFpUnsigned/FpToUbv/FpToSbv) are reached via
            // parse_indexed_op, not builtin_for; FpToReal is reached via builtin_for.
            BuiltinOp::ToFp { .. }
            | BuiltinOp::ToFpUnsigned { .. }
            | BuiltinOp::FpToUbv(_)
            | BuiltinOp::FpToSbv(_)
            | BuiltinOp::FpToReal => Self::mk(ctx, Op::Builtin(op), &args, &sp),
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
                let (name, nsp) = self.expect_symbol()?;
                reject_reserved(ctx, &name, &nsp)?;
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
                let (name, nsp) = self.expect_symbol()?;
                reject_reserved(ctx, &name, &nsp)?;
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
            Some((Err(()), sp)) => {
                return Err(Diagnostic::new(sp.clone(), "invalid attribute value"))
            }
            Some((Ok(_), _)) => {
                // A value token is present; consume it and capture its text.
                let (tok, _) = self.bump().expect("peek saw a token");
                let tok = tok.expect("peek saw Ok(token)");
                AttrValue::Token(Some(token_value_text(&tok)))
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
    fn nullary_define_fun_expands_as_bare_symbol() {
        // SMT-LIB: a 0-ary defined fun is used WITHOUT parens. Gap fixed in
        // slice 6 — resolve_leaf never consulted the macro table.
        let cs = commands(
            "(define-fun one () Int 1)\n(declare-fun y () Int)\n(assert (= y one))\n(check-sat)",
        );
        assert!(matches!(cs[0], Ok(Command::DeclareFun { .. })));
        assert!(matches!(cs[1], Ok(Command::Assert(_))));
        assert!(matches!(cs[2], Ok(Command::CheckSat)));
        assert_eq!(cs.len(), 3);
    }

    #[test]
    fn non_nullary_macro_bare_use_is_an_error() {
        let cs = commands(
            "(define-fun dbl ((a Real)) Real (+ a a))\n(declare-fun y () Real)\n(assert (= y dbl))",
        );
        assert!(
            cs.iter().any(|c| c.is_err()),
            "bare use of a non-nullary macro must be a diagnostic"
        );
    }

    #[test]
    fn error_recovers_and_continues() {
        // Unknown command; following check-sat must still parse.
        let cs = commands("(bad-command foo bar)\n(check-sat)");
        assert!(cs[0].is_err());
        assert!(matches!(cs[1], Ok(Command::CheckSat)));
    }

    /// Helper: parse all commands from `src`, asserting no diagnostic errors.
    /// Returns (ctx, commands).
    fn parse_all_ok(src: &str) -> (Context, Vec<Command>) {
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        let mut cmds = Vec::new();
        while let Some(c) = p.next_command(&mut ctx) {
            cmds.push(c.expect("unexpected parse error"));
        }
        (ctx, cmds)
    }

    /// Task-4 TDD test: `(_ BitVec n)` sort, `#x` hex literals, `#b` binary
    /// literals are parsed correctly and produce the right BV constants.
    ///
    /// Non-vacuous assertions:
    ///   - declare-const x (_ BitVec 8): the declared sort is exactly bv_sort(8).
    ///   - (assert (= x #xFF)): #xFF parses without error; `bv_const_value` confirms
    ///     width=8, value=255.
    ///   - (assert (= x #b11111111)): #b11111111 parses without error; confirms
    ///     width=8, value=255 (same BV const as #xFF → same TermId).
    ///   - standalone parse_term: #b1010 gives width=4, value=10.
    #[test]
    fn parses_bv_sort_and_hex_binary_literals() {
        // --- Part 1: full command pipeline ---
        let src = "(declare-const x (_ BitVec 8))\n\
                   (assert (= x #xFF))\n\
                   (assert (= x #b11111111))\n";
        let (mut ctx, cmds) = parse_all_ok(src);

        // Three commands must have been produced.
        assert_eq!(cmds.len(), 3, "expected 3 commands");
        assert!(matches!(cmds[0], Command::DeclareFun { .. }));
        assert!(matches!(cmds[1], Command::Assert(_)));
        assert!(matches!(cmds[2], Command::Assert(_)));

        // The declared constant has the BitVec(8) sort.
        if let Command::DeclareFun { result, .. } = &cmds[0] {
            assert_eq!(
                *result,
                ctx.bv_sort(8),
                "declare-const must have BitVec(8) sort"
            );
        }

        // --- Part 2: direct literal parsing for precise value assertions ---
        // #xFF — 8-bit hex, value 255.
        {
            let mut ctx2 = Context::new();
            let mut p = Parser::new("#xFF");
            let t = p.parse_term(&mut ctx2).expect("#xFF must parse");
            let (w, v) = ctx2.bv_const_value(t).expect("#xFF must be a BV const");
            assert_eq!(w, 8, "#xFF width must be 8");
            assert_eq!(*v, Integer::from(255u64), "#xFF value must be 255");
        }

        // #b1010 — 4-bit binary, value 10.
        {
            let mut ctx2 = Context::new();
            let mut p = Parser::new("#b1010");
            let t = p.parse_term(&mut ctx2).expect("#b1010 must parse");
            let (w, v) = ctx2.bv_const_value(t).expect("#b1010 must be a BV const");
            assert_eq!(w, 4, "#b1010 width must be 4");
            assert_eq!(*v, Integer::from(10u64), "#b1010 value must be 10");
        }

        // #b11111111 — 8-bit binary 255: same value as #xFF.
        {
            let mut ctx2 = Context::new();
            let mut p = Parser::new("#b11111111");
            let t = p.parse_term(&mut ctx2).expect("#b11111111 must parse");
            let (w, v) = ctx2
                .bv_const_value(t)
                .expect("#b11111111 must be a BV const");
            assert_eq!(w, 8, "#b11111111 width must be 8");
            assert_eq!(*v, Integer::from(255u64), "#b11111111 value must be 255");
        }

        // (_ BitVec 8) sort round-trip: parse_sort directly.
        {
            let mut ctx2 = Context::new();
            let mut p = Parser::new("(_ BitVec 8)");
            let s = p
                .parse_sort(&mut ctx2)
                .expect("(_ BitVec 8) must parse as a sort");
            assert_eq!(
                s,
                ctx2.bv_sort(8),
                "(_ BitVec 8) must resolve to bv_sort(8)"
            );
        }
    }

    #[test]
    fn parses_array_sort_and_select_store() {
        let src = "\
(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun i () I)
(declare-fun e () E)
(assert (= (select (store a i e) i) e))
(check-sat)";
        let mut ctx = shinri_core::Context::new();
        let mut p = Parser::new(src);
        // Drive all commands; assert none produce a parse diagnostic.
        while let Some(cmd) = p.next_command(&mut ctx) {
            cmd.expect("array sort / select / store must parse");
        }
    }

    /// Helper: parse all commands from `src`; return Ok(cmds) or the first Err.
    fn parse_all(src: &str) -> Result<Vec<Command>, Diagnostic> {
        let mut ctx = Context::new();
        let mut p = Parser::new(src);
        let mut cmds = Vec::new();
        while let Some(c) = p.next_command(&mut ctx) {
            cmds.push(c?);
        }
        Ok(cmds)
    }

    /// Task-5 TDD test: BV operator symbols + indexed identifiers.
    ///
    /// Positive assertions:
    ///   - The width-correct formula parses without error.
    ///   - `((_ extract 3 0) x)` where x : BitVec 8 has sort bv_sort(4).
    ///   - `(_ bv1 8)` is a BitVec const of width 8, value 1.
    ///   - `(concat ((_ extract 7 4) x) ((_ extract 3 0) x))` has sort bv_sort(8).
    ///
    /// Negative assertion:
    ///   - `(bvadd x y)` where x : BitVec 8 and y : BitVec 16 errors (sort mismatch).
    #[test]
    fn parses_indexed_bv_ops_and_bv_numeral() {
        // --- Positive: full command round-trip ---
        let src = "(declare-const x (_ BitVec 8))\n\
                   (assert (= (concat ((_ extract 7 4) x) ((_ extract 3 0) x)) (bvadd x (_ bv1 8))))\n";
        assert!(
            parse_all(src).is_ok(),
            "width-correct BV formula must parse"
        );

        // --- Positive: extract sort check ---
        {
            let mut ctx = Context::new();
            let mut p = Parser::new("(declare-const x (_ BitVec 8))");
            p.next_command(&mut ctx).unwrap().unwrap();
            let mut p2 = Parser::with_env("((_ extract 3 0) x)", p.into_env());
            let t = p2.parse_term(&mut ctx).expect("extract must parse");
            assert_eq!(
                ctx.sort_of(t),
                ctx.bv_sort(4),
                "extract [3:0] of bv8 must have sort bv4"
            );
        }

        // --- Positive: (_ bv1 8) literal ---
        {
            let mut ctx = Context::new();
            let mut p = Parser::new("(_ bv1 8)");
            let t = p.parse_term(&mut ctx).expect("(_ bv1 8) must parse");
            let (w, v) = ctx.bv_const_value(t).expect("(_ bv1 8) must be a BV const");
            assert_eq!(w, 8, "(_ bv1 8) width must be 8");
            assert_eq!(*v, Integer::from(1u64), "(_ bv1 8) value must be 1");
        }

        // --- Positive: concat sort ---
        {
            let mut ctx = Context::new();
            let mut p = Parser::new("(declare-const x (_ BitVec 8))");
            p.next_command(&mut ctx).unwrap().unwrap();
            let mut p2 = Parser::with_env(
                "(concat ((_ extract 7 4) x) ((_ extract 3 0) x))",
                p.into_env(),
            );
            let t = p2.parse_term(&mut ctx).expect("concat must parse");
            assert_eq!(
                ctx.sort_of(t),
                ctx.bv_sort(8),
                "concat of two bv4 must have sort bv8"
            );
        }

        // --- Negative: width-mismatched bvadd must error ---
        {
            let src_bad = "(declare-const x (_ BitVec 8))\n\
                           (declare-const y (_ BitVec 16))\n\
                           (assert (bvadd x y))\n";
            let result = parse_all(src_bad);
            assert!(
                result.is_err(),
                "bvadd of bv8 and bv16 must produce a sort error"
            );
        }
    }

    /// Task-4 TDD test: String sort, string literals, and str.* operators.
    ///
    /// The script declares `x : String`, then asserts
    /// `(= (str.len (str.++ x "ab")) 5)`.
    ///
    /// Assertions:
    ///   - Parsing returns Ok (no diagnostics).
    ///   - The assert term is an Eq whose first child is StrLen.
    ///   - The literal "ab" round-trips as a string const of value "ab".
    #[test]
    fn parses_strings_concat_len_and_literal() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let src = r#"
            (declare-fun x () String)
            (assert (= (str.len (str.++ x "ab")) 5))
        "#;
        let (ctx, cmds) = parse_all_ok(src);
        // Two commands: declare-fun + assert.
        assert_eq!(cmds.len(), 2, "expected declare-fun + assert");
        // The second command is an Assert.
        let assert_term = match &cmds[1] {
            Command::Assert(t) => *t,
            other => panic!("expected Assert, got {other:?}"),
        };
        // Top-level term must be Eq.
        let eq_args = match ctx.term_node(assert_term).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Eq),
                args,
                ..
            } => ctx.children(args).to_vec(),
            other => panic!("expected Eq App at top level, got {other:?}"),
        };
        // First child of Eq is StrLen.
        let strlen_arg = match ctx.term_node(eq_args[0]).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrLen),
                args,
                ..
            } => ctx.children(args).to_vec(),
            other => panic!("expected StrLen as lhs of Eq, got {other:?}"),
        };
        // The StrLen's argument is StrConcat.
        let concat_args = match ctx.term_node(strlen_arg[0]).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrConcat),
                args,
                ..
            } => ctx.children(args).to_vec(),
            other => panic!("expected StrConcat inside StrLen, got {other:?}"),
        };
        // Second arg of StrConcat is the literal "ab".
        let lit_ab = concat_args[1];
        assert_eq!(
            ctx.string_const_value(lit_ab),
            Some("ab"),
            "literal \"ab\" must round-trip as string const"
        );
    }

    /// Parse `(str.at x 1)` and verify the App's op is StrAt.
    #[test]
    fn parses_strings_str_at() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let src = r#"
            (declare-fun x () String)
            (assert (= (str.at x 1) "a"))
        "#;
        let (ctx, cmds) = parse_all_ok(src);
        assert_eq!(cmds.len(), 2, "expected declare-fun + assert");
        let assert_term = match &cmds[1] {
            Command::Assert(t) => *t,
            other => panic!("expected Assert, got {other:?}"),
        };
        // Top-level term must be Eq.
        let eq_args = match ctx.term_node(assert_term).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Eq),
                args,
                ..
            } => ctx.children(args).to_vec(),
            other => panic!("expected Eq App at top level, got {other:?}"),
        };
        // First child of Eq must be StrAt.
        match ctx.term_node(eq_args[0]).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrAt),
                ..
            } => {}
            other => panic!("expected StrAt as lhs of Eq, got {other:?}"),
        }
    }

    /// Parse `(str.substr x 1 2)` and verify the App's op is StrSubstr.
    #[test]
    fn parses_strings_str_substr() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        let src = r#"
            (declare-fun x () String)
            (assert (= (str.substr x 1 2) "ab"))
        "#;
        let (ctx, cmds) = parse_all_ok(src);
        assert_eq!(cmds.len(), 2, "expected declare-fun + assert");
        let assert_term = match &cmds[1] {
            Command::Assert(t) => *t,
            other => panic!("expected Assert, got {other:?}"),
        };
        // Top-level term must be Eq.
        let eq_args = match ctx.term_node(assert_term).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Eq),
                args,
                ..
            } => ctx.children(args).to_vec(),
            other => panic!("expected Eq App at top level, got {other:?}"),
        };
        // First child of Eq must be StrSubstr.
        match ctx.term_node(eq_args[0]).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrSubstr),
                ..
            } => {}
            other => panic!("expected StrSubstr as lhs of Eq, got {other:?}"),
        }
    }

    /// Parse each of the three string predicates and verify op + Bool sort
    /// (slice 12).
    #[test]
    fn parses_string_predicates() {
        use shinri_core::{BuiltinOp, Op, TermNode};
        for (src, want) in [
            (r#"(assert (str.prefixof x "a"))"#, BuiltinOp::StrPrefixOf),
            (r#"(assert (str.suffixof x "a"))"#, BuiltinOp::StrSuffixOf),
            (r#"(assert (str.contains x "a"))"#, BuiltinOp::StrContains),
        ] {
            let full_src = format!("(declare-fun x () String)\n{src}");
            let (ctx, cmds) = parse_all_ok(&full_src);
            assert_eq!(cmds.len(), 2, "expected declare-fun + assert for {src}");
            let assert_term = match &cmds[1] {
                Command::Assert(t) => *t,
                other => panic!("expected Assert, got {other:?}"),
            };
            // Top-level term must be the expected predicate op.
            match ctx.term_node(assert_term).clone() {
                TermNode::App {
                    op: Op::Builtin(got),
                    ..
                } => {
                    assert_eq!(got, want, "op mismatch for {src}");
                }
                other => panic!("expected App at top level for {src}, got {other:?}"),
            }
            // Predicates are Bool-sorted.
            assert_eq!(
                ctx.sort_of(assert_term),
                ctx.bool_sort(),
                "predicate must be Bool-sorted for {src}"
            );
        }
    }

    /// A predicate with a non-String argument is a sort error, not a parse
    /// crash (slice 12).
    #[test]
    fn string_predicate_wrong_sort_rejected() {
        let cs = commands("(declare-fun x () String)\n(assert (str.contains x 1))");
        assert!(matches!(cs[0], Ok(Command::DeclareFun { .. })));
        assert!(
            cs[1].is_err(),
            "(str.contains x 1): 1 is Int, not String, so this must be a diagnostic"
        );
    }

    /// Task-5 TDD test: `(_ FloatingPoint eb sb)`, `FloatNN` aliases, and
    /// `RoundingMode` are recognised by `parse_sort`.
    #[test]
    fn parse_fp_and_rm_sorts() {
        use shinri_core::Context;
        fn sort_of_str(src: &str) -> (Context, shinri_core::SortId) {
            let mut ctx = Context::new();
            let mut p = Parser::new(src);
            let s = p.parse_sort(&mut ctx).expect("parse sort");
            (ctx, s)
        }
        let (ctx, s) = sort_of_str("(_ FloatingPoint 8 24)");
        assert_eq!(ctx.fp_widths(s), Some((8, 24)));

        let (ctx, s) = sort_of_str("Float64");
        assert_eq!(ctx.fp_widths(s), Some((11, 53)));

        let (ctx, s) = sort_of_str("Float16");
        assert_eq!(ctx.fp_widths(s), Some((5, 11)));

        let (ctx, s) = sort_of_str("Float32");
        assert_eq!(ctx.fp_widths(s), Some((8, 24)));

        let (ctx, s) = sort_of_str("Float128");
        assert_eq!(ctx.fp_widths(s), Some((15, 113)));

        let (mut ctx, s) = sort_of_str("RoundingMode");
        assert_eq!(s, ctx.rm_sort());
    }

    /// Task-6 TDD test: rounding-mode constant leaf symbols resolve to RM constants.
    ///
    /// Covers both short forms (RNE, RNA, RTP, RTN, RTZ) and long forms
    /// (roundNearestTiesToEven, etc.).  Each is parsed as a bare symbol term
    /// and the resulting TermId is checked via `ctx.rm_const_value`.
    #[test]
    fn parse_rounding_mode_constants() {
        use shinri_core::{term::RoundingMode, Context};
        fn rm_of(src: &str) -> Option<RoundingMode> {
            let mut ctx = Context::new();
            let mut p = Parser::new(src);
            let t = p.parse_term_pub(&mut ctx).expect("parse term");
            ctx.rm_const_value(t)
        }
        assert_eq!(rm_of("RNE"), Some(RoundingMode::Rne));
        assert_eq!(rm_of("roundNearestTiesToEven"), Some(RoundingMode::Rne));
        assert_eq!(rm_of("RNA"), Some(RoundingMode::Rna));
        assert_eq!(rm_of("roundNearestTiesToAway"), Some(RoundingMode::Rna));
        assert_eq!(rm_of("RTP"), Some(RoundingMode::Rtp));
        assert_eq!(rm_of("roundTowardPositive"), Some(RoundingMode::Rtp));
        assert_eq!(rm_of("RTN"), Some(RoundingMode::Rtn));
        assert_eq!(rm_of("roundTowardNegative"), Some(RoundingMode::Rtn));
        assert_eq!(rm_of("RTZ"), Some(RoundingMode::Rtz));
        assert_eq!(rm_of("roundTowardZero"), Some(RoundingMode::Rtz));
    }

    /// Task-5 negative-path coverage: the `(_ FloatingPoint eb sb)` parser
    /// boundary guard rejects `eb < 2` or `sb < 2` with a recoverable
    /// Diagnostic (never a panic).
    #[test]
    fn parse_fp_sort_rejects_too_small_widths() {
        use shinri_core::Context;
        fn err_of_str(src: &str) -> Diagnostic {
            let mut ctx = Context::new();
            let mut p = Parser::new(src);
            p.parse_sort(&mut ctx)
                .expect_err("FloatingPoint with eb<2/sb<2 must be rejected")
        }
        let e = err_of_str("(_ FloatingPoint 1 24)");
        assert!(
            e.message.contains("eb>=2") && e.message.contains("sb>=2"),
            "diagnostic should mention the eb>=2/sb>=2 requirement, got: {}",
            e.message
        );
        let e = err_of_str("(_ FloatingPoint 8 1)");
        assert!(
            e.message.contains("eb>=2") && e.message.contains("sb>=2"),
            "diagnostic should mention the eb>=2/sb>=2 requirement, got: {}",
            e.message
        );
    }

    /// Task-7 TDD test: `(fp s e m)` bit-constructor and `(_ ±oo/±zero/NaN eb sb)`
    /// special FP literals parse correctly and produce the right bit patterns.
    #[test]
    fn parse_fp_constructor_and_specials() {
        use shinri_core::Context;
        fn parse(src: &str) -> (Context, shinri_core::TermId) {
            let mut ctx = Context::new();
            let mut p = Parser::new(src);
            let t = p.parse_term_pub(&mut ctx).expect("parse term");
            (ctx, t)
        }

        // (fp #b0 #b00000000 #b00000000000000000000000) is +zero in Float32.
        let (ctx, t) = parse("(fp #b0 #b00000000 #b00000000000000000000000)");
        assert_eq!(ctx.fp_widths(ctx.sort_of(t)), Some((8, 24)));

        // (_ +zero 8 24): all bits zero.
        let (ctx, t) = parse("(_ +zero 8 24)");
        let (eb, sb, bits) = ctx.fp_const_value(t).expect("fp const");
        assert_eq!((eb, sb), (8, 24));
        assert!(bits.is_zero(), "+zero must be all-zero bits");

        // (_ -zero 8 24): only the sign bit (bit 31) set => 2^31.
        let (ctx, t) = parse("(_ -zero 8 24)");
        let (_, _, bits) = ctx.fp_const_value(t).unwrap();
        assert_eq!(bits.to_i128(), Some(1i128 << 31));

        // (_ +oo 8 24): exp all ones, sig 0 => 0xFF << 23 = 0x7F800000.
        let (ctx, t) = parse("(_ +oo 8 24)");
        let (_, _, bits) = ctx.fp_const_value(t).unwrap();
        assert_eq!(bits.to_i128(), Some(0x7F80_0000));

        // (_ -oo 8 24): sign + exp all ones => 0xFF800000.
        let (ctx, t) = parse("(_ -oo 8 24)");
        let (_, _, bits) = ctx.fp_const_value(t).unwrap();
        assert_eq!(bits.to_i128(), Some(0xFF80_0000u32 as i128));

        // (_ NaN 8 24): exp all ones, quiet bit (sig MSB, bit 22) set => 0x7FC00000.
        let (ctx, t) = parse("(_ NaN 8 24)");
        let (_, _, bits) = ctx.fp_const_value(t).unwrap();
        assert_eq!(bits.to_i128(), Some(0x7FC0_0000));
    }

    /// Task-8 TDD test: `fp.*` operator names and indexed FP conversions parse
    /// and sort-check correctly.
    ///
    /// Assertions:
    ///   - `(fp.add RNE x x)` with x:Float32 → Float32 (fp_widths == Some((8,24)))
    ///   - `(fp.isNaN x)` with x:Float32 → Bool
    ///   - `((_ to_fp 11 53) RNE x)` with x:Float32 → Float64 (fp_widths == Some((11,53)))
    ///   - `((_ fp.to_sbv 16) RNE x)` with x:Float32 → BV16 (bv_width == Some(16))
    #[test]
    fn parse_fp_operators_and_conversions() {
        use shinri_core::Context;

        /// Declare `x` of sort `decl_sort` into a Context, then parse `expr`
        /// in that same environment (sharing the declared symbol).
        fn parse_with_x(decl_sort: &str, expr: &str) -> (Context, shinri_core::TermId) {
            let mut ctx = Context::new();
            let decl = format!("(declare-fun x () {decl_sort})");
            let mut p = Parser::new(&decl);
            p.next_command(&mut ctx).unwrap().unwrap();
            let mut p2 = Parser::with_env(expr, p.into_env());
            let t = p2.parse_term(&mut ctx).expect("parse expr");
            (ctx, t)
        }

        // fp.add RNE x x : Float32 → Float32
        let (ctx, t) = parse_with_x("Float32", "(fp.add RNE x x)");
        assert_eq!(
            ctx.fp_widths(ctx.sort_of(t)),
            Some((8, 24)),
            "fp.add result must be Float32"
        );

        // fp.isNaN x : Bool
        let (ctx, t) = parse_with_x("Float32", "(fp.isNaN x)");
        assert_eq!(
            ctx.sort_of(t),
            ctx.bool_sort(),
            "fp.isNaN result must be Bool"
        );

        // ((_ to_fp 11 53) RNE x) : Float32 → Float64
        let (ctx, t) = parse_with_x("Float32", "((_ to_fp 11 53) RNE x)");
        assert_eq!(
            ctx.fp_widths(ctx.sort_of(t)),
            Some((11, 53)),
            "to_fp 11 53 result must be Float64"
        );

        // ((_ fp.to_sbv 16) RNE x) : Float32 → BV16
        let (ctx, t) = parse_with_x("Float32", "((_ fp.to_sbv 16) RNE x)");
        assert_eq!(
            ctx.bv_width(ctx.sort_of(t)),
            Some(16),
            "fp.to_sbv 16 result must be BV16"
        );
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

#[cfg(test)]
mod attr_tests {
    use super::Parser;
    use shinri_core::Context;
    use shinri_frontend::{AttrValue, Command};

    #[test]
    fn set_option_bool_value_is_semantic_text() {
        let mut ctx = Context::new();
        let mut p = Parser::new("(set-option :print-success false)");
        let cmd = p.next_command(&mut ctx).unwrap().unwrap();
        assert_eq!(
            cmd,
            Command::SetOption {
                keyword: ":print-success".into(),
                value: AttrValue::Token(Some("false".into())),
            }
        );
    }

    #[test]
    fn set_option_string_value_strips_quotes() {
        let mut ctx = Context::new();
        let mut p = Parser::new("(set-option :regular-output-channel \"out.txt\")");
        let cmd = p.next_command(&mut ctx).unwrap().unwrap();
        assert_eq!(
            cmd,
            Command::SetOption {
                keyword: ":regular-output-channel".into(),
                value: AttrValue::Token(Some("out.txt".into())),
            }
        );
    }

    #[test]
    fn set_option_bare_keyword_has_no_value() {
        let mut ctx = Context::new();
        let mut p = Parser::new("(set-info :some-flag)");
        let cmd = p.next_command(&mut ctx).unwrap().unwrap();
        assert_eq!(
            cmd,
            Command::SetInfo {
                keyword: ":some-flag".into(),
                value: AttrValue::Token(None),
            }
        );
    }
}
