//! SMT-LIB 2.6 term and sort printing (slice 55; moved from
//! `shinri-parser`). One printer for the parser's round-trip tests and for
//! every solver output path (`get-value` echo, `get-model`), so they agree
//! on one rule set — the same reason `smtlib_string` lives here.
use std::borrow::Cow;

use crate::{BuiltinOp, ConstVal, Context, Op, SortId, SortNode, TermId, TermNode};

/// Node-visit budget for one `get-value` response (slice 43 T6 review
/// finding 1). The term DAG is hash-consed and the parser's `let` binds a
/// name to a TermId without duplicating it, so a LINEAR-size, SMALL-depth
/// script can share a subterm at every level (`x_i := (g x_{i-1} x_{i-1})`).
/// The printer has no memoization, so it re-walks a shared child once per
/// occurrence: `2^N` node-visits for `N` levels, not `N`. Measured pre-budget
/// with a 22-level chain (612-byte script): a 29 MB response in ~4.3s,
/// roughly doubling per extra level (100 MB/16.5s at N=24). The depth cap
/// does NOT bound this; the blowup is severe at depth 22-24.
///
/// The budget counts down by one per node visited (checked BEFORE recursing,
/// so it bounds work done, not just output size); remaining subterms print
/// as `|<truncated>|` once it hits zero. 100_000 is far more nodes than any
/// human-written `get-value` target has, yet cuts an exponential chain off
/// at roughly its 17th sharing level, so the worst case is sub-millisecond.
///
/// The budget is built ONCE PER `get-value` RESPONSE (in the
/// `Command::GetValue` arm) and threaded through every label: `(get-value
/// (t1 … tK))` with a per-term budget would bound each label but not the
/// response. Measured on a 24_635-byte script whose K=40 labels all name the
/// same 25-level `let`-shared term: 14.0 MB in 0.55s per-term, 350 KB in
/// 0.017s shared — the multiplier is exactly K, bounded only by script
/// length. Moved from `shinri-solver/src/tseitin.rs`.
pub const DISPLAY_TERM_BUDGET: usize = 100_000;

/// Printed in place of a subterm once the budget or the depth backstop is
/// exhausted: a parseable symbol that is visibly not a real term (never a
/// TermId index, which is what slice 55 removed).
const TRUNCATED: &str = "|<truncated>|";

/// Term depth is attacker-controlled (threat model); a mechanical backstop,
/// mirroring `render_value`'s cap. The operative output bound is the budget.
const MAX_DEPTH: u32 = 10_000;

/// SMT-LIB 2.6 reserved words (§3.1), including every command name.
const RESERVED: &[&str] = &[
    "!",
    "_",
    "as",
    "BINARY",
    "DECIMAL",
    "exists",
    "HEXADECIMAL",
    "forall",
    "let",
    "match",
    "NUMERAL",
    "par",
    "STRING",
    "assert",
    "check-sat",
    "check-sat-assuming",
    "declare-const",
    "declare-datatype",
    "declare-datatypes",
    "declare-fun",
    "declare-sort",
    "define-fun",
    "define-fun-rec",
    "define-funs-rec",
    "define-sort",
    "echo",
    "exit",
    "get-assertions",
    "get-assignment",
    "get-info",
    "get-model",
    "get-option",
    "get-proof",
    "get-unsat-assumptions",
    "get-unsat-core",
    "get-value",
    "pop",
    "push",
    "reset",
    "reset-assertions",
    "set-info",
    "set-logic",
    "set-option",
];

fn is_simple_symbol(name: &str) -> bool {
    const PUNCT: &str = "~!@$%^&*_+=<>.?/-";
    let mut cs = name.chars();
    let Some(first) = cs.next() else { return false };
    (first.is_ascii_alphabetic() || PUNCT.contains(first))
        && cs.all(|c| c.is_ascii_alphanumeric() || PUNCT.contains(c))
}

/// `name` bare if it is a simple SMT-LIB symbol (the lexer's rule) and not
/// reserved, else `|name|`. A name containing `|` or `\` cannot be quoted;
/// the lexer cannot produce one and internal names are simple.
pub fn quote_symbol(name: &str) -> Cow<'_, str> {
    if is_simple_symbol(name) && !RESERVED.contains(&name) {
        Cow::Borrowed(name)
    } else {
        debug_assert!(
            !name.contains(['|', '\\']),
            "unquotable symbol name: {name:?}"
        );
        Cow::Owned(format!("|{name}|"))
    }
}

/// A sort's SMT-LIB name with user sort / datatype names quoted.
pub fn print_sort(ctx: &Context, s: SortId) -> String {
    match ctx.sort_node(s) {
        SortNode::Uninterpreted(sym) | SortNode::Datatype(sym) => {
            quote_symbol(ctx.symbol_name(*sym)).into_owned()
        }
        SortNode::Array(i, e) => {
            format!("(Array {} {})", print_sort(ctx, *i), print_sort(ctx, *e))
        }
        _ => ctx.sort_name(s),
    }
}

/// Print a term as an s-expression that re-parses to the same id. Unbounded:
/// for the parser and tests. Solver output paths use `print_term_budgeted`.
pub fn print_term(ctx: &Context, t: TermId) -> String {
    let mut budget = usize::MAX;
    print_term_budgeted(ctx, t, &mut budget)
}

/// `print_term` with a node-visit budget shared by the caller across a whole
/// response. Each visit costs one unit, checked before recursing.
pub fn print_term_budgeted(ctx: &Context, t: TermId, budget: &mut usize) -> String {
    let mut s = String::new();
    write_term(ctx, t, 0, budget, &mut s);
    s
}

fn write_term(ctx: &Context, t: TermId, depth: u32, budget: &mut usize, out: &mut String) {
    if depth > MAX_DEPTH || *budget == 0 {
        out.push_str(TRUNCATED);
        return;
    }
    *budget -= 1;
    match ctx.term_node(t).clone() {
        TermNode::Const { val, sort } => match val {
            ConstVal::Bool(b) => out.push_str(if b { "true" } else { "false" }),
            ConstVal::BitVec(_) => {
                let (width, value) = ctx.bv_const_value(t).unwrap();
                // Render as SMT-LIB indexed bitvector literal: (_ bv<value> <width>)
                out.push_str(&format!("(_ bv{value} {width})"));
            }
            ConstVal::Num(_) => {
                // Minimal printer: assumes non-negative numerals; negatives are out of scope for round-trip (Phase 1).
                let r = ctx.numeral_value(t).unwrap();
                let numer = r.numer();
                let denom = r.denom();
                let is_real = sort == ctx.real_sort();
                if denom == shinri_num::Integer::one() {
                    // Integral value: print as decimal (e.g. "1.0") for Real sort,
                    // or plain numeral (e.g. "1") for Int sort, so re-parse yields
                    // the same sort.
                    if is_real {
                        out.push_str(&format!("{numer}.0"));
                    } else {
                        out.push_str(&numer.to_string());
                    }
                } else {
                    out.push_str(&format!("(/ {numer} {denom})"));
                }
            }
            ConstVal::String(_) => {
                // The inverse of the parser's decode_literal (slice 51).
                let s = ctx.string_const_value(t).unwrap();
                out.push_str(&crate::smtlib_string::encode_literal(s));
            }
            ConstVal::Float(_) => {
                let (eb, sb, bits) = ctx.fp_const_value(t).expect("Float const");
                out.push_str(&format_fp_triple(eb, sb, bits));
            }
            ConstVal::Rm(_) => {
                let rm = ctx.rm_const_value(t).expect("RM const");
                out.push_str(match rm {
                    crate::RoundingMode::Rne => "RNE",
                    crate::RoundingMode::Rna => "RNA",
                    crate::RoundingMode::Rtp => "RTP",
                    crate::RoundingMode::Rtn => "RTN",
                    crate::RoundingMode::Rtz => "RTZ",
                });
            }
        },
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            if children.is_empty() {
                match op {
                    Op::Uninterpreted(sym) => out.push_str(&quote_symbol(ctx.symbol_name(sym))),
                    Op::Builtin(b) => out.push_str(&builtin_name(b)),
                }
                return;
            }
            out.push('(');
            match op {
                Op::Builtin(b) => out.push_str(&builtin_name(b)),
                Op::Uninterpreted(sym) => out.push_str(&quote_symbol(ctx.symbol_name(sym))),
            }
            for c in children {
                out.push(' ');
                write_term(ctx, c, depth + 1, budget, out);
            }
            out.push(')');
        }
    }
}

/// Render an FP literal as `(fp #b<sign> #b<exp> #b<trailing-sig>)`.
fn format_fp_triple(eb: u32, sb: u32, bits: &shinri_num::Integer) -> String {
    let two = shinri_num::Integer::from(2u64);
    let bin = |val: &shinri_num::Integer, width: u32| -> String {
        let mut rem = val.clone();
        let mut b: Vec<u8> = Vec::with_capacity(width as usize);
        for _ in 0..width {
            let (q, r) = rem.div_rem(&two);
            b.push(r.to_i128().unwrap_or(0) as u8);
            rem = q;
        }
        b.reverse();
        b.iter().map(|&x| if x == 1 { '1' } else { '0' }).collect()
    };
    // Layout: bits = sign | exp | trailing-sig (MSB to LSB)
    // low (sb-1) bits = trailing significand; next eb bits = exponent; top bit = sign.
    let mut sig_mod = shinri_num::Integer::one();
    for _ in 0..(sb - 1) {
        sig_mod *= two.clone();
    }
    let sig = bits.div_rem(&sig_mod).1;
    let mut hi = bits.clone();
    for _ in 0..(sb - 1) {
        hi = hi.div_rem(&two).0;
    }
    let mut exp_mod = shinri_num::Integer::one();
    for _ in 0..eb {
        exp_mod *= two.clone();
    }
    let exp = hi.div_rem(&exp_mod).1;
    let mut sign = hi;
    for _ in 0..eb {
        sign = sign.div_rem(&two).0;
    }
    format!(
        "(fp #b{} #b{} #b{})",
        bin(&sign, 1),
        bin(&exp, eb),
        bin(&sig, sb - 1)
    )
}

fn builtin_name(b: BuiltinOp) -> String {
    use BuiltinOp::*;
    match b {
        Not => "not".to_owned(),
        And => "and".to_owned(),
        Or => "or".to_owned(),
        Implies => "=>".to_owned(),
        Xor => "xor".to_owned(),
        Eq => "=".to_owned(),
        Distinct => "distinct".to_owned(),
        Ite => "ite".to_owned(),
        Neg => "-".to_owned(),
        Add => "+".to_owned(),
        Sub => "-".to_owned(),
        Mul => "*".to_owned(),
        Le => "<=".to_owned(),
        Lt => "<".to_owned(),
        Ge => ">=".to_owned(),
        Gt => ">".to_owned(),
        Select => "select".to_owned(),
        Store => "store".to_owned(),
        // Bitvector fixed-arity ops — SMT-LIB names
        BvNot => "bvnot".to_owned(),
        BvAnd => "bvand".to_owned(),
        BvOr => "bvor".to_owned(),
        BvXor => "bvxor".to_owned(),
        BvNand => "bvnand".to_owned(),
        BvNor => "bvnor".to_owned(),
        BvXnor => "bvxnor".to_owned(),
        BvNeg => "bvneg".to_owned(),
        BvAdd => "bvadd".to_owned(),
        BvSub => "bvsub".to_owned(),
        BvMul => "bvmul".to_owned(),
        BvUdiv => "bvudiv".to_owned(),
        BvUrem => "bvurem".to_owned(),
        BvSdiv => "bvsdiv".to_owned(),
        BvSrem => "bvsrem".to_owned(),
        BvSmod => "bvsmod".to_owned(),
        BvShl => "bvshl".to_owned(),
        BvLshr => "bvlshr".to_owned(),
        BvAshr => "bvashr".to_owned(),
        BvUlt => "bvult".to_owned(),
        BvUle => "bvule".to_owned(),
        BvUgt => "bvugt".to_owned(),
        BvUge => "bvuge".to_owned(),
        BvSlt => "bvslt".to_owned(),
        BvSle => "bvsle".to_owned(),
        BvSgt => "bvsgt".to_owned(),
        BvSge => "bvsge".to_owned(),
        BvConcat => "concat".to_owned(),
        // Bitvector indexed ops — SMT-LIB indexed identifier syntax: (_ op params...)
        BvExtract { hi, lo } => format!("(_ extract {hi} {lo})"),
        BvZeroExtend(k) => format!("(_ zero_extend {k})"),
        BvSignExtend(k) => format!("(_ sign_extend {k})"),
        BvRotateLeft(k) => format!("(_ rotate_left {k})"),
        BvRotateRight(k) => format!("(_ rotate_right {k})"),
        BvRepeat(k) => format!("(_ repeat {k})"),
        // String ops — SMT-LIB names
        StrConcat => "str.++".to_owned(),
        StrLen => "str.len".to_owned(),
        StrAt => "str.at".to_owned(),
        StrSubstr => "str.substr".to_owned(),
        // String predicates — SMT-LIB names (slice 12)
        StrPrefixOf => "str.prefixof".to_owned(),
        StrSuffixOf => "str.suffixof".to_owned(),
        StrContains => "str.contains".to_owned(),
        // Slice 23
        StrLt => "str.<".to_owned(),
        StrLeq => "str.<=".to_owned(),
        // Slice 13
        StrIndexOf => "str.indexof".to_owned(),
        StrReplace => "str.replace".to_owned(),
        // Slice 14
        StrReplaceAll => "str.replace_all".to_owned(),
        // Slice 15
        StrToInt => "str.to_int".to_owned(),
        StrFromInt => "str.from_int".to_owned(),
        // Slice 18
        StrToCode => "str.to_code".to_owned(),
        StrFromCode => "str.from_code".to_owned(),
        StrIsDigit => "str.is_digit".to_owned(),
        // Slice 19
        StrInRe => "str.in_re".to_owned(),
        StrToRe => "str.to_re".to_owned(),
        ReNone => "re.none".to_owned(),
        ReAll => "re.all".to_owned(),
        ReAllChar => "re.allchar".to_owned(),
        ReConcat => "re.++".to_owned(),
        ReUnion => "re.union".to_owned(),
        ReInter => "re.inter".to_owned(),
        ReDiff => "re.diff".to_owned(),
        ReStar => "re.*".to_owned(),
        RePlus => "re.+".to_owned(),
        ReOpt => "re.opt".to_owned(),
        ReComp => "re.comp".to_owned(),
        ReRange => "re.range".to_owned(),
        ReLoop { lo, hi } => format!("(_ re.loop {lo} {hi})"),
        RePow(n) => format!("(_ re.^ {n})"),
        // Floating-point ops — SMT-LIB names
        FpAbs => "fp.abs".to_owned(),
        FpNeg => "fp.neg".to_owned(),
        FpAdd => "fp.add".to_owned(),
        FpSub => "fp.sub".to_owned(),
        FpMul => "fp.mul".to_owned(),
        FpDiv => "fp.div".to_owned(),
        FpFma => "fp.fma".to_owned(),
        FpSqrt => "fp.sqrt".to_owned(),
        FpRoundToIntegral => "fp.roundToIntegral".to_owned(),
        FpRem => "fp.rem".to_owned(),
        FpMin => "fp.min".to_owned(),
        FpMax => "fp.max".to_owned(),
        FpLeq => "fp.leq".to_owned(),
        FpLt => "fp.lt".to_owned(),
        FpGeq => "fp.geq".to_owned(),
        FpGt => "fp.gt".to_owned(),
        FpEq => "fp.eq".to_owned(),
        FpIsNormal => "fp.isNormal".to_owned(),
        FpIsSubnormal => "fp.isSubnormal".to_owned(),
        FpIsZero => "fp.isZero".to_owned(),
        FpIsInfinite => "fp.isInfinite".to_owned(),
        FpIsNaN => "fp.isNaN".to_owned(),
        FpIsNegative => "fp.isNegative".to_owned(),
        FpIsPositive => "fp.isPositive".to_owned(),
        FpFromBits => "fp".to_owned(),
        // Floating-point indexed conversion ops — SMT-LIB indexed identifier syntax
        ToFp { eb, sb } => format!("(_ to_fp {eb} {sb})"),
        ToFpUnsigned { eb, sb } => format!("(_ to_fp_unsigned {eb} {sb})"),
        FpToUbv(m) => format!("(_ fp.to_ubv {m})"),
        FpToSbv(m) => format!("(_ fp.to_sbv {m})"),
        FpToReal => "fp.to_real".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prints_fp_const_and_rm() {
        use crate::{Context, RoundingMode};
        use shinri_num::Integer;
        let mut ctx = Context::new();
        // Float32 +zero
        let pz = ctx.mk_fp_const(8, 24, Integer::zero());
        assert_eq!(
            print_term(&ctx, pz),
            "(fp #b0 #b00000000 #b00000000000000000000000)"
        );
        // rounding mode
        let rne = ctx.mk_rm_const(RoundingMode::Rne);
        assert_eq!(print_term(&ctx, rne), "RNE");
    }

    #[test]
    fn prints_indexof_and_replace() {
        use crate::{BuiltinOp, Op, Rational};
        let mut ctx = crate::Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let f = ctx.declare_fun("x", &[], str_s);
        let x = ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap();
        let a = ctx.mk_string_const("a");
        let zero = ctx.mk_numeral(Rational::from_int(0i128.into()), int_s);
        let idx = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrIndexOf), &[x, a, zero])
            .unwrap();
        assert_eq!(print_term(&ctx, idx), r#"(str.indexof x "a" 0)"#);
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplace), &[x, a, a])
            .unwrap();
        assert_eq!(print_term(&ctx, rep), r#"(str.replace x "a" "a")"#);
    }

    #[test]
    fn prints_replace_all() {
        use crate::{BuiltinOp, Op};
        let mut ctx = crate::Context::new();
        let str_s = ctx.string_sort();
        let x = {
            let f = ctx.declare_fun("x", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let a = ctx.mk_string_const("a");
        let b = ctx.mk_string_const("b");
        let rep = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrReplaceAll), &[x, a, b])
            .unwrap();
        assert_eq!(print_term(&ctx, rep), r#"(str.replace_all x "a" "b")"#);
    }

    #[test]
    fn print_to_from_int_roundtrip() {
        use crate::{BuiltinOp, Op};
        let mut ctx = crate::Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let s = {
            let f = ctx.declare_fun("s", &[], str_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let n = {
            let f = ctx.declare_fun("n", &[], int_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let ti = ctx.mk_app(Op::Builtin(BuiltinOp::StrToInt), &[s]).unwrap();
        assert_eq!(print_term(&ctx, ti), "(str.to_int s)");
        let fi = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrFromInt), &[n])
            .unwrap();
        assert_eq!(print_term(&ctx, fi), "(str.from_int n)");
    }

    fn nullary(ctx: &mut Context, name: &str, sort: SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn quote_symbol_table() {
        for simple in ["x", "a.b", "<=>", "is-mk", "bool!0", "ite!3", "@x", "~q"] {
            assert_eq!(quote_symbol(simple), simple, "{simple}");
        }
        for (raw, quoted) in [
            ("a#b", "|a#b|"),
            ("my sort", "|my sort|"),
            ("0x", "|0x|"),
            ("", "||"),
            ("__ESBMC_rounding_mode&0#10", "|__ESBMC_rounding_mode&0#10|"),
            ("let", "|let|"),
            ("par", "|par|"),
            ("assert", "|assert|"),
            ("check-sat", "|check-sat|"),
            ("_", "|_|"),
            ("!", "|!|"),
        ] {
            assert_eq!(quote_symbol(raw), quoted, "{raw}");
        }
    }

    #[test]
    fn prints_quoted_symbols_in_terms() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let x = nullary(&mut ctx, "a#b", int);
        let g = ctx.declare_fun("f g", &[int], int);
        let app = ctx.mk_app(Op::Uninterpreted(g), &[x]).unwrap();
        assert_eq!(print_term(&ctx, app), "(|f g| |a#b|)");
    }

    #[test]
    fn prints_builtin_application() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let a = nullary(&mut ctx, "a", int);
        let one = ctx.mk_numeral(crate::Rational::from_int(1i128.into()), int);
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[a, one]).unwrap();
        assert_eq!(print_term(&ctx, sum), "(+ a 1)");
    }

    #[test]
    fn prints_nullary_builtins() {
        let mut ctx = Context::new();
        for (op, name) in [
            (BuiltinOp::ReNone, "re.none"),
            (BuiltinOp::ReAll, "re.all"),
            (BuiltinOp::ReAllChar, "re.allchar"),
        ] {
            let t = ctx.mk_app(Op::Builtin(op), &[]).unwrap();
            assert_eq!(print_term(&ctx, t), name);
        }
    }

    #[test]
    fn print_sort_quotes_user_sorts() {
        let mut ctx = Context::new();
        let u = ctx.declare_sort("my sort");
        let int = ctx.int_sort();
        let arr = ctx.array_sort(int, u);
        assert_eq!(print_sort(&ctx, u), "|my sort|");
        assert_eq!(print_sort(&ctx, arr), "(Array Int |my sort|)");
        assert_eq!(print_sort(&ctx, int), "Int");
        let bv = ctx.bv_sort(8);
        assert_eq!(print_sort(&ctx, bv), "(_ BitVec 8)");
    }

    #[test]
    fn budget_truncates_with_placeholder_and_bounds_work() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let g = ctx.declare_fun("g", &[int, int], int);
        let mut t = ctx.mk_numeral(crate::Rational::from_int(0i128.into()), int);
        for _ in 0..30 {
            t = ctx.mk_app(Op::Uninterpreted(g), &[t, t]).unwrap();
        }
        let mut budget = 1_000;
        let s = print_term_budgeted(&ctx, t, &mut budget);
        assert_eq!(budget, 0);
        assert!(s.contains("|<truncated>|"), "{s}");
        // <= 1 000 visited nodes (`(g ` ... `)`) plus <= 1 001 placeholders
        // (13 bytes each) -- well under 32 bytes per budget unit.
        assert!(
            s.len() < 1_000 * 32,
            "output not bounded: {} bytes",
            s.len()
        );
        assert!(
            !s.split([' ', '(', ')']).any(|tok| tok.len() > 1
                && tok.starts_with('t')
                && tok[1..].chars().all(|c| c.is_ascii_digit())),
            "TermId index leaked: {s}"
        );
    }

    #[test]
    fn unbounded_print_never_truncates() {
        let mut ctx = Context::new();
        let int = ctx.int_sort();
        let a = nullary(&mut ctx, "a", int);
        assert_eq!(print_term(&ctx, a), "a");
    }
}
