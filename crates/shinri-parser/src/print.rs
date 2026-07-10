use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermId, TermNode};

/// Print a term as an s-expression that re-parses to the same id.
pub fn print_term(ctx: &Context, t: TermId) -> String {
    let mut s = String::new();
    write_term(ctx, t, &mut s);
    s
}

fn write_term(ctx: &Context, t: TermId, out: &mut String) {
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
                // Render as SMT-LIB string literal: "" wraps, internal " is escaped as "".
                let s = ctx.string_const_value(t).unwrap();
                out.push('"');
                for ch in s.chars() {
                    if ch == '"' {
                        out.push_str("\"\"");
                    } else {
                        out.push(ch);
                    }
                }
                out.push('"');
            }
            ConstVal::Float(_) => {
                let (eb, sb, bits) = ctx.fp_const_value(t).expect("Float const");
                out.push_str(&format_fp_triple(eb, sb, bits));
            }
            ConstVal::Rm(_) => {
                let rm = ctx.rm_const_value(t).expect("RM const");
                out.push_str(match rm {
                    shinri_core::RoundingMode::Rne => "RNE",
                    shinri_core::RoundingMode::Rna => "RNA",
                    shinri_core::RoundingMode::Rtp => "RTP",
                    shinri_core::RoundingMode::Rtn => "RTN",
                    shinri_core::RoundingMode::Rtz => "RTZ",
                });
            }
        },
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            if children.is_empty() {
                if let Op::Uninterpreted(sym) = op {
                    out.push_str(ctx.symbol_name(sym));
                }
                return;
            }
            out.push('(');
            match op {
                Op::Builtin(b) => out.push_str(&builtin_name(b)),
                Op::Uninterpreted(sym) => out.push_str(ctx.symbol_name(sym)),
            }
            for c in children {
                out.push(' ');
                write_term(ctx, c, out);
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
        // Slice 13
        StrIndexOf => "str.indexof".to_owned(),
        StrReplace => "str.replace".to_owned(),
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
        use shinri_core::{Context, RoundingMode};
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
        use shinri_core::{BuiltinOp, Op, Rational};
        let mut ctx = shinri_core::Context::new();
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
}
