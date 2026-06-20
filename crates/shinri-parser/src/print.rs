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
                Op::Builtin(b) => out.push_str(builtin_name(b)),
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

fn builtin_name(b: BuiltinOp) -> &'static str {
    use BuiltinOp::*;
    match b {
        Not => "not",
        And => "and",
        Or => "or",
        Implies => "=>",
        Xor => "xor",
        Eq => "=",
        Distinct => "distinct",
        Ite => "ite",
        Neg => "-",
        Add => "+",
        Sub => "-",
        Mul => "*",
        Le => "<=",
        Lt => "<",
        Ge => ">=",
        Gt => ">",
    }
}
