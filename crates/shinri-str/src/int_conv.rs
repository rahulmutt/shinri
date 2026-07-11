//! Slice 15 pre-pass: `str.to_int` / `str.from_int` — fold + exact roundtrip
//! rewrite + fence.
//!
//! Both ops are value-sorted FUNCTIONS (Int / String), so — like the slice-13
//! indexof/replace ops — the rewrites are exact at any position and polarity;
//! zero fresh variables are introduced here (the only fresh var is the `!ite`
//! that `reduce_assertions`' `elim_term_ite` mints for the roundtrip below).
//!
//! Stages (run by the solver's string-path seam):
//! 1. [`partial_eval_int_conv`] — bottom-up memoized rewrite:
//!    - fold `str.to_int(<lit>)` / `str.from_int(<numeral>)` to a literal;
//!    - rewrite `str.to_int(str.from_int(n))` → `ite(n >= 0, n, -1)` (exact).
//! 2. [`has_unreduced_int_conv`] — presence fence: any surviving application
//!    (symbolic string to `to_int`; symbolic non-roundtrip Int to `from_int`)
//!    fences the query to a sound `Unknown`.
//!
//! Strings are handled as code points; digit classification is EXACTLY
//! `char::is_ascii_digit()` (`'0'..='9'`) — never `char::is_numeric()`, which
//! would unsoundly fold non-ASCII Unicode digits.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Integer, Op, Rational, TermId, TermNode};

/// Concrete `str.to_int(s)` per SMT-LIB 2.6: the value of `s` iff it is a
/// non-empty run of ASCII digits (leading zeros allowed); otherwise `-1`.
fn eval_to_int(s: &str) -> Integer {
    if s.is_empty() || !s.chars().all(|c| c.is_ascii_digit()) {
        return Integer::from(-1i128);
    }
    Integer::from_str_radix(s, 10).expect("validated ASCII-digit run parses")
}

/// Concrete `str.from_int(n)` per SMT-LIB 2.6: canonical decimal for `n >= 0`
/// (no leading zeros, `0 -> "0"`); the empty string for `n < 0`.
fn eval_from_int(n: &Integer) -> String {
    if n.signum() < 0 {
        String::new()
    } else {
        n.to_string()
    }
}

/// Stage 1: bottom-up memoized rewrite. Folds fully-literal applications;
/// the roundtrip case is added in Task 4. Untouched subtrees keep their TermIds.
pub fn partial_eval_int_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    assertions
        .iter()
        .map(|&a| rewrite(ctx, a, &mut memo))
        .collect()
}

fn rewrite(ctx: &mut Context, t: TermId, memo: &mut FxHashMap<TermId, TermId>) -> TermId {
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let result = match ctx.term_node(t).clone() {
        TermNode::Const { .. } => t,
        TermNode::App { op, args, .. } => {
            let children: Vec<TermId> = ctx.children(args).to_vec();
            let new_children: Vec<TermId> =
                children.iter().map(|&c| rewrite(ctx, c, memo)).collect();
            let special = match op {
                Op::Builtin(BuiltinOp::StrToInt) => rewrite_to_int(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrFromInt) => rewrite_from_int(ctx, &new_children),
                _ => None,
            };
            if let Some(r) = special {
                r
            } else {
                let changed = new_children
                    .iter()
                    .zip(children.iter())
                    .any(|(n, o)| n != o);
                if changed {
                    ctx.mk_app(op, &new_children)
                        .expect("rewrite: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// `(str.to_int x)`, child already rewritten. Folds a literal argument; the
/// roundtrip `str.to_int(str.from_int(n))` case is added in Task 4. None leaves
/// the app in place (-> fence).
fn rewrite_to_int(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    if let Some(s) = ctx.string_const_value(kids[0]).map(str::to_owned) {
        let int_s = ctx.int_sort();
        return Some(ctx.mk_numeral(Rational::from_int(eval_to_int(&s)), int_s));
    }
    // Exact roundtrip: str.to_int(str.from_int(n)) = ite(n >= 0, n, -1).
    // For n >= 0, from_int yields canonical digits recovered exactly; for n < 0,
    // from_int = "" and to_int("") = -1. Polarity-free, exact.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrFromInt),
        args,
        ..
    } = ctx.term_node(kids[0]).clone()
    {
        let n = ctx.children(args)[0];
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(Rational::from_int(Integer::from(0i128)), int_s);
        let neg1 = ctx.mk_numeral(Rational::from_int(Integer::from(-1i128)), int_s);
        let ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero])
            .expect("n >= 0");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[ge, n, neg1])
                .expect("roundtrip ite"),
        );
    }
    None
}

/// `(str.from_int x)`, child already rewritten. Folds a numeral argument.
/// None (symbolic Int) leaves the app in place (-> fence).
fn rewrite_from_int(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    let r = int_literal(ctx, kids[0])?;
    Some(ctx.mk_string_const(&eval_from_int(&r.numer())))
}

/// Extracts an integer numeral's exact value from `t`: either a plain literal
/// (`ctx.numeral_value`), or `(- <numeral>)` — `BuiltinOp::Neg` applied to a
/// numeral, the standard SMT-LIB spelling of a negative integer literal (the
/// parser does NOT fold unary `-` into a `Const` numeral; see
/// `shinri-parser`'s `unify_arith`/`Sub` handling). `None` for any other
/// (non-literal / symbolic) term.
fn int_literal(ctx: &Context, t: TermId) -> Option<Rational> {
    if let Some(r) = ctx.numeral_value(t) {
        return Some(r.clone());
    }
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::Neg),
        args,
        ..
    } = ctx.term_node(t)
    {
        let children = ctx.children(*args);
        if let [only] = children {
            return ctx.numeral_value(*only).cloned().map(|r| -r);
        }
    }
    None
}

/// Stage 2: presence fence. True iff any `str.to_int` / `str.from_int`
/// application SURVIVED [`partial_eval_int_conv`].
pub fn has_unreduced_int_conv(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(op, Op::Builtin(BuiltinOp::StrToInt | BuiltinOp::StrFromInt))
                    || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
            }
            TermNode::Const { .. } => false,
        }
    }
    assertions.iter().any(|&a| walk(ctx, a))
}

#[cfg(test)]
mod tests {
    use super::*; // brings in Integer, Rational, BuiltinOp, Context, Op, TermId, TermNode

    /// A nullary uninterpreted constant of the given sort (codebase pattern —
    /// there is no `mk_const`).
    fn nullary(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], sort);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn eval_to_int_pinned_semantics() {
        assert_eq!(eval_to_int("0"), Integer::from(0i128));
        assert_eq!(eval_to_int("007"), Integer::from(7i128)); // leading zeros ok
        assert_eq!(eval_to_int("42"), Integer::from(42i128));
        assert_eq!(eval_to_int(""), Integer::from(-1i128)); // empty
        assert_eq!(eval_to_int("12a"), Integer::from(-1i128)); // non-digit
        assert_eq!(eval_to_int("-5"), Integer::from(-1i128)); // sign char
        assert_eq!(eval_to_int("+5"), Integer::from(-1i128));
        assert_eq!(eval_to_int(" 5"), Integer::from(-1i128)); // whitespace
                                                              // NON-ASCII digit trap: must be -1, NOT 3.
        assert_eq!(eval_to_int("\u{0663}"), Integer::from(-1i128)); // Arabic-Indic ٣
        assert_eq!(eval_to_int("\u{FF13}"), Integer::from(-1i128)); // fullwidth ３
                                                                    // Big int (no i128 overflow): 40-digit roundtrip.
        let big = "1234567890123456789012345678901234567890";
        assert_eq!(eval_to_int(big).to_string(), big);
    }

    #[test]
    fn eval_from_int_pinned_semantics() {
        assert_eq!(eval_from_int(&Integer::from(0i128)), "0");
        assert_eq!(eval_from_int(&Integer::from(42i128)), "42");
        assert_eq!(eval_from_int(&Integer::from(-1i128)), ""); // negative -> ""
        assert_eq!(eval_from_int(&Integer::from(-5i128)), "");
    }

    fn to_int(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToInt), &[s]).unwrap()
    }
    fn from_int(ctx: &mut Context, n: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrFromInt), &[n])
            .unwrap()
    }

    #[test]
    fn fold_literal_applications() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        // str.to_int("42") folds to the numeral 42.
        let lit = ctx.mk_string_const("42");
        let app = to_int(&mut ctx, lit);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(
            ctx.numeral_value(out[0]).map(|r| r.numer().to_string()),
            Some("42".to_string())
        );
        // str.from_int(-5) folds to "".
        let neg = ctx.mk_numeral(Rational::from_int(Integer::from(-5i128)), int_s);
        let app = from_int(&mut ctx, neg);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(ctx.string_const_value(out[0]), Some(""));
        // No survivor -> not fenced.
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn fold_from_int_of_neg_wrapped_numeral_literal() {
        // The SMT-LIB parser spells negative integer literals as `(- 5)` —
        // `BuiltinOp::Neg` applied to a numeral, NOT a single `Const` numeral
        // (see `int_literal`'s doc comment). This is the shape `str.from_int`
        // actually sees from parsed input for its spec-mandated negative case;
        // it must fold exactly like a directly-built negative `mk_numeral`.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let five = ctx.mk_numeral(Rational::from_int(Integer::from(5i128)), int_s);
        let neg_five = ctx.mk_app(Op::Builtin(BuiltinOp::Neg), &[five]).unwrap();
        let app = from_int(&mut ctx, neg_five);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(ctx.string_const_value(out[0]), Some(""));
        assert!(!has_unreduced_int_conv(&ctx, &out));
    }

    #[test]
    fn symbolic_application_survives_to_fence() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s); // symbolic string
        let app = to_int(&mut ctx, s);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert!(
            has_unreduced_int_conv(&ctx, &out),
            "symbolic to_int must fence"
        );
    }

    #[test]
    fn roundtrip_to_int_of_from_int_rewrites_to_ite() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s); // symbolic Int (helper from Task 3)
        let inner = from_int(&mut ctx, n);
        let app = to_int(&mut ctx, inner);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        // Neither str op survives -> not fenced.
        assert!(
            !has_unreduced_int_conv(&ctx, &out),
            "roundtrip must fully eliminate both ops"
        );
        // Top node is an Int-sorted ite.
        match ctx.term_node(out[0]) {
            TermNode::App { op, .. } => {
                assert_eq!(*op, Op::Builtin(BuiltinOp::Ite), "expected ite, got {op:?}");
            }
            other => panic!("expected ite app, got {other:?}"),
        }
        assert_eq!(ctx.sort_of(out[0]), int_s);
    }

    #[test]
    fn nested_literal_roundtrip_folds_through() {
        // str.to_int(str.from_int(42)) : from_int folds to "42", then to_int folds to 42.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let k = ctx.mk_numeral(Rational::from_int(Integer::from(42i128)), int_s);
        let inner = from_int(&mut ctx, k); // split: avoid double &mut ctx in one expr
        let app = to_int(&mut ctx, inner);
        let out = partial_eval_int_conv(&mut ctx, &[app]);
        assert_eq!(
            ctx.numeral_value(out[0]).map(|r| r.numer().to_string()),
            Some("42".to_string())
        );
    }
}
