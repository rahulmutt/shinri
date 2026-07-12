//! Slice 18 pre-pass: `str.to_code` / `str.from_code` / `str.is_digit` —
//! exact rewriting + fence.
//!
//! Every rewrite in this module is a FULL logical equivalence — sound at any
//! position, any polarity, any occurrence count. No model repair, no length
//! pins, no occurrence analysis (unlike int_conv's slice-17 stage): the
//! fragment is decided by a SINGLE bottom-up pass plus a presence fence.
//!
//! Stages (run by the solver's string-path seam, right after int_conv):
//! 1. [`rewrite_code_conv`] — bottom-up memoized rewrite applying the whole
//!    spec catalog (R1–R10): literal folds, both roundtrip rewrites,
//!    constant-RHS atom equivalences (either orientation), and `str.is_digit`
//!    expansion. (Lands in Tasks 2–3.)
//! 2. [`has_unreduced_code_conv`] — presence fence: any surviving
//!    application ⇒ the solver returns a sound `Unknown`.
//!
//! Representational fence: `Box<str>` cannot hold surrogate code points
//! (`0xD800..=0xDFFF`) even though the SMT-LIB alphabet includes them —
//! `from_code(<surrogate k>)` never folds and `to_code(s) = <surrogate k>`
//! never rewrites; both survive to the fence. Input literals cannot contain
//! surrogates (the parser does not decode `\u{...}` escapes), so the
//! literal side of an equality needs no surrogate case.

use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Integer, Op, Rational, TermId, TermNode};

use crate::int_conv::int_const_value;

/// Largest SMT-LIB string character (inclusive): U+2FFFF.
pub const MAX_CODE: i128 = 0x2FFFF;

fn is_surrogate(k: i128) -> bool {
    (0xD800..=0xDFFF).contains(&k)
}

/// The singleton string's char for in-alphabet, NON-surrogate `k`; None for
/// surrogates (in the SMT-LIB alphabet but unrepresentable in `Box<str>`)
/// and out-of-alphabet values.
fn char_of_code(k: i128) -> Option<char> {
    if !(0..=MAX_CODE).contains(&k) || is_surrogate(k) {
        return None;
    }
    char::from_u32(k as u32)
}

/// Concrete `str.to_code(s)` per SMT-LIB 2.6: the code point for a singleton,
/// `-1` otherwise. None (no fold) for a singleton ABOVE the SMT-LIB alphabet
/// — such a literal is not a valid String value; leave it to the fence.
fn eval_to_code(s: &str) -> Option<Integer> {
    let mut it = s.chars();
    match (it.next(), it.next()) {
        (Some(c), None) => {
            let code = c as u32 as i128;
            if code > MAX_CODE {
                return None;
            }
            Some(Integer::from(code))
        }
        _ => Some(Integer::from(-1i128)),
    }
}

/// Concrete `str.from_code(k)` per SMT-LIB 2.6: the singleton for in-alphabet
/// `k`, `""` for out-of-alphabet `k` (including values beyond i128). None
/// (no fold -> fence) for surrogates: representable in the SMT-LIB alphabet
/// but not in `Box<str>`.
fn eval_from_code(k: &Integer) -> Option<String> {
    match k.to_i128() {
        Some(v) if (0..=MAX_CODE).contains(&v) => char_of_code(v).map(String::from),
        _ => Some(String::new()),
    }
}

/// Single exact rewrite pass (spec R1–R10): bottom-up, memoized; untouched
/// subtrees keep their TermIds. Every rule is a full equivalence — no model
/// repair, no polarity tracking, no occurrence analysis.
pub fn rewrite_code_conv(ctx: &mut Context, assertions: &[TermId]) -> Vec<TermId> {
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
                Op::Builtin(BuiltinOp::StrToCode) => rewrite_to_code(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrFromCode) => rewrite_from_code(ctx, &new_children),
                Op::Builtin(BuiltinOp::StrIsDigit) => rewrite_is_digit(ctx, new_children[0]),
                Op::Builtin(BuiltinOp::Eq) => try_code_atom(ctx, &new_children),
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
                        .expect("code_conv: well-sorted rebuild")
                } else {
                    t
                }
            }
        }
    };
    memo.insert(t, result);
    result
}

/// `(str.to_code x)`, child already rewritten. R1 fold + R2 roundtrip.
/// None leaves the app in place (-> fence).
fn rewrite_to_code(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    // R1: fold a literal argument.
    if let Some(s) = ctx.string_const_value(kids[0]).map(str::to_owned) {
        let v = eval_to_code(&s)?;
        let int_s = ctx.int_sort();
        return Some(ctx.mk_numeral(Rational::from_int(v), int_s));
    }
    // R2: to_code(from_code(n)) → ite(0 <= n <= MAX_CODE, n, -1). Exact for
    // ALL n — surrogates included, since no literal is minted.
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrFromCode),
        args,
        ..
    } = ctx.term_node(kids[0]).clone()
    {
        let n = ctx.children(args)[0];
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(Rational::from_int(Integer::zero()), int_s);
        let max = ctx.mk_numeral(Rational::from_int(Integer::from(MAX_CODE)), int_s);
        let neg1 = ctx.mk_numeral(Rational::from_int(Integer::from(-1i128)), int_s);
        let ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero])
            .expect("n >= 0");
        let le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[n, max])
            .expect("n <= MAX_CODE");
        let in_range = ctx
            .mk_app(Op::Builtin(BuiltinOp::And), &[ge, le])
            .expect("range conj");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[in_range, n, neg1])
                .expect("roundtrip ite"),
        );
    }
    None
}

/// `(str.from_code x)`, child already rewritten. R1 fold + R3 roundtrip.
/// None leaves the app in place (-> fence; surrogate literals land here).
fn rewrite_from_code(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    // R1: fold a numeral argument (None on a surrogate -> fence).
    if let Some(k) = int_const_value(ctx, kids[0]) {
        let s = eval_from_code(&k)?;
        return Some(ctx.mk_string_const(&s));
    }
    // R3: from_code(to_code(s)) → ite(len(s) = 1, s, ""). Exact: for a
    // singleton the code roundtrips (surrogates cannot occur in s — Box<str>);
    // otherwise to_code = -1 and from_code(-1) = "".
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::StrToCode),
        args,
        ..
    } = ctx.term_node(kids[0]).clone()
    {
        let s = ctx.children(args)[0];
        let len = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[s])
            .expect("len");
        let int_s = ctx.int_sort();
        let one = ctx.mk_numeral(Rational::from_int(Integer::one()), int_s);
        let cond = ctx.mk_eq(len, one).expect("len = 1");
        let empty = ctx.mk_string_const("");
        return Some(
            ctx.mk_app(Op::Builtin(BuiltinOp::Ite), &[cond, s, empty])
                .expect("roundtrip ite"),
        );
    }
    None
}

/// `(str.is_digit x)`, child already rewritten. R1 fold for a literal; R10
/// expansion otherwise: `(or (= t "0") … (= t "9"))` — each minted equality
/// is routed back through the atom rules, so `is_digit(from_code(n))`
/// reduces fully in this same pass (no fixpoint loop).
fn rewrite_is_digit(ctx: &mut Context, t: TermId) -> Option<TermId> {
    if let Some(s) = ctx.string_const_value(t).map(str::to_owned) {
        let mut it = s.chars();
        let v = matches!((it.next(), it.next()), (Some('0'..='9'), None));
        return Some(ctx.mk_const_bool(v));
    }
    let disjuncts: Vec<TermId> = ('0'..='9')
        .map(|d| {
            let lit = ctx.mk_string_const(&d.to_string());
            let kids = [t, lit];
            try_code_atom(ctx, &kids)
                .unwrap_or_else(|| ctx.mk_eq(t, lit).expect("is_digit: t = digit"))
        })
        .collect();
    Some(
        ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disjuncts)
            .expect("is_digit expansion"),
    )
}

/// R4–R9: constant-RHS equality atoms, either orientation. Children are
/// already rewritten (so a foldable side has already folded). None → not a
/// code-conv atom, or the surrogate fence.
fn try_code_atom(ctx: &mut Context, kids: &[TermId]) -> Option<TermId> {
    if kids.len() != 2 {
        return None;
    }
    for (a, b) in [(kids[0], kids[1]), (kids[1], kids[0])] {
        match ctx.term_node(a).clone() {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrToCode),
                args,
                ..
            } => {
                let s = ctx.children(args)[0];
                if let Some(k) = int_const_value(ctx, b) {
                    return rw_to_code_const(ctx, s, &k);
                }
            }
            TermNode::App {
                op: Op::Builtin(BuiltinOp::StrFromCode),
                args,
                ..
            } => {
                let n = ctx.children(args)[0];
                if let Some(lit) = ctx.string_const_value(b).map(str::to_owned) {
                    return Some(rw_from_code_const(ctx, n, &lit));
                }
            }
            _ => {}
        }
    }
    None
}

/// R4/R5/R6: `(= (str.to_code s) k)` — a full partition of k:
/// `-1` ⇒ `not (len(s) = 1)`; in-alphabet non-surrogate ⇒ `s = "<char k>"`;
/// surrogate ⇒ None (representational fence); anything else ⇒ `false`.
fn rw_to_code_const(ctx: &mut Context, s: TermId, k: &Integer) -> Option<TermId> {
    match k.to_i128() {
        Some(-1) => {
            let len = ctx
                .mk_app(Op::Builtin(BuiltinOp::StrLen), &[s])
                .expect("len");
            let int_s = ctx.int_sort();
            let one = ctx.mk_numeral(Rational::from_int(Integer::one()), int_s);
            let eq1 = ctx.mk_eq(len, one).expect("len = 1");
            Some(
                ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq1])
                    .expect("not singleton"),
            )
        }
        Some(v) if (0..=MAX_CODE).contains(&v) => {
            let c = char_of_code(v)?; // surrogate → fence
            let lit = ctx.mk_string_const(&c.to_string());
            Some(ctx.mk_eq(s, lit).expect("s = char"))
        }
        // k <= -2, k > MAX_CODE, or |k| beyond i128: outside to_code's range.
        _ => Some(ctx.mk_const_bool(false)),
    }
}

/// R7/R8/R9: `(= (str.from_code n) "lit")`.
fn rw_from_code_const(ctx: &mut Context, n: TermId, lit: &str) -> TermId {
    if lit.is_empty() {
        // R8: the out-of-alphabet escape — n < 0 ∨ n > MAX_CODE.
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(Rational::from_int(Integer::zero()), int_s);
        let max = ctx.mk_numeral(Rational::from_int(Integer::from(MAX_CODE)), int_s);
        let lt = ctx
            .mk_app(Op::Builtin(BuiltinOp::Lt), &[n, zero])
            .expect("n < 0");
        let gt = ctx
            .mk_app(Op::Builtin(BuiltinOp::Gt), &[n, max])
            .expect("n > MAX_CODE");
        return ctx
            .mk_app(Op::Builtin(BuiltinOp::Or), &[lt, gt])
            .expect("escape disj");
    }
    let mut it = lit.chars();
    match (it.next(), it.next()) {
        // R7: from_code is injective on the alphabet ⇒ n = code(c).
        (Some(c), None) if (c as u32 as i128) <= MAX_CODE => {
            let int_s = ctx.int_sort();
            let code = ctx.mk_numeral(Rational::from_int(Integer::from(c as u32 as i128)), int_s);
            ctx.mk_eq(n, code).expect("n = code")
        }
        // R9: multi-char, or a singleton above the alphabet — outside
        // from_code's range.
        _ => ctx.mk_const_bool(false),
    }
}

/// Presence fence: true iff any `str.to_code` / `str.from_code` /
/// `str.is_digit` application survived [`rewrite_code_conv`].
pub fn has_unreduced_code_conv(ctx: &Context, assertions: &[TermId]) -> bool {
    fn walk(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App { op, args, .. } => {
                matches!(
                    op,
                    Op::Builtin(
                        BuiltinOp::StrToCode | BuiltinOp::StrFromCode | BuiltinOp::StrIsDigit
                    )
                ) || ctx.children(*args).to_vec().iter().any(|&c| walk(ctx, c))
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
    fn to_code(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrToCode), &[s]).unwrap()
    }
    fn from_code(ctx: &mut Context, n: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrFromCode), &[n])
            .unwrap()
    }
    fn is_digit(ctx: &mut Context, s: TermId) -> TermId {
        ctx.mk_app(Op::Builtin(BuiltinOp::StrIsDigit), &[s])
            .unwrap()
    }
    fn int_lit(ctx: &mut Context, v: i128) -> TermId {
        let int_s = ctx.int_sort();
        ctx.mk_numeral(Rational::from_int(Integer::from(v)), int_s)
    }

    #[test]
    fn eval_to_code_pinned_semantics() {
        assert_eq!(eval_to_code("a"), Some(Integer::from(97i128)));
        assert_eq!(eval_to_code("0"), Some(Integer::from(48i128)));
        assert_eq!(eval_to_code(""), Some(Integer::from(-1i128))); // empty
        assert_eq!(eval_to_code("ab"), Some(Integer::from(-1i128))); // multi-char
        assert_eq!(eval_to_code("\u{2FFFF}"), Some(Integer::from(0x2FFFFi128)));
        // A char ABOVE the SMT-LIB alphabet: not a valid String value — no fold.
        assert_eq!(eval_to_code("\u{30000}"), None);
    }

    #[test]
    fn eval_from_code_pinned_semantics() {
        assert_eq!(eval_from_code(&Integer::from(97i128)), Some("a".to_owned()));
        assert_eq!(
            eval_from_code(&Integer::from(0i128)),
            Some("\u{0}".to_owned())
        );
        assert_eq!(
            eval_from_code(&Integer::from(0x2FFFFi128)),
            Some("\u{2FFFF}".to_owned())
        );
        // Out of the alphabet (negative / too large) -> "".
        assert_eq!(eval_from_code(&Integer::from(-1i128)), Some(String::new()));
        assert_eq!(
            eval_from_code(&Integer::from(0x30000i128)),
            Some(String::new())
        );
        // A value too large for i128 is certainly out of the alphabet -> "".
        let huge = Integer::from_str_radix("1234567890123456789012345678901234567890", 10).unwrap();
        assert_eq!(eval_from_code(&huge), Some(String::new()));
        // Surrogates: unrepresentable -> None (fence).
        assert_eq!(eval_from_code(&Integer::from(0xD800i128)), None);
        assert_eq!(eval_from_code(&Integer::from(0xDFFFi128)), None);
        // Surrogate-block edges DO fold.
        assert_eq!(
            eval_from_code(&Integer::from(0xD7FFi128)),
            Some("\u{D7FF}".to_owned())
        );
        assert_eq!(
            eval_from_code(&Integer::from(0xE000i128)),
            Some("\u{E000}".to_owned())
        );
    }

    #[test]
    fn folds_literal_applications() {
        let mut ctx = Context::new();
        let a_lit = ctx.mk_string_const("a");
        let tc = to_code(&mut ctx, a_lit);
        let k97 = int_lit(&mut ctx, 97);
        let fc = from_code(&mut ctx, k97);
        let idig = is_digit(&mut ctx, a_lit);
        let seven = ctx.mk_string_const("7");
        let idig7 = is_digit(&mut ctx, seven);

        let out = rewrite_code_conv(&mut ctx, &[tc, fc, idig, idig7]);
        // to_code("a") -> 97 (hash-consed: same id as the numeral).
        assert_eq!(out[0], int_lit(&mut ctx, 97));
        // from_code(97) -> "a".
        assert_eq!(out[1], ctx.mk_string_const("a"));
        // is_digit("a") -> false; is_digit("7") -> true.
        assert_eq!(out[2], ctx.mk_const_bool(false));
        assert_eq!(out[3], ctx.mk_const_bool(true));
    }

    #[test]
    fn surrogate_from_code_does_not_fold() {
        let mut ctx = Context::new();
        let k = int_lit(&mut ctx, 0xD800);
        let fc = from_code(&mut ctx, k);
        let out = rewrite_code_conv(&mut ctx, &[fc]);
        assert_eq!(out[0], fc, "surrogate from_code must survive to the fence");
        assert!(has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn roundtrip_to_code_of_from_code() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fc = from_code(&mut ctx, n);
        let tc = to_code(&mut ctx, fc);
        let out = rewrite_code_conv(&mut ctx, &[tc]);
        // ite(and(n >= 0, n <= MAX_CODE), n, -1)
        let zero = int_lit(&mut ctx, 0);
        let max = int_lit(&mut ctx, MAX_CODE);
        let neg1 = int_lit(&mut ctx, -1);
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero]).unwrap();
        let le = ctx.mk_app(Op::Builtin(BuiltinOp::Le), &[n, max]).unwrap();
        let in_range = ctx.mk_app(Op::Builtin(BuiltinOp::And), &[ge, le]).unwrap();
        let want = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[in_range, n, neg1])
            .unwrap();
        assert_eq!(out[0], want);
        assert!(!has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn roundtrip_from_code_of_to_code() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);
        let fc = from_code(&mut ctx, tc);
        let out = rewrite_code_conv(&mut ctx, &[fc]);
        // ite(len(s) = 1, s, "")
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[s]).unwrap();
        let one = int_lit(&mut ctx, 1);
        let cond = ctx.mk_eq(len, one).unwrap();
        let empty = ctx.mk_string_const("");
        let want = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ite), &[cond, s, empty])
            .unwrap();
        assert_eq!(out[0], want);
        assert!(!has_unreduced_code_conv(&ctx, &out));
    }

    #[test]
    fn untouched_subtrees_keep_their_termids() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let t = nullary(&mut ctx, "t", str_s);
        // An assertion with NO code-conv content at all.
        let eq = ctx.mk_eq(s, t).unwrap();
        let out = rewrite_code_conv(&mut ctx, &[eq]);
        assert_eq!(out[0], eq, "no-op inputs must keep their TermId");
    }

    /// Convenience: rewrite a single assertion.
    fn rw1(ctx: &mut Context, t: TermId) -> TermId {
        rewrite_code_conv(ctx, &[t])[0]
    }

    #[test]
    fn to_code_const_rhs_boundary_lattice() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);

        // R4: in-alphabet, non-surrogate k ⇒ s = "<char k>". Check the edges
        // and a digit: 0, '9' (0x39), 0xD7FF, 0xE000, MAX_CODE.
        for k in [0i128, 0x39, 0xD7FF, 0xE000, MAX_CODE] {
            let kt = int_lit(&mut ctx, k);
            let atom = ctx.mk_eq(tc, kt).unwrap();
            let lit = ctx.mk_string_const(&char::from_u32(k as u32).unwrap().to_string());
            let want = ctx.mk_eq(s, lit).unwrap();
            assert_eq!(rw1(&mut ctx, atom), want, "k = {k:#x}");
        }

        // R5: k = -1 ⇒ not (len(s) = 1).
        let neg1 = int_lit(&mut ctx, -1);
        let atom = ctx.mk_eq(tc, neg1).unwrap();
        let len = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[s]).unwrap();
        let one = int_lit(&mut ctx, 1);
        let eq1 = ctx.mk_eq(len, one).unwrap();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[eq1]).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);

        // R6: k <= -2 or k > MAX_CODE ⇒ false.
        for k in [-2i128, 0x30000] {
            let kt = int_lit(&mut ctx, k);
            let atom = ctx.mk_eq(tc, kt).unwrap();
            assert_eq!(rw1(&mut ctx, atom), ctx.mk_const_bool(false), "k = {k}");
        }

        // Surrogate k: representational fence — the atom must SURVIVE.
        for k in [0xD800i128, 0xDFFF] {
            let kt = int_lit(&mut ctx, k);
            let atom = ctx.mk_eq(tc, kt).unwrap();
            let out = rw1(&mut ctx, atom);
            assert_eq!(out, atom, "surrogate k = {k:#x} must fence");
            assert!(has_unreduced_code_conv(&ctx, &[out]));
        }
    }

    #[test]
    fn to_code_const_rhs_matches_either_orientation() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);
        let k = int_lit(&mut ctx, 97);
        // (= 97 (str.to_code s)) — literal on the LEFT.
        let atom = ctx.mk_eq(k, tc).unwrap();
        let a_lit = ctx.mk_string_const("a");
        let want = ctx.mk_eq(s, a_lit).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);
    }

    #[test]
    fn to_code_const_rhs_under_negation_and_or() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let tc = to_code(&mut ctx, s);
        let k = int_lit(&mut ctx, 97);
        let atom = ctx.mk_eq(tc, k).unwrap();
        let neg = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[atom]).unwrap();
        let bool_s = ctx.bool_sort();
        let t = nullary(&mut ctx, "p", bool_s);
        let or = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[neg, t]).unwrap();

        let a_lit = ctx.mk_string_const("a");
        let want_eq = ctx.mk_eq(s, a_lit).unwrap();
        let want_neg = ctx.mk_app(Op::Builtin(BuiltinOp::Not), &[want_eq]).unwrap();
        let want = ctx
            .mk_app(Op::Builtin(BuiltinOp::Or), &[want_neg, t])
            .unwrap();
        assert_eq!(rw1(&mut ctx, or), want);
    }

    #[test]
    fn from_code_const_rhs_shapes() {
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fc = from_code(&mut ctx, n);

        // R7: singleton literal ⇒ n = code.
        let a_lit = ctx.mk_string_const("a");
        let atom = ctx.mk_eq(fc, a_lit).unwrap();
        let k97 = int_lit(&mut ctx, 97);
        let want = ctx.mk_eq(n, k97).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);

        // R8: empty literal ⇒ n < 0 ∨ n > MAX_CODE.
        let empty = ctx.mk_string_const("");
        let atom = ctx.mk_eq(fc, empty).unwrap();
        let zero = int_lit(&mut ctx, 0);
        let max = int_lit(&mut ctx, MAX_CODE);
        let lt = ctx.mk_app(Op::Builtin(BuiltinOp::Lt), &[n, zero]).unwrap();
        let gt = ctx.mk_app(Op::Builtin(BuiltinOp::Gt), &[n, max]).unwrap();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &[lt, gt]).unwrap();
        assert_eq!(rw1(&mut ctx, atom), want);

        // R9: multi-char literal ⇒ false; above-alphabet singleton ⇒ false.
        for lit in ["ab", "\u{30000}"] {
            let l = ctx.mk_string_const(lit);
            let atom = ctx.mk_eq(fc, l).unwrap();
            assert_eq!(rw1(&mut ctx, atom), ctx.mk_const_bool(false), "lit {lit:?}");
        }
    }

    #[test]
    fn is_digit_expands_to_ten_way_disjunction() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let idig = is_digit(&mut ctx, s);
        let out = rw1(&mut ctx, idig);
        let disjuncts: Vec<TermId> = ('0'..='9')
            .map(|d| {
                let lit = ctx.mk_string_const(&d.to_string());
                ctx.mk_eq(s, lit).unwrap()
            })
            .collect();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disjuncts).unwrap();
        assert_eq!(out, want);
        assert!(!has_unreduced_code_conv(&ctx, &[out]));
    }

    #[test]
    fn is_digit_of_from_code_reduces_fully_in_one_pass() {
        // The minted-atom chain: is_digit(from_code(n)) must become a pure
        // LIA disjunction n = 48 ∨ … ∨ n = 57 — R10 routing each minted
        // equality through R7.
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let n = nullary(&mut ctx, "n", int_s);
        let fc = from_code(&mut ctx, n);
        let idig = is_digit(&mut ctx, fc);
        let out = rw1(&mut ctx, idig);
        let disjuncts: Vec<TermId> = (48i128..=57)
            .map(|code| {
                let k = int_lit(&mut ctx, code);
                ctx.mk_eq(n, k).unwrap()
            })
            .collect();
        let want = ctx.mk_app(Op::Builtin(BuiltinOp::Or), &disjuncts).unwrap();
        assert_eq!(out, want);
        assert!(!has_unreduced_code_conv(&ctx, &[out]));
    }

    #[test]
    fn symbolic_linking_still_fences() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let int_s = ctx.int_sort();
        let s = nullary(&mut ctx, "s", str_s);
        let n = nullary(&mut ctx, "n", int_s);
        let tc = to_code(&mut ctx, s);
        // (= (str.to_code s) n): symbolic RHS — no rule applies.
        let atom = ctx.mk_eq(tc, n).unwrap();
        let out = rw1(&mut ctx, atom);
        assert_eq!(out, atom);
        assert!(has_unreduced_code_conv(&ctx, &[out]));
    }
}
