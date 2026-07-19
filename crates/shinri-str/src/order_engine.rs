//! Slice 31: the online head-peel engine for two-symbolic-var `str.<`/`str.<=`.
//! The character-order comparison uses a dedicated UNINTERPRETED
//! `!strcode : String -> Int` function so EUF congruence-closes it
//! (`shinri-euf` congruences only `Op::Uninterpreted` apps). Range + on-demand
//! constant folding (Task 6) supply its semantics; nothing here uses
//! `str.to_code` (a Builtin, which EUF would not congruence).

use shinri_core::{BuiltinOp, Context, Integer, Op, Rational, SymbolId, TermId};

/// Arith-facing largest code point (mirror of `code_conv::MAX_CODE`).
#[allow(dead_code)] // used in Task 4/6
pub const MAX_CODE_I128: i128 = 0x2FFFF;

/// Declare-or-fetch the single `!strcode : String -> Int` symbol.
#[allow(dead_code)] // used in Task 4
pub fn code_fun(terms: &mut Context) -> SymbolId {
    let str_s = terms.string_sort();
    let int_s = terms.int_sort();
    terms.declare_fun("!strcode", &[str_s], int_s)
}

/// Build `(!strcode h)`.
#[allow(dead_code)] // used in Task 4
pub fn code_of(terms: &mut Context, h: TermId) -> TermId {
    let f = code_fun(terms);
    terms
        .mk_app(Op::Uninterpreted(f), &[h])
        .expect("!strcode well-sorted")
}

#[allow(dead_code)] // used in Task 4
fn int_lit(terms: &mut Context, k: i128) -> TermId {
    let int_s = terms.int_sort();
    terms.mk_numeral(Rational::from_int(Integer::from(k)), int_s)
}

/// `[ (>= code_h 0), (<= code_h MAX_CODE) ]`.
#[allow(dead_code)] // used in Task 4
pub fn range_atoms(terms: &mut Context, code_h: TermId) -> Vec<TermId> {
    let zero = int_lit(terms, 0);
    let hi = int_lit(terms, MAX_CODE_I128);
    let ge = terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[code_h, zero])
        .expect("ge");
    let le = terms
        .mk_app(Op::Builtin(BuiltinOp::Le), &[code_h, hi])
        .expect("le");
    vec![ge, le]
}

/// The surrogate-hole disjunction `(<= code_h 0xD7FF) ∨ (>= code_h 0xE000)`,
/// returned as the two disjunct atoms of a single split.
#[allow(dead_code)] // used in Task 4
pub fn surrogate_hole_atoms(terms: &mut Context, code_h: TermId) -> Vec<TermId> {
    let lo = int_lit(terms, 0xD7FF);
    let hi = int_lit(terms, 0xE000);
    let below = terms
        .mk_app(Op::Builtin(BuiltinOp::Le), &[code_h, lo])
        .expect("le");
    let above = terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[code_h, hi])
        .expect("ge");
    vec![below, above]
}

/// `(< ca cb)`.
#[allow(dead_code)] // used in Task 4
pub fn code_lt(terms: &mut Context, ca: TermId, cb: TermId) -> TermId {
    terms
        .mk_app(Op::Builtin(BuiltinOp::Lt), &[ca, cb])
        .expect("lt")
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op, TermNode};

    fn str_var(ctx: &mut Context, n: &str) -> TermId {
        let s = ctx.string_sort();
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn code_of_is_congruent_uninterpreted_int_app() {
        let mut ctx = Context::new();
        let h1 = str_var(&mut ctx, "h1");
        let c1 = code_of(&mut ctx, h1);
        // Same argument → same hash-consed term (functional at the term level).
        let c1b = code_of(&mut ctx, h1);
        assert_eq!(c1, c1b);
        // It is Int-sorted and headed by an Uninterpreted op (so EUF congruences it).
        assert_eq!(ctx.sort_of(c1), ctx.int_sort());
        assert!(matches!(
            ctx.term_node(c1),
            TermNode::App {
                op: Op::Uninterpreted(_),
                ..
            }
        ));
    }

    #[test]
    fn range_atoms_are_arith_inequalities() {
        let mut ctx = Context::new();
        let h = str_var(&mut ctx, "h");
        let code_h = code_of(&mut ctx, h);
        let atoms = range_atoms(&mut ctx, code_h);
        assert_eq!(atoms.len(), 2);
        for a in atoms {
            assert!(matches!(
                ctx.term_node(a),
                TermNode::App {
                    op: Op::Builtin(BuiltinOp::Ge | BuiltinOp::Le),
                    ..
                }
            ));
        }
    }
}
