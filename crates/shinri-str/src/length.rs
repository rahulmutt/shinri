use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermId, TermNode};

/// Build `(>= len_term 0)`.
fn ge_zero(terms: &mut Context, len_term: TermId) -> TermId {
    let int_s = terms.int_sort();
    let zero = terms.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
    terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_term, zero])
        .expect("well-sorted")
}

/// For `str.len(arg)`, the defining equation atom, or None if `arg` is an opaque variable.
fn defining_eq(terms: &mut Context, len_term: TermId, arg: TermId) -> Option<TermId> {
    // Clone the node to avoid borrow conflict with later mut calls.
    match terms.term_node(arg).clone() {
        TermNode::Const {
            val: ConstVal::String(_),
            ..
        } => {
            let n = terms.string_const_value(arg).unwrap().chars().count() as i128;
            let int_s = terms.int_sort();
            let k = terms.mk_numeral(shinri_core::Rational::from_int(n.into()), int_s);
            Some(terms.mk_eq(len_term, k).expect("well-sorted"))
        }
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            args,
            ..
        } => {
            // Collect children before mutating.
            let kids = terms.children(args).to_vec();
            let parts: Vec<TermId> = kids
                .iter()
                .map(|&c| {
                    terms
                        .mk_app(Op::Builtin(BuiltinOp::StrLen), &[c])
                        .expect("well-sorted")
                })
                .collect();
            let sum = terms
                .mk_app(Op::Builtin(BuiltinOp::Add), &parts)
                .expect("well-sorted");
            Some(terms.mk_eq(len_term, sum).expect("well-sorted"))
        }
        _ => None,
    }
}

/// Return the next axiom for `len_term` not yet emitted, or `None` if all are done.
///
/// Axiom order per `len_term`:
/// 1. `(>= len_term 0)`
/// 2. `(= len_term k)` if arg is a string literal  —or—
///    `(= len_term (+ (str.len a) (str.len b) ...))` if arg is a concat
pub fn next_axiom(
    terms: &mut Context,
    len_term: TermId,
    emitted: &FxHashSet<TermId>,
) -> Option<TermId> {
    // Extract the single argument of the str.len application.
    let arg = match terms.term_node(len_term).clone() {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrLen),
            args,
            ..
        } => terms.children(args)[0],
        _ => return None,
    };

    // Axiom 1: >= 0
    let ge = ge_zero(terms, len_term);
    if !emitted.contains(&ge) {
        return Some(ge);
    }

    // Axiom 2: structural defining equation (literal or concat)
    if let Some(eqn) = defining_eq(terms, len_term, arg) {
        if !emitted.contains(&eqn) {
            return Some(eqn);
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};
    use crate::StrSolver;

    #[test]
    fn emits_literal_length_axiom() {
        // "café" has 4 Unicode scalar values but 5 UTF-8 bytes.
        // The axiom must be (= (str.len "café") 4), not 5.
        let mut ctx = Context::new();
        // Build the string literal "café".
        let lit = ctx.mk_string_const("café");
        let len_lit = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[lit])
            .unwrap();
        // Wire into solver via an arith atom (>= (str.len "café") 0).
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_lit, zero])
            .unwrap();

        // Build the expected axiom: (= (str.len "café") 4).
        let four = ctx.mk_numeral(shinri_core::Rational::from_int(4i128.into()), int_s);
        let expected_axiom = ctx.mk_eq(len_lit, four).unwrap();
        // Sanity: "café" has exactly 4 chars (not 5 bytes).
        assert_eq!("café".chars().count(), 4, "sanity: char count");
        assert_eq!("café".len(), 5, "sanity: byte count");

        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);

        // Drive check until Sat, collecting all split axioms.
        let mut found_literal_axiom = false;
        for _ in 0..8 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split { atoms: a, .. } => {
                    assert_eq!(a.len(), 1, "length axioms are unit lemmas");
                    if a[0] == expected_axiom {
                        found_literal_axiom = true;
                    }
                }
                TCheck::Sat => break,
                TCheck::Conflict(_) => panic!("no conflict expected"),
            }
        }
        assert!(
            found_literal_axiom,
            "must emit (= (str.len \"café\") 4) — char count, not byte count"
        );
        assert!(
            matches!(s.check(&mut cx, Effort::Full), TCheck::Sat),
            "fixpoint after all axioms emitted"
        );
    }

    #[test]
    fn emits_concat_length_axiom() {
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");
        let cc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        let len_cc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrLen), &[cc])
            .unwrap();
        let zero = ctx.mk_numeral(
            shinri_core::Rational::from_int(0i128.into()),
            ctx.int_sort(),
        );
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_cc, zero])
            .unwrap();

        let mut s = StrSolver::default();
        let mut eq = EqualityEngine::default();
        let areg = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq,
            atoms: &areg,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), atom);
        // The solver must, over successive checks, emit len(x++y) = len(x)+len(y) and len >= 0 axioms.
        let mut emitted = 0;
        for _ in 0..8 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split { atoms: a, .. } => {
                    assert_eq!(a.len(), 1, "length axioms are unit lemmas");
                    emitted += 1;
                }
                TCheck::Sat => break,
                TCheck::Conflict(_) => panic!("no conflict expected"),
            }
        }
        assert!(
            emitted >= 2,
            "must emit at least the >=0 and concat-sum axioms"
        );
        assert!(
            matches!(s.check(&mut cx, Effort::Full), TCheck::Sat),
            "fixpoint after all axioms emitted"
        );
    }
}
