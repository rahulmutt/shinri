use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermId, TermNode};
use shinri_theory::EqualityEngine;

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

/// Attempt to resolve the EUF class representative of `arg` to a string
/// constant. Returns the constant TermId if `arg` is in a class with a known
/// string constant (e.g. because `x = ""` was merged), or `None` otherwise.
///
/// This enables `next_axiom` to emit the defining equation `(= len_term k)`
/// even when `arg` is an opaque variable whose value was set via EUF merging
/// (N-O boundary: the String theory discovers the variable's value via
/// the shared EqualityEngine).
fn euf_representative_const(
    terms: &Context,
    eq: &mut EqualityEngine,
    arg: TermId,
    known: &[TermId],
) -> Option<TermId> {
    // Build an ENodeId → preferred TermId map, preferring constants.
    let mut node_of: rustc_hash::FxHashMap<shinri_theory::types::ENodeId, TermId> =
        rustc_hash::FxHashMap::default();
    for &t in known {
        let n = eq.intern(t);
        let root = eq.find(n);
        let is_str_const = matches!(
            terms.term_node(t),
            TermNode::Const { val: ConstVal::String(_), .. }
        );
        match node_of.get(&root).copied() {
            None => { node_of.insert(root, t); }
            Some(prev) => {
                let prev_is_const = matches!(
                    terms.term_node(prev),
                    TermNode::Const { val: ConstVal::String(_), .. }
                );
                if is_str_const && !prev_is_const {
                    node_of.insert(root, t);
                }
            }
        }
    }
    let arg_n = eq.intern(arg);
    let arg_root = eq.find(arg_n);
    let rep = *node_of.get(&arg_root)?;
    // Only return if it's a string constant (not an opaque variable).
    if matches!(terms.term_node(rep), TermNode::Const { val: ConstVal::String(_), .. }) {
        Some(rep)
    } else {
        None
    }
}

/// Return the next axiom for `len_term` not yet emitted, or `None` if all are done.
///
/// Axiom order per `len_term`:
/// 1. `(>= len_term 0)`
/// 2. `(= len_term k)` if arg is a string literal — or if the EUF has merged arg
///    with a string constant (N-O: e.g. `x = ""` was asserted, so len(x) = 0) —
///    or `(= len_term (+ (str.len a) (str.len b) ...))` if arg is a concat.
/// 3. `(=> (= len_term 0) (= arg ""))` — the empty-length link (valid tautology).
///    Emitted once per `len_term` with `guard: None` since it is unconditionally
///    true: a string has length 0 iff it is empty.
///
/// `eq` and `known` are used to check the EUF representative of `arg` so that
/// when a string variable is merged with a constant (e.g. `x = ""`), the
/// defining equation is emitted eagerly via N-O.
pub fn next_axiom(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
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

    // Axiom 2: structural defining equation (literal or concat).
    // First try the structural form of `arg` directly.
    // If arg is opaque but its EUF class representative is a string constant
    // (e.g. x = "" was asserted), use the representative instead.
    let effective_arg = match terms.term_node(arg).clone() {
        TermNode::Const { val: ConstVal::String(_), .. } | TermNode::App { op: Op::Builtin(BuiltinOp::StrConcat), .. } => arg,
        _ => {
            // Try to resolve via EUF.
            euf_representative_const(terms, eq, arg, known).unwrap_or(arg)
        }
    };
    if let Some(eqn) = defining_eq(terms, len_term, effective_arg) {
        if !emitted.contains(&eqn) {
            return Some(eqn);
        }
    }

    // Axiom 3: empty-length link `(=> (= len_term 0) (= arg ""))`
    //
    // This is a valid tautology over string algebra: `len(s) = 0 ↔ s = ""`.
    // It is emitted with `guard: None` (a unit tautology split) so the SAT
    // layer asserts it unconditionally. The implication is built as a single
    // `Implies` Boolean atom: `(=> (= len_term 0) (= arg ""))`.
    let empty_link = empty_length_link(terms, len_term, arg);
    if !emitted.contains(&empty_link) {
        return Some(empty_link);
    }

    None
}

/// Build `(=> (= len_term 0) (= arg ""))`.
fn empty_length_link(terms: &mut Context, len_term: TermId, arg: TermId) -> TermId {
    let int_s = terms.int_sort();
    let zero = terms.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
    // Antecedent: (= len_term 0)
    let len_eq_zero = terms.mk_eq(len_term, zero).expect("well-sorted");
    // Consequent: (= arg "")
    let empty = terms.mk_string_const("");
    let arg_eq_empty = terms.mk_eq(arg, empty).expect("well-sorted");
    // Implication: (=> antecedent consequent)
    terms
        .mk_app(Op::Builtin(BuiltinOp::Implies), &[len_eq_zero, arg_eq_empty])
        .expect("well-sorted")
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
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
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
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
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
