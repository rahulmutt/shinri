use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermId, TermNode};
use shinri_theory::EqualityEngine;

/// If `atom` is an equality `(= a b)` over Int/Real operands, return its
/// arithmetic companions `((>= a b), (<= a b))`. Returns `None` for non-equality
/// or non-arith-sorted atoms.
///
/// A bare arith equality emitted by a theory is classified to EUF (the top-level
/// `lower()` pass that adds Le/Ge companions does not run on theory-emitted
/// atoms), so it never reaches the Arith solver. Emitting the Le/Ge companions —
/// which DO route to Arith — is what makes a length equality actually enforced.
pub fn arith_eq_companions(terms: &mut Context, atom: TermId) -> Option<(TermId, TermId)> {
    let (a, b) = match terms.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Eq),
            args,
            ..
        } => {
            let ch = terms.children(*args);
            if ch.len() != 2 {
                return None;
            }
            (ch[0], ch[1])
        }
        _ => return None,
    };
    let s = terms.sort_of(a);
    if s != terms.int_sort() && s != terms.real_sort() {
        return None;
    }
    let ge = terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[a, b])
        .expect("(>= a b) well-sorted");
    let le = terms
        .mk_app(Op::Builtin(BuiltinOp::Le), &[a, b])
        .expect("(<= a b) well-sorted");
    Some((ge, le))
}

/// Build `(>= len_term 0)`.
fn ge_zero(terms: &mut Context, len_term: TermId) -> TermId {
    let int_s = terms.int_sort();
    let zero = terms.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
    terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_term, zero])
        .expect("well-sorted")
}

/// For `str.len(a)` where `a` is a bare string VARIABLE, build the two
/// disjuncts of the emptiness tautology `(or (= a "") (>= (str.len a) 1))`.
/// Returns `None` for any other shape.
///
/// The clause is VALID in the SMT-LIB String theory for every string term: a
/// string is either empty or has length at least one. Being a tautology, it is
/// entailed at level 0 unconditionally and needs NO guard — unlike the
/// merge-derived length lemmas in this module, it has no antecedents that a
/// backtracked branch could invalidate.
///
/// Its purpose is to close the one-way N–O seam: arith owns lengths and the
/// string theory owns word equations, so when arith derives `len(a) = 0`
/// nothing today tells the string theory that `a = ""`. Under `len(a) ≤ 0` the
/// arith disjunct is false and unit propagation forces `a = ""` into EUF.
///
/// **Qualifier — bare leaf variables only.** `a` must be an uninterpreted
/// NULLARY symbol and not a string constant. Concat lengths, literal lengths,
/// and any compound are declined. This is the flood control: emission is then
/// bounded by the number of string variables rather than the number of
/// `str.len` terms, and concat lengths — the terms that multiply as the
/// word-equation engine rewrites — contribute nothing. Emitting an empty-link
/// for EVERY `str.len` term is the shape documented at the bottom of this file
/// as livelocking concat+length queries; do not widen this qualifier without
/// re-running the timing gate.
#[allow(dead_code)]
pub fn empty_length_tautology(terms: &mut Context, len_term: TermId) -> Option<(TermId, TermId)> {
    // Extract the single argument of the str.len application.
    let arg = match terms.term_node(len_term).clone() {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrLen),
            args,
            ..
        } => terms.children(args)[0],
        _ => return None,
    };

    // Qualifier: a bare uninterpreted nullary symbol, not a string constant.
    // Mirrors the `all_var` predicate the empty-residual lemma uses
    // (lib.rs:577-586) rather than inventing a second notion of leafness.
    let is_bare_var = terms.string_const_value(arg).is_none()
        && match terms.term_node(arg) {
            TermNode::App {
                op: Op::Uninterpreted(_),
                args,
                ..
            } => terms.children(*args).is_empty(),
            _ => false,
        };
    if !is_bare_var {
        return None;
    }

    let empty = terms.mk_string_const("");
    let eq_empty = terms.mk_eq(arg, empty).expect("(= a \"\") well-sorted");
    let int_s = terms.int_sort();
    let one = terms.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
    let ge_one = terms
        .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_term, one])
        .expect("(>= (str.len a) 1) well-sorted");
    Some((eq_empty, ge_one))
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
            TermNode::Const {
                val: ConstVal::String(_),
                ..
            }
        );
        match node_of.get(&root).copied() {
            None => {
                node_of.insert(root, t);
            }
            Some(prev) => {
                let prev_is_const = matches!(
                    terms.term_node(prev),
                    TermNode::Const {
                        val: ConstVal::String(_),
                        ..
                    }
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
    if matches!(
        terms.term_node(rep),
        TermNode::Const {
            val: ConstVal::String(_),
            ..
        }
    ) {
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
///
/// The empty-length link `len(s)=0 → s=""` is NOT emitted here — see
/// the solver's non-empty-length lemma, emitted on demand only for `s ≠ ""`
/// disequalities (the soundness-relevant case).
///
/// `eq` and `known` are used to check the EUF representative of `arg` so that
/// when a string variable is merged with a constant (e.g. `x = ""`), the
/// defining equation is emitted eagerly via N-O.
/// `lit_lvl` (E1 iter 3): maps each asserted string (dis)equality literal to its
/// decision level. The EUF-representative resolution of an opaque variable's length
/// (`x ≈ const` ⟹ `len(x)=const-length`) emits an UNCONDITIONAL `guard=None` unit
/// pinned at dl0, so it is sound ONLY when the SPECIFIC merge `arg ≈ rep` that
/// discovered the constant is itself unconditionally entailed — every proof-forest
/// antecedent of that merge is a level-0 literal. iter-2 gated this coarsely (skip
/// whenever ANY conditional equality was active); this is ANTECEDENT-PRECISE: an
/// unrelated conditional (dis)equality no longer suppresses a `len(x)=k` whose own
/// `x ≈ const` merge is dl0. Structural axioms (arg literally a constant / concat)
/// are unaffected — they read `arg`'s syntax, not the merge map.
pub fn next_axiom(
    terms: &mut Context,
    eq: &mut EqualityEngine,
    known: &[TermId],
    len_term: TermId,
    emitted: &FxHashSet<TermId>,
    lit_lvl: &rustc_hash::FxHashMap<shinri_core::Lit, u32>,
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
        TermNode::Const {
            val: ConstVal::String(_),
            ..
        }
        | TermNode::App {
            op: Op::Builtin(BuiltinOp::StrConcat),
            ..
        } => arg,
        _ => {
            // Try to resolve via EUF — but only when the SPECIFIC merge `arg ≈ rep`
            // is unconditionally entailed (every proof-forest antecedent is dl0). A
            // branch-local merge (a decided disjunct `x="a"`, or a minted char-peel
            // `x=""`) must NOT pin a global `len(x)=k` (ce1/ce3/ce4). Leave `arg`
            // opaque otherwise so `defining_eq` yields `None`.
            match euf_representative_const(terms, eq, arg, known) {
                Some(rep) => {
                    let an = eq.intern(arg);
                    let rn = eq.intern(rep);
                    let mut leaves = Vec::new();
                    eq.explain(an, rn, &mut leaves);
                    if crate::leaves_all_dl0(&leaves, lit_lvl) {
                        rep
                    } else {
                        arg
                    }
                }
                None => arg,
            }
        }
    };
    if let Some(eqn) = defining_eq(terms, len_term, effective_arg) {
        // The defining equation `(= len_term k|Σ)` is an arith EQUALITY; a bare
        // theory-emitted Int equality routes to EUF (not Arith) and is held
        // opaquely, so arith never learns the numeric relation. Emit its `(>= )`
        // and `(<= )` companions (which DO route to Arith) one at a time across
        // successive rounds — together they entail the equality, which is what
        // makes length reasoning over concats effective (e.g.
        // `len(x)=1 ∧ len(y)=1 ∧ len(x++y)=5` UNSAT). We mark `eqn` emitted only
        // once BOTH companions are out, so this is re-entered until done.
        if let Some((ge_c, le_c)) = arith_eq_companions(terms, eqn) {
            if !emitted.contains(&ge_c) {
                return Some(ge_c);
            }
            if !emitted.contains(&le_c) {
                return Some(le_c);
            }
        } else if !emitted.contains(&eqn) {
            return Some(eqn);
        }
    }

    // NOTE: the empty-length link `len(s)=0 → s=""` is NOT emitted here. The
    // solver emits, on demand, the guarded lemma `(s≠"") → len(s)≥1` (a pure-arith
    // consequent) and ONLY for `s ≠ ""` disequalities — the only place it is
    // soundness-relevant. Emitting an empty-link for every `str.len` term
    // (including every fresh F-split skolem's length) floods the shared-Int
    // MBTC / N-O exchange and causes a livelock on concat+length queries.
    None
}

#[cfg(test)]
mod tests {
    use crate::StrSolver;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    #[test]
    fn emits_literal_length_axiom() {
        // "café" has 4 Unicode scalar values but 5 UTF-8 bytes.
        // The axiom must be (= (str.len "café") 4), not 5.
        let mut ctx = Context::new();
        // Build the string literal "café".
        let lit = ctx.mk_string_const("café");
        let len_lit = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[lit]).unwrap();
        // Wire into solver via an arith atom (>= (str.len "café") 0).
        let int_s = ctx.int_sort();
        let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_lit, zero])
            .unwrap();

        // The defining equation `(= (str.len "café") 4)` is emitted through its
        // arith companions `(>= (str.len "café") 4)` and `(<= (str.len "café") 4)`
        // (a bare Int equality would route to EUF, not Arith — see the seam note
        // in `next_axiom`). Expect both to be emitted (char count 4, not byte 5).
        let four = ctx.mk_numeral(shinri_core::Rational::from_int(4i128.into()), int_s);
        let expected_ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_lit, four])
            .unwrap();
        let expected_le = ctx
            .mk_app(Op::Builtin(BuiltinOp::Le), &[len_lit, four])
            .unwrap();
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
        let (mut found_ge, mut found_le) = (false, false);
        for _ in 0..8 {
            match s.check(&mut cx, Effort::Full) {
                TCheck::Split { atoms: a, .. } => {
                    assert_eq!(a.len(), 1, "length axioms are unit lemmas");
                    if a[0] == expected_ge {
                        found_ge = true;
                    }
                    if a[0] == expected_le {
                        found_le = true;
                    }
                }
                TCheck::Sat => break,
                TCheck::Conflict(_) => panic!("no conflict expected"),
                TCheck::Unknown => panic!("default fuel is large; unexpected Unknown"),
            }
        }
        assert!(
            found_ge && found_le,
            "must emit (>= …) and (<= …) companions of (= (str.len \"café\") 4) — char count, not byte count"
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
        let len_cc = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[cc]).unwrap();
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

    #[test]
    fn tautology_offered_for_bare_string_variable() {
        use super::empty_length_tautology;
        use shinri_core::{BuiltinOp, ConstVal, Context, Op, TermNode};
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let sym = ctx.declare_fun("x", &[], str_s);
        let x = ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap();
        let len_x = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[x]).unwrap();

        let (eq_empty, ge_one) =
            empty_length_tautology(&mut ctx, len_x).expect("bare variable qualifies");

        // eq_empty must be (= x "").
        let empty = ctx.mk_string_const("");
        let expected_eq = ctx.mk_eq(x, empty).unwrap();
        assert_eq!(eq_empty, expected_eq, "first disjunct is (= x \"\")");

        // ge_one must be (>= (str.len x) 1).
        let int_s = ctx.int_sort();
        let one = ctx.mk_numeral(shinri_core::Rational::from_int(1i128.into()), int_s);
        let expected_ge = ctx
            .mk_app(Op::Builtin(BuiltinOp::Ge), &[len_x, one])
            .unwrap();
        assert_eq!(ge_one, expected_ge, "second disjunct is (>= (str.len x) 1)");

        // Sanity: the empty constant really is the empty string.
        assert!(matches!(
            ctx.term_node(empty),
            TermNode::Const {
                val: ConstVal::String(_),
                ..
            }
        ));
    }

    #[test]
    fn tautology_declined_for_concat_and_literal_lengths() {
        use super::empty_length_tautology;
        use shinri_core::{BuiltinOp, Context, Op};
        let mut ctx = Context::new();
        let str_s = ctx.string_sort();
        let mk = |c: &mut Context, n: &str| {
            let s = c.declare_fun(n, &[], str_s);
            c.mk_app(Op::Uninterpreted(s), &[]).unwrap()
        };
        let x = mk(&mut ctx, "x");
        let y = mk(&mut ctx, "y");

        // Concat length: len(x ++ y) must NOT qualify — a concat carries hidden
        // mandatory constant length and multiplies as the engine rewrites; this
        // is exactly the per-str.len flood the length.rs:254 note warns about.
        let cc = ctx
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[x, y])
            .unwrap();
        let len_cc = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[cc]).unwrap();
        assert!(
            empty_length_tautology(&mut ctx, len_cc).is_none(),
            "concat length must not qualify"
        );

        // Literal length: len("ab") must NOT qualify — its length is already
        // pinned by the structural defining equation.
        let lit = ctx.mk_string_const("ab");
        let len_lit = ctx.mk_app(Op::Builtin(BuiltinOp::StrLen), &[lit]).unwrap();
        assert!(
            empty_length_tautology(&mut ctx, len_lit).is_none(),
            "literal length must not qualify"
        );
    }

    #[test]
    fn tautology_declined_for_non_len_term() {
        use super::empty_length_tautology;
        use shinri_core::{BuiltinOp, Context, Op};
        let mut ctx = Context::new();
        let int_s = ctx.int_sort();
        let sym = ctx.declare_fun("n", &[], int_s);
        let n = ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap();
        let zero = ctx.mk_numeral(shinri_core::Rational::from_int(0i128.into()), int_s);
        let ge = ctx.mk_app(Op::Builtin(BuiltinOp::Ge), &[n, zero]).unwrap();
        assert!(
            empty_length_tautology(&mut ctx, ge).is_none(),
            "a non-str.len term must not qualify"
        );
    }
}
