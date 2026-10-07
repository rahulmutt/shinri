//! Slice 62: exact length bounds of a bare leaf's membership intersection,
//! emitted as guarded lemmas `¬m₁ ∨ … ∨ ¬mₖ ∨ bound`. The slice-26 carve-out
//! bounds `len` per atom with the structural `min_len`/`max_len`; when every
//! arm has a `*` (Norn `ab` 135: `a*b ∩ a*b+ ∩ ab* ∩ [a-u]*` = `{ab}`) the
//! intersection's bounds never reach arith, which then picks a length no
//! word realizes. Each lemma is a string-theory tautology: a word in every
//! `mᵢ`'s language lies in `L(∩)`, whose lengths are within `len_bounds`.

use crate::regex::{self, Rex};
use crate::{memb, model, side_clean, wordeq, StrSolver};
use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Lit, Op, TermId, TermNode};
use shinri_theory::types::ENodeId;
use shinri_theory::{TCheck, TheoryCtx};

/// One bound lemma per call, or `None` (nothing new to say). Runs at the end
/// of `memb_check`, under the same fuel peek.
pub(crate) fn bound_split(
    s: &mut StrSolver,
    cx: &mut TheoryCtx,
    known: &[TermId],
    input_cond_roots: &FxHashSet<ENodeId>,
) -> Option<TCheck> {
    if s.fuel.remaining == 0 {
        return None;
    }
    // Group by bare-leaf subject, in first-seen order (determinism).
    let mut order: Vec<TermId> = Vec::new();
    let mut groups: FxHashMap<TermId, Vec<(Lit, Rex, bool)>> = FxHashMap::default();
    let mut poisoned: FxHashSet<TermId> = FxHashSet::default();
    for &(atom, lit, pos) in &s.memb_true {
        let (t, re_t) = memb::memb_sides(cx.terms, atom);
        let is_leaf = matches!(
            cx.terms.term_node(t),
            TermNode::App { op: Op::Uninterpreted(_), args, .. }
                if cx.terms.children(*args).is_empty()
        );
        if !is_leaf {
            continue;
        }
        let Some(mut rex) = regex::extract_const_regex(cx.terms, re_t) else {
            poisoned.insert(t);
            continue;
        };
        if !pos {
            rex = regex::comp(rex);
        }
        if !groups.contains_key(&t) {
            order.push(t);
        }
        groups.entry(t).or_default().push((lit, rex, pos));
    }
    for t in order {
        if poisoned.contains(&t) {
            continue;
        }
        if model::is_repair_pinned(cx.terms, cx.eq, known, t) {
            continue;
        }
        if !side_clean(cx.eq, cx.terms, t, input_cond_roots) {
            continue;
        }
        let members = &groups[&t];
        let mut guards: Vec<Lit> = members.iter().map(|(l, _, _)| l.negate()).collect();
        guards.sort_by_key(|l| l.code());
        guards.dedup();
        let bounds = match s.len_bounds_cache.get(&guards) {
            Some(b) => *b,
            None => {
                let goal = regex::inter(members.iter().map(|(_, r, _)| r.clone()).collect());
                let b = regex::len_bounds(&goal);
                s.len_bounds_cache.insert(guards.clone(), b);
                b
            }
        };
        let Some((lo, hi)) = bounds else {
            continue;
        };
        // What the per-atom (structural) bounds already tell arith.
        // Positive atoms only (spec 4.4 step 4): a negative member reaches
        // arith through no structural bound.
        let lo0 = members
            .iter()
            .filter(|m| m.2)
            .map(|m| regex::min_len(&m.1))
            .max()
            .unwrap_or(0);
        let hi0 = members
            .iter()
            .filter(|m| m.2)
            .filter_map(|m| regex::max_len(&m.1))
            .min();
        let lr = wordeq::len_of(cx.terms, t);
        let mut cands: Vec<TermId> = Vec::new();
        if lo > lo0 {
            cands.push(cmp(cx, BuiltinOp::Ge, lr, lo));
        }
        if let Some(h) = hi {
            if hi0.is_none_or(|h0| h < h0) {
                cands.push(cmp(cx, BuiltinOp::Le, lr, h));
            }
        }
        for b in cands {
            let key = (b, guards.clone());
            if s.emitted_group_len_axioms.contains(&key) {
                continue;
            }
            s.emitted_group_len_axioms.insert(key);
            return Some(memb::emit_split_guards(s, cx.terms, vec![b], guards));
        }
    }
    None
}

/// `(op len k)` over an Int numeral `k`.
fn cmp(cx: &mut TheoryCtx, op: BuiltinOp, len: TermId, k: u32) -> TermId {
    let n = cx.terms.mk_numeral(
        shinri_core::Rational::from_int(i128::from(k).into()),
        cx.terms.int_sort(),
    );
    cx.terms
        .mk_app(Op::Builtin(op), &[len, n])
        .expect("(cmp len k) well-sorted")
}

#[cfg(test)]
mod tests {
    use crate::regex::{self, Rex};
    use crate::StrSolver;
    use shinri_core::{BuiltinOp, Context, Lit, Op, TermId, Var};
    use shinri_sat::Effort;
    use shinri_theory::{AtomRegistry, EqualityEngine, TCheck, TheoryCtx, TheorySolver};

    fn var(ctx: &mut Context, n: &str) -> TermId {
        let str_s = ctx.string_sort();
        let s = ctx.declare_fun(n, &[], str_s);
        ctx.mk_app(Op::Uninterpreted(s), &[]).unwrap()
    }

    fn memb_atom(ctx: &mut Context, t: TermId, r: &Rex) -> TermId {
        let re_t = regex::rex_to_term_test(ctx, r);
        ctx.mk_app(Op::Builtin(BuiltinOp::StrInRe), &[t, re_t])
            .unwrap()
    }

    /// Norn 135's four regexes on one leaf.
    fn norn135(ctx: &mut Context, x: TermId) -> Vec<TermId> {
        let a_star = regex::star_lit_test("a");
        let rs = [
            regex::concat(vec![a_star.clone(), regex::lit_test("b")]),
            regex::concat(vec![
                a_star,
                regex::lit_test("b"),
                regex::star_lit_test("b"),
            ]),
            regex::concat(vec![regex::lit_test("a"), regex::star_lit_test("b")]),
            regex::star_range_test('a', 'u'),
        ];
        rs.iter().map(|r| memb_atom(ctx, x, r)).collect()
    }

    /// Drive `check` to a fixpoint; return every Split as (atoms, guards).
    fn rounds(s: &mut StrSolver, cx: &mut TheoryCtx) -> Vec<(Vec<TermId>, Vec<Lit>)> {
        let mut out = Vec::new();
        for _ in 0..64 {
            match s.check(cx, Effort::Full) {
                TCheck::Split { atoms, guards, .. } => out.push((atoms, guards)),
                TCheck::Sat => return out,
                _ => panic!("unexpected non-Split/Sat result"),
            }
        }
        panic!("no fixpoint");
    }

    fn is_op(terms: &Context, t: TermId, want: BuiltinOp) -> bool {
        matches!(terms.term_node(t), shinri_core::TermNode::App { op: Op::Builtin(o), .. } if *o == want)
    }

    fn numeral_arg(terms: &Context, t: TermId) -> Option<i128> {
        match terms.term_node(t) {
            shinri_core::TermNode::App { args, .. } => {
                let k = terms.children(*args)[1];
                terms.numeral_value(k).and_then(|r| r.numer().to_i128())
            }
            _ => None,
        }
    }

    fn setup(ctx: &mut Context, atoms: &[TermId], lits: &[Lit]) -> StrSolver {
        let mut s = StrSolver::default();
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx {
            terms: ctx,
            eq: &mut eq_e,
            atoms: &areg,
        };
        for (i, &a) in atoms.iter().enumerate() {
            s.new_var(&mut cx, lits[i].var(), a);
            s.test_force_memb_true_lit(a, lits[i], lits[i].is_positive());
        }
        s
    }

    fn lits(n: u32) -> Vec<Lit> {
        (0..n).map(|i| Lit::new(Var::new(i), true)).collect()
    }

    #[test]
    fn norn135_group_emits_both_bounds_with_all_guards() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let atoms = norn135(&mut ctx, x);
        let ls = lits(4);
        let mut s = setup(&mut ctx, &atoms, &ls);
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &areg,
        };
        let splits = rounds(&mut s, &mut cx);
        let group: Vec<_> = splits.iter().filter(|(_, g)| g.len() == 4).collect();
        assert_eq!(group.len(), 2, "one ≥ and one ≤ group lemma: {splits:?}");
        let mut want: Vec<Lit> = ls.iter().map(|l| l.negate()).collect();
        want.sort_by_key(|l| l.code());
        for (a, g) in &group {
            assert_eq!(g, &want);
            assert_eq!(a.len(), 1);
            assert_eq!(numeral_arg(cx.terms, a[0]), Some(2));
        }
        assert!(group
            .iter()
            .any(|(a, _)| is_op(cx.terms, a[0], BuiltinOp::Ge)));
        assert!(group
            .iter()
            .any(|(a, _)| is_op(cx.terms, a[0], BuiltinOp::Le)));
    }

    #[test]
    fn no_group_lemma_when_structural_bounds_are_tight() {
        // x ∈ [a-c]·"b": per-atom bounds are already 2..2.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let r = regex::concat(vec![
            Rex::Range('a' as u32, 'c' as u32),
            regex::lit_test("b"),
        ]);
        let m = memb_atom(&mut ctx, x, &r);
        let mut s = setup(&mut ctx, &[m], &lits(1));
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &areg,
        };
        rounds(&mut s, &mut cx);
        assert!(s.emitted_group_len_axioms.is_empty());
    }

    #[test]
    fn pinned_leaf_emits_no_group_lemma() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let atoms = norn135(&mut ctx, x);
        let ab = ctx.mk_string_const("ab");
        let mut s = setup(&mut ctx, &atoms, &lits(4));
        s.test_force_str_term(ab);
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let (xn, cn) = (eq_e.intern(x), eq_e.intern(ab));
        let _ = eq_e.merge(xn, cn, shinri_theory::types::EqJust::Definitional);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &areg,
        };
        let _ = super::bound_split(&mut s, &mut cx, &[x, ab], &Default::default());
        assert!(s.emitted_group_len_axioms.is_empty());
    }

    #[test]
    fn group_dedup_key_includes_guards() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let mut atoms = norn135(&mut ctx, x);
        let extra = memb_atom(&mut ctx, x, &regex::star_range_test('a', 'z'));
        let mut s = setup(&mut ctx, &atoms, &lits(4));
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &areg,
        };
        rounds(&mut s, &mut cx);
        let before = s.emitted_group_len_axioms.len();
        assert_eq!(before, 2);
        // A fifth membership (bounds unchanged) is a new guard set: the same
        // two bound atoms must be emitted again under 5 guards.
        let l5 = Lit::new(Var::new(4), true);
        s.new_var(&mut cx, l5.var(), extra);
        s.test_force_memb_true_lit(extra, l5, true);
        atoms.push(extra);
        let splits = rounds(&mut s, &mut cx);
        assert_eq!(splits.iter().filter(|(_, g)| g.len() == 5).count(), 2);
        assert_eq!(s.emitted_group_len_axioms.len(), before + 2);
    }

    #[test]
    fn negative_member_joins_group() {
        // x ∈ (a|b)(a|b)?  ∧  x ∉ (a|b): only length-2 words remain.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let ab = regex::union(vec![regex::lit_test("a"), regex::lit_test("b")]);
        let pos_r = regex::concat(vec![ab.clone(), regex::union(vec![ab.clone(), Rex::Eps])]);
        let mp = memb_atom(&mut ctx, x, &pos_r);
        let mn = memb_atom(&mut ctx, x, &ab);
        let lp = Lit::new(Var::new(0), true);
        let ln = Lit::new(Var::new(1), false); // asserted false: x ∉ (a|b)
        let mut s = setup(&mut ctx, &[mp, mn], &[lp, ln]);
        let (mut eq_e, areg) = (EqualityEngine::default(), AtomRegistry::default());
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &areg,
        };
        let splits = rounds(&mut s, &mut cx);
        let ge: Vec<_> = splits
            .iter()
            .filter(|(a, g)| g.len() == 2 && is_op(cx.terms, a[0], BuiltinOp::Ge))
            .collect();
        assert_eq!(ge.len(), 1, "{splits:?}");
        assert_eq!(numeral_arg(cx.terms, ge[0].0[0]), Some(2));
        let mut want = vec![lp.negate(), ln.negate()];
        want.sort_by_key(|l| l.code());
        assert_eq!(ge[0].1, want);
    }
}
