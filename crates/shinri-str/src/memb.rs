//! Slice 21: the membership pass — lazy guarded derivative unfolding of
//! `str.in_re` atoms into word equations, run at the end of every Full check.

use crate::regex::{self, Rex};
use crate::{collect, normalize, side_clean, wordeq, StrSolver};
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};
use shinri_theory::types::{ENodeId, EqLeaf};
use shinri_theory::{TCheck, TheoryCtx};

const RULE_E: u8 = 0;
const RULE_S1: u8 = 1;
const RULE_S2: u8 = 2;
const RULE_S3: u8 = 3;
const RULE_S4: u8 = 4;

/// The two children of a `str.in_re` atom: (string side, regex side).
pub(crate) fn memb_sides(terms: &Context, atom: TermId) -> (TermId, TermId) {
    match terms.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::StrInRe),
            args,
            ..
        } => {
            let ch = terms.children(*args);
            (ch[0], ch[1])
        }
        _ => panic!("memb_sides: expected str.in_re atom"),
    }
}

/// `str.++` of `atoms` (1 atom → itself; 0 → the empty literal).
fn mk_concat(terms: &mut Context, atoms: &[TermId]) -> TermId {
    match atoms.len() {
        0 => terms.mk_string_const(""),
        1 => atoms[0],
        _ => terms
            .mk_app(Op::Builtin(BuiltinOp::StrConcat), atoms)
            .expect("str.++ well-sorted"),
    }
}

/// Register a freshly-minted split atom exactly like the F-split path does:
/// collect its len/str terms and mark any string equality as minted so the
/// length seam skips it.
fn register_atom(s: &mut StrSolver, terms: &mut Context, atom: TermId) {
    let mut seen = FxHashSet::default();
    collect::collect(terms, atom, &mut s.len_terms, &mut s.str_terms, &mut seen);
    if let TermNode::App {
        op: Op::Builtin(BuiltinOp::Eq | BuiltinOp::Distinct),
        args,
        ..
    } = terms.term_node(atom)
    {
        let kids = terms.children(*args).to_vec();
        if !kids.is_empty() && terms.sort_of(kids[0]) == terms.string_sort() {
            s.minted_eqs.insert(atom);
        }
    }
}

/// Spend fuel and emit one guarded/unguarded split, registering every atom.
fn emit_split(
    s: &mut StrSolver,
    terms: &mut Context,
    atoms: Vec<TermId>,
    guard: Option<shinri_core::Lit>,
) -> TCheck {
    for &a in &atoms {
        register_atom(s, terms, a);
    }
    if !s.fuel.spend() {
        return TCheck::Unknown;
    }
    TCheck::Split { atoms, guard }
}

/// The slice-21 membership pass. `Some(tcheck)` = a verdict or an emission
/// this round; `None` = nothing to do (all memberships discharged, deduped,
/// or skipped as unclean — the caller falls through to Sat, backstopped by
/// the post-solve self-check).
pub(crate) fn memb_check(
    s: &mut StrSolver,
    cx: &mut TheoryCtx,
    known: &[TermId],
    input_cond_roots: &FxHashSet<ENodeId>,
) -> Option<TCheck> {
    let membs: Vec<(TermId, shinri_core::Lit, bool)> = s.memb_true.clone();
    for (atom, lit, pos) in membs {
        let (t, re_t) = memb_sides(cx.terms, atom);
        // Constant by the solver fence (input) or by construction (minted);
        // a failure here is a seam break — fence to Unknown, never guess.
        let Some(mut rex) = regex::extract_const_regex(cx.terms, re_t) else {
            return Some(TCheck::Unknown);
        };
        if !pos {
            rex = regex::comp(rex); // t ∉ R ≡ t ∈ comp(R)
        }

        // ── Rule G: consume the ground NF prefix ─────────────────────────
        // Fully-cited NF (the diseq Case-2 pattern): expansion antecedents
        // are collected so a ground Conflict can cite them and stay UNGATED.
        let mut expand_ante: Vec<EqLeaf> = Vec::new();
        let Some(nf) =
            normalize::deep_normal_form_cited(cx.terms, cx.eq, known, t, &mut expand_ante)
        else {
            return Some(TCheck::Unknown); // non-convergent merge — sound bail
        };
        let mut cur = rex;
        let mut i = 0usize;
        let mut fenced = false;
        while i < nf.len() {
            let Some(w) = cx.terms.string_const_value(nf[i]).map(str::to_owned) else {
                break;
            };
            for c in w.chars() {
                cur = regex::deriv(c as u32, &cur);
                if regex::node_count(&cur) > regex::FUEL_NODE_CAP {
                    fenced = true;
                    break;
                }
            }
            if fenced {
                break;
            }
            i += 1;
        }
        if fenced {
            return Some(TCheck::Unknown);
        }
        if i == nf.len() {
            // Fully ground: nullability decides the atom.
            if regex::nullable(&cur) {
                continue; // discharged this round
            }
            let mut just = vec![EqLeaf::Asserted(lit)];
            just.extend(expand_ante.iter().copied());
            return Some(TCheck::Conflict(just));
        }

        // Residual: nf[i..] with a variable head. Guarded lemmas read the
        // NF, so they fire only when it is branch-independent w.r.t. EXTERNAL
        // disjunctions — `side_clean(input_cond_roots)`, the SAME gate the
        // word-equation loop uses for F-SPLIT emission (spec: "the same
        // gating F-splits use today"). The engine's OWN minted disjuncts are
        // deliberately NOT in this set, so unfolding keeps stepping over its
        // previously-emitted splits (else a dl0 membership stalls at
        // Unknown). Sound for the same reason F-splits are: these lemmas add
        // only GUARDED branches (guard ¬lit; fresh lone witnesses), never a
        // global fact — verdicts stay with the fully-cited Rule-G/E
        // conflicts, and any admitted SAT is re-validated by the post-solve
        // model self-check. Skipped ⟹ revisited when clean; never a verdict.
        if !side_clean(cx.eq, cx.terms, t, input_cond_roots) {
            continue;
        }
        let residual_atoms: Vec<TermId> = nf[i..].to_vec();
        let residual = mk_concat(cx.terms, &residual_atoms);
        let x = residual_atoms[0];
        let cur_t = regex::rex_to_term(cx.terms, &cur);
        let guard = Some(lit.negate());

        // ── Rule S: head-forced `C · R''` — peel one char off `x` ────────
        if let Some(((lo, hi), tail_rex)) = regex::head_forced(&cur) {
            // S1: lit → x = "" ∨ x = h·z (fresh h, z; the F-split argument).
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S1)) {
                s.emitted_memb.insert((x, cur_t, RULE_S1));
                let h = wordeq::fresh_str(cx.terms, &mut s.fresh_ctr);
                let z = wordeq::fresh_str(cx.terms, &mut s.fresh_ctr);
                s.memb_wits.insert((x, cur_t), (h, z));
                let hz = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[h, z])
                    .expect("str.++ well-sorted");
                let e = cx.terms.mk_string_const("");
                let x_eps = cx.terms.mk_eq(x, e).expect("eq well-sorted");
                let x_hz = cx.terms.mk_eq(x, hz).expect("eq well-sorted");
                return Some(emit_split(s, cx.terms, vec![x_eps, x_hz], guard));
            }
            let &(h, z) = s
                .memb_wits
                .get(&(x, cur_t))
                .expect("S1 emitted ⟹ witnesses recorded");
            let hz = cx
                .terms
                .mk_app(Op::Builtin(BuiltinOp::StrConcat), &[h, z])
                .expect("str.++ well-sorted");
            let dist = cx
                .terms
                .mk_app(Op::Builtin(BuiltinOp::Distinct), &[x, hz])
                .expect("distinct well-sorted");
            // S2 (unguarded fresh-witness canonicalization): x=h·z → len(h)=1.
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S2)) {
                s.emitted_memb.insert((x, cur_t, RULE_S2));
                let lh = wordeq::len_of(cx.terms, h);
                let one = cx.terms.mk_numeral(
                    shinri_core::Rational::from_int(1i128.into()),
                    cx.terms.int_sort(),
                );
                let len1 = cx.terms.mk_eq(lh, one).expect("eq well-sorted");
                return Some(emit_split(s, cx.terms, vec![dist, len1], None));
            }
            // S3: lit ∧ x=h·z → h ∈ C.
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S3)) {
                s.emitted_memb.insert((x, cur_t, RULE_S3));
                let c_t = regex::rex_to_term(cx.terms, &Rex::Range(lo, hi));
                let m_h = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[h, c_t])
                    .expect("str.in_re well-sorted");
                return Some(emit_split(s, cx.terms, vec![dist, m_h], guard));
            }
            // S4: lit ∧ x=h·z → z·γ ∈ R''.
            if !s.emitted_memb.contains(&(x, cur_t, RULE_S4)) {
                s.emitted_memb.insert((x, cur_t, RULE_S4));
                let mut tail_atoms = vec![z];
                tail_atoms.extend_from_slice(&residual_atoms[1..]);
                let tail_t = mk_concat(cx.terms, &tail_atoms);
                let tail_re = regex::rex_to_term(cx.terms, &tail_rex);
                let m_tail = cx
                    .terms
                    .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[tail_t, tail_re])
                    .expect("str.in_re well-sorted");
                return Some(emit_split(s, cx.terms, vec![dist, m_tail], guard));
            }
            continue; // fully unfolded at this level — wait for SAT/merges
        }

        // ── Rule E: class expansion (fundamental derivative equivalence)
        //    L(cur) = [ε if ν] ∪ ⋃_C C·L(∂_C cur) — single-atom disjuncts. ──
        if !s.emitted_memb.contains(&(residual, cur_t, RULE_E)) {
            s.emitted_memb.insert((residual, cur_t, RULE_E));
            let Some(classes) = regex::next_classes(&cur) else {
                return Some(TCheck::Unknown); // CLASS_SPLIT_CAP — fence
            };
            let mut disj: Vec<TermId> = Vec::new();
            if regex::nullable(&cur) {
                let e = cx.terms.mk_string_const("");
                disj.push(cx.terms.mk_eq(residual, e).expect("eq well-sorted"));
            }
            for (lo, hi) in classes {
                // ∂ at the class representative — exact across the class
                // (u32 space: surrogate classes included, never dropped).
                let d = regex::deriv(lo, &cur);
                if regex::node_count(&d) > regex::FUEL_NODE_CAP {
                    return Some(TCheck::Unknown);
                }
                if matches!(d, Rex::Empty) {
                    continue; // C·∅ = ∅ — a dead disjunct, dropping is exact
                }
                let shape = regex::concat(vec![Rex::Range(lo, hi), d]);
                let shape_t = regex::rex_to_term(cx.terms, &shape);
                disj.push(
                    cx.terms
                        .mk_app(Op::Builtin(BuiltinOp::StrInRe), &[residual, shape_t])
                        .expect("str.in_re well-sorted"),
                );
            }
            if disj.is_empty() {
                // No ε, no live class: L(cur) = ∅ — the membership is
                // unsatisfiable. Fully-cited conflict (trigger + NF merges).
                let mut just = vec![EqLeaf::Asserted(lit)];
                just.extend(expand_ante.iter().copied());
                return Some(TCheck::Conflict(just));
            }
            return Some(emit_split(s, cx.terms, disj, guard));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use crate::regex::{self, Rex};
    use crate::StrSolver;
    use shinri_core::{BuiltinOp, Context, Op, TermId};
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

    // Sanctioned deviation from the brief's verbatim snippet: the `ctx`
    // param was unused (warning) — renamed `_ctx`.
    fn harness(_ctx: &mut Context) -> (StrSolver, EqualityEngine, AtomRegistry) {
        (
            StrSolver::default(),
            EqualityEngine::default(),
            AtomRegistry::default(),
        )
    }

    /// Drive check() to a fixpoint, collecting every emitted Split; panics on
    /// Unknown. Returns the terminal TCheck (Sat or Conflict).
    fn run_rounds(
        s: &mut StrSolver,
        cx: &mut TheoryCtx,
        max: usize,
    ) -> (Vec<(Vec<TermId>, bool)>, TCheck) {
        let mut splits = Vec::new();
        for _ in 0..max {
            match s.check(cx, Effort::Full) {
                TCheck::Split { atoms, guard } => splits.push((atoms, guard.is_some())),
                other => return (splits, other),
            }
        }
        panic!("no fixpoint within {max} rounds");
    }

    #[test]
    fn rule_g_ground_conflict_and_discharge() {
        // x = "ab" merged, x ∈ a*  ⇒ Conflict (ground eval false).
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let ab = ctx.mk_string_const("ab");
        let eq = ctx.mk_eq(x, ab).unwrap();
        let m = memb_atom(&mut ctx, x, &regex::star_lit_test("a"));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), eq);
        s.new_var(&mut cx, shinri_core::Var::new(1), m);
        s.test_force_eq_true(eq);
        // Unit tests drive the eq engine EXPLICITLY (the Combiner does this
        // in production) — same incantation as the wordeq.rs tests.
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(ab));
        let _ = cx
            .eq
            .merge(xn, cn, shinri_theory::types::EqJust::Definitional);
        s.test_force_memb_true(m, true);
        let (_, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(
            matches!(terminal, TCheck::Conflict(_)),
            "ground violation must conflict"
        );

        // Same shape, x ∈ (str.to_re "ab") ⇒ discharged, Sat fixpoint.
        let mut ctx2 = Context::new();
        let x2 = var(&mut ctx2, "x");
        let ab2 = ctx2.mk_string_const("ab");
        let eq2 = ctx2.mk_eq(x2, ab2).unwrap();
        let m2 = memb_atom(&mut ctx2, x2, &regex::lit_test("ab"));
        let (mut s2, mut eq_e2, atoms2) = harness(&mut ctx2);
        let mut cx2 = TheoryCtx {
            terms: &mut ctx2,
            eq: &mut eq_e2,
            atoms: &atoms2,
        };
        s2.new_var(&mut cx2, shinri_core::Var::new(0), eq2);
        s2.new_var(&mut cx2, shinri_core::Var::new(1), m2);
        s2.test_force_eq_true(eq2);
        let (xn2, cn2) = (cx2.eq.intern(x2), cx2.eq.intern(ab2));
        let _ = cx2
            .eq
            .merge(xn2, cn2, shinri_theory::types::EqJust::Definitional);
        s2.test_force_memb_true(m2, true);
        let (_, terminal2) = run_rounds(&mut s2, &mut cx2, 16);
        assert!(
            matches!(terminal2, TCheck::Sat),
            "satisfied ground membership discharges"
        );
    }

    #[test]
    fn negative_polarity_uses_complement() {
        // x = "ab" merged, ¬(x ∈ a*) ⇒ discharged (comp semantics); and
        // ¬(x ∈ (str.to_re "ab")) ⇒ Conflict.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let ab = ctx.mk_string_const("ab");
        let eq = ctx.mk_eq(x, ab).unwrap();
        let m_astar = memb_atom(&mut ctx, x, &regex::star_lit_test("a"));
        let m_ab = memb_atom(&mut ctx, x, &regex::lit_test("ab"));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), eq);
        s.test_force_eq_true(eq);
        let (xn, cn) = (cx.eq.intern(x), cx.eq.intern(ab));
        let _ = cx
            .eq
            .merge(xn, cn, shinri_theory::types::EqJust::Definitional);
        s.test_force_memb_true(m_astar, false); // "ab" ∉ a* — true, discharges
        let (_, t1) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(t1, TCheck::Sat));
        s.test_force_memb_true(m_ab, false); // "ab" ∉ {ab} — false, conflicts
        let (_, t2) = run_rounds(&mut s, &mut cx, 16);
        assert!(matches!(t2, TCheck::Conflict(_)));
    }

    #[test]
    fn rule_e_expansion_shape() {
        // x ∈ [a-c]* (not head-forced, nullable): ONE guarded clause whose
        // atoms are the ε equality + one membership per class with a
        // non-empty derivative (here exactly one: [a-c]·[a-c]*).
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let r = regex::star_range_test('a', 'c');
        let m = memb_atom(&mut ctx, x, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        // Rounds may interleave length axioms; find the ONE expansion split
        // (the guarded split containing a str.in_re disjunct). Terminal Sat
        // proves the expansion dedups (no re-emission).
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 16);
        assert!(
            matches!(terminal, TCheck::Sat),
            "expansion must dedup to a fixpoint"
        );
        let is_memb = |t: &TermId| {
            matches!(
                cx.terms.term_node(*t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrInRe),
                    ..
                }
            )
        };
        let expansions: Vec<_> = splits
            .iter()
            .filter(|(atoms, _)| atoms.iter().any(is_memb))
            .collect();
        assert_eq!(
            expansions.len(),
            1,
            "exactly one Rule-E expansion for [a-c]*"
        );
        let (disj, guarded) = expansions[0];
        assert!(*guarded, "expansion must be guarded by ¬lit");
        assert_eq!(disj.len(), 2, "ε disjunct + one live class disjunct");
        // One disjunct is x = "" and the other a str.in_re atom on x.
        let memb_disj = disj.iter().find(|t| is_memb(t)).unwrap();
        let (mt, _) = super::memb_sides(cx.terms, *memb_disj);
        assert_eq!(mt, x);
        let eq_disj = disj.iter().find(|t| !is_memb(t)).unwrap();
        let (l, rr) = crate::wordeq::sides(cx.terms, *eq_disj);
        assert!(
            cx.terms.string_const_value(l) == Some("")
                || cx.terms.string_const_value(rr) == Some("")
        );
    }

    #[test]
    fn rule_s_head_split_clause_sequence() {
        // x ∈ [a-c]·(str.to_re "") — head-forced: S1..S4 in order, then fixpoint.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let r = Rex::Range('a' as u32, 'c' as u32);
        let m = memb_atom(&mut ctx, x, &r);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (splits, terminal) = run_rounds(&mut s, &mut cx, 24);
        assert!(matches!(terminal, TCheck::Sat));
        // Rounds may interleave length axioms (len(h) enters the length seam).
        // Identify the S-clauses by SHAPE, order-independent:
        let is_memb = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::StrInRe),
                    ..
                }
            )
        };
        let is_dist = |terms: &Context, t: TermId| {
            matches!(
                terms.term_node(t),
                shinri_core::TermNode::App {
                    op: Op::Builtin(BuiltinOp::Distinct),
                    ..
                }
            )
        };
        // S1: guarded, two string EQUALITIES on x (one against "").
        let s1 = splits.iter().filter(|(a, g)| {
            *g && a.len() == 2
                && a.iter()
                    .all(|&t| !is_memb(cx.terms, t) && !is_dist(cx.terms, t))
        });
        assert_eq!(s1.count(), 1, "exactly one S1 head split");
        // S2: the ONLY unguarded clause — [distinct(x,h·z), len(h)=1].
        let s2: Vec<_> = splits
            .iter()
            .filter(|(a, g)| !*g && a.iter().any(|&t| is_dist(cx.terms, t)))
            .collect();
        assert_eq!(
            s2.len(),
            1,
            "exactly one unguarded witness canonicalization (S2)"
        );
        // S3 + S4: guarded [distinct, str.in_re] clauses.
        let s34: Vec<_> = splits
            .iter()
            .filter(|(a, g)| {
                *g && a.iter().any(|&t| is_dist(cx.terms, t))
                    && a.iter().any(|&t| is_memb(cx.terms, t))
            })
            .collect();
        assert_eq!(
            s34.len(),
            2,
            "head-class (S3) + tail-membership (S4) clauses"
        );
        // Their membership atoms sit on fresh terms (h resp. z·γ), not on x,
        // and their regex sides re-extract as constant regexes.
        for (atoms, _) in &s34 {
            let mt = atoms
                .iter()
                .copied()
                .find(|&t| is_memb(cx.terms, t))
                .unwrap();
            let (side, re_side) = super::memb_sides(cx.terms, mt);
            assert_ne!(side, x, "S3/S4 memberships are on fresh witnesses");
            assert!(crate::regex::extract_const_regex(cx.terms, re_side).is_some());
        }
    }

    #[test]
    fn empty_language_residual_conflicts() {
        // x ∈ re.none survives the pre-pass only when minted mid-search, but
        // the rule must still conflict on it directly.
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let m = memb_atom(&mut ctx, x, &Rex::Empty);
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        let (_, terminal) = run_rounds(&mut s, &mut cx, 8);
        assert!(matches!(terminal, TCheck::Conflict(_)));
    }

    #[test]
    fn fuel_exhaustion_yields_unknown() {
        let mut ctx = Context::new();
        let x = var(&mut ctx, "x");
        let m = memb_atom(&mut ctx, x, &regex::star_range_test('a', 'c'));
        let (mut s, mut eq_e, atoms) = harness(&mut ctx);
        let mut cx = TheoryCtx {
            terms: &mut ctx,
            eq: &mut eq_e,
            atoms: &atoms,
        };
        s.new_var(&mut cx, shinri_core::Var::new(0), m);
        s.test_force_memb_true(m, true);
        s.test_set_fuel(0);
        assert!(matches!(s.check(&mut cx, Effort::Full), TCheck::Unknown));
    }
}
