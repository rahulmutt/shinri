use shinri_core::{Context, Lit, Op, TermId, Var};
use shinri_euf::Euf;
use shinri_theory::types::EqLeaf;
use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
    let sym = ctx.declare_fun(name, &[], s);
    ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
}

/// x = y  ∧  f(x) ≠ f(y)  is EUF-unsatisfiable.
#[test]
fn congruence_conflict_x_eq_y_implies_fx_eq_fy() {
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let x = uconst(&mut ctx, "x", u);
    let y = uconst(&mut ctx, "y", u);
    let f = ctx.declare_fun("f", &[u], u);
    let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
    let fy = ctx.mk_app(Op::Uninterpreted(f), &[y]).unwrap();
    let eq_xy = ctx.mk_eq(x, y).unwrap();
    let eq_ff = ctx.mk_eq(fx, fy).unwrap();

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let v_xy = Var::new(0);
    let v_ff = Var::new(1);
    atoms.register(v_xy, eq_xy, shinri_theory::types::Owner::Euf);
    atoms.register(v_ff, eq_ff, shinri_theory::types::Owner::Euf);

    let mut euf = Euf::default();
    {
        let mut cx = TheoryCtx {
            terms: &ctx,
            eq: &mut eq,
            atoms: &atoms,
        };
        euf.new_var(&mut cx, v_xy, eq_xy);
        euf.new_var(&mut cx, v_ff, eq_ff);
        // assert f(x) ≠ f(y)
        assert!(euf.assert(&mut cx, Lit::new(v_ff, false)).is_none());
        // assert x = y  -> congruence forces f(x)=f(y) -> conflict
        let conflict = euf.assert(&mut cx, Lit::new(v_xy, true));
        assert!(conflict.is_some(), "x=y with f(x)!=f(y) must conflict");
    }
}

/// Regression for the CRITICAL conflict-soundness bug: when the violated
/// disequality was asserted between class members OTHER than the merged app
/// nodes, the conflict clause must BRIDGE the merged nodes to the diseq
/// endpoints. Scenario: f(s)=w, w≠f(t), s=t. Congruence merges f(s),f(t),
/// violating the diseq stored on (f(s), f(t)) (= (find(w), find(f(t)))). The
/// sound conflict MUST include the `f(s)=w` equality literal that the old code
/// dropped; otherwise {s=t, w≠f(t)} is satisfiable and not a valid conflict.
#[test]
fn conflict_bridges_to_diseq_endpoints_sufficiency() {
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let s = uconst(&mut ctx, "s", u);
    let t = uconst(&mut ctx, "t", u);
    let w = uconst(&mut ctx, "w", u);
    let f = ctx.declare_fun("f", &[u], u);
    let fs = ctx.mk_app(Op::Uninterpreted(f), &[s]).unwrap();
    let ft = ctx.mk_app(Op::Uninterpreted(f), &[t]).unwrap();
    let eq_fsw = ctx.mk_eq(fs, w).unwrap(); // f(s) = w
    let eq_wft = ctx.mk_eq(w, ft).unwrap(); // w = f(t)  (asserted negatively)
    let eq_st = ctx.mk_eq(s, t).unwrap(); // s = t

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let v_fsw = Var::new(0);
    let v_wft = Var::new(1);
    let v_st = Var::new(2);
    atoms.register(v_fsw, eq_fsw, shinri_theory::types::Owner::Euf);
    atoms.register(v_wft, eq_wft, shinri_theory::types::Owner::Euf);
    atoms.register(v_st, eq_st, shinri_theory::types::Owner::Euf);

    let lit_fsw = Lit::new(v_fsw, true); // the literal that MUST appear
    let lit_wft = Lit::new(v_wft, false); // w ≠ f(t)
    let lit_st = Lit::new(v_st, true); // s = t

    let mut euf = Euf::default();
    let mut cx = TheoryCtx {
        terms: &ctx,
        eq: &mut eq,
        atoms: &atoms,
    };
    euf.new_var(&mut cx, v_fsw, eq_fsw);
    euf.new_var(&mut cx, v_wft, eq_wft);
    euf.new_var(&mut cx, v_st, eq_st);

    assert!(euf.assert(&mut cx, lit_fsw).is_none(), "f(s)=w ok");
    assert!(euf.assert(&mut cx, lit_wft).is_none(), "w!=f(t) ok");
    // s=t -> congruence f(s)=f(t) -> conflict with w!=f(t).
    let conflict = euf
        .assert(&mut cx, lit_st)
        .expect("s=t must conflict via congruence + diseq");

    // SUFFICIENCY: the leaf set must contain the bridging equality f(s)=w (the
    // literal the buggy code omitted), plus s=t and the diseq w!=f(t). Without
    // f(s)=w the conjunction {s=t, w!=f(t)} is satisfiable — not a conflict.
    assert!(
        conflict.contains(&EqLeaf::Asserted(lit_fsw)),
        "conflict MUST include the bridging equality f(s)=w; got {conflict:?}"
    );
    assert!(
        conflict.contains(&EqLeaf::Asserted(lit_st)),
        "conflict must include s=t; got {conflict:?}"
    );
    assert!(
        conflict.contains(&EqLeaf::Asserted(lit_wft)),
        "conflict must include w!=f(t); got {conflict:?}"
    );
}

/// p(a) ∧ ¬p(b) ∧ a=b  is unsat (predicate congruence).
#[test]
fn predicate_congruence_conflict() {
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let boolsort = ctx.bool_sort();
    let a = uconst(&mut ctx, "a", u);
    let b = uconst(&mut ctx, "b", u);
    let p = ctx.declare_fun("p", &[u], boolsort);
    let pa = ctx.mk_app(Op::Uninterpreted(p), &[a]).unwrap();
    let pb = ctx.mk_app(Op::Uninterpreted(p), &[b]).unwrap();
    let eq_ab = ctx.mk_eq(a, b).unwrap();

    let t_true = ctx.mk_const_bool(true);
    let t_false = ctx.mk_const_bool(false);

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let (vpa, vpb, vab) = (Var::new(0), Var::new(1), Var::new(2));
    atoms.register(vpa, pa, shinri_theory::types::Owner::Euf);
    atoms.register(vpb, pb, shinri_theory::types::Owner::Euf);
    atoms.register(vab, eq_ab, shinri_theory::types::Owner::Euf);

    let mut euf = Euf::default();
    euf.set_truth_terms(t_true, t_false);
    let mut cx = TheoryCtx {
        terms: &ctx,
        eq: &mut eq,
        atoms: &atoms,
    };
    euf.new_var(&mut cx, vpa, pa);
    euf.new_var(&mut cx, vpb, pb);
    euf.new_var(&mut cx, vab, eq_ab);
    assert!(euf.assert(&mut cx, Lit::new(vpa, true)).is_none());
    assert!(euf.assert(&mut cx, Lit::new(vpb, false)).is_none());
    let conflict = euf.assert(&mut cx, Lit::new(vab, true));
    assert!(conflict.is_some(), "p(a) ∧ ¬p(b) ∧ a=b must conflict");
}

/// a=c ∧ b=d ∧ g(a,b) ≠ g(c,d) is unsat (n-ary congruence).
#[test]
fn nary_congruence_conflict() {
    let mut ctx = Context::new();
    let u = ctx.declare_sort("U");
    let a = uconst(&mut ctx, "a", u);
    let b = uconst(&mut ctx, "b", u);
    let c = uconst(&mut ctx, "c", u);
    let d = uconst(&mut ctx, "d", u);
    let g = ctx.declare_fun("g", &[u, u], u);
    let gab = ctx.mk_app(Op::Uninterpreted(g), &[a, b]).unwrap();
    let gcd = ctx.mk_app(Op::Uninterpreted(g), &[c, d]).unwrap();
    let eq_ac = ctx.mk_eq(a, c).unwrap();
    let eq_bd = ctx.mk_eq(b, d).unwrap();
    let eq_gg = ctx.mk_eq(gab, gcd).unwrap();

    let mut eq = EqualityEngine::default();
    let mut atoms = AtomRegistry::default();
    let (v0, v1, v2) = (Var::new(0), Var::new(1), Var::new(2));
    atoms.register(v0, eq_ac, shinri_theory::types::Owner::Euf);
    atoms.register(v1, eq_bd, shinri_theory::types::Owner::Euf);
    atoms.register(v2, eq_gg, shinri_theory::types::Owner::Euf);

    let mut euf = Euf::default();
    let mut cx = TheoryCtx {
        terms: &ctx,
        eq: &mut eq,
        atoms: &atoms,
    };
    euf.new_var(&mut cx, v0, eq_ac);
    euf.new_var(&mut cx, v1, eq_bd);
    euf.new_var(&mut cx, v2, eq_gg);
    assert!(euf.assert(&mut cx, Lit::new(v2, false)).is_none());
    assert!(euf.assert(&mut cx, Lit::new(v0, true)).is_none());
    let conflict = euf.assert(&mut cx, Lit::new(v1, true));
    assert!(
        conflict.is_some(),
        "a=c ∧ b=d ⇒ g(a,b)=g(c,d) contradicts ≠"
    );
}
