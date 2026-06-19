use shinri_core::{Context, Lit, Op, TermId, Var};
use shinri_euf::Euf;
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
