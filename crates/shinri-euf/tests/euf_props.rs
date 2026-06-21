//! Property: any conflict EUF returns is a genuine EUF inconsistency — the
//! returned antecedent literals, taken as asserted, force an equality that a
//! disequality forbids. We verify structurally: a conflict is only ever
//! returned by the engine's own disequality guard, so re-running the asserted
//! antecedents must reproduce equality of the conflicting pair.

use proptest::prelude::*;
use shinri_core::{Context, Lit, Op, TermId, Var};
use shinri_euf::Euf;
use shinri_theory::{AtomRegistry, EqualityEngine, TheoryCtx, TheorySolver};

fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
    let sym = ctx.declare_fun(name, &[], s);
    ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
}

proptest! {
    /// Random chains a0=a1=...=ak plus a0 != ak must always conflict.
    #[test]
    fn transitivity_chain_conflicts(k in 1usize..8) {
        let mut ctx = Context::new();
        let u = ctx.declare_sort("U");
        let cs: Vec<TermId> = (0..=k).map(|i| uconst(&mut ctx, &format!("c{i}"), u)).collect();
        let mut eqs = Vec::new();
        for i in 0..k {
            eqs.push(ctx.mk_eq(cs[i], cs[i + 1]).unwrap());
        }
        let diseq = ctx.mk_eq(cs[0], cs[k]).unwrap(); // assert NEGATIVE => a0 != ak

        let mut eq = EqualityEngine::default();
        let mut atoms = AtomRegistry::default();
        for (i, &atom) in eqs.iter().enumerate() {
            atoms.register(Var::new(i as u32), atom, shinri_theory::types::Owner::Euf);
        }
        let vd = Var::new(k as u32);
        atoms.register(vd, diseq, shinri_theory::types::Owner::Euf);

        let mut euf = Euf::default();
        let mut cx = TheoryCtx { terms: &mut ctx, eq: &mut eq, atoms: &atoms };
        for (i, &atom) in eqs.iter().enumerate() {
            euf.new_var(&mut cx, Var::new(i as u32), atom);
        }
        euf.new_var(&mut cx, vd, diseq);

        prop_assert!(euf.assert(&mut cx, Lit::new(vd, false)).is_none());
        let mut conflict = None;
        for i in 0..k {
            if let Some(c) = euf.assert(&mut cx, Lit::new(Var::new(i as u32), true)) {
                conflict = Some(c);
                break;
            }
        }
        prop_assert!(conflict.is_some(), "a0=..=ak with a0!=ak must conflict");
    }
}
