//! Model-based consistency checks producing refinement lemmas.
use crate::abstraction::Abstraction;
use crate::collect::Collected;
use crate::driver::{Lemma, LemmaLit, SatBridge};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

/// The base array of a select term (`select(array, index)`), and its index.
fn select_parts(ctx: &Context, sel: TermId) -> Option<(TermId, TermId)> {
    match ctx.term_node(sel) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Select),
            args,
            ..
        } => {
            let k = ctx.children(*args);
            Some((k[0], k[1]))
        }
        _ => None,
    }
}

/// §5.1 Functional consistency: two reads on the SAME array term whose index
/// VALUES coincide but whose read VALUES differ ⇒ (i=j) → (ri=rj).
pub fn functional_consistency(
    ctx: &mut Context,
    abs: &Abstraction,
    c: &Collected,
    bridge: &dyn SatBridge,
) -> Vec<Lemma> {
    let mut lemmas = Vec::new();
    let sels = &c.selects;
    for x in 0..sels.len() {
        for y in (x + 1)..sels.len() {
            let (sx, sy) = (sels[x], sels[y]);
            let (Some((ax, ix)), Some((ay, iy))) = (select_parts(ctx, sx), select_parts(ctx, sy))
            else {
                continue;
            };
            if ax != ay {
                continue;
            } // same syntactic array only
            let (rx, ry) = (abs.read_of[&sx], abs.read_of[&sy]);
            let (Some(vix), Some(viy)) = (bridge.value_bv(ctx, ix), bridge.value_bv(ctx, iy))
            else {
                continue;
            };
            let (Some(vrx), Some(vry)) = (bridge.value_bv(ctx, rx), bridge.value_bv(ctx, ry))
            else {
                continue;
            };
            if vix.1 == viy.1 && vrx.1 != vry.1 {
                let eq_ij = ctx.mk_eq(ix, iy).expect("same index width");
                let eq_rr = ctx.mk_eq(rx, ry).expect("same elem width");
                lemmas.push(Lemma(vec![
                    LemmaLit {
                        atom: eq_ij,
                        pos: false,
                    },
                    LemmaLit {
                        atom: eq_rr,
                        pos: true,
                    },
                ]));
            }
        }
    }
    lemmas
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abstraction::abstract_arrays;
    use crate::collect::collect;
    use crate::driver::fake::FakeBridge;
    use shinri_num::Integer;

    fn arr(ctx: &mut Context) -> shinri_core::SortId {
        let i = ctx.bv_sort(8);
        let e = ctx.bv_sort(8);
        ctx.array_sort(i, e)
    }
    fn uconst(ctx: &mut Context, n: &str, s: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(n, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn equal_index_values_but_unequal_reads_emit_congruence_lemma() {
        let mut ctx = Context::new();
        let a = arr(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let av = uconst(&mut ctx, "a", a);
        let i = uconst(&mut ctx, "i", s8);
        let j = uconst(&mut ctx, "j", s8);
        let s1 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[av, i])
            .unwrap();
        let s2 = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[av, j])
            .unwrap();
        let c1 = ctx.mk_bv_const(8, Integer::from(1u64));
        let e1 = ctx.mk_eq(s1, c1).unwrap();
        let c2 = ctx.mk_bv_const(8, Integer::from(2u64));
        let e2 = ctx.mk_eq(s2, c2).unwrap();
        let c = collect(&ctx, &[e1, e2]);
        let abs = abstract_arrays(&mut ctx, &[e1, e2], &c);
        let (r1, r2) = (abs.read_of[&s1], abs.read_of[&s2]);

        // Model: i == j (both 5), but r1=1, r2=2 — a violation.
        let mut fake = FakeBridge::default();
        fake.bv.insert(i, (8, Integer::from(5u64)));
        fake.bv.insert(j, (8, Integer::from(5u64)));
        fake.bv.insert(r1, (8, Integer::from(1u64)));
        fake.bv.insert(r2, (8, Integer::from(2u64)));

        let lemmas = functional_consistency(&mut ctx, &abs, &c, &fake);
        assert_eq!(lemmas.len(), 1, "one congruence violation");
        // Lemma is (i=j) -> (r1=r2): [¬eq(i,j), eq(r1,r2)].
        let eq_ij = ctx.mk_eq(i, j).unwrap();
        let eq_rr = ctx.mk_eq(r1, r2).unwrap();
        assert_eq!(
            lemmas[0],
            Lemma(vec![
                LemmaLit {
                    atom: eq_ij,
                    pos: false
                },
                LemmaLit {
                    atom: eq_rr,
                    pos: true
                },
            ])
        );
    }
}
