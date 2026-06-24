//! Model-based consistency checks producing refinement lemmas.
use crate::abstraction::Abstraction;
use crate::collect::Collected;
use crate::driver::{Lemma, LemmaLit, SatBridge};
use rustc_hash::FxHashMap;
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};

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

fn array_pair(ctx: &Context, atom: TermId) -> Option<(TermId, TermId)> {
    match ctx.term_node(atom) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Eq),
            args,
            ..
        }
        | TermNode::App {
            op: Op::Builtin(BuiltinOp::Distinct),
            args,
            ..
        } => {
            let k = ctx.children(*args);
            Some((k[0], k[1]))
        }
        _ => None,
    }
}

/// Index width of an array-sorted term.
fn index_width(ctx: &Context, arr: TermId) -> u32 {
    match ctx.sort_node(ctx.sort_of(arr)) {
        SortNode::Array(idx, _) => ctx.bv_width(*idx).expect("BV index"),
        _ => panic!("not an array sort"),
    }
}

/// Index terms of all selects whose base array is `a` or `b`.
fn accessed_indices(ctx: &Context, c: &Collected, a: TermId, b: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    for &sel in &c.selects {
        if let Some((base, idx)) = select_parts(ctx, sel) {
            if base == a || base == b {
                out.push(idx);
            }
        }
    }
    out
}

pub fn extensionality(
    ctx: &mut Context,
    abs: &mut Abstraction,
    c: &Collected,
    bridge: &dyn SatBridge,
    witnesses: &mut FxHashMap<TermId, TermId>,
) -> Vec<Lemma> {
    let mut lemmas = Vec::new();
    for &atom in &c.array_eqs.clone() {
        let Some((a, b)) = array_pair(ctx, atom) else {
            continue;
        };
        let p = abs.eq_proxy[&atom];
        match bridge.value_bool(p) {
            Some(true) => {
                // Agreement over accessed indices.
                for k in accessed_indices(ctx, c, a, b) {
                    let sak = ctx
                        .mk_app(Op::Builtin(BuiltinOp::Select), &[a, k])
                        .expect("ws");
                    let sbk = ctx
                        .mk_app(Op::Builtin(BuiltinOp::Select), &[b, k])
                        .expect("ws");
                    let (rak, _) = crate::abstraction::read_of_or_make(ctx, abs, sak);
                    let (rbk, _) = crate::abstraction::read_of_or_make(ctx, abs, sbk);
                    if bridge.value_bv(ctx, rak).map(|x| x.1)
                        != bridge.value_bv(ctx, rbk).map(|x| x.1)
                    {
                        let eq_rr = ctx.mk_eq(rak, rbk).expect("ws");
                        lemmas.push(Lemma(vec![
                            LemmaLit {
                                atom: p,
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
            Some(false) => {
                // One witness per pair, minted once.
                let w = if let Some(&existing) = witnesses.get(&atom) {
                    existing
                } else {
                    let iw = index_width(ctx, a);
                    let s = ctx.bv_sort(iw);
                    let name = format!("$abv_wit_{}", witnesses.len());
                    let fresh = crate::abstraction::fresh_const(ctx, &name, s);
                    witnesses.insert(atom, fresh);
                    fresh
                };
                let saw = ctx
                    .mk_app(Op::Builtin(BuiltinOp::Select), &[a, w])
                    .expect("ws");
                let sbw = ctx
                    .mk_app(Op::Builtin(BuiltinOp::Select), &[b, w])
                    .expect("ws");
                let (raw, _) = crate::abstraction::read_of_or_make(ctx, abs, saw);
                let (rbw, _) = crate::abstraction::read_of_or_make(ctx, abs, sbw);
                let eq_rr = ctx.mk_eq(raw, rbw).expect("ws");
                lemmas.push(Lemma(vec![
                    LemmaLit { atom: p, pos: true },
                    LemmaLit {
                        atom: eq_rr,
                        pos: false,
                    },
                ]));
            }
            None => {}
        }
    }
    lemmas
}

fn store_parts(ctx: &Context, t: TermId) -> Option<(TermId, TermId, TermId)> {
    match ctx.term_node(t) {
        TermNode::App {
            op: Op::Builtin(BuiltinOp::Store),
            args,
            ..
        } => {
            let k = ctx.children(*args);
            Some((k[0], k[1], k[2]))
        }
        _ => None,
    }
}

/// §5.2 ROW. For each `select(store(a,i,e), j)`:
///   val(i)==val(j): lemma (i=j) → (r=e)
///   val(i)!=val(j): mint select(a,j); lemma (i≠j) → (r = read(select(a,j)))
///
/// NOTE: ROW-2 introduces `selaj` which is NOT yet in `c.selects`. The controller
/// (Task 8) must, after each round, re-run `collect`-equivalent registration for
/// newly minted selects (they are recorded in `abs.read_of`); functional-consistency
/// over the *new* read is reached in subsequent rounds because the controller adds
/// fresh selects to its working set.
pub fn read_over_write(
    ctx: &mut Context,
    abs: &mut Abstraction,
    c: &Collected,
    bridge: &dyn SatBridge,
) -> Vec<Lemma> {
    let mut lemmas = Vec::new();
    for &sel in &c.selects.clone() {
        let Some((base, j)) = select_parts(ctx, sel) else {
            continue;
        };
        let Some((a, i, e)) = store_parts(ctx, base) else {
            continue;
        };
        let r = abs.read_of[&sel];
        let (Some(vi), Some(vj)) = (bridge.value_bv(ctx, i), bridge.value_bv(ctx, j)) else {
            continue;
        };
        if vi.1 == vj.1 {
            // ROW-1: only emit if model currently violates r == e.
            if bridge.value_bv(ctx, r).map(|x| x.1) != bridge.value_bv(ctx, e).map(|x| x.1) {
                let eq_ij = ctx.mk_eq(i, j).expect("idx width");
                let eq_re = ctx.mk_eq(r, e).expect("elem width");
                lemmas.push(Lemma(vec![
                    LemmaLit {
                        atom: eq_ij,
                        pos: false,
                    },
                    LemmaLit {
                        atom: eq_re,
                        pos: true,
                    },
                ]));
            }
        } else {
            // ROW-2: select(a, j) on demand.
            let selaj = ctx
                .mk_app(Op::Builtin(BuiltinOp::Select), &[a, j])
                .expect("well-sorted");
            let (raj, _fresh) = crate::abstraction::read_of_or_make(ctx, abs, selaj);
            if bridge.value_bv(ctx, r).map(|x| x.1) != bridge.value_bv(ctx, raj).map(|x| x.1) {
                let eq_ij = ctx.mk_eq(i, j).expect("idx width");
                let eq_rr = ctx.mk_eq(r, raj).expect("elem width");
                lemmas.push(Lemma(vec![
                    LemmaLit {
                        atom: eq_ij,
                        pos: true, // (i≠j) in antecedent → eq(i,j) appears positive in disjunction
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
    fn row1_equal_index_emits_read_equals_stored() {
        let mut ctx = Context::new();
        let arr_s = {
            let i = ctx.bv_sort(8);
            let e = ctx.bv_sort(8);
            ctx.array_sort(i, e)
        };
        let s8 = ctx.bv_sort(8);
        let a = {
            let f = ctx.declare_fun("a", &[], arr_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let i = {
            let f = ctx.declare_fun("i", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let j = {
            let f = ctx.declare_fun("j", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let e = {
            let f = ctx.declare_fun("e", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, j])
            .unwrap();
        let atom = ctx.mk_eq(sel, e).unwrap();
        let c = crate::collect::collect(&ctx, &[atom]);
        let mut abs = crate::abstraction::abstract_arrays(&mut ctx, &[atom], &c);
        let r = abs.read_of[&sel];

        // Model: val(i)==val(j)==3 → ROW-1 violation candidate (r must equal e).
        let mut fake = crate::driver::fake::FakeBridge::default();
        fake.bv.insert(i, (8, shinri_num::Integer::from(3u64)));
        fake.bv.insert(j, (8, shinri_num::Integer::from(3u64)));
        fake.bv.insert(r, (8, shinri_num::Integer::from(0u64)));
        fake.bv.insert(e, (8, shinri_num::Integer::from(9u64))); // r != e in model → violated

        let lemmas = read_over_write(&mut ctx, &mut abs, &c, &fake);
        let eq_ij = ctx.mk_eq(i, j).unwrap();
        let eq_re = ctx.mk_eq(r, e).unwrap();
        assert!(lemmas.contains(&Lemma(vec![
            LemmaLit {
                atom: eq_ij,
                pos: false
            },
            LemmaLit {
                atom: eq_re,
                pos: true
            },
        ])));
    }

    #[test]
    fn row2_unequal_index_emits_read_equals_aliased_read() {
        let mut ctx = Context::new();
        let arr_s = {
            let i = ctx.bv_sort(8);
            let e = ctx.bv_sort(8);
            ctx.array_sort(i, e)
        };
        let s8 = ctx.bv_sort(8);
        let a = {
            let f = ctx.declare_fun("a2", &[], arr_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let i = {
            let f = ctx.declare_fun("i2", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let j = {
            let f = ctx.declare_fun("j2", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let e = {
            let f = ctx.declare_fun("e2", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, j])
            .unwrap();
        let atom = ctx.mk_eq(sel, e).unwrap();
        let c = crate::collect::collect(&ctx, &[atom]);
        let mut abs = crate::abstraction::abstract_arrays(&mut ctx, &[atom], &c);
        let r = abs.read_of[&sel];

        // Pre-create select(a, j) and pin its read var so we know raj's TermId
        // before read_over_write runs (hash-consing guarantees same TermId).
        let selaj = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let (raj, _) = crate::abstraction::read_of_or_make(&mut ctx, &mut abs, selaj);

        // Model: val(i)=1, val(j)=2 (unequal → ROW-2), val(r)=5, val(raj)=7 (violated).
        let mut fake = crate::driver::fake::FakeBridge::default();
        fake.bv.insert(i, (8, shinri_num::Integer::from(1u64)));
        fake.bv.insert(j, (8, shinri_num::Integer::from(2u64)));
        fake.bv.insert(r, (8, shinri_num::Integer::from(5u64)));
        fake.bv.insert(raj, (8, shinri_num::Integer::from(7u64))); // r != raj → violation

        let lemmas = read_over_write(&mut ctx, &mut abs, &c, &fake);
        let eq_ij = ctx.mk_eq(i, j).unwrap();
        let eq_rr = ctx.mk_eq(r, raj).unwrap();
        assert!(
            lemmas.contains(&Lemma(vec![
                LemmaLit {
                    atom: eq_ij,
                    pos: true // (i≠j) antecedent → eq(i,j) is positive in disjunction
                },
                LemmaLit {
                    atom: eq_rr,
                    pos: true
                },
            ])),
            "ROW-2 lemma not found in: {lemmas:?}"
        );

        // Sanity: when model does NOT violate (r == raj), no lemma should be emitted.
        fake.bv.insert(r, (8, shinri_num::Integer::from(7u64)));
        // raj already 7 → no violation
        let lemmas_no_viol = read_over_write(&mut ctx, &mut abs, &c, &fake);
        assert!(
            !lemmas_no_viol.contains(&Lemma(vec![
                LemmaLit {
                    atom: eq_ij,
                    pos: true
                },
                LemmaLit {
                    atom: eq_rr,
                    pos: true
                },
            ])),
            "ROW-2 lemma should not fire when model satisfies r == raj"
        );
    }

    #[test]
    fn ext_false_proxy_mints_witness_disequality() {
        let mut ctx = Context::new();
        let arr_s = {
            let i = ctx.bv_sort(8);
            let e = ctx.bv_sort(8);
            ctx.array_sort(i, e)
        };
        let a = {
            let f = ctx.declare_fun("a", &[], arr_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let b = {
            let f = ctx.declare_fun("b", &[], arr_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let atom = ctx.mk_eq(a, b).unwrap();
        let c = crate::collect::collect(&ctx, &[atom]);
        let mut abs = crate::abstraction::abstract_arrays(&mut ctx, &[atom], &c);
        let p = abs.eq_proxy[&atom];

        let mut fake = crate::driver::fake::FakeBridge::default();
        fake.boolv.insert(p, false); // a != b asserted

        let mut witnesses = rustc_hash::FxHashMap::default();
        let lemmas = extensionality(&mut ctx, &mut abs, &c, &fake, &mut witnesses);
        assert_eq!(lemmas.len(), 1);
        let w = witnesses[&atom];
        assert_eq!(ctx.bv_width(ctx.sort_of(w)), Some(8));
        // Lemma: [p (pos:true), ¬eq(read(sel a w), read(sel b w))].
        let saw = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, w]).unwrap();
        let sbw = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[b, w]).unwrap();
        let raw = abs.read_of[&saw];
        let rbw = abs.read_of[&sbw];
        let eq_rr = ctx.mk_eq(raw, rbw).unwrap();
        assert_eq!(
            lemmas[0],
            Lemma(vec![
                LemmaLit { atom: p, pos: true },
                LemmaLit {
                    atom: eq_rr,
                    pos: false
                },
            ])
        );
    }

    #[test]
    fn ext_true_proxy_emits_agreement_when_reads_differ() {
        let mut ctx = Context::new();
        let arr_s = {
            let i = ctx.bv_sort(8);
            let e = ctx.bv_sort(8);
            ctx.array_sort(i, e)
        };
        let s8 = ctx.bv_sort(8);
        let a = {
            let f = ctx.declare_fun("a", &[], arr_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let b = {
            let f = ctx.declare_fun("b", &[], arr_s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let k = {
            let f = ctx.declare_fun("k", &[], s8);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let sak = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, k]).unwrap();
        let sbk = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[b, k]).unwrap();
        let aeq = ctx.mk_eq(a, b).unwrap();
        // Reads are present in the formula so accessed_indices finds k.
        let c = crate::collect::collect(&ctx, &[aeq, sak, sbk]);
        let mut abs = crate::abstraction::abstract_arrays(&mut ctx, &[aeq, sak, sbk], &c);
        let p = abs.eq_proxy[&aeq];
        let (rak, rbk) = (abs.read_of[&sak], abs.read_of[&sbk]);
        let mut fake = crate::driver::fake::FakeBridge::default();
        fake.boolv.insert(p, true);
        fake.bv.insert(rak, (8, shinri_num::Integer::from(1u64)));
        fake.bv.insert(rbk, (8, shinri_num::Integer::from(2u64)));
        let mut w = rustc_hash::FxHashMap::default();
        let lemmas = extensionality(&mut ctx, &mut abs, &c, &fake, &mut w);
        let eq_rr = ctx.mk_eq(rak, rbk).unwrap();
        assert!(lemmas.contains(&Lemma(vec![
            LemmaLit {
                atom: p,
                pos: false
            },
            LemmaLit {
                atom: eq_rr,
                pos: true
            },
        ])));
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
