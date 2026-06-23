//! Collect array operations (select/store/array-equality) over BV-sorted arrays.
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, SortNode, TermId, TermNode};

/// Array operations found in the assertion DAG.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Collected {
    pub selects: Vec<TermId>,
    pub stores: Vec<TermId>,
    /// `(= a b)` or `(distinct a b)` whose operands are array-sorted.
    pub array_eqs: Vec<TermId>,
}

/// True if `t` has an `(Array _ _)` sort.
fn is_array_sorted(ctx: &Context, t: TermId) -> bool {
    matches!(ctx.sort_node(ctx.sort_of(t)), SortNode::Array(_, _))
}

pub fn collect(ctx: &Context, assertions: &[TermId]) -> Collected {
    let mut out = Collected::default();
    let mut seen = FxHashSet::default();
    let mut sel = FxHashSet::default();
    let mut sto = FxHashSet::default();
    let mut aeq = FxHashSet::default();
    for &a in assertions {
        walk(ctx, a, &mut seen, &mut out, &mut sel, &mut sto, &mut aeq);
    }
    out
}

fn walk(
    ctx: &Context,
    t: TermId,
    seen: &mut FxHashSet<TermId>,
    out: &mut Collected,
    sel: &mut FxHashSet<TermId>,
    sto: &mut FxHashSet<TermId>,
    aeq: &mut FxHashSet<TermId>,
) {
    if !seen.insert(t) {
        return;
    }
    let (op, kids) = match ctx.term_node(t) {
        TermNode::App { op, args, .. } => (*op, ctx.children(*args).to_vec()),
        TermNode::Const { .. } => return,
    };
    match op {
        Op::Builtin(BuiltinOp::Select) => {
            if sel.insert(t) {
                out.selects.push(t);
            }
        }
        Op::Builtin(BuiltinOp::Store) => {
            if sto.insert(t) {
                out.stores.push(t);
            }
        }
        Op::Builtin(BuiltinOp::Eq) | Op::Builtin(BuiltinOp::Distinct)
            if !kids.is_empty() && is_array_sorted(ctx, kids[0]) && aeq.insert(t) =>
        {
            out.array_eqs.push(t);
        }
        _ => {}
    }
    for k in kids {
        walk(ctx, k, seen, out, sel, sto, aeq);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_num::Integer;

    fn bv_arr(ctx: &mut Context) -> shinri_core::SortId {
        let i = ctx.bv_sort(8);
        let e = ctx.bv_sort(8);
        ctx.array_sort(i, e)
    }
    fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn collects_select_store_and_array_eq() {
        let mut ctx = Context::new();
        let arr = bv_arr(&mut ctx);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let st = ctx
            .mk_app(Op::Builtin(BuiltinOp::Store), &[a, i, e])
            .unwrap();
        let sel = ctx
            .mk_app(Op::Builtin(BuiltinOp::Select), &[st, i])
            .unwrap();
        let b = uconst(&mut ctx, "b", arr);
        let aeq = ctx.mk_eq(a, b).unwrap();
        let bv_eq = {
            let c = ctx.mk_bv_const(8, Integer::from(0u64));
            ctx.mk_eq(i, c).unwrap() // NOT an array eq — must be ignored
        };

        let got = collect(&ctx, &[sel, aeq, bv_eq]);
        assert_eq!(got.selects, vec![sel]);
        assert_eq!(got.stores, vec![st]);
        assert_eq!(got.array_eqs, vec![aeq]);
    }
}
