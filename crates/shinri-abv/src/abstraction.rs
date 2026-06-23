//! Build the pure-BV+Bool over-approximation of a QF_ABV formula.
use crate::collect::Collected;
use rustc_hash::FxHashMap;
use shinri_core::{Context, Op, TermId, TermNode};
use std::sync::atomic::{AtomicUsize, Ordering};

static FRESH_CTR: AtomicUsize = AtomicUsize::new(1_000_000);

pub struct Abstraction {
    pub assertions: Vec<TermId>,
    pub read_of: FxHashMap<TermId, TermId>,
    pub eq_proxy: FxHashMap<TermId, TermId>,
}

/// Mint a fresh nullary uninterpreted constant of the given sort.
pub(crate) fn fresh_const(ctx: &mut Context, name: &str, sort: shinri_core::SortId) -> TermId {
    let sym = ctx.declare_fun(name, &[], sort);
    ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
}

/// Read var for `sel`, minting one if absent. Returns `(read_var, Some(sel))`
/// when a new read was introduced (so the caller can blast it), else `None`.
pub fn read_of_or_make(
    ctx: &mut Context,
    abs: &mut Abstraction,
    sel: TermId,
) -> (TermId, Option<TermId>) {
    if let Some(&r) = abs.read_of.get(&sel) {
        return (r, None);
    }
    let elem_sort = ctx.sort_of(sel);
    let n = FRESH_CTR.fetch_add(1, Ordering::Relaxed);
    let r = fresh_const(ctx, &format!("$abv_read_{n}"), elem_sort);
    abs.read_of.insert(sel, r);
    (r, Some(sel))
}

pub fn abstract_arrays(ctx: &mut Context, assertions: &[TermId], c: &Collected) -> Abstraction {
    let mut read_of: FxHashMap<TermId, TermId> = FxHashMap::default();
    let mut eq_proxy: FxHashMap<TermId, TermId> = FxHashMap::default();

    // Read var per distinct select, of the element width (a select's own sort IS the element sort).
    for (n, &sel) in c.selects.iter().enumerate() {
        let elem_sort = ctx.sort_of(sel);
        let r = fresh_const(ctx, &format!("$abv_read_{n}"), elem_sort);
        read_of.insert(sel, r);
    }

    // Bool proxy per distinct array (dis)equality.
    let bool_sort = ctx.bool_sort();
    for (n, &atom) in c.array_eqs.iter().enumerate() {
        let p = fresh_const(ctx, &format!("$abv_eq_{n}"), bool_sort);
        eq_proxy.insert(atom, p);
    }

    // Substitute throughout each assertion.
    let mut memo: FxHashMap<TermId, TermId> = FxHashMap::default();
    let assertions = assertions
        .iter()
        .map(|&a| subst(ctx, a, &read_of, &eq_proxy, &mut memo))
        .collect();

    Abstraction {
        assertions,
        read_of,
        eq_proxy,
    }
}

/// Rewrite a term, replacing select subterms by read vars and array-eq atoms by
/// their proxies. Memoized over the shared DAG.
fn subst(
    ctx: &mut Context,
    t: TermId,
    read_of: &FxHashMap<TermId, TermId>,
    eq_proxy: &FxHashMap<TermId, TermId>,
    memo: &mut FxHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&r) = read_of.get(&t) {
        return r;
    }
    if let Some(&p) = eq_proxy.get(&t) {
        return p;
    }
    if let Some(&m) = memo.get(&t) {
        return m;
    }
    let (op, kids) = match ctx.term_node(t) {
        TermNode::App { op, args, .. } => (*op, ctx.children(*args).to_vec()),
        TermNode::Const { .. } => {
            memo.insert(t, t);
            return t;
        }
    };
    let new_kids: Vec<TermId> = kids
        .iter()
        .map(|&k| subst(ctx, k, read_of, eq_proxy, memo))
        .collect();
    let rebuilt = if new_kids == kids {
        t
    } else {
        ctx.mk_app(op, &new_kids)
            .expect("abstraction preserves sorts")
    };
    memo.insert(t, rebuilt);
    rebuilt
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collect::collect;
    use shinri_core::{BuiltinOp, SortNode};

    fn bv_arr(ctx: &mut Context, iw: u32, ew: u32) -> shinri_core::SortId {
        let i = ctx.bv_sort(iw);
        let e = ctx.bv_sort(ew);
        ctx.array_sort(i, e)
    }
    fn uconst(ctx: &mut Context, name: &str, s: shinri_core::SortId) -> TermId {
        let f = ctx.declare_fun(name, &[], s);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    #[test]
    fn read_of_or_make_is_idempotent() {
        let mut ctx = Context::new();
        let arr = bv_arr(&mut ctx, 8, 8);
        let a = uconst(&mut ctx, "a", arr);
        let s8 = ctx.bv_sort(8);
        let j = uconst(&mut ctx, "j", s8);
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let mut abs = Abstraction {
            assertions: vec![],
            read_of: FxHashMap::default(),
            eq_proxy: FxHashMap::default(),
        };
        let (r1, fresh1) = read_of_or_make(&mut ctx, &mut abs, sel);
        let (r2, fresh2) = read_of_or_make(&mut ctx, &mut abs, sel);
        assert_eq!(r1, r2);
        assert_eq!(fresh1, Some(sel));
        assert_eq!(fresh2, None);
        assert_eq!(ctx.bv_width(ctx.sort_of(r1)), Some(8));
    }

    #[test]
    fn select_becomes_fresh_bv_var_of_element_width() {
        let mut ctx = Context::new();
        let arr = bv_arr(&mut ctx, 8, 8);
        let s8 = ctx.bv_sort(8);
        let a = uconst(&mut ctx, "a", arr);
        let i = uconst(&mut ctx, "i", s8);
        let e = uconst(&mut ctx, "e", s8);
        let sel = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let atom = ctx.mk_eq(sel, e).unwrap();
        let c = collect(&ctx, &[atom]);

        let abs = abstract_arrays(&mut ctx, &[atom], &c);
        // The select got a read var of width 8.
        let r = abs.read_of[&sel];
        assert_eq!(ctx.bv_width(ctx.sort_of(r)), Some(8));
        // The abstracted assertion is (= r e): no Select node remains.
        assert_eq!(abs.assertions.len(), 1);
        assert!(!contains_select(&ctx, abs.assertions[0]));
    }

    fn contains_select(ctx: &Context, t: TermId) -> bool {
        match ctx.term_node(t) {
            TermNode::App {
                op: Op::Builtin(BuiltinOp::Select),
                ..
            } => true,
            TermNode::App { args, .. } => ctx
                .children(*args)
                .to_vec()
                .iter()
                .any(|&k| contains_select(ctx, k)),
            _ => false,
        }
    }

    #[test]
    fn array_eq_becomes_bool_proxy() {
        let mut ctx = Context::new();
        let arr = bv_arr(&mut ctx, 8, 8);
        let a = uconst(&mut ctx, "a", arr);
        let b = uconst(&mut ctx, "b", arr);
        let atom = ctx.mk_eq(a, b).unwrap();
        let c = collect(&ctx, &[atom]);
        let abs = abstract_arrays(&mut ctx, &[atom], &c);
        let p = abs.eq_proxy[&atom];
        assert!(matches!(ctx.sort_node(ctx.sort_of(p)), SortNode::Bool));
        assert_eq!(abs.assertions, vec![p]);
    }
}
