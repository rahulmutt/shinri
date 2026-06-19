//! Shared interface variables + purification (spec §7).

use crate::types::ENodeId;
use rustc_hash::FxHashSet;
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

#[derive(Default)]
pub struct InterfaceSet {
    shared: Vec<ENodeId>,
    shared_set: FxHashSet<ENodeId>,
    counter: u32,
}

impl InterfaceSet {
    pub fn mark_shared(&mut self, n: ENodeId) {
        if self.shared_set.insert(n) {
            self.shared.push(n);
        }
    }
    #[inline]
    pub fn is_shared(&self, n: ENodeId) -> bool {
        self.shared_set.contains(&n)
    }
    #[inline]
    pub fn shared(&self) -> &[ENodeId] {
        &self.shared
    }
    fn fresh_name(&mut self) -> String {
        let id = self.counter;
        self.counter += 1;
        format!("!iface{id}")
    }
}

/// Theory of a term by its top operator (leaves are theory-neutral).
#[derive(Clone, Copy, PartialEq, Eq)]
enum TTheory {
    Arith,
    Euf,
    Leaf,
}

fn theory_of(terms: &Context, t: TermId) -> TTheory {
    match terms.term_node(t) {
        TermNode::Const { .. } => TTheory::Leaf,
        TermNode::App { op, args, .. } => {
            let arity = terms.children(*args).len();
            match op {
                Op::Builtin(BuiltinOp::Add | BuiltinOp::Sub | BuiltinOp::Mul | BuiltinOp::Neg) => {
                    TTheory::Arith
                }
                Op::Uninterpreted(_) if arity == 0 => TTheory::Leaf, // a plain variable
                Op::Uninterpreted(_) => TTheory::Euf,
                _ => TTheory::Leaf,
            }
        }
    }
}

/// Recursively purify `t`; whenever a child's theory differs from the parent's
/// (and neither is a leaf), replace the child with a fresh interface variable
/// and emit its defining equality.
pub fn purify(
    terms: &mut Context,
    iface: &mut InterfaceSet,
    atom: TermId,
) -> (TermId, Vec<(TermId, TermId)>) {
    let mut defs = Vec::new();
    let out = purify_rec(terms, iface, atom, &mut defs);
    (out, defs)
}

fn purify_rec(
    terms: &mut Context,
    iface: &mut InterfaceSet,
    t: TermId,
    defs: &mut Vec<(TermId, TermId)>,
) -> TermId {
    let (op, child_ids) = match terms.term_node(t) {
        TermNode::Const { .. } => return t,
        TermNode::App { op, args, .. } => (*op, terms.children(*args).to_vec()),
    };
    let parent_th = theory_of(terms, t);
    let mut new_children = Vec::with_capacity(child_ids.len());
    let mut changed = false;
    for c in child_ids {
        let pc = purify_rec(terms, iface, c, defs);
        let child_th = theory_of(terms, pc);
        let cross = !matches!(parent_th, TTheory::Leaf)
            && !matches!(child_th, TTheory::Leaf)
            && parent_th != child_th;
        if cross {
            // Introduce a fresh interface variable of the child's sort.
            let sort = terms.sort_of(pc);
            let name = iface.fresh_name();
            let sym = terms.declare_fun(&name, &[], sort);
            let w = terms.mk_app(Op::Uninterpreted(sym), &[]).unwrap();
            defs.push((w, pc));
            new_children.push(w);
            changed = true;
        } else {
            changed |= pc != c;
            new_children.push(pc);
        }
    }
    if changed {
        terms
            .mk_app(op, &new_children)
            .expect("purify: sort-preserving rebuild")
    } else {
        t
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::Rational;

    #[test]
    fn purify_lifts_arith_argument_under_uninterpreted_fn() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        // f : (Real) Real, x,y : Real
        let f = ctx.declare_fun("f", &[real], real);
        let xs = ctx.declare_fun("x", &[], real);
        let ys = ctx.declare_fun("y", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(ys), &[]).unwrap();
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, y]).unwrap();
        let fsum = ctx.mk_app(Op::Uninterpreted(f), &[sum]).unwrap();
        let mut iface = InterfaceSet::default();
        let (pure, defs) = purify(&mut ctx, &mut iface, fsum);
        assert_eq!(defs.len(), 1);
        let (w, def) = defs[0];
        assert_eq!(def, sum); // w := x + y
        assert_ne!(pure, fsum); // f(w) != f(x+y)
                                // The purified term is f(w).
        assert_eq!(pure, ctx.mk_app(Op::Uninterpreted(f), &[w]).unwrap());
    }

    #[test]
    fn purify_leaves_pure_terms_untouched() {
        let mut ctx = Context::new();
        let real = ctx.real_sort();
        let xs = ctx.declare_fun("x", &[], real);
        let x = ctx.mk_app(Op::Uninterpreted(xs), &[]).unwrap();
        let one = ctx.mk_numeral(Rational::from_int(1i128.into()), real);
        let sum = ctx.mk_app(Op::Builtin(BuiltinOp::Add), &[x, one]).unwrap();
        let mut iface = InterfaceSet::default();
        let (pure, defs) = purify(&mut ctx, &mut iface, sum);
        assert!(defs.is_empty());
        assert_eq!(pure, sum);
    }
}
