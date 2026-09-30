//! Slice 52 (H3): the word-equation resolution gate's view of conditional
//! merges.
//!
//! The E1 gate refuses to resolve a word equation whose sides sit in a class
//! that a CONDITIONAL (dl>0) merge touched, because resolution reads the
//! single-level normal forms and does not cite that merge (ce1..ce8). The
//! shared `input_cond_roots` set is too coarse for this one gate, in two ways:
//!
//! - it holds every conditional DISEQUALITY, but a disequality merges nothing,
//!   so it cannot make a normal form branch-local;
//! - it holds the equation's OWN literal, but every result of resolving the
//!   equation already cites that literal (`Conflict`/`Propagate` carry
//!   `Asserted(lit)`, `Split` is guarded by `¬lit`).
//!
//! So this map records, per class root, WHICH conditional sources touched it.
//! Only non-minted conditional equalities and conditional propagation merges
//! are recorded. A side is clean for equation `e` iff no root it reads has a
//! contributor other than `e` itself. The other readers of `input_cond_roots`
//! (membership, order, same-word conflicts) are unchanged.
use rustc_hash::FxHashMap;
use shinri_core::{Context, TermId};
use shinri_theory::types::ENodeId;
use shinri_theory::EqualityEngine;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CondSrc {
    /// A conditional (dl>0), non-minted input equality atom.
    Eq(TermId),
    /// A conditional slice-33 propagation merge. Never exempt.
    Propagation,
}

#[derive(Default, Debug)]
pub(crate) struct WordEqGate {
    by_root: FxHashMap<ENodeId, Vec<CondSrc>>,
}

impl WordEqGate {
    pub(crate) fn add(&mut self, root: ENodeId, src: CondSrc) {
        let v = self.by_root.entry(root).or_default();
        if !v.contains(&src) {
            v.push(src);
        }
    }

    /// Carry both pre-merge roots' contributors onto the post-merge root, so an
    /// intra-check merge never launders a dirty class clean.
    pub(crate) fn on_merge(&mut self, old_a: ENodeId, old_b: ENodeId, new_root: ENodeId) {
        let mut moved = Vec::new();
        for r in [old_a, old_b] {
            if r != new_root {
                if let Some(v) = self.by_root.remove(&r) {
                    moved.extend(v);
                }
            }
        }
        for s in moved {
            self.add(new_root, s);
        }
    }

    /// `true` iff every flattened atom of `t` sits in a class whose only
    /// conditional contributor (if any) is the equation `own` itself.
    pub(crate) fn side_clean_for(
        &self,
        eq: &mut EqualityEngine,
        terms: &Context,
        t: TermId,
        own: TermId,
    ) -> bool {
        if self.by_root.is_empty() {
            return true;
        }
        let mut flat = Vec::new();
        crate::normalize::flatten(terms, t, &mut flat);
        flat.iter().all(|&a| {
            let n = eq.intern(a);
            self.by_root
                .get(&eq.find(n))
                .is_none_or(|v| v.iter().all(|&s| s == CondSrc::Eq(own)))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use shinri_core::{Lit, Op, Var};
    use shinri_theory::types::EqJust;

    fn var(ctx: &mut Context, name: &str) -> TermId {
        let ss = ctx.string_sort();
        let f = ctx.declare_fun(name, &[], ss);
        ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
    }

    /// `(ctx, eq, x, y, e_own, e_other)` with `e_own = (= x "A")`,
    /// `e_other = (= y "B")`.
    fn fixture() -> (Context, EqualityEngine, TermId, TermId, TermId, TermId) {
        let mut ctx = Context::new();
        let eq = EqualityEngine::default();
        let x = var(&mut ctx, "x_g");
        let y = var(&mut ctx, "y_g");
        let a = ctx.mk_string_const("A");
        let b = ctx.mk_string_const("B");
        let e_own = ctx.mk_eq(x, a).unwrap();
        let e_other = ctx.mk_eq(y, b).unwrap();
        (ctx, eq, x, y, e_own, e_other)
    }

    fn root(eq: &mut EqualityEngine, t: TermId) -> ENodeId {
        let n = eq.intern(t);
        eq.find(n)
    }

    #[test]
    fn empty_gate_is_clean() {
        let (ctx, mut eq, x, _y, e_own, _) = fixture();
        assert!(WordEqGate::default().side_clean_for(&mut eq, &ctx, x, e_own));
    }

    #[test]
    fn own_equation_is_clean_for_itself_only() {
        let (ctx, mut eq, x, _y, e_own, e_other) = fixture();
        let mut g = WordEqGate::default();
        let rx = root(&mut eq, x);
        g.add(rx, CondSrc::Eq(e_own));
        assert!(g.side_clean_for(&mut eq, &ctx, x, e_own));
        assert!(!g.side_clean_for(&mut eq, &ctx, x, e_other));
    }

    #[test]
    fn second_conditional_equation_blocks() {
        let (ctx, mut eq, x, _y, e_own, e_other) = fixture();
        let mut g = WordEqGate::default();
        let rx = root(&mut eq, x);
        g.add(rx, CondSrc::Eq(e_own));
        g.add(rx, CondSrc::Eq(e_other));
        assert!(!g.side_clean_for(&mut eq, &ctx, x, e_own));
    }

    #[test]
    fn propagation_contributor_blocks() {
        let (ctx, mut eq, x, _y, e_own, _) = fixture();
        let mut g = WordEqGate::default();
        let rx = root(&mut eq, x);
        g.add(rx, CondSrc::Propagation);
        assert!(!g.side_clean_for(&mut eq, &ctx, x, e_own));
    }

    #[test]
    fn untouched_class_is_clean() {
        let (ctx, mut eq, x, y, e_own, e_other) = fixture();
        let mut g = WordEqGate::default();
        let ry = root(&mut eq, y);
        g.add(ry, CondSrc::Eq(e_other));
        assert!(g.side_clean_for(&mut eq, &ctx, x, e_own));
    }

    /// Review Focus 4: after a merge unions x's and y's classes, y's other
    /// contributor must still block x's equation.
    #[test]
    fn on_merge_carries_contributors() {
        let (ctx, mut eq, x, y, e_own, e_other) = fixture();
        let mut g = WordEqGate::default();
        let (rx, ry) = (root(&mut eq, x), root(&mut eq, y));
        g.add(rx, CondSrc::Eq(e_own));
        g.add(ry, CondSrc::Eq(e_other));
        let _ = eq.merge(rx, ry, EqJust::Asserted(Lit::new(Var::new(1), true)));
        let r = eq.find(rx);
        g.on_merge(rx, ry, r);
        assert!(!g.side_clean_for(&mut eq, &ctx, x, e_own));
        assert!(!g.side_clean_for(&mut eq, &ctx, y, e_own));
    }
}
