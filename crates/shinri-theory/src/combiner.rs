//! The Nelson–Oppen combinator (spec §6). Generic over its two theory fields
//! (`euf`, `arith`) until shinri-euf/shinri-arith exist; a fixed-arity,
//! enum-routed, fully monomorphized struct — not a variadic tuple.

use crate::atom::{classify, AtomRegistry, Unsupported};
use crate::eq_engine::EqualityEngine;
use crate::interface::InterfaceSet;
use crate::solver_trait::{TheoryCtx, TheorySolver};
use crate::types::{MergeEvent, Owner};
use shinri_core::{Context, Lit, TermId, TheoryJust, Var};
use shinri_sat::{Effort, Theory, TheoryResult};

pub struct Combiner<E: TheorySolver, A: TheorySolver> {
    terms: Context,
    eq: EqualityEngine,
    atoms: AtomRegistry,
    iface: InterfaceSet,
    euf: E,
    arith: A,
    level: usize,
    merges: Vec<MergeEvent>,
    /// A conflict detected during `assert` (the SAT seam's `assert` is
    /// infallible); surfaced on the next `propagate` (spec §5.2 bridge).
    pending_conflict: Option<Vec<crate::types::EqLeaf>>,
}

impl<E: TheorySolver, A: TheorySolver> Default for Combiner<E, A> {
    fn default() -> Self {
        Combiner::with_context(Context::new())
    }
}

impl<E: TheorySolver, A: TheorySolver> Combiner<E, A> {
    pub fn with_context(terms: Context) -> Self {
        Combiner {
            terms,
            eq: EqualityEngine::default(),
            atoms: AtomRegistry::default(),
            iface: InterfaceSet::default(),
            euf: E::default(),
            arith: A::default(),
            level: 0,
            merges: Vec::new(),
            pending_conflict: None,
        }
    }

    /// Classify and register an atom, refusing unsupported constructs (spec §9).
    pub fn register_atom(&mut self, v: Var, atom: TermId) -> Result<(), Unsupported> {
        let owner = classify(&self.terms, atom)?;
        self.atoms.register(v, atom, owner);
        // Split the ctx borrow from the theory fields (the §5.5 pattern).
        match owner {
            Owner::Euf => {
                let mut cx = TheoryCtx {
                    terms: &self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.euf.new_var(&mut cx, v, atom);
            }
            Owner::Arith => {
                let mut cx = TheoryCtx {
                    terms: &self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.arith.new_var(&mut cx, v, atom);
            }
            Owner::Shared => {
                // Purify first: splits mixed terms, emitting defining equalities
                // for fresh interface variables (borrow of self.terms is separate
                // from self.eq / self.iface).
                let (_pure, defs) = crate::interface::purify(&mut self.terms, &mut self.iface, atom);
                for (w, def) in defs {
                    let wn = self.eq.intern(w);
                    let dn = self.eq.intern(def);
                    self.iface.mark_shared(wn);
                    // Definitional equality holds unconditionally (level 0).
                    let _ = self.eq.merge(wn, dn, crate::types::EqJust::Asserted(Lit::from_code(0)));
                }
                // Re-borrow to notify both theories of the (purified) atom.
                let mut cx = TheoryCtx {
                    terms: &self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                self.euf.new_var(&mut cx, v, atom);
                self.arith.new_var(&mut cx, v, atom);
            }
        }
        Ok(())
    }
}

impl<E: TheorySolver, A: TheorySolver> Theory for Combiner<E, A> {
    fn assert(&mut self, lit: Lit) {
        let owner = self.atoms.owner(lit.var());
        let mut cx = TheoryCtx {
            terms: &self.terms,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        let conflict = match owner {
            Owner::Euf => self.euf.assert(&mut cx, lit),
            Owner::Arith => self.arith.assert(&mut cx, lit),
            Owner::Shared => {
                let e = self.euf.assert(&mut cx, lit);
                let a = self.arith.assert(&mut cx, lit);
                e.or(a)
            }
        };
        if conflict.is_some() && self.pending_conflict.is_none() {
            self.pending_conflict = conflict;
        }
    }

    fn new_var(&mut self, _v: Var) {
        // Atom registration (register_atom) is the real entry point; the SAT
        // layer's new_var carries no atom, so there is nothing to do here.
    }

    fn propagate(&mut self, out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
        if let Some(leaves) = self.take_pending_conflict_leaves() {
            return Some(self.expand_conflict(leaves));
        }
        if let Some(leaves) = self.drive_propagation(out) {
            return Some(self.expand_conflict(leaves));
        }
        None
    }

    fn explain(&mut self, _just: TheoryJust, _out: &mut Vec<Lit>) {
        // Task 12 implements the cross-theory expansion.
    }

    fn check(&mut self, _effort: Effort) -> TheoryResult {
        // Task 11 replaces this with the final-check fixpoint.
        TheoryResult::Sat
    }

    fn push(&mut self) {
        self.level += 1;
        self.eq.push();
        self.euf.push();
        self.arith.push();
    }

    fn pop(&mut self, n: usize) {
        let target = self.level - n;
        self.eq.pop(target);
        self.euf.pop(target);
        self.arith.pop(target);
        self.level = target;
    }
}

impl<E: TheorySolver, A: TheorySolver> Combiner<E, A> {
    fn drive_propagation(
        &mut self,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<crate::types::EqLeaf>> {
        loop {
            let before = out.len();
            // 1. Theory propagation.
            {
                let mut cx = TheoryCtx {
                    terms: &self.terms,
                    eq: &mut self.eq,
                    atoms: &self.atoms,
                };
                if let Some(cf) = self.euf.propagate(&mut cx, out) {
                    return Some(cf);
                }
                if let Some(cf) = self.arith.propagate(&mut cx, out) {
                    return Some(cf);
                }
            }
            // 2. Drain congruence/interface merges so each theory can react
            //    next iteration. EUF's congruence driver consumes them via the
            //    shared engine; here we only detect whether progress occurred.
            self.merges.clear();
            self.eq.drain_merges(&mut self.merges);
            let progressed = out.len() != before || !self.merges.is_empty();
            self.merges.clear();
            if !progressed {
                return None;
            }
        }
    }

    fn take_pending_conflict_leaves(&mut self) -> Option<Vec<crate::types::EqLeaf>> {
        self.pending_conflict.take()
    }

    /// Task 12 replaces this with the cross-theory Explainer expansion + negation.
    fn expand_conflict(&mut self, _leaves: Vec<crate::types::EqLeaf>) -> Vec<Lit> {
        Vec::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver_trait::TCheck;
    use crate::types::EqLeaf;
    use crate::{Explainer, ModelBuilder};
    use shinri_core::Op;

    /// Records asserted literals; never conflicts. Lets us observe routing.
    #[derive(Default)]
    struct Spy {
        asserted: Vec<Lit>,
        level: usize,
    }
    impl TheorySolver for Spy {
        const THEORY_ID: u16 = 1;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>> {
            self.asserted.push(lit);
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _out: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {
            self.level += 1;
        }
        fn pop(&mut self, level: usize) {
            self.level = level;
        }
    }

    /// Returns a conflict on its FIRST assert, then never again. Lets us drive
    /// the assert→propagate `pending_conflict` bridge.
    #[derive(Default)]
    struct AssertConflicter {
        fired: bool,
    }
    impl TheorySolver for AssertConflicter {
        const THEORY_ID: u16 = 7;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
            if !self.fired {
                self.fired = true;
                Some(vec![EqLeaf::Asserted(Lit::new(Var::new(99), true))])
            } else {
                None
            }
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _out: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _level: usize) {}
    }

    fn real_var(ctx: &mut Context, name: &str) -> TermId {
        let real = ctx.real_sort();
        let sym = ctx.declare_fun(name, &[], real);
        ctx.mk_app(Op::Uninterpreted(sym), &[]).unwrap()
    }

    #[test]
    fn assert_routes_to_the_owning_theory() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let le = ctx.mk_app(Op::Builtin(shinri_core::BuiltinOp::Le), &[x, y]).unwrap();
        let mut c: Combiner<Spy, Spy> = Combiner::with_context(ctx);
        let v = Var::new(0);
        c.register_atom(v, le).unwrap();
        c.assert(Lit::new(v, true));
        assert_eq!(c.arith.asserted, vec![Lit::new(v, true)]);
        assert!(c.euf.asserted.is_empty());
    }

    #[test]
    fn push_pop_track_absolute_levels() {
        let mut c: Combiner<Spy, Spy> = Combiner::default();
        c.push();
        c.push();
        assert_eq!(c.level, 2);
        c.pop(1); // close 1 scope -> target level 1
        assert_eq!(c.level, 1);
        assert_eq!(c.arith.level, 1);
        assert_eq!(c.euf.level, 1);
    }

    #[test]
    fn unsupported_atom_is_refused() {
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let xy = ctx.mk_app(shinri_core::Op::Builtin(shinri_core::BuiltinOp::Mul), &[x, y]).unwrap();
        let z = real_var(&mut ctx, "z");
        let le = ctx.mk_app(shinri_core::Op::Builtin(shinri_core::BuiltinOp::Le), &[xy, z]).unwrap();
        let mut c: Combiner<Spy, Spy> = Combiner::with_context(ctx);
        assert!(c.register_atom(Var::new(0), le).is_err());
    }

    /// Emits one propagation `(p, just)` exactly once, to drive the fixpoint loop.
    #[derive(Default)]
    struct OneShotProp {
        fired: bool,
        p: Option<Lit>,
    }
    impl TheorySolver for OneShotProp {
        const THEORY_ID: u16 = 2;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            out: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            if !self.fired {
                self.fired = true;
                if let Some(p) = self.p {
                    out.push((p, TheoryJust { theory: 2, tag: 0 }));
                }
            }
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _e: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _level: usize) {}
    }

    #[test]
    fn propagate_collects_theory_implications_to_fixpoint() {
        let mut c: Combiner<OneShotProp, OneShotProp> = Combiner::default();
        c.euf.p = Some(Lit::new(Var::new(7), true));
        let mut out = Vec::new();
        assert!(c.propagate(&mut out).is_none());
        assert_eq!(out, vec![(Lit::new(Var::new(7), true), TheoryJust { theory: 2, tag: 0 })]);
    }

    #[test]
    fn assert_conflict_is_stashed_and_surfaced_by_propagate() {
        // A `Le` atom routes to `arith`; make arith the conflicter. The
        // infallible assert stashes the conflict; the next propagate surfaces
        // and drains it; a following propagate is clean.
        let mut ctx = Context::new();
        let x = real_var(&mut ctx, "x");
        let y = real_var(&mut ctx, "y");
        let le = ctx
            .mk_app(Op::Builtin(shinri_core::BuiltinOp::Le), &[x, y])
            .unwrap();
        let mut c: Combiner<Spy, AssertConflicter> = Combiner::with_context(ctx);
        let v = Var::new(0);
        c.register_atom(v, le).unwrap();
        c.assert(Lit::new(v, true));
        let mut out = Vec::new();
        assert!(c.propagate(&mut out).is_some(), "stashed conflict must surface");
        let mut out2 = Vec::new();
        assert!(c.propagate(&mut out2).is_none(), "conflict must be drained");
    }
}
