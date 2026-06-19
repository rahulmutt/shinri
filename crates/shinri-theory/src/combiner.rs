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
    /// Placeholder; populated in Task 10.
    #[allow(dead_code)]
    iface: InterfaceSet,
    euf: E,
    arith: A,
    level: usize,
    /// Populated in Task 9 (propagation).
    #[allow(dead_code)]
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
        let mut cx = TheoryCtx {
            terms: &self.terms,
            eq: &mut self.eq,
            atoms: &self.atoms,
        };
        match owner {
            Owner::Euf => self.euf.new_var(&mut cx, v, atom),
            Owner::Arith => self.arith.new_var(&mut cx, v, atom),
            Owner::Shared => {
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

    fn propagate(&mut self, _out: &mut Vec<(Lit, TheoryJust)>) -> Option<Vec<Lit>> {
        // Task 9 replaces this. For now, surface only an assert-time conflict.
        self.take_pending_conflict()
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
    /// Drain any conflict stashed during `assert`, mapped to a SAT clause.
    /// Real expansion lands in Task 12; here it is a no-leaf placeholder.
    fn take_pending_conflict(&mut self) -> Option<Vec<Lit>> {
        self.pending_conflict.take().map(|_leaves| Vec::new())
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
