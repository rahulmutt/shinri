//! Refinement controller + the SatBridge seam.
use rustc_hash::{FxHashMap, FxHashSet};
use shinri_core::{BuiltinOp, Context, Op, TermId, TermNode};

use crate::abstraction::Abstraction;
use crate::collect::Collected;

/// A BV (dis)equality literal in a lemma: (atom term, polarity).
/// `atom` is a Bool-sorted BV equality `(= u v)` over read vars / indices /
/// elements, or an array-eq proxy. `pos=false` means the negation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LemmaLit {
    pub atom: TermId,
    pub pos: bool,
}

/// A learned clause: the disjunction of its lits.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Lemma(pub Vec<LemmaLit>);

/// What the controller needs from the SAT/blast layer. Implemented for real by
/// shinri-solver (Task 10) and by a fake in tests.
pub trait SatBridge {
    /// Solve the current clause set. Returns true on SAT.
    fn solve(&mut self) -> bool;
    /// Concrete value of a BV-sorted term in the latest SAT model.
    fn value_bv(&self, ctx: &Context, t: TermId) -> Option<(u32, shinri_num::Integer)>;
    /// Truth of an array-eq proxy term in the latest SAT model.
    fn value_bool(&self, t: TermId) -> Option<bool>;
    /// Ensure `atom` (a Bool-sorted BV (dis)equality) is blasted into the live
    /// solver, returning nothing; idempotent. Mints clauses for any new reads.
    fn ensure_atom(&mut self, ctx: &mut Context, atom: TermId);
    /// Add one lemma clause over already-ensured atoms.
    fn add_lemma(&mut self, ctx: &mut Context, lemma: &Lemma);
}

/// Outcome of the abstraction-refinement loop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AbvOutcome {
    Sat,
    Unsat,
    Unknown,
}

/// Run the abstraction–refinement loop. `bridge` already holds the blasted
/// abstraction (Task 10 sets it up). The controller re-solves, checks the
/// model, and feeds lemmas back until convergence.
pub fn refine<B: SatBridge>(
    ctx: &mut Context,
    abs: &mut Abstraction,
    c: &mut Collected,
    bridge: &mut B,
) -> AbvOutcome {
    let mut added: FxHashSet<Lemma> = FxHashSet::default();
    let mut witnesses: FxHashMap<TermId, TermId> = FxHashMap::default();
    loop {
        if !bridge.solve() {
            return AbvOutcome::Unsat;
        }

        let mut round: Vec<Lemma> = Vec::new();
        round.extend(crate::check::functional_consistency(ctx, abs, c, bridge));
        round.extend(crate::check::read_over_write(ctx, abs, c, bridge));
        round.extend(crate::check::extensionality(
            ctx,
            abs,
            c,
            bridge,
            &mut witnesses,
        ));

        // Register any selects minted this round (recorded in abs.read_of) into c.
        sync_new_selects(ctx, abs, c);

        let mut progress = false;
        for lemma in round {
            if added.insert(lemma.clone()) {
                for lit in &lemma.0 {
                    bridge.ensure_atom(ctx, lit.atom);
                }
                bridge.add_lemma(ctx, &lemma);
                progress = true;
            }
        }
        if !progress {
            return AbvOutcome::Sat;
        }
    }
}

/// Append selects present in `abs.read_of` but not yet in `c.selects`.
fn sync_new_selects(ctx: &Context, abs: &Abstraction, c: &mut Collected) {
    let existing: FxHashSet<TermId> = c.selects.iter().copied().collect();
    for &sel in abs.read_of.keys() {
        if !existing.contains(&sel)
            && matches!(
                ctx.term_node(sel),
                TermNode::App {
                    op: Op::Builtin(BuiltinOp::Select),
                    ..
                }
            )
        {
            c.selects.push(sel);
        }
    }
}

#[cfg(test)]
mod loop_tests {
    use super::fake::FakeBridge;
    use super::*;
    use crate::abstraction::abstract_arrays;
    use crate::collect::collect;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

    #[test]
    fn converges_to_unsat_when_congruence_forces_contradiction() {
        let mut ctx = Context::new();
        let arr_s = {
            let i = ctx.bv_sort(8);
            let e = ctx.bv_sort(8);
            ctx.array_sort(i, e)
        };
        let s8 = ctx.bv_sort(8);
        let mk = |ctx: &mut Context, n: &str, s| {
            let f = ctx.declare_fun(n, &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let a = mk(&mut ctx, "a", arr_s);
        let i = mk(&mut ctx, "i", s8);
        let j = mk(&mut ctx, "j", s8);
        let s1 = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let s2 = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, j]).unwrap();
        let atom = ctx.mk_eq(s1, s2).unwrap(); // placeholder assertion
        let mut c = collect(&ctx, &[atom]);
        let mut abs = abstract_arrays(&mut ctx, &[atom], &c);
        let (r1, r2) = (abs.read_of[&s1], abs.read_of[&s2]);

        // Fake: i==j, r1!=r2 → congruence fires; flip to UNSAT after 1 lemma.
        let mut fake = FakeBridge::default();
        fake.bv.insert(i, (8, Integer::from(5u64)));
        fake.bv.insert(j, (8, Integer::from(5u64)));
        fake.bv.insert(r1, (8, Integer::from(1u64)));
        fake.bv.insert(r2, (8, Integer::from(2u64)));
        fake.unsat_after = Some(1);

        let out = refine(&mut ctx, &mut abs, &mut c, &mut fake);
        assert_eq!(out, AbvOutcome::Unsat);
        assert_eq!(fake.added.len(), 1, "exactly the congruence lemma");
    }

    #[test]
    fn consistent_model_returns_sat_without_lemmas() {
        let mut ctx = Context::new();
        let arr_s = {
            let i = ctx.bv_sort(8);
            let e = ctx.bv_sort(8);
            ctx.array_sort(i, e)
        };
        let s8 = ctx.bv_sort(8);
        let mk = |ctx: &mut Context, n: &str, s| {
            let f = ctx.declare_fun(n, &[], s);
            ctx.mk_app(Op::Uninterpreted(f), &[]).unwrap()
        };
        let a = mk(&mut ctx, "a", arr_s);
        let i = mk(&mut ctx, "i", s8);
        let s1 = ctx.mk_app(Op::Builtin(BuiltinOp::Select), &[a, i]).unwrap();
        let atom = ctx.mk_eq(s1, s1).unwrap();
        let mut c = collect(&ctx, &[atom]);
        let mut abs = abstract_arrays(&mut ctx, &[atom], &c);
        let mut fake = FakeBridge::default();
        fake.bv.insert(i, (8, Integer::from(0u64)));
        fake.bv.insert(abs.read_of[&s1], (8, Integer::from(0u64)));
        let out = refine(&mut ctx, &mut abs, &mut c, &mut fake);
        assert_eq!(out, AbvOutcome::Sat);
        assert!(fake.added.is_empty());
    }
}

#[cfg(test)]
pub(crate) mod fake {
    use super::*;
    use rustc_hash::FxHashMap;
    use shinri_num::Integer;

    /// A scripted bridge: returns a fixed model, records lemmas, and (optionally)
    /// flips to a different model / UNSAT after N lemmas are added (to simulate
    /// refinement convergence).
    #[derive(Default)]
    pub struct FakeBridge {
        pub bv: FxHashMap<TermId, (u32, Integer)>,
        pub boolv: FxHashMap<TermId, bool>,
        pub added: Vec<Lemma>,
        pub ensured: Vec<TermId>,
        /// Become UNSAT once `added.len()` reaches this (None = always SAT).
        pub unsat_after: Option<usize>,
    }
    impl SatBridge for FakeBridge {
        fn solve(&mut self) -> bool {
            match self.unsat_after {
                Some(n) => self.added.len() < n,
                None => true,
            }
        }
        fn value_bv(&self, _ctx: &Context, t: TermId) -> Option<(u32, Integer)> {
            self.bv.get(&t).cloned()
        }
        fn value_bool(&self, t: TermId) -> Option<bool> {
            self.boolv.get(&t).copied()
        }
        fn ensure_atom(&mut self, _ctx: &mut Context, atom: TermId) {
            self.ensured.push(atom);
        }
        fn add_lemma(&mut self, _ctx: &mut Context, lemma: &Lemma) {
            self.added.push(lemma.clone());
        }
    }
}
