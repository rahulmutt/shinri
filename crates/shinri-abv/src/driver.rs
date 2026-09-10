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
    ///
    /// `ctx` is passed so an implementation may blast any word `value_bv`
    /// asked for since the previous solve BEFORE solving. That ordering is
    /// load-bearing: adding a clause to the live SAT solver backtracks it to
    /// level 0 and DESTROYS the model, so a bridge that blasts lazily from
    /// inside `value_bv` would wipe the very model the checks are reading.
    fn solve(&mut self, ctx: &Context) -> bool;
    /// Concrete value of a BV-sorted term in the latest SAT model.
    ///
    /// MUST NOT mutate the solver. `None` means "this model does not give the
    /// term a value" — either it was never blasted, or its bits were allocated
    /// after the model was taken. `functional_consistency` treats `None` as
    /// silence, but ROW-1, ROW-2 and extensionality-positive
    /// (`crates/shinri-abv/src/check.rs:163-164`, `:258`, `:278`) compare
    /// `value_bv(..).map(|x| x.1) != value_bv(..).map(|x| x.1)` directly, so
    /// `Some(v) != None` reads as a mismatch and eagerly emits a lemma there —
    /// sound (the lemma is an entailed array axiom either way), but not
    /// "every check treats `None` as silence". Tightening those three sites
    /// to skip on any `None` (rather than treat it as a forced mismatch) is
    /// queued as a follow-up slice: it changes which lemmas are emitted on
    /// which round and needs a corpus re-measure, not just a doc fix. See
    /// "Queued for the next slice" in
    /// `docs/superpowers/specs/2026-09-09-shinri-slice47-qfabv-wrong-sat-design.md`.
    fn value_bv(&self, ctx: &Context, t: TermId) -> Option<(u32, shinri_num::Integer)>;
    /// True when `value_bv` was asked, since the last solve, for a word the
    /// model could not value. Solving again blasts those words first, so the
    /// next round sees real values where this one saw `None`.
    fn pending_words(&self) -> bool {
        false
    }
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
    /// The loop reached a fixpoint and reported `Sat`, but the post-solve
    /// array-model gate (`crate::validate`) found the model violates an array
    /// axiom, so the `Sat` is spurious. SOUND downgrade to `Unknown` at the
    /// solver boundary — never reported as `sat`.
    ModelRejected,
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
    // Defensive fence on the word-driven rounds below. Each such round is
    // charged to at least one word entering the bridge's blasted set, and that
    // set only grows, so the bound is never reached by a terminating instance;
    // it exists so a bridge that mis-reports `pending_words` degrades to a
    // SOUND `Unknown` instead of spinning.
    const MAX_WORD_ROUNDS: u32 = 10_000;
    let mut word_rounds: u32 = 0;
    loop {
        if !bridge.solve(ctx) {
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

        let round_len = round.len();
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
        if std::env::var_os("SHINRI_ABV_DEBUG").is_some() {
            eprintln!(
                "abv round: emitted={} added_total={} progress={} pending_words={}",
                round_len,
                added.len(),
                progress,
                bridge.pending_words()
            );
        }
        if !progress {
            // A round that emitted no lemma has NOT necessarily examined the
            // model: a check whose index or element word had no value in this
            // model skipped silently (`value_bv` returns `None` rather than
            // fabricating a zero). Solving again blasts those words first, so
            // re-run rather than declaring a fixpoint on a model the checks
            // could not read. Terminating: `pending_words` is only true when a
            // word the bridge has NEVER blasted was queried, and solving blasts
            // it, so each such round consumes at least one word from a finite
            // set.
            if !bridge.pending_words() {
                return AbvOutcome::Sat;
            }
            word_rounds += 1;
            if word_rounds >= MAX_WORD_ROUNDS {
                return AbvOutcome::Unknown;
            }
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
        fn solve(&mut self, _ctx: &Context) -> bool {
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
