//! The per-theory abstraction (spec §5). Sub-theories see only the shared
//! context, never the SAT solver. Conflicts and explanations are expressed in
//! `EqLeaf` antecedents the Combiner expands.

use crate::eq_engine::EqualityEngine;
use crate::model::ModelBuilder;
use crate::types::EqLeaf;
use crate::AtomRegistry;
use crate::Explainer;
use shinri_core::{Context, Lit, TermId, TheoryJust, Var};
use shinri_sat::Effort;

/// The borrowed context threaded into every `TheorySolver` call (spec §5.1).
pub struct TheoryCtx<'a> {
    pub terms: &'a Context,
    pub eq: &'a mut EqualityEngine,
    pub atoms: &'a AtomRegistry,
}

/// A sub-theory consistency verdict. Convex Phase-1 theories produce conflicts,
/// never free-standing lemmas. `Split` is the SINGLE sanctioned exception (QF_LIA
/// Plan A): a clause of theory-valid positive atoms (`TermId`s) the Combiner
/// lifts to `TheoryResult::SplitAtoms`. Only arithmetic emits it; EUF/Empty never do.
pub enum TCheck {
    Sat,
    Conflict(Vec<EqLeaf>),
    Split(Vec<TermId>),
}

/// `pop(level)` uses ABSOLUTE target levels (matching `EqualityEngine`/`UndoLog`).
/// The Combiner translates the SAT seam's "close n scopes" into a target once.
pub trait TheorySolver: Default {
    const THEORY_ID: u16;

    fn new_var(&mut self, cx: &mut TheoryCtx, v: Var, atom: TermId);
    fn assert(&mut self, cx: &mut TheoryCtx, lit: Lit) -> Option<Vec<EqLeaf>>;
    fn propagate(
        &mut self,
        cx: &mut TheoryCtx,
        out: &mut Vec<(Lit, TheoryJust)>,
    ) -> Option<Vec<EqLeaf>>;
    fn check(&mut self, cx: &mut TheoryCtx, effort: Effort) -> TCheck;
    fn explain(&mut self, cx: &mut TheoryCtx, tag: u32, exp: &mut Explainer);
    fn model(&mut self, cx: &mut TheoryCtx, m: &mut ModelBuilder);
    fn push(&mut self);
    fn pop(&mut self, level: usize);

    // ----- Nelson-Oppen equality-exchange seam (Task 12b) -------------------
    // Default no-op implementations so a theory that does not participate in a
    // given direction (or the unit-test stubs) need not implement them.

    /// The set of shared Real-sorted TermIds this theory reasons about. EUF
    /// returns its registered Real terms; arith returns none (the combiner
    /// drives the set FROM the EUF side). Used to compute the N-O shared set S.
    fn shared_real_terms(&self, _cx: &mut TheoryCtx) -> Vec<TermId> {
        Vec::new()
    }

    /// Ensure this theory has a variable for the shared Real term `t` (arith
    /// interns a problem var; numerals get an unconditional fixed bound). Called
    /// for every term in S BEFORE the arith check that reads entailed equalities.
    fn ensure_shared_var(&mut self, _cx: &mut TheoryCtx, _t: TermId) {}

    /// Right after a Sat Full check: the equalities this theory ENTAILS among
    /// `shared`, each with an explanation tag resolvable via `explain`. Leaves
    /// this theory's state UNPERTURBED. (Arith implements; EUF returns none.)
    fn entailed_equalities(
        &mut self,
        _cx: &mut TheoryCtx,
        _shared: &[TermId],
    ) -> Vec<(TermId, TermId, u32)> {
        Vec::new()
    }

    /// Install `a = b` (derived by ANOTHER theory) into this theory and close
    /// its own reasoning. EUF merges the e-nodes and closes congruence; arith
    /// installs fixed bounds. Returns conflict leaves if it makes this theory
    /// infeasible. `just` lets a resulting conflict be explained back.
    fn consume_interface_equality(
        &mut self,
        _cx: &mut TheoryCtx,
        _a: TermId,
        _b: TermId,
        _just: TheoryJust,
    ) -> Option<Vec<EqLeaf>> {
        None
    }

    /// Mint an explanation tag (resolvable via THIS theory's `explain`) for a
    /// pair `(a, b)` this theory has made equal — so when the OTHER theory cites
    /// the resulting interface equality in a conflict, it resolves back to this
    /// theory's input-literal antecedents. EUF mints from its proof forest;
    /// arith does not export EUF-derived equalities so the default is unused.
    fn mint_eq_tag(&mut self, _cx: &mut TheoryCtx, _a: TermId, _b: TermId) -> u32 {
        0
    }

    /// Intern every Real-sorted UF-application subterm of an ARITH atom `atom`
    /// into THIS theory so congruence applies and they join the shared set S
    /// (CRITICAL-2). A UF-app used directly inside a linear arith term (e.g.
    /// `(- (f x0) (f x1))`) is otherwise opaque to EUF, so the EUF-derived
    /// equality between the f-apps never reaches arith (and dually). Recursive
    /// over nesting so `f(g(x))` interns `g(x)` and `f(g(x))` both. EUF
    /// implements; arith (and stubs) default to a no-op.
    fn register_arith_uf_terms(&mut self, _cx: &mut TheoryCtx, _atom: TermId) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A do-nothing theory: proves the trait is implementable and object-safe
    /// in the monomorphized sense (used as a Combiner stub in later tasks).
    #[derive(Default)]
    struct NullTheory;

    impl TheorySolver for NullTheory {
        const THEORY_ID: u16 = 99;
        fn new_var(&mut self, _cx: &mut TheoryCtx, _v: Var, _atom: TermId) {}
        fn assert(&mut self, _cx: &mut TheoryCtx, _lit: Lit) -> Option<Vec<EqLeaf>> {
            None
        }
        fn propagate(
            &mut self,
            _cx: &mut TheoryCtx,
            _out: &mut Vec<(Lit, TheoryJust)>,
        ) -> Option<Vec<EqLeaf>> {
            None
        }
        fn check(&mut self, _cx: &mut TheoryCtx, _effort: Effort) -> TCheck {
            TCheck::Sat
        }
        fn explain(&mut self, _cx: &mut TheoryCtx, _tag: u32, _exp: &mut Explainer) {}
        fn model(&mut self, _cx: &mut TheoryCtx, _m: &mut ModelBuilder) {}
        fn push(&mut self) {}
        fn pop(&mut self, _level: usize) {}
    }

    #[test]
    fn null_theory_checks_sat() {
        let mut t = NullTheory;
        let terms = Context::new();
        let mut eq = EqualityEngine::default();
        let atoms = AtomRegistry::default();
        let mut cx = TheoryCtx {
            terms: &terms,
            eq: &mut eq,
            atoms: &atoms,
        };
        assert!(matches!(t.check(&mut cx, Effort::Full), TCheck::Sat));
    }

    #[test]
    fn tcheck_split_carries_atoms() {
        let t = shinri_core::TermId::new(5).unwrap();
        let c = TCheck::Split(vec![t]);
        match c {
            TCheck::Split(atoms) => assert_eq!(atoms, vec![t]),
            _ => panic!("expected Split"),
        }
    }
}
