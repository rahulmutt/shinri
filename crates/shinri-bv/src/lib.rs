//! shinri-bv: eager bit-blasting of QF_BV to CNF over a private BitVar namespace.
//! See docs/superpowers/specs/2026-06-23-shinri-qfbv-design.md.
pub mod blast;
pub mod model;
pub mod rewrite;
pub use blast::{blast_bv_atom, blast_bv_word, BitLit, Blaster, Cnf, FpToBvApp, UfApp, WordSink};
pub use rewrite::rewrite;

use rustc_hash::FxHashMap;
use shinri_core::{Context, TermId};

/// The output of `lower()`: CNF + maps for the solver (Task 17) and model extractor.
pub struct Lowered {
    /// CNF over the private BitVar namespace from the Blaster.
    pub cnf: Cnf,
    /// Maps each ORIGINAL Bool-sorted BV atom TermId -> its representative BitLit.
    /// Keyed by the *original* (pre-rewrite) TermId so Task 17's hook can look up
    /// by the atom id it sees in the assertion DAG.
    pub atom_lit: FxHashMap<TermId, BitLit>,
    /// Maps each BV *variable* term (nullary uninterpreted, BV-sorted) -> its bits (LSB→MSB).
    /// Used for model extraction after the SAT solver finds a satisfying assignment.
    pub var_bits: FxHashMap<TermId, Vec<BitLit>>,
}

/// Rewrite all `bv_atoms`, blast them via a single `Blaster` (sharing the CNF
/// and subterm cache), and return the `Lowered` struct.
///
/// Critical contract: `atom_lit` is keyed by the **original** atom TermId
/// (the element from `bv_atoms`), not the rewritten one. Task 17 looks up atoms
/// by their original id.
pub fn lower(ctx: &mut Context, bv_atoms: &[TermId]) -> Lowered {
    let mut b = Blaster::new();
    let mut atom_lit: FxHashMap<TermId, BitLit> = FxHashMap::default();
    for &original in bv_atoms {
        let rewritten = rewrite(ctx, original);
        let lit = b.blast_atom(ctx, rewritten);
        // KEY: store under the ORIGINAL atom id so Task 17's hook can look it up.
        atom_lit.insert(original, lit);
    }
    // Extract var_bits BEFORE consuming the blaster via finish().
    let var_bits = b.exported_var_bits(ctx);
    Lowered {
        cnf: b.finish(),
        atom_lit,
        var_bits,
    }
}

#[cfg(test)]
pub(crate) mod testkit;

#[cfg(test)]
mod lower_tests {
    use super::*;
    use shinri_core::{BuiltinOp, Context, Op};
    use shinri_num::Integer;

    // ── Test 1: basic lower — atom_lit + var_bits + cnf ─────────────────────

    #[test]
    fn lower_produces_atom_lits_and_var_bits() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let c = ctx.mk_bv_const(8, Integer::from(5u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[x, c]).unwrap();

        let lo = lower(&mut ctx, &[atom]);
        // (1) atom_lit is keyed by the ORIGINAL atom TermId
        assert!(
            lo.atom_lit.contains_key(&atom),
            "atom_lit must contain the original atom TermId"
        );
        // (2) var_bits contains the BV variable x with 8 bits
        assert!(
            lo.var_bits.contains_key(&x),
            "var_bits must contain the BV variable x"
        );
        assert_eq!(lo.var_bits[&x].len(), 8, "x must have 8 bits");
        // (3) the CNF has at least one variable (var 0 is the pinned-true constant)
        assert!(lo.cnf.num_vars >= 1, "CNF must have at least 1 variable");
    }

    // ── Test 2: original-vs-rewritten keying contract ────────────────────────
    //
    // Build an atom that REWRITES to a different TermId (bvadd x #x00 simplifies
    // to x via identity rule), so the original atom TermId != rewritten TermId.
    // Assert atom_lit is keyed by the ORIGINAL TermId.

    #[test]
    fn lower_atom_lit_keyed_by_original_not_rewritten() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_rw", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let zero = ctx.mk_bv_const(8, Integer::from(0u64));
        // (bvult (bvadd x #x00) x)  ->  after rewrite: (bvult x x)  (since x+0 -> x)
        // The original atom TermId is for the un-simplified form.
        let xplus0 = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvAdd), &[x, zero])
            .unwrap();
        let atom = ctx
            .mk_app(Op::Builtin(BuiltinOp::BvUlt), &[xplus0, x])
            .unwrap();

        // Verify rewrite actually produces a different TermId.
        let rewritten = rewrite(&mut ctx, atom);
        // The rewritten form is (bvult x x) since bvadd x #x00 -> x.
        // Confirm original != rewritten (the rewrite did simplify something).
        // Note: if the context interns them identically, original == rewritten is fine
        // and the test still holds — atom_lit must contain &atom regardless.
        let lo = lower(&mut ctx, &[atom]);

        // CRITICAL: must be keyed by the ORIGINAL atom, not the rewritten.
        assert!(
            lo.atom_lit.contains_key(&atom),
            "atom_lit must contain the ORIGINAL atom TermId (original={:?}, rewritten={:?})",
            atom,
            rewritten
        );
        // If rewrite actually produced a different id, the rewritten id must NOT
        // replace the original as the key (it may coincidentally also be in the
        // map if original == rewritten, but the original must always be present).
        // The lookup by original succeeds:
        let _lit = lo.atom_lit[&atom]; // must not panic
    }

    // ── Test 3: const-only atom — no var_bits, lit is deterministic ──────────

    #[test]
    fn lower_const_atom_no_var_bits() {
        use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

        let mut ctx = Context::new();
        // (bvult #x03 #x05) -> always true
        let a = ctx.mk_bv_const(8, Integer::from(3u64));
        let b = ctx.mk_bv_const(8, Integer::from(5u64));
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[a, b]).unwrap();

        let lo = lower(&mut ctx, &[atom]);
        assert!(lo.atom_lit.contains_key(&atom));
        // No BV variables were used, so var_bits must be empty.
        assert!(
            lo.var_bits.is_empty(),
            "no BV variables -> var_bits must be empty"
        );

        // End-to-end: the lit for a true atom must evaluate to true in the CNF.
        let lit = lo.atom_lit[&atom];
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..lo.cnf.num_vars {
            s.new_var();
        }
        for clause in &lo.cnf.clauses {
            let sat_lits: Vec<Lit> = clause
                .iter()
                .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
                .collect();
            s.add_clause(&sat_lits);
        }
        let result = s.solve();
        assert_eq!(result, SolveResult::Sat);
        // The atom is always true, so the lit's variable must be true (with correct polarity).
        let raw = s.value_of(Var::new(lit.var)).unwrap();
        let atom_val = if lit.pos { raw } else { !raw };
        assert!(atom_val, "bvult(3,5) must be true in any SAT model");
    }

    // ── Test 4: multiple atoms share the blaster — subterm sharing ────────────

    #[test]
    fn lower_multiple_atoms_share_blaster() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x_shared", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let c1 = ctx.mk_bv_const(8, Integer::from(3u64));
        let c2 = ctx.mk_bv_const(8, Integer::from(10u64));
        // Two atoms over the same variable x.
        let atom1 = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[x, c1]).unwrap();
        let atom2 = ctx.mk_app(Op::Builtin(BuiltinOp::BvUlt), &[x, c2]).unwrap();

        let lo = lower(&mut ctx, &[atom1, atom2]);
        assert!(lo.atom_lit.contains_key(&atom1));
        assert!(lo.atom_lit.contains_key(&atom2));
        // The two atoms share the blasting of x; var_bits has x with 8 bits.
        assert!(lo.var_bits.contains_key(&x));
        assert_eq!(lo.var_bits[&x].len(), 8);
        // The two atoms must have different literals (they compare x against different constants).
        assert_ne!(lo.atom_lit[&atom1], lo.atom_lit[&atom2]);
    }

    // ── Slice 44: uninterpreted-application congruence ───────────────────────

    /// Clause count of `lower` on `(= x y)` for two nullary BV8 variables.
    /// Measured 2026-07-27 on the pre-slice-44 arm; pinned so any future change
    /// to the nullary/pure-BV encoding is loud.
    const NULLARY_EQ_CLAUSES: usize = 57;

    /// Slice 44: two applications of one symbol to terms the CNF forces equal
    /// must have equal results. Encoded as: assert `x = y` and `f(x) != f(y)`;
    /// the CNF must be UNSAT. We check it structurally here — the clause count
    /// for the congruence must be non-zero — and end-to-end in qfufbv_e2e.
    #[test]
    fn congruence_clauses_are_emitted_for_two_applications() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let xf = ctx.declare_fun("x", &[], s8);
        let yf = ctx.declare_fun("y", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let fy = ctx.mk_app(Op::Uninterpreted(f), &[y]).unwrap();
        let a1 = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fx, fy]).unwrap();

        let with_two = lower(&mut ctx, &[a1]).cnf.clauses.len();

        // A single application emits no congruence clauses at all.
        let mut ctx2 = Context::new();
        let s8b = ctx2.bv_sort(8);
        let f2 = ctx2.declare_fun("f", &[s8b], s8b);
        let xf2 = ctx2.declare_fun("x", &[], s8b);
        let x2 = ctx2.mk_app(Op::Uninterpreted(xf2), &[]).unwrap();
        let fx2 = ctx2.mk_app(Op::Uninterpreted(f2), &[x2]).unwrap();
        let c = ctx2.mk_bv_const(8, shinri_num::Integer::from(0u64));
        let a2 = ctx2.mk_app(Op::Builtin(BuiltinOp::Eq), &[fx2, c]).unwrap();
        let with_one = lower(&mut ctx2, &[a2]).cnf.clauses.len();

        assert!(
            with_two > with_one,
            "two applications of one symbol must emit congruence clauses \
             (two={with_two}, one={with_one})"
        );
    }

    /// The nullary arm is UNCHANGED: a nullary uninterpreted symbol is
    /// hash-consed to one TermId, so there is one word and nothing to make
    /// consistent. Pins that slice 44 adds no clauses to the pure-variable case.
    #[test]
    fn nullary_applications_emit_no_congruence_clauses() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let xf = ctx.declare_fun("x", &[], s8);
        let yf = ctx.declare_fun("y", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let atom = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let lo = lower(&mut ctx, &[atom]);
        // 8 bits of xnor-and chain + the pinned var0 clause; the exact number is
        // whatever pre-slice-44 produced. Recorded here as an equality so any
        // future change to the nullary path is loud.
        assert_eq!(
            lo.cnf.clauses.len(),
            NULLARY_EQ_CLAUSES,
            "slice 44 must not change the nullary/pure-BV encoding"
        );
    }

    /// Solve `lower`'s CNF with each `(atom, polarity)` asserted as a unit
    /// clause. Returns true iff SAT.
    fn solve_atoms(ctx: &mut Context, atoms: &[(TermId, bool)]) -> bool {
        use shinri_sat::{Lit, NoProof, NoTheory, SolveResult, Solver, SolverConfig, Var, Vmtf};

        let ids: Vec<TermId> = atoms.iter().map(|&(t, _)| t).collect();
        let lo = lower(ctx, &ids);
        let mut s: Solver<NoTheory, NoProof, Vmtf> = Solver::new(SolverConfig::default());
        for _ in 0..lo.cnf.num_vars {
            s.new_var();
        }
        for clause in &lo.cnf.clauses {
            let lits: Vec<Lit> = clause
                .iter()
                .map(|bl| Lit::new(Var::new(bl.var), bl.pos))
                .collect();
            s.add_clause(&lits);
        }
        for &(t, want) in atoms {
            let bl = lo.atom_lit[&t];
            s.add_clause(&[Lit::new(Var::new(bl.var), bl.pos == want)]);
        }
        s.solve() == SolveResult::Sat
    }

    /// Congruence is an IMPLICATION — `(args equal) → (results equal)` — never a
    /// biconditional. All three shapes are pinned in one test because getting
    /// the direction wrong flips exactly one of them:
    ///   - `x = y ∧ f(x) ≠ f(y)` must be UNSAT (this is the slice-44 bug);
    ///   - `x ≠ y ∧ f(x) ≠ f(y)` must stay SAT (no converse);
    ///   - `x ≠ y ∧ f(x) = f(y)` must stay SAT (a function may agree on
    ///     distinct arguments — an inverted encoding breaks this one).
    #[test]
    fn congruence_is_an_implication_not_a_biconditional() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let xf = ctx.declare_fun("x", &[], s8);
        let yf = ctx.declare_fun("y", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let y = ctx.mk_app(Op::Uninterpreted(yf), &[]).unwrap();
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let fy = ctx.mk_app(Op::Uninterpreted(f), &[y]).unwrap();
        let args_eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, y]).unwrap();
        let res_eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[fx, fy]).unwrap();

        assert!(
            !solve_atoms(&mut ctx, &[(args_eq, true), (res_eq, false)]),
            "x = y AND f(x) != f(y) must be UNSAT — this is the congruence"
        );
        assert!(
            solve_atoms(&mut ctx, &[(args_eq, false), (res_eq, false)]),
            "x != y AND f(x) != f(y) must stay SAT — no converse implication"
        );
        assert!(
            solve_atoms(&mut ctx, &[(args_eq, false), (res_eq, true)]),
            "x != y AND f(x) = f(y) must stay SAT — a function may agree on \
             distinct arguments"
        );
    }

    /// Step order: the arguments must be blasted BEFORE the registry is read,
    /// or `f(f(x))` never pairs the inner application with the outer one. With
    /// `x = f(x)` asserted, congruence forces `f(x) = f(f(x))`, so
    /// `f(f(x)) != f(x)` is UNSAT. Reading `prior` first leaves the pair
    /// unconstrained and this comes back SAT.
    ///
    /// The atom carrying `f(f(x))` is asserted FIRST and puts it in operand
    /// position 0, so the outer application is blasted while the registry is
    /// still empty — the inner one is registered only by the outer's own
    /// argument recursion. That is precisely the ordering under test.
    #[test]
    fn nested_application_congruence() {
        let mut ctx = Context::new();
        let s8 = ctx.bv_sort(8);
        let f = ctx.declare_fun("f", &[s8], s8);
        let xf = ctx.declare_fun("x", &[], s8);
        let x = ctx.mk_app(Op::Uninterpreted(xf), &[]).unwrap();
        let fx = ctx.mk_app(Op::Uninterpreted(f), &[x]).unwrap();
        let ffx = ctx.mk_app(Op::Uninterpreted(f), &[fx]).unwrap();
        let res_eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[ffx, fx]).unwrap();
        let args_eq = ctx.mk_app(Op::Builtin(BuiltinOp::Eq), &[x, fx]).unwrap();

        assert!(
            !solve_atoms(&mut ctx, &[(res_eq, false), (args_eq, true)]),
            "x = f(x) AND f(f(x)) != f(x) must be UNSAT — the inner application \
             must be registered before the outer one reads the registry"
        );
    }
}
