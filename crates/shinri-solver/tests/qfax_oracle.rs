//! Differential oracle: shinri-solver vs z3 on random QF_AX instances.
//!
//! Run with:
//!   export PATH="$PATH:/home/dev/.local/share/mise/installs/github-z3-prover-z3/z3-4.16.0/bin"
//!   cargo test -p shinri-solver --features oracle --test qfax_oracle -- --nocapture
//!
//! Requires `z3` on PATH at runtime. Guarded by `#[cfg(feature = "oracle")]` at
//! the crate level, matching the existing `tests/oracle.rs` convention.
#![cfg(feature = "oracle")]

use shinri_core::{BuiltinOp, Op};
use shinri_solver::{SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand.
/// Copied verbatim from tests/oracle.rs to match the existing convention.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0 >> 16
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Step 1: Differential oracle — random QF_AX instances vs z3
//
// Each instance is structured as:
//   - 1 "store witness": (select (store A i_s e_s) i_q) — exercises ROW-1/ROW-2
//   - 0-3 "plain select" atoms: (= (select A i) e) or (distinct ...)
//   - 0-2 index (dis)equalities: (= i_p i_q) / (distinct i_p i_q)
//
// Using at most ONE store per instance bounds the ROW-split tree depth,
// keeping each shinri call tractable. We still exercise the ROW-1 and
// ROW-2 axioms through the store witness atom.
//
// NEVER generates array-sorted equalities (= a b) — those are the fence,
// tested in Step 2.
//
// Compares verdicts with TEETH: (Sat,Unsat) and (Unsat,Sat) PANIC.
// Our Unknown is never a failure (fence might fire on mixed instances,
// though this generator avoids the fence).
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn differential_qf_ax_small() {
    let mut rng = Lcg(0x4A_7B_C3_D1);

    // Pool sizes: 2 arrays, 4 index constants, 4 element constants.
    const N_ARRAYS: usize = 2;
    const N_IDX: usize = 4;
    const N_ELT: usize = 4;
    const N_ITERS: usize = 200;

    let mut n_sat = 0usize;
    let mut n_unsat = 0usize;
    let mut n_unknown = 0usize;

    for iter in 0..N_ITERS {
        // ── shinri setup ────────────────────────────────────────────────────
        let mut s = Solver::new();
        let i_sort = s.declare_sort("I");
        let e_sort = s.declare_sort("E");
        let arr_sort = s.array_sort(i_sort, e_sort);

        let arrays: Vec<_> = (0..N_ARRAYS)
            .map(|k| s.declare_const(&format!("a{k}"), arr_sort))
            .collect();
        let idxs: Vec<_> = (0..N_IDX)
            .map(|k| s.declare_const(&format!("i{k}"), i_sort))
            .collect();
        let elts: Vec<_> = (0..N_ELT)
            .map(|k| s.declare_const(&format!("e{k}"), e_sort))
            .collect();

        // ── z3 setup (easy-smt) ─────────────────────────────────────────────
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .unwrap();
        ctx.set_logic("QF_AX").unwrap();

        // Declare sorts I, E and array sort (Array I E).
        let zi = ctx.declare_sort("I", 0).unwrap();
        let ze = ctx.declare_sort("E", 0).unwrap();
        let zarr = ctx.list(vec![ctx.atom("Array"), zi, ze]);

        let z_arrays: Vec<_> = (0..N_ARRAYS)
            .map(|k| ctx.declare_const(format!("a{k}"), zarr).unwrap())
            .collect();
        let z_idxs: Vec<_> = (0..N_IDX)
            .map(|k| ctx.declare_const(format!("i{k}"), zi).unwrap())
            .collect();
        let z_elts: Vec<_> = (0..N_ELT)
            .map(|k| ctx.declare_const(format!("e{k}"), ze).unwrap())
            .collect();

        // Build dump string for debuggability on disagreement.
        let mut dump = format!(
            "iter={iter}\n(set-logic QF_AX)\n\
             (declare-sort I 0)\n(declare-sort E 0)"
        );
        for k in 0..N_ARRAYS {
            dump.push_str(&format!("\n(declare-const a{k} (Array I E))"));
        }
        for k in 0..N_IDX {
            dump.push_str(&format!("\n(declare-const i{k} I)"));
        }
        for k in 0..N_ELT {
            dump.push_str(&format!("\n(declare-const e{k} E)"));
        }

        // ── Atom 0: ONE store-select witness (exercises ROW-1 / ROW-2) ─────
        // (= (select (store a{ai} i{si} e{se}) i{qi}) e{ce})
        // or (distinct ...) depending on rng.
        {
            let ai = rng.below(N_ARRAYS as u64) as usize;
            let si = rng.below(N_IDX as u64) as usize;
            let se = rng.below(N_ELT as u64) as usize;
            let qi = rng.below(N_IDX as u64) as usize;
            let ce = rng.below(N_ELT as u64) as usize;
            let neg = rng.below(2) == 1;

            // shinri: (store a{ai} i{si} e{se})
            let st = s.app(
                Op::Builtin(BuiltinOp::Store),
                &[arrays[ai], idxs[si], elts[se]],
            );
            // (select (store ...) i{qi})
            let sel = s.app(Op::Builtin(BuiltinOp::Select), &[st, idxs[qi]]);

            // z3: (store ...) and (select (store ...) ...)
            let z_st = ctx.list(vec![
                ctx.atom("store"),
                z_arrays[ai],
                z_idxs[si],
                z_elts[se],
            ]);
            let z_sel = ctx.list(vec![ctx.atom("select"), z_st, z_idxs[qi]]);

            if neg {
                let atom = s.app(Op::Builtin(BuiltinOp::Distinct), &[sel, elts[ce]]);
                s.assert(atom);
                let z_atom = ctx.not(ctx.eq(z_sel, z_elts[ce]));
                ctx.assert(z_atom).unwrap();
                dump.push_str(&format!(
                    "\n(assert (distinct (select (store a{ai} i{si} e{se}) i{qi}) e{ce}))"
                ));
            } else {
                let atom = s.eq(sel, elts[ce]);
                s.assert(atom);
                let z_atom = ctx.eq(z_sel, z_elts[ce]);
                ctx.assert(z_atom).unwrap();
                dump.push_str(&format!(
                    "\n(assert (= (select (store a{ai} i{si} e{se}) i{qi}) e{ce}))"
                ));
            }
        }

        // ── Atoms 1..=3: plain select atoms (no store) ──────────────────────
        let n_plain = 1 + rng.below(3) as usize; // 1..=3 additional atoms
        for _ in 0..n_plain {
            let kind = rng.below(4); // 0=SelectEq, 1=SelectDistinct, 2=IndexEq, 3=IndexDistinct
            match kind {
                0 | 1 => {
                    // (= (select a{ai} i{ii}) e{ei}) or (distinct ...)
                    let ai = rng.below(N_ARRAYS as u64) as usize;
                    let ii = rng.below(N_IDX as u64) as usize;
                    let ei = rng.below(N_ELT as u64) as usize;

                    let sel = s.app(Op::Builtin(BuiltinOp::Select), &[arrays[ai], idxs[ii]]);
                    let z_sel = ctx.list(vec![ctx.atom("select"), z_arrays[ai], z_idxs[ii]]);

                    if kind == 0 {
                        let atom = s.eq(sel, elts[ei]);
                        s.assert(atom);
                        let z_atom = ctx.eq(z_sel, z_elts[ei]);
                        ctx.assert(z_atom).unwrap();
                        dump.push_str(&format!("\n(assert (= (select a{ai} i{ii}) e{ei}))"));
                    } else {
                        let atom = s.app(Op::Builtin(BuiltinOp::Distinct), &[sel, elts[ei]]);
                        s.assert(atom);
                        let z_atom = ctx.not(ctx.eq(z_sel, z_elts[ei]));
                        ctx.assert(z_atom).unwrap();
                        dump.push_str(&format!(
                            "\n(assert (distinct (select a{ai} i{ii}) e{ei}))"
                        ));
                    }
                }
                2 => {
                    // (= i{p} i{q})
                    let p = rng.below(N_IDX as u64) as usize;
                    let q = rng.below(N_IDX as u64) as usize;
                    let atom = s.eq(idxs[p], idxs[q]);
                    s.assert(atom);
                    let z_atom = ctx.eq(z_idxs[p], z_idxs[q]);
                    ctx.assert(z_atom).unwrap();
                    dump.push_str(&format!("\n(assert (= i{p} i{q}))"));
                }
                _ => {
                    // (distinct i{p} i{q})
                    let p = rng.below(N_IDX as u64) as usize;
                    let q = rng.below(N_IDX as u64) as usize;
                    let atom = s.app(Op::Builtin(BuiltinOp::Distinct), &[idxs[p], idxs[q]]);
                    s.assert(atom);
                    let z_atom = ctx.not(ctx.eq(z_idxs[p], z_idxs[q]));
                    ctx.assert(z_atom).unwrap();
                    dump.push_str(&format!("\n(assert (distinct i{p} i{q}))"));
                }
            }
        }

        dump.push_str("\n(check-sat)");

        let ours = s.check_sat();
        let theirs = ctx.check().unwrap();

        match (ours, theirs) {
            (SolveOutcome::Unknown, _) => {
                // Our Unknown is never a failure — fence may fire.
                n_unknown += 1;
            }
            (SolveOutcome::Sat, easy_smt::Response::Sat) => {
                n_sat += 1;
            }
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {
                n_unsat += 1;
            }
            (o, t) => {
                panic!(
                    "QF_AX SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                     Reproduce with this instance:\n{dump}"
                );
            }
        }
    }

    println!(
        "differential_qf_ax_small: {N_ITERS} instances checked, 0 disagreements\n  \
         sat={n_sat} unsat={n_unsat} unknown={n_unknown}"
    );

    // The generator must reach both SAT and UNSAT — otherwise it proves nothing.
    assert!(
        n_sat > 0,
        "generator produced zero SAT instances — check atom kinds or pool sizes"
    );
    assert!(
        n_unsat > 0,
        "generator produced zero UNSAT instances — check atom kinds or pool sizes"
    );
}

// ────────────────────────────────────────────────────────────────────────────
// Step 2: Fence soundness
//
// Instances that contain array-sorted (= a b) equalities must return Unknown —
// never Sat or Unsat — proving the extensionality fence never wrong-answers.
// ────────────────────────────────────────────────────────────────────────────

#[test]
fn array_equality_instances_are_unknown_never_wrong() {
    // Each sub-instance mixes one array-sorted equality with select atoms.
    // All must return Unknown.

    // Instance 1: simplest possible — bare array equality (= a b).
    {
        let mut s = Solver::new();
        let i_sort = s.declare_sort("I");
        let e_sort = s.declare_sort("E");
        let arr_sort = s.array_sort(i_sort, e_sort);
        let a = s.declare_const("a", arr_sort);
        let b = s.declare_const("b", arr_sort);
        let eq = s.eq(a, b);
        s.assert(eq);
        assert_eq!(
            s.check_sat(),
            SolveOutcome::Unknown,
            "bare (= a b) over array sort must be Unknown (extensionality fence)"
        );
    }

    // Instance 2: (= a b) ∧ (= (select a i) e) — mixed with selects.
    {
        let mut s = Solver::new();
        let i_sort = s.declare_sort("I");
        let e_sort = s.declare_sort("E");
        let arr_sort = s.array_sort(i_sort, e_sort);
        let a = s.declare_const("a", arr_sort);
        let b = s.declare_const("b", arr_sort);
        let i = s.declare_const("i", i_sort);
        let e = s.declare_const("e", e_sort);
        let arr_eq = s.eq(a, b);
        let sel = s.app(Op::Builtin(BuiltinOp::Select), &[a, i]);
        let sel_eq = s.eq(sel, e);
        s.assert(arr_eq);
        s.assert(sel_eq);
        assert_eq!(
            s.check_sat(),
            SolveOutcome::Unknown,
            "(= a b) ∧ (= (select a i) e) must be Unknown"
        );
    }

    // Instance 3: (= a b) ∧ select-store atom — should still be Unknown.
    {
        let mut s = Solver::new();
        let i_sort = s.declare_sort("I");
        let e_sort = s.declare_sort("E");
        let arr_sort = s.array_sort(i_sort, e_sort);
        let a = s.declare_const("a", arr_sort);
        let b = s.declare_const("b", arr_sort);
        let i = s.declare_const("i", i_sort);
        let e = s.declare_const("e", e_sort);
        let arr_eq = s.eq(a, b);
        let st = s.app(Op::Builtin(BuiltinOp::Store), &[a, i, e]);
        let sel = s.app(Op::Builtin(BuiltinOp::Select), &[st, i]);
        let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[sel, e]);
        // (= a b) ∧ (distinct (select (store a i e) i) e) — fence fires.
        s.assert(arr_eq);
        s.assert(dist);
        assert_eq!(
            s.check_sat(),
            SolveOutcome::Unknown,
            "(= a b) ∧ ROW-1 UNSAT witness must be Unknown due to fence"
        );
    }

    // Instance 4: distinct between two arrays (= negated array equality).
    {
        let mut s = Solver::new();
        let i_sort = s.declare_sort("I");
        let e_sort = s.declare_sort("E");
        let arr_sort = s.array_sort(i_sort, e_sort);
        let a = s.declare_const("a", arr_sort);
        let b = s.declare_const("b", arr_sort);
        // (distinct a b) ≡ (not (= a b)) — also triggers the fence.
        let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[a, b]);
        s.assert(dist);
        assert_eq!(
            s.check_sat(),
            SolveOutcome::Unknown,
            "(distinct a b) over array sort must be Unknown (extensionality fence)"
        );
    }

    // Instance 5: random seed — array equality amidst several select atoms.
    {
        let mut rng = Lcg(0xFE5E_D123);
        for _ in 0..20 {
            let mut s = Solver::new();
            let i_sort = s.declare_sort("I");
            let e_sort = s.declare_sort("E");
            let arr_sort = s.array_sort(i_sort, e_sort);
            let a = s.declare_const("a", arr_sort);
            let b = s.declare_const("b", arr_sort);
            // Always assert the array equality (fence trigger).
            let arr_eq = s.eq(a, b);
            s.assert(arr_eq);

            // Add 1-3 select atoms to mix things up.
            let i_consts: Vec<_> = (0..3)
                .map(|k| s.declare_const(&format!("fi{k}"), i_sort))
                .collect();
            let e_consts: Vec<_> = (0..3)
                .map(|k| s.declare_const(&format!("fe{k}"), e_sort))
                .collect();
            let n_extra = 1 + rng.below(3) as usize;
            for _ in 0..n_extra {
                let ii = rng.below(3) as usize;
                let ei = rng.below(3) as usize;
                let pick_a = rng.below(2) == 0;
                let arr_ref = if pick_a { a } else { b };
                let sel = s.app(Op::Builtin(BuiltinOp::Select), &[arr_ref, i_consts[ii]]);
                let atom = s.eq(sel, e_consts[ei]);
                s.assert(atom);
            }

            assert_eq!(
                s.check_sat(),
                SolveOutcome::Unknown,
                "random array-equality instance must be Unknown (fence must never return Sat/Unsat)"
            );
        }
    }

    println!(
        "array_equality_instances_are_unknown_never_wrong: \
         all fence instances correctly returned Unknown"
    );
}
