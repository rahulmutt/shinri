//! Differential oracle: shinri-solver vs z3 on random QF_ABV instances.
//!
//! Run with:
//!   cargo test -p shinri-solver --features oracle --test qfabv_oracle -- --nocapture
//!
//! Requires `z3` on PATH at runtime. Guarded by `#[cfg(feature = "oracle")]`.
//! Mirrors the structure and harness of tests/qfax_oracle.rs and tests/qfbv_oracle.rs.
//!
//! Note on seed: the brief shows `0xABV_0000_0001` which is not valid hex
//! (B/V are not hex digits). We use `0xAB00_0000_0001u64` (replacing 'V' with '0')
//! as the deterministic seed, following the seed style of qfbv_oracle.rs.
#![cfg(feature = "oracle")]

use shinri_core::{BuiltinOp, Op};
use shinri_solver::{SolveOutcome, Solver};

// ─────────────────────────────────────────────────────────────────────────────
// Deterministic PRNG — copied verbatim from qfbv_oracle.rs / oracle.rs
// ─────────────────────────────────────────────────────────────────────────────

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

// ─────────────────────────────────────────────────────────────────────────────
// Number of oracle iterations.
// ─────────────────────────────────────────────────────────────────────────────

const N_ITERS: usize = 200;

// ─────────────────────────────────────────────────────────────────────────────
// QF_ABV instance generator
//
// Per instance:
//   - 3 BV-arrays a0, a1, a2 of type (Array (_ BitVec 8) (_ BitVec 8))
//   - 3 index consts i0, i1, i2 of (_ BitVec 8)
//   - 3 element consts e0, e1, e2 of (_ BitVec 8)
//
// Atoms generated (kept in sync between shinri and the z3 dump):
//
//   Atom 0: 1 store-select witness:
//             (select (store a{ai} i{si} e{se}) i{qi}) =/≠ e{ce}
//           Exercises ROW-1 (si==qi ⇒ result is e{se}) and ROW-2 (si≠qi).
//           ONE store per instance bounds the refinement tree depth (mirrors
//           qfax_oracle.rs).
//
//   Atom 1: 1 functional-consistency atom:
//             (= (select a{ai} i{p}) (select a{ai} i{q}))  or  (distinct ...)
//           Exercises the functional-consistency lemma path.
//
//   Atom 2: 1 extensionality atom — binary OR n-ary, `=` OR `distinct`:
//             (= a0 a1) | (distinct a0 a1) | (= a0 a1 a2) | (distinct a0 a1 a2)
//           Exercises the array-equality abstraction (eq_proxy) path AND the
//           n-ary/distinct desugar (the soundness fix). BV-array (dis)equality is
//           IN SCOPE for QF_ABV (the fence allows it).
//
//   Atom 3 (with prob 1/2): a `(distinct ax ay)` paired with a pinned per-cell
//           agreement `(= (select ax i{p}) (select ay i{p}))` — drives the
//           `distinct` extensionality WITNESS path.
// ─────────────────────────────────────────────────────────────────────────────

/// Generate one QF_ABV instance.
///
/// Returns `(solver_with_assertions, dump_text)` where `dump_text` is the
/// SMT-LIB2 script (without `(check-sat)`) that exactly represents the same
/// formula sent to z3.  The two are built in lockstep so they are always in sync.
fn gen_instance(rng: &mut Lcg) -> (Solver, String) {
    const N_ARR: usize = 3;
    const N_IDX: usize = 3;
    const N_ELT: usize = 3;
    let width: u32 = 8;

    // ── shinri setup ────────────────────────────────────────────────────────
    let mut s = Solver::new();
    let bv8 = s.bv_sort(width);
    let arr_sort = s.array_sort(bv8, bv8);

    let arrays: Vec<shinri_core::TermId> = (0..N_ARR)
        .map(|k| s.declare_const(&format!("a{k}"), arr_sort))
        .collect();
    let idxs: Vec<shinri_core::TermId> = (0..N_IDX)
        .map(|k| s.declare_const(&format!("i{k}"), bv8))
        .collect();
    let elts: Vec<shinri_core::TermId> = (0..N_ELT)
        .map(|k| s.declare_const(&format!("e{k}"), bv8))
        .collect();

    // ── dump header ─────────────────────────────────────────────────────────
    let mut dump = String::from("(set-logic QF_ABV)");
    for k in 0..N_ARR {
        dump.push_str(&format!(
            "\n(declare-const a{k} (Array (_ BitVec {width}) (_ BitVec {width})))"
        ));
    }
    for k in 0..N_IDX {
        dump.push_str(&format!("\n(declare-const i{k} (_ BitVec {width}))"));
    }
    for k in 0..N_ELT {
        dump.push_str(&format!("\n(declare-const e{k} (_ BitVec {width}))"));
    }

    // ── Atom 0: store-select witness ─────────────────────────────────────────
    {
        let ai = rng.below(N_ARR as u64) as usize;
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

        if neg {
            let atom = s.app(Op::Builtin(BuiltinOp::Distinct), &[sel, elts[ce]]);
            s.assert(atom);
            dump.push_str(&format!(
                "\n(assert (distinct (select (store a{ai} i{si} e{se}) i{qi}) e{ce}))"
            ));
        } else {
            let atom = s.eq(sel, elts[ce]);
            s.assert(atom);
            dump.push_str(&format!(
                "\n(assert (= (select (store a{ai} i{si} e{se}) i{qi}) e{ce}))"
            ));
        }
    }

    // ── Atom 1: functional-consistency ──────────────────────────────────────
    {
        let ai = rng.below(N_ARR as u64) as usize;
        let p = rng.below(N_IDX as u64) as usize;
        let q = rng.below(N_IDX as u64) as usize;
        let neg = rng.below(2) == 1;

        let sel_p = s.app(Op::Builtin(BuiltinOp::Select), &[arrays[ai], idxs[p]]);
        let sel_q = s.app(Op::Builtin(BuiltinOp::Select), &[arrays[ai], idxs[q]]);

        if neg {
            let atom = s.app(Op::Builtin(BuiltinOp::Distinct), &[sel_p, sel_q]);
            s.assert(atom);
            dump.push_str(&format!(
                "\n(assert (distinct (select a{ai} i{p}) (select a{ai} i{q})))"
            ));
        } else {
            let atom = s.eq(sel_p, sel_q);
            s.assert(atom);
            dump.push_str(&format!(
                "\n(assert (= (select a{ai} i{p}) (select a{ai} i{q})))"
            ));
        }
    }

    // ── Atom 2: extensionality (binary + n-ary, = and distinct) ───────────────
    // Exercises the array-equality abstraction (eq_proxy) and — crucially after
    // the soundness fix — the n-ary `=`/`distinct` desugar and the `distinct`
    // witness path. `kind` selects among:
    //   0: (= a0 a1)            1: (distinct a0 a1)
    //   2: (= a0 a1 a2)         3: (distinct a0 a1 a2)
    // BV-array (dis)equality is IN SCOPE: the fence allows it (is_bv_array=true).
    {
        let kind = rng.below(4);
        match kind {
            0 => {
                let atom = s.eq(arrays[0], arrays[1]);
                s.assert(atom);
                dump.push_str("\n(assert (= a0 a1))");
            }
            1 => {
                let atom = s.app(Op::Builtin(BuiltinOp::Distinct), &[arrays[0], arrays[1]]);
                s.assert(atom);
                dump.push_str("\n(assert (distinct a0 a1))");
            }
            2 => {
                let atom = s.app(
                    Op::Builtin(BuiltinOp::Eq),
                    &[arrays[0], arrays[1], arrays[2]],
                );
                s.assert(atom);
                dump.push_str("\n(assert (= a0 a1 a2))");
            }
            _ => {
                let atom = s.app(
                    Op::Builtin(BuiltinOp::Distinct),
                    &[arrays[0], arrays[1], arrays[2]],
                );
                s.assert(atom);
                dump.push_str("\n(assert (distinct a0 a1 a2))");
            }
        }
    }

    // ── Atom 3 (sometimes): a distinct that can force a witness ───────────────
    // With probability 1/2, additionally assert agreement of a pair of arrays at
    // EVERY accessed cell while also asserting they are distinct — this drives the
    // `distinct` extensionality witness path (the array must differ at SOME index
    // not pinned). Choose two arrays and pin them equal at i{p} via two reads, then
    // assert (distinct ax ay): SAT iff there is a free index where they may differ.
    {
        if rng.below(2) == 1 {
            let ax = rng.below(N_ARR as u64) as usize;
            let mut ay = rng.below(N_ARR as u64) as usize;
            if ay == ax {
                ay = (ay + 1) % N_ARR;
            }
            let p = rng.below(N_IDX as u64) as usize;
            // (= (select ax i{p}) (select ay i{p}))
            let sax = s.app(Op::Builtin(BuiltinOp::Select), &[arrays[ax], idxs[p]]);
            let say = s.app(Op::Builtin(BuiltinOp::Select), &[arrays[ay], idxs[p]]);
            let eqp = s.eq(sax, say);
            s.assert(eqp);
            dump.push_str(&format!(
                "\n(assert (= (select a{ax} i{p}) (select a{ay} i{p})))"
            ));
            // (distinct ax ay)
            let dist = s.app(Op::Builtin(BuiltinOp::Distinct), &[arrays[ax], arrays[ay]]);
            s.assert(dist);
            dump.push_str(&format!("\n(assert (distinct a{ax} a{ay}))"));
        }
    }

    (s, dump)
}

// ─────────────────────────────────────────────────────────────────────────────
// z3 verdict helper — shells out via z3 -smt2 -in (same approach as qfax_oracle.rs)
// ─────────────────────────────────────────────────────────────────────────────

/// Run `z3 -smt2 -in` with the given dump (no trailing `(check-sat)`) and return
/// the verdict string: "sat", "unsat", or "unknown".
fn z3_verdict(dump: &str) -> String {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let mut input = dump.to_string();
    input.push_str("\n(check-sat)\n");

    let mut child = Command::new("z3")
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("z3 not on PATH — required for #[cfg(feature = \"oracle\")]");

    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();

    let out = child.wait_with_output().unwrap();
    let stdout = String::from_utf8_lossy(&out.stdout);
    // z3 may emit multiple lines; take the last non-empty one as the verdict.
    stdout
        .trim()
        .lines()
        .rfind(|l| !l.trim().is_empty())
        .unwrap_or("unknown")
        .trim()
        .to_string()
}

// ─────────────────────────────────────────────────────────────────────────────
// Main oracle test
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn qfabv_matches_z3() {
    // Seed: the brief shows `0xABV_0000_0001` which is NOT valid hex (V is not a
    // hex digit). Adaptation: replace 'V' with '0' → `0xAB00_0000_0001u64`,
    // following the seed style of qfbv_oracle.rs (`0xB1_B2_B3_B4_B5_B6`).
    let mut rng = Lcg(0xAB00_0000_0001u64);

    let mut n_sat = 0usize;
    let mut n_unsat = 0usize;
    let mut n_unknown_or_skipped = 0usize;

    for it in 0..N_ITERS {
        let (mut solver, dump) = gen_instance(&mut rng);

        let ours = solver.check_sat();
        let theirs = z3_verdict(&dump);

        match (ours, theirs.as_str()) {
            (SolveOutcome::Sat, "sat") => {
                n_sat += 1;
            }
            (SolveOutcome::Unsat, "unsat") => {
                n_unsat += 1;
            }
            // Our incompleteness: shinri Unknown is always allowed (fence may fire).
            (SolveOutcome::Unknown, _) => {
                n_unknown_or_skipped += 1;
            }
            // z3 unknown — no ground truth, skip.
            (_, "unknown") => {
                n_unknown_or_skipped += 1;
            }
            (o, t) => {
                panic!(
                    "QF_ABV SOUNDNESS DISAGREEMENT (iter {it}): shinri={o:?} z3={t}\n\
                     Reproduce with this instance:\n{dump}\n(check-sat)"
                );
            }
        }
    }

    println!(
        "qfabv_matches_z3: {N_ITERS} iters, {n_sat} sat / {n_unsat} unsat / \
         {n_unknown_or_skipped} unknown-or-skipped, 0 mismatches"
    );

    // Both SAT and UNSAT must be exercised — otherwise the oracle proves nothing.
    assert!(
        n_sat > 0,
        "generator produced zero SAT instances — generator or solver is broken"
    );
    assert!(
        n_unsat > 0,
        "generator produced zero UNSAT instances — generator or solver is broken"
    );
}
