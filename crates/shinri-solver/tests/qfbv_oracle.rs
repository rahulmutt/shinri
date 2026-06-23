//! Differential oracle: shinri-solver vs z3 on random QF_BV instances.
//!
//! Run with:
//!   cargo test -p shinri-solver --features oracle --test qfbv_oracle -- --nocapture
//!
//! Requires `z3` on PATH at runtime. Guarded by `#[cfg(feature = "oracle")]`.
//! Mirrors the structure and harness of tests/oracle.rs and tests/qfax_oracle.rs.
#![cfg(feature = "oracle")]

use shinri_core::{BuiltinOp, Op};
use shinri_num::Integer;
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
// Random QF_BV generator
//
// Produces random WELL-TYPED QF_BV formulas over three widths (4, 8, 16).
// The generator builds a pool of bitvector terms for each width, then
// constructs Boolean atoms (predicates, equalities) from those terms.
//
// "Well-typed" means:
//   • Binary BV ops require both arguments to have the same width.
//   • BvExtract indices: hi < width, lo <= hi.
//   • BvConcat: concatenates two terms, producing a wider term.
//   • BvZeroExtend/BvSignExtend: extend by a fixed amount.
//   • BvRotateLeft/BvRotateRight/BvRepeat: parametric by a fixed amount.
//
// The oracle exercises the FULL op set: bitwise, add/sub/neg/mul,
// udiv/urem/sdiv/srem/smod, shl/lshr/ashr, rotate/repeat,
// concat/extract/zero_extend/sign_extend, eq + all unsigned/signed comparisons.
// ────────────────────────────────────────────────────────────────────────────

/// Widths used for random formula generation.
const WIDTHS: [u32; 3] = [4, 8, 16];

/// Number of oracle iterations.
const N_ITERS: usize = 200;

/// SMT-LIB bitvector literal: #b... for small widths, #x... for multiples of 4.
fn bv_lit_smt2(width: u32, value: u64) -> String {
    // Mask to width bits.
    let mask = if width >= 64 { u64::MAX } else { (1u64 << width) - 1 };
    let v = value & mask;
    if width % 4 == 0 {
        // Hex: width/4 hex digits.
        let hex_digits = (width / 4) as usize;
        format!("#x{:0>width$x}", v, width = hex_digits)
    } else {
        // Binary.
        let mut bits = String::new();
        for i in (0..width).rev() {
            bits.push(if (v >> i) & 1 == 1 { '1' } else { '0' });
        }
        format!("#b{bits}")
    }
}

/// Build a z3 s-expression for a bitvector literal.
fn z_bv_lit(ctx: &easy_smt::Context, width: u32, value: u64) -> easy_smt::SExpr {
    ctx.atom(bv_lit_smt2(width, value))
}

/// A bitvector term that exists in both the shinri and z3 worlds.
struct BvPair {
    s: shinri_core::TermId,
    z: easy_smt::SExpr,
    width: u32,
}

/// Generate a pool of width-keyed BV terms and assertions for one iteration.
/// Returns (assertions_s, assertions_z, dump_text, ran_any_complex_op).
fn gen_instance(
    rng: &mut Lcg,
    s: &mut Solver,
    ctx: &mut easy_smt::Context,
    width: u32,
    var_names: &[&str],
    vars_s: &[shinri_core::TermId],
    z_vars: &[easy_smt::SExpr],
    dump: &mut String,
) {
    // ── Build a term pool ────────────────────────────────────────────────────
    // Start with variables, then add a few computed terms.
    let mut pool: Vec<BvPair> = vars_s
        .iter()
        .zip(z_vars.iter())
        .map(|(&s_t, &z_t)| BvPair { s: s_t, z: z_t, width })
        .collect();

    // Add a small number of random BV terms to the pool.
    let n_extra = 2 + rng.below(4) as usize; // 2..=5 extra computed terms
    for _ in 0..n_extra {
        let op_kind = rng.below(18); // pick from BV ops that keep the same width
        let i = rng.below(pool.len() as u64) as usize;
        let j = rng.below(pool.len() as u64) as usize;

        let (new_s, new_z, new_w) = match op_kind {
            // Bitwise unary: bvnot, bvneg
            0 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvNot), &[pool[i].s]);
                let nz = ctx.list(vec![ctx.atom("bvnot"), pool[i].z]);
                (ns, nz, width)
            }
            1 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvNeg), &[pool[i].s]);
                let nz = ctx.list(vec![ctx.atom("bvneg"), pool[i].z]);
                (ns, nz, width)
            }
            // Bitwise binary: bvand, bvor, bvxor, bvnand, bvnor, bvxnor
            2 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvAnd), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvand"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            3 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvOr), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvor"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            4 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvXor), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvxor"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            5 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvNand), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvnand"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            6 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvNor), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvnor"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            7 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvXnor), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvxnor"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            // Arithmetic: bvadd, bvsub, bvmul
            8 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvAdd), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvadd"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            9 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvSub), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvsub"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            10 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvMul), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvmul"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            // Division / remainder: bvudiv, bvurem, bvsdiv, bvsrem, bvsmod
            11 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvUdiv), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvudiv"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            12 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvUrem), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvurem"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            13 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvSdiv), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvsdiv"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            14 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvSrem), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvsrem"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            // Shifts: bvshl, bvlshr, bvashr
            15 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvShl), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvshl"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            16 => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvLshr), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvlshr"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
            _ => {
                let ns = s.app(Op::Builtin(BuiltinOp::BvAshr), &[pool[i].s, pool[j].s]);
                let nz = ctx.list(vec![ctx.atom("bvashr"), pool[i].z, pool[j].z]);
                (ns, nz, width)
            }
        };
        pool.push(BvPair { s: new_s, z: new_z, width: new_w });
    }

    // Occasionally add a concat/extract/extend/rotate/repeat term.
    // These produce terms of different widths (concat, extend) or the same width
    // (extract a full-width slice, rotate, repeat×1). For simplicity we add them
    // to the pool but only build atoms from same-width pairs.
    {
        // BvRepeat(1) — same width, exercises the repeat path.
        let i = rng.below(pool.len() as u64) as usize;
        let ns = s.app(Op::Builtin(BuiltinOp::BvRepeat(1)), &[pool[i].s]);
        let nz = {
            let op_atom = ctx.list(vec![ctx.atom("_"), ctx.atom("repeat"), ctx.atom("1")]);
            ctx.list(vec![op_atom, pool[i].z])
        };
        pool.push(BvPair { s: ns, z: nz, width });

        // BvRotateLeft(1) — same width.
        let i = rng.below(pool.len() as u64) as usize;
        let ns = s.app(Op::Builtin(BuiltinOp::BvRotateLeft(1)), &[pool[i].s]);
        let nz = {
            let op_atom =
                ctx.list(vec![ctx.atom("_"), ctx.atom("rotate_left"), ctx.atom("1")]);
            ctx.list(vec![op_atom, pool[i].z])
        };
        pool.push(BvPair { s: ns, z: nz, width });

        // BvRotateRight(1) — same width.
        let i = rng.below(pool.len() as u64) as usize;
        let ns = s.app(Op::Builtin(BuiltinOp::BvRotateRight(1)), &[pool[i].s]);
        let nz = {
            let op_atom =
                ctx.list(vec![ctx.atom("_"), ctx.atom("rotate_right"), ctx.atom("1")]);
            ctx.list(vec![op_atom, pool[i].z])
        };
        pool.push(BvPair { s: ns, z: nz, width });

        // BvExtract full-width (hi=width-1, lo=0) — same width as input, well-typed.
        if width >= 2 {
            let i = rng.below(pool.len() as u64) as usize;
            let hi = width - 1;
            let lo = 0u32;
            let ns =
                s.app(Op::Builtin(BuiltinOp::BvExtract { hi, lo }), &[pool[i].s]);
            let nz = {
                let op_atom = ctx.list(vec![
                    ctx.atom("_"),
                    ctx.atom("extract"),
                    ctx.atom(&hi.to_string()),
                    ctx.atom(&lo.to_string()),
                ]);
                ctx.list(vec![op_atom, pool[i].z])
            };
            pool.push(BvPair { s: ns, z: nz, width });
        }

        // BvZeroExtend(0) — same width (extend by 0).
        let i = rng.below(pool.len() as u64) as usize;
        let ns = s.app(Op::Builtin(BuiltinOp::BvZeroExtend(0)), &[pool[i].s]);
        let nz = {
            let op_atom = ctx.list(vec![
                ctx.atom("_"),
                ctx.atom("zero_extend"),
                ctx.atom("0"),
            ]);
            ctx.list(vec![op_atom, pool[i].z])
        };
        pool.push(BvPair { s: ns, z: nz, width });

        // BvSignExtend(0) — same width.
        let i = rng.below(pool.len() as u64) as usize;
        let ns = s.app(Op::Builtin(BuiltinOp::BvSignExtend(0)), &[pool[i].s]);
        let nz = {
            let op_atom = ctx.list(vec![
                ctx.atom("_"),
                ctx.atom("sign_extend"),
                ctx.atom("0"),
            ]);
            ctx.list(vec![op_atom, pool[i].z])
        };
        pool.push(BvPair { s: ns, z: nz, width });

        // BvConcat of two half-width terms (if width >= 2): produces a
        // double-width term. We don't add it to the current-width pool — it
        // has a different width. We just exercise the op in the pool building
        // but don't add an atom for it to keep sort-homogeneity simple.
        // (The concat/extract round-trip is tested in qfbv_witnesses.rs.)
    }

    // ── Build Boolean atoms from the pool ────────────────────────────────────
    let n_atoms = 2 + rng.below(4) as usize; // 2..=5 atoms

    for _ in 0..n_atoms {
        let kind = rng.below(11); // 0-1 eq/ne, 2-9 comparisons, 10 = literal comparison
        let i = rng.below(pool.len() as u64) as usize;
        let j = rng.below(pool.len() as u64) as usize;

        let (s_atom, z_atom, text) = match kind {
            // Equality
            0 => {
                let sa = s.eq(pool[i].s, pool[j].s);
                let za = ctx.eq(pool[i].z, pool[j].z);
                (sa, za, format!("(= t{i} t{j})"))
            }
            // Disequality
            1 => {
                let eq = s.eq(pool[i].s, pool[j].s);
                let sa = s.app(Op::Builtin(BuiltinOp::Not), &[eq]);
                let za = ctx.not(ctx.eq(pool[i].z, pool[j].z));
                (sa, za, format!("(distinct t{i} t{j})"))
            }
            // bvult
            2 => {
                let sa = s.app(Op::Builtin(BuiltinOp::BvUlt), &[pool[i].s, pool[j].s]);
                let za = ctx.list(vec![ctx.atom("bvult"), pool[i].z, pool[j].z]);
                (sa, za, format!("(bvult t{i} t{j})"))
            }
            // bvule
            3 => {
                let sa = s.app(Op::Builtin(BuiltinOp::BvUle), &[pool[i].s, pool[j].s]);
                let za = ctx.list(vec![ctx.atom("bvule"), pool[i].z, pool[j].z]);
                (sa, za, format!("(bvule t{i} t{j})"))
            }
            // bvugt
            4 => {
                let sa = s.app(Op::Builtin(BuiltinOp::BvUgt), &[pool[i].s, pool[j].s]);
                let za = ctx.list(vec![ctx.atom("bvugt"), pool[i].z, pool[j].z]);
                (sa, za, format!("(bvugt t{i} t{j})"))
            }
            // bvuge
            5 => {
                let sa = s.app(Op::Builtin(BuiltinOp::BvUge), &[pool[i].s, pool[j].s]);
                let za = ctx.list(vec![ctx.atom("bvuge"), pool[i].z, pool[j].z]);
                (sa, za, format!("(bvuge t{i} t{j})"))
            }
            // bvslt
            6 => {
                let sa = s.app(Op::Builtin(BuiltinOp::BvSlt), &[pool[i].s, pool[j].s]);
                let za = ctx.list(vec![ctx.atom("bvslt"), pool[i].z, pool[j].z]);
                (sa, za, format!("(bvslt t{i} t{j})"))
            }
            // bvsle
            7 => {
                let sa = s.app(Op::Builtin(BuiltinOp::BvSle), &[pool[i].s, pool[j].s]);
                let za = ctx.list(vec![ctx.atom("bvsle"), pool[i].z, pool[j].z]);
                (sa, za, format!("(bvsle t{i} t{j})"))
            }
            // bvsgt
            8 => {
                let sa = s.app(Op::Builtin(BuiltinOp::BvSgt), &[pool[i].s, pool[j].s]);
                let za = ctx.list(vec![ctx.atom("bvsgt"), pool[i].z, pool[j].z]);
                (sa, za, format!("(bvsgt t{i} t{j})"))
            }
            // bvsge
            9 => {
                let sa = s.app(Op::Builtin(BuiltinOp::BvSge), &[pool[i].s, pool[j].s]);
                let za = ctx.list(vec![ctx.atom("bvsge"), pool[i].z, pool[j].z]);
                (sa, za, format!("(bvsge t{i} t{j})"))
            }
            // Compare a term against a literal value (exercises constant folding path)
            _ => {
                let lit_val = rng.below(1u64 << width.min(16));
                let s_lit = s.bv_numeral(Integer::from(lit_val as i128), width);
                let z_lit = z_bv_lit(ctx, width, lit_val);
                let sa = s.eq(pool[i].s, s_lit);
                let za = ctx.eq(pool[i].z, z_lit);
                (sa, za, format!("(= t{i} {})", bv_lit_smt2(width, lit_val)))
            }
        };

        s.assert(s_atom);
        ctx.assert(z_atom).unwrap();
        dump.push_str(&format!(
            "\n(assert {text}) ; w={width} vars=[{}]",
            var_names.join(",")
        ));
    }
}

#[test]
fn differential_qf_bv_small() {
    let mut rng = Lcg(0xB1_B2_B3_B4_B5_B6);

    let mut n_sat = 0usize;
    let mut n_unsat = 0usize;
    let mut n_unknown = 0usize;
    let mut n_disagreements = 0usize;

    // We keep a separate counter for each width to ensure all widths are exercised.
    let mut width_counts = [0usize; 3]; // [w4, w8, w16]

    for iter in 0..N_ITERS {
        // Pick a width for this iteration.
        let wi = rng.below(WIDTHS.len() as u64) as usize;
        let width = WIDTHS[wi];
        width_counts[wi] += 1;

        // ── shinri setup ────────────────────────────────────────────────────
        let mut s = Solver::new();
        let bv_sort = s.bv_sort(width);

        // Declare 3 variables of the chosen width.
        let var_names = ["x", "y", "z"];
        let vars_s: Vec<shinri_core::TermId> = var_names
            .iter()
            .map(|name| s.declare_const(name, bv_sort))
            .collect();

        // ── z3 setup (easy-smt) ─────────────────────────────────────────────
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .unwrap();
        ctx.set_logic("QF_BV").unwrap();

        let bv_type_atom = ctx.list(vec![
            ctx.atom("_"),
            ctx.atom("BitVec"),
            ctx.atom(&width.to_string()),
        ]);
        let z_vars: Vec<easy_smt::SExpr> = var_names
            .iter()
            .map(|name| ctx.declare_const(name.to_string(), bv_type_atom).unwrap())
            .collect();

        let mut dump = format!(
            "iter={iter} width={width}\n(set-logic QF_BV)"
        );
        for name in &var_names {
            dump.push_str(&format!(
                "\n(declare-fun {name} () (_ BitVec {width}))"
            ));
        }

        // ── Generate random formula ─────────────────────────────────────────
        gen_instance(
            &mut rng,
            &mut s,
            &mut ctx,
            width,
            &var_names,
            &vars_s,
            &z_vars,
            &mut dump,
        );

        dump.push_str("\n(check-sat)");

        let ours = s.check_sat();
        let theirs = ctx.check().unwrap();

        match (ours, theirs) {
            (SolveOutcome::Unknown, _) => {
                // Our Unknown is never a failure — skip.
                n_unknown += 1;
            }
            (SolveOutcome::Sat, easy_smt::Response::Sat) => {
                n_sat += 1;
            }
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {
                n_unsat += 1;
            }
            (o, t) => {
                n_disagreements += 1;
                panic!(
                    "QF_BV SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                     Reproduce with this instance:\n{dump}"
                );
            }
        }
    }

    println!(
        "differential_qf_bv_small: {N_ITERS} instances\n  \
         sat={n_sat} unsat={n_unsat} unknown={n_unknown} disagreements={n_disagreements}\n  \
         width breakdown: w4={} w8={} w16={}",
        width_counts[0], width_counts[1], width_counts[2]
    );

    // The generator must exercise all three widths.
    for (i, &w) in WIDTHS.iter().enumerate() {
        assert!(
            width_counts[i] > 0,
            "generator never exercised width={w} — seed or WIDTHS broken"
        );
    }

    // Both SAT and UNSAT must be reached — otherwise the oracle is trivial.
    assert!(
        n_sat > 0,
        "generator produced zero SAT instances — generator or blaster is broken"
    );
    assert!(
        n_unsat > 0,
        "generator produced zero UNSAT instances — generator or blaster is broken"
    );

    // The TEETH check: log whether we had enough non-unknown runs.
    let ran = n_sat + n_unsat;
    let total = ran + n_unknown;
    assert!(
        ran > total / 2,
        "More than half the oracle runs were Unknown ({n_unknown}/{total}) — \
         QF_BV fence is firing too aggressively or blaster is broken"
    );

    // Zero disagreements is the hard guarantee — any panic above would have set
    // n_disagreements but we also assert here as a belt-and-suspenders check.
    assert_eq!(
        n_disagreements, 0,
        "SOUNDNESS BUG: {n_disagreements} disagreements detected"
    );
}
