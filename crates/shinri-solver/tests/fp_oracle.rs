//! Differential oracle: shinri-solver vs z3 on random rounding-free QF_FP.
//!
//! Run with:
//!   cargo test -p shinri-solver --features oracle --test fp_oracle -- --nocapture
//!
//! Requires `z3` on PATH at runtime. Guarded by `#[cfg(feature = "oracle")]`.
//! Mirrors the structure and harness of tests/qfbv_oracle.rs.
#![cfg(feature = "oracle")]

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, SolveOutcome, Solver};

/// A tiny deterministic LCG so the corpus is reproducible without rand.
/// Copied verbatim from tests/qfbv_oracle.rs to match the existing convention.
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

/// Number of oracle iterations.
const N_ITERS: usize = 200;

/// Classification predicates supported by slice-1 (rounding-free).
const PREDS: &[&str] = &[
    "fp.isNaN",
    "fp.isInfinite",
    "fp.isZero",
    "fp.isNormal",
    "fp.isSubnormal",
    "fp.isNegative",
    "fp.isPositive",
];

/// FP32 special-form constants that parse into proper TermNode::Const nodes
/// (NOT App/FpFromBits nodes, which would trigger the BV fence via their BV children).
/// The `(_ ±zero/±oo/NaN eb sb)` indexed forms go through `mk_fp_const` and produce
/// a `Const { val: ConstVal::Float(..) }` node that `blast_word` handles directly.
const FP32_SPECIALS: &[&str] = &[
    "(_ +zero 8 24)",
    "(_ -zero 8 24)",
    "(_ +oo 8 24)",
    "(_ -oo 8 24)",
    "(_ NaN 8 24)",
];

/// Generate a random rounding-free QF_FP SMT-LIB script.
///
/// Declares one variable `x : (_ FloatingPoint 8 24)` (= Float32), builds
/// 1..=3 random assertions drawn from the 7 classification predicates, `fp.eq`,
/// and core `=`, then appends `(check-sat)`.  The same text is fed to both
/// shinri and z3, keeping the comparison exact.
///
/// FP constants use the `(_ +zero/±oo/NaN 8 24)` special forms, which produce
/// TermNode::Const nodes that the slice-1 FP blaster handles without triggering
/// the BV fence (the `(fp #b... #b... #b...)` constructor form produces App/FpFromBits
/// nodes with BV-sorted children, which would trip `solver_uses_bv` → Unknown).
fn gen_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n",
    );

    let n_asserts = 1 + rng.below(3) as usize; // 1..=3 asserts

    for _ in 0..n_asserts {
        // Atom kinds:
        //   0..PREDS.len()           classification predicate on x
        //   PREDS.len()              fp.eq x <special-const>
        //   PREDS.len()+1            fp.eq <special-const> <special-const>  (constant folding)
        //   PREDS.len()+2            = x <special-const>   (core equality, NaN-aware)
        let n_choices = PREDS.len() as u64 + 3;
        let choice = rng.below(n_choices) as usize;

        let atom: String = if choice < PREDS.len() {
            format!("({} x)", PREDS[choice])
        } else if choice == PREDS.len() {
            let c = FP32_SPECIALS[rng.below(FP32_SPECIALS.len() as u64) as usize];
            format!("(fp.eq x {c})")
        } else if choice == PREDS.len() + 1 {
            let ca = FP32_SPECIALS[rng.below(FP32_SPECIALS.len() as u64) as usize];
            let cb = FP32_SPECIALS[rng.below(FP32_SPECIALS.len() as u64) as usize];
            format!("(fp.eq {ca} {cb})")
        } else {
            let c = FP32_SPECIALS[rng.below(FP32_SPECIALS.len() as u64) as usize];
            format!("(= x {c})")
        };

        // Randomly negate.
        if rng.below(2) == 0 {
            s.push_str(&format!("(assert (not {atom}))\n"));
        } else {
            s.push_str(&format!("(assert {atom})\n"));
        }
    }

    // Occasionally add a conjunctive/disjunctive pair for broader coverage.
    if rng.below(3) == 0 {
        let pa = PREDS[rng.below(PREDS.len() as u64) as usize];
        let pb = PREDS[rng.below(PREDS.len() as u64) as usize];
        if rng.below(2) == 0 {
            s.push_str(&format!("(assert (and ({pa} x) ({pb} x)))\n"));
        } else {
            s.push_str(&format!("(assert (or ({pa} x) ({pb} x)))\n"));
        }
    }

    s.push_str("(check-sat)\n");
    s
}

/// Run the shinri parser+solver pipeline on a complete SMT-LIB script.
fn shinri_outcome(src: &str) -> SolveOutcome {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut outcome = SolveOutcome::Unknown;
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        let cmd = result.expect("parse error in generated script");
        match solver.execute(cmd) {
            CommandResponse::Sat => outcome = SolveOutcome::Sat,
            CommandResponse::Unsat => outcome = SolveOutcome::Unsat,
            CommandResponse::Unknown => outcome = SolveOutcome::Unknown,
            _ => {}
        }
    }
    outcome
}

/// Feed a QF_FP arithmetic script to z3 via easy_smt.
///
/// Unlike `z3_outcome` (which hardcodes declaring only `x`), this version
/// forwards every `(declare-fun …)` and `(assert …)` line verbatim, making it
/// suitable for scripts that declare x, y, z, and optionally an `rm` variable.
fn z3_outcome_arith(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_FP").expect("z3 set-logic failed");
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(declare-fun ") || t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 send failed");
            ctx.raw_recv().expect("z3 ack failed");
        }
    }
    ctx.check().expect("z3 check-sat failed")
}

/// Rounding mode literals for QF_FP arithmetic oracle.
const RMS: &[&str] = &["RNE", "RNA", "RTP", "RTN", "RTZ"];

/// Generate a random QF_FP script with fp.add/fp.sub over all five rounding modes.
///
/// Declares three fp32 variables (x, y, z) and optionally a symbolic rounding mode.
/// Builds 1–3 assertions mixing fp.add/fp.sub with fp.eq/=/fp.isNaN atoms,
/// some negated, so that both SAT and UNSAT witnesses arise across iterations.
fn gen_arith_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let use_sym_rm = rng.below(4) == 0;
    if use_sym_rm {
        s.push_str("(declare-fun rm () RoundingMode)\n");
    }
    let rm = |rng: &mut Lcg| -> String {
        if use_sym_rm && rng.below(2) == 0 {
            "rm".to_string()
        } else {
            RMS[rng.below(RMS.len() as u64) as usize].to_string()
        }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let op = if rng.below(2) == 0 { "fp.add" } else { "fp.sub" };
        let term = format!("({op} {} x y)", rm(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq z {term})"),
            1 => format!("(= z {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 {
            s.push_str(&format!("(assert (not {atom}))\n"));
        } else {
            s.push_str(&format!("(assert {atom})\n"));
        }
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_fp_add_sub() {
    // Seed: brief had invalid hex 0xADD_5UB_0001 ('U' is not a hex digit).
    // Fixed to 0x0ADD_5AB_0001 (replaced U→A, prepended 0 for valid u64 literal).
    let mut rng = Lcg(0x00AD_D5AB_0001);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_arith_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_FP add/sub DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
        }
    }
    println!("differential_qf_fp_add_sub: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}

/// Feed a QF_FP script to z3 via easy_smt and return its check-sat response.
///
/// Mirrors qfbv_oracle.rs: create a fresh easy_smt context (= fresh z3 subprocess)
/// per iteration via `ContextBuilder::new().solver("z3", …).build()`, set the logic,
/// declare the variable, send each `(assert …)` line as a raw atom command, then
/// call `ctx.check()` for the verdict.
///
/// Using `raw_send` + `raw_recv` for each assert: `ContextBuilder::build` enables
/// `:print-success true` so z3 echoes "success" after each ack'd command.
fn z3_outcome(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    // (set-logic QF_FP)
    ctx.set_logic("QF_FP").expect("z3 set-logic failed");

    // (declare-fun x () (_ FloatingPoint 8 24))
    let fp_sort = ctx.list(vec![
        ctx.atom("_"),
        ctx.atom("FloatingPoint"),
        ctx.atom("8"),
        ctx.atom("24"),
    ]);
    ctx.declare_fun("x", vec![], fp_sort)
        .expect("z3 declare_fun failed");

    // Send each (assert ...) line directly as a raw command.
    // `ctx.atom(line)` treats the entire line as an atom; `raw_send` writes it
    // verbatim to z3's stdin.  Since `:print-success true` is active, z3 echoes
    // "success" after each command, so we `raw_recv` to consume it.
    for line in src.lines() {
        let t = line.trim();
        if t.starts_with("(assert ") {
            let sexpr = ctx.atom(t);
            ctx.raw_send(sexpr).expect("z3 assert send failed");
            ctx.raw_recv().expect("z3 assert ack failed");
        }
    }

    // check-sat
    ctx.check().expect("z3 check-sat failed")
}

#[test]
fn differential_qf_fp_rounding_free() {
    let mut rng = Lcg(0x000F_10A7_1234);

    let mut n_sat = 0usize;
    let mut n_unsat = 0usize;
    let mut n_unknown = 0usize;
    let mut n_disagreements = 0usize;

    for iter in 0..N_ITERS {
        let src = gen_script(&mut rng);

        // ── shinri verdict ──────────────────────────────────────────────────
        let ours = shinri_outcome(&src);

        // Sound abstention: shinri returns Unknown for any out-of-scope
        // construct; skip those iterations (they are not disagreements).
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }

        // ── z3 verdict (mirroring qfbv_oracle.rs idiom) ────────────────────
        // Create a fresh easy_smt context (= fresh z3 process) per iteration,
        // exactly as qfbv_oracle.rs does for QF_BV.
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");

        let theirs = z3_outcome(&mut ctx, &src);

        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => {
                n_sat += 1;
            }
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {
                n_unsat += 1;
            }
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => {
                // z3 returned Unknown (e.g. timeout); skip this iteration.
                continue;
            }
            (o, t) => {
                // Increment before panicking so the disagreement appears in the
                // final assert_eq! if test harness somehow resumes (belt-and-suspenders).
                #[allow(unused_assignments)]
                {
                    n_disagreements += 1;
                }
                panic!(
                    "QF_FP SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                     Script:\n{src}"
                );
            }
        }
    }

    println!(
        "differential_qf_fp_rounding_free: {N_ITERS} instances\n  \
         sat={n_sat} unsat={n_unsat} unknown={n_unknown} disagreements={n_disagreements}"
    );

    // Both SAT and UNSAT must be reached — otherwise the oracle provides no coverage.
    assert!(
        n_sat > 0,
        "generator produced zero SAT instances — generator or FP blaster is broken"
    );
    assert!(
        n_unsat > 0,
        "generator produced zero UNSAT instances — generator or FP blaster is broken"
    );

    // Enough non-unknown runs to be meaningful.
    let ran = n_sat + n_unsat;
    let total = ran + n_unknown;
    assert!(
        ran > total / 2,
        "More than half the oracle runs were Unknown ({n_unknown}/{total}) — \
         FP fence is firing too aggressively or FP blaster is broken"
    );

    // Zero disagreements is the hard guarantee.
    assert_eq!(
        n_disagreements, 0,
        "SOUNDNESS BUG: {n_disagreements} disagreements detected"
    );
}

/// Generate a random QF_FP script with fp.mul over all five rounding modes.
/// Declares three fp32 variables (x, y, z) and optionally a symbolic rounding
/// mode; builds 1–3 assertions mixing fp.mul with fp.eq/=/fp.isNaN atoms, some
/// negated, so both SAT and UNSAT witnesses arise across iterations.
fn gen_mul_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let use_sym_rm = rng.below(4) == 0;
    if use_sym_rm {
        s.push_str("(declare-fun rm () RoundingMode)\n");
    }
    let rm = |rng: &mut Lcg| -> String {
        if use_sym_rm && rng.below(2) == 0 {
            "rm".to_string()
        } else {
            RMS[rng.below(RMS.len() as u64) as usize].to_string()
        }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = format!("(fp.mul {} x y)", rm(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq z {term})"),
            1 => format!("(= z {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 {
            s.push_str(&format!("(assert (not {atom}))\n"));
        } else {
            s.push_str(&format!("(assert {atom})\n"));
        }
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_fp_mul() {
    let mut rng = Lcg(0x00B0_0B5_FACE);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_mul_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_FP mul DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
        }
    }
    println!("differential_qf_fp_mul: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}

/// Generate a random QF_FP script with fp.div over all five rounding modes.
/// Declares three fp32 variables (x, y, z) and optionally a symbolic rounding
/// mode; builds 1–3 assertions mixing fp.div with fp.eq/=/fp.isNaN atoms, some
/// negated, so both SAT and UNSAT witnesses arise across iterations.
fn gen_div_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let use_sym_rm = rng.below(4) == 0;
    if use_sym_rm {
        s.push_str("(declare-fun rm () RoundingMode)\n");
    }
    let rm = |rng: &mut Lcg| -> String {
        if use_sym_rm && rng.below(2) == 0 {
            "rm".to_string()
        } else {
            RMS[rng.below(RMS.len() as u64) as usize].to_string()
        }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = format!("(fp.div {} x y)", rm(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq z {term})"),
            1 => format!("(= z {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 {
            s.push_str(&format!("(assert (not {atom}))\n"));
        } else {
            s.push_str(&format!("(assert {atom})\n"));
        }
    }
    s.push_str("(check-sat)\n");
    s
}

// fp.div instances are ~60-70x slower per iteration than fp.mul: the restoring
// udivurem over 50-bit significands yields ~2500-level gate circuits, so each z3
// cross-check runs ~18s. Bound this oracle independently of N_ITERS so a full
// gated run completes in minutes while still covering both SAT and UNSAT.
const DIV_ITERS: usize = 40;

#[test]
fn differential_qf_fp_div() {
    let mut rng = Lcg(0x00D1_F00D_2C3D);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..DIV_ITERS {
        let src = gen_div_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_FP div DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
        }
    }
    println!("differential_qf_fp_div: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}

/// Generate a random QF_FP script with fp.sqrt over all five rounding modes.
/// Declares two fp32 variables (x, z) and optionally a symbolic rounding mode
/// (fp.sqrt is unary — no y operand).  Builds 1–3 assertions mixing fp.sqrt
/// with fp.eq/=/fp.isNaN atoms, some negated, so both SAT and UNSAT witnesses
/// arise across iterations.
fn gen_sqrt_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let use_sym_rm = rng.below(4) == 0;
    if use_sym_rm {
        s.push_str("(declare-fun rm () RoundingMode)\n");
    }
    let rm = |rng: &mut Lcg| -> String {
        if use_sym_rm && rng.below(2) == 0 {
            "rm".to_string()
        } else {
            RMS[rng.below(RMS.len() as u64) as usize].to_string()
        }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = format!("(fp.sqrt {} x)", rm(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq z {term})"),
            1 => format!("(= z {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 {
            s.push_str(&format!("(assert (not {atom}))\n"));
        } else {
            s.push_str(&format!("(assert {atom})\n"));
        }
    }
    s.push_str("(check-sat)\n");
    s
}

// fp.sqrt instances involve a digit-recurrence square-root over ~50-bit
// significands; bound this oracle independently of N_ITERS so a full gated
// run completes in minutes while still covering both SAT and UNSAT.
const SQRT_ITERS: usize = 40;

#[test]
fn differential_qf_fp_sqrt() {
    let mut rng = Lcg(0x0050_312C_3D51_17);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..SQRT_ITERS {
        let src = gen_sqrt_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_FP sqrt DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
        }
    }
    println!("differential_qf_fp_sqrt: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}
