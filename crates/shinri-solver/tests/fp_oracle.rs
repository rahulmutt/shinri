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
        let op = if rng.below(2) == 0 {
            "fp.add"
        } else {
            "fp.sub"
        };
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
            (o, t) => {
                panic!("QF_FP add/sub DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}")
            }
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
            (o, t) => panic!("QF_FP mul DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
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
            (o, t) => panic!("QF_FP div DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    println!("differential_qf_fp_div: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}

/// Generate a random QF_FP script with fp.rem (two fp32 vars; no rounding mode —
/// fp.rem is exact). Builds 1–3 assertions mixing fp.rem with fp.eq/=/fp.isNaN
/// atoms, some negated, so both SAT and UNSAT witnesses arise.
fn gen_rem_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = "(fp.rem x y)".to_string();
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

// fp.rem is the deepest FP datapath: the fmod reduction loop unrolls to ~276
// stages for Float32, so each symbolic instance is a very deep circuit. Bound the
// oracle well below the div bound; raise only behind a per-instance wall-clock
// timeout (a hard symbolic UNSAT can grind for hours in the eager bit-blaster).
const REM_ITERS: usize = 20;

#[test]
fn differential_qf_fp_rem() {
    let mut rng = Lcg(0x00FE_2C0D_3E11);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..REM_ITERS {
        let src = gen_rem_script(&mut rng);
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
            (o, t) => panic!("QF_FP rem DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    println!("differential_qf_fp_rem: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0, "oracle produced no SAT coverage");
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
// run completes in seconds while still covering both SAT and UNSAT.
//
// Bound chosen below the first intractable-for-us instance: with this seed,
// iters 0..30 each solve in <100ms (SAT plus UNSAT at 9/17/22/28), but some
// later scripts conjoin multiple symbolic fp.sqrt terms across distinct
// rounding modes (e.g. iter 37 is `z=sqrt_RNE(x) ∧ z≠sqrt_RTZ(x) ∧
// z≠sqrt_RNA(x)`, which is UNSAT). z3 refutes those in <0.2s via its native
// FP theory, but our *eager* bit-blaster must grind a full propositional
// refutation over three deep digit-recurrence circuits — hours of search.
// Such instances carry no correctness signal here (a shinri-vs-z3
// disagreement can only arise where both solvers decide), so we bound below
// them rather than wait them out. Do NOT raise this without first adding a
// per-instance wall-clock timeout — a higher bound will hang on a hard UNSAT.
const SQRT_ITERS: usize = 30;

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
            (o, t) => panic!("QF_FP sqrt DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    println!("differential_qf_fp_sqrt: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}

/// Rounding-free QF_FP over two vars, exercising fp.lt/leq/gt/geq and fp.min/max.
fn gen_rel_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n",
    );
    const RELS: &[&str] = &["fp.lt", "fp.leq", "fp.gt", "fp.geq"];
    let vars = ["x", "y"];
    let pick_operand = |rng: &mut Lcg| -> String {
        // 50% a variable, 50% a special constant.
        if rng.below(2) == 0 {
            vars[rng.below(2) as usize].to_string()
        } else {
            FP32_SPECIALS[rng.below(FP32_SPECIALS.len() as u64) as usize].to_string()
        }
    };

    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let kind = rng.below(2);
        let atom = if kind == 0 {
            // relation between two operands
            let rel = RELS[rng.below(RELS.len() as u64) as usize];
            let a = pick_operand(rng);
            let b = pick_operand(rng);
            format!("({rel} {a} {b})")
        } else {
            // min/max folded into an fp.eq so its word output is observable
            let mm = if rng.below(2) == 0 {
                "fp.min"
            } else {
                "fp.max"
            };
            let a = pick_operand(rng);
            let b = pick_operand(rng);
            let c = pick_operand(rng);
            format!("(fp.eq ({mm} {a} {b}) {c})")
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

/// Random QF_FP with fp.roundToIntegral over all five rounding modes (unary op).
fn gen_roundint_script(rng: &mut Lcg) -> String {
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
        let term = format!("(fp.roundToIntegral {} x)", rm(rng));
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

// fp.roundToIntegral is a shallow circuit (two barrel shifts + an add, no
// digit-recurrence), so this can run the full N_ITERS unlike div/sqrt.
const ROUNDINT_ITERS: usize = N_ITERS;

#[test]
fn differential_qf_fp_roundint() {
    let mut rng = Lcg(0x00A1_7E2D_4C9F_03);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..ROUNDINT_ITERS {
        let src = gen_roundint_script(&mut rng);
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
                "QF_FP roundToIntegral DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
        }
    }
    println!("differential_qf_fp_roundint: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}

/// Random QF_FP with fp.fma over all five rounding modes (ternary op). Operands
/// mix variables and special constants to keep instances decidable-fast.
fn gen_fma_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n\
         (declare-fun w () (_ FloatingPoint 8 24))\n",
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
    const SPECIALS: &[&str] = &[
        "(_ +zero 8 24)",
        "(_ -zero 8 24)",
        "(_ +oo 8 24)",
        "(_ -oo 8 24)",
        "(_ NaN 8 24)",
    ];
    let vars = ["x", "y", "z"];
    let operand = |rng: &mut Lcg| -> String {
        if rng.below(2) == 0 {
            vars[rng.below(3) as usize].to_string()
        } else {
            SPECIALS[rng.below(SPECIALS.len() as u64) as usize].to_string()
        }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = format!(
            "(fp.fma {} {} {} {})",
            rm(rng),
            operand(rng),
            operand(rng),
            operand(rng)
        );
        let atom = match rng.below(3) {
            0 => format!("(fp.eq w {term})"),
            1 => format!("(= w {term})"),
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

// fp.fma is the DEEPEST FP datapath (2·sb multiply + 2·sb LZC/shifts + the
// rounder). Bound this oracle well below N_ITERS, mirroring SQRT_ITERS/DIV_ITERS:
// z3 refutes hard conjoined symbolic-fma UNSAT instances in <1s via its native FP
// theory, but our eager bit-blaster must grind a full propositional refutation
// over multiple deep circuits — minutes-to-hours. Such instances carry no
// correctness signal (a disagreement can only arise where both solvers decide),
// so bound below the first intractable iter rather than wait it out. Start at 20;
// lower it (after confirming zero disagreement up to that point) if a late
// instance grinds. Do NOT raise without first adding a per-instance wall-clock
// timeout — a higher bound will hang on a hard UNSAT.
const FMA_ITERS: usize = 20;

#[test]
fn differential_qf_fp_fma() {
    let mut rng = Lcg(0x00FA_2D11_6C03_55);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..FMA_ITERS {
        let src = gen_fma_script(&mut rng);
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
            (o, t) => panic!("QF_FP fma DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    println!("differential_qf_fp_fma: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}

// The file is gated at module level (`#![cfg(feature = "oracle")]`), so no
// per-test cfg is needed. `Lcg` is the tuple struct `Lcg(u64)`.
#[test]
fn differential_qf_fp_relations() {
    let mut rng = Lcg(0x002D_5EED_0001);
    let (mut n_sat, mut n_unsat) = (0usize, 0usize);
    for iter in 0..N_ITERS {
        let src = gen_rel_script(&mut rng);
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        let ours = shinri_outcome(&src);
        match (&ours, &theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (o, t) => {
                panic!("QF_FP relations DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}")
            }
        }
    }
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no coverage");
}

/// Random QF_FP script exercising the two non-BV to_fp faces: widen/narrow between
/// Float32 and Float64, and to_fp of a constant Real (a ratio of small integers).
/// Mixes with fp.eq / = / fp.isNaN atoms, some negated, so SAT and UNSAT both arise.
fn gen_to_fp_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(set-logic QF_FP)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun w () (_ FloatingPoint 11 53))\n\
         (declare-fun z () (_ FloatingPoint 8 24))\n",
    );
    let modes = ["RNE", "RNA", "RTP", "RTN", "RTZ"];
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let rm = modes[rng.below(5) as usize];
        // pick a conversion term of Float32 sort so it composes with z / fp.isNaN.
        let term = match rng.below(3) {
            0 => format!("((_ to_fp 8 24) {rm} w)"), // narrow Float64→Float32
            1 => {
                let num = 1 + rng.below(9);
                let den = 1 + rng.below(9);
                format!("((_ to_fp 8 24) {rm} (/ {num}.0 {den}.0))") // const-Real→Float32
            }
            _ => format!("((_ to_fp 8 24) {rm} ((_ to_fp 11 53) {rm} x))"), // round-trip via Float64
        };
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

const TO_FP_ITERS: usize = 60;

#[test]
fn differential_qf_fp_to_fp() {
    let mut rng = Lcg(0x0A_11_3E_5C_07_D1);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..TO_FP_ITERS {
        let src = gen_to_fp_script(&mut rng);
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
            (o, t) => {
                panic!("QF_FP to_fp DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}")
            }
        }
    }
    println!("differential_qf_fp_to_fp: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(
        n_sat > 0 && n_unsat > 0,
        "oracle produced no SAT/UNSAT coverage"
    );
}

/// One mixed BV+FP script: a BV comparison AND an FP comparison over
/// independently-declared vars (no crossing conversion — slice 4b's fence
/// only lifted for non-crossing mixed queries). Both sides are forwarded to
/// z3 verbatim by `z3_outcome_mixed`.
fn gen_mixed_script(rng: &mut Lcg) -> String {
    // Reuse the FP32 special-form constant pool the other generators use.
    let a = FP32_SPECIALS[rng.below(FP32_SPECIALS.len() as u64) as usize];
    let b = FP32_SPECIALS[rng.below(FP32_SPECIALS.len() as u64) as usize];
    // BV side: an 8-bit unsigned comparison against a random constant.
    let k = (rng.next() & 0xff) as u8;
    const FP_RELS: &[&str] = &["fp.lt", "fp.leq", "fp.gt", "fp.geq", "fp.eq"];
    const BV_RELS: &[&str] = &["bvult", "bvule", "bvugt", "bvuge"];
    let fp_rel = FP_RELS[rng.below(FP_RELS.len() as u64) as usize];
    let bv_rel = BV_RELS[rng.below(BV_RELS.len() as u64) as usize];
    format!(
        "(declare-fun bx () (_ BitVec 8))\n\
         (declare-fun fa () (_ FloatingPoint 8 24))\n\
         (declare-fun fb () (_ FloatingPoint 8 24))\n\
         (assert (= fa {a}))\n\
         (assert (= fb {b}))\n\
         (assert (and ({bv_rel} bx #x{k:02x}) ({fp_rel} fa fb)))\n\
         (check-sat)\n"
    )
}

/// Feed a mixed BV+FP script to z3 via easy_smt using `QF_BVFP` (mixed-capable
/// logic), NOT `QF_FP`. Empirically, z3 4.16.0 rejects `(declare-fun bx ()
/// (_ BitVec 8))` under `(set-logic QF_FP)` with `(error "unknown sort
/// 'BitVec'")`, which would silently drop every mixed script into the
/// "z3 unknown" arm and make the differential test a false pass. `QF_BVFP`
/// is a real z3 logic and accepts both sorts (confirmed manually: a script
/// declaring `bx : BitVec 8` and `fa,fb : Float32` under `QF_BVFP` returns a
/// concrete `sat`, exit code 0, whereas the same script under `QF_FP` errors
/// before reaching `check-sat`). This is a SIBLING to `z3_outcome_arith` so
/// the existing pure-FP oracle callers (`differential_qf_fp_add_sub`,
/// `differential_qf_fp_rounding_free`, etc.) keep using `QF_FP` unchanged.
fn z3_outcome_mixed(ctx: &mut easy_smt::Context, src: &str) -> easy_smt::Response {
    ctx.set_logic("QF_BVFP").expect("z3 set-logic failed");
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

#[test]
fn differential_qf_bvfp_mixed() {
    let mut rng = Lcg(0xB0FE_1234);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    // Counts iterations where z3 returned a CONCRETE verdict (Sat or Unsat,
    // not Unknown/error). Guards against the E2 false-pass: if z3 rejected
    // every mixed script (e.g. wrong logic), this would stay 0 even though
    // n_sat/n_unsat (computed from OUR outcomes) could still be > 0.
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_mixed_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_mixed(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => {
                n_z3_checked += 1;
            }
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => {
                n_z3_checked += 1;
            }
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_BVFP MIXED SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_bvfp_mixed: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0,
        "expected some SAT results ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(
        n_unsat > 0,
        "expected some UNSAT results ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(
        n_z3_checked > 0,
        "z3 never returned a concrete verdict — differential oracle did no real work"
    );
}

/// One BV→FP bitcast script: constrain a 32-bit BV var to a value, bitcast it to
/// Float32 two ways — `(fp sign exp sig)` slicing the BV, and 1-arg `to_fp` of
/// the whole BV — and relate the results with a random FP relation. Exercises
/// both bitcast faces against z3 under QF_BVFP.
fn gen_bitcast_script(rng: &mut Lcg) -> String {
    // A uniform-random 32-bit pattern (full field coverage — observed sat/unsat/z3-checked all > 0).
    let hi = (rng.next() & 0xffff) as u32;
    let lo = (rng.next() & 0xffff) as u32;
    let word = (hi << 16) | lo;
    const FP_RELS: &[&str] = &["fp.lt", "fp.leq", "fp.gt", "fp.geq", "fp.eq"];
    let fp_rel = FP_RELS[rng.below(FP_RELS.len() as u64) as usize];
    // Slice the 32-bit constant into sign(1) / exp(8) / sig(23) literal fields
    // so the (fp …) form and the 1-arg to_fp form describe the SAME value.
    let sign = (word >> 31) & 0x1;
    let exp = (word >> 23) & 0xff;
    let sig = word & 0x7f_ffff;
    format!(
        "(declare-fun b () (_ BitVec 32))\n\
         (declare-fun p () (_ FloatingPoint 8 24))\n\
         (declare-fun q () (_ FloatingPoint 8 24))\n\
         (assert (= b (_ bv{word} 32)))\n\
         (assert (= p (fp (_ bv{sign} 1) (_ bv{exp} 8) (_ bv{sig} 23))))\n\
         (assert (= q ((_ to_fp 8 24) b)))\n\
         (assert ({fp_rel} p q))\n\
         (check-sat)\n"
    )
}

#[test]
fn differential_qf_bvfp_bitcast() {
    let mut rng = Lcg(0x4C_B17_CA5);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_bitcast_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_mixed(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_BVFP BITCAST SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_bvfp_bitcast: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(
        n_z3_checked > 0,
        "z3 never returned a concrete verdict — check the logic/harness"
    );
}

/// One int→FP script: a constant BV converted BOTH ways — signed 2-arg `to_fp`
/// and `to_fp_unsigned` — under a random rounding mode and target format, then
/// related with a random FP relation. Signed and unsigned reads agree exactly
/// when the top bit is clear and diverge otherwise, so the relation verdict is
/// mode-, format- and sign-sensitive. Verdicts are decidable (constant source).
fn gen_int_to_fp_script(rng: &mut Lcg) -> String {
    const WIDTHS: &[u32] = &[8, 16, 32];
    let mw = WIDTHS[rng.below(WIDTHS.len() as u64) as usize];
    let word = rng.next() & ((1u64 << mw) - 1);
    // Half Float32, half Float16 — Float16 overflows on large 16/32-bit values
    // (mode-dependent: RNE→+oo, RTZ→max finite), which is exactly the boundary
    // we want cross-checked.
    let (eb, sb) = if rng.below(2) == 0 {
        (8u32, 24u32)
    } else {
        (5, 11)
    };
    const FP_RELS: &[&str] = &["fp.lt", "fp.leq", "fp.gt", "fp.geq", "fp.eq"];
    let rel = FP_RELS[rng.below(FP_RELS.len() as u64) as usize];
    const RMS: &[&str] = &["RNE", "RNA", "RTP", "RTN", "RTZ"];
    let rm = RMS[rng.below(RMS.len() as u64) as usize];
    format!(
        "(declare-fun b () (_ BitVec {mw}))\n\
         (declare-fun p () (_ FloatingPoint {eb} {sb}))\n\
         (declare-fun q () (_ FloatingPoint {eb} {sb}))\n\
         (assert (= b (_ bv{word} {mw})))\n\
         (assert (= p ((_ to_fp {eb} {sb}) {rm} b)))\n\
         (assert (= q ((_ to_fp_unsigned {eb} {sb}) {rm} b)))\n\
         (assert ({rel} p q))\n\
         (check-sat)\n"
    )
}

#[test]
fn differential_qf_bvfp_int_to_fp() {
    let mut rng = Lcg(0x1_2FE_4D4D);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_int_to_fp_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_mixed(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_BVFP INT→FP SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_bvfp_int_to_fp: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(
        n_z3_checked > 0,
        "z3 never returned a concrete verdict — check the logic/harness"
    );
}

/// FP→BV: a random source bit-pattern (naturally hitting NaN/±inf/subnormal/
/// out-of-range) pinned via the 1-arg to_fp bitcast, converted under a random
/// face/width/mode, then related to a random BV constant. One in four scripts
/// is instead a two-application congruence probe (equal-forced operands,
/// distinct results) — the encoding must agree with z3's UF-of-(rm,x) reading.
fn gen_fp_to_bv_script(rng: &mut Lcg) -> String {
    const MS: &[u32] = &[4, 8, 16];
    let m = MS[rng.below(MS.len() as u64) as usize];
    let (eb, sb) = if rng.below(2) == 0 {
        (5u32, 11u32)
    } else {
        (8, 24)
    };
    let w = (eb + sb) as usize;
    let bits = rng.next() & if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let face = if rng.below(2) == 0 {
        "fp.to_ubv"
    } else {
        "fp.to_sbv"
    };
    const RMS: &[&str] = &["RNE", "RNA", "RTP", "RTN", "RTZ"];
    let rm = RMS[rng.below(RMS.len() as u64) as usize];
    if rng.below(4) == 0 {
        return format!(
            "(declare-fun x () (_ FloatingPoint {eb} {sb}))\n\
             (declare-fun y () (_ FloatingPoint {eb} {sb}))\n\
             (assert (= x ((_ to_fp {eb} {sb}) #b{bits:0w$b})))\n\
             (assert (= y x))\n\
             (assert (distinct ((_ {face} {m}) {rm} x) ((_ {face} {m}) {rm} y)))\n\
             (check-sat)\n"
        );
    }
    let k = rng.next() & ((1u64 << m) - 1);
    const RELS: &[&str] = &["=", "bvult", "bvule", "bvugt"];
    let rel = RELS[rng.below(RELS.len() as u64) as usize];
    let mw = m as usize;
    format!(
        "(declare-fun x () (_ FloatingPoint {eb} {sb}))\n\
         (declare-fun a () (_ BitVec {m}))\n\
         (assert (= x ((_ to_fp {eb} {sb}) #b{bits:0w$b})))\n\
         (assert (= a ((_ {face} {m}) {rm} x)))\n\
         (assert ({rel} a #b{k:0mw$b}))\n\
         (check-sat)\n"
    )
}

#[test]
fn differential_qf_bvfp_fp_to_bv() {
    let mut rng = Lcg(0x4E_F92A_11);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_fp_to_bv_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_mixed(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_BVFP FP→BV SOUNDNESS DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_bvfp_fp_to_bv: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(
        n_unknown == 0,
        "no admitted-face script may fence ({n_unknown} unknown)"
    );
    assert!(n_z3_checked > 0, "z3 never returned a concrete verdict");
}

/// BV operand pool for the ite/n-ary oracle: three free bytes plus the two
/// all-zero/all-one constants, mirroring the brief's `<bv>` pool.
const BVFP_ITE_BV_OPS: &[&str] = &["u", "v", "w", "#x00", "#xff"];

/// Draw a random `<cond>` for a word-ite: the two atoms directly, the two
/// cross-sort atoms (`bvult`, `fp.lt`), a conjunction, and a Bool-sorted
/// `ite` — the last exercises the word_norm ite-elimination pass on a
/// Bool-typed ite nested inside a BV/FP/RM-typed one.
fn gen_ite_cond(rng: &mut Lcg) -> String {
    match rng.below(6) {
        0 => "p".to_string(),
        1 => "(not p)".to_string(),
        2 => "(bvult u v)".to_string(),
        3 => "(fp.lt x y)".to_string(),
        4 => "(and p (bvult u v))".to_string(),
        _ => "(ite p (fp.lt x y) (bvult u v))".to_string(),
    }
}

/// Draw a random FP operand: `x`/`y` or one of the FP32 special constants.
fn gen_ite_fp_operand(rng: &mut Lcg) -> String {
    if rng.below(2) == 0 {
        if rng.below(2) == 0 {
            "x".to_string()
        } else {
            "y".to_string()
        }
    } else {
        FP32_SPECIALS[rng.below(FP32_SPECIALS.len() as u64) as usize].to_string()
    }
}

/// Draw a random BV operand from `BVFP_ITE_BV_OPS`.
fn gen_ite_bv_operand(rng: &mut Lcg) -> String {
    BVFP_ITE_BV_OPS[rng.below(BVFP_ITE_BV_OPS.len() as u64) as usize].to_string()
}

/// Generate one assertion drawn from the 6 families the slice landed:
/// word-level ite over FP, word-level ite over BV, n-ary `distinct`, n-ary
/// `=`, RM equality atoms, and an RM-typed ite feeding a rounded FP op.
fn gen_ite_assertion(rng: &mut Lcg) -> String {
    match rng.below(6) {
        0 => {
            // (= (ite <cond> <fp> <fp>) <fp>)
            let cond = gen_ite_cond(rng);
            let a = gen_ite_fp_operand(rng);
            let b = gen_ite_fp_operand(rng);
            let c = gen_ite_fp_operand(rng);
            format!("(= (ite {cond} {a} {b}) {c})")
        }
        1 => {
            // (bvult (ite <cond> <bv> <bv>) <bv>) or (= (ite <cond> <bv> <bv>) <bv>)
            let cond = gen_ite_cond(rng);
            let a = gen_ite_bv_operand(rng);
            let b = gen_ite_bv_operand(rng);
            let c = gen_ite_bv_operand(rng);
            if rng.below(2) == 0 {
                format!("(bvult (ite {cond} {a} {b}) {c})")
            } else {
                format!("(= (ite {cond} {a} {b}) {c})")
            }
        }
        2 => {
            // (distinct t1 t2 t3), all-BV or all-FP
            if rng.below(2) == 0 {
                let (a, b, c) = (
                    gen_ite_bv_operand(rng),
                    gen_ite_bv_operand(rng),
                    gen_ite_bv_operand(rng),
                );
                format!("(distinct {a} {b} {c})")
            } else {
                let (a, b, c) = (
                    gen_ite_fp_operand(rng),
                    gen_ite_fp_operand(rng),
                    gen_ite_fp_operand(rng),
                );
                format!("(distinct {a} {b} {c})")
            }
        }
        3 => {
            // (= t1 t2 t3), all-BV or all-FP
            if rng.below(2) == 0 {
                let (a, b, c) = (
                    gen_ite_bv_operand(rng),
                    gen_ite_bv_operand(rng),
                    gen_ite_bv_operand(rng),
                );
                format!("(= {a} {b} {c})")
            } else {
                let (a, b, c) = (
                    gen_ite_fp_operand(rng),
                    gen_ite_fp_operand(rng),
                    gen_ite_fp_operand(rng),
                );
                format!("(= {a} {b} {c})")
            }
        }
        4 => {
            // RM atoms: (= r <lit>) or (distinct r <lit> <lit>)
            if rng.below(2) == 0 {
                let lit = RMS[rng.below(RMS.len() as u64) as usize];
                format!("(= r {lit})")
            } else {
                let l1 = RMS[rng.below(RMS.len() as u64) as usize];
                let l2 = RMS[rng.below(RMS.len() as u64) as usize];
                format!("(distinct r {l1} {l2})")
            }
        }
        _ => {
            // (fp.eq (fp.add (ite <cond> <RM-literal> <RM-literal>) x y) x)
            let cond = gen_ite_cond(rng);
            let l1 = RMS[rng.below(RMS.len() as u64) as usize];
            let l2 = RMS[rng.below(RMS.len() as u64) as usize];
            format!("(fp.eq (fp.add (ite {cond} {l1} {l2}) x y) x)")
        }
    }
}

/// Generate a full QF_BVFP script exercising word-level ite over BV/FP/RM,
/// n-ary `=`/`distinct` expansion, and RM equality atoms — the surface
/// slice 5 landed (word_norm pass wired first in check_sat, RM equality
/// blasting, RM→FP routing, model hygiene). Declares `p:Bool`, `x,y:Float32`,
/// `u,v,w:(_ BitVec 8)`, `r:RoundingMode`, then 1..=3 assertions each drawn
/// from `gen_ite_assertion`.
fn gen_ite_script(rng: &mut Lcg) -> String {
    let mut s = String::from(
        "(declare-fun p () Bool)\n\
         (declare-fun x () (_ FloatingPoint 8 24))\n\
         (declare-fun y () (_ FloatingPoint 8 24))\n\
         (declare-fun u () (_ BitVec 8))\n\
         (declare-fun v () (_ BitVec 8))\n\
         (declare-fun w () (_ BitVec 8))\n\
         (declare-fun r () RoundingMode)\n",
    );
    let n_asserts = 1 + rng.below(3) as usize; // 1..=3
    for _ in 0..n_asserts {
        s.push_str(&format!("(assert {})\n", gen_ite_assertion(rng)));
    }
    s.push_str("(check-sat)\n");
    s
}

#[test]
fn differential_qf_bvfp_ite() {
    let mut rng = Lcg(0x17E_1234_ABCD);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    let mut n_z3_checked = 0usize;
    for iter in 0..N_ITERS {
        let src = gen_ite_script(&mut rng);
        let ours = shinri_outcome(&src);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
            continue;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => unreachable!(),
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_mixed(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_z3_checked += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_z3_checked += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!(
                "QF_BVFP ite DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n\
                 script:\n{src}"
            ),
        }
    }
    println!(
        "differential_qf_bvfp_ite: sat={n_sat} unsat={n_unsat} unknown={n_unknown} \
         z3_checked={n_z3_checked}"
    );
    assert!(
        n_sat > 0 && n_unsat > 0,
        "expected SAT and UNSAT coverage ({n_sat} sat, {n_unsat} unsat, {n_unknown} unknown)"
    );
    assert!(
        n_unknown == 0,
        "unknown must be 0 post-slice ({n_unknown} unknown)"
    );
    assert!(
        n_z3_checked == N_ITERS,
        "expected every iteration z3-checked with zero disagreements \
         ({n_z3_checked}/{N_ITERS} checked)"
    );
}

/// Constant-source `fp.to_real` oracle (slice 9, Task 6): binds `x` to a random
/// Float16 literal via the exact `(fp s e sig)` triple, then constrains
/// `(fp.to_real x)` against a random integer bound via LRA `<=`. Since `x` is
/// fully constant, both solvers must decide — this is the zero-Unknown gate
/// on the Real-bridge seam (spec §5/§7): no admitted `fp.to_real` instance may
/// fence to Unknown once the operand is concrete.
#[cfg(feature = "oracle")]
fn gen_to_real_script(rng: &mut Lcg) -> String {
    let bits = (rng.next() & 0xFFFF) as u16;
    let s = (bits >> 15) & 1;
    let e = (bits >> 10) & 0x1F;
    let sig = bits & 0x3FF;
    let bound = (rng.next() % 21) as i64 - 10; // integer bound in [-10,10]
                                               // SMT-LIB decimals have no sign; negative bounds must use `(- n.0)`.
    let bound_term = if bound < 0 {
        format!("(- {}.0)", -bound)
    } else {
        format!("{bound}.0")
    };
    format!(
        "(declare-fun x () Float16)\n\
         (assert (= x (fp #b{s:01b} #b{e:05b} #b{sig:010b})))\n\
         (assert (<= (fp.to_real x) {bound_term}))\n\
         (check-sat)\n"
    )
}

#[cfg(feature = "oracle")]
#[test]
fn differential_qf_fp_to_real() {
    let mut rng = Lcg(0xB000_0BEE_F001);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let s = gen_to_real_script(&mut rng);
        let ours = shinri_outcome(&s);
        if ours == SolveOutcome::Unknown {
            n_unknown += 1;
        }
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => {}
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &s);
        assert!(
            !matches!(
                (ours, theirs),
                (SolveOutcome::Sat, easy_smt::Response::Unsat)
                    | (SolveOutcome::Unsat, easy_smt::Response::Sat)
            ),
            "QF_FP fp.to_real DISAGREEMENT (iter {iter}): shinri={ours:?} z3={theirs:?}\n{s}"
        );
    }
    println!("differential_qf_fp_to_real: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(
        n_sat > 0 && n_unsat > 0,
        "oracle produced no SAT/UNSAT coverage"
    );
    assert_eq!(
        n_unknown, 0,
        "constant-source fp.to_real must never fence ({n_unknown})"
    );
}

/// Functionality pin (spec §5/§7): `fp.to_real` must be a genuine function even
/// over NaN payloads. If `x = y` and both are NaN, then `fp.to_real x = fp.to_real y`
/// must hold — i.e. asserting the negation must be Unsat. This is a fixed
/// (non-fuzzed) instance pinned against z3 so neither solver treats `fp.to_real`
/// as non-functional over the NaN equivalence class.
#[cfg(feature = "oracle")]
#[test]
fn differential_qf_fp_to_real_nan_functionality() {
    let s = "(declare-fun x () Float16)\n\
             (declare-fun y () Float16)\n\
             (assert (fp.isNaN x))\n\
             (assert (fp.isNaN y))\n\
             (assert (= x y))\n\
             (assert (not (= (fp.to_real x) (fp.to_real y))))\n\
             (check-sat)\n";
    let ours = shinri_outcome(s);
    let mut ctx = easy_smt::ContextBuilder::new()
        .solver("z3", ["-smt2", "-in"])
        .build()
        .expect("failed to launch z3 — ensure z3 is on PATH");
    let theirs = z3_outcome_arith(&mut ctx, s);
    assert_eq!(
        ours,
        SolveOutcome::Unsat,
        "fp.to_real must be functional over NaN (x=y both NaN ⇒ to_real x = to_real y): \
         shinri returned {ours:?}\n{s}"
    );
    assert!(
        !matches!(
            (ours, theirs),
            (SolveOutcome::Sat, easy_smt::Response::Unsat)
                | (SolveOutcome::Unsat, easy_smt::Response::Sat)
        ),
        "QF_FP fp.to_real NaN-functionality DISAGREEMENT: shinri={ours:?} z3={theirs:?}\n{s}"
    );
}

/// QF_UFLRA + bridge differential oracle (slice 9 broadening): the `fp.to_real`
/// Real-bridge is admitted mixed with EUF over the resulting Real. This fuzzes
/// DECIDABLE queries that link a constant-source `(fp.to_real x)` to an
/// uninterpreted `(f a)` (EUF-structure, `f: Real -> Real`) and a random integer
/// bound, pinning every instance against z3 with ZERO tolerated disagreements.
///
/// Because `x` is a concrete Float16 literal and `(= (f a) (fp.to_real x))`
/// pins `(f a)` to that concrete real, the outer relation `(<op> (f a) bound)`
/// is fully decidable — both solvers must decide, and must AGREE. A single
/// disagreement (our Sat vs z3 Unsat, or our Unsat vs z3 Sat) would prove the
/// broadened QF_UFLRA + bridge scope UNSOUND (the reverted fence necessary).
///
/// Soundness rests on the Combiner's Nelson–Oppen EUF⋈Arith combination
/// deciding the shared-Real interface between the bridged `fp.to_real` value
/// and the uninterpreted `f`. Coverage here is EUF-over-Real; Array/Str-Real
/// operands are admitted by the Real-sorted recognizer but not exercised (see
/// spec §6 FOLLOW-UP note).
#[cfg(feature = "oracle")]
fn gen_to_real_uflra_script(rng: &mut Lcg) -> String {
    let bits = (rng.next() & 0xFFFF) as u16;
    let s = (bits >> 15) & 1;
    let e = (bits >> 10) & 0x1F;
    let sig = bits & 0x3FF;
    let bound = (rng.next() % 21) as i64 - 10; // integer bound in [-10,10]
    let bound_term = if bound < 0 {
        format!("(- {}.0)", -bound)
    } else {
        format!("{bound}.0")
    };
    // Vary the outer relation so both SAT and UNSAT witnesses arise: `=` yields
    // mostly UNSAT, the inequalities yield a mix depending on the literal's real
    // value vs. the bound.
    let ops = ["<=", "<", ">=", ">", "="];
    let op = ops[(rng.next() % ops.len() as u64) as usize];
    format!(
        "(declare-fun x () Float16)\n\
         (declare-fun f (Real) Real)\n\
         (declare-fun a () Real)\n\
         (assert (= x (fp #b{s:01b} #b{e:05b} #b{sig:010b})))\n\
         (assert (= (f a) (fp.to_real x)))\n\
         (assert ({op} (f a) {bound_term}))\n\
         (check-sat)\n"
    )
}

#[cfg(feature = "oracle")]
#[test]
fn differential_qf_fp_to_real_uflra() {
    // Fixed NaN/EUF functionality pin (spec §5/§7 composed with EUF): if x=y and
    // both NaN, then f(to_real x) = f(to_real y) — asserting the negation is
    // Unsat. Verifies fp.to_real functionality composes through an uninterpreted
    // f under the broadened QF_UFLRA + bridge scope.
    {
        let s = "(declare-fun x () Float16)\n\
                 (declare-fun y () Float16)\n\
                 (declare-fun f (Real) Real)\n\
                 (assert (fp.isNaN x))\n\
                 (assert (fp.isNaN y))\n\
                 (assert (= x y))\n\
                 (assert (not (= (f (fp.to_real x)) (f (fp.to_real y)))))\n\
                 (check-sat)\n";
        let ours = shinri_outcome(s);
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, s);
        assert_eq!(
            ours,
            SolveOutcome::Unsat,
            "fp.to_real functionality must compose with EUF (x=y both NaN ⇒ \
             f(to_real x) = f(to_real y)): shinri returned {ours:?}\n{s}"
        );
        assert!(
            !matches!(
                (ours, theirs),
                (SolveOutcome::Sat, easy_smt::Response::Unsat)
                    | (SolveOutcome::Unsat, easy_smt::Response::Sat)
            ),
            "QF_UFLRA+bridge NaN/EUF-functionality DISAGREEMENT: shinri={ours:?} z3={theirs:?}\n{s}"
        );
    }

    let mut rng = Lcg(0xF13_A5EE_D009_u64);
    let (mut n_sat, mut n_unsat, mut n_unknown) = (0usize, 0usize, 0usize);
    for iter in 0..N_ITERS {
        let s = gen_to_real_uflra_script(&mut rng);
        let ours = shinri_outcome(&s);
        match ours {
            SolveOutcome::Sat => n_sat += 1,
            SolveOutcome::Unsat => n_unsat += 1,
            SolveOutcome::Unknown => n_unknown += 1,
        }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"])
            .build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &s);
        assert!(
            !matches!(
                (ours, theirs),
                (SolveOutcome::Sat, easy_smt::Response::Unsat)
                    | (SolveOutcome::Unsat, easy_smt::Response::Sat)
            ),
            "QF_UFLRA+bridge DISAGREEMENT (iter {iter}): shinri={ours:?} z3={theirs:?}\n{s}"
        );
    }
    println!("differential_qf_fp_to_real_uflra: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(
        n_sat > 0 && n_unsat > 0,
        "QF_UFLRA+bridge oracle produced no SAT/UNSAT coverage (sat={n_sat} unsat={n_unsat})"
    );
}
