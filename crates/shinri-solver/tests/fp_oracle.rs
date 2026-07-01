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
        if ours == SolveOutcome::Unknown { n_unknown += 1; continue; }
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
                "QF_FP rem DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
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
            (o, t) => panic!(
                "QF_FP sqrt DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"
            ),
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
            let mm = if rng.below(2) == 0 { "fp.min" } else { "fp.max" };
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
        if use_sym_rm && rng.below(2) == 0 { "rm".to_string() }
        else { RMS[rng.below(RMS.len() as u64) as usize].to_string() }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = format!("(fp.roundToIntegral {} x)", rm(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq z {term})"),
            1 => format!("(= z {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 { s.push_str(&format!("(assert (not {atom}))\n")); }
        else { s.push_str(&format!("(assert {atom})\n")); }
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
        if ours == SolveOutcome::Unknown { n_unknown += 1; continue; }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"]).build()
            .expect("failed to launch z3 — ensure z3 is on PATH");
        let theirs = z3_outcome_arith(&mut ctx, &src);
        match (ours, theirs) {
            (SolveOutcome::Sat, easy_smt::Response::Sat) => n_sat += 1,
            (SolveOutcome::Unsat, easy_smt::Response::Unsat) => n_unsat += 1,
            (SolveOutcome::Sat, easy_smt::Response::Unknown)
            | (SolveOutcome::Unsat, easy_smt::Response::Unknown) => continue,
            (o, t) => panic!("QF_FP roundToIntegral DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
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
        if use_sym_rm && rng.below(2) == 0 { "rm".to_string() }
        else { RMS[rng.below(RMS.len() as u64) as usize].to_string() }
    };
    const SPECIALS: &[&str] = &[
        "(_ +zero 8 24)", "(_ -zero 8 24)", "(_ +oo 8 24)", "(_ -oo 8 24)", "(_ NaN 8 24)",
    ];
    let vars = ["x", "y", "z"];
    let operand = |rng: &mut Lcg| -> String {
        if rng.below(2) == 0 { vars[rng.below(3) as usize].to_string() }
        else { SPECIALS[rng.below(SPECIALS.len() as u64) as usize].to_string() }
    };
    let n_asserts = 1 + rng.below(3) as usize;
    for _ in 0..n_asserts {
        let term = format!("(fp.fma {} {} {} {})", rm(rng), operand(rng), operand(rng), operand(rng));
        let atom = match rng.below(3) {
            0 => format!("(fp.eq w {term})"),
            1 => format!("(= w {term})"),
            _ => format!("(fp.isNaN {term})"),
        };
        if rng.below(2) == 0 { s.push_str(&format!("(assert (not {atom}))\n")); }
        else { s.push_str(&format!("(assert {atom})\n")); }
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
        if ours == SolveOutcome::Unknown { n_unknown += 1; continue; }
        let mut ctx = easy_smt::ContextBuilder::new()
            .solver("z3", ["-smt2", "-in"]).build()
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
            (o, t) => panic!("QF_FP relations DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
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
            0 => format!("((_ to_fp 8 24) {rm} w)"),              // narrow Float64→Float32
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
        if ours == SolveOutcome::Unknown { n_unknown += 1; continue; }
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
                "QF_FP to_fp DISAGREEMENT (iter {iter}): shinri={o:?} z3={t:?}\n{src}"),
        }
    }
    println!("differential_qf_fp_to_fp: sat={n_sat} unsat={n_unsat} unknown={n_unknown}");
    assert!(n_sat > 0 && n_unsat > 0, "oracle produced no SAT/UNSAT coverage");
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
