//! The end-to-end differential oracle lives in `shinri-solver` (it needs the
//! concrete `Euf` theory, which `shinri-theory` cannot depend on without
//! inverting the crate graph). See `crates/shinri-solver/tests/oracle.rs`,
//! run with `--features oracle` and a `z3` binary on PATH.

#![cfg(feature = "oracle")]

#[test]
#[ignore = "live in shinri-solver/tests/oracle.rs (differential_qf_uflia_small, --features oracle); \
            Combiner<Euf, Arith> activated for QF_UFLIA via MBTC"]
fn qf_uflra_matches_z3() {
    // Construction sketch (filled in when concrete theories land):
    //   let mut ctx = easy_smt::ContextBuilder::new().solver("z3", ["-in"]).build().unwrap();
    //   for each generated QF_UFLRA instance:
    //     let ours = solve_with_combiner(&instance);   // Combiner<Euf, Arith>
    //     let theirs = ask_z3(&mut ctx, &instance);
    //     assert_eq!(ours.is_sat(), theirs.is_sat(), "differential disagreement");
    //   on SAT: validate our model; on UNSAT: recheck our CertLog.
}
