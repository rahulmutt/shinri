//! Differential QF_UFLRA harness vs an external z3 (spec §10). Inert until
//! shinri-euf/shinri-arith provide concrete theories for `Combiner<Euf, Arith>`;
//! until then there is no end-to-end solve to diff. Gated behind `--features
//! oracle` and `#[ignore]` so CI does not require a z3 binary yet.

#![cfg(feature = "oracle")]

#[test]
#[ignore = "activates when Combiner<Euf, Arith> exists (shinri-euf/arith)"]
fn qf_uflra_matches_z3() {
    // Construction sketch (filled in when concrete theories land):
    //   let mut ctx = easy_smt::ContextBuilder::new().solver("z3", ["-in"]).build().unwrap();
    //   for each generated QF_UFLRA instance:
    //     let ours = solve_with_combiner(&instance);   // Combiner<Euf, Arith>
    //     let theirs = ask_z3(&mut ctx, &instance);
    //     assert_eq!(ours.is_sat(), theirs.is_sat(), "differential disagreement");
    //   on SAT: validate our model; on UNSAT: recheck our CertLog.
}
