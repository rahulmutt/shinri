//! Slice 44 — UF/BV congruence in the bit-blaster.
//!
//! Task 2 pins Fence 1: an uninterpreted application with a BV result sort
//! whose argument has no blastable word must fence to `unknown` rather than
//! reach the congruence arm (Task 3). Tasks 4, 5, 6 and 7 append more tests
//! to this file.

use shinri_parser::Parser;
use shinri_solver::{CommandResponse, Solver};

fn run_script(src: &str) -> Vec<String> {
    let mut solver = Solver::new();
    let mut parser = Parser::new(src);
    let mut out = Vec::new();
    while let Some(result) = parser.next_command(solver.ctx_mut()) {
        match result {
            Ok(cmd) => match solver.execute(cmd) {
                CommandResponse::None => {}
                CommandResponse::Sat => out.push("sat".into()),
                CommandResponse::Unsat => out.push("unsat".into()),
                CommandResponse::Unknown => out.push("unknown".into()),
                CommandResponse::Model(s) | CommandResponse::Values(s) => out.push(s),
                CommandResponse::Error(e) => out.push(format!("(error \"{e}\")")),
            },
            Err(diag) => out.push(format!("(error \"{}\")", diag.message)),
        }
    }
    out
}

/// Fence 1 (spec §4): an Int-sorted argument has no blastable word, so the
/// query fences to a SOUND `unknown` rather than reaching the congruence arm.
/// This is the spec §2.1 named decided → unknown exception.
#[test]
fn int_argument_to_a_bv_uf_fences_to_unknown() {
    let out = run_script(
        "(set-logic ALL)(declare-fun h (Int) (_ BitVec 8))(declare-fun n () Int)\
         (assert (= (h n) #x2a))(check-sat)",
    );
    assert_eq!(
        out.first().map(|s| s.as_str()),
        Some("unknown"),
        "got {out:?}"
    );
}
