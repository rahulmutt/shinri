//! The runner end-to-end over a six-file mini-corpus and a stub solver.
use shinri_bench::instance::walk;
use shinri_bench::oracle::Oracle;
use shinri_bench::process::{tools_available, Limits};
use shinri_bench::results::{read_all, Fixture, ResultsFile};
use shinri_bench::runner::{run_all, RunConfig};
use shinri_bench::verdict::Verdict;
use std::path::Path;

#[test]
fn six_verdicts_from_the_stub_solver() {
    if let Err(e) = tools_available() {
        eprintln!("skipping: {e}");
        return;
    }
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/corpus");
    let stub = corpus.join("stub-solver.sh");
    let insts = walk(&corpus, &["QF_T".into()]).unwrap();
    assert_eq!(insts.len(), 6);
    let out = std::env::temp_dir().join(format!("shinri-bench-e2e-{}.jsonl", std::process::id()));
    let _ = std::fs::remove_file(&out);
    let fx = Fixture {
        sha: "test".into(),
        version: "stub".into(),
        timeout_s: 2,
        mem_mb: 512,
        jobs: 3,
        cpu_max: "-".into(),
        memory_max: "-".into(),
        corpus: "mini".into(),
        started: "now".into(),
        solver: Some(stub.to_string_lossy().into_owned()),
        solver_md5: None,
    };
    let (mut rf, skip) = ResultsFile::open(&out, &fx).unwrap();
    let cfg = RunConfig {
        solver: stub.to_string_lossy().into_owned(),
        solver_args: vec!["--stats".into()],
        limits: Limits {
            timeout_s: 2,
            mem_mb: 512,
        },
        jobs: 3,
        // The stub is also the oracle: `lies.smt2` gets `sat` from "z3" and
        // "cvc5", so with :status unsat it lands on StatusSuspect.
        oracle: Oracle {
            z3: stub.to_string_lossy().into_owned(),
            cvc5: stub.to_string_lossy().into_owned(),
        },
    };
    let t0 = std::time::Instant::now();
    let mut seen_progress = Vec::new();
    run_all(insts, &cfg, &mut rf, &skip, &mut |done, total, v| {
        seen_progress.push((done, total, v.key()))
    })
    .unwrap();
    assert!(
        t0.elapsed().as_secs() < 8,
        "pool did not overlap or kill: {:?}",
        t0.elapsed()
    );
    assert_eq!(seen_progress.len(), 6);
    assert_eq!(seen_progress[5].0, 6);
    assert!(seen_progress.iter().all(|(_, total, _)| *total == 6));
    let (_, rows) = read_all(&out).unwrap();
    let by: std::collections::HashMap<_, _> = rows
        .iter()
        .map(|r| (r.path.clone(), r.verdict.clone()))
        .collect();
    assert_eq!(by["QF_T/sat.smt2"], Verdict::Correct);
    assert_eq!(by["QF_T/unsat.smt2"], Verdict::Correct);
    assert_eq!(by["QF_T/lies.smt2"], Verdict::StatusSuspect);
    assert_eq!(by["QF_T/slow.smt2"], Verdict::Timeout);
    assert_eq!(by["QF_T/hog.smt2"], Verdict::Oom);
    assert_eq!(by["QF_T/crash.smt2"], Verdict::Panic);
    let lies = rows.iter().find(|r| r.path == "QF_T/lies.smt2").unwrap();
    assert_eq!(
        lies.oracle.as_ref().unwrap().z3,
        Some(shinri_bench::verdict::Answer::Sat)
    );
    // Resume: a second open reports all six as done.
    let (_, seen) = ResultsFile::open(&out, &fx).unwrap();
    assert_eq!(seen.len(), 6);
    std::fs::remove_file(out).unwrap();
}
