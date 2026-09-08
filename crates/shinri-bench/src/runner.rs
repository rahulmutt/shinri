//! The worker pool: run one instance, or a whole corpus, into a resumable
//! results file.
//!
//! A worker never aborts the run — an unreadable file or a wrapper that will
//! not spawn becomes a `malformed:…` row, so one bad instance out of six
//! thousand costs one row, not the run. The oracles are consulted lazily, in
//! z3-then-cvc5 order, and only while `classify` still says `NeedsOracle`.

use crate::instance::Instance;
use crate::oracle::Oracle;
use crate::process::{run_limited, Limits};
use crate::results::{ResultsFile, Row};
use crate::verdict::{classify, Answer, Observed, OracleAnswers, Verdict};
use std::collections::{HashSet, VecDeque};
use std::io;
use std::sync::{mpsc, Mutex};

/// Everything one run needs: what to invoke, under what limits, how wide,
/// and which oracles to fall back on.
pub struct RunConfig {
    pub solver: String,
    pub solver_args: Vec<String>,
    pub limits: Limits,
    pub jobs: usize,
    pub oracle: Oracle,
}

/// The most stderr we keep per row.
const STDERR_HEAD_BYTES: usize = 2048;

/// Run one instance and classify it. Never panics; never returns an error.
pub fn run_one(inst: &Instance, cfg: &RunConfig) -> Row {
    // Probe readability first: a permission or I/O error here is the
    // harness's problem, not the solver's, and must not read as a crash.
    if let Err(e) = std::fs::File::open(&inst.abs_path) {
        return bare_row(inst, Verdict::Malformed(format!("unreadable: {e}")));
    }

    let file = inst.abs_path.to_string_lossy().into_owned();
    let mut args: Vec<&str> = cfg.solver_args.iter().map(String::as_str).collect();
    args.push(&file);
    let exec = run_limited(&cfg.solver, &args, &cfg.limits);
    if let Some(err) = &exec.spawn_error {
        return bare_row(inst, Verdict::Malformed(format!("spawn: {err}")));
    }

    let (answers, stdout_errors) = parse_answers(&exec.stdout);
    let fence = parse_stats_fence(&exec.stderr);
    let mut stderr_head = strip_stats(&exec.stderr, STDERR_HEAD_BYTES);

    let observe = |oracle: Option<&OracleAnswers>| -> Verdict {
        classify(&Observed {
            rc: exec.rc,
            killed_by_timeout: exec.killed_by_timeout,
            answers: &answers,
            stderr: &exec.stderr,
            fence: fence.as_deref(),
            status: inst.status,
            oracle,
            stdout_errors,
        })
    };

    // Escalate only as far as the classifier actually needs.
    let mut oracle: Option<OracleAnswers> = None;
    let mut verdict = observe(None);
    if verdict == Verdict::NeedsOracle {
        oracle = Some(OracleAnswers {
            z3: Some(cfg.oracle.z3(&inst.abs_path, &cfg.limits)),
            cvc5: None,
        });
        verdict = observe(oracle.as_ref());
        if verdict == Verdict::NeedsOracle {
            if let Some(answers) = oracle.as_mut() {
                answers.cvc5 = Some(cfg.oracle.cvc5(&inst.abs_path, &cfg.limits));
            }
            verdict = observe(oracle.as_ref());
        }
    }
    if verdict == Verdict::NeedsOracle {
        // Unreachable: `classify` settles once both oracles are present.
        // Recorded rather than panicked so a future classifier change costs
        // one honest row instead of a dead worker.
        verdict = Verdict::Unverified;
        stderr_head = strip_stats(
            &format!(
                "shinri-bench: classifier still needed an oracle after z3 and cvc5\n{}",
                exec.stderr
            ),
            STDERR_HEAD_BYTES,
        );
    }

    Row {
        path: inst.rel_path.clone(),
        logic: inst.logic.clone(),
        bytes: inst.bytes,
        status: inst.status,
        rc: exec.rc,
        wall_ms: exec.wall_ms,
        answers,
        fence,
        stderr_head,
        verdict,
        oracle,
    }
}

/// A row for an instance that never reached the solver.
fn bare_row(inst: &Instance, verdict: Verdict) -> Row {
    Row {
        path: inst.rel_path.clone(),
        logic: inst.logic.clone(),
        bytes: inst.bytes,
        status: inst.status,
        rc: None,
        wall_ms: 0,
        answers: Vec::new(),
        fence: None,
        stderr_head: String::new(),
        verdict,
        oracle: None,
    }
}

/// Run every instance not already in `skip`, appending each row as it lands
/// so a killed run resumes from the file. Returns the first append error,
/// which aborts the run — rows already written stay valid.
pub fn run_all(
    instances: Vec<Instance>,
    cfg: &RunConfig,
    results: &mut ResultsFile,
    skip: &HashSet<String>,
    progress: &mut dyn FnMut(usize, usize, &Verdict),
) -> io::Result<()> {
    let pending: VecDeque<Instance> = instances
        .into_iter()
        .filter(|inst| !skip.contains(&inst.rel_path))
        .collect();
    let total = pending.len();
    if total == 0 {
        return Ok(());
    }
    let queue = Mutex::new(pending);
    let (tx, rx) = mpsc::channel::<Row>();
    let jobs = cfg.jobs.max(1).min(total);

    let mut failure: Option<io::Error> = None;
    std::thread::scope(|scope| {
        for _ in 0..jobs {
            let tx = tx.clone();
            let queue = &queue;
            scope.spawn(move || loop {
                let next = queue.lock().unwrap_or_else(|e| e.into_inner()).pop_front();
                let Some(inst) = next else { break };
                // A send error means the receiver gave up (append failed):
                // stop pulling work rather than finishing a doomed run.
                if tx.send(run_one(&inst, cfg)).is_err() {
                    break;
                }
            });
        }
        // Only the workers' clones keep the channel open, so the loop below
        // ends exactly when the last worker finishes.
        drop(tx);

        let mut done = 0usize;
        while let Ok(row) = rx.recv() {
            done += 1;
            if let Err(e) = results.append(&row) {
                failure = Some(e);
                break;
            }
            progress(done, total, &row.verdict);
        }
        // Dropping the receiver unblocks the workers' sends immediately, so
        // an append failure does not wait out the rest of the corpus.
        drop(rx);
    });

    match failure {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// The `fence=` tag of the last `stats:` line, or `None` for `-` / absent.
pub fn parse_stats_fence(stderr: &str) -> Option<String> {
    let last = stderr
        .lines()
        .rev()
        .find(|line| line.trim_start().starts_with("stats:"))?;
    let tag = last
        .split_whitespace()
        .find_map(|field| field.strip_prefix("fence="))?;
    if tag == "-" {
        None
    } else {
        Some(tag.to_string())
    }
}

/// `stderr` minus its `stats:` lines, truncated to the largest character
/// boundary at or below `max` bytes.
pub fn strip_stats(stderr: &str, max: usize) -> String {
    let kept: String = stderr
        .split_inclusive('\n')
        .filter(|line| !line.trim_start().starts_with("stats:"))
        .collect();
    let mut end = max.min(kept.len());
    while end > 0 && !kept.is_char_boundary(end) {
        end -= 1;
    }
    kept[..end].to_string()
}

/// The solver's answers in order, plus the number of `(error …)` lines that
/// preceded the first one. Anything else on stdout — `success` acks, models,
/// banners — is ignored.
pub fn parse_answers(stdout: &str) -> (Vec<Answer>, usize) {
    let mut answers = Vec::new();
    let mut errors = 0usize;
    for line in stdout.lines() {
        let trimmed = line.trim();
        match trimmed {
            "sat" => answers.push(Answer::Sat),
            "unsat" => answers.push(Answer::Unsat),
            "unknown" => answers.push(Answer::Unknown),
            _ => {
                if answers.is_empty() && trimmed.starts_with("(error") {
                    errors += 1;
                }
            }
        }
    }
    (answers, errors)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn answers_and_error_count() {
        assert_eq!(
            parse_answers("success\n(error \"x\")\nunsat\n"),
            (vec![Answer::Unsat], 1)
        );
        assert_eq!(
            parse_answers("sat\n(error \"after\")\n"),
            (vec![Answer::Sat], 0)
        );
        assert_eq!(parse_answers("(define-fun x () Int 3)\n"), (vec![], 0));
    }

    #[test]
    fn a_missing_file_is_a_malformed_row_not_an_abort() {
        let inst = Instance {
            rel_path: "QF_T/gone.smt2".into(),
            abs_path: std::path::PathBuf::from("/nonexistent/QF_T/gone.smt2"),
            logic: "QF_T".into(),
            bytes: 0,
            status: None,
        };
        let cfg = RunConfig {
            solver: "does-not-matter".into(),
            solver_args: Vec::new(),
            limits: Limits {
                timeout_s: 1,
                mem_mb: 64,
            },
            jobs: 1,
            oracle: Oracle::default(),
        };
        let row = run_one(&inst, &cfg);
        assert_eq!(row.path, "QF_T/gone.smt2");
        assert_eq!(row.rc, None);
        assert_eq!(row.wall_ms, 0);
        assert!(
            matches!(&row.verdict, Verdict::Malformed(r) if r.starts_with("unreadable: ")),
            "unexpected verdict: {:?}",
            row.verdict
        );
    }

    #[test]
    fn fence_from_last_stats_line() {
        assert_eq!(
            parse_stats_fence("stats: cmd=check-sat wall_ms=3 outcome=unknown fence=str-order\n"),
            Some("str-order".into())
        );
        assert_eq!(
            parse_stats_fence("stats: cmd=check-sat wall_ms=3 outcome=sat fence=-\n"),
            None
        );
        assert_eq!(parse_stats_fence("junk\n"), None);
    }

    #[test]
    fn stderr_head_drops_stats_and_truncates_on_char_boundary() {
        let s = "stats: cmd=check-sat wall_ms=1 outcome=sat fence=-\nerr é line\n";
        assert_eq!(strip_stats(s, 100), "err é line\n");
        assert_eq!(strip_stats(s, 5), "err ");
        assert_eq!(strip_stats(s, 6), "err \u{e9}");
    }
}
