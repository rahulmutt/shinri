//! The reference oracles, consulted on demand.
//!
//! The runner only asks an oracle when a verdict cannot be settled from the
//! `:status` annotation alone (spec §5): the corpus is far too large to run
//! z3 and cvc5 over every instance. Both are invoked under the same limits
//! as the solver itself, and both are read the same way — the last decided
//! line on stdout wins, anything else is `unknown`.

use crate::process::{run_limited, Exec, Limits};
use crate::verdict::Answer;
use std::collections::HashSet;
use std::path::Path;
use std::sync::{Mutex, OnceLock};

/// The oracle programs to invoke. Defaults are the bare names, resolved on
/// `PATH`.
pub struct Oracle {
    pub z3: String,
    pub cvc5: String,
}

impl Default for Oracle {
    fn default() -> Self {
        Oracle {
            z3: "z3".to_string(),
            cvc5: "cvc5".to_string(),
        }
    }
}

impl Oracle {
    /// Ask z3 about `path`.
    pub fn z3(&self, path: &Path, limits: &Limits) -> Answer {
        let file = path.to_string_lossy().into_owned();
        answer_of(&self.z3, run_limited(&self.z3, &[&file], limits))
    }

    /// Ask cvc5 about `path`. cvc5 needs `--lang smt2` to read an `.smt2`
    /// file that has no shebang-style language hint.
    pub fn cvc5(&self, path: &Path, limits: &Limits) -> Answer {
        let file = path.to_string_lossy().into_owned();
        answer_of(
            &self.cvc5,
            run_limited(&self.cvc5, &["--lang", "smt2", &file], limits),
        )
    }
}

fn answer_of(program: &str, exec: Exec) -> Answer {
    if let Some(err) = &exec.spawn_error {
        warn_once(program, err);
        return Answer::Unknown;
    }
    if exec.killed_by_timeout {
        return Answer::Timeout;
    }
    // `prlimit` reports a missing program as 127; without this the whole run
    // would silently classify as `unverified` with no hint why.
    if exec.rc == Some(127) {
        warn_once(program, "exit 127 (not found or not executable)");
    }
    exec.stdout
        .lines()
        .rev()
        .find_map(|line| match line.trim() {
            "sat" => Some(Answer::Sat),
            "unsat" => Some(Answer::Unsat),
            "unknown" => Some(Answer::Unknown),
            _ => None,
        })
        .unwrap_or(Answer::Unknown)
}

/// One warning per oracle program per process: a missing z3 should be
/// visible once, not once per instance across a six-thousand-file run.
fn warn_once(program: &str, reason: &str) {
    static WARNED: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
    let warned = WARNED.get_or_init(|| Mutex::new(HashSet::new()));
    let mut warned = warned.lock().unwrap_or_else(|e| e.into_inner());
    if warned.insert(program.to_string()) {
        eprintln!("shinri-bench: warning: oracle '{program}' unavailable ({reason}); affected instances will be unverified");
    }
}
