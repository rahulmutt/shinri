//! Limited subprocess execution.
//!
//! Every solver and oracle invocation goes through [`run_limited`], which
//! wraps the program in the spec's limit chain
//!
//! ```text
//! prlimit --as=<mem_mb MiB> timeout -s KILL <t+1> timeout <t> <program> <args…>
//! ```
//!
//! The inner `timeout` sends `TERM` at the wall-clock budget; the outer one
//! escalates to `KILL` a second later so a solver that ignores `TERM` still
//! dies. `timeout` signals the child's whole process group, so no descendant
//! outlives the run. stdin is closed (a benchmark run is never interactive)
//! and both pipes are drained on their own threads, so a solver that fills
//! the 64 KiB pipe buffer on either stream cannot deadlock the harness.

use std::io::Read;
use std::process::{Command, Stdio};
use std::time::Instant;

/// Per-instance resource budget.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub timeout_s: u64,
    pub mem_mb: u64,
}

/// The outcome of one limited invocation.
#[derive(Clone, Debug, Default)]
pub struct Exec {
    /// Exit status, or `None` if the process was terminated by a signal.
    pub rc: Option<i32>,
    pub stdout: String,
    pub stderr: String,
    pub wall_ms: u64,
    pub killed_by_timeout: bool,
    /// Set (with everything else defaulted) when the wrapper could not even
    /// be spawned — `prlimit` missing, say. Callers turn this into a
    /// `malformed:spawn: …` row rather than aborting the run.
    pub spawn_error: Option<String>,
}

/// Run `program args…` under the limit chain, returning what was observed.
/// Never panics and never propagates an error: a failure to spawn comes back
/// as `Exec { spawn_error: Some(_), .. }`.
pub fn run_limited(program: &str, args: &[&str], limits: &Limits) -> Exec {
    let mut cmd = Command::new("prlimit");
    cmd.arg(format!("--as={}", limits.mem_mb * 1024 * 1024))
        .arg("timeout")
        .arg("-s")
        .arg("KILL")
        .arg((limits.timeout_s + 1).to_string())
        .arg("timeout")
        .arg(limits.timeout_s.to_string())
        .arg(program)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let start = Instant::now();
    let mut child = match cmd.spawn() {
        Ok(child) => child,
        Err(e) => {
            return Exec {
                spawn_error: Some(format!("prlimit {program}: {e}")),
                ..Exec::default()
            }
        }
    };

    // Drain both pipes concurrently: a program that writes a lot to stderr
    // while we block reading stdout (or vice versa) would otherwise wedge.
    let mut out_pipe = child.stdout.take();
    let mut err_pipe = child.stderr.take();
    let out_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(pipe) = out_pipe.as_mut() {
            let _ = pipe.read_to_end(&mut buf);
        }
        buf
    });
    let err_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(pipe) = err_pipe.as_mut() {
            let _ = pipe.read_to_end(&mut buf);
        }
        buf
    });

    let status = child.wait();
    let stdout = out_thread.join().unwrap_or_default();
    let stderr = err_thread.join().unwrap_or_default();
    let wall_ms = start.elapsed().as_millis() as u64;

    let rc = match status {
        Ok(status) => status.code(),
        Err(e) => {
            return Exec {
                spawn_error: Some(format!("wait {program}: {e}")),
                wall_ms,
                ..Exec::default()
            }
        }
    };

    // 124 is `timeout`'s own "expired" status. 137 (128+KILL) or a signal
    // death only count as a timeout if the budget had actually elapsed —
    // otherwise it is an abort/OOM kill and must classify as such.
    let budget_ms = limits.timeout_s.saturating_mul(1000);
    let killed_by_timeout = rc == Some(124)
        || (rc == Some(137) && wall_ms >= budget_ms)
        || (rc.is_none() && wall_ms >= budget_ms);

    Exec {
        rc,
        stdout: String::from_utf8_lossy(&stdout).into_owned(),
        stderr: String::from_utf8_lossy(&stderr).into_owned(),
        wall_ms,
        killed_by_timeout,
        spawn_error: None,
    }
}

/// Check that the external limit tools are on `PATH`, so a run fails at
/// startup with one clear message instead of six thousand malformed rows.
pub fn tools_available() -> Result<(), String> {
    for tool in ["prlimit", "timeout"] {
        let ok = Command::new(tool)
            .arg("--version")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|s| s.success())
            .map_err(|e| format!("{tool} not usable: {e}"))?;
        if !ok {
            return Err(format!("{tool} --version failed"));
        }
    }
    Ok(())
}
