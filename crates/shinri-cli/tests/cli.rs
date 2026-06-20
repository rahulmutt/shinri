//! Black-box tests over the built `shinri` binary.
use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_shinri"))
}

#[test]
fn version_prints_and_exits_zero() {
    let out = bin().arg("--version").output().unwrap();
    assert!(out.status.success());
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.starts_with("shinri "), "got: {stdout:?}");
}

#[test]
fn help_exits_zero() {
    let out = bin().arg("--help").output().unwrap();
    assert!(out.status.success());
    assert!(String::from_utf8(out.stdout).unwrap().contains("Usage:"));
}

#[test]
fn unknown_flag_exits_two() {
    let out = bin().arg("--nope").output().unwrap();
    assert_eq!(out.status.code(), Some(2));
}

use std::io::Write;
use std::process::Stdio;

/// Run the binary with `stdin_text` piped in; return (stdout, exit code).
fn run_stdin(stdin_text: &str) -> (String, Option<i32>) {
    let mut child = bin()
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin_text.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    (String::from_utf8(out.stdout).unwrap(), out.status.code())
}

const UNSAT_SCRIPT: &str = "(set-option :print-success false)\
(set-logic QF_UF)(declare-sort U 0)(declare-fun a () U)(declare-fun b () U)\
(declare-fun f (U) U)(assert (= a b))(assert (distinct (f a) (f b)))(check-sat)";

#[test]
fn stdin_qf_uf_unsat_quiet() {
    let (stdout, code) = run_stdin(UNSAT_SCRIPT);
    assert_eq!(stdout, "unsat\n");
    assert_eq!(code, Some(0));
}

#[test]
fn print_success_emits_success_lines() {
    // No `:print-success false`: declarations and asserts each print `success`.
    let (stdout, _) = run_stdin(
        "(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 0.0))(check-sat)",
    );
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines.first(), Some(&"success")); // set-logic
    assert_eq!(lines.last(), Some(&"sat"));
    assert_eq!(lines.iter().filter(|l| **l == "success").count(), 3);
}

#[test]
fn parse_error_does_not_stop_the_stream() {
    let (stdout, code) = run_stdin(
        "(set-option :print-success false)(this-is-not-a-command)\
(set-logic QF_LRA)(declare-fun x () Real)(assert (> x 0.0))(check-sat)",
    );
    assert!(stdout.contains("(error"), "expected an error line, got: {stdout:?}");
    assert!(stdout.trim_end().ends_with("sat"), "stream should continue: {stdout:?}");
    assert_eq!(code, Some(0)); // in-band error, not a process failure
}

#[test]
fn file_mode_matches_stdin_mode() {
    let path = std::env::temp_dir().join(format!("shinri_e2e_{}.smt2", std::process::id()));
    std::fs::write(&path, UNSAT_SCRIPT).unwrap();
    let out = bin().arg(&path).output().unwrap();
    assert_eq!(String::from_utf8(out.stdout).unwrap(), "unsat\n");
    assert_eq!(out.status.code(), Some(0));
    let _ = std::fs::remove_file(&path);
}

#[test]
fn regular_output_channel_redirects_to_file() {
    let path = std::env::temp_dir().join(format!("shinri_redir_{}.out", std::process::id()));
    let p = path.to_str().unwrap();
    let script = format!(
        "(set-option :print-success false)\
(set-option :regular-output-channel \"{p}\")(echo \"hi\")"
    );
    let (stdout, _) = run_stdin(&script);
    assert_eq!(stdout, "", "output should have gone to the file, not stdout");
    let body = std::fs::read_to_string(&path).unwrap();
    assert!(body.contains("hi"), "redirected file got: {body:?}");
    let _ = std::fs::remove_file(&path);
}

#[test]
fn unreadable_file_exits_two() {
    let out = bin().arg("/no/such/shinri/file.smt2").output().unwrap();
    assert_eq!(out.status.code(), Some(2));
}
