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
