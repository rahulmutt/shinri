//! Corpus discovery: walk `<corpus>/<LOGIC>/**/*.smt2` and scan each file's
//! head for a `(set-info :status ...)` declaration.

use crate::verdict::Answer;
use std::fs::{self, File};
use std::io::{self, Read};
use std::path::{Path, PathBuf};

/// One `.smt2` file found under the corpus root.
#[derive(Debug)]
pub struct Instance {
    pub rel_path: String,
    pub abs_path: PathBuf,
    pub logic: String,
    pub bytes: u64,
    pub status: Option<Answer>,
}

/// Scan the first 64 KiB for `(set-info :status <sat|unsat|unknown>)`
/// outside comments. Only the first match counts.
pub fn scan_status(head: &str) -> Option<Answer> {
    let stripped = strip_comments(head);

    let mut rest = stripped.as_str();
    while let Some(pos) = rest.find("(set-info") {
        rest = &rest[pos + "(set-info".len()..];
        rest = rest.trim_start();
        if let Some(after_status) = rest.strip_prefix(":status") {
            let after_status = after_status.trim_start();
            let tok_end = after_status
                .find(|c: char| c.is_whitespace() || c == ')')
                .unwrap_or(after_status.len());
            let tok = &after_status[..tok_end];
            if let Some(a) = Answer::parse(tok) {
                return Some(a);
            }
        }
    }
    None
}

/// Strip `;`-to-end-of-line comments from SMT-LIB source, respecting
/// string literals (`"..."`, where `""` inside a string is an escaped
/// quote per SMT-LIB 2.6 §3.1, not a terminator) and quoted symbols
/// (`|...|`) so a `;` inside either is not mistaken for a comment start.
/// Only comment text is dropped; everything else — including the quote
/// characters themselves — is kept verbatim, so callers can still find
/// literal command text such as `(set-info`.
///
/// If a string or quoted symbol is left unterminated by the end of `head`,
/// no special handling kicks in: nothing after the opening quote was ever
/// comment text (there being no confirmed close), so nothing is dropped,
/// and a `(set-info :status ...)` occurring later in the text is still
/// found. `head` is only the first 64 KiB of a file, so a literal
/// straddling that boundary is an expected shape, not necessarily
/// malformed input — see `unterminated_string_still_finds_trailing_status`.
fn strip_comments(head: &str) -> String {
    #[derive(Clone, Copy, PartialEq)]
    enum State {
        Normal,
        Str,
        Sym,
    }

    let mut out = String::with_capacity(head.len());
    let mut state = State::Normal;
    let mut chars = head.chars().peekable();
    while let Some(c) = chars.next() {
        match state {
            State::Normal => match c {
                ';' => {
                    while let Some(&next) = chars.peek() {
                        if next == '\n' {
                            break;
                        }
                        chars.next();
                    }
                }
                '"' => {
                    state = State::Str;
                    out.push(c);
                }
                '|' => {
                    state = State::Sym;
                    out.push(c);
                }
                _ => out.push(c),
            },
            State::Str => match c {
                '"' => {
                    if chars.peek() == Some(&'"') {
                        out.push('"');
                        out.push('"');
                        chars.next();
                    } else {
                        out.push('"');
                        state = State::Normal;
                    }
                }
                _ => out.push(c),
            },
            State::Sym => match c {
                '|' => {
                    out.push(c);
                    state = State::Normal;
                }
                _ => out.push(c),
            },
        }
    }
    out
}

/// Walk `<corpus>/<LOGIC>/**/*.smt2` for each logic in `logics`, returning
/// instances sorted by `rel_path`. Errors if a requested logic directory is
/// missing (suggests running `fetch` first).
pub fn walk(corpus: &Path, logics: &[String]) -> io::Result<Vec<Instance>> {
    let mut out = Vec::new();
    for logic in logics {
        let logic_dir = corpus.join(logic);
        if !logic_dir.is_dir() {
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!(
                    "logic directory not found: {} (run `fetch` first?)",
                    logic_dir.display()
                ),
            ));
        }
        walk_dir(corpus, &logic_dir, logic, &mut out)?;
    }
    out.sort_by(|a, b| a.rel_path.cmp(&b.rel_path));
    Ok(out)
}

fn walk_dir(corpus: &Path, dir: &Path, logic: &str, out: &mut Vec<Instance>) -> io::Result<()> {
    let mut entries: Vec<_> = fs::read_dir(dir)?.collect::<Result<_, _>>()?;
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            walk_dir(corpus, &path, logic, out)?;
        } else if file_type.is_file() && path.extension().and_then(|e| e.to_str()) == Some("smt2") {
            let rel_path = path
                .strip_prefix(corpus)
                .unwrap_or(&path)
                .to_string_lossy()
                .replace('\\', "/");
            let bytes = entry.metadata()?.len();

            let mut buf = vec![0u8; 65536];
            let mut file = File::open(&path)?;
            let n = file.read(&mut buf)?;
            let head = String::from_utf8_lossy(&buf[..n]);
            let status = scan_status(&head);

            out.push(Instance {
                rel_path,
                abs_path: path,
                logic: logic.to_string(),
                bytes,
                status,
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn status_present() {
        assert_eq!(
            scan_status("(set-logic QF_BV)\n(set-info :status unsat)\n"),
            Some(Answer::Unsat)
        );
        assert_eq!(
            scan_status("(set-info   :status   sat )"),
            Some(Answer::Sat)
        );
        assert_eq!(
            scan_status("(set-info :status unknown)"),
            Some(Answer::Unknown)
        );
    }

    #[test]
    fn status_absent_or_in_comment() {
        assert_eq!(scan_status("(set-logic QF_BV)\n(check-sat)\n"), None);
        assert_eq!(
            scan_status("; (set-info :status sat)\n(set-logic QF_BV)"),
            None
        );
    }

    #[test]
    fn status_after_check_sat_still_counts_and_crlf() {
        assert_eq!(
            scan_status("(check-sat)\r\n(set-info :status sat)\r\n"),
            Some(Answer::Sat)
        );
    }

    #[test]
    fn semicolon_inside_string_literal_is_not_a_comment() {
        assert_eq!(
            scan_status("(assert (= s \";\"))(set-info :status sat)"),
            Some(Answer::Sat)
        );
    }

    #[test]
    fn escaped_quote_inside_string_literal_keeps_scanning() {
        assert_eq!(
            scan_status("(assert (= s \"a\"\"b;c\"))\n(set-info :status unsat)"),
            Some(Answer::Unsat)
        );
    }

    #[test]
    fn semicolon_inside_quoted_symbol_is_not_a_comment() {
        assert_eq!(
            scan_status("(declare-fun |x;y| () Int)(set-info :status sat)"),
            Some(Answer::Sat)
        );
    }

    #[test]
    fn real_comment_before_real_status_on_next_line_still_found() {
        assert_eq!(
            scan_status("; (set-info :status sat)\n(set-info :status unsat)"),
            Some(Answer::Unsat)
        );
    }

    #[test]
    fn unterminated_string_still_finds_trailing_status() {
        // `head` is only the first 64 KiB of a file, so a string literal
        // left open at the point we stop reading is an expected shape, not
        // necessarily malformed input. Nothing after the opening quote was
        // ever comment text, so `strip_comments` drops nothing and the
        // later `:status` is still found. A `None` "fail closed" would also
        // be a defensible choice; this pins the one actually implemented so
        // a future change to it is a conscious decision.
        assert_eq!(
            scan_status("(assert (= s \"abc\n(set-info :status sat)"),
            Some(Answer::Sat)
        );
    }

    #[test]
    fn walk_sorts_and_derives_logic_from_top_dir() {
        let dir = std::env::temp_dir().join(format!("shinri-bench-walk-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("QF_BV/b")).unwrap();
        std::fs::create_dir_all(dir.join("QF_LRA")).unwrap();
        std::fs::write(dir.join("QF_BV/b/y.smt2"), "(set-info :status sat)").unwrap();
        std::fs::write(dir.join("QF_BV/a.smt2"), "").unwrap();
        std::fs::write(dir.join("QF_BV/README"), "").unwrap();
        std::fs::write(dir.join("QF_LRA/z.smt2"), "").unwrap();
        let v = walk(&dir, &["QF_BV".into()]).unwrap();
        assert_eq!(
            v.iter().map(|i| i.rel_path.as_str()).collect::<Vec<_>>(),
            ["QF_BV/a.smt2", "QF_BV/b/y.smt2"]
        );
        assert_eq!(v[1].logic, "QF_BV");
        assert_eq!(v[1].status, Some(Answer::Sat));
        assert_eq!(v[1].bytes, 22);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn walk_missing_logic_dir_errors_and_names_it() {
        let dir =
            std::env::temp_dir().join(format!("shinri-bench-walk-missing-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let err = walk(&dir, &["QF_BV".into()]).unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("QF_BV"), "message should name the dir: {msg}");
        assert!(msg.contains("fetch"), "message should suggest fetch: {msg}");
        std::fs::remove_dir_all(dir).unwrap();
    }
}
