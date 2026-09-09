//! Resumable JSONL results file: a `{"fixture":{...}}` header line followed
//! by one `Row` per line. Hand-serialised (see `json::escape` /
//! `json::parse_object`) — this is the on-disk schema every later task
//! reads, so field names below match the struct fields exactly.

use crate::json::{self, JsonVal};
use crate::verdict::{Answer, OracleAnswers, Verdict};
use std::collections::HashSet;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

/// Identifies one benchmark run: what was run, and under what limits.
pub struct Fixture {
    pub sha: String,
    pub version: String,
    pub timeout_s: u64,
    pub mem_mb: u64,
    pub jobs: usize,
    pub cpu_max: String,
    pub memory_max: String,
    pub corpus: String,
    pub started: String,
    /// The resolved `--solver` path. Optional: files written before the
    /// field existed have neither this nor `solver_md5`.
    pub solver: Option<String>,
    /// `md5sum` of that binary, so two different builds of the same repo sha
    /// cannot resume into one results file (slice 46 review I2). `None` when
    /// the digest could not be taken.
    pub solver_md5: Option<String>,
}

impl Fixture {
    pub fn to_json(&self) -> String {
        let mut out = format!(
            "{{\"fixture\":{{\"sha\":{},\"version\":{},\"timeout_s\":{},\"mem_mb\":{},\"jobs\":{},\"cpu_max\":{},\"memory_max\":{},\"corpus\":{},\"started\":{}",
            json::escape(&self.sha),
            json::escape(&self.version),
            self.timeout_s,
            self.mem_mb,
            self.jobs,
            json::escape(&self.cpu_max),
            json::escape(&self.memory_max),
            json::escape(&self.corpus),
            json::escape(&self.started),
        );
        // Emitted only when known, so a fixture without them serialises
        // byte-for-byte as it did before the fields existed.
        if let Some(solver) = &self.solver {
            out.push_str(&format!(",\"solver\":{}", json::escape(solver)));
        }
        if let Some(md5) = &self.solver_md5 {
            out.push_str(&format!(",\"solver_md5\":{}", json::escape(md5)));
        }
        out.push_str("}}");
        out
    }

    pub fn from_json(line: &str) -> Option<Fixture> {
        let fields = json::parse_object(line)?;
        let (_, fixture_val) = fields.into_iter().find(|(k, _)| k == "fixture")?;
        let inner = match fixture_val {
            JsonVal::Obj(o) => o,
            _ => return None,
        };
        let get = |name: &str| {
            inner
                .iter()
                .find(|(k, _)| k == name)
                .map(|(_, v)| v.clone())
        };
        let str_field = |name: &str| match get(name) {
            Some(JsonVal::Str(s)) => Some(s),
            _ => None,
        };
        let num_field = |name: &str| match get(name) {
            Some(JsonVal::Num(n)) => Some(n),
            _ => None,
        };

        Some(Fixture {
            sha: str_field("sha")?,
            version: str_field("version")?,
            timeout_s: num_field("timeout_s")? as u64,
            mem_mb: num_field("mem_mb")? as u64,
            jobs: num_field("jobs")? as usize,
            cpu_max: str_field("cpu_max").unwrap_or_default(),
            memory_max: str_field("memory_max").unwrap_or_default(),
            corpus: str_field("corpus").unwrap_or_default(),
            started: str_field("started").unwrap_or_default(),
            solver: str_field("solver"),
            solver_md5: str_field("solver_md5"),
        })
    }

    /// Two fixtures belong to the same run iff the corpus snapshot and the
    /// run limits match: `sha`, `timeout_s`, `mem_mb`, `jobs` — plus the
    /// solver binary's digest when *both* sides carry one, so a debug and a
    /// release build of the same sha are not merged (review I2). A file
    /// written before the field existed stays resumable.
    pub fn same_run(&self, other: &Fixture) -> bool {
        let same_binary = match (&self.solver_md5, &other.solver_md5) {
            (Some(a), Some(b)) => a == b,
            _ => true,
        };
        same_binary
            && self.sha == other.sha
            && self.timeout_s == other.timeout_s
            && self.mem_mb == other.mem_mb
            && self.jobs == other.jobs
    }
}

/// One benchmark instance's observed result.
pub struct Row {
    pub path: String,
    pub logic: String,
    pub bytes: u64,
    pub status: Option<Answer>,
    pub rc: Option<i32>,
    pub wall_ms: u64,
    pub answers: Vec<Answer>,
    /// `(error …)` lines seen on stdout before the first answer; kept per
    /// row so a `parse-error` can be told apart from a clean one later
    /// without re-running the corpus.
    pub stdout_errors: usize,
    /// The first of those `(error …)` lines verbatim (≤512 B). The report
    /// splits parse-error buckets on it; it is `None` on rows written before
    /// the field existed and on rows that saw no stdout error.
    pub first_error: Option<String>,
    pub fence: Option<String>,
    pub stderr_head: String,
    pub verdict: Verdict,
    pub oracle: Option<OracleAnswers>,
}

fn answer_json(a: Option<Answer>) -> String {
    match a {
        Some(a) => json::escape(a.as_str()),
        None => "null".to_string(),
    }
}

impl Row {
    pub fn to_json(&self) -> String {
        let rc = match self.rc {
            Some(v) => v.to_string(),
            None => "null".to_string(),
        };
        let answers = {
            let items: Vec<String> = self
                .answers
                .iter()
                .map(|a| json::escape(a.as_str()))
                .collect();
            format!("[{}]", items.join(","))
        };
        let fence = match &self.fence {
            Some(f) => json::escape(f),
            None => "null".to_string(),
        };
        let first_error = match &self.first_error {
            Some(e) => json::escape(e),
            None => "null".to_string(),
        };
        let oracle = match &self.oracle {
            Some(o) => format!(
                "{{\"z3\":{},\"cvc5\":{}}}",
                answer_json(o.z3),
                answer_json(o.cvc5)
            ),
            None => "null".to_string(),
        };
        format!(
            "{{\"path\":{},\"logic\":{},\"bytes\":{},\"status\":{},\"rc\":{},\"wall_ms\":{},\"answers\":{},\"stdout_errors\":{},\"first_error\":{},\"fence\":{},\"stderr_head\":{},\"verdict\":{},\"oracle\":{}}}",
            json::escape(&self.path),
            json::escape(&self.logic),
            self.bytes,
            answer_json(self.status),
            rc,
            self.wall_ms,
            answers,
            self.stdout_errors,
            first_error,
            fence,
            json::escape(&self.stderr_head),
            json::escape(&self.verdict.key()),
            oracle,
        )
    }

    pub fn from_json(line: &str) -> Option<Row> {
        let fields = json::parse_object(line)?;
        let get = |name: &str| {
            fields
                .iter()
                .find(|(k, _)| k == name)
                .map(|(_, v)| v.clone())
        };

        let path = match get("path")? {
            JsonVal::Str(s) => s,
            _ => return None,
        };
        let logic = match get("logic")? {
            JsonVal::Str(s) => s,
            _ => return None,
        };
        let bytes = match get("bytes")? {
            JsonVal::Num(n) => n as u64,
            _ => return None,
        };
        let status = match get("status") {
            Some(JsonVal::Str(s)) => Answer::parse(&s),
            _ => None,
        };
        let rc = match get("rc") {
            Some(JsonVal::Num(n)) => Some(n as i32),
            _ => None,
        };
        let wall_ms = match get("wall_ms") {
            Some(JsonVal::Num(n)) => n as u64,
            _ => return None,
        };
        let answers = match get("answers") {
            Some(JsonVal::Arr(items)) => items
                .iter()
                .filter_map(|v| match v {
                    JsonVal::Str(s) => Answer::parse(s),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        // Absent in files written before the field existed.
        let stdout_errors = match get("stdout_errors") {
            Some(JsonVal::Num(n)) => n as usize,
            _ => 0,
        };
        // Absent in files written before the field existed.
        let first_error = match get("first_error") {
            Some(JsonVal::Str(s)) => Some(s),
            _ => None,
        };
        let fence = match get("fence") {
            Some(JsonVal::Str(s)) => Some(s),
            _ => None,
        };
        let stderr_head = match get("stderr_head") {
            Some(JsonVal::Str(s)) => s,
            _ => String::new(),
        };
        let verdict = match get("verdict") {
            Some(JsonVal::Str(s)) => Verdict::parse(&s),
            _ => return None,
        };
        let oracle = match get("oracle") {
            Some(JsonVal::Obj(o)) => {
                let z3 = o
                    .iter()
                    .find(|(k, _)| k == "z3")
                    .and_then(|(_, v)| match v {
                        JsonVal::Str(s) => Answer::parse(s),
                        _ => None,
                    });
                let cvc5 = o
                    .iter()
                    .find(|(k, _)| k == "cvc5")
                    .and_then(|(_, v)| match v {
                        JsonVal::Str(s) => Answer::parse(s),
                        _ => None,
                    });
                Some(OracleAnswers { z3, cvc5 })
            }
            _ => None,
        };

        Some(Row {
            path,
            logic,
            bytes,
            status,
            rc,
            wall_ms,
            answers,
            stdout_errors,
            first_error,
            fence,
            stderr_head,
            verdict,
            oracle,
        })
    }
}

/// A results JSONL file open for append. The first line is always the
/// `Fixture` header.
pub struct ResultsFile {
    path: PathBuf,
    file: File,
}

impl ResultsFile {
    /// Open or create the results file at `path`. If it already exists, its
    /// fixture line must match `fixture` per [`Fixture::same_run`] — refuses
    /// with an error otherwise. Returns the recorded paths already present
    /// (for resuming) and a handle open for appending further rows.
    pub fn open(path: &Path, fixture: &Fixture) -> Result<(ResultsFile, HashSet<String>), String> {
        let existed = path.exists();
        let mut seen = HashSet::new();

        if existed {
            let content = fs::read_to_string(path)
                .map_err(|e| format!("failed to read {}: {e}", path.display()))?;
            let mut lines = content.lines();
            let on_disk = lines
                .next()
                .and_then(Fixture::from_json)
                .ok_or_else(|| format!("{} has no valid fixture line", path.display()))?;
            if !on_disk.same_run(fixture) {
                return Err(
                    "results file was produced by a different fixture (sha/timeout/mem/jobs); use a new --run-id"
                        .to_string(),
                );
            }
            for line in lines {
                if let Some(row) = Row::from_json(line) {
                    seen.insert(row.path);
                }
            }
        }

        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .map_err(|e| format!("failed to open {} for append: {e}", path.display()))?;

        if !existed {
            writeln!(file, "{}", fixture.to_json())
                .map_err(|e| format!("failed to write fixture line to {}: {e}", path.display()))?;
            file.flush()
                .map_err(|e| format!("failed to flush {}: {e}", path.display()))?;
        }

        Ok((
            ResultsFile {
                path: path.to_path_buf(),
                file,
            },
            seen,
        ))
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Append one row and flush, so a killed run leaves a readable file.
    pub fn append(&mut self, row: &Row) -> io::Result<()> {
        writeln!(self.file, "{}", row.to_json())?;
        self.file.flush()
    }
}

/// Read an entire results file: the fixture header (if parsable) and every
/// parsable row. Unparsable row lines (e.g. a truncated last line from a
/// killed run) are silently skipped; a summary is printed to stderr if any
/// were.
pub fn read_all(path: &Path) -> io::Result<(Option<Fixture>, Vec<Row>)> {
    let content = fs::read_to_string(path)?;
    let mut lines = content.lines();
    let fixture = lines.next().and_then(Fixture::from_json);

    let mut rows = Vec::new();
    let mut skipped = 0usize;
    for line in lines {
        if line.trim().is_empty() {
            continue;
        }
        match Row::from_json(line) {
            Some(row) => rows.push(row),
            None => skipped += 1,
        }
    }
    if skipped > 0 {
        eprintln!(
            "shinri-bench: {}: skipped {skipped} unparsable row line(s)",
            path.display()
        );
    }
    Ok((fixture, rows))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> Fixture {
        Fixture {
            sha: "abc".into(),
            version: "shinri 0.1.0".into(),
            timeout_s: 20,
            mem_mb: 3072,
            jobs: 6,
            cpu_max: "800000 100000".into(),
            memory_max: "34359738368".into(),
            corpus: "zenodo.11061097".into(),
            started: "2026-09-08T00:00:00Z".into(),
            solver: Some("target/release/shinri".into()),
            solver_md5: Some("d41d8cd98f00b204e9800998ecf8427e".into()),
        }
    }

    fn row() -> Row {
        Row {
            path: "QF_S/a \"q\"\n.smt2".into(),
            logic: "QF_S".into(),
            bytes: 7,
            status: None,
            rc: Some(0),
            wall_ms: 12,
            answers: vec![Answer::Sat],
            stdout_errors: 3,
            first_error: Some("(error \"sort error: Arity { expected: 2, found: 64 }\")".into()),
            fence: None,
            stderr_head: "line1\nline2\\".into(),
            verdict: Verdict::Unverified,
            oracle: Some(OracleAnswers {
                z3: Some(Answer::Timeout),
                cvc5: None,
            }),
        }
    }

    #[test]
    fn row_round_trips() {
        let r = row();
        let back = Row::from_json(&r.to_json()).unwrap();
        assert_eq!(back.path, r.path);
        assert_eq!(back.stderr_head, r.stderr_head);
        assert_eq!(back.verdict, r.verdict);
        assert_eq!(back.oracle, r.oracle);
        assert_eq!(back.answers, r.answers);
        assert_eq!(back.stdout_errors, r.stdout_errors);
        assert_eq!(back.first_error, r.first_error);
    }

    #[test]
    fn stdout_errors_defaults_to_zero_on_older_rows() {
        // A line written before the field existed must still parse.
        let older = r#"{"path":"a.smt2","logic":"QF_UF","bytes":7,"status":null,"rc":0,"wall_ms":12,"answers":["sat"],"fence":null,"stderr_head":"","verdict":"unverified","oracle":null}"#;
        let back = Row::from_json(older).expect("older rows stay readable");
        assert_eq!(back.stdout_errors, 0);
        assert_eq!(back.first_error, None);
        assert_eq!(back.answers, vec![Answer::Sat]);
    }

    #[test]
    fn fixture_round_trips() {
        let f = fixture();
        let back = Fixture::from_json(&f.to_json()).unwrap();
        assert!(f.same_run(&back));
        assert_eq!(back.started, f.started);
        assert_eq!(back.solver.as_deref(), Some("target/release/shinri"));
        assert_eq!(
            back.solver_md5.as_deref(),
            Some("d41d8cd98f00b204e9800998ecf8427e")
        );
    }

    #[test]
    fn same_run_tolerates_a_missing_digest_but_not_a_different_one() {
        // The in-progress baseline's fixture line predates both fields; it
        // must stay resumable against a fixture that now carries them.
        let mut older = fixture();
        older.solver = None;
        older.solver_md5 = None;
        assert!(older.same_run(&fixture()));
        assert!(fixture().same_run(&older));
        // Two different builds of the same sha are two different runs.
        let mut other_build = fixture();
        other_build.solver_md5 = Some("00000000000000000000000000000000".into());
        assert!(!fixture().same_run(&other_build));
    }

    #[test]
    fn a_fixture_without_a_solver_serialises_as_it_did_before_the_fields() {
        let mut f = fixture();
        f.solver = None;
        f.solver_md5 = None;
        assert!(!f.to_json().contains("solver"));
        let back = Fixture::from_json(&f.to_json()).unwrap();
        assert_eq!(back.solver, None);
        assert_eq!(back.solver_md5, None);
    }

    #[test]
    fn open_resumes_and_refuses_mismatch() {
        let p = std::env::temp_dir().join(format!("shinri-bench-res-{}.jsonl", std::process::id()));
        let _ = std::fs::remove_file(&p);
        let (mut f, seen) = ResultsFile::open(&p, &fixture()).unwrap();
        assert!(seen.is_empty());
        f.append(&row()).unwrap();
        drop(f);
        let (_, seen) = ResultsFile::open(&p, &fixture()).unwrap();
        assert!(seen.contains(&row().path));
        let mut other = fixture();
        other.timeout_s = 60;
        assert!(ResultsFile::open(&p, &other).is_err());
        std::fs::remove_file(&p).unwrap();
    }

    #[test]
    fn read_all_skips_truncated_last_line() {
        let p =
            std::env::temp_dir().join(format!("shinri-bench-trunc-{}.jsonl", std::process::id()));
        std::fs::write(
            &p,
            format!(
                "{}\n{}\n{{\"path\":\"cut",
                fixture().to_json(),
                row().to_json()
            ),
        )
        .unwrap();
        let (fx, rows) = read_all(&p).unwrap();
        assert!(fx.is_some());
        assert_eq!(rows.len(), 1);
        std::fs::remove_file(&p).unwrap();
    }
}
