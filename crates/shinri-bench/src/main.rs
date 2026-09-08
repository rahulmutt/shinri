//! shinri-bench: fetch / run / rerun / report over the SMT-LIB corpus.
//!
//! This binary is dispatch, hand-rolled argument parsing (mirroring
//! `shinri-cli`'s style) and fixture assembly only — every decision about
//! what a run *means* lives in the library modules.

use shinri_bench::corpus::{self, Manifest};
use shinri_bench::instance::{self, Instance};
use shinri_bench::oracle::Oracle;
use shinri_bench::process::{self, Limits};
use shinri_bench::report;
use shinri_bench::results::{self, Fixture, ResultsFile, Row};
use shinri_bench::runner::{self, RunConfig};
use shinri_bench::verdict::Verdict;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::slice::Iter;
use std::time::{SystemTime, UNIX_EPOCH};

const DEFAULT_MANIFEST: &str = "bench/manifest.toml";
const DEFAULT_CORPUS: &str = "bench/corpus";
const DEFAULT_RESULTS: &str = "bench/results";
const DEFAULT_TIMEOUT_S: u64 = 20;
const DEFAULT_MEM_MB: u64 = 3072;
const DEFAULT_JOBS: usize = 6;
/// The release build the mise tasks produce; anything else falls back to
/// whatever `shinri` is on `PATH`.
const BUILT_SOLVER: &str = "target/release/shinri";

const USAGE: &str = "\
Usage: shinri-bench <COMMAND> [OPTIONS]

Commands:
  fetch     Download, verify and extract the pinned SMT-LIB archives
  run       Run shinri over the corpus under per-instance limits
  rerun     Re-run the instances of a previous run that got a given verdict
  report    Render a Markdown report for a finished run

fetch [--logics A,B] [--mirror URL|DIR] [--dry-run] [--manifest PATH]
      [--corpus DIR]
  --logics A,B      Comma-separated logics (default: every manifest logic)
  --mirror URL|DIR  Fetch from this base instead of the manifest's; a path
                    starting with `/` is used as a local file:// mirror
  --dry-run         Report what would be fetched; download nothing
  --manifest PATH   Manifest to read (default: bench/manifest.toml)
  --corpus DIR      Corpus root to extract into (default: bench/corpus)

run [--logics A,B] [--timeout S] [--mem-mb M] [--jobs N] [--run-id ID]
    [--solver PATH] [--corpus DIR] [--results DIR]
  --timeout S       Per-instance wall-clock budget in seconds (default: 20)
  --mem-mb M        Per-instance address-space limit in MiB (default: 3072)
  --jobs N          Worker threads (default: 6)
  --run-id ID       Results go to <results>/<ID>/results.jsonl
                    (default: the UTC start time, YYYYMMDDTHHMMSSZ)
  --solver PATH     Solver to benchmark (default: target/release/shinri if
                    built, else `shinri` on PATH); always run with --stats
  --results DIR     Results root (default: bench/results)

  An existing results file for the same run-id and limits is resumed: the
  instances it already records are skipped. `Fixture::same_run` keys that on
  the commit sha, which carries a `-dirty` suffix whenever the working tree
  has uncommitted changes — so a rebuilt solver never resumes another
  build's rows.

rerun <RESULTS.jsonl> --verdict v1,v2 [--timeout S] [--mem-mb M] [--jobs N]
      [--run-id ID] [--solver PATH] [--corpus DIR] [--results DIR]
  --verdict v1,v2   Verdict keys to re-run; a bare family selects every
                    sub-key (`unknown` takes every `unknown:<fence>`)

report <RUN-DIR>
  Reads <RUN-DIR>/results.jsonl, writes <RUN-DIR>/report.md, prints its path.
";

fn main() {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let Some((cmd, rest)) = argv.split_first() else {
        usage_exit("missing subcommand");
    };
    let outcome = match cmd.as_str() {
        "-h" | "--help" | "help" => {
            print!("{USAGE}");
            return;
        }
        "fetch" => cmd_fetch(or_usage(parse_fetch_args(rest))),
        "run" => cmd_run(or_usage(parse_run_args(rest))),
        "rerun" => cmd_rerun(or_usage(parse_rerun_args(rest))),
        "report" => cmd_report(or_usage(parse_report_args(rest))),
        other => usage_exit(&format!("unknown command: {other}")),
    };
    if let Err(e) = outcome {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

/// A bad command line is exit 2 with the usage text; a failed *run* is
/// exit 1 with a one-line reason (see `main`).
fn usage_exit(msg: &str) -> ! {
    eprintln!("error: {msg}");
    eprint!("{USAGE}");
    std::process::exit(2);
}

fn or_usage<T>(parsed: Result<T, String>) -> T {
    match parsed {
        Ok(v) => v,
        Err(e) => usage_exit(&e),
    }
}

// ---------------------------------------------------------------- arguments

/// The value of a `--flag VALUE` pair.
fn value(flag: &str, args: &mut Iter<'_, String>) -> Result<String, String> {
    args.next()
        .cloned()
        .ok_or_else(|| format!("{flag} needs a value"))
}

fn number<T: std::str::FromStr>(flag: &str, args: &mut Iter<'_, String>) -> Result<T, String> {
    let raw = value(flag, args)?;
    raw.parse()
        .map_err(|_| format!("{flag}: not a number: {raw}"))
}

/// The value of a `--logics` pair. An explicitly given list that names no
/// logic is a mistake, not a request for all of them (an empty `logics`
/// field means "every manifest logic").
fn logics_value(flag: &str, args: &mut Iter<'_, String>) -> Result<Vec<String>, String> {
    let raw = value(flag, args)?;
    let logics = list(&raw);
    if logics.is_empty() {
        return Err(format!("{flag}: no logic names in {raw:?}"));
    }
    Ok(logics)
}

/// `A,B, C` → `["A", "B", "C"]`; empty entries are dropped.
fn list(raw: &str) -> Vec<String> {
    raw.split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(String::from)
        .collect()
}

#[derive(Debug, PartialEq, Eq)]
struct FetchArgs {
    logics: Vec<String>,
    mirror: Option<String>,
    dry_run: bool,
    manifest: PathBuf,
    corpus: PathBuf,
}

#[derive(Debug, PartialEq, Eq)]
struct RunArgs {
    logics: Vec<String>,
    timeout_s: u64,
    mem_mb: u64,
    jobs: usize,
    run_id: String,
    solver: Option<String>,
    corpus: PathBuf,
    results: PathBuf,
}

#[derive(Debug, PartialEq, Eq)]
struct RerunArgs {
    source: PathBuf,
    verdicts: Vec<String>,
    timeout_s: u64,
    mem_mb: u64,
    jobs: usize,
    run_id: String,
    solver: Option<String>,
    corpus: PathBuf,
    /// `None` = the results root the source run lives in.
    results: Option<PathBuf>,
}

#[derive(Debug, PartialEq, Eq)]
struct ReportArgs {
    run_dir: PathBuf,
}

fn parse_fetch_args(argv: &[String]) -> Result<FetchArgs, String> {
    let mut out = FetchArgs {
        logics: Vec::new(),
        mirror: None,
        dry_run: false,
        manifest: PathBuf::from(DEFAULT_MANIFEST),
        corpus: PathBuf::from(DEFAULT_CORPUS),
    };
    let mut args = argv.iter();
    while let Some(a) = args.next() {
        match a.as_str() {
            "--logics" => out.logics = logics_value("--logics", &mut args)?,
            "--mirror" => out.mirror = Some(value("--mirror", &mut args)?),
            "--dry-run" => out.dry_run = true,
            "--manifest" => out.manifest = PathBuf::from(value("--manifest", &mut args)?),
            "--corpus" => out.corpus = PathBuf::from(value("--corpus", &mut args)?),
            other => return Err(format!("fetch: unexpected argument: {other}")),
        }
    }
    Ok(out)
}

fn parse_run_args(argv: &[String]) -> Result<RunArgs, String> {
    let mut out = RunArgs {
        logics: Vec::new(),
        timeout_s: DEFAULT_TIMEOUT_S,
        mem_mb: DEFAULT_MEM_MB,
        jobs: DEFAULT_JOBS,
        run_id: compact_timestamp(now_secs()),
        solver: None,
        corpus: PathBuf::from(DEFAULT_CORPUS),
        results: PathBuf::from(DEFAULT_RESULTS),
    };
    let mut args = argv.iter();
    while let Some(a) = args.next() {
        match a.as_str() {
            "--logics" => out.logics = logics_value("--logics", &mut args)?,
            "--timeout" => out.timeout_s = number("--timeout", &mut args)?,
            "--mem-mb" => out.mem_mb = number("--mem-mb", &mut args)?,
            "--jobs" => out.jobs = number("--jobs", &mut args)?,
            "--run-id" => out.run_id = value("--run-id", &mut args)?,
            "--solver" => out.solver = Some(value("--solver", &mut args)?),
            "--corpus" => out.corpus = PathBuf::from(value("--corpus", &mut args)?),
            "--results" => out.results = PathBuf::from(value("--results", &mut args)?),
            other => return Err(format!("run: unexpected argument: {other}")),
        }
    }
    check_limits(out.timeout_s, out.mem_mb, out.jobs, &out.run_id)?;
    Ok(out)
}

fn parse_rerun_args(argv: &[String]) -> Result<RerunArgs, String> {
    let mut source: Option<PathBuf> = None;
    let mut out = RerunArgs {
        source: PathBuf::new(),
        verdicts: Vec::new(),
        timeout_s: DEFAULT_TIMEOUT_S,
        mem_mb: DEFAULT_MEM_MB,
        jobs: DEFAULT_JOBS,
        run_id: compact_timestamp(now_secs()),
        solver: None,
        corpus: PathBuf::from(DEFAULT_CORPUS),
        results: None,
    };
    let mut args = argv.iter();
    while let Some(a) = args.next() {
        match a.as_str() {
            "--verdict" => out.verdicts.extend(list(&value("--verdict", &mut args)?)),
            "--timeout" => out.timeout_s = number("--timeout", &mut args)?,
            "--mem-mb" => out.mem_mb = number("--mem-mb", &mut args)?,
            "--jobs" => out.jobs = number("--jobs", &mut args)?,
            "--run-id" => out.run_id = value("--run-id", &mut args)?,
            "--solver" => out.solver = Some(value("--solver", &mut args)?),
            "--corpus" => out.corpus = PathBuf::from(value("--corpus", &mut args)?),
            "--results" => out.results = Some(PathBuf::from(value("--results", &mut args)?)),
            other if other.starts_with("--") => {
                return Err(format!("rerun: unexpected argument: {other}"))
            }
            path => {
                if source.is_some() {
                    return Err("rerun: expected exactly one results file".to_string());
                }
                source = Some(PathBuf::from(path));
            }
        }
    }
    out.source = source.ok_or_else(|| "rerun: missing <RESULTS.jsonl>".to_string())?;
    if out.verdicts.is_empty() {
        return Err("rerun: --verdict is required (e.g. --verdict wrong,unknown)".to_string());
    }
    check_limits(out.timeout_s, out.mem_mb, out.jobs, &out.run_id)?;
    Ok(out)
}

fn parse_report_args(argv: &[String]) -> Result<ReportArgs, String> {
    match argv {
        [dir] if !dir.starts_with("--") => Ok(ReportArgs {
            run_dir: PathBuf::from(dir),
        }),
        [] => Err("report: missing <RUN-DIR>".to_string()),
        _ => Err("report: expected exactly one run directory".to_string()),
    }
}

/// Reject the limit values that would make a run meaningless (and the
/// run-ids that would escape the results root) before anything is spawned.
fn check_limits(timeout_s: u64, mem_mb: u64, jobs: usize, run_id: &str) -> Result<(), String> {
    if timeout_s == 0 {
        return Err("--timeout must be at least 1 second".to_string());
    }
    if mem_mb == 0 {
        return Err("--mem-mb must be at least 1 MiB".to_string());
    }
    if jobs == 0 {
        return Err("--jobs must be at least 1".to_string());
    }
    if run_id.is_empty() || run_id.contains('/') || run_id.contains('\\') || run_id.starts_with('.')
    {
        return Err(format!("--run-id must be a plain directory name: {run_id}"));
    }
    Ok(())
}

// ----------------------------------------------------------------- commands

fn cmd_fetch(a: FetchArgs) -> Result<(), String> {
    let manifest = corpus::load_manifest(&a.manifest)?;
    let logics = resolve_logics(&a.logics, &manifest);
    corpus::fetch(
        &manifest,
        &logics,
        &a.corpus,
        a.mirror.as_deref(),
        a.dry_run,
    )
}

fn cmd_run(a: RunArgs) -> Result<(), String> {
    let (logics, record) = manifest_context(&a.logics)?;
    let (solver, version) = prepare_solver(a.solver.as_deref())?;
    let instances = instance::walk(&a.corpus, &logics).map_err(|e| e.to_string())?;
    eprintln!(
        "shinri-bench: {} instance(s) across {} logic(s)",
        instances.len(),
        logics.len()
    );
    let fixture = build_fixture(
        &version,
        a.timeout_s,
        a.mem_mb,
        a.jobs,
        corpus_provenance(&a.corpus, record),
    );
    let cfg = run_config(solver, a.timeout_s, a.mem_mb, a.jobs);
    execute(instances, fixture, &a.results, &a.run_id, &cfg)
}

fn cmd_rerun(a: RerunArgs) -> Result<(), String> {
    let source_dir = a
        .source
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .ok_or_else(|| format!("{} is not inside a run directory", a.source.display()))?
        .to_path_buf();
    let results_root = a.results.clone().unwrap_or_else(|| {
        source_dir
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .map(Path::to_path_buf)
            .unwrap_or_else(|| PathBuf::from(DEFAULT_RESULTS))
    });
    if same_dir(&results_root.join(&a.run_id), &source_dir) {
        return Err(format!(
            "--run-id {} names the source run; a rerun always writes a new run",
            a.run_id
        ));
    }

    let (_, rows) =
        results::read_all(&a.source).map_err(|e| format!("{}: {e}", a.source.display()))?;
    let selected: Vec<&Row> = rows
        .iter()
        .filter(|r| verdict_selected(&r.verdict, &a.verdicts))
        .collect();
    if selected.is_empty() {
        return Err(format!(
            "no rows in {} match --verdict {}",
            a.source.display(),
            a.verdicts.join(",")
        ));
    }
    let mut instances = Vec::with_capacity(selected.len());
    for row in selected {
        let abs_path = a.corpus.join(&row.path);
        if !abs_path.is_file() {
            return Err(format!(
                "instance not found under {}: {} (wrong --corpus?)",
                a.corpus.display(),
                row.path
            ));
        }
        instances.push(Instance {
            rel_path: row.path.clone(),
            abs_path,
            logic: row.logic.clone(),
            bytes: row.bytes,
            status: row.status,
        });
    }

    let (solver, version) = prepare_solver(a.solver.as_deref())?;
    eprintln!(
        "shinri-bench: re-running {} instance(s) from {}",
        instances.len(),
        a.source.display()
    );
    let fixture = build_fixture(
        &version,
        a.timeout_s,
        a.mem_mb,
        a.jobs,
        corpus_provenance(&a.corpus, corpus_record()),
    );
    let cfg = run_config(solver, a.timeout_s, a.mem_mb, a.jobs);
    execute(instances, fixture, &results_root, &a.run_id, &cfg)
}

fn cmd_report(a: ReportArgs) -> Result<(), String> {
    let jsonl = a.run_dir.join("results.jsonl");
    let (fixture, rows) =
        results::read_all(&jsonl).map_err(|e| format!("{}: {e}", jsonl.display()))?;
    let markdown = report::render(fixture.as_ref(), &rows);
    let out = a.run_dir.join("report.md");
    fs::write(&out, markdown).map_err(|e| format!("failed to write {}: {e}", out.display()))?;
    println!("{}", out.display());
    Ok(())
}

/// Open (or resume) `<results>/<run-id>/results.jsonl` and run every
/// instance not already recorded there.
fn execute(
    instances: Vec<Instance>,
    fixture: Fixture,
    results_root: &Path,
    run_id: &str,
    cfg: &RunConfig,
) -> Result<(), String> {
    let dir = results_root.join(run_id);
    fs::create_dir_all(&dir).map_err(|e| format!("failed to create {}: {e}", dir.display()))?;
    let path = dir.join("results.jsonl");
    let (mut file, done) = ResultsFile::open(&path, &fixture)?;
    if !done.is_empty() {
        eprintln!(
            "shinri-bench: resuming {}: {} instance(s) already recorded",
            path.display(),
            done.len()
        );
    }

    let mut progress = Progress::default();
    let outcome = runner::run_all(instances, cfg, &mut file, &done, &mut |done, total, v| {
        progress.tick(done, total, v)
    });
    progress.finish();
    outcome.map_err(|e| format!("failed to append to {}: {e}", path.display()))?;
    println!("{}", path.display());
    Ok(())
}

// ------------------------------------------------------------------ fixture

fn run_config(solver: String, timeout_s: u64, mem_mb: u64, jobs: usize) -> RunConfig {
    RunConfig {
        solver,
        // `--stats` is what carries the fence tag behind an `unknown`.
        solver_args: vec!["--stats".to_string()],
        limits: Limits { timeout_s, mem_mb },
        jobs,
        oracle: Oracle::default(),
    }
}

fn build_fixture(
    version: &str,
    timeout_s: u64,
    mem_mb: u64,
    jobs: usize,
    corpus: String,
) -> Fixture {
    Fixture {
        sha: git_sha(),
        version: version.to_string(),
        timeout_s,
        mem_mb,
        jobs,
        cpu_max: read_first_line("/sys/fs/cgroup/cpu.max"),
        memory_max: read_first_line("/sys/fs/cgroup/memory.max"),
        corpus,
        started: iso_timestamp(now_secs()),
    }
}

/// The manifest supplies both the default logic list and the fixture's
/// corpus record. A run that names its logics explicitly still works
/// without one — the record just degrades to `-`.
fn manifest_context(explicit: &[String]) -> Result<(Vec<String>, String), String> {
    match corpus::load_manifest(Path::new(DEFAULT_MANIFEST)) {
        Ok(m) => Ok((resolve_logics(explicit, &m), m.record)),
        Err(e) if explicit.is_empty() => Err(format!("{e} (and no --logics given)")),
        Err(_) => Ok((explicit.to_vec(), "-".to_string())),
    }
}

/// The fixture's `corpus` field. The pinned Zenodo record describes the
/// repo's own corpus and nothing else, so a run pointed elsewhere with
/// `--corpus` is described by that path instead.
fn corpus_provenance(corpus: &Path, record: String) -> String {
    if corpus == Path::new(DEFAULT_CORPUS) {
        record
    } else {
        corpus.display().to_string()
    }
}

/// Just the manifest's corpus record — a rerun takes its instance list from
/// the source results file, so it needs no logic list.
fn corpus_record() -> String {
    corpus::load_manifest(Path::new(DEFAULT_MANIFEST))
        .map(|m| m.record)
        .unwrap_or_else(|_| "-".to_string())
}

fn resolve_logics(explicit: &[String], manifest: &Manifest) -> Vec<String> {
    if explicit.is_empty() {
        manifest.archives.iter().map(|a| a.logic.clone()).collect()
    } else {
        explicit.to_vec()
    }
}

/// Resolve the solver and prove it runs *before* a results file exists: a
/// solver that cannot be spawned would otherwise produce one
/// `malformed:spawn` row per corpus instance. Also checks the limit
/// wrappers, and warns (only) about missing oracles — a run without z3
/// is still a valid run, its undecidable rows just become `unverified`.
fn prepare_solver(explicit: Option<&str>) -> Result<(String, String), String> {
    let solver = explicit.map(String::from).unwrap_or_else(default_solver);
    let version =
        probe_version(&solver).map_err(|e| format!("solver {solver} is not runnable: {e}"))?;
    process::tools_available()?;
    let oracle = Oracle::default();
    for program in [&oracle.z3, &oracle.cvc5] {
        if probe_version(program).is_err() {
            eprintln!(
                "shinri-bench: warning: oracle '{program}' is not runnable; rows that need it will be recorded as unverified"
            );
        }
    }
    eprintln!("shinri-bench: solver {solver} ({version})");
    Ok((solver, version))
}

fn default_solver() -> String {
    if Path::new(BUILT_SOLVER).is_file() {
        BUILT_SOLVER.to_string()
    } else {
        "shinri".to_string()
    }
}

/// First line of `<program> --version`, or why it could not be obtained.
fn probe_version(program: &str) -> Result<String, String> {
    let out = Command::new(program)
        .arg("--version")
        .stdin(Stdio::null())
        .output()
        .map_err(|e| e.to_string())?;
    if !out.status.success() {
        return Err(format!("`--version` exited with {}", out.status));
    }
    let text = String::from_utf8_lossy(&out.stdout);
    Ok(text
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("-")
        .to_string())
}

/// The fixture's `sha`: the HEAD commit, marked `-dirty` when the working
/// tree carries uncommitted changes. `-` if git cannot answer.
fn git_sha() -> String {
    match (
        git_output(&["rev-parse", "--short=12", "HEAD"]),
        git_output(&["status", "--porcelain"]),
    ) {
        (Some(sha), Some(porcelain)) if !sha.is_empty() => sha_with_dirty_flag(&sha, &porcelain),
        _ => "-".to_string(),
    }
}

/// Trimmed stdout of `git <args>`, or `None` if git could not be run or
/// exited non-zero. An empty-but-successful run is `Some("")` — that is
/// exactly what a clean `git status --porcelain` looks like.
fn git_output(args: &[&str]) -> Option<String> {
    let out = Command::new("git")
        .args(args)
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

/// A sha alone does not identify a solver built from a modified tree, and
/// `Fixture::same_run` keys resume on it — two different builds must not
/// share one fixture header, so a dirty tree gets its own sha.
fn sha_with_dirty_flag(sha: &str, porcelain: &str) -> String {
    if porcelain.trim().is_empty() {
        sha.to_string()
    } else {
        format!("{sha}-dirty")
    }
}

fn read_first_line(path: &str) -> String {
    fs::read_to_string(path)
        .ok()
        .and_then(|s| s.lines().next().map(|l| l.trim().to_string()))
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "-".to_string())
}

/// True when both paths name the same existing directory (or are equal).
fn same_dir(a: &Path, b: &Path) -> bool {
    a == b || matches!((fs::canonicalize(a), fs::canonicalize(b)), (Ok(x), Ok(y)) if x == y)
}

/// A selector matches a whole verdict key, or a family: `unknown` selects
/// every `unknown:<fence>`.
fn verdict_selected(verdict: &Verdict, selectors: &[String]) -> bool {
    let key = verdict.key();
    selectors.iter().any(|sel| {
        key == *sel
            || (key.len() > sel.len()
                && key.starts_with(sel.as_str())
                && key[sel.len()..].starts_with(':'))
    })
}

// ----------------------------------------------------------------- progress

/// Verdict tally, printed every 50 rows and once at the end so a long run
/// shows its shape without one line per instance.
#[derive(Debug)]
struct Progress {
    done: usize,
    total: usize,
    /// `done` at the last printed line; `usize::MAX` until the first one.
    printed: usize,
    correct: usize,
    wrong: usize,
    status_suspect: usize,
    parse_error: usize,
    panic: usize,
    oom: usize,
    timeout: usize,
    unknown: usize,
    unverified: usize,
    malformed: usize,
}

impl Default for Progress {
    fn default() -> Self {
        Progress {
            done: 0,
            total: 0,
            printed: usize::MAX,
            correct: 0,
            wrong: 0,
            status_suspect: 0,
            parse_error: 0,
            panic: 0,
            oom: 0,
            timeout: 0,
            unknown: 0,
            unverified: 0,
            malformed: 0,
        }
    }
}

const PROGRESS_EVERY: usize = 50;

impl Progress {
    fn tick(&mut self, done: usize, total: usize, verdict: &Verdict) {
        self.done = done;
        self.total = total;
        match verdict {
            Verdict::Correct => self.correct += 1,
            Verdict::Wrong => self.wrong += 1,
            Verdict::StatusSuspect => self.status_suspect += 1,
            Verdict::ParseError => self.parse_error += 1,
            Verdict::Panic => self.panic += 1,
            Verdict::Oom => self.oom += 1,
            Verdict::Timeout => self.timeout += 1,
            Verdict::Unknown(_) => self.unknown += 1,
            Verdict::Unverified => self.unverified += 1,
            Verdict::Malformed(_) => self.malformed += 1,
            // Never final: the runner resolves it against the oracle.
            Verdict::NeedsOracle => {}
        }
        if done.is_multiple_of(PROGRESS_EVERY) {
            self.line();
        }
    }

    fn finish(&mut self) {
        if self.printed != self.done {
            self.line();
        }
    }

    fn line(&mut self) {
        self.printed = self.done;
        eprintln!(
            "{}/{}  correct={} wrong={} status-suspect={} parse-error={} panic={} oom={} timeout={} unknown={} unverified={} malformed={}",
            self.done,
            self.total,
            self.correct,
            self.wrong,
            self.status_suspect,
            self.parse_error,
            self.panic,
            self.oom,
            self.timeout,
            self.unknown,
            self.unverified,
            self.malformed,
        );
    }
}

// ---------------------------------------------------------------- timestamps

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// A Unix timestamp as UTC `(year, month, day, hour, minute, second)`.
///
/// Howard Hinnant's `civil_from_days`, shifted to an era starting on
/// 0000-03-01 so leap days land at the end of a year. Keeps the harness
/// free of a calendar dependency.
fn civil_from_epoch(secs: u64) -> (i64, u32, u32, u32, u32, u32) {
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    let (hour, minute, second) = (
        (rem / 3600) as u32,
        ((rem % 3600) / 60) as u32,
        (rem % 60) as u32,
    );

    let z = days + 719_468; // days since 0000-03-01
    let era = z.div_euclid(146_097); // 400-year cycle
    let doe = z.rem_euclid(146_097); // day of era, [0, 146096]
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365; // [0, 399]
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100); // day of (March-based) year
    let mp = (5 * doy + 2) / 153; // month, March = 0
    let day = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let month = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    let year = yoe + era * 400 + i64::from(month <= 2);
    (year, month, day, hour, minute, second)
}

/// `YYYY-MM-DDTHH:MM:SSZ` — the fixture's `started` field.
fn iso_timestamp(secs: u64) -> String {
    let (y, mo, d, h, mi, s) = civil_from_epoch(secs);
    format!("{y:04}-{mo:02}-{d:02}T{h:02}:{mi:02}:{s:02}Z")
}

/// `YYYYMMDDTHHMMSSZ` — the default run-id (a directory name).
fn compact_timestamp(secs: u64) -> String {
    let (y, mo, d, h, mi, s) = civil_from_epoch(secs);
    format!("{y:04}{mo:02}{d:02}T{h:02}{mi:02}{s:02}Z")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn argv(args: &[&str]) -> Vec<String> {
        args.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn run_args_have_documented_defaults() {
        let a = parse_run_args(&["--logics".into(), "QF_AX,QF_S".into()]).unwrap();
        assert_eq!((a.timeout_s, a.mem_mb, a.jobs), (20, 3072, 6));
        assert_eq!(a.logics, vec!["QF_AX", "QF_S"]);
        assert!(a.run_id.len() >= 15); // YYYYMMDDTHHMMSSZ
    }

    #[test]
    fn rerun_requires_verdicts() {
        assert!(parse_rerun_args(&["bench/results/x/results.jsonl".into()]).is_err());
    }

    #[test]
    fn run_args_accept_every_documented_flag() {
        let a = parse_run_args(&argv(&[
            "--logics",
            "QF_AX",
            "--timeout",
            "5",
            "--mem-mb",
            "512",
            "--jobs",
            "2",
            "--run-id",
            "smoke",
            "--solver",
            "/bin/true",
            "--corpus",
            "c",
            "--results",
            "r",
        ]))
        .unwrap();
        assert_eq!((a.timeout_s, a.mem_mb, a.jobs), (5, 512, 2));
        assert_eq!(a.run_id, "smoke");
        assert_eq!(a.solver.as_deref(), Some("/bin/true"));
        assert_eq!(a.corpus, PathBuf::from("c"));
        assert_eq!(a.results, PathBuf::from("r"));
    }

    #[test]
    fn run_args_reject_bad_values() {
        assert!(parse_run_args(&argv(&["--timeout"])).is_err()); // missing value
        assert!(parse_run_args(&argv(&["--timeout", "soon"])).is_err());
        assert!(parse_run_args(&argv(&["--timeout", "0"])).is_err());
        assert!(parse_run_args(&argv(&["--mem-mb", "0"])).is_err());
        // An explicit but empty list is a typo, not "every logic".
        assert!(parse_run_args(&argv(&["--logics", ""])).is_err());
        assert!(parse_run_args(&argv(&["--logics", ",,"])).is_err());
        assert!(parse_fetch_args(&argv(&["--logics", ""])).is_err());
        assert!(parse_run_args(&argv(&["--jobs", "0"])).is_err());
        assert!(parse_run_args(&argv(&["--run-id", "a/b"])).is_err());
        assert!(parse_run_args(&argv(&["--nope"])).is_err());
        assert!(parse_run_args(&argv(&["extra"])).is_err());
    }

    #[test]
    fn fetch_args_default_to_the_repo_paths() {
        let a = parse_fetch_args(&[]).unwrap();
        assert_eq!(a.manifest, PathBuf::from("bench/manifest.toml"));
        assert_eq!(a.corpus, PathBuf::from("bench/corpus"));
        assert!(a.logics.is_empty() && a.mirror.is_none() && !a.dry_run);

        let b =
            parse_fetch_args(&argv(&["--dry-run", "--mirror", "/m", "--logics", "QF_AX"])).unwrap();
        assert!(b.dry_run);
        assert_eq!(b.mirror.as_deref(), Some("/m"));
        assert_eq!(b.logics, vec!["QF_AX"]);
    }

    #[test]
    fn rerun_args_take_a_source_and_verdicts() {
        let a = parse_rerun_args(&argv(&[
            "bench/results/x/results.jsonl",
            "--verdict",
            "wrong,unknown",
            "--jobs",
            "1",
        ]))
        .unwrap();
        assert_eq!(a.source, PathBuf::from("bench/results/x/results.jsonl"));
        assert_eq!(a.verdicts, vec!["wrong", "unknown"]);
        assert_eq!(a.jobs, 1);
        assert_eq!(a.results, None);
        // Two positional arguments are a mistake, not a second source.
        assert!(parse_rerun_args(&argv(&["a.jsonl", "b.jsonl", "--verdict", "wrong"])).is_err());
    }

    #[test]
    fn report_args_take_one_run_dir() {
        assert_eq!(
            parse_report_args(&argv(&["bench/results/x"]))
                .unwrap()
                .run_dir,
            PathBuf::from("bench/results/x")
        );
        assert!(parse_report_args(&[]).is_err());
        assert!(parse_report_args(&argv(&["a", "b"])).is_err());
    }

    #[test]
    fn verdict_selector_matches_family_but_not_prefix() {
        let unknown = Verdict::Unknown("str-order".to_string());
        assert!(verdict_selected(&unknown, &["unknown".to_string()]));
        assert!(verdict_selected(
            &unknown,
            &["unknown:str-order".to_string()]
        ));
        assert!(!verdict_selected(&unknown, &["unknown:other".to_string()]));
        // `unverified` starts with neither; a bare prefix must not match.
        assert!(!verdict_selected(
            &Verdict::Unverified,
            &["unk".to_string()]
        ));
        assert!(verdict_selected(
            &Verdict::Correct,
            &["wrong".to_string(), "correct".to_string()]
        ));
    }

    #[test]
    fn dirty_tree_gets_its_own_sha() {
        // Clean tree: `git status --porcelain` says nothing.
        assert_eq!(sha_with_dirty_flag("abc123", ""), "abc123");
        assert_eq!(sha_with_dirty_flag("abc123", "\n  \n"), "abc123");
        // Any modification must not compare equal to the committed sha —
        // `Fixture::same_run` would otherwise resume one build into another.
        assert_eq!(
            sha_with_dirty_flag("abc123", " M crates/shinri-bench/src/main.rs"),
            "abc123-dirty"
        );
        assert_eq!(sha_with_dirty_flag("abc123", "?? new.rs"), "abc123-dirty");
        assert_ne!(
            sha_with_dirty_flag("abc123", " M x.rs"),
            sha_with_dirty_flag("abc123", "")
        );
    }

    #[test]
    fn corpus_field_describes_where_the_instances_came_from() {
        let record = || "10.5281/zenodo.11061097".to_string();
        // The repo corpus is the one the manifest actually pins.
        assert_eq!(
            corpus_provenance(Path::new("bench/corpus"), record()),
            "10.5281/zenodo.11061097"
        );
        // Anywhere else, the record would be a false provenance claim.
        assert_eq!(
            corpus_provenance(Path::new("/tmp/other"), record()),
            "/tmp/other"
        );
    }

    #[test]
    fn timestamps_are_utc_civil_dates() {
        assert_eq!(iso_timestamp(0), "1970-01-01T00:00:00Z");
        assert_eq!(iso_timestamp(1_757_289_600), "2025-09-08T00:00:00Z");
        assert_eq!(iso_timestamp(1_788_870_896), "2026-09-08T12:34:56Z");
        // Leap day, last second.
        assert_eq!(iso_timestamp(1_709_251_199), "2024-02-29T23:59:59Z");
        // Century non-leap boundary.
        assert_eq!(iso_timestamp(951_868_800), "2000-03-01T00:00:00Z");
        assert_eq!(compact_timestamp(1_757_289_600), "20250908T000000Z");
        assert_eq!(compact_timestamp(1_757_289_600).len(), 16);
    }

    #[test]
    fn progress_prints_every_50_rows_and_once_at_the_end() {
        let mut p = Progress::default();
        for i in 1..=51 {
            p.tick(i, 51, &Verdict::Correct);
        }
        assert_eq!(p.printed, 50); // printed at 50, not at 51
        p.finish();
        assert_eq!(p.printed, 51);
        assert_eq!(p.correct, 51);
        // A second finish does not repeat the line.
        let before = p.printed;
        p.finish();
        assert_eq!(p.printed, before);
    }
}
