//! Markdown report over a results JSONL file (spec §6).
//!
//! Everything printed is plain Markdown with explicit sort keys, so a later
//! re-run's `report.md` diffs cleanly against the baseline. No `HashMap`
//! iteration order reaches the output: per-logic and per-bucket maps are
//! `BTreeMap`s and every list is sorted by a total order before printing.

use crate::results::{Fixture, Row};
use crate::verdict::{Answer, Verdict};
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::fmt::Write as _;

/// Normalise one diagnostic line so variants that differ only in literals
/// collapse into a single bucket: every run of ASCII digits and every
/// `0x…`/`#x…`/`#b…` literal becomes `N`, every `"…"` string and `|…|`
/// quoted symbol becomes `S`, and trailing whitespace is trimmed.
pub fn normalise_diag(line: &str) -> String {
    let b = line.as_bytes();
    let mut out = String::with_capacity(line.len());
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c == b'"' || c == b'|' {
            // A quoted string / quoted symbol: swallow up to the closer.
            i += 1;
            while i < b.len() && b[i] != c {
                i += 1;
            }
            i += usize::from(i < b.len());
            out.push('S');
        } else if is_radix_literal(b, i) {
            i += 2;
            while i < b.len() && b[i].is_ascii_alphanumeric() {
                i += 1;
            }
            out.push('N');
        } else if c.is_ascii_digit() {
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            out.push('N');
        } else {
            // Copy one whole UTF-8 character verbatim.
            let start = i;
            i += 1;
            while i < b.len() && (b[i] & 0xC0) == 0x80 {
                i += 1;
            }
            out.push_str(&line[start..i]);
        }
    }
    out.truncate(out.trim_end().len());
    out
}

/// `0x…` (hex), `#x…` (SMT-LIB hex) or `#b…` (SMT-LIB binary) at `i`.
fn is_radix_literal(b: &[u8], i: usize) -> bool {
    if i + 2 >= b.len() || !b[i + 2].is_ascii_alphanumeric() {
        return false;
    }
    match (b[i], b[i + 1]) {
        (b'0', b'x') | (b'0', b'X') => b[i + 2].is_ascii_hexdigit(),
        (b'#', b'x') | (b'#', b'b') => true,
        _ => false,
    }
}

/// The first line of `text` containing `marker`, else its first non-empty
/// line, else `-`.
fn diag_line<'a>(text: &'a str, marker: &str) -> &'a str {
    let mut first = "";
    for line in text.lines() {
        if line.contains(marker) {
            return line;
        }
        if first.is_empty() && !line.trim().is_empty() {
            first = line;
        }
    }
    if first.is_empty() {
        "-"
    } else {
        first
    }
}

/// Verdict counts for one logic (or for the `all` aggregate).
#[derive(Default, Clone)]
struct Counts {
    total: usize,
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
    /// `needs-oracle`: never final in a completed run, but never dropped.
    other: usize,
}

impl Counts {
    fn add(&mut self, v: &Verdict) {
        self.total += 1;
        match v {
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
            Verdict::NeedsOracle => self.other += 1,
        }
    }

    fn merge(&mut self, o: &Counts) {
        self.total += o.total;
        self.correct += o.correct;
        self.wrong += o.wrong;
        self.status_suspect += o.status_suspect;
        self.parse_error += o.parse_error;
        self.panic += o.panic;
        self.oom += o.oom;
        self.timeout += o.timeout;
        self.unknown += o.unknown;
        self.unverified += o.unverified;
        self.malformed += o.malformed;
        self.other += o.other;
    }
}

/// Everything the report needs about one logic. `correct` is sorted by
/// `(wall_ms, path)` once, and then serves both the median/p90 columns and
/// the slowest-instances table.
#[derive(Default)]
struct Logic<'a> {
    counts: Counts,
    correct: Vec<&'a Row>,
}

fn collect<'a>(rows: &'a [Row]) -> BTreeMap<&'a str, Logic<'a>> {
    let mut logics: BTreeMap<&str, Logic> = BTreeMap::new();
    for row in rows {
        let l = logics.entry(row.logic.as_str()).or_default();
        l.counts.add(&row.verdict);
        if row.verdict == Verdict::Correct {
            l.correct.push(row);
        }
    }
    for l in logics.values_mut() {
        l.correct
            .sort_unstable_by(|a, b| a.wall_ms.cmp(&b.wall_ms).then_with(|| a.path.cmp(&b.path)));
    }
    logics
}

/// Median = the upper middle element (index `n/2`) of the ascending list.
fn median(v: &[u64]) -> Option<u64> {
    v.get(v.len() / 2).copied()
}

/// p90 = the element at index `ceil(0.9*n) - 1` of the ascending list
/// (integer form: `(9n + 9) / 10 - 1`), i.e. the smallest value at or above
/// the 90th percentile. `None` for an empty list.
fn p90(v: &[u64]) -> Option<u64> {
    if v.is_empty() {
        return None;
    }
    v.get((9 * v.len()).div_ceil(10) - 1).copied()
}

fn opt_ms(v: Option<u64>) -> String {
    match v {
        Some(v) => v.to_string(),
        None => "n/a".to_string(),
    }
}

fn answer(a: Option<Answer>) -> &'static str {
    a.map_or("-", Answer::as_str)
}

/// Markdown table cells are `|`-delimited; a `|` inside a path would split
/// the row.
fn cell(s: &str) -> Cow<'_, str> {
    if s.contains('|') {
        Cow::Owned(s.replace('|', "\\|"))
    } else {
        Cow::Borrowed(s)
    }
}

/// Render the full Markdown report: fixture header, per-logic matrix, ranked
/// gaps, wrong answers, perf tail.
pub fn render(fixture: Option<&Fixture>, rows: &[Row]) -> String {
    let logics = collect(rows);
    let mut out = String::with_capacity(4096);
    out.push_str("# shinri-bench report\n\n");
    render_fixture(&mut out, fixture, rows, &logics);
    render_matrix(&mut out, &logics);
    render_gaps(&mut out, rows);
    render_wrong(&mut out, rows);
    render_perf(&mut out, rows, &logics);
    out
}

fn render_fixture(
    out: &mut String,
    fixture: Option<&Fixture>,
    rows: &[Row],
    logics: &BTreeMap<&str, Logic>,
) {
    out.push_str("## Fixture\n\n");
    match fixture {
        None => out.push_str("_no fixture line_\n\n"),
        Some(f) => {
            out.push_str("| field | value |\n| --- | --- |\n");
            let _ = writeln!(out, "| sha | {} |", cell(&f.sha));
            let _ = writeln!(out, "| version | {} |", cell(&f.version));
            let _ = writeln!(out, "| timeout_s | {} |", f.timeout_s);
            let _ = writeln!(out, "| mem_mb | {} |", f.mem_mb);
            let _ = writeln!(out, "| jobs | {} |", f.jobs);
            let _ = writeln!(out, "| cpu_max | {} |", cell(&f.cpu_max));
            let _ = writeln!(out, "| memory_max | {} |", cell(&f.memory_max));
            let _ = writeln!(out, "| corpus | {} |", cell(&f.corpus));
            let _ = writeln!(out, "| started | {} |", cell(&f.started));
            out.push('\n');
        }
    }
    let _ = writeln!(
        out,
        "Rows: {} across {} logic(s).\n",
        rows.len(),
        logics.len()
    );
}

fn render_matrix(out: &mut String, logics: &BTreeMap<&str, Logic>) {
    out.push_str("## Per-logic matrix\n\n");
    out.push_str("| logic | total | correct | wrong | status-suspect | parse-error | panic | oom | timeout | unknown | unverified | malformed | decided% | median ms | p90 ms |\n");
    out.push_str("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |\n");

    let mut all = Counts::default();
    let mut all_walls: Vec<u64> = Vec::new();
    for (name, l) in logics {
        let walls: Vec<u64> = l.correct.iter().map(|r| r.wall_ms).collect();
        matrix_row(out, name, &l.counts, &walls);
        all.merge(&l.counts);
        all_walls.extend_from_slice(&walls);
    }
    all_walls.sort_unstable();
    matrix_row(out, "all", &all, &all_walls);
    out.push('\n');
}

/// `walls` must be ascending.
fn matrix_row(out: &mut String, name: &str, c: &Counts, walls: &[u64]) {
    // decided% = correct / (total - malformed): a malformed row is a harness
    // failure, not an instance the solver was asked to decide.
    let denom = c.total - c.malformed;
    let decided = if denom == 0 {
        "n/a".to_string()
    } else {
        format!("{:.1}", c.correct as f64 * 100.0 / denom as f64)
    };
    let _ = writeln!(
        out,
        "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
        cell(name),
        c.total,
        c.correct,
        c.wrong,
        c.status_suspect,
        c.parse_error,
        c.panic,
        c.oom,
        c.timeout,
        c.unknown,
        c.unverified,
        c.malformed,
        decided,
        opt_ms(median(walls)),
        opt_ms(p90(walls)),
    );
}

/// The gap bucket a row belongs to, or `None` for verdicts that are not gaps
/// (`correct`; `wrong`/`status-suspect` have their own section).
fn gap_key(row: &Row) -> Option<Cow<'_, str>> {
    match &row.verdict {
        Verdict::Correct | Verdict::Wrong | Verdict::StatusSuspect => None,
        Verdict::ParseError => Some(Cow::Owned(format!(
            "parse-error:{}",
            normalise_diag(diag_line(&row.stderr_head, "(error"))
        ))),
        Verdict::Panic => Some(Cow::Owned(format!(
            "panic:{}",
            normalise_diag(diag_line(&row.stderr_head, "panicked at"))
        ))),
        Verdict::Unknown(tag) => Some(Cow::Owned(format!("unknown:{tag}"))),
        Verdict::Malformed(reason) => Some(Cow::Owned(format!("malformed:{reason}"))),
        Verdict::Timeout => Some(Cow::Borrowed("timeout")),
        Verdict::Oom => Some(Cow::Borrowed("oom")),
        Verdict::Unverified => Some(Cow::Borrowed("unverified")),
        Verdict::NeedsOracle => Some(Cow::Borrowed("needs-oracle")),
    }
}

#[derive(Default)]
struct Bucket<'a> {
    count: usize,
    per_logic: BTreeMap<&'a str, usize>,
    /// The three cheapest reproducers: ascending by `(bytes, path)`, kept
    /// bounded so a 258k-row corpus never materialises a full list.
    examples: Vec<(u64, &'a str)>,
}

impl<'a> Bucket<'a> {
    fn add(&mut self, row: &'a Row) {
        self.count += 1;
        *self.per_logic.entry(row.logic.as_str()).or_default() += 1;
        self.examples.push((row.bytes, row.path.as_str()));
        self.examples.sort_unstable();
        self.examples.truncate(3);
    }
}

fn render_gaps(out: &mut String, rows: &[Row]) {
    let mut buckets: BTreeMap<String, Bucket> = BTreeMap::new();
    for row in rows {
        let Some(key) = gap_key(row) else { continue };
        // Only allocate the key String when the bucket is new.
        if let Some(b) = buckets.get_mut(key.as_ref()) {
            b.add(row);
        } else {
            buckets.entry(key.into_owned()).or_default().add(row);
        }
    }

    out.push_str("## Ranked gaps\n\n");
    if buckets.is_empty() {
        out.push_str("_none_\n\n");
        return;
    }
    // Count descending, then key ascending.
    let mut ranked: Vec<(&String, &Bucket)> = buckets.iter().collect();
    ranked.sort_by(|a, b| b.1.count.cmp(&a.1.count).then_with(|| a.0.cmp(b.0)));

    for (key, b) in ranked {
        let _ = writeln!(out, "### {} — {}\n", cell(key), b.count);
        let split: Vec<String> = b
            .per_logic
            .iter()
            .map(|(logic, n)| format!("{logic}: {n}"))
            .collect();
        let _ = writeln!(out, "{}\n", split.join(", "));
        for (bytes, path) in &b.examples {
            let _ = writeln!(out, "- `{path}` ({bytes} bytes)");
        }
        out.push('\n');
    }
}

fn render_wrong(out: &mut String, rows: &[Row]) {
    out.push_str("## Wrong answers\n\n");
    let mut wrong: Vec<&Row> = Vec::new();
    let mut suspect: Vec<&Row> = Vec::new();
    for row in rows {
        match row.verdict {
            Verdict::Wrong => wrong.push(row),
            Verdict::StatusSuspect => suspect.push(row),
            _ => {}
        }
    }
    if wrong.is_empty() && suspect.is_empty() {
        out.push_str("_none_\n\n");
        return;
    }
    wrong.sort_unstable_by(|a, b| a.path.cmp(&b.path));
    suspect.sort_unstable_by(|a, b| a.path.cmp(&b.path));

    out.push_str("| path | :status | shinri | z3 | cvc5 |\n| --- | --- | --- | --- | --- |\n");
    for row in wrong.iter().chain(suspect.iter()) {
        let (z3, cvc5) = match &row.oracle {
            Some(o) => (answer(o.z3), answer(o.cvc5)),
            None => ("-", "-"),
        };
        let _ = writeln!(
            out,
            "| `{}` | {} | {} | {} | {} |",
            cell(&row.path),
            answer(row.status),
            answer(row.answers.first().copied()),
            z3,
            cvc5,
        );
    }
    out.push('\n');
}

fn render_perf(out: &mut String, rows: &[Row], logics: &BTreeMap<&str, Logic>) {
    out.push_str("## Perf tail\n\n### timeout+oom by logic\n\n");
    out.push_str(
        "| logic | timeout | oom | timeout+oom | total |\n| --- | ---: | ---: | ---: | ---: |\n",
    );
    let (mut t_all, mut o_all, mut n_all) = (0usize, 0usize, 0usize);
    for (name, l) in logics {
        let c = &l.counts;
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} |",
            cell(name),
            c.timeout,
            c.oom,
            c.timeout + c.oom,
            c.total
        );
        t_all += c.timeout;
        o_all += c.oom;
        n_all += c.total;
    }
    let _ = writeln!(
        out,
        "| all | {t_all} | {o_all} | {} | {n_all} |\n",
        t_all + o_all
    );

    // Deciles over ALL rows' bytes: ten equal-count bins of the ascending
    // list. Empty bins (fewer than 10 rows) are skipped, so a small run
    // prints one bin per instance.
    out.push_str("### timeout+oom by size decile\n\n");
    let mut by_bytes: Vec<&Row> = rows.iter().collect();
    by_bytes.sort_unstable_by(|a, b| a.bytes.cmp(&b.bytes).then_with(|| a.path.cmp(&b.path)));
    if by_bytes.is_empty() {
        out.push_str("_none_\n\n");
    } else {
        out.push_str("| decile | bytes | rows | timeout+oom |\n| ---: | --- | ---: | ---: |\n");
        let n = by_bytes.len();
        let mut printed = 0usize;
        for i in 0..10 {
            let (lo, hi) = (i * n / 10, (i + 1) * n / 10);
            if lo >= hi {
                continue;
            }
            let bin = &by_bytes[lo..hi];
            let hits = bin
                .iter()
                .filter(|r| matches!(r.verdict, Verdict::Timeout | Verdict::Oom))
                .count();
            printed += 1;
            let _ = writeln!(
                out,
                "| {} | {}–{} | {} | {} |",
                printed,
                bin[0].bytes,
                bin[bin.len() - 1].bytes,
                bin.len(),
                hits
            );
        }
        out.push('\n');
    }

    out.push_str("### 20 slowest correct instances per logic\n\n");
    for (name, l) in logics {
        let _ = writeln!(out, "#### {}\n", cell(name));
        if l.correct.is_empty() {
            out.push_str("_none_\n\n");
            continue;
        }
        // `l.correct` is ascending by (wall_ms, path); take the tail and
        // re-sort it descending by wall_ms, ties by path ascending.
        let start = l.correct.len().saturating_sub(20);
        let mut slowest: Vec<&Row> = l.correct[start..].to_vec();
        slowest
            .sort_unstable_by(|a, b| b.wall_ms.cmp(&a.wall_ms).then_with(|| a.path.cmp(&b.path)));
        out.push_str("| path | wall_ms | bytes |\n| --- | ---: | ---: |\n");
        for r in slowest {
            let _ = writeln!(out, "| `{}` | {} | {} |", cell(&r.path), r.wall_ms, r.bytes);
        }
        out.push('\n');
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::results::read_all;
    use std::path::Path;

    #[test]
    fn diag_normalisation_merges_symbol_and_number_variants() {
        assert_eq!(
            normalise_diag("(error \"unknown symbol foo\")"),
            normalise_diag("(error \"unknown symbol bar\")")
        );
        assert_eq!(
            normalise_diag("line 12: unexpected token |x|"),
            "line N: unexpected token S"
        );
    }

    #[test]
    fn render_handles_no_correct_rows() {
        let r = Row {
            path: "QF_X/a.smt2".into(),
            logic: "QF_X".into(),
            bytes: 1,
            status: None,
            rc: Some(124),
            wall_ms: 20000,
            answers: vec![],
            stdout_errors: 0,
            fence: None,
            stderr_head: String::new(),
            verdict: Verdict::Timeout,
            oracle: None,
        };
        let md = render(None, &[r]);
        assert!(md.contains("| QF_X |"));
        assert!(md.contains("n/a"));
    }

    #[test]
    fn ranking_is_stable_under_permutation() {
        let (_, mut rows) = read_all(Path::new(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/tests/fixtures/report_rows.jsonl"
        )))
        .unwrap();
        let a = render(None, &rows);
        rows.reverse();
        assert_eq!(a, render(None, &rows));
    }
}
