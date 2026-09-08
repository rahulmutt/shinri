//! Corpus manifest, fetch, verify, and extract.
//!
//! `bench/manifest.toml` pins the Zenodo SMT-LIB release: per-archive md5
//! and size. `fetch` downloads each selected archive (resumable, via
//! `curl`), verifies its md5, extracts it through
//! `archive::{ZstdStream, extract_tar}`, and writes a `.verified` marker
//! (the md5) so a repeat run can skip already-good archives.

use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, BufReader};
use std::path::Path;
use std::process::Command;

use crate::archive::{extract_tar, ZstdStream};

/// One archive entry from `bench/manifest.toml`, with `url` already
/// resolved from `base_url + file + "/content"`.
pub struct ArchiveSpec {
    pub logic: String,
    pub url: String,
    pub md5: String,
    pub size: u64,
    pub smt2_count: Option<u64>,
}

/// The parsed `bench/manifest.toml`.
pub struct Manifest {
    pub record: String,
    pub base_url: String,
    pub archives: Vec<ArchiveSpec>,
}

#[derive(Debug, Clone)]
enum TomlValue {
    Str(String),
    Int(u64),
}

impl TomlValue {
    fn into_string(self) -> Result<String, String> {
        match self {
            TomlValue::Str(s) => Ok(s),
            TomlValue::Int(n) => Err(format!("expected a string, got integer {n}")),
        }
    }

    fn into_int(self) -> Result<u64, String> {
        match self {
            TomlValue::Int(n) => Ok(n),
            TomlValue::Str(s) => Err(format!("expected an integer, got string {s:?}")),
        }
    }
}

fn parse_value(raw: &str) -> Result<TomlValue, String> {
    let raw = raw.trim();
    if raw.len() >= 2 && raw.starts_with('"') && raw.ends_with('"') {
        Ok(TomlValue::Str(raw[1..raw.len() - 1].to_string()))
    } else {
        raw.parse::<u64>()
            .map(TomlValue::Int)
            .map_err(|_| format!("cannot parse value: {raw:?}"))
    }
}

const TOP_KEYS: &[&str] = &["record", "base_url"];
const ARCHIVE_KEYS: &[&str] = &["logic", "file", "size", "md5", "smt2_count"];

/// Line-oriented `bench/manifest.toml` reader: `key = "string"` / `key =
/// 123` pairs, `[[archive]]` starts a new archive table, `#` starts a
/// comment (and blank lines are skipped). Any key other than the known
/// top-level keys (`record`, `base_url`) or archive keys (`logic`,
/// `file`, `size`, `md5`, `smt2_count`) is rejected, as is an archive
/// missing one of `logic`, `file`, `size`, `md5`.
pub fn parse_manifest(text: &str) -> Result<Manifest, String> {
    let mut top: HashMap<&str, TomlValue> = HashMap::new();
    let mut archives_raw: Vec<HashMap<&str, TomlValue>> = Vec::new();

    for (lineno, raw_line) in text.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "[[archive]]" {
            archives_raw.push(HashMap::new());
            continue;
        }
        let (key, value) = line
            .split_once('=')
            .ok_or_else(|| format!("manifest.toml:{}: expected `key = value`", lineno + 1))?;
        let key = key.trim();
        let value = parse_value(value).map_err(|e| format!("manifest.toml:{}: {e}", lineno + 1))?;

        if let Some(table) = archives_raw.last_mut() {
            let known = ARCHIVE_KEYS.iter().copied().find(|k| *k == key);
            let known = known.ok_or_else(|| {
                format!("manifest.toml:{}: unknown archive key `{key}`", lineno + 1)
            })?;
            table.insert(known, value);
        } else {
            let known = TOP_KEYS.iter().copied().find(|k| *k == key);
            let known = known.ok_or_else(|| {
                format!(
                    "manifest.toml:{}: unknown top-level key `{key}`",
                    lineno + 1
                )
            })?;
            top.insert(known, value);
        }
    }

    let record = top
        .remove("record")
        .ok_or("manifest.toml: missing top-level `record`")?
        .into_string()?;
    let base_url = top
        .remove("base_url")
        .ok_or("manifest.toml: missing top-level `base_url`")?
        .into_string()?;

    let mut archives = Vec::with_capacity(archives_raw.len());
    for mut table in archives_raw {
        let logic = table
            .remove("logic")
            .ok_or("archive missing `logic`")?
            .into_string()?;
        let file = table
            .remove("file")
            .ok_or_else(|| format!("archive `{logic}` missing `file`"))?
            .into_string()?;
        let size = table
            .remove("size")
            .ok_or_else(|| format!("archive `{logic}` missing `size`"))?
            .into_int()?;
        let md5 = table
            .remove("md5")
            .ok_or_else(|| format!("archive `{logic}` missing `md5`"))?
            .into_string()?;
        let smt2_count = table
            .remove("smt2_count")
            .map(TomlValue::into_int)
            .transpose()?;
        let url = format!("{base_url}{file}/content");
        archives.push(ArchiveSpec {
            logic,
            url,
            md5,
            size,
            smt2_count,
        });
    }

    Ok(Manifest {
        record,
        base_url,
        archives,
    })
}

/// Read and parse a manifest file.
pub fn load_manifest(path: &Path) -> Result<Manifest, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    parse_manifest(&text)
}

/// Rewrite `url`'s `base_url` prefix to `mirror` (`<mirror>/<rest>`);
/// returns `url` unchanged if it doesn't start with `base_url`. A local
/// filesystem mirror path (starting with `/`) is returned as a plain
/// path here — `fetch` prefixes it with `file://` before handing it to
/// `curl`.
pub fn mirror_url(url: &str, base_url: &str, mirror: &str) -> String {
    match url.strip_prefix(base_url) {
        Some(rest) => format!("{mirror}/{rest}"),
        None => url.to_string(),
    }
}

/// `md5sum <path>`, taking the first 32 characters of stdout as the hex
/// digest.
pub fn md5_of(path: &Path) -> io::Result<String> {
    let output = Command::new("md5sum").arg(path).output()?;
    if !output.status.success() {
        return Err(io::Error::other(format!(
            "md5sum exited with {}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    if stdout.len() < 32 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("unexpected md5sum output: {stdout:?}"),
        ));
    }
    Ok(stdout[..32].to_string())
}

/// Count of `.smt2` files anywhere under `dir`, recursively. Deliberately
/// independent of `instance::walk` (which additionally reads each file's
/// head to scan for a status comment) — this only needs a count.
fn count_smt2_files(dir: &Path) -> io::Result<u64> {
    let mut n = 0u64;
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let file_type = entry.file_type()?;
        if file_type.is_dir() {
            n += count_smt2_files(&path)?;
        } else if file_type.is_file() && path.extension().and_then(|e| e.to_str()) == Some("smt2") {
            n += 1;
        }
    }
    Ok(n)
}

/// The archive's on-disk file name, as published in the manifest (e.g.
/// `QF_AX.tar.zst`), recovered from `url` (`.../<file>/content`).
fn archive_filename(url: &str) -> &str {
    let without_content = url.strip_suffix("/content").unwrap_or(url);
    without_content
        .rsplit('/')
        .next()
        .unwrap_or(without_content)
}

/// `curl` → `md5sum` → extract → `.verified`, for each of `logics` (an
/// unknown logic is a hard `Err`, checked up front so it fails even under
/// `dry_run`). `mirror`, when given, is passed to `mirror_url` in place
/// of `manifest.base_url`; a mirror starting with `/` is a local path,
/// passed to `curl` as a `file://` URL.
///
/// Progress goes to stderr, one line per archive (already-verified /
/// downloading / md5 ok / extracted-N). A failure on one archive (bad
/// download, md5 mismatch, bad extraction) is recorded and does not stop
/// the remaining archives; at the end, if any archive failed, every
/// recorded error is printed and `fetch` returns `Err`.
pub fn fetch(
    manifest: &Manifest,
    logics: &[String],
    corpus_dir: &Path,
    mirror: Option<&str>,
    dry_run: bool,
) -> Result<(), String> {
    let mut selected = Vec::with_capacity(logics.len());
    for logic in logics {
        let archive = manifest
            .archives
            .iter()
            .find(|a| &a.logic == logic)
            .ok_or_else(|| format!("unknown logic: {logic}"))?;
        selected.push(archive);
    }

    let mut errors: Vec<String> = Vec::new();
    for archive in selected {
        if let Err(e) = fetch_one(manifest, archive, corpus_dir, mirror, dry_run) {
            errors.push(format!("{}: {e}", archive.logic));
        }
    }

    if errors.is_empty() {
        return Ok(());
    }
    eprintln!("fetch: {} archive(s) failed:", errors.len());
    for e in &errors {
        eprintln!("  {e}");
    }
    Err(errors.join("; "))
}

fn fetch_one(
    manifest: &Manifest,
    archive: &ArchiveSpec,
    corpus_dir: &Path,
    mirror: Option<&str>,
    dry_run: bool,
) -> Result<(), String> {
    let logic = &archive.logic;
    let logic_dir = corpus_dir.join(logic);
    let verified_path = logic_dir.join(".verified");

    if let Ok(existing) = fs::read_to_string(&verified_path) {
        if existing.trim() == archive.md5.trim() {
            eprintln!("{logic}: already verified (md5 {})", archive.md5);
            return Ok(());
        }
    }

    let effective_url = match mirror {
        Some(m) => {
            let rewritten = mirror_url(&archive.url, &manifest.base_url, m);
            if m.starts_with('/') {
                format!("file://{rewritten}")
            } else {
                rewritten
            }
        }
        None => archive.url.clone(),
    };

    if dry_run {
        eprintln!("{logic}: (dry-run) {effective_url}");
        return Ok(());
    }

    let dl_dir = corpus_dir.join(".dl");
    fs::create_dir_all(&dl_dir).map_err(|e| format!("creating {}: {e}", dl_dir.display()))?;
    let file_name = archive_filename(&archive.url);
    let dl_path = dl_dir.join(file_name);

    eprintln!("{logic}: downloading {effective_url}");
    let status = Command::new("curl")
        .args([
            "-L",
            "--fail",
            "--retry",
            "5",
            "--retry-all-errors",
            "-C",
            "-",
            "-o",
        ])
        .arg(&dl_path)
        .arg(&effective_url)
        .status()
        .map_err(|e| format!("spawning curl: {e}"))?;
    if !status.success() {
        return Err(format!("curl exited with {status}"));
    }

    let digest = md5_of(&dl_path).map_err(|e| format!("md5sum: {e}"))?;
    if digest != archive.md5 {
        let bad_path = dl_dir.join(format!("{file_name}.bad"));
        let _ = fs::rename(&dl_path, &bad_path);
        return Err(format!(
            "md5 mismatch: expected {}, got {digest} (renamed to {})",
            archive.md5,
            bad_path.display()
        ));
    }
    eprintln!("{logic}: md5 ok ({digest})");

    // A half-extracted tree from a previously killed run must not survive
    // to poison this extraction — but only when it isn't already known
    // good (`.verified` present, which also means we'd have skipped
    // above; this covers the case where a stale `.verified` had a
    // different, now-superseded md5).
    if logic_dir.exists() && !verified_path.exists() {
        fs::remove_dir_all(&logic_dir)
            .map_err(|e| format!("removing stale {}: {e}", logic_dir.display()))?;
    }

    let file = File::open(&dl_path).map_err(|e| format!("opening {}: {e}", dl_path.display()))?;
    let zstd = ZstdStream::new(BufReader::new(file));
    extract_tar(zstd, corpus_dir).map_err(|e| format!("extracting: {e}"))?;

    if !logic_dir.is_dir() {
        return Err(format!(
            "archive did not contain a top-level {logic}/ directory"
        ));
    }

    let count = count_smt2_files(&logic_dir).map_err(|e| format!("counting .smt2 files: {e}"))?;
    eprintln!("{logic}: extracted {count} .smt2 files");
    if let Some(expected) = archive.smt2_count {
        if expected != count {
            return Err(format!("expected {expected} .smt2 files, found {count}"));
        }
    }

    fs::write(&verified_path, &archive.md5)
        .map_err(|e| format!("writing {}: {e}", verified_path.display()))?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    const MINI: &str = "record = \"10.5281/zenodo.1\"\nbase_url = \"https://h/f/\"\n\n[[archive]]\nlogic = \"QF_AX\"\nfile = \"QF_AX.tar.zst\"\nsize = 10\nmd5 = \"6d323ea02eb4d74e8ac77420bf94e3cb\"\nsmt2_count = 551\n";

    #[test]
    fn parses_manifest() {
        let m = parse_manifest(MINI).unwrap();
        assert_eq!(m.record, "10.5281/zenodo.1");
        assert_eq!(m.archives.len(), 1);
        assert_eq!(m.archives[0].url, "https://h/f/QF_AX.tar.zst/content");
        assert_eq!(m.archives[0].smt2_count, Some(551));
    }

    #[test]
    fn rejects_missing_md5_and_unknown_key() {
        assert!(
            parse_manifest(&MINI.replace("md5 = \"6d323ea02eb4d74e8ac77420bf94e3cb\"\n", ""))
                .is_err()
        );
        assert!(parse_manifest(&format!("{MINI}sha1 = \"x\"\n")).is_err());
    }

    #[test]
    fn committed_manifest_parses_and_lists_every_scoped_logic() {
        let m = load_manifest(Path::new(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../bench/manifest.toml"
        )))
        .unwrap();
        for l in [
            "QF_BV", "QF_ABV", "QF_AUFBV", "QF_UFBV", "QF_FP", "QF_BVFP", "QF_LRA", "QF_LIA",
            "QF_UF", "QF_UFLIA", "QF_UFLRA", "QF_AX", "QF_S", "QF_SLIA", "QF_DT",
        ] {
            assert!(m.archives.iter().any(|a| a.logic == l), "missing {l}");
        }
        for a in &m.archives {
            assert_eq!(a.md5.len(), 32);
            assert!(a.md5.bytes().all(|b| b.is_ascii_hexdigit()));
        }
    }

    #[test]
    fn md5_of_matches_coreutils_vector() {
        let p = std::env::temp_dir().join(format!("shinri-bench-md5-{}", std::process::id()));
        std::fs::write(&p, b"abc").unwrap();
        assert_eq!(md5_of(&p).unwrap(), "900150983cd24fb0d6963f7d28e17f72");
        std::fs::remove_file(p).unwrap();
    }

    #[test]
    fn dry_run_prints_urls_and_touches_nothing() {
        let m = parse_manifest(MINI).unwrap();
        let dir = std::env::temp_dir().join(format!("shinri-bench-dry-{}", std::process::id()));
        fetch(&m, &["QF_AX".into()], &dir, None, true).unwrap();
        assert!(!dir.exists());
        fetch(&m, &["QF_NOPE".into()], &dir, None, true).unwrap_err();
    }

    #[test]
    fn mirror_rewrites_prefix() {
        assert_eq!(
            mirror_url(
                "https://zenodo.org/api/records/11061097/files/QF_AX.tar.zst/content",
                "https://zenodo.org/api/records/11061097/files/",
                "/mnt/mirror"
            ),
            "/mnt/mirror/QF_AX.tar.zst/content"
        );
    }
}
