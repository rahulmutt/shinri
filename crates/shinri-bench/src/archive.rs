//! Multi-frame zstd `Read` adapter and a streaming ustar extractor.
//!
//! Zenodo publishes the SMT-LIB corpus as `.tar.zst`. `ZstdStream` decodes a
//! concatenation of zstd frames (zstd files may hold several) without
//! buffering the whole archive, and `extract_tar` streams a ustar archive
//! (GNU long-name entries included) out to disk.

use std::fs;
use std::io::{self, BufRead, Read};
use std::path::{Component, Path, PathBuf};

use ruzstd::decoding::{BlockDecodingStrategy, FrameDecoder};

/// `Read` over a concatenation of zstd frames (zstd files may hold several).
pub struct ZstdStream<R: BufRead> {
    src: R,
    decoder: FrameDecoder,
    started: bool,
}

impl<R: BufRead> ZstdStream<R> {
    pub fn new(src: R) -> ZstdStream<R> {
        ZstdStream {
            src,
            decoder: FrameDecoder::new(),
            started: false,
        }
    }
}

impl<R: BufRead> Read for ZstdStream<R> {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        loop {
            if !self.started || (self.decoder.is_finished() && self.decoder.can_collect() == 0) {
                let buf = self.src.fill_buf()?;
                if buf.is_empty() {
                    // Clean EOF: no more frames.
                    return Ok(0);
                }
                self.decoder.init(&mut self.src).map_err(io::Error::other)?;
                self.started = true;
            }
            if self.decoder.can_collect() == 0 && !self.decoder.is_finished() {
                self.decoder
                    .decode_blocks(&mut self.src, BlockDecodingStrategy::UptoBytes(1 << 20))
                    .map_err(io::Error::other)?;
            }
            let n = self.decoder.read(out)?;
            if n > 0 {
                return Ok(n);
            }
        }
    }
}

/// Validate a ustar entry path is safe to extract under `dest`: reject
/// absolute paths and any `..` component, and reject empty names (after
/// trimming a leading `./`). Returns the normalised relative path.
fn safe_relative_path(raw: &str) -> io::Result<PathBuf> {
    let trimmed = raw.strip_prefix("./").unwrap_or(raw);
    if trimmed.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("archive entry has empty path: {raw:?}"),
        ));
    }
    let path = Path::new(trimmed);
    if path.is_absolute() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("archive entry has absolute path: {raw:?}"),
        ));
    }
    for comp in path.components() {
        match comp {
            Component::Normal(_) | Component::CurDir => {}
            Component::ParentDir => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("archive entry escapes destination: {raw:?}"),
                ));
            }
            Component::RootDir | Component::Prefix(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("archive entry has absolute path: {raw:?}"),
                ));
            }
        }
    }
    Ok(path.to_path_buf())
}

fn read_exact_or_eof(mut r: impl Read, buf: &mut [u8]) -> io::Result<bool> {
    // Reads buf.len() bytes; returns Ok(false) only on a clean EOF at the
    // very first byte, Ok(true) on a full read, and an UnexpectedEof error
    // on a short read partway through.
    let mut read_total = 0usize;
    while read_total < buf.len() {
        let n = r.read(&mut buf[read_total..])?;
        if n == 0 {
            if read_total == 0 {
                return Ok(false);
            }
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "truncated archive: short read",
            ));
        }
        read_total += n;
    }
    Ok(true)
}

fn parse_octal_field(field: &[u8]) -> io::Result<u64> {
    if field.first().is_some_and(|&b| b & 0x80 != 0) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "base-256 tar size fields are not supported",
        ));
    }
    let end = field
        .iter()
        .position(|&b| b == 0 || b == b' ')
        .unwrap_or(field.len());
    let s = std::str::from_utf8(&field[..end])
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "non-UTF8 tar size field"))?
        .trim();
    if s.is_empty() {
        return Ok(0);
    }
    u64::from_str_radix(s, 8).map_err(|_| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("bad octal field: {s:?}"),
        )
    })
}

fn field_str(field: &[u8]) -> io::Result<&str> {
    let end = field.iter().position(|&b| b == 0).unwrap_or(field.len());
    std::str::from_utf8(&field[..end])
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "non-UTF8 tar name field"))
}

/// Skip `size` bytes of entry body plus padding to the next 512-byte
/// boundary, without buffering the body.
fn skip_body(mut tar: impl Read, size: u64) -> io::Result<()> {
    let mut buf = [0u8; 65536];
    let mut remaining = size;
    while remaining > 0 {
        let want = remaining.min(buf.len() as u64) as usize;
        if !read_exact_or_eof(&mut tar, &mut buf[..want])? {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "truncated archive: entry body cut short",
            ));
        }
        remaining -= want as u64;
    }
    let pad = (512 - (size % 512) % 512) % 512;
    if pad > 0 {
        let mut pad_buf = [0u8; 512];
        if !read_exact_or_eof(&mut tar, &mut pad_buf[..pad as usize])? {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "truncated archive: missing entry padding",
            ));
        }
    }
    Ok(())
}

/// Stream `size` bytes of entry body from `tar` into a newly created file at
/// `dest_path`, through a fixed 64 KiB buffer, then skip the padding to the
/// next 512-byte boundary.
fn extract_regular_file(mut tar: impl Read, dest_path: &Path, size: u64) -> io::Result<()> {
    if let Some(parent) = dest_path.parent() {
        fs::create_dir_all(parent)?;
    }
    let mut out = fs::File::create(dest_path)?;
    let mut buf = [0u8; 65536];
    let mut remaining = size;
    while remaining > 0 {
        let want = remaining.min(buf.len() as u64) as usize;
        if !read_exact_or_eof(&mut tar, &mut buf[..want])? {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "truncated archive: entry body cut short",
            ));
        }
        io::Write::write_all(&mut out, &buf[..want])?;
        remaining -= want as u64;
    }
    let pad = (512 - (size % 512) % 512) % 512;
    if pad > 0 {
        let mut pad_buf = [0u8; 512];
        if !read_exact_or_eof(&mut tar, &mut pad_buf[..pad as usize])? {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "truncated archive: missing entry padding",
            ));
        }
    }
    Ok(())
}

/// Extract a (possibly GNU-longname) ustar stream into `dest`; returns the
/// number of regular files written. Entries whose normalised path escapes
/// `dest` (`..`, absolute) are rejected with an error.
pub fn extract_tar(mut tar: impl Read, dest: &Path) -> io::Result<usize> {
    let mut header = [0u8; 512];
    let mut pending_long_name: Option<String> = None;
    let mut count = 0usize;

    loop {
        if !read_exact_or_eof(&mut tar, &mut header)? {
            // Clean EOF where a header was expected: treat as end of
            // stream (well-formed archives end with two zero blocks, but
            // tolerate a stream that simply stops).
            return Ok(count);
        }

        if header.iter().all(|&b| b == 0) {
            // First zero block: peek for the second one that officially
            // ends the archive. A clean EOF here is also acceptable.
            let mut second = [0u8; 512];
            if read_exact_or_eof(&mut tar, &mut second)? && second.iter().any(|&b| b != 0) {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "archive has a lone zero header block",
                ));
            }
            return Ok(count);
        }

        let typeflag = header[156];
        let size = parse_octal_field(&header[124..136])?;

        if typeflag == b'L' {
            // GNU long name: body is the long path (NUL-terminated) for the
            // *next* header.
            let mut body = vec![0u8; size as usize];
            if !read_exact_or_eof(&mut tar, &mut body)? {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "truncated archive: GNU long-name body cut short",
                ));
            }
            let pad = (512 - (size % 512) % 512) % 512;
            if pad > 0 {
                let mut pad_buf = [0u8; 512];
                if !read_exact_or_eof(&mut tar, &mut pad_buf[..pad as usize])? {
                    return Err(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "truncated archive: missing GNU long-name padding",
                    ));
                }
            }
            let end = body.iter().position(|&b| b == 0).unwrap_or(body.len());
            let name = std::str::from_utf8(&body[..end])
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "non-UTF8 GNU long name"))?
                .to_string();
            pending_long_name = Some(name);
            continue;
        }

        let name: String = if let Some(long) = pending_long_name.take() {
            long
        } else {
            let base = field_str(&header[0..100])?;
            let prefix = field_str(&header[345..500])?;
            if prefix.is_empty() {
                base.to_string()
            } else {
                format!("{prefix}/{base}")
            }
        };

        match typeflag {
            b'0' | 0 => {
                // Regular file.
                let rel = safe_relative_path(&name)?;
                let dest_path = dest.join(&rel);
                extract_regular_file(&mut tar, &dest_path, size)?;
                count += 1;
            }
            b'5' => {
                // Directory.
                let rel = safe_relative_path(&name)?;
                fs::create_dir_all(dest.join(&rel))?;
            }
            _ => {
                // Symlinks, hard links, pax extended headers ('x'/'g'),
                // and anything else we don't materialise: consume and
                // discard the body.
                skip_body(&mut tar, size)?;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ruzstd::encoding::{compress_to_vec, CompressionLevel};

    /// Build a ustar archive in memory: (path, contents) pairs; dirs get
    /// typeflag '5'.
    ///
    /// Ruling R3: split long names at a `/` boundary so that
    /// `prefix + "/" + base == name`, per the ustar standard — a raw
    /// byte-offset split (as in the original brief) can land the split
    /// inside a path component and produce a path that round-trips to
    /// something other than `name`.
    fn tar_bytes(entries: &[(&str, Option<&[u8]>)]) -> Vec<u8> {
        let mut out = Vec::new();
        for (name, data) in entries {
            let mut h = [0u8; 512];
            let (prefix, base) = split_name(name);
            h[..base.len()].copy_from_slice(base.as_bytes());
            h[345..345 + prefix.len()].copy_from_slice(prefix.as_bytes());
            h[100..108].copy_from_slice(b"0000644\0");
            let size = data.map_or(0, |d| d.len());
            h[124..136].copy_from_slice(format!("{size:011o}\0").as_bytes());
            h[156] = if data.is_some() { b'0' } else { b'5' };
            h[257..263].copy_from_slice(b"ustar\0");
            h[263..265].copy_from_slice(b"00");
            h[148..156].copy_from_slice(b"        ");
            let sum: u32 = h.iter().map(|&b| b as u32).sum();
            h[148..156].copy_from_slice(format!("{sum:06o}\0 ").as_bytes());
            out.extend_from_slice(&h);
            if let Some(d) = data {
                out.extend_from_slice(d);
                out.resize(out.len() + (512 - d.len() % 512) % 512, 0);
            }
        }
        out.extend_from_slice(&[0u8; 1024]);
        out
    }

    /// Split `name` into (prefix, base) so that `base.len() <= 100`,
    /// `prefix.len() <= 155`, and `prefix + "/" + base == name` — matching
    /// ustar semantics (prefix and base are joined by an inserted `/`, not
    /// concatenated raw).
    fn split_name(name: &str) -> (&str, &str) {
        if name.len() <= 100 {
            return ("", name);
        }
        // Find a `/` such that the tail (base) is <= 100 bytes and the
        // head (prefix, `/` dropped) is <= 155 bytes.
        for (i, _) in name.char_indices() {
            if name.as_bytes()[i] == b'/' {
                let prefix = &name[..i];
                let base = &name[i + 1..];
                if base.len() <= 100 && prefix.len() <= 155 {
                    return (prefix, base);
                }
            }
        }
        panic!("test name {name:?} has no ustar-representable split");
    }

    /// Build a ustar archive containing a single GNU long-name ('L') entry
    /// followed by its data entry.
    fn tar_bytes_gnu_long_name(long_path: &str, data: &[u8]) -> Vec<u8> {
        let mut out = Vec::new();

        // 'L' header: name field is conventionally "././@LongLink", size is
        // the long path's length (including the NUL terminator).
        let mut lh = [0u8; 512];
        let ln = b"././@LongLink";
        lh[..ln.len()].copy_from_slice(ln);
        lh[100..108].copy_from_slice(b"0000644\0");
        let body_len = long_path.len() + 1; // + NUL
        lh[124..136].copy_from_slice(format!("{body_len:011o}\0").as_bytes());
        lh[156] = b'L';
        lh[257..263].copy_from_slice(b"ustar\0");
        lh[263..265].copy_from_slice(b"00");
        lh[148..156].copy_from_slice(b"        ");
        let sum: u32 = lh.iter().map(|&b| b as u32).sum();
        lh[148..156].copy_from_slice(format!("{sum:06o}\0 ").as_bytes());
        out.extend_from_slice(&lh);
        let mut body = long_path.as_bytes().to_vec();
        body.push(0);
        out.extend_from_slice(&body);
        out.resize(out.len() + (512 - body.len() % 512) % 512, 0);

        // Data header: name field can hold whatever (truncated) — GNU tar
        // still fills the classic name field with a truncated copy, but
        // our extractor must prefer the pending long name regardless.
        let mut dh = [0u8; 512];
        let truncated = &long_path.as_bytes()[..long_path.len().min(100)];
        dh[..truncated.len()].copy_from_slice(truncated);
        dh[100..108].copy_from_slice(b"0000644\0");
        dh[124..136].copy_from_slice(format!("{:011o}\0", data.len()).as_bytes());
        dh[156] = b'0';
        dh[257..263].copy_from_slice(b"ustar\0");
        dh[263..265].copy_from_slice(b"00");
        dh[148..156].copy_from_slice(b"        ");
        let sum: u32 = dh.iter().map(|&b| b as u32).sum();
        dh[148..156].copy_from_slice(format!("{sum:06o}\0 ").as_bytes());
        out.extend_from_slice(&dh);
        out.extend_from_slice(data);
        out.resize(out.len() + (512 - data.len() % 512) % 512, 0);

        out.extend_from_slice(&[0u8; 1024]);
        out
    }

    #[test]
    fn zstd_stream_decodes_two_concatenated_frames() {
        let a = compress_to_vec(&b"hello "[..], CompressionLevel::Fastest);
        let b = compress_to_vec(&b"world"[..], CompressionLevel::Uncompressed);
        let mut joined = a;
        joined.extend(b);
        let mut out = Vec::new();
        ZstdStream::new(std::io::Cursor::new(joined))
            .read_to_end(&mut out)
            .unwrap();
        assert_eq!(out, b"hello world");
    }

    #[test]
    fn extract_regular_files_dirs_and_prefix_names() {
        let long = format!("{}/x.smt2", "d".repeat(120));
        let tar = tar_bytes(&[
            ("QF_X/", None),
            ("QF_X/a.smt2", Some(b"(check-sat)")),
            (long.as_str(), Some(b"z")),
        ]);
        let dest = std::env::temp_dir().join(format!("shinri-bench-tar-{}", std::process::id()));
        let n = extract_tar(std::io::Cursor::new(tar), &dest).unwrap();
        assert_eq!(n, 2);
        assert_eq!(
            std::fs::read(dest.join("QF_X/a.smt2")).unwrap(),
            b"(check-sat)"
        );
        assert_eq!(std::fs::read(dest.join(&long)).unwrap(), b"z");
        std::fs::remove_dir_all(dest).unwrap();
    }

    #[test]
    fn extract_rejects_path_escape() {
        let tar = tar_bytes(&[("../evil", Some(b"x"))]);
        let dest = std::env::temp_dir().join(format!("shinri-bench-esc-{}", std::process::id()));
        assert!(extract_tar(std::io::Cursor::new(tar), &dest).is_err());
        let _ = std::fs::remove_dir_all(dest);
    }

    #[test]
    fn extract_through_zstd() {
        let tar = tar_bytes(&[("L/f.smt2", Some(b"(set-info :status sat)"))]);
        let z = compress_to_vec(&tar[..], CompressionLevel::Fastest);
        let dest = std::env::temp_dir().join(format!("shinri-bench-tz-{}", std::process::id()));
        assert_eq!(
            extract_tar(ZstdStream::new(std::io::Cursor::new(z)), &dest).unwrap(),
            1
        );
        std::fs::remove_dir_all(dest).unwrap();
    }

    #[test]
    fn extract_gnu_long_name_entry() {
        let long = format!("{}/{}/x.smt2", "d".repeat(60), "e".repeat(60));
        let tar = tar_bytes_gnu_long_name(&long, b"(set-info :status unsat)");
        let dest = std::env::temp_dir().join(format!("shinri-bench-gnu-{}", std::process::id()));
        let n = extract_tar(std::io::Cursor::new(tar), &dest).unwrap();
        assert_eq!(n, 1);
        assert_eq!(
            std::fs::read(dest.join(&long)).unwrap(),
            b"(set-info :status unsat)"
        );
        std::fs::remove_dir_all(dest).unwrap();
    }
}
