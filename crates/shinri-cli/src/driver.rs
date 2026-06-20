//! The streaming driver: feeds bytes to the parser, executes commands on the
//! solver, and owns all presentation state (`:print-success`, output channels).

use std::fs::File;
use std::io::{self, BufWriter, Write};

/// An SMT-LIB output channel: a standard stream or a file.
pub enum OutChannel {
    Stdout,
    Stderr,
    File(BufWriter<File>),
}

impl OutChannel {
    /// Open a channel from an SMT-LIB channel name: `"stdout"`, `"stderr"`, or
    /// a filename (created/truncated).
    pub fn open(name: &str) -> io::Result<OutChannel> {
        match name {
            "stdout" => Ok(OutChannel::Stdout),
            "stderr" => Ok(OutChannel::Stderr),
            path => Ok(OutChannel::File(BufWriter::new(File::create(path)?))),
        }
    }

    /// Write one line (terminated by `\n`) and flush immediately, so an
    /// interactive caller sees each response without waiting on a buffer.
    pub fn write_line(&mut self, line: &str) -> io::Result<()> {
        match self {
            OutChannel::Stdout => {
                let out = io::stdout();
                let mut h = out.lock();
                writeln!(h, "{line}")?;
                h.flush()
            }
            OutChannel::Stderr => {
                let err = io::stderr();
                let mut h = err.lock();
                writeln!(h, "{line}")?;
                h.flush()
            }
            OutChannel::File(w) => {
                writeln!(w, "{line}")?;
                w.flush()
            }
        }
    }
}

/// Driver-owned presentation state. The solver never sees any of this.
///
/// Only the *regular* output channel is modeled: Phase 1 produces no diagnostic
/// (non-response) output, and SMT-LIB `(error …)` responses are written to the
/// regular channel. `:diagnostic-output-channel` is therefore accepted but not
/// applied (handled in the driver by letting it fall through to the solver).
pub struct Presentation {
    pub print_success: bool,
    pub regular: OutChannel,
}

impl Default for Presentation {
    fn default() -> Self {
        Presentation {
            print_success: true,
            regular: OutChannel::Stdout,
        }
    }
}

#[cfg(test)]
mod channel_tests {
    use super::*;

    #[test]
    fn open_maps_standard_streams() {
        assert!(matches!(OutChannel::open("stdout").unwrap(), OutChannel::Stdout));
        assert!(matches!(OutChannel::open("stderr").unwrap(), OutChannel::Stderr));
    }

    #[test]
    fn file_channel_writes_lines() {
        let path = std::env::temp_dir().join(format!("shinri_ch_{}.out", std::process::id()));
        let p = path.to_str().unwrap();
        {
            let mut ch = OutChannel::open(p).unwrap();
            ch.write_line("hello").unwrap();
            ch.write_line("world").unwrap();
        } // drop flushes/closes the file
        let body = std::fs::read_to_string(&path).unwrap();
        assert_eq!(body, "hello\nworld\n");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn default_print_success_is_true() {
        assert!(Presentation::default().print_success);
    }
}
