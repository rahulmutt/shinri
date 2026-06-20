//! The streaming driver: feeds bytes to the parser, executes commands on the
//! solver, and owns all presentation state (`:print-success`, output channels).

use std::fs::File;
use std::io::{self, BufWriter, Write};

use shinri_frontend::{AttrValue, Command};
use shinri_parser::{StreamItem, StreamingParser};
use shinri_solver::{CommandResponse, Solver};

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

/// Escape a string for inclusion inside an SMT-LIB `"..."` literal.
fn escape(s: &str) -> String {
    s.replace('"', "\"\"")
}

pub struct Driver {
    solver: Solver,
    parser: StreamingParser,
    pres: Presentation,
}

impl Default for Driver {
    fn default() -> Self {
        Self::new()
    }
}

impl Driver {
    pub fn new() -> Driver {
        Driver {
            solver: Solver::new(),
            parser: StreamingParser::new(),
            pres: Presentation::default(),
        }
    }

    /// Feed a chunk and execute every complete command it completes.
    /// Returns `Ok(true)` once `(exit)`/end-of-stream is reached.
    pub fn feed(&mut self, chunk: &str) -> io::Result<bool> {
        self.parser.push_str(chunk);
        self.drain()
    }

    /// Flush at input EOF: report a trailing partial command, if any.
    pub fn finish(&mut self) -> io::Result<()> {
        if let StreamItem::Command(Err(d)) = self.parser.finish(self.solver.ctx_mut()) {
            self.error(&d.message)?;
        }
        Ok(())
    }

    fn drain(&mut self) -> io::Result<bool> {
        loop {
            match self.parser.next_command(self.solver.ctx_mut()) {
                StreamItem::NeedMore => return Ok(false),
                StreamItem::Done => return Ok(true),
                StreamItem::Command(Err(d)) => self.error(&d.message)?,
                StreamItem::Command(Ok(cmd)) => {
                    if self.handle(cmd)? {
                        return Ok(true);
                    }
                }
            }
        }
    }

    /// Execute one command. Returns `Ok(true)` if it was `(exit)`.
    fn handle(&mut self, cmd: Command) -> io::Result<bool> {
        // Presentation-affecting options are handled here, not by the solver.
        if let Command::SetOption { keyword, value } = &cmd {
            if let Some(result) = self.try_presentation_option(keyword, value) {
                match result {
                    Ok(()) => self.success()?,
                    Err(msg) => self.error(&msg)?,
                }
                return Ok(false);
            }
        }

        let exiting = matches!(cmd, Command::Exit);
        match self.solver.execute(cmd) {
            CommandResponse::None => self.success()?,
            CommandResponse::Sat => self.pres.regular.write_line("sat")?,
            CommandResponse::Unsat => self.pres.regular.write_line("unsat")?,
            CommandResponse::Unknown => self.pres.regular.write_line("unknown")?,
            CommandResponse::Model(s) | CommandResponse::Values(s) => {
                self.pres.regular.write_line(&s)?
            }
            CommandResponse::Error(e) => self.error(&e)?,
        }
        Ok(exiting)
    }

    fn success(&mut self) -> io::Result<()> {
        if self.pres.print_success {
            self.pres.regular.write_line("success")?;
        }
        Ok(())
    }

    fn error(&mut self, msg: &str) -> io::Result<()> {
        self.pres.regular.write_line(&format!("(error \"{}\")", escape(msg)))
    }

    /// `Some(result)` if `keyword` is a presentation option handled here;
    /// `None` if it should fall through to the solver.
    fn try_presentation_option(
        &mut self,
        keyword: &str,
        value: &AttrValue,
    ) -> Option<Result<(), String>> {
        let AttrValue::Token(v) = value;
        match keyword {
            ":print-success" => Some(match v.as_deref() {
                Some("true") => {
                    self.pres.print_success = true;
                    Ok(())
                }
                Some("false") => {
                    self.pres.print_success = false;
                    Ok(())
                }
                _ => Err(":print-success expects true or false".to_string()),
            }),
            ":regular-output-channel" => Some(self.set_regular_channel(v.as_deref())),
            // `:diagnostic-output-channel` falls through (returns None) to the
            // solver no-op: accepted and `success`-acked, but not applied —
            // Phase 1 emits no diagnostic output to route. See Presentation.
            _ => None,
        }
    }

    fn set_regular_channel(&mut self, name: Option<&str>) -> Result<(), String> {
        let name = name.ok_or_else(|| "output-channel expects a string".to_string())?;
        match OutChannel::open(name) {
            Ok(ch) => {
                self.pres.regular = ch;
                Ok(())
            }
            Err(e) => Err(format!("cannot open channel {name}: {e}")),
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
