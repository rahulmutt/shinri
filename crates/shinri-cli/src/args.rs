//! Hand-rolled command-line argument parsing (no external deps).

#[derive(Debug, PartialEq, Eq)]
pub enum Input {
    File(String),
    Stdin,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Invocation {
    Run { input: Input },
    Help,
    Version,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ArgError {
    Unknown(String),
    TooMany,
}

pub const USAGE: &str = "\
Usage: shinri [FILE]

Read an SMT-LIB 2.6 script from FILE, or from stdin if no FILE is given.

Options:
  -h, --help       Print this help and exit
  -V, --version    Print version and exit
";

/// Parse arguments (excluding the program name).
pub fn parse_args<I: IntoIterator<Item = String>>(args: I) -> Result<Invocation, ArgError> {
    let mut file: Option<String> = None;
    for a in args {
        match a.as_str() {
            "-h" | "--help" => return Ok(Invocation::Help),
            "-V" | "--version" => return Ok(Invocation::Version),
            s if s.starts_with('-') && s != "-" => return Err(ArgError::Unknown(a)),
            _ => {
                if file.is_some() {
                    return Err(ArgError::TooMany);
                }
                file = Some(a);
            }
        }
    }
    let input = match file {
        Some(f) => Input::File(f),
        None => Input::Stdin,
    };
    Ok(Invocation::Run { input })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(args: &[&str]) -> Result<Invocation, ArgError> {
        parse_args(args.iter().map(|s| s.to_string()))
    }

    #[test]
    fn no_args_reads_stdin() {
        assert_eq!(parse(&[]), Ok(Invocation::Run { input: Input::Stdin }));
    }

    #[test]
    fn file_arg_is_file_input() {
        assert_eq!(
            parse(&["foo.smt2"]),
            Ok(Invocation::Run { input: Input::File("foo.smt2".into()) })
        );
    }

    #[test]
    fn help_and_version_flags() {
        assert_eq!(parse(&["--help"]), Ok(Invocation::Help));
        assert_eq!(parse(&["-h"]), Ok(Invocation::Help));
        assert_eq!(parse(&["--version"]), Ok(Invocation::Version));
        assert_eq!(parse(&["-V"]), Ok(Invocation::Version));
    }

    #[test]
    fn unknown_flag_errors() {
        assert_eq!(parse(&["--nope"]), Err(ArgError::Unknown("--nope".into())));
    }

    #[test]
    fn two_files_error() {
        assert_eq!(parse(&["a.smt2", "b.smt2"]), Err(ArgError::TooMany));
    }
}
