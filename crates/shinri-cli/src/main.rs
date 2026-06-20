mod args;
mod driver;

use std::process::ExitCode;

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    match args::parse_args(argv) {
        Ok(args::Invocation::Help) => {
            print!("{}", args::USAGE);
            ExitCode::SUCCESS
        }
        Ok(args::Invocation::Version) => {
            println!("shinri {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Ok(args::Invocation::Run { input: _ }) => {
            // Wired to the streaming driver in a later task.
            ExitCode::SUCCESS
        }
        Err(e) => {
            let msg = match e {
                args::ArgError::Unknown(a) => format!("error: unknown argument '{a}'"),
                args::ArgError::TooMany => "error: more than one input file given".to_string(),
            };
            eprintln!("{msg}\n\n{}", args::USAGE);
            ExitCode::from(2)
        }
    }
}
