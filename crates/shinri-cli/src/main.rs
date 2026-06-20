mod args;
mod driver;

use std::io::{self, BufRead, Read};
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
        Ok(args::Invocation::Run { input }) => run(input),
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

fn run(input: args::Input) -> ExitCode {
    let mut driver = driver::Driver::new();
    let result = match input {
        args::Input::File(path) => run_file(&mut driver, &path),
        args::Input::Stdin => run_stdin(&mut driver),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(2)
        }
    }
}

fn run_file(driver: &mut driver::Driver, path: &str) -> io::Result<()> {
    let mut src = String::new();
    std::fs::File::open(path)?.read_to_string(&mut src)?;
    if driver.feed(&src)? {
        return Ok(());
    }
    driver.finish()
}

fn run_stdin(driver: &mut driver::Driver) -> io::Result<()> {
    let stdin = io::stdin();
    let mut lock = stdin.lock();
    let mut line = String::new();
    loop {
        line.clear();
        if lock.read_line(&mut line)? == 0 {
            break; // EOF (Ctrl-D / closed pipe)
        }
        if driver.feed(&line)? {
            return Ok(()); // (exit) seen
        }
    }
    driver.finish()
}
