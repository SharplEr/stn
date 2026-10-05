use std::{ffi::OsString, io::Write, path::PathBuf, process::ExitCode};
use stn_validator::{ValidationError, ValidationOptions, validate_source};

struct Args {
    input: PathBuf,
    output: Option<PathBuf>,
    options: ValidationOptions,
}
enum Command {
    Validate(Args),
    Help,
    Version,
}

fn main() -> ExitCode {
    let args = match parse_args(std::env::args_os().skip(1)) {
        Ok(Command::Help) => {
            print_help();
            return ExitCode::SUCCESS;
        }
        Ok(Command::Version) => {
            println!("stn-validator {}", env!("CARGO_PKG_VERSION"));
            return ExitCode::SUCCESS;
        }
        Ok(Command::Validate(args)) => args,
        Err(message) => {
            eprintln!("error: {message}\nRun stn-validator --help for usage.");
            return ExitCode::from(2);
        }
    };
    let source = match std::fs::read_to_string(&args.input) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("{}: {error}", args.input.display());
            return ExitCode::from(1);
        }
    };
    let mut report = match validate_source(&source, &args.options) {
        Ok(report) => report,
        Err(error) => {
            eprintln!("{}: {error}", args.input.display());
            return ExitCode::from(if matches!(error, ValidationError::ExpansionLimit { .. }) {
                4
            } else {
                2
            });
        }
    };
    report.source_name = args.input.display().to_string();
    let code = if report.has_incomplete_search() {
        4
    } else if report.has_unresolved_features() {
        3
    } else {
        0
    };
    let rendered = report.to_string();
    let result = match args.output {
        Some(path) => {
            std::fs::write(&path, rendered).map_err(|e| format!("{}: {e}", path.display()))
        }
        None => std::io::stdout()
            .lock()
            .write_all(rendered.as_bytes())
            .map_err(|e| format!("stdout: {e}")),
    };
    if let Err(error) = result {
        eprintln!("error: {error}");
        return ExitCode::from(1);
    }
    ExitCode::from(code)
}

fn parse_args(mut args: impl Iterator<Item = OsString>) -> Result<Command, String> {
    let mut input = None;
    let mut output = None;
    let mut options = ValidationOptions::default();
    let mut positional_only = false;
    while let Some(arg) = args.next() {
        if positional_only {
            set_input(&mut input, arg)?;
            continue;
        }
        match arg.to_str() {
            Some("-h" | "--help") => return Ok(Command::Help),
            Some("-V" | "--version") => return Ok(Command::Version),
            Some("--") => positional_only = true,
            Some("-o" | "--output") => {
                output = Some(PathBuf::from(
                    args.next().ok_or("--output requires a path")?,
                ))
            }
            Some("--exhaustive") => options.exhaustive = true,
            Some(name @ ("--max-depth" | "--max-proofs" | "--max-types" | "--max-steps")) => {
                let raw = args
                    .next()
                    .ok_or_else(|| format!("{name} requires an integer"))?;
                let number: usize = raw
                    .to_str()
                    .and_then(|s| s.parse().ok())
                    .ok_or_else(|| format!("invalid {name} value: {}", raw.to_string_lossy()))?;
                if name != "--max-depth" && number == 0 {
                    return Err(format!("{name} must be positive"));
                }
                match name {
                    "--max-depth" => options.max_depth = number,
                    "--max-proofs" => options.max_proofs = number,
                    "--max-types" => options.max_types = number,
                    "--max-steps" => options.max_steps = number,
                    _ => unreachable!(),
                }
            }
            Some(s) if s.starts_with('-') => return Err(format!("unknown option: {s}")),
            _ => set_input(&mut input, arg)?,
        }
    }
    Ok(Command::Validate(Args {
        input: input.ok_or("missing input file")?,
        output,
        options,
    }))
}
fn set_input(input: &mut Option<PathBuf>, value: OsString) -> Result<(), String> {
    if input.replace(PathBuf::from(value)).is_some() {
        Err("only one input file may be specified".into())
    } else {
        Ok(())
    }
}
fn print_help() {
    println!(
        "Semantic Types Notation validator

Usage: stn-validator [OPTIONS] <INPUT>

Options:
  -o, --output <PATH>  Write the report to a file (default: stdout)
      --max-depth <N>  Synthesized collection/product nesting [default: 2]
      --max-proofs <N> Equal minimum-cost alternatives per feature [default: 5]
      --max-types <N>  Type universe resource limit [default: 20000]
      --max-steps <N>  Work resource limit [default: 2000000]
      --exhaustive     Enumerate the complete bounded constructor universe
  -h, --help           Print help
  -V, --version        Print version

Default search uses the relevant universe; see README.md for its scope.
Exit codes: 0 proved, 1 I/O error, 2 invalid input, 3 unresolved, 4 resource limit."
    );
}
