use clap::{Parser, builder::RangedU64ValueParser};
use std::{io::Write, path::PathBuf, process::ExitCode};
use stn_validator::{ValidationError, ValidationOptions, validate_source};

/// Declarative command-line schema parsed by clap before any files are opened.
/// Field attributes define flags, defaults, and admissible numeric values.
#[derive(Parser)]
#[command(
    name = "stn-validator",
    version,
    about = "Semantic Types Notation validator",
    after_help = "Default search uses the relevant universe; see README.md for its scope.\nExit codes: 0 proved, 1 I/O error, 2 invalid input, 3 unresolved, 4 resource limit."
)]
struct Args {
    /// Path of the specification to read as UTF-8
    #[arg(value_name = "INPUT")]
    input: PathBuf,
    /// Write the report to a file (default: stdout)
    #[arg(short, long, value_name = "PATH")]
    output: Option<PathBuf>,
    /// Maximum nesting depth of synthesized collections and products
    #[arg(long, value_name = "N", default_value_t = ValidationOptions::default().max_depth)]
    max_depth: usize,
    /// Maximum equal-minimum-cost proofs per feature
    #[arg(
        long, value_name = "N",
        default_value_t = ValidationOptions::default().max_proofs,
        value_parser = RangedU64ValueParser::<usize>::new().range(1..)
    )]
    max_proofs: usize,
    /// Type universe resource limit
    #[arg(
        long, value_name = "N",
        default_value_t = ValidationOptions::default().max_types,
        value_parser = RangedU64ValueParser::<usize>::new().range(1..)
    )]
    max_types: usize,
    /// Work budget for universe construction and proof search
    #[arg(
        long, value_name = "N",
        default_value_t = ValidationOptions::default().max_steps,
        value_parser = RangedU64ValueParser::<usize>::new().range(1..)
    )]
    max_steps: usize,
    /// Enumerate the complete bounded constructor universe
    #[arg(long)]
    exhaustive: bool,
}

impl Args {
    /// Convert CLI values into the search configuration used by the library.
    fn validation_options(&self) -> ValidationOptions {
        ValidationOptions {
            max_depth: self.max_depth,
            max_proofs: self.max_proofs,
            max_types: self.max_types,
            max_steps: self.max_steps,
            exhaustive: self.exhaustive,
        }
    }
}

/// Parse CLI options, validate the input, and write a report to the chosen output.
/// Map I/O, invalid declarations, unresolved goals, and resource exhaustion to
/// the documented exit codes after handling any report-writing failure.
fn main() -> ExitCode {
    let args = Args::parse();
    let options = args.validation_options();
    let source = match std::fs::read_to_string(&args.input) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("{}: {error}", args.input.display());
            return ExitCode::from(1);
        }
    };
    let report = match validate_source(args.input.display().to_string(), &source, &options) {
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
    let code = if report.has_incomplete_search() {
        4
    } else if report.has_unresolved_features() {
        3
    } else {
        0
    };
    ExitCode::from(code)
}
