use clap::Parser;
use std::{
    fmt,
    io::{self, Write},
    num::NonZeroUsize,
    path::PathBuf,
    process::ExitCode,
};
use stn_validator::{ValidationError, ValidationOptions, ValidationReport, validate_source};

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
        default_value_t = ValidationOptions::default().max_proofs
    )]
    max_proofs: NonZeroUsize,
    /// Type universe resource limit
    #[arg(
        long, value_name = "N",
        default_value_t = ValidationOptions::default().max_types
    )]
    max_types: NonZeroUsize,
    /// Work budget for universe construction and proof search
    #[arg(
        long, value_name = "N",
        default_value_t = ValidationOptions::default().max_steps
    )]
    max_steps: NonZeroUsize,
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

    /// Read, validate, and write the specification, propagating failures to `main`.
    /// Determine the feature outcome only after the report has been written.
    fn run(&self) -> Result<ExitCode, CliError> {
        let options = self.validation_options();
        let input_text = std::fs::read_to_string(&self.input).map_err(|io_error| CliError::Io {
            target: self.input.display().to_string(),
            source: io_error,
        })?;
        let report = validate_source(self.input.display().to_string(), input_text, options)
            .map_err(|validation_error| CliError::Validation {
                input: self.input.clone(),
                source: validation_error,
            })?;
        self.write_report(&report)?;

        let code = if report.has_incomplete_search() {
            4
        } else if report.has_unresolved_features() {
            3
        } else {
            0
        };
        Ok(ExitCode::from(code))
    }

    /// Render the report and write it to the selected destination.
    /// Attach file or stdout context while propagating the original I/O error.
    fn write_report(&self, report: &ValidationReport) -> Result<(), CliError> {
        let rendered = report.to_string();
        match &self.output {
            Some(path) => std::fs::write(path, rendered).map_err(|source| CliError::Io {
                target: path.display().to_string(),
                source,
            }),
            None => io::stdout()
                .lock()
                .write_all(rendered.as_bytes())
                .map_err(|source| CliError::Io {
                    target: "stdout".into(),
                    source,
                }),
        }
    }
}

/// CLI failure with its original cause and the input or output being processed.
/// Error presentation and exit-code selection happen once, at the program boundary.
#[derive(Debug)]
enum CliError {
    /// Failure to read the input or write the report.
    Io {
        /// Display label of the file or stdout that failed.
        target: String,
        /// Original operating-system or UTF-8 decoding error.
        source: io::Error,
    },
    /// Syntax, declaration, or finite-expansion failure in the input document.
    Validation {
        /// Input path attached to the library diagnostic.
        input: PathBuf,
        /// Original validation failure, retaining its structured category.
        source: ValidationError,
    },
}

impl CliError {
    /// Map failures to the CLI's documented I/O, invalid-input, and resource codes.
    fn exit_code(&self) -> ExitCode {
        ExitCode::from(match self {
            Self::Io { .. } => 1,
            Self::Validation {
                source: ValidationError::ExpansionLimit { .. },
                ..
            } => 4,
            Self::Validation { .. } => 2,
        })
    }
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { target, source } => write!(f, "{target}: {source}"),
            Self::Validation { input, source } => write!(f, "{}: {source}", input.display()),
        }
    }
}

impl std::error::Error for CliError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::Validation { source, .. } => Some(source),
        }
    }
}

/// Let clap handle argument errors, then execute the command with one error handler.
fn main() -> ExitCode {
    let args = Args::parse();
    args.run().unwrap_or_else(|error| {
        eprintln!("error: {error}");
        error.exit_code()
    })
}
