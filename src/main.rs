use clap::Parser;
use log::{error, info};
use std::error::Error;
use std::fs;
use std::io::{self, Read, Write};
use std::path::PathBuf;
use sygus_parser::ast::SyGuSFile;

/// SyGuS Parser Application
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Read from input stream (stdin)
    #[arg(short, long)]
    r#in: bool,

    /// Path to the SyGuS file to parse (required if --in is not used)
    file_path: Option<PathBuf>,

    /// Enable verbose output
    #[arg(short, long, default_value_t = false)]
    verbose: bool,
}

/// Runs an application that parses a SyGuS input file and outputs either a detailed or minimal representation of the parsed problem.
///
///
/// Processes command-line arguments to determine the file path for the SyGuS input and whether verbose output is enabled, reads the file content, and attempts to parse it according to the SyGuS v2.1 standard.
/// In the event of errors during file reading or parsing, it provides appropriate error messages before terminating.
/// When parsing succeeds, it conditionally prints detailed information if verbosity is enabled, or prompts the user to enable verbose mode.
fn main() -> Result<(), Box<dyn Error>> {
    // Parse command line arguments
    let args = Args::parse();
    env_logger::Builder::from_default_env()
        .format(|buf, record| {
            let level = match record.level() {
                log::Level::Error => "\x1b[31mERROR\x1b[0m",
                log::Level::Warn => "\x1b[33mWARN\x1b[0m",
                log::Level::Info => "\x1b[34mINFO\x1b[0m",
                log::Level::Debug => "\x1b[35mDEBUG\x1b[0m",
                log::Level::Trace => "\x1b[36mTRACE\x1b[0m",
            };
            let msg = if record.target() == "parsed" {
                format!("\x1b[32m{}\x1b[0m", record.args())
            } else {
                record.args().to_string()
            };
            writeln!(
                buf,
                "{} {} {}:{}",
                level,
                msg,
                record.file().unwrap_or("unknown"),
                record.line().unwrap_or(0)
            )
        })
        .filter_level(if args.verbose {
            log::LevelFilter::Info
        } else {
            log::LevelFilter::Warn
        })
        .init();

    // Read content from file or stdin based on arguments
    let content = if args.r#in {
        // Read from stdin
        if args.verbose {
            info!("Reading from stdin");
        }
        let mut buffer = String::new();
        io::stdin().read_to_string(&mut buffer).map_err(|e| {
            error!("Error reading from stdin: {}", e);
            e
        })?;
        buffer
    } else {
        // Read from file path
        let file_path = args.file_path.ok_or_else(|| {
            let err_msg = "Error: file path is required when --in is not used";
            error!("{}", err_msg);
            io::Error::new(io::ErrorKind::InvalidInput, err_msg)
        })?;

        if args.verbose {
            info!("Parsing: {}", file_path.display());
        }

        fs::read_to_string(&file_path).map_err(|e| {
            error!("Error reading file {}: {}", file_path.display(), e);
            e
        })?
    };

    // Parse the SyGuS problem
    let result = SyGuSFile::from_str(&content);
    match result {
        Ok(problem) => {
            if args.verbose {
                info!(target: "parsed", "{}", problem);
            }
        }
        Err(e) => {
            error!("Error parsing SyGuS problem: {}", e);
            return Err(e.into());
        }
    }

    Ok(())
}
