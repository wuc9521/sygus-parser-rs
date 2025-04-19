use std::error::Error;
use std::fs;
use std::path::PathBuf;
use clap::Parser;
use sygus_parser::ast::SyGuSFile;

/// SyGuS Parser Application
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the SyGuS file to parse
    #[arg(short, long)]
    file: PathBuf,

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

    // Read content from the provided file path
    let content = match fs::read_to_string(&args.file) {
        Ok(content) => content,
        Err(e) => {
            eprintln!("Error reading file {}: {}", args.file.display(), e);
            return Err(e.into());
        }
    };

    if args.verbose {
        println!("Parsing file: {}", args.file.display());
    }

    // Parse the SyGuS problem
    let result = SyGuSFile::from_str(&content);
    match result {
        Ok(problem) => {
            if args.verbose {
                println!("{:?}", problem);
            } else {
                println!("Use --verbose for detailed output");
            }
        }
        Err(e) => {
            eprintln!("Error parsing SyGuS problem: {}", e);
            return Err(e.into());
        }
    }
    
    Ok(())
}