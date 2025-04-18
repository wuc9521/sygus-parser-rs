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
    let result = SyGuSFile::parse(&content);
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