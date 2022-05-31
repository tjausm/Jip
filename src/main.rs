#[macro_use]
extern crate lalrpop_util;

use std::io;
use std::path::PathBuf;
use clap::{ArgEnum, Parser, Subcommand};

// module declarations
mod ast;
mod cfg;
mod paths;
mod z3;
mod see;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Cli {

    /// Dit is een test commentje
    #[clap(subcommand)]
    mode: Mode,
}

#[derive(Subcommand)]
enum Mode {
    /// verifies file on given filepath
    VerifyFile {
        /// The file
        path: PathBuf,
    },
    VerifyString {
        /// The program as a string
        string: String,
    },
}

fn main() {
    let cli = Cli::parse();

    match cli.mode {
        Mode::VerifyFile {path} => {
            println!("{}", see::verify_file_and_print(&path))
        }
        Mode::VerifyString {string} => {
            println!("{}", see::verify_string_and_print(&string))
        }
    }
}
