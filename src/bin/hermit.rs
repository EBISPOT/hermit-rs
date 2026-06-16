// The `hermit` command-line binary (port of HermiT's `CommandLine.main`).

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match hermit_rs::cli::run(&args) {
        Ok(output) => {
            // `run` returns the exact bytes the global output writer produced
            // (each action line already carries its trailing newline, mirroring
            // Java's autoflush PrintWriter), so emit it verbatim with `print!` and
            // add nothing. An empty string (e.g. an `-o FILE` run) prints nothing.
            print!("{output}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            // CommandLine.java:797-800: print message, usageString, then help hint.
            eprintln!("{error}");
            eprintln!("{}", hermit_rs::cli::USAGE);
            eprintln!("Try 'hermit --help' for more information.");
            ExitCode::FAILURE
        }
    }
}
