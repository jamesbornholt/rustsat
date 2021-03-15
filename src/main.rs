use clap::{App, Arg};
use rustsat::formula::dimacs::{parse, DimacsParseError};
use rustsat::formula::Formula;
use rustsat::*;
use std::fs::File;

fn main() {
    let matches = App::new("solver")
        .arg(Arg::with_name("INPUT").help("input file (in CNF)").index(1))
        .get_matches();

    let f = if let Some(path) = matches.value_of("INPUT") {
        parse_from_file(path)
    } else {
        parse(std::io::stdin())
    };

    match f {
        Ok(f) => {
            let mut solver = Solver::new(f);

            let exit_code = match solver.solve() {
                SatResult::Satisfiable => 0,
                SatResult::Unsatisfiable => 1,
            };
            std::process::exit(exit_code);
        }
        Err(e) => {
            eprintln!("parse error: {:?}", e);
            std::process::exit(-1);
        }
    }
}

fn parse_from_file(path: &str) -> Result<Formula, DimacsParseError> {
    let file = File::open(path)?;
    parse(file)
}
