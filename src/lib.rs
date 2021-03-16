//! A stupid little SAT solver, mostly for fooling around with Rust stuff.
//!
//! Currently this is an implementation of DPLL with chronological backtracking, implemented via
//! clause learning.

pub mod formula;
mod solver;

#[cfg(test)]
mod brute_force;

#[derive(PartialEq, Clone, Debug)]
pub enum SatResult {
    Satisfiable, // TODO model
    Unsatisfiable,
}

pub use solver::Solver;
