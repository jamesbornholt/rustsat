use rustsat::*;

fn main() {
    let c1 = Clause::new(vec![Literal::Positive(Variable(0)), Literal::Positive(Variable(1))]);
    let c2 = Clause::new(vec![Literal::Negative(Variable(0))]);
    let f = Formula::new(vec![c1, c2]);

    let mut solver = Solver::new(&f);

    let exit_code = match solver.solve() {
        SatResult::Satisfiable => 0,
        SatResult::Unsatisfiable => 1,
    };
    std::process::exit(exit_code);
}
