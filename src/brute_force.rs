use crate::*;

// Simple brute-force implementation for use in QuickCheck
#[cfg(test)]
pub(crate) fn solve_brute_force(f: &Formula) -> SatResult {
    let num_variables = f.num_variables();
    assert!(num_variables <= 15); // just for safety

    fn assignment_for(assignment: u32, x: usize) -> bool {
        assignment & (1 << x) == 0
    }

    'search: for assignment in 0..2u32.pow(num_variables as u32) {
        'clauses: for clause in &f.clauses {
            for literal in &clause.literals {
                if assignment_for(assignment, literal.idx()) == literal.is_positive() {
                    // this clause is satisfied, let's go to the next one
                    continue 'clauses;
                }
            }
            // if we got here, this clause was not satisfied, so this assignment is bogus
            continue 'search;
        }
        // if we got here, every clause was satisfied, so we're done and satisfiable
        return SatResult::Satisfiable;
    }
    // no assignment is valid
    return SatResult::Unsatisfiable;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(x: usize) -> Literal {
        Literal::Positive(Variable(x))
    }
    fn n(x: usize) -> Literal {
        Literal::Negative(Variable(x))
    }

    #[test]
    fn solve_bcp_sat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![n(0)]);
        let f = Formula::new(vec![c1, c2]);

        assert_eq!(solve_brute_force(&f), SatResult::Satisfiable);
    }

    #[test]
    fn solve_bcp_unsat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![n(0)]);
        let c3 = Clause::new(vec![n(1)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let mut solver = Solver::new(&f);
        assert_eq!(solve_brute_force(&f), SatResult::Unsatisfiable);
    }

    #[test]
    fn solve_bcp_decide_sat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![p(0)]);
        let f = Formula::new(vec![c1, c2]);

        let mut solver = Solver::new(&f);
        assert_eq!(solve_brute_force(&f), SatResult::Satisfiable);
    }

    #[test]
    fn solve_conflict_sat() {
        let c1 = Clause::new(vec![p(0), p(1), p(2)]);
        let c2 = Clause::new(vec![n(0), n(1), p(2)]);
        let c3 = Clause::new(vec![n(1), n(2)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let mut solver = Solver::new(&f);
        assert_eq!(solve_brute_force(&f), SatResult::Satisfiable);
    }

    #[test]
    fn solve_conflict_unsat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![n(0)]);
        let c3 = Clause::new(vec![n(1)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let mut solver = Solver::new(&f);
        assert_eq!(solve_brute_force(&f), SatResult::Unsatisfiable);
    }
}
