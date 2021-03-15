#[cfg(test)]
extern crate quickcheck;

mod formula;
mod solver;

#[cfg(test)]
mod brute_force;

#[derive(PartialEq, Clone, Debug)]
pub enum SatResult {
    Satisfiable, // TODO model
    Unsatisfiable,
}

pub use formula::{Clause, Formula, Literal, Variable};
pub use solver::Solver;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::{Clause, Formula, Literal, Variable};
    use crate::solver::Solver;
    use brute_force::solve_brute_force;
    use quickcheck::{Arbitrary, Gen, QuickCheck};
    use std::collections::HashMap;

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

        let mut solver = Solver::new(f);
        assert_eq!(solver.solve(), SatResult::Satisfiable);
    }

    #[test]
    fn solve_bcp_unsat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![n(0)]);
        let c3 = Clause::new(vec![n(1)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let mut solver = Solver::new(f);
        assert_eq!(solver.solve(), SatResult::Unsatisfiable);
    }

    #[test]
    fn solve_bcp_decide_sat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![p(0)]);
        let f = Formula::new(vec![c1, c2]);

        let mut solver = Solver::new(f);
        assert_eq!(solver.solve(), SatResult::Satisfiable);
    }

    #[test]
    fn solve_conflict_sat() {
        let c1 = Clause::new(vec![p(0), p(1), p(2)]);
        let c2 = Clause::new(vec![n(0), n(1), p(2)]);
        let c3 = Clause::new(vec![n(1), n(2)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let mut solver = Solver::new(f);
        assert_eq!(solver.solve(), SatResult::Satisfiable);
    }

    #[test]
    fn solve_conflict_unsat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![n(0)]);
        let c3 = Clause::new(vec![n(1)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let mut solver = Solver::new(f);
        assert_eq!(solver.solve(), SatResult::Unsatisfiable);
    }

    fn canonicalize(f: &Formula) -> Formula {
        // We're going to be renaming the variables to start at 0
        let mut rewrite = HashMap::new();
        for clause in f.clauses() {
            for literal in clause.literals() {
                if !rewrite.contains_key(&literal.idx()) {
                    rewrite.insert(literal.idx(), rewrite.len());
                }
            }
        }
        Formula::new(f.clauses().map(|clause| {
            Clause::new(clause.literals().map(|literal| match literal {
                Literal::Positive(Variable(x)) => Literal::Positive(Variable(rewrite[x])),
                Literal::Negative(Variable(x)) => Literal::Negative(Variable(rewrite[x])),
            }))
        }))
    }

    #[test]
    fn test_canonicalize() {
        let c1 = Clause::new(vec![p(10), p(11)]);
        let c2 = Clause::new(vec![n(10)]);
        let c3 = Clause::new(vec![n(11)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let f2 = canonicalize(&f);
        assert_eq!(f2.clauses().count(), 3);
        assert_eq!(
            f2.clauses().nth(0).unwrap().literals().cloned().collect::<Vec<_>>(),
            vec![p(0), p(1)]
        );
        assert_eq!(
            f2.clauses().nth(1).unwrap().literals().cloned().collect::<Vec<_>>(),
            vec![n(0)]
        );
        assert_eq!(
            f2.clauses().nth(2).unwrap().literals().cloned().collect::<Vec<_>>(),
            vec![n(1)]
        );
    }

    // QuickCheck for formulas
    impl Arbitrary for Formula {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            const MAX_VARS: u32 = 15;
            const MAX_CLAUSES: u32 = 10;
            let num_vars = g.next_u32() % MAX_VARS + 1;
            let num_clauses = g.next_u32() % MAX_CLAUSES + 1;

            let f = Formula::new((0..num_clauses).map(|_| {
                let clause_size = g.next_u32() % num_vars + 1;
                Clause::new((0..clause_size).map(|_| {
                    let var = Variable((g.next_u32() % num_vars) as usize);
                    if g.next_u32() % 2 == 0 {
                        Literal::Positive(var)
                    } else {
                        Literal::Negative(var)
                    }
                }))
            }));

            canonicalize(&f)
        }
    }

    #[test]
    fn quickcheck_formulas() {
        fn solver_eq_brute_force(f: Formula) -> bool {
            let brute_force = solve_brute_force(&f);
            let solver = Solver::new(f).solve();
            solver == brute_force
        }

        QuickCheck::new().tests(1000).quickcheck(solver_eq_brute_force as fn(Formula) -> bool);
    }
}
