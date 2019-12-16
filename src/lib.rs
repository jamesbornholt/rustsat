#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

mod brute_force;

use std::fmt::{Debug, Error, Formatter};

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct Variable(pub usize);

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Literal {
    Positive(Variable),
    Negative(Variable),
}

impl Literal {
    fn variable(&self) -> &Variable {
        match self {
            Literal::Positive(v) => v,
            Literal::Negative(v) => v,
        }
    }

    fn is_positive(&self) -> bool {
        match self {
            Literal::Positive(_) => true,
            Literal::Negative(_) => false,
        }
    }

    fn idx(&self) -> usize {
        self.variable().0
    }

    fn negated(&self) -> Self {
        match self {
            Literal::Positive(v) => Literal::Negative(*v),
            Literal::Negative(v) => Literal::Positive(*v),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Clause {
    literals: Vec<Literal>,
}

impl Clause {
    pub fn new(disjuncts: impl IntoIterator<Item = Literal>) -> Self {
        Self {
            literals: disjuncts.into_iter().collect(),
        }
    }
}

#[derive(Clone)]
pub struct Formula {
    clauses: Vec<Clause>,
}

impl Formula {
    pub fn new(conjuncts: impl IntoIterator<Item = Clause>) -> Self {
        Self {
            clauses: conjuncts.into_iter().collect(),
        }
    }

    // Assumes F is in canonical form (variables are densely indexed from 0)
    fn num_variables(&self) -> usize {
        self.clauses
            .iter()
            .map(|clause| {
                clause
                    .literals
                    .iter()
                    .map(|literal| literal.variable())
                    .max()
                    .expect("can't use an empty clause")
            })
            .max()
            .expect("can't use an empty formula")
            .0
            + 1
    }
}

impl Debug for Formula {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let mut first_clause = true;
        for clause in &self.clauses {
            if first_clause {
                first_clause = false;
            } else {
                f.write_str(" & ")?;
            }
            if clause.literals.len() > 1 {
                f.write_str("(")?;
            }
            let mut first_literal = true;
            for literal in &clause.literals {
                if first_literal {
                    first_literal = false;
                } else {
                    f.write_str(" | ")?;
                }
                match literal {
                    Literal::Positive(Variable(x)) => f.write_fmt(format_args!("{}", x))?,
                    Literal::Negative(Variable(x)) => f.write_fmt(format_args!("!{}", x))?,
                }
            }
            if clause.literals.len() > 1 {
                f.write_str(")")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
struct Decision {
    literal: Literal,
    level: DecisionLevel,
    implied: bool,
}

impl Decision {
    fn negated(&self) -> Literal {
        self.literal.negated()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Assignment {
    True,
    False,
    Undecided,
}

pub struct Solver {
    clauses: Vec<Clause>,
    state: SolverState,
}

#[derive(Debug)]
struct SolverState {
    decisions: Vec<Decision>,
    assignment: Vec<Assignment>,
    decision_level: DecisionLevel,
}

impl SolverState {
    fn new(formula: &Formula) -> Self {
        let num_variables = formula.num_variables();
        Self {
            decisions: vec![],
            assignment: vec![Assignment::Undecided; num_variables as usize],
            decision_level: DecisionLevel(0),
        }
    }

    fn assignment_for(&self, literal: &Literal) -> Assignment {
        match self.assignment[literal.idx()] {
            Assignment::True => {
                if literal.is_positive() {
                    Assignment::True
                } else {
                    Assignment::False
                }
            }
            Assignment::False => {
                if literal.is_positive() {
                    Assignment::False
                } else {
                    Assignment::True
                }
            }
            Assignment::Undecided => Assignment::Undecided,
        }
    }

    fn assign(&mut self, literal: &Literal, implied: bool) {
        assert_eq!(self.assignment[literal.idx()], Assignment::Undecided);
        assert!(implied || self.decision_level > DecisionLevel(0));
        let decision = Decision {
            literal: literal.clone(),
            level: self.decision_level,
            implied,
        };
        self.decisions.push(decision);
        self.assignment[literal.idx()] = if literal.is_positive() {
            Assignment::True
        } else {
            Assignment::False
        }
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum SatResult {
    Satisfiable, // TODO model
    Unsatisfiable,
}

#[derive(PartialEq, Clone, Debug)]
enum BcpResult {
    Conflict,
    NoConflict,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
struct DecisionLevel(usize);

impl DecisionLevel {
    fn next(&self) -> Self {
        Self(self.0 + 1)
    }
}

#[derive(Debug)]
struct Backtrack {
    level: DecisionLevel,
    // The index of the first decision to drop during the backtrack
    decision_index: usize,
}

impl Solver {
    pub fn new(formula: &Formula) -> Self {
        Self {
            clauses: formula.clauses.iter().cloned().collect(),
            state: SolverState::new(formula),
        }
    }

    pub fn solve(&mut self) -> SatResult {
        if self.bcp() == BcpResult::Conflict {
            return SatResult::Unsatisfiable;
        }
        loop {
            self.state.decision_level = self.state.decision_level.next();
            match self.decide() {
                None => break SatResult::Satisfiable,
                Some(literal) => {
                    self.state.assign(&literal, false);
                    while self.bcp() == BcpResult::Conflict {
                        match self.analyze_conflict() {
                            None => return SatResult::Unsatisfiable,
                            Some(backtrack) => self.backtrack(backtrack),
                        }
                    }
                }
            }
        }
    }

    fn bcp(&mut self) -> BcpResult {
        let mut did_work = true;
        while did_work {
            did_work = false;
            'clauses: for clause in &self.clauses {
                let mut last_literal = None;
                'literals: for literal in &clause.literals {
                    match self.state.assignment_for(literal) {
                        // true => this clause is satisfied
                        Assignment::True => continue 'clauses,
                        // false => need to look at more literals, but we can't change the assignment
                        Assignment::False => continue 'literals,
                        // undecided => we'll be assigning this literal if it's the only undecided one
                        Assignment::Undecided => {
                            if last_literal.is_none() {
                                last_literal = Some(literal);
                            } else {
                                // Second undecided literal, can't resolve this clause
                                continue 'clauses;
                            }
                        }
                    }
                }
                // if last_literal is none, every literal was false => we have a conflict
                // otherwise we can apply unit resolution and continue
                match last_literal {
                    Some(literal) => self.state.assign(literal, true),
                    None => return BcpResult::Conflict,
                }
                did_work = true;
            }
        }
        BcpResult::NoConflict
    }

    fn decide(&self) -> Option<Literal> {
        // TODO a less stupid heuristic
        // for now: just enumerate variables looking for one that's unassigned
        for (i, assignment) in self.state.assignment.iter().enumerate() {
            if *assignment == Assignment::Undecided {
                return Some(Literal::Positive(Variable(i)));
            }
        }
        None
    }

    fn analyze_conflict(&mut self) -> Option<Backtrack> {
        // Invariant: self.bcp() returned conflict
        // Invariant: self.state.decisions is not empty, and contains at least one non-implied decision
        // TODO better conflict analysis
        // for now: the most recent decision was wrong. so we:
        // (a) generate a conflict clause ruling out everything up to and including that decision
        //     (and therefore that clause will become unit immediately after backtracking)
        // (b) return the level right before that one

        // If there are no non-implied decisions, our conflict is at level 0, so we return None
        // (nowhere to backtrack to)
        let (idx, last_decision) = self
            .state
            .decisions
            .iter()
            .enumerate()
            .filter(|(_i, decision)| !decision.implied)
            .last()?;
        // The conflict clause negates everything up to and including the last non-implied decision
        let conflict_decisions = &self.state.decisions[..=idx];
        let conflict_clause_vec = conflict_decisions
            .iter()
            .map(|decision| decision.negated())
            .collect::<Vec<_>>();
        let conflict_clause = Clause {
            literals: conflict_clause_vec,
        };
        self.clauses.push(conflict_clause);
        // All non-implied decisions are above level 0, so the subtraction is safe
        assert!(last_decision.level > DecisionLevel(0));
        Some(Backtrack {
            level: DecisionLevel(last_decision.level.0 - 1),
            decision_index: idx,
        })
    }

    fn backtrack(&mut self, backtrack: Backtrack) {
        assert!(backtrack.decision_index < self.state.decisions.len());
        let dropped = self.state.decisions.split_off(backtrack.decision_index);
        for decision in &dropped {
            self.state.assignment[decision.literal.idx()] = Assignment::Undecided;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use brute_force::solve_brute_force;
    use quickcheck::{Arbitrary, Gen};
    //    use rand::{Rng, RngCore};
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

        let mut solver = Solver::new(&f);
        assert_eq!(solver.solve(), SatResult::Satisfiable);
    }

    #[test]
    fn solve_bcp_unsat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![n(0)]);
        let c3 = Clause::new(vec![n(1)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let mut solver = Solver::new(&f);
        assert_eq!(solver.solve(), SatResult::Unsatisfiable);
    }

    #[test]
    fn solve_bcp_decide_sat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![p(0)]);
        let f = Formula::new(vec![c1, c2]);

        let mut solver = Solver::new(&f);
        assert_eq!(solver.solve(), SatResult::Satisfiable);
    }

    #[test]
    fn solve_conflict_sat() {
        let c1 = Clause::new(vec![p(0), p(1), p(2)]);
        let c2 = Clause::new(vec![n(0), n(1), p(2)]);
        let c3 = Clause::new(vec![n(1), n(2)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let mut solver = Solver::new(&f);
        assert_eq!(solver.solve(), SatResult::Satisfiable);
    }

    #[test]
    fn solve_conflict_unsat() {
        let c1 = Clause::new(vec![p(0), p(1)]);
        let c2 = Clause::new(vec![n(0)]);
        let c3 = Clause::new(vec![n(1)]);
        let f = Formula::new(vec![c1, c2, c3]);

        let mut solver = Solver::new(&f);
        assert_eq!(solver.solve(), SatResult::Unsatisfiable);
    }

    fn canonicalize(f: &Formula) -> Formula {
        // We're going to be renaming the variables to start at 0
        let mut rewrite = HashMap::new();
        for clause in &f.clauses {
            for literal in &clause.literals {
                if !rewrite.contains_key(&literal.idx()) {
                    rewrite.insert(literal.idx(), rewrite.len());
                }
            }
        }
        Formula::new(f.clauses.iter().map(|clause| {
            Clause::new(clause.literals.iter().map(|literal| match literal {
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
        assert_eq!(f2.clauses.len(), 3);
        assert_eq!(f2.clauses[0].literals, vec![p(0), p(1)]);
        assert_eq!(f2.clauses[1].literals, vec![n(0)]);
        assert_eq!(f2.clauses[2].literals, vec![n(1)]);
    }

    // QuickCheck for formulas
    impl Arbitrary for Formula {
        fn arbitrary<G: Gen>(g: &mut G) -> Self {
            const MAX_VARS: u32 = 10;
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

    #[quickcheck]
    fn quickcheck_formulas(f: Formula) {
        let brute_force = solve_brute_force(&f);
        let solver = Solver::new(&f).solve();
        assert_eq!(solver, brute_force);
    }
}
