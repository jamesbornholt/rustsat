use crate::formula::{Clause, Formula, Literal, Variable};
use crate::SatResult;
use log::trace;
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Assignment {
    True,
    False,
    Undecided,
}

pub struct Solver {
    clauses: Vec<Clause>,
    #[allow(unused)] // TODO use to invert canonicalization when outputting a model
    variable_map: HashMap<Variable, Variable>,
    state: SolverState,
}

#[derive(Debug)]
struct SolverState {
    variables: Vec<VariableState>,
    trail: Vec<Variable>,
    decision_level: DecisionLevel,
}

#[derive(Debug, Clone)]
struct VariableState {
    assignment: Assignment,
    reason: Option<ClauseIdx>,
    decision_level: DecisionLevel,
}

impl VariableState {
    fn clear(&mut self) {
        self.assignment = Assignment::Undecided;
        self.reason = None;
        self.decision_level = DecisionLevel(0);
    }
}

impl Default for VariableState {
    fn default() -> Self {
        VariableState {
            assignment: Assignment::Undecided,
            reason: None,
            decision_level: DecisionLevel(0),
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ClauseIdx(usize);

impl SolverState {
    fn new(formula: &Formula) -> Self {
        let num_variables = formula.num_variables();
        let variables = vec![Default::default(); num_variables];
        Self {
            variables,
            trail: vec![],
            decision_level: DecisionLevel(0),
        }
    }

    fn assignment_for(&self, literal: &Literal) -> Assignment {
        match self.variables[literal.idx()].assignment {
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

    fn assign(&mut self, literal: &Literal, reason: Option<ClauseIdx>) {
        assert_eq!(self.assignment_for(literal), Assignment::Undecided);
        assert!(reason.is_some() || self.decision_level > DecisionLevel(0));

        trace!(
            "{} {:?} at level {:?}",
            match reason {
                Some(c) => format!("implied by {}", c.0),
                None => "decision".to_string(),
            },
            literal,
            self.decision_level
        );

        self.trail.push(*literal.variable());
        let var = &mut self.variables[literal.idx()];
        var.assignment = if literal.is_positive() {
            Assignment::True
        } else {
            Assignment::False
        };
        var.reason = reason;
        var.decision_level = self.decision_level;
    }
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
    pub fn new(mut formula: Formula) -> Self {
        let variable_map = formula.canonicalize();
        let state = SolverState::new(&formula);
        Self {
            clauses: formula.into_clauses(),
            variable_map,
            state,
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
                    self.state.assign(&literal, None);
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
            'clauses: for (idx, clause) in self.clauses.iter().enumerate() {
                let mut last_literal = None;
                'literals: for literal in clause.literals() {
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
                    Some(literal) => self.state.assign(literal, Some(ClauseIdx(idx))),
                    None => return BcpResult::Conflict,
                }
                did_work = true;
            }
        }
        BcpResult::NoConflict
    }

    fn decide(&self) -> Option<Literal> {
        // TODO a less stupid heuristic. for now, just enumerate variables looking for one that's unassigned
        // why is it complete to only return positive assignments? because [`analyze_conflict`] will generate a conflict
        // clause that will reverse this decision if it's involved in a conflict.
        for (i, state) in self.state.variables.iter().enumerate() {
            if state.assignment == Assignment::Undecided {
                return Some(Literal::Positive(Variable(i)));
            }
        }
        None
    }

    fn analyze_conflict(&mut self) -> Option<Backtrack> {
        // Invariant: self.bcp() returned conflict
        // Invariant: self.state.decisions is not empty, contains at least one non-implied decision,
        //            and ends with at least one implied decision

        // TODO better conflict analysis
        // for now: the most recent decision was wrong. so we:
        // (a) generate a conflict clause ruling out everything up to and including that decision
        //     (and therefore that clause will become unit immediately after backtracking)
        // (b) return the level right before that one
        // If there are no non-implied decisions, our conflict is at level 0, so we return None
        // (nowhere to backtrack to)
        let decision_index = self
            .state
            .trail
            .iter()
            .rposition(|var| self.state.variables[var.0].reason.is_none())?;
        let last_decision_variable = self.state.trail[decision_index];
        let last_decision_level = self.state.variables[last_decision_variable.0].decision_level;

        // The conflict clause negates every non-implied decision up to and including the latest one
        let conflict_clause = self
            .state
            .trail
            .iter()
            .take(decision_index + 1)
            .filter(|v| self.state.variables[v.0].reason.is_none())
            .map(|v| {
                if self.state.variables[v.0].assignment == Assignment::True {
                    Literal::Negative(*v)
                } else {
                    Literal::Positive(*v)
                }
            });
        let conflict_clause = Clause::new(conflict_clause);

        trace!(
            "backtracking to {:?}, learned clause {:?}",
            last_decision_level.0 - 1,
            conflict_clause
        );
        self.clauses.push(conflict_clause);

        // All non-implied decisions are above level 0, so the subtraction is safe
        assert!(last_decision_level > DecisionLevel(0));
        Some(Backtrack {
            level: DecisionLevel(last_decision_level.0 - 1),
            decision_index,
        })
    }

    fn backtrack(&mut self, backtrack: Backtrack) {
        assert!(backtrack.decision_index < self.state.trail.len());
        let dropped = self.state.trail.split_off(backtrack.decision_index);
        for variable in &dropped {
            self.state.variables[variable.0].clear();
        }
        self.state.decision_level = backtrack.level;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::brute_force::solve_brute_force;
    use crate::formula::{n, p};
    use crate::solver::Solver;
    use quickcheck::QuickCheck;
    use test_env_log::test;

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

    #[test]
    fn quickcheck_formulas() {
        fn solver_eq_brute_force(f: Formula) -> bool {
            let brute_force = solve_brute_force(&f);
            let solver = Solver::new(f).solve();
            log::trace!("result = {:?}", solver);
            solver == brute_force
        }

        QuickCheck::new()
            .tests(1000)
            .quickcheck(solver_eq_brute_force as fn(Formula) -> bool);
    }
}
