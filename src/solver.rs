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
    fn literal(&self, v: Variable) -> Literal {
        match self.assignment {
            Assignment::Undecided => panic!("cannot get literal for unassigned variable"),
            Assignment::True => Literal::Positive(v),
            Assignment::False => Literal::Negative(v),
        }
    }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
            "{} {} at level {}",
            match reason {
                Some(c) => format!("implied({})", c.0),
                None => "decision".to_string(),
            },
            literal,
            self.decision_level.0
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

#[derive(PartialEq, Eq, Clone, Debug)]
enum BcpResult {
    Conflict(ClauseIdx),
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
        if let BcpResult::Conflict(_) = self.bcp() {
            return SatResult::Unsatisfiable;
        }
        loop {
            self.state.decision_level = self.state.decision_level.next();
            match self.decide() {
                None => break SatResult::Satisfiable,
                Some(literal) => {
                    self.state.assign(&literal, None);
                    while let BcpResult::Conflict(reason) = self.bcp() {
                        match self.analyze_conflict2(reason) {
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
                    None => return BcpResult::Conflict(ClauseIdx(idx)),
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

    fn analyze_conflict(&mut self, reason: ClauseIdx) -> Option<Backtrack> {
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

    fn analyze_conflict2(&mut self, reason: ClauseIdx) -> Option<Backtrack> {
        if self.state.decision_level == DecisionLevel(0) {
            return None;
        }

        // #[cfg(test)]
        // let _ = self.dump_trail(reason);

        let mut reason = &self.clauses[reason.0];
        let mut conflict_clause = vec![];
        let mut seen = vec![false; self.state.variables.len()];
        let mut frontier = 0;
        let mut trail_end = self.state.trail.len() - 1;
        let first_uip = loop {
            for l in reason.literals() {
                if seen[l.idx()] {
                    continue;
                }
                seen[l.idx()] = true;

                let var = &self.state.variables[l.idx()];
                if var.decision_level < self.state.decision_level {
                    conflict_clause.push(l.clone());
                } else {
                    debug_assert_eq!(var.decision_level, self.state.decision_level);
                    frontier += 1;
                }
            }

            // TODO ugly
            let uip = loop {
                let v = self.state.trail[trail_end];
                let old_end = trail_end;
                trail_end = trail_end.saturating_sub(1);
                if seen[v.0] {
                    break v;
                }
                debug_assert_ne!(old_end, 0);
            };

            debug_assert_eq!(self.state.variables[uip.0].decision_level, self.state.decision_level);

            frontier -= 1;
            if frontier == 0 {
                break self.state.variables[uip.0].literal(uip);
            } else {
                let clause_idx = self.state.variables[uip.0]
                    .reason
                    .expect("uip should be an implied variable");
                reason = &self.clauses[clause_idx.0];
            }
        };
        conflict_clause.push(first_uip.negated());
        let max_decision_level = self.state.variables[first_uip.idx()].decision_level;

        let decision_level = conflict_clause
            .iter()
            .map(|l| self.state.variables[l.idx()].decision_level)
            .filter(|l| *l < max_decision_level)
            .max()
            .unwrap_or(DecisionLevel(0));
        let decision_index = self
            .state
            .trail
            .iter()
            .position(|v| self.state.variables[v.0].decision_level > decision_level)
            .unwrap_or_else(|| self.state.trail.len());

        let conflict_clause = Clause::new(conflict_clause);
        log::trace!(
            "conflict clause {}, backtrack to level {}",
            conflict_clause,
            decision_level.0
        );
        self.clauses.push(conflict_clause);

        Some(Backtrack {
            level: decision_level,
            decision_index,
        })
    }

    #[cfg(test)]
    fn dump_trail(&self, reason_idx: ClauseIdx) -> Result<(), std::io::Error> {
        use std::io::Write;
        use tempfile::NamedTempFile;

        let file = NamedTempFile::new()?;
        let (mut f, path) = file.keep()?;

        writeln!(f, "digraph cc {{")?;
        for v in &self.state.trail {
            let name = format!("x{}", v.0);
            let vs = &self.state.variables[v.0];
            let label = format!(
                "{}{}@{}",
                if vs.assignment == Assignment::True { "" } else { "!" },
                v.0,
                vs.decision_level.0
            );
            let style = if vs.reason.is_none() { ",peripheries=2" } else { "" };
            writeln!(f, "  {} [label=\"{}\"{}];", name, label, style)?;

            if let Some(idx) = vs.reason {
                let reason = &self.clauses[idx.0];
                for l in reason.literals() {
                    if l.variable() != v {
                        writeln!(f, "  x{} -> x{} [label=\"c{}\"];", l.variable().0, v.0, idx.0)?;
                    }
                }
            }
        }

        writeln!(f, "  k;")?;
        let reason = &self.clauses[reason_idx.0];
        for l in reason.literals() {
            writeln!(f, "  x{} -> k [label=\"c{}\"];", l.variable().0, reason_idx.0)?;
        }

        writeln!(f, "}}")?;

        println!("dumped to {}", path.display());

        Ok(())
    }

    fn backtrack(&mut self, backtrack: Backtrack) {
        log::trace!(
            "backtrack: dropping to {} from {}",
            backtrack.decision_index,
            self.state.trail.len()
        );
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
    use crate::formula::{formula_3sat_strategy, n, p};
    use crate::solver::Solver;
    use proptest::prelude::*;
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
    fn solve_simple() {
        // (!0 | !0 | !0) & (!0 | !1 | !1) & (!1 | 2 | 3) & (!1 | 3 | 3)
        let c1 = Clause::new(vec![n(0), n(0), n(0)]);
        let c2 = Clause::new(vec![n(0), n(1), n(1)]);
        let c3 = Clause::new(vec![n(1), p(2), p(3)]);
        let c4 = Clause::new(vec![n(1), p(3), n(3)]);
        let f = Formula::new(vec![c1, c2, c3, c4]);

        let mut solver = Solver::new(f);
        assert_eq!(solver.solve(), SatResult::Satisfiable);
    }

    #[test]
    fn solve_failing() {
        use Literal::*;

        let mut f = Formula::new(vec![
            Clause {
                literals: vec![Negative(Variable(1)), Positive(Variable(1)), Negative(Variable(7))],
            },
            Clause {
                literals: vec![Negative(Variable(10)), Negative(Variable(13)), Negative(Variable(1))],
            },
            Clause {
                literals: vec![Negative(Variable(7)), Negative(Variable(7)), Negative(Variable(10))],
            },
            Clause {
                literals: vec![Positive(Variable(6)), Negative(Variable(9)), Negative(Variable(15))],
            },
            Clause {
                literals: vec![Negative(Variable(2)), Negative(Variable(1)), Negative(Variable(1))],
            },
            Clause {
                literals: vec![Negative(Variable(6)), Negative(Variable(7)), Negative(Variable(15))],
            },
            Clause {
                literals: vec![Positive(Variable(9)), Positive(Variable(10)), Positive(Variable(6))],
            },
            Clause {
                literals: vec![Negative(Variable(13)), Negative(Variable(7)), Negative(Variable(9))],
            },
            Clause {
                literals: vec![Positive(Variable(9)), Positive(Variable(15)), Positive(Variable(15))],
            },
        ]);
        f.canonicalize();
        println!("{}", f);

        let brute_force = solve_brute_force(&f);
        assert_eq!(Solver::new(f).solve(), brute_force);
    }

    proptest! {
        #[test]
        fn proptest_solve(f in formula_3sat_strategy()) {
            let brute_force = solve_brute_force(&f);
            let solver = Solver::new(f).solve();
            log::trace!("result = {:?}", solver);
            assert_eq!(solver, brute_force);
        }
    }
}
