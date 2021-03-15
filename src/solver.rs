use crate::formula::{Clause, Formula, Literal, Variable};
use crate::SatResult;

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
    pub fn new(formula: Formula) -> Self {
        let state = SolverState::new(&formula);
        Self {
            clauses: formula.into_clauses(),
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
        let conflict_clause_vec = conflict_decisions.iter().map(|decision| decision.negated());
        let conflict_clause = Clause::new(conflict_clause_vec);
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
