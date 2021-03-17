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
                        match self.analyze_conflict(reason) {
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

    /// Conflict analysis adds a new conflict clause to the clause set and returns information about
    /// the next backtracking step to take. If no more backtracking is possible, the problem is
    /// unsat.
    fn analyze_conflict(&mut self, reason: ClauseIdx) -> Option<Backtrack> {
        if self.state.decision_level == DecisionLevel(0) {
            return None;
        }

        // # Conflict analysis, in theory
        //
        // The conflict analysis works by finding the first UIP of the conflict graph, building the
        // conflict clause along the way. In the terms of [KS16, Algorithm 2.2.2], this looks like:
        //
        //    cl = current_conflicting_clause;
        //    while !stop_criterion_met(cl) {
        //        lit = last_assigned_literal(cl);
        //        var = variable_of_literal(lit);
        //        ante = antecedent(lit);
        //        cl = resolve(cl, ante, var);
        //    }
        //    add_clause_to_database(cl);
        //    return clause_asserting_level(cl);  // 2nd highest decision level in cl
        //
        // where `stop_criterion_met` returns true iff `cl` contains the negation of the first UIP
        // as its single literal at the current decision level. This stopping criterion ensures that
        // this negated literal becomes asserted immediately after backtracking.
        //
        // # Conflict analysis, in practice
        //
        // We could use a heavyweight graph analysis to find the first UIP and then run the above
        // algorithm literally. But we'd like to avoid materializing the entire conflict graph to
        // discover the first UIP. In fact, in the case of the conflict graph, we can find the first
        // UIP in linear time. We'd also like to avoid explicitly doing the binary resolution step.
        //
        // To achieve these goals, notice a few properties of the algorithm above. The algorithm
        // eventually visits every vertex in the conflict graph that lies on any path from the first
        // UIP to the conflict node, in the sense that every such vertex will at some iteration be
        // the value of `var`. When the algorithm visits `var`, it has the effect of *removing*
        // `var` from the conflict clause `cl` by binary resolution. Every such vertex is at the
        // same decision level as the first UIP, which is at the current decision level. So rather
        // than explicitly performing binary resolution at each step, we can compute the final
        // conflict clause `cl` by just adding to it any variable we encounter in `ante` that is
        // below the current decision level.
        //
        // To find the first UIP, we start from the conflict node, and keep track of a "frontier" of
        // vertices in the graph at the current decision level that we haven't yet seen. When the
        // frontier is non-empty, we choose the next vertex to explore in reverse decision order, to
        // ensure we're doing a breadth-first traversal. When the frontier is empty, it means we've
        // explored every path from the conflict node to the current vertex, and therefore the
        // current vertex is the first UIP.
        //
        // [KS16]: Decision Procedures, Kroening & Strichman, 2nd edition

        let mut reason = &self.clauses[reason.0];
        let mut conflict_clause = vec![];
        let mut seen = vec![false; self.state.variables.len()];
        let mut frontier = 0;
        let mut trail = self.state.trail.iter().rev();
        let first_uip = loop {
            // Consider all literals in the current antecedent that we haven't yet seen
            for l in reason.literals() {
                if seen[l.idx()] {
                    continue;
                }
                seen[l.idx()] = true;

                // If the literal is below our decision level, it will end up in the conflict clause
                // because binary resolution will never remove it. Otherwise, we need to add it to
                // the frontier of vertexes to explore.
                let var = &self.state.variables[l.idx()];
                if var.decision_level < self.state.decision_level {
                    conflict_clause.push(l.clone());
                } else {
                    debug_assert_eq!(
                        var.decision_level, self.state.decision_level,
                        "no decisions above the current level"
                    );
                    frontier += 1;
                }
            }

            // Current variable has now been considered, so remove it from the frontier
            frontier -= 1;

            // Find the next variable in reverse decision order. Note the trickiness here: `trail`
            // is mutated by this call so that we can persist our current position in the trail
            // across loop iterations.
            let next_var = trail
                .by_ref()
                .filter(|v| seen[v.0])
                .next()
                .expect("ran out of trail variables before finding uip");

            debug_assert_eq!(
                self.state.variables[next_var.0].decision_level, self.state.decision_level,
                "shouldn't go beyond the current decision level"
            );

            // If the frontier is empty, then the `next_var` is the first UIP, as every path back
            // from the conflict node has converged to it. Otherwise, the `next_var` tells us our
            // next antecedent.
            if frontier == 0 {
                break self.state.variables[next_var.0].literal(*next_var);
            } else {
                let clause_idx = self.state.variables[next_var.0]
                    .reason
                    .expect("next_var should be an implied variable");
                reason = &self.clauses[clause_idx.0];
            }
        };
        conflict_clause.push(first_uip.negated());

        // We backtrack to the second highest decision level in the conflict clause. By construction,
        // the UIP at the highest decision level.
        let max_decision_level = self.state.variables[first_uip.idx()].decision_level;
        let backtrack_to_level = conflict_clause
            .iter()
            .map(|l| self.state.variables[l.idx()].decision_level)
            .filter(|l| *l < max_decision_level)
            .max()
            .unwrap_or(DecisionLevel(0));
        // We'll undo all decisions in the trail that come at or after the backtrack decision level
        let new_trail_end = self
            .state
            .trail
            .iter()
            .position(|v| self.state.variables[v.0].decision_level > backtrack_to_level)
            .unwrap_or_else(|| self.state.trail.len());

        let conflict_clause = Clause::new(conflict_clause);

        log::trace!(
            "conflict clause {}, backtrack to level {}",
            conflict_clause,
            backtrack_to_level.0
        );

        self.clauses.push(conflict_clause);

        Some(Backtrack {
            level: backtrack_to_level,
            decision_index: new_trail_end,
        })
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

    #[cfg(test)]
    #[allow(unused)]
    fn dump_conflict_graph(&self, reason_idx: ClauseIdx) -> Result<(), std::io::Error> {
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::brute_force::solve_brute_force;
    use crate::formula::{formula_3sat_strategy, formula_wide_strategy, n, p};
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

    proptest! {
        #[test]
        fn proptest_solve_3sat(f in formula_3sat_strategy()) {
            let brute_force = solve_brute_force(&f);
            let solver = Solver::new(f).solve();
            log::trace!("result = {:?}", solver);
            assert_eq!(solver, brute_force);
        }

        #[test]
        fn proptest_solve_wide(f in formula_wide_strategy()) {
            let brute_force = solve_brute_force(&f);
            let solver = Solver::new(f).solve();
            log::trace!("result = {:?}", solver);
            assert_eq!(solver, brute_force);
        }
    }
}
