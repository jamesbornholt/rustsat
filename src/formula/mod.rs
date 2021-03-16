pub mod dimacs;

#[cfg(test)]
use quickcheck::{Arbitrary, Gen};
use std::collections::HashMap;
use std::fmt::Debug;
use std::fmt::{self, Formatter};

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Variable(pub usize);

impl Debug for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Literal {
    Positive(Variable),
    Negative(Variable),
}

impl Literal {
    pub fn variable(&self) -> &Variable {
        match self {
            Literal::Positive(v) => v,
            Literal::Negative(v) => v,
        }
    }

    pub fn variable_mut(&mut self) -> &mut Variable {
        match self {
            Literal::Positive(v) => v,
            Literal::Negative(v) => v,
        }
    }

    pub fn is_positive(&self) -> bool {
        match self {
            Literal::Positive(_) => true,
            Literal::Negative(_) => false,
        }
    }

    pub fn idx(&self) -> usize {
        self.variable().0
    }

    pub fn negated(&self) -> Self {
        match self {
            Literal::Positive(v) => Literal::Negative(*v),
            Literal::Negative(v) => Literal::Positive(*v),
        }
    }
}

impl Debug for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Positive(v) => write!(f, "{:?}", v),
            Literal::Negative(v) => write!(f, "!{:?}", v),
        }
    }
}

#[derive(Clone)]
pub struct Clause {
    literals: Vec<Literal>,
}

impl Clause {
    pub fn new(disjuncts: impl IntoIterator<Item = Literal>) -> Self {
        Self {
            literals: disjuncts.into_iter().collect(),
        }
    }

    pub fn literals(&self) -> impl Iterator<Item = &Literal> {
        self.literals.iter()
    }
}

impl Debug for Clause {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut first_literal = true;
        write!(f, "(")?;
        for l in &self.literals {
            if !first_literal {
                write!(f, " | ")?;
            }
            first_literal = false;
            write!(f, "{:?}", l)?;
        }
        write!(f, ")")
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
    pub fn num_variables(&self) -> usize {
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

    pub fn clauses(&self) -> impl Iterator<Item = &Clause> {
        self.clauses.iter()
    }

    pub(crate) fn into_clauses(self) -> Vec<Clause> {
        self.clauses
    }

    pub(crate) fn canonicalize(&mut self) -> HashMap<Variable, Variable> {
        let mut rewrite = HashMap::new();
        for clause in self.clauses.iter_mut() {
            for literal in clause.literals.iter_mut() {
                let len = rewrite.len();
                let target = rewrite.entry(*literal.variable()).or_insert(Variable(len));
                *literal.variable_mut() = *target;
            }
        }
        rewrite
    }
}

impl Debug for Formula {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        let mut first_clause = true;
        for clause in &self.clauses {
            if !first_clause {
                write!(f, " & ")?;
            }
            first_clause = false;
            write!(f, "{:?}", clause)?;
        }
        Ok(())
    }
}

#[cfg(test)]
pub(crate) fn p(x: usize) -> Literal {
    Literal::Positive(Variable(x))
}

#[cfg(test)]
pub(crate) fn n(x: usize) -> Literal {
    Literal::Negative(Variable(x))
}

#[cfg(test)]
impl Arbitrary for Formula {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        const MAX_VARS: u32 = 15;
        const MAX_CLAUSE_FACTOR: u32 = 9;

        let num_vars = g.next_u32() % MAX_VARS + 1;
        let clause_factor = g.next_u32() % MAX_CLAUSE_FACTOR + 1;
        let num_clauses = num_vars * clause_factor;

        let mut f = Formula::new((0..num_clauses).map(|_| {
            let clause_size = 3;
            Clause::new((0..clause_size).map(|_| {
                let var = Variable((g.next_u32() % num_vars) as usize);
                if g.next_u32() % 2 == 0 {
                    Literal::Positive(var)
                } else {
                    Literal::Negative(var)
                }
            }))
        }));

        f.canonicalize();
        f
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::brute_force::solve_brute_force;
    use quickcheck::QuickCheck;

    #[test]
    fn test_canonicalize() {
        let c1 = Clause::new(vec![p(12), p(11)]);
        let c2 = Clause::new(vec![n(12)]);
        let c3 = Clause::new(vec![n(11)]);
        let mut f = Formula::new(vec![c1, c2, c3]);

        f.canonicalize();

        assert_eq!(f.clauses().count(), 3);
        assert_eq!(
            f.clauses().nth(0).unwrap().literals().cloned().collect::<Vec<_>>(),
            vec![p(0), p(1)]
        );
        assert_eq!(
            f.clauses().nth(1).unwrap().literals().cloned().collect::<Vec<_>>(),
            vec![n(0)]
        );
        assert_eq!(
            f.clauses().nth(2).unwrap().literals().cloned().collect::<Vec<_>>(),
            vec![n(1)]
        );
    }

    #[test]
    fn test_canonicalize_quickcheck_equisatisfiable() {
        fn equisatisfiable(f: Formula) -> bool {
            let mut f2 = f.clone();
            f2.canonicalize();
            let sol1 = solve_brute_force(&f);
            let sol2 = solve_brute_force(&f2);
            sol1 == sol2
        }

        QuickCheck::new()
            .tests(100)
            .quickcheck(equisatisfiable as fn(Formula) -> bool);
    }
}
