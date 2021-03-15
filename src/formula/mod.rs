pub mod dimacs;

use std::fmt::Debug;
use std::fmt::{self, Formatter};

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct Variable(pub usize);

#[derive(Clone, PartialEq, Eq, Debug)]
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

    pub fn literals(&self) -> impl Iterator<Item = &Literal> {
        self.literals.iter()
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
}

impl Debug for Formula {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
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
