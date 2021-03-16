use crate::formula::{Clause, Formula, Literal, Variable};
use std::io::{BufRead, BufReader, Read};

pub fn parse<R: Read>(reader: R) -> Result<Formula, DimacsParseError> {
    let reader = BufReader::new(reader);

    let mut clauses = vec![];
    let mut num_clauses = None;

    for line in reader.lines() {
        let line = line?;
        let mut line = line.split_whitespace().peekable();

        match line.peek() {
            Some(&"c") | None => continue,
            Some(&"p") => {
                let _ = line.next();

                if line.next() != Some("cnf") {
                    return Err(DimacsParseError::Format("missing 'cnf'".into()));
                }

                let _num_variables = line
                    .next()
                    .and_then(|c| usize::from_str_radix(c, 10).ok())
                    .ok_or_else(|| DimacsParseError::Format("invalid num_variables".into()))?;

                num_clauses = Some(
                    line.next()
                        .and_then(|c| usize::from_str_radix(c, 10).ok())
                        .ok_or_else(|| DimacsParseError::Format("invalid num_clauses".into()))?,
                );
            }
            Some(_) => {
                if num_clauses.is_none() {
                    return Err(DimacsParseError::Format("missing 'p' line before clauses".into()));
                }

                let mut clause = vec![];
                for x in line {
                    match parse_literal(x)? {
                        Some(l) => clause.push(l),
                        None => break,
                    }
                }
                if !clause.is_empty() {
                    clauses.push(Clause::new(clause));
                }

                if clauses.len() >= num_clauses.unwrap() {
                    break;
                }
            }
        }
    }

    if num_clauses.is_none() {
        return Err(DimacsParseError::Format("missing 'p' line before clauses".into()));
    }

    let formula = Formula::new(clauses);
    Ok(formula)
}

fn parse_literal(s: &str) -> Result<Option<Literal>, DimacsParseError> {
    let l = isize::from_str_radix(s, 10).map_err(|_| DimacsParseError::Format("invalid literal".into()))?;
    if l > 0 {
        Ok(Some(Literal::Positive(Variable(l as usize))))
    } else if l < 0 {
        Ok(Some(Literal::Negative(Variable(-l as usize))))
    } else {
        Ok(None)
    }
}

#[derive(Debug)]
pub enum DimacsParseError {
    Io(std::io::Error),
    Format(String),
}

impl From<std::io::Error> for DimacsParseError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

#[cfg(test)]
mod tests {
    use crate::{SatResult, Solver};

    use super::*;

    fn p(x: usize) -> Literal {
        Literal::Positive(Variable(x))
    }
    fn n(x: usize) -> Literal {
        Literal::Negative(Variable(x))
    }

    #[test]
    fn parse_cnf_basic() {
        let cnf = "c  simple_v3_c2.cnf
c
p cnf 3 2
1 -3 0
2 3 -1 0";
        let f = parse(cnf.as_bytes()).expect("failed to parse");
        assert_eq!(f.clauses().count(), 2);

        assert_eq!(
            f.clauses().nth(0).unwrap().literals().cloned().collect::<Vec<_>>(),
            vec![p(1), n(3)]
        );
        assert_eq!(
            f.clauses().nth(1).unwrap().literals().cloned().collect::<Vec<_>>(),
            vec![p(2), p(3), n(1)]
        );
    }

    #[test]
    fn solve_cnf_quinn() {
        let cnf = "c  quinn.cnf
c
p cnf 16 18
  1    2  0
 -2   -4  0
  3    4  0
 -4   -5  0
  5   -6  0
  6   -7  0
  6    7  0
  7  -16  0
  8   -9  0
 -8  -14  0
  9   10  0
  9  -10  0
-10  -11  0
 10   12  0
 11   12  0
 13   14  0
 14  -15  0
 15   16  0
";

        let f = parse(cnf.as_bytes()).expect("failed to parse");

        let mut solver = Solver::new(f);
        let r = solver.solve();

        assert_eq!(r, SatResult::Satisfiable);
    }
}
