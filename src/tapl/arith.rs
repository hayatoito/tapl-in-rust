// chapter 3: Untyped Arithmetic Expressions
// chapter 4: An ML Implementation of Arithmetic Expressions

use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    True,
    False,
    If(Box<Term>, Box<Term>, Box<Term>),
    Zero,
    Succ(Box<Term>),
    Pred(Box<Term>),
    IsZero(Box<Term>),
}

use self::Term::*;

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            True => write!(f, "True"),
            False => write!(f, "False"),
            If(ref t0, ref t1, ref t2) => write!(f, "(If {} {} {})", t0, t1, t2),
            Zero => write!(f, "Zero"),
            Succ(ref t0) => write!(f, "(Succ {})", t0),
            Pred(ref t0) => write!(f, "(Pred {})", t0),
            IsZero(ref t0) => write!(f, "(IsZero {})", t0),
        }
    }
}

fn is_numeric_val(t: &Term) -> bool {
    match *t {
        Zero => true,
        Succ(ref t1) => is_numeric_val(t1),
        _ => false,
    }
}

fn is_val(t: &Term) -> bool {
    match *t {
        True | False => true,
        ref t1 if is_numeric_val(t1) => true,
        _ => false,
    }
}

enum EvalError {
    NoRule(Term),
}

// See https://github.com/rust-lang/rfcs/blob/master/text/0107-pattern-guards-with-bind-by-move.md
fn eval1(t: Term) -> Result<Term, EvalError> {
    match t {
        If(box True, t1, _) => Ok(*t1),
        If(box False, _, t2) => Ok(*t2),
        If(t0, t1, t2) => Ok(If(box eval1(*t0)?, t1, t2)),
        Succ(t1) => Ok(Succ(box eval1(*t1)?)),
        Pred(box Zero) => Ok(Zero),
        Pred(box Succ(box ref nv)) if is_numeric_val(nv) => Ok((*nv).clone()),
        Pred(t0) => Ok(Pred(box eval1(*t0)?)),
        IsZero(box Zero) => Ok(True),
        IsZero(box Succ(box ref nv)) if is_numeric_val(nv) => Ok(False),
        IsZero(t0) => Ok(IsZero(box eval1(*t0)?)),
        t0 => Err(EvalError::NoRule(t0)),
    }
}

fn short_step_eval(t: Term) -> Term {
    match eval1(t.clone()) {
        Ok(t1) => short_step_eval(t1),
        // Err(EvalError::NoRule(t0)) => t0,
        Err(EvalError::NoRule(_)) => t,
    }
}

// Exercise 4.2.2
fn eval_big_step(t: Term) -> Term {
    if is_val(&t) {
        t
    } else {
        match t {
            If(box True, t1, _) => eval_big_step(*t1),
            If(box False, _, t2) => eval_big_step(*t2),
            Succ(t0) => Succ(box eval_big_step(*t0)),
            Pred(t0) => {
                match eval_big_step(*t0) {
                    Zero => Zero,
                    Succ(box ref nv) if is_numeric_val(nv) => (*nv).clone(),
                    t => Pred(box t),
                }
            }
            IsZero(t0) => {
                match eval_big_step(*t0) {
                    Zero => True,
                    Succ(box ref nv) if is_numeric_val(nv) => False,
                    _ => False,
                }
            }
            t => t,
        }
    }
}

trait Eval {
    fn eval(t: Term) -> Term;
}

struct SmallStepEval;

impl Eval for SmallStepEval {
    fn eval(t: Term) -> Term {
        short_step_eval(t)
    }
}

struct BigStepEval;

impl Eval for BigStepEval {
    fn eval(t: Term) -> Term {
        eval_big_step(t)
    }
}

mod parser {
    extern crate nom;

    use nom::multispace;
    use nom::IResult;

    use super::Term;
    use super::Term::*;

    named!(term <&[u8], Term>, alt!(
        tag!("True") => { |_| True }
        | tag!("False") => { |_| False }
        | tag!("Zero") => { |_| Zero }
        | chain!(char!('(') ~ multispace?
                 ~ tag!("If") ~ multispace
                 ~ t0: term ~ multispace
                 ~ t1: term ~ multispace
                 ~ t2: term ~ multispace? ~ char!(')'),
                 { || If(box t0, box t1, box t2) })
        | chain!(char!('(') ~ multispace?
                 ~ tag!("Succ") ~ multispace
                 ~ t0: term ~ multispace? ~ char!(')'),
                 { || Succ(box t0) })
        | chain!(char!('(') ~ multispace?
                 ~ tag!("Pred") ~ multispace
                 ~ t0: term ~ multispace? ~ char!(')'),
                 { || Pred(box t0) })
        | chain!(char!('(') ~ multispace?
                 ~ tag!("IsZero") ~ multispace
                 ~ t0: term ~ multispace? ~ char!(')'),
                 { || IsZero(box t0) })
    ));

    pub fn parse(s: &[u8]) -> Option<Term> {
        match term(s) {
            IResult::Done(_, o) => Some(o),
            _ => None,
        }
    }
}

pub enum RunError {
    ParseError,
}

fn run_internal<E: Eval>(s: &str) -> Result<String, RunError> {
    parser::parse(s.as_bytes())
        .map(E::eval)
        .map(|t| t.to_string())
        .ok_or(RunError::ParseError)
}

pub fn run(s: &str) -> Result<String, RunError> {
    run_internal::<SmallStepEval>(s)
}

pub fn run_with_big(s: &str) -> Result<String, RunError> {
    run_internal::<BigStepEval>(s)
}

#[cfg(test)]
mod tests {

    use super::{SmallStepEval, BigStepEval};
    use super::{is_numeric_val, is_val, Eval};
    use super::Term;
    use super::Term::*;

    use super::run;
    use super::parser::parse;

    #[test]
    fn enum_size() {
        let size = 4;
        assert_eq!(::std::mem::size_of::<Term>(), ::std::mem::size_of::<usize>() * size);
    }

    #[test]
    fn display() {
        assert_eq!(format!("{}", Zero), "Zero");
        assert_eq!(format!("{}", IsZero(box Zero)), "(IsZero Zero)");
        assert_eq!(format!("{}", If(box True, box Succ(box Zero), box Zero)),
                   "(If True (Succ Zero) Zero)");
    }

    fn eval_with<E: Eval>() {
        let eval = E::eval;
        assert!(is_numeric_val(&Zero));
        assert!(is_numeric_val(&Succ(box Zero)));
        assert!(!is_numeric_val(&Succ(box True)));

        assert!(is_val(&True));
        assert!(is_val(&False));
        assert!(!is_val(&Succ(box True)));

        assert_eq!(eval(Zero), Zero);
        assert_eq!(eval(True), True);
        assert_eq!(eval(False), False);
        assert_eq!(eval(IsZero(box Zero)), True);
        assert_eq!(eval(Pred(box Zero)), Zero);
        assert_eq!(eval(Succ(box Zero)), Succ(box Zero));
        assert_eq!(eval(Pred(box Succ(box Zero))), Zero);
        assert!(is_val(&eval(Pred(box Succ(box Zero)))));
        assert_eq!(eval(If(box True, box Pred(box Zero), box Succ(box Pred(box Zero)))), Zero);
        assert_eq!(eval(If(box False, box Pred(box Zero), box Succ(box Pred(box Zero)))), Succ(box Zero));

        // Non values
        assert_eq!(eval(Succ(box True)), Succ(box True));
        assert!(!is_val(&eval(Succ(box True))));
    }

    #[test]
    fn eval_small_step_test() {
        eval_with::<SmallStepEval>();
    }

    #[test]
    fn eval_big_step_test() {
        eval_with::<BigStepEval>();
    }

    #[test]
    fn parse_test() {
        assert_eq!(parse(b"Zero"), Some(Zero));
        assert_eq!(parse(b"False"), Some(False));
        assert_eq!(parse(b"True"), Some(True));
        assert_eq!(parse(b"Foo"), None);

        assert_eq!(parse(b"(Succ Zero)"), Some(Succ(box Zero)));
        assert_eq!(parse(b"(If True True True)"), Some(If(box True, box True, box True)));
        assert_eq!(parse(b"(IsZero (If True True True))"), Some(IsZero(box If(box True, box True, box True))));
    }

    #[test]
    fn run_test() {
        assert_eq!(run("(IsZero Zero)").ok().unwrap(), "True");
        assert_eq!(run("(Pred Zero)").ok().unwrap(), "Zero");
        assert_eq!(run("(IsZero (Succ Zero))").ok().unwrap(), "False");
        assert_eq!(run("(If True (Pred Zero) (Succ Zero))").ok().unwrap(), "Zero");
        assert_eq!(run("(If False (Pred Zero) (Succ Zero))").ok().unwrap(), "(Succ Zero)");
    }
}
