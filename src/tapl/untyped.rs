// chapter 5 - 7

// chapter 5: The Untyped Lambda-Calculas

// Ocaml version
// https://www.cis.upenn.edu/~bcpierce/tapl/checkers/untyped/

// tru = λt. λf. t;
// fls = λt. λf. f;
// test = λl. λm. λn. l m n;
// and = λb. λc. b c fls;

// Exercise: 5.2.1 <2016-05-02 Mon>
// or = λb. λc. b tru c;
// not = λb. b fls tru;

// Exercise: 5.2.2 => Skip <2016-05-02 Mon>

// plus = λm. λn. λs. λz. m s (n s z)

// Exercise: 5.2.3 => Skip <2016-05-02 Mon>
// Exercise: 5.2.4 => Skip <2016-05-02 Mon>
// Exercise: 5.2.5
// subtract = λm. λn. λs. λz. n pred (m s z) => wrong..
// => substract = λm. λn. n pred m

// chapter 6: Nameless Representaion of Terms
// chapter 7: An ML Implementation of the Lambda-Calculus

// Suppress clippy
// #![allow(enum_variant_names)]
// #![allow(many_single_char_names)]
// #![allow(len_without_is_empty)]
// #![allow(new_without_default)]
// #![allow(new_without_default_derive)]

use std::fmt;

#[derive(Clone, PartialEq, Debug)]
pub enum Term {
    // page 84. (index, ctx_len (depth_of_lambda))
    TmVar(usize, usize),
    TmAbs(String, Box<Term>),
    TmApp(Box<Term>, Box<Term>),
}

use self::Term::*;

#[derive(Clone)]
struct Context {
    contexts: Vec<String>,
}

impl Context {
    fn new() -> Context {
        Context { contexts: Vec::new() }
    }

    fn pickfreshname(&self, x: &str) -> (Context, String) {
        let s = x.to_owned();
        if self.contexts.contains(&s) {
            self.pickfreshname(&(s + "'"))
        } else {
            let mut newc = (*self).clone();
            newc.contexts.push(s.clone());
            (newc, s)
        }
    }

    fn len(&self) -> usize {
        self.contexts.len()
    }

    fn index2name(&self, i: usize) -> String {
        if i < self.len() {
            self.contexts[self.len() - 1 - (i as usize)].clone()
        } else {
            panic!(format!("variable look up fails. index: {}, context length: {}.",
                           i,
                           self.contexts.len()))
        }
    }

    fn name2index(&self, s: &str) -> usize {
        match self.contexts.iter().position(|a| a == s) {
            Some(i) => self.contexts.len() - 1 - i,
            None => panic!(format!("variable look up fails: {}", s)),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", ContextTerm(&Context::new(), self))
    }
}

struct ContextTerm<'a>(&'a Context, &'a Term);

impl<'a> fmt::Display for ContextTerm<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ContextTerm(context, term) = *self;
        match *term {
            TmAbs(ref x, ref t1) => {
                let (ctx1, x1) = context.pickfreshname(x);
                write!(f, "(lambda {}. {})", x1, ContextTerm(&ctx1, t1))
            }
            TmApp(ref t1, ref t2) => {
                write!(f,
                       "({} {})",
                       ContextTerm(context, t1),
                       ContextTerm(context, t2))
            }
            TmVar(x, n) => {
                if context.len() == n {
                    write!(f, "{}", context.index2name(x))
                } else {
                    panic!("[bad index]")
                }
            }
        }
    }
}

enum EvalStop {
    NoRuleApplies,
}

// ((lambda . t12) (v2))
// => term_subst_top(v2, t12)
fn term_subst_top(s: &Term, t: &Term) -> Term {
    t.term_subst(0, &s.term_shift(1)).term_shift(-1)
}

impl Term {
    fn term_shift(&self, d: i32) -> Term {

        fn walk(d: i32, c: i32, t: &Term) -> Term {
            match *t {
                TmVar(x, n) => {
                    if x as i32 >= c {
                        let nx = x as i32 + d;
                        assert!(nx >= 0);
                        TmVar(nx as usize, (n as i32 + d) as usize)
                    } else {
                        TmVar(x, (n as i32 + d) as usize)
                    }
                }
                TmAbs(ref x, ref t1) => TmAbs(x.clone(), box walk(d, c + 1, t1)),
                TmApp(ref t1, ref t2) => TmApp(box walk(d, c, t1), box walk(d, c, t2)),
            }
        }

        walk(d, 0, self)
    }

    fn term_subst(&self, j: i32, s: &Term) -> Term {

        fn walk(j: i32, s: &Term, c: i32, t: &Term) -> Term {
            match *t {
                TmVar(x, n) => {
                    if x as i32 == j + c {
                        s.term_shift(c)
                    } else {
                        TmVar(x, n)
                    }
                }
                TmAbs(ref x, ref t1) => TmAbs(x.clone(), box walk(j, s, c + 1, t1)),
                TmApp(ref t1, ref t2) => TmApp(box walk(j, s, c, t1), box walk(j, s, c, t2)),
            }
        }
        walk(j, s, 0, self)
    }

    fn is_val(&self, _: &Context) -> bool {
        match *self {
            TmAbs(_, _) => true,
            _ => false,
        }
    }

    fn eval1(&self, ctx: &Context) -> Result<Term, EvalStop> {
        match *self {
            TmApp(box TmAbs(_, ref t12), ref v2) if v2.is_val(ctx) => Ok(term_subst_top(v2, t12)),
            TmApp(ref v1, ref t2) if v1.is_val(ctx) => Ok(TmApp(v1.clone(), box t2.eval1(ctx)?)),
            TmApp(ref t1, ref t2) => Ok(TmApp(box t1.eval1(ctx)?, t2.clone())),
            _ => Err(EvalStop::NoRuleApplies),
        }
    }

    fn eval(&self, ctx: &Context) -> Term {
        match self.eval1(ctx) {
            Ok(t) => t.eval(ctx),
            Err(EvalStop::NoRuleApplies) => self.clone(),
        }
    }
}

mod parser {
    extern crate nom;

    use std::str;

    use nom::multispace;
    use nom::alphanumeric;
    use nom::IResult;

    use super::Term;
    use super::Term::*;

    use super::Context;

    type Res = Box<Fn(Context) -> Term>;

    fn tos(s: &[u8]) -> String {
        str::from_utf8(s).unwrap().to_owned()
    }

    named!(tmvar <&[u8], Res>,
           map!(alphanumeric, |x| {
               let s = tos(x);
               Box::new(move |ctx: Context| -> Term {
                   TmVar(ctx.name2index(&s), ctx.len())
               })}));

    named!(tmabs <&[u8], Res>,
           chain!(char!('(') ~ multispace?
                  ~ tag!("lambda") ~ multispace
                  ~ x: alphanumeric ~ multispace?
                  ~ tag!(".") ~ multispace
                  ~ t1: term ~ multispace?
                  ~ char!(')'),
                  { || {
                      let s = tos(x);
                      Box::new(move |ctx: Context| {
                          let (c2, x2) = ctx.pickfreshname(&s);
                          if s != x2 {
                              // TODO: Update var's index.
                              println!("Warning: Name conflict is not well supported: {} {}: ", s, x2);
                          }
                          TmAbs(x2, Box::new(t1(c2)))
                      })}}));

    named!(tmapp <&[u8], Res>,
           chain!(char!('(') ~ multispace?
                  ~ t1: term
                  ~ multispace
                  ~ t2: term
                  ~ multispace? ~ char!(')'),
                  { || Box::new(move |ctx: Context|
                                TmApp(box t1(ctx.clone()), box t2(ctx.clone()))) }));

    named!(term <&[u8], Res>, alt!(tmapp | tmvar | tmabs));

    pub fn parse(s: &[u8]) -> Option<Term> {
        match term(s) {
            IResult::Done(_, res) => Some((*res)(Context::new())),
            _ => None,
        }
    }
}

pub enum RunError {
    ParseError,
}

pub fn run(s: &str) -> Result<String, RunError> {
    parser::parse(s.as_bytes())
        .map(|t| t.eval(&Context::new()))
        .map(|t| t.to_string())
        .ok_or(RunError::ParseError)
}

#[cfg(test)]
mod tests {

    use super::Term;
    use super::Term::*;
    use super::Context;

    fn var(i: usize, ctx_len: usize) -> Term {
        TmVar(i, ctx_len)
    }

    fn lambda(x: &str, t: Term) -> Term {
        TmAbs(x.to_string(), box t)
    }

    fn apply(t0: Term, t1: Term) -> Term {
        TmApp(box t0, box t1)
    }

    #[test]
    fn term_display() {
        let t = lambda("a", var(0, 1));
        assert_eq!(t.to_string(), "(lambda a. a)");

        let t = apply(t.clone(), t.clone());
        assert_eq!(t.to_string(), "((lambda a. a) (lambda a. a))");

        let t = lambda("a", apply(var(0, 1), var(0, 1)));
        assert_eq!(t.to_string(), "(lambda a. (a a))");

        let t = lambda("a", lambda("b", apply(var(0, 2), var(1, 2))));
        assert_eq!(t.to_string(), "(lambda a. (lambda b. (b a)))");

        let t = lambda("a", lambda("a", apply(var(0, 2), var(1, 2))));
        assert_eq!(t.to_string(), "(lambda a. (lambda a'. (a' a)))");

        let t = apply(lambda("a", var(0, 1)),
                      lambda("a", apply(var(0, 1), var(0, 1))));
        assert_eq!(t.to_string(), "((lambda a. a) (lambda a. (a a)))");

        let t = apply(lambda("a", var(0, 1)),
                      lambda("b", apply(var(0, 1), var(0, 1))));
        assert_eq!(t.to_string(), "((lambda a. a) (lambda b. (b b)))");
    }

    #[test]
    fn term_shift() {
        let t = lambda("a", var(0, 1));
        assert_eq!(t.term_shift(1), lambda("a", var(0, 2)));

        // There is no free variables.
        let t = lambda("a", lambda("b", apply(var(0, 2), var(1, 2))));
        assert_eq!(t.term_shift(1),
                   lambda("a",
                          lambda("b",
                                 apply(var(0, 3),
                                       var(1, 3)))));

        // There is a free variable.
        let t = lambda("a",
                       lambda("b",
                              apply(var(0, 2),
                                    // Free variable
                                    var(2, 2))));
        assert_eq!(t.term_shift(1),
                   lambda("a",
                          lambda("b",
                                 apply(var(0, 3),
                                       // Free variable's index is shifted
                                       var(3, 3)))));
    }

    #[test]
    fn term_subst() {
        let s = lambda("a", var(0, 1));
        let t = var(0, 1);  // Free variable.

        assert_eq!(t.term_subst(1, &s), var(0, 1));
        assert_eq!(t.term_subst(0, &s), lambda("a", var(0, 1)));

        let s = lambda("b", var(0, 1));
        let t = lambda("a",
                       apply(// bound variable
                             var(0, 2),
                             apply(// Free variables
                                   var(1, 2), // Refer to one-outer variable.
                                   var(2, 2))));
        assert_eq!(t.term_subst(0, &s),
                   lambda("a",
                          apply(
                              var(0, 2),
                              apply(
                                  lambda("b", var(0, 2)),
                                  var(2, 2)))));
    }

    #[test]
    fn eval_test() {
        fn eval(t: &Term) -> Term {
            t.eval(&Context::new())
        }

        let t = apply(lambda("a", var(0, 1)), lambda("b", var(0, 1)));
        assert_eq!(eval(&t), lambda("b", var(0, 1)));

        let t = apply(lambda("b", apply(var(0, 1), lambda("x", lambda("y", var(2, 3))))), /* var(2, 3) -> b */
                      lambda("a", var(0, 1)));
        assert_eq!(t.to_string(),
                   "((lambda b. (b (lambda x. (lambda y. b)))) (lambda a. a))");

        assert_eq!(eval(&t),
                   lambda("x",
                          lambda("y",
                                 lambda("a", var(0, 3)))));

        assert_eq!(eval(&t).to_string(),
                   "(lambda x. (lambda y. (lambda a. a)))");
    }

    #[test]
    fn parse_test() {
        use super::parser::parse;

        assert_eq!(parse(b"(lambda x. x)"), Some(lambda("x", var(0, 1))));
        assert_eq!(parse(b"((lambda x. x) (lambda x. x))"),
                   Some(apply(lambda("x", var(0, 1)), lambda("x", var(0, 1)))));
        assert_eq!(parse(b"(lambda x. (lambda y. x))"),
                   Some(lambda("x", lambda("y", var(1, 2)))));
        assert_eq!(parse(b"((lambda x. (lambda y. x)) (lambda y. y))"),
                   Some(apply(lambda("x", (lambda("y", var(1, 2)))),
                              lambda("y", var(0, 1)))));
    }

    #[test]
    fn run_test() {
        use super::run;
        assert_eq!(run("(lambda x. x)").ok().unwrap(), "(lambda x. x)");
        assert_eq!(run("((lambda x. (x x)) (lambda y. y))").ok().unwrap(),
                   "(lambda y. y)");
        assert_eq!(run("(((lambda a. (lambda b. (b a))) (lambda z. z)) (lambda x. (lambda y. (y x))))").ok().unwrap(),
                   "(lambda y. (y (lambda z. z)))");
    }
}
