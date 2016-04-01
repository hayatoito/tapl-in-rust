// chapter 8 - 10

// chapter 8: Typed Arithmetic Expressions

// tyarith
// Ocaml version
// https://www.cis.upenn.edu/~bcpierce/tapl/checkers/tyarith/

// chapter 9: Simply Typed Lambda-Calculus

// Chapter 10: An ML Implementation of Simple Types
// Ocaml version
// https://www.cis.upenn.edu/~bcpierce/tapl/checkers/simplebool/

// Suppress clippy
// #![allow(enum_variant_names)]
// #![allow(many_single_char_names)]
// #![allow(len_without_is_empty)]
// #![allow(new_without_default_derive)]

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    TyArr(Box<Ty>, Box<Ty>),
    TyBool,
}

use self::Ty::*;

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TyArr(ref ty1, ref ty2) => write!(f, "({} -> {})", ty1, ty2),
            TyBool => write!(f, "Bool"),
        }
    }
}

#[derive(Clone)]
enum Binding {
    #[allow(dead_code)]
    NameBind,
    VarBind(Ty),
}

use self::Binding::*;

#[derive(Clone)]
struct Context {
    contexts: Vec<(String, Binding)>,
}

impl Context {
    fn new() -> Context {
        Context { contexts: Vec::new() }
    }

    fn add_binding(&self, x: String, bind: Binding) -> Context {
        assert!(self.contexts.iter().find(|&&(ref si, _)| *si == x).is_none());
        let mut v = self.contexts.clone();
        v.push((x, bind));
        Context { contexts: v }
    }

    fn get_binding(&self, i: usize) -> Binding {
        self.contexts[self.contexts.len() - 1 - i].1.clone()
    }

    fn get_type_from_context(&self, i: usize) -> Result<Ty, String> {
        match self.get_binding(i) {
            VarBind(ty) => Ok(ty),
            _ => Err("get_type_from_context: TODO: Message".to_string()),
        }
    }

    fn len(&self) -> usize {
        self.contexts.len()
    }

    fn index2name(&self, i: usize) -> String {
        if i < self.len() {
            self.contexts[self.len() - 1 - (i as usize)].0.clone()
        } else {
            panic!(format!("variable look up fails. index: {}, context length: {}.", i, self.contexts.len()))
        }
    }

    fn name2index(&self, s: &str) -> usize {
        match self.contexts.iter().position(|&(ref si, _)| si == s) {
            Some(i) => self.contexts.len() - 1 - i,
            None => panic!(format!("variable look up fails: {}", s)),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Term {
    TmVar(usize, usize),
    TmAbs(String, Ty, Box<Term>),
    TmApp(Box<Term>, Box<Term>),
    TmTrue,
    TmFalse,
    TmIf(Box<Term>, Box<Term>, Box<Term>),
}

use self::Term::*;

use std::fmt;

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", ContextTerm(&Context::new(), self))
    }
}

struct ContextTerm<'a>(&'a Context, &'a Term);

impl<'a> fmt::Display for ContextTerm<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ContextTerm(ctx, term) = *self;
        match *term {
            TmAbs(ref x, ref ty, ref t1) => {
                // let (ctx1, x1) = ctx.pickfreshname(x);
                let ctx1 = ctx.add_binding(x.clone(), Binding::VarBind(ty.clone()));
                write!(f, "(lambda {}: {}. {})", x, ty, ContextTerm(&ctx1, t1))
            }
            TmApp(ref t1, ref t2) => {
                write!(f, "({} {})", ContextTerm(ctx, t1), ContextTerm(ctx, t2))
            }
            TmVar(x, n) => {
                if ctx.len() == n {
                    write!(f, "{}", ctx.index2name(x))
                } else {
                    panic!("[bad index]")
                }
            }
            TmTrue => write!(f, "true"),
            TmFalse => write!(f, "false"),
            TmIf(ref t1, ref t2, ref t3) => write!(f, "(if {} {} {})", ContextTerm(ctx, t1), ContextTerm(ctx, t2), ContextTerm(ctx, t3)),
        }
    }
}

fn type_of(ctx: &Context, t: &Term) -> Result<Ty, String> {
    match *t {
        TmVar(i, _) => ctx.get_type_from_context(i),
        TmAbs(ref x, ref ty, ref t2) => {
            let ctx2 = ctx.add_binding(x.clone(), VarBind(ty.clone()));
            Ok(TyArr(box ty.clone(), box type_of(&ctx2, &**t2)?))
        }
        TmApp(ref t1, ref t2) => {
            let ty1 = type_of(ctx, &**t1)?;
            let ty2 = type_of(ctx, &**t2)?;
            match ty1 {
                TyArr(ref ty11, ref ty12) if ty2 == **ty11 => Ok((**ty12).clone()),
                _ => Err("type mismatch".to_string()),
            }
        }
        TmTrue | TmFalse => Ok(TyBool),
        TmIf(ref t1, ref t2, ref t3) => {
            match type_of(ctx, &**t1)? {
                TyBool => {
                    let ty2 = type_of(ctx, &**t2)?;
                    let ty3 = type_of(ctx, &**t3)?;
                    if ty2 == ty3 {
                        Ok(ty2)
                    } else {
                        Err("arms of conditional have different types".to_string())
                    }
                }
                _ => Err("guard of conditional not a boolean".to_string()),
            }
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

    use super::Ty;
    use super::Ty::*;

    use super::Binding;

    use super::Context;

    type Res = Box<Fn(Context) -> Term>;

    fn tos(s: &[u8]) -> String {
        str::from_utf8(s).unwrap().to_owned()
    }

    // e.g.
    // (lambda x: Bool. x) -> (Bool -> Bool)
    // (lambda x: (Bool -> Bool). x) -> ((Bool -> Bool) -> (Bool -> Bool))

    named!(ctype <&[u8], Ty>, alt!(
        tag!("Bool") => { |_| TyBool }
        | chain!(char!('(') ~ multispace?
                 ~ ty1: ctype ~ multispace?
                 ~ tag!("->") ~ multispace?
                 ~ ty2: ctype ~ multispace? ~ char!(')'),
                 { || TyArr(box ty1, box ty2) })
    ));

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
                  ~ tag!(":") ~ multispace?
                  ~ ty: ctype ~ multispace?
                  ~ tag!(".") ~ multispace
                  ~ tm: term ~ multispace?
                  ~ char!(')'),
                  { move || {
                      let s = tos(x);
                      Box::new(move |ctx: Context| {
                          let c2 = ctx.add_binding(s.clone(), Binding::VarBind(ty.clone()));
                          TmAbs(s.clone(), ty.clone(), Box::new(tm(c2)))
                      })}}));

    named!(tmapp <&[u8], Res>,
           chain!(char!('(') ~ multispace?
                  ~ t1: term
                  ~ multispace
                  ~ t2: term
                  ~ multispace? ~ char!(')'),
                  { || Box::new(move |ctx: Context|
                                TmApp(box t1(ctx.clone()), box t2(ctx.clone()))) }));

    named!(tmtrue <&[u8], Res>,
           map!(tag!("true"), {
               |_| Box::new(|_: Context| TmTrue)
           }));

    named!(tmfalse <&[u8], Res>,
           map!(tag!("false"), {
               |_| Box::new(|_: Context| TmFalse)
           }));

    named!(tmif <&[u8], Res>,
           chain!(char!('(') ~ multispace?
                  ~ tag!("if") ~ multispace
                  ~ t1: term
                  ~ multispace
                  ~ t2: term
                  ~ multispace
                  ~ t3: term
                  ~ multispace? ~ char!(')'),
                  { || Box::new(move |ctx: Context|
                                TmIf(box t1(ctx.clone()), box t2(ctx.clone()), box t3(ctx.clone()))) }));

    named!(term <&[u8], Res>,
           alt!(tmtrue | tmfalse | tmvar | tmabs | tmapp | tmif));

    #[cfg(test)]
    pub fn parse_type(s: &str) -> Option<Ty> {
        match ctype(s.as_bytes()) {
            IResult::Done(_, res) => Some(res),
            _ => None,
        }
    }

    // TODO: Propagate errors. Use Result<Term, ParseError>.
    pub fn parse(s: &str) -> Option<Term> {
        match term(s.as_bytes()) {
            IResult::Done(ref i, ref res) if i.is_empty() => Some((*res)(Context::new())),
            _ => None,
        }
    }
}

pub fn type_for(tm: &str) -> Option<Ty> {
    parser::parse(tm).and_then(|term| type_of(&Context::new(), &term).ok())
}

#[cfg(test)]
mod tests {

    use super::Term::*;
    use super::Ty::*;
    use super::type_for;
    use super::parser::parse;
    use super::parser::parse_type;

    #[test]
    fn ty_display_test() {
        assert_eq!(TyBool.to_string(), "Bool");
        assert_eq!(TyArr(Box::new(TyBool), Box::new(TyBool)).to_string(),
                   "(Bool -> Bool)");
        assert_eq!(TyArr(Box::new(TyBool), Box::new(TyArr(Box::new(TyBool), Box::new(TyBool)))).to_string(),
                   "(Bool -> (Bool -> Bool))");
    }

    #[test]
    fn term_display_test() {
        assert_eq!(TmTrue.to_string(), "true");
        assert_eq!(TmIf(Box::new(TmTrue), Box::new(TmFalse), Box::new(TmTrue)).to_string(),
                   "(if true false true)");
        assert_eq!(TmAbs("x".to_owned(), TyBool, Box::new(TmVar(0, 1))).to_string(),
                   "(lambda x: Bool. x)");
    }

    #[test]
    fn parse_test() {
        assert_eq!(parse("true").unwrap(), TmTrue);
        assert_eq!(parse("(if true false true)").unwrap(),
                   TmIf(Box::new(TmTrue), Box::new(TmFalse), Box::new(TmTrue)));
        assert_eq!(parse("(lambda x: Bool. x)").unwrap(),
                   TmAbs("x".to_owned(), TyBool, Box::new(TmVar(0, 1))));
        assert_eq!(parse("(lambda x: (Bool -> Bool). x)").unwrap(),
                   TmAbs("x".to_owned(), TyArr(box TyBool, box TyBool), Box::new(TmVar(0, 1))));
        assert_eq!(parse("(lambda x: (Bool -> (Bool -> Bool)). x)").unwrap(),
                   TmAbs("x".to_owned(),
                         TyArr(box TyBool,
                               box TyArr(box TyBool, box TyBool)),
                         Box::new(TmVar(0, 1))));

        assert_eq!(parse("(lambda x: (Bool -> (Bool -> Bool)). x)").unwrap().to_string(),
                   "(lambda x: (Bool -> (Bool -> Bool)). x)");
    }

    #[test]
    fn type_of_test() {

        fn assert_type(tm: &str, ty: &str) {
            let ty1 = type_for(tm);
            let ty2 = parse_type(ty);
            match (ty1.clone(), ty2.clone()) {
                (Some(a), Some(b)) => assert_eq!(a, b),
                _ => assert!(false, format!("mismatch {:?} {:?} ", ty1, ty2)),
            }
        }

        assert_type("true", "Bool");
        assert_type("(lambda x: Bool. true)", "(Bool -> Bool)");
        assert_type("((lambda x: Bool. x) false)", "Bool");
        assert_type("(if true false true)", "Bool");
        assert!(type_for("(if true (lambda x: Bool. true) true)").is_none());
        assert!(type_for("((lambda x: Bool. (x x)) false)").is_none());
    }
}
