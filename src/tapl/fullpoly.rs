//  chapter 25: An ML Implementation of System F

// Ocaml version
// https://www.cis.upenn.edu/~bcpierce/tapl/checkers/fullpoly/

// For clippy
// #![allow(enum_variant_names)]
// #![allow(many_single_char_names)]
// #![allow(new_without_default_derive)]

#![allow(dead_code)]
#![allow(non_snake_case)]

#[derive(Clone, PartialEq, Debug)]
enum Ty {
    // TmVar { index: usize, ctx_len: usize },
    TyVar(usize, usize), // Type variables
    TyArr(Box<Ty>, Box<Ty>),
    TyAll(String, Box<Ty>), // Universal quantifiers
    TySome(String, Box<Ty>), // Existential quantifiers
}

use self::Ty::*;

impl Ty {
    // p383
    // let tymap onvar c tyT
    fn ty_map<F>(&self, onvar: &F, c: i32) -> Ty
        where F: Fn(i32, usize, usize) -> Ty
    {
        match *self {
            TyArr(ref t1, ref t2) => TyArr(box t1.ty_map(onvar, c), box t2.ty_map(onvar, c)),
            TyVar(x, n) => onvar(c, x, n),
            TyAll(ref ty_X, ref ty2) => TyAll(ty_X.clone(), box ty2.ty_map(onvar, c + 1)),
            TySome(ref ty_X, ref ty2) => TySome(ty_X.clone(), box ty2.ty_map(onvar, c + 1)),
        }
    }

    fn type_shift_above(&self, d: i32, c: i32) -> Ty {
        self.ty_map(&|c, x, n| if x >= c as usize {
                        TyVar(x + d as usize, n + d as usize)
                    } else {
                        TyVar(x, n + d as usize)
                    },
                    c)
    }

    fn type_shift(&self, d: i32) -> Ty {
        self.type_shift_above(d, 0)
    }

    // let typeSubst tyS j tyT
    // self == tyT
    fn type_subst(&self, s: &Ty, j: i32) -> Ty {
        self.ty_map(&|j, x, n| if x == j as usize {
                        s.type_shift(j)
                    } else {
                        TyVar(x, n)
                    },
                    j)
    }

    // let typeSubstTop tyS tyT
    // ((lambda . t12) (v2))
    // => term_subst_top(v2, t12)

    // t12.type_subst_top(v2)
    fn type_subst_top(&self, s: &Ty) -> Ty {
        self.type_subst(&s.type_shift(1), 0).type_shift(-1)
    }
}

// p382
#[derive(Clone)]
enum Binding {
    NameBind, // Not used. This is usef only by the parsing and printing.
    VarBind(Ty),
    TyVarBind,
}

// p383
#[derive(Clone, PartialEq, Debug)]
enum Term {
    // TmVar { index: usize, ctx_len: usize },
    TmVar(usize, usize),
    TmAbs(String, Ty, Box<Term>), // "(lambda x:Nat: x)" -> TmAbs("x", Nat, x)
    TmApp(Box<Term>, Box<Term>), // "((lambda x:Nat: x) y)" -> TmApp((lambda x:Nat: x), y)
    TmTAbs(String, Box<Term>), // "VX.X->X" -> TmTbs("X", X->X)
    TmTApp(Box<Term>, Ty), // "((VX.X->X) [Nat])" -> TmTApp((VX.X->X), Nat)
    TmPack(Ty, Box<Term>, Ty), // "{*Nat, term}" as {EX, T}"  -> TmPack(Nat, term, {EX, T})
    TmUnpack(String, String, Box<Term>, Box<Term>), /* "let {X, x} = t1 in t2" -> TmUnpack("X", "x", t1, t2) */
}

use self::Term::*;

impl Term {
    // p384
    // let tmmap onvar ontype c t
    fn tm_map<F1, F2>(&self, onvar: &F1, ontype: &F2, c: i32) -> Term
        where F1: Fn(i32, usize, usize) -> Term,
              F2: Fn(i32, &Ty) -> Ty
    {
        match *self {
            TmVar(x, n) => onvar(c, x, n),
            TmAbs(ref x, ref ty1, ref t2) => {
                TmAbs(x.clone(),
                      ontype(c, ty1),
                      box t2.tm_map(onvar, ontype, c + 1))
            }
            TmApp(ref t1, ref t2) => {
                TmApp(box t1.tm_map(onvar, ontype, c),
                      box t2.tm_map(onvar, ontype, c))
            }
            TmTAbs(ref ty_X, ref t2) => TmTAbs(ty_X.clone(), box t2.tm_map(onvar, ontype, c + 1)),
            TmTApp(ref t1, ref ty2) => TmTApp(box t1.tm_map(onvar, ontype, c), ontype(c, ty2)),
            TmPack(ref ty1, ref t2, ref ty2) => {
                TmPack(ontype(c, ty1),
                       box t2.tm_map(onvar, ontype, c),
                       ontype(c, ty2))
            }
            TmUnpack(ref ty_X, ref x, ref t1, ref t2) => {
                TmUnpack(ty_X.clone(),
                         x.clone(),
                         box t1.tm_map(onvar, ontype, c),
                         box t2.tm_map(onvar, ontype, c))
            }
        }
    }

    // let termShiftAbove d c t
    fn term_shift_above(&self, d: i32, c: i32) -> Term {
        self.tm_map(&|c, x, n| if x >= c as usize {
                        TmVar(x + d as usize, n + d as usize)
                    } else {
                        TmVar(x, n + d as usize)
                    },
                    &|c, ty| ty.type_shift_above(d, c),
                    c)
    }

    // let termShift d t = termShiftAbove d 0 t
    fn term_shift(&self, d: i32) -> Term {
        self.term_shift_above(d, 0)
    }

    // let termSubst j s t
    fn term_subst(&self, j: i32, s: &Term) -> Term {
        self.tm_map(&|j, x, n| if x == j as usize {
                        s.term_shift(j)
                    } else {
                        TmVar(x, n)
                    },
                    &|_, ty| ty.clone(),
                    j)
    }

    // (E-TappTabs)
    // let rec tytermSubst tyS j t
    fn ty_term_subst(&self, tyS: &Ty, j: i32) -> Term {
        self.tm_map(&|_, x, n| TmVar(x, n), &|j, ty| ty.type_subst(tyS, j), j)
    }

    fn term_subst_top(&self, s: &Term) -> Term {
        self.term_subst(0, &s.term_shift(1)).term_shift(-1)
    }

    fn ty_term_subst_top(&self, s: &Ty) -> Term {
        self.ty_term_subst(&s.type_shift(1), 0).term_shift(-1)
    }

    // TODO <2016-05-06 Fri>
    // fn eval1(&self, ctx: &Context) -> Term {
    // }

    // TODO <2016-05-06 Fri>
    // type_of
}

use self::Binding::*;

struct Context {
    contexts: Vec<(String, Binding)>,
}

impl Context {
    fn new() -> Context {
        Context { contexts: Vec::new() }
    }

    fn add_binding(&self, x: String, bind: Binding) -> Context {
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
}
