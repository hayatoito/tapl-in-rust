//  chapter 17: An ML Implementation of Subtyping

// Ocaml version
// https://www.cis.upenn.edu/~bcpierce/tapl/checkers/fullsub/

// Suppress clippy
// #![allow(enum_variant_names)]
// #![allow(many_single_char_names)]
// #![allow(new_without_default_derive)]

#[derive(Clone, PartialEq, Debug)]
pub enum Ty {
    TyRecord(Vec<(String, Ty)>),
    TyTop,
    TyArr(Box<Ty>, Box<Ty>),
}

use self::Ty::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Term {
    TmVar {
        index: usize,
        ctx_len: usize,
    },
    TmAbs(String, Ty, Box<Term>),
    TmApp(Box<Term>, Box<Term>),
    TmRecord(Vec<(String, Box<Term>)>),
    TmProj(Box<Term>, String),
}

use self::Term::*;

fn subtype(s: &Ty, t: &Ty) -> bool {
    if s == t {
        true
    } else {
        match (s, t) {
            (_, &TyTop) => true,
            (&TyArr(ref s1, ref s2), &TyArr(ref t1, ref t2)) => subtype(t1, s1) && subtype(s2, t2),
            (&TyRecord(ref s), &TyRecord(ref t)) => {
                t.iter().all(|&(ref li, ref ti)| {
                    s.iter()
                        .find(|&&(ref s_li, _)| s_li == li)
                        .map(|&(_, ref s_ti)| subtype(s_ti, ti))
                        .is_some()
                })
            }
            _ => false,
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

pub fn type_of(t: &Term) -> Ty {

    fn ty_of(ctx: &Context, t: &Term) -> Ty {
        match *t {
            TmRecord(ref v) => {
                TyRecord(v.iter().map(|&(ref li, ref ti)| (li.clone(), ty_of(ctx, &*ti))).collect())
            }
            TmProj(ref t1, ref l) => {
                match ty_of(ctx, t1) {
                    TyRecord(ref v) => {
                        v.iter()
                            .find(|&&(ref li, _)| li == l)
                            .map(|&(_, ref ti)| ti.clone())
                            .expect(&format!("label {} not found", l))
                    }
                    _ => panic!("Expected record type"),
                }
            }
            TmVar { index, .. } => {
                ctx.get_type_from_context(index as usize).expect("var type is not found")
            }
            TmAbs(ref x, ref ty1, ref t2) => {
                let ctx1 = ctx.add_binding(x.clone(), VarBind(ty1.clone()));
                TyArr(Box::new(ty1.clone()), Box::new(ty_of(&ctx1, t2)))
            }
            TmApp(ref t1, ref t2) => {
                let ty1 = ty_of(ctx, t1);
                let ty2 = ty_of(ctx, t2);
                match ty1 {
                    TyArr(ref ty11, ref ty12) => {
                        if subtype(&ty2, ty11) {
                            (**ty12).clone()
                        } else {
                            panic!("parameter type mismatch")
                        }
                    }
                    _ => panic!("arrow type expected"),
                }
            }
        }
    }

    ty_of(&Context::new(), t)
}

// TODO: Write a parser

#[cfg(test)]
mod tests {

    use super::Ty::*;
    use super::Term::*;

    use super::subtype;
    use super::type_of;

    #[test]
    fn subtype_test() {
        assert!(subtype(&TyTop, &TyTop));

        let x = TyRecord(vec![("x".to_owned(), TyTop)]);
        let xy = TyRecord(vec![("x".to_owned(), TyTop), ("y".to_owned(), TyTop)]);

        assert!(subtype(&xy, &x));
        assert!(!subtype(&x, &xy));

        let f_x_x = TyArr(Box::new(x.clone()), Box::new(x.clone()));
        let f_x_xy = TyArr(Box::new(x.clone()), Box::new(xy.clone()));
        let f_xy_x = TyArr(Box::new(xy.clone()), Box::new(x.clone()));

        assert!(!subtype(&f_x_x, &f_x_xy));
        assert!(subtype(&f_x_xy, &f_x_x));

        assert!(subtype(&f_x_x, &f_xy_x));
        assert!(!subtype(&f_xy_x, &f_x_x));

        assert!(subtype(&f_x_xy, &f_xy_x));
        assert!(!subtype(&f_xy_x, &f_x_xy));
    }

    #[test]
    fn type_of_test() {
        // (lambda x:TyTop. x): TyTop -> TyTop
        let abs = TmAbs("x".to_owned(),
                        TyTop,
                        Box::new(TmVar {
                            index: 0,
                            ctx_len: 1,
                        }));
        assert_eq!(type_of(&abs), TyArr(Box::new(TyTop), Box::new(TyTop)));

        // ((lambda a:{"x": {"y": TyTop}}. a.x) {"x": {"y": abs})
        // ===> type:  {"y": TyTop}

        // type: {"y": TyTop}
        let ty_record_y = TyRecord(vec![("y".to_owned(), TyTop)]);
        // type: {"x": {"y": TyTop}}
        let ty_record_x_y = TyRecord(vec![("x".to_owned(), ty_record_y.clone())]);

        // term: var(0).x
        let tm_a_x = TmProj(Box::new(TmVar {
                                index: 0,
                                ctx_len: 1,
                            }),
                            "x".to_owned());

        // (lambda a:{"x": {"y": TyTop}}. a.x)
        let lambda_a = TmAbs("a".to_owned(),
                             ty_record_x_y.clone(),
                             Box::new(tm_a_x.clone()));

        // term: {"x": {"y": abs})
        let tm_p = TmRecord(vec![("x".to_owned(),
                                  Box::new(TmRecord(vec![("y".to_owned(),
                                                          Box::new(abs.clone()))]) ))]);

        // term: ((lambda a:{"x": {"y": TyTop}}. a.x) {"x": {"y": abs})
        let tm_app = TmApp(Box::new(lambda_a.clone()), Box::new(tm_p.clone()));

        assert_eq!(type_of(&tm_app), ty_record_y);
    }
}
