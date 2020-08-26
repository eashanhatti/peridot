#![allow(warnings)]

use std::collections::HashSet;
use std::fmt::Debug;
use std::default::*;
use super::{
    context::*,
    eval::*,
    typing::*
};

pub fn wrap<T: Default>(term: InnerTerm<T>) -> Term<T> { Term(Box::new(term), Default::default()) }

#[derive(Clone, Debug, PartialEq)]
/*pub */enum CapturesList<T> { // ex: `Int -> <(Int, Nil)> Int -> Int`, type of `+`
    Cons(Term<T>, Term<T>),
    Nil
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Usage {
    Unique,
    Shared
}

#[derive(Clone, Debug, PartialEq)]
pub enum InnerTerm<T> {
    Ann(Term<T>, Term<T>),
    UniverseIntro(usize, Usage),
    Var(usize),
    Rec(Term<T>),
    FunctionTypeIntro(Term<T>, Term<T>),
    FunctionIntro(Term<T>),
    FunctionElim(Term<T>, Term<T>),
    PairTypeIntro(Term<T>, Term<T>),
    PairIntro(Term<T>, Term<T>),
    PairElim(Term<T>, Term<T>),
    EnumTypeIntro(usize),
    EnumIntro(usize),
    EnumElim(Term<T>, Vec<Term<T>>),
    FoldTypeIntro(Term<T>),
    FoldIntro(Term<T>),
    FoldElim(Term<T>)
}

#[derive(Clone, Debug, PartialEq)]
pub struct Term<T>(pub Box<InnerTerm<T>>, pub T);

impl<T: Clone + Default + PartialEq> Term<T> {

    pub fn r#type<'a>(&'a self, context: Context<T>) -> CheckResult<'a, T, Self> {
        use InnerTerm::*;

        match *self.0 {
            Ann(_, ref type_ann) => {
                let mut errors = Vec::new();

                let type_ann_type = type_ann.r#type(context.clone())?;
                
                push_check(&mut errors, check(type_ann, type_ann_type, context.clone()));
                push_check(&mut errors, check_type(type_ann, context.clone()));

                if errors.len() > 0 {
                    Err(errors)
                } else {
                    Ok(type_ann.clone())
                }
            }
            UniverseIntro(level, usage) => Ok(wrap(UniverseIntro(level + 1, Usage::Unique))),
            _ => panic!("BUG: cannot infer type")
        }
    }

    pub fn usage<'a>(&'a self, context: Context<T>) -> CheckResult<'a, T, Usage> { // called on types
        use InnerTerm::*;
        use Usage::*;

        match *self.r#type(context)?.0 {
            UniverseIntro(_, usage) => Ok(usage),
            _ => Ok(Unique) // so uniqueness types work with polymorphism
        }
    }
}