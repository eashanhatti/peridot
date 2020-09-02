#![allow(warnings)]

use std::{
    collections::HashSet,
    fmt::Debug,
    default::*,
    hash::Hash
};
use super::{
    context::*,
    eval::*,
    typing::{
        *,
        InnerError::*
    }
};

pub fn wrap<T: Default>(term: InnerTerm<T>) -> Term<T> { Term(Box::new(term), Default::default()) }

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum List<T> { // ex: `Int -> <(Int, Nil)> Int -> Int`, type of `+`
    Cons(Term<T>, Term<T>),
    Nil
}

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
pub enum Usage {
    Unique,
    Shared
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum InnerTerm<T> {
    Ann(Term<T>, Term<T>),
    UniverseIntro(usize, Usage),
    Var(usize),
    Rec(Term<T>),
    FunctionTypeIntro(Term<T>, Term<T>, Term<T>),
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
    FoldElim(Term<T>),
    CapturesListTypeIntro(usize),
    CapturesListIntro(List<T>)
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct Term<T>(pub Box<InnerTerm<T>>, pub T);

fn max(lop: usize, rop: usize) -> usize {
    if lop > rop {
        lop
    } else {
        rop
    }
}

impl<T: Clone + Default + PartialEq + Debug + Hash + Eq> Term<T> {

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
                    Ok(normalize(type_ann.clone(), Context::new()))
                }
            },
            Var(index) =>
                match context.find(index) {
                    Some(var_type) => Ok(var_type),
                    None => Err(vec![Error::new(self, context, NonexistentVar { index })])
                },
            UniverseIntro(level, usage) => Ok(wrap(UniverseIntro(level + 1, Usage::Unique))),
            FunctionTypeIntro(ref caps_list, ref in_type, ref out_type) =>
                match (*(caps_list.r#type(context.clone())?).0, *(in_type.r#type(context.clone())?).0, *(out_type.r#type(context)?).0) {
                    (CapturesListTypeIntro(level1), UniverseIntro(level2, _), UniverseIntro(level3, _)) =>
                        Ok(wrap(UniverseIntro(max(level1, max(level2, level3)), Usage::Shared))),
                    _ => panic!()
                }
            FunctionElim(ref abs, ref arg) => {
                let abs_type = abs.r#type(context.clone())?;
                match *abs_type.0 {
                    FunctionTypeIntro(caps_list, in_type, out_type) => Ok(normalize(out_type, Context::new().insert(0, arg.clone()))),
                    _ => Err(vec![Error::new(self, context, ExpectedOfFunctionType { giv_type: abs_type })])
                }
            },
            PairIntro(ref fst, ref snd) => Ok(wrap(PairTypeIntro(fst.r#type(context.clone())?, snd.r#type(context)?))),
            EnumTypeIntro(_) => Ok(wrap(UniverseIntro(0, Usage::Unique))),
            CapturesListTypeIntro(level) => Ok(wrap(UniverseIntro(level + 1, Usage::Unique))),
            _ => panic!("BUG: cannot get type of {:?}", self)
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