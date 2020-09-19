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

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum List { // ex: `Int -> <(Int, Nil)> Int -> Int`, type of `+`
    Cons(Term, Term),
    Nil
}

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
pub enum Usage {
    Unique,
    Shared
}

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
pub enum Doub {
    This,
    That
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum InnerTerm {
    TypeTypeIntro(usize, Usage),
    Var(usize),
    Rec(Term),
    FunctionTypeIntro(Term, Term, Term),
    FunctionIntro(Term),
    FunctionElim(Term, Term),
    PairTypeIntro(Term, Term),
    PairIntro(Term, Term),
    PairElim(Term, Term),
    VoidTypeIntro,
    UnitTypeIntro,
    UnitIntro,
    DoubTypeIntro,
    DoubIntro(Doub),
    DoubElim(Term, Term, Term),
    FoldTypeIntro(Term),
    FoldIntro(Term),
    FoldElim(Term),
    CapturesListTypeIntro(usize),
    CapturesListIntro(List)
}

// TODO: make .1 private and add constructors for each term
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct Term(pub Box<InnerTerm>, pub Option<Box<Term>>);

fn max(lop: usize, rop: usize) -> usize {
    if lop > rop {
        lop
    } else {
        rop
    }
}

impl Term {
    // returns the normalized and checked type of a term
    // type may be infered if the term is a universe, in all other cases the type must be given
    // when given, the type of the type is checked as well
    pub fn r#type<'a>(&'a self, context: Context) -> CheckResult<'a, Self> {
        use InnerTerm::*;

        match &self.1 {
            Some(r#type) => {
                let r#type = &**r#type;
                let mut errors = Vec::new();
                
                push_check(&mut errors, check(r#type, r#type.r#type(context.clone())?, context.clone()));
                push_check(&mut errors, check_type(r#type, context.clone()));

                if errors.len() > 0 {
                    Ok(normalize(r#type.clone(), context))
                } else {
                    Err(errors)
                }
            },
            None =>
                match *self.0 {
                    TypeTypeIntro(level, _) => Ok(Term(Box::new(TypeTypeIntro(level + 1, Usage::Unique)), None)),
                    _ => panic!("all terms should be explicitly typed")
                }
        }
    }

    // returns the type of a term, unchecked. there is also no gaurantee the term is in normal form
    pub fn type_raw(&self) -> Term {
        use InnerTerm::*;

        match &self.1 {
            Some(r#type) => *r#type.clone(),
            None =>
                match *self.0 {
                    TypeTypeIntro(level, _) => Term(Box::new(TypeTypeIntro(level + 1, Usage::Unique)), None),
                    _ => panic!("all terms should be explicitly typed")
                }
        }
    }

    pub fn usage<'a>(&'a self, context: Context) -> CheckResult<'a, Usage> { // called on types
        use InnerTerm::*;
        use Usage::*;

        match *self.r#type(context)?.0 {
            TypeTypeIntro(_, usage) => Ok(usage),
            _ => Ok(Unique) // so uniqueness types work with polymorphic kinds
        }
    }
}