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
pub enum List {
    Cons(Term, Term),
    Nil
}
use List::*;

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

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct Term {
    pub data: Box<InnerTerm>,
    pub type_ann: Option<Box<Term>>
}

fn max(lop: usize, rop: usize) -> usize {
    if lop > rop {
        lop
    } else {
        rop
    }
}

impl Term {
    pub fn new(data: Box<InnerTerm>, r#type_ann: Option<Box<Term>>) -> Term {
        Term {
            data,
            type_ann
        }
    }

    // returns the type of a term, unchecked. there is also no gaurantee the term is in normal form
    pub fn r#type(&self) -> Term {
        use InnerTerm::*;
        match &self.type_ann {
            Some(type_ann) => *type_ann.clone(),
            None =>
                match *self.data {
                    TypeTypeIntro(level, _) => Term::new(Box::new(TypeTypeIntro(level + 1, Usage::Unique)), None),
                    _ => panic!("all terms should be explicitly typed")
                }
        }
    }

    pub fn usage(&self) -> Usage { // called on types
        match *self.r#type().data {
            InnerTerm::TypeTypeIntro(_, usage) => usage,
            _ => Usage::Unique // so uniqueness types work with polymorphic kinds
        }
    }

    pub fn level(&self) -> usize {
        match *self.r#type().data {
            InnerTerm::TypeTypeIntro(level, _) => level,
            _ => panic!("level can only be extracted from types")
        }
    }
}

// checks if two terms are equal, disregarding type ann
pub fn is_terms_eq(type1: &Term, type2: &Term) -> bool {
    use InnerTerm::*;
    
    match &(&(*type1.data), &(*type2.data)) {
        (TypeTypeIntro(level1, usage1), TypeTypeIntro(level2, usage2)) =>
            level1 == level2 && usage1 == usage2,
        (Var(index1), Var(index2)) =>
            index1 == index2,
        (Rec(ref inner_term1), Rec(ref inner_term2)) =>
            is_terms_eq(inner_term1, inner_term2),
        (FunctionTypeIntro(ref caps_list1, ref in_type1, ref out_type1), FunctionTypeIntro(ref caps_list2, ref in_type2, ref out_type2)) =>
            is_terms_eq(caps_list1, caps_list2) && is_terms_eq(in_type1, in_type2) && is_terms_eq(out_type1, out_type2),
        (FunctionIntro(ref body1), FunctionIntro(ref body2)) =>
            is_terms_eq(body1, body2),
        (FunctionElim(ref abs1, ref arg1), FunctionElim(ref abs2, ref arg2)) =>
            is_terms_eq(abs1, abs2) && is_terms_eq(arg1, arg2),
        (VoidTypeIntro, VoidTypeIntro) => true,
        (UnitTypeIntro, UnitTypeIntro) => true,
        (UnitIntro, UnitIntro) => true,
        (PairTypeIntro(ref fst_type1, ref snd_type1), PairTypeIntro(ref fst_type2, ref snd_type2)) =>
            is_terms_eq(fst_type1, snd_type1) && is_terms_eq(fst_type2, snd_type2),
        (PairIntro(ref fst1, ref snd1), PairIntro(ref fst2, ref snd2)) =>
            is_terms_eq(fst1, fst2) && is_terms_eq(snd1, snd2),
        (PairElim(ref discrim1, ref body1), PairElim(ref discrim2, ref body2)) =>
            is_terms_eq(discrim1, discrim2) && is_terms_eq(body1, body2),
        (DoubTypeIntro, DoubTypeIntro) => true,
        (DoubIntro(ref label1), DoubIntro(ref label2)) =>
            label1 == label2,
        (DoubElim(ref discrim1, ref branch11, ref branch21), DoubElim(ref discrim2, ref branch12, ref branch22)) =>
            is_terms_eq(discrim1, discrim2) && is_terms_eq(branch11, branch12) && is_terms_eq(branch21, branch22),
        (FoldTypeIntro(ref inner_type1), FoldTypeIntro(ref inner_type2)) =>
            is_terms_eq(inner_type1, inner_type2),
        (FoldIntro(ref inner_term1), FoldIntro(ref inner_term2)) =>
            is_terms_eq(inner_term1, inner_term2),
        (FoldElim(ref inner_term1), FoldElim(ref inner_term2)) =>
            is_terms_eq(inner_term1, inner_term2),
        (CapturesListTypeIntro(level1), CapturesListTypeIntro(level2)) =>
            level1 == level2,
        (CapturesListIntro(ref list1), CapturesListIntro(ref list2)) =>
            match (list1, list2) {
                (Cons(ref data1, ref next1), Cons(ref data2, ref next2)) =>
                    is_terms_eq(data1, data2) && is_terms_eq(next1, next2),
                (Nil, Nil) => true,
                _ => false
            }
        _ => false
    }
}

// impl std::fmt::Display for Term {
//     fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
//         let string_form =
//             match self.data {

//             }
//         write!(formatter, "{}", string_form)
//     }
// } 