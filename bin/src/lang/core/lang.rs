#![allow(warnings)]

use std::{
    collections::HashSet,
    fmt::{self, Debug, Display},
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

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Note(pub String);

impl Debug for Note {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

#[derive(Copy, Clone, PartialEq, Hash, Eq)]
pub enum Usage {
    Unique,
    Shared
}

impl Debug for Usage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", match self { Unique => "unique", Shared => "shared" })
    }
}

#[derive(Copy, Clone, PartialEq, Hash, Eq)]
pub enum Doub {
    This,
    That
}

impl Display for Doub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", match self { This => "this", That => "that" })
    }
}

#[derive(Copy, Clone, PartialEq, Hash, Eq, Debug)]
pub struct Symbol(pub usize);

#[derive(Copy, Clone, PartialEq, Hash, Eq, Debug)]
pub enum VarInner {
    Bound(usize),
    Free(Symbol)
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum InnerTerm {
    TypeTypeIntro(usize, Usage),
    Var(VarInner),
    Rec(Term),
    FunctionTypeIntro(Term, Term),
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
    IndexedTypeIntro(usize, Term),
    IndexedIntro(Term),
    IndexedElim(Term),
    Anything
}

fn indent_to_string(indent: usize) -> String {
    let mut string = String::new();
    for _ in 0..indent {
        string.push_str("|   ");
    }
    string
}

fn display_inner_term(term: &InnerTerm, indent: usize) -> String {
    use InnerTerm::*;

    let string =
        match term {
            TypeTypeIntro(level, usage) => format!("Univ {} {:?}", level, usage),
            Var(index) => format!("var {:?}", index),
            Rec(ref inner) => format!("rec\n{}", display_term(inner, indent + 1)),
            FunctionTypeIntro(ref in_type, ref out_type) =>
                format!("Pi\n{}\n{}",
                    display_term(in_type, indent + 1),
                    display_term(out_type, indent + 1)),
            FunctionIntro(ref body) => format!("lam\n{}", display_term(body, indent + 1)),
            FunctionElim(ref abs, ref arg) =>
                format!("app\n{}\n{}", display_term(abs, indent + 1), display_term(arg, indent + 1)),
            PairTypeIntro(ref fst_type, ref snd_type) =>
                format!("Sigma\n{}\n{}", display_term(fst_type, indent + 1), display_term(snd_type, indent + 1)),
            PairIntro(ref fst, ref snd) =>
                format!("pair\n{}\n{}", display_term(fst, indent + 1), display_term(snd, indent + 1)),
            PairElim(ref discrim, ref body) =>
                format!("split\n{}\n{}", display_term(discrim, indent + 1), display_term(body, indent + 1)),
            VoidTypeIntro => String::from("Void"),
            UnitTypeIntro => String::from("Unit"),
            UnitIntro => String::from("unit"),
            DoubTypeIntro => String::from("Doub"),
            DoubIntro(val) => format!("{}", val),
            DoubElim(ref discrim, ref branch1, ref branch2) =>
                format!("case\n{}\n{}\n{}",
                    display_term(discrim, indent + 1),
                    display_term(branch1, indent + 1),
                    display_term(branch2, indent + 1)),
            FoldTypeIntro(ref inner) => format!("Fold\n{}", display_term(inner, indent + 1)),
            FoldIntro(ref inner) => format!("fold\n{}", display_term(inner, indent + 1)),
            FoldElim(ref inner) => format!("unfold\n{}", display_term(inner, indent + 1)),
            IndexedTypeIntro(_, ref inner) => format!("Indexed\n{}", display_term(inner, indent + 1)),
            IndexedIntro(ref inner) => format!("indexed\n{}", display_term(inner, indent + 1)),
            IndexedElim(ref inner) => format!("indexedelim\n{}", display_term(inner, indent + 1)),
            Anything => String::from("Anything")
        };
    format!("{}{}\n", indent_to_string(indent), string)
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Location {
    line: usize
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Term {
    pub data: Box<InnerTerm>,
    pub type_ann: Option<Box<Term>>,
    pub note: Option<Note>,
    loc: Location
}

static mut line: usize = 0;

// impl Clone for Term {
//     fn clone(&self) -> Term {
//         unsafe { line += 1; }
//         Term {
//             data: self.data.clone(),
//             type_ann: self.type_ann.clone(),
//             note: self.note.clone(),
//             loc: Location { line: unsafe { line } }
//         }
//     }
// }

fn display_term(term: &Term, indent: usize) -> String {
    let mut string = format!("{}: {}Term \"{}\"\n", format!("{:5}", term.loc.line), indent_to_string(indent), if let Some(Note(ref s)) = term.note { s.clone() } else { String::new() });
    string = format!("{}       {}", string, display_inner_term(&*term.data, indent + 1));
    if let Some(type_ann) = &term.type_ann {
        string = format!("{}    {}", string, display_term(&*type_ann, indent + 1));
    }
    string
}

impl Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", display_term(self, 0))
    }
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
        unsafe { line += 1; }
        Term {
            data,
            type_ann,
            note: None,
            loc: Location { line: unsafe { line } }
        }
    }

    pub fn new_with_note(note: Note, data: Box<InnerTerm>, r#type_ann: Option<Box<Term>>) -> Term {
        unsafe { line += 1; }
        Term {
            data,
            type_ann,
            note: Some(note),
            loc: Location { line: unsafe { line } }
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
        let r#type = self.r#type();
        match *normalize(r#type, Context::new()).data {
            InnerTerm::TypeTypeIntro(level, _) => level,
            _ => panic!("level can only be extracted from types\n{:?}", self)
        }
    }
}

#[derive(Debug)]
pub enum TermComparison {
    True,
    False(Vec<(Term, Term)>)
}
use TermComparison::*;

pub fn comb<'a>(c1: TermComparison, c2: TermComparison) -> TermComparison {
    match (c1, c2) {
        (True, True) => True,
        (False(terms), True) => False(terms),
        (True, False(terms)) => False(terms),
        (False(terms1), False(terms2)) => {
            let mut all_terms = Vec::new();
            for term in terms1.into_iter() {
                all_terms.push(term);
            }
            for term in terms2.into_iter() {
                all_terms.push(term);
            }
            False(all_terms)
        }
    }
}

fn bool_to_tc(it: bool) -> TermComparison {
    match it {
        true => True,
        false => False(Vec::new())
    }
}

static mut count: usize = 0;

// checks if two terms are equal, disregarding type ann
pub fn is_terms_eq(type1: &Term, type2: &Term, equivs: HashSet<(VarInner, VarInner)>) -> TermComparison {
    use InnerTerm::*;

    match &(&(*type1.data), &(*type2.data)) {
        (TypeTypeIntro(level1, usage1), TypeTypeIntro(level2, usage2)) =>
            comb(bool_to_tc(level1 <= level2), bool_to_tc(usage1 == usage2)),
        (Var(index1), Var(index2)) => bool_to_tc(index1 == index2 || equivs.contains(&(*index1, *index2))),
        (Rec(ref inner_term1), Rec(ref inner_term2)) =>
            is_terms_eq(inner_term1, inner_term2, equivs),
        (FunctionTypeIntro(ref in_type1, ref out_type1), FunctionTypeIntro(ref in_type2, ref out_type2)) =>
            comb(is_terms_eq(in_type1, in_type2, equivs.clone()), is_terms_eq(out_type1, out_type2, equivs)),
        (FunctionIntro(ref body1), FunctionIntro(ref body2)) =>
            is_terms_eq(body1, body2, equivs),
        (FunctionElim(ref abs1, ref arg1), FunctionElim(ref abs2, ref arg2)) =>
            comb(is_terms_eq(abs1, abs2, equivs.clone()), is_terms_eq(arg1, arg2, equivs)),
        (VoidTypeIntro, VoidTypeIntro) => True,
        (UnitTypeIntro, UnitTypeIntro) => True,
        (UnitIntro, UnitIntro) => True,
        (PairTypeIntro(ref fst_type1, ref snd_type1), PairTypeIntro(ref fst_type2, ref snd_type2)) =>
            comb(is_terms_eq(fst_type1, fst_type2, equivs.clone()), is_terms_eq(snd_type1, snd_type2, equivs)),
        (PairIntro(ref fst1, ref snd1), PairIntro(ref fst2, ref snd2)) =>
            comb(is_terms_eq(fst1, fst2, equivs.clone()), is_terms_eq(snd1, snd2, equivs)),
        (PairElim(ref discrim1, ref body1), PairElim(ref discrim2, ref body2)) =>
            comb(is_terms_eq(discrim1, discrim2, equivs.clone()), is_terms_eq(body1, body2, equivs)),
        (DoubTypeIntro, DoubTypeIntro) => True,
        (DoubIntro(ref label1), DoubIntro(ref label2)) =>
            bool_to_tc(label1 == label2),
        (DoubElim(ref discrim1, ref left_branch1, ref right_branch1), DoubElim(ref discrim2, ref left_branch2, ref right_branch2)) =>
            comb(is_terms_eq(discrim1, discrim2, equivs.clone()), comb(is_terms_eq(left_branch1, left_branch2, equivs.clone()), is_terms_eq(right_branch1, right_branch2, equivs))),
        (FoldTypeIntro(ref inner_type1), FoldTypeIntro(ref inner_type2)) =>
            is_terms_eq(inner_type1, inner_type2, equivs),
        (FoldIntro(ref inner_term1), FoldIntro(ref inner_term2)) =>
            is_terms_eq(inner_term1, inner_term2, equivs),
        (FoldElim(ref inner_term1), FoldElim(ref inner_term2)) =>
            is_terms_eq(inner_term1, inner_term2, equivs),
        (IndexedTypeIntro(index1, ref inner_type1), IndexedTypeIntro(index2, ref inner_type2)) => 
            comb(is_terms_eq(inner_type1, inner_type2, equivs), bool_to_tc(index1 == index2)),
        (IndexedIntro(ref inner_term1), IndexedIntro(ref inner_term2)) => 
            is_terms_eq(inner_term1, inner_term2, equivs),
        (IndexedElim(ref inner_term1), IndexedElim(ref inner_term2)) =>
            is_terms_eq(inner_term1, inner_term2, equivs),
        (Anything, _) => True,
        (_, Anything) => True,
        _ => False(vec![(type1.clone(), type2.clone())])
    }
}