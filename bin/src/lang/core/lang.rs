#![allow(warnings)]

use std::{
    collections::{
        HashSet,
        HashMap
    },
    fmt::{self, Debug, Display},
    default::*,
    hash::Hash,
    convert::TryInto
};
use super::{
    context::*,
    eval::*,
    typing::{
        *,
        InnerError::*
    }
};
extern crate macros;
use macros::*;

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Note(pub String);

impl Debug for Note {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.0)
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
pub enum InnerVar {
    Bound(usize),
    Free(Symbol)
}
use InnerVar::*;

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum InnerTerm {
    TypeTypeIntro,
    Var(InnerVar),
    Rec(Term),
    Let(Vec<Term>, Term),
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
    Postulate(Symbol)
}
use InnerTerm::*;

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
            TypeTypeIntro => String::from("Univ"),
            Var(index) => format!("var {:?}", index),
            Rec(ref inner) => format!("rec\n{}", display_term(inner, indent + 1)),
            Let(ref bindings, ref body) => {
                let mut s = String::new();
                for (i, binding) in bindings.iter().enumerate() {
                    s = format!("{}ITEM '{}'{:?}\n", s, i, binding);
                }
                format!("{}\n{:?}", s, body)
            },
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
            IndexedTypeIntro(index, ref inner) => format!("Indexed {}\n{}", index, display_term(inner, indent + 1)),
            IndexedIntro(ref inner) => format!("indexed\n{}", display_term(inner, indent + 1)),
            IndexedElim(ref inner) => format!("indexedelim\n{}", display_term(inner, indent + 1)),
            Postulate(sym) => format!("postulate {:?}", sym)
        };
    format!("{}{}\n", indent_to_string(indent), string)
}

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub struct Location {
    pub line: usize
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Term {
    pub data: Box<InnerTerm>,
    pub type_ann: Option<Box<Term>>,
    pub note: Option<Note>,
    loc: Option<Location>
}

pub fn display_term(term: &Term, indent: usize) -> String {
    let mut string =
        format!("{}: {}Term \"{}\"\n",
            format!("{:5}", term.loc.map_or("no loc".to_string(), |loc| loc.line.to_string())), indent_to_string(indent),
            if let Some(Note(ref s)) = term.note {
                s.clone()
            } else {
                String::new()
            });
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

impl Term {
    pub fn new(data: Box<InnerTerm>, type_ann: Option<Box<Term>>) -> Term {
        Term {
            data,
            type_ann,
            note: None,
            loc: None
        }
    }

    pub fn new_with_note(note: Note, data: Box<InnerTerm>, type_ann: Option<Box<Term>>) -> Term {
        Term {
            data,
            type_ann,
            note: Some(note),
            loc: None
        }
    }

    pub fn loc(&self) -> Option<Location> {
        self.loc
    }

    // returns the type of a term, unchecked
    pub fn r#type(&self, context: Context) -> Term {
        use InnerTerm::*;
        use InnerVar::*;

        match &self.type_ann {
            Some(r#type) => normalize(*r#type.clone(), context),
            None =>
                match *self.data {
                    TypeTypeIntro => Term::new(Box::new(TypeTypeIntro), None),
                    // these are here only for convience of implementation, hence why they panic if the type can't be inferred
                    Var(index) =>
                        match context.get_dec(index) {
                            Some(var_type) => var_type,
                            None => panic!("(var) all terms must be explicitly typed, this term is not:\n{:#?}", self)
                        },
                    Let(ref bindings, ref body) => {
                        let num_bindings = bindings.len().try_into().unwrap();
                        let mut new_context = context.inc_and_shift(num_bindings);
                        for (i, binding) in bindings.iter().enumerate() {
                            let normal_binding = normalize(binding.clone(), new_context.clone());
                            let binding_type = binding.r#type(new_context.clone());
                            new_context = new_context
                                .with_dec(Bound(i), binding_type)
                                .with_def(Bound(i), normal_binding);
                        }
                        normalize(body.r#type(new_context.clone()), new_context)
                    },
                    FunctionElim(ref abs, ref arg) => {
                        let abs_type = abs.r#type(context.clone());
                        match &*abs_type.data {
                            FunctionTypeIntro(_, ref out_type) =>
                                normalize(
                                    out_type.clone(),
                                    context.clone().inc_and_shift(1)
                                        .with_def(Bound(0), normalize(arg.clone(), context))),
                            _ => panic!("(apply) all terms must be explicitly typed, this term is not:\n{:#?}", self)
                        } 
                    }
                    _ => panic!("all terms must be explicitly typed, this term is not:\n{:#?}", self)
                }
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

// checks if two terms are equal
pub fn is_terms_eq(type1: &Term, type2: &Term, equivs: HashSet<(InnerVar, InnerVar)>) -> TermComparison {
    use InnerTerm::*;
    /* TODO: figure out how to make this work properly
    let type_compare =
        match (&type1.type_ann, &type2.type_ann) {
            (Some(type_ann1), Some(type_ann2)) => is_terms_eq(&*type_ann1, &*type_ann2, equivs.clone()),
            (_, _) => False(vec![(type1.clone(), type2.clone())])
        };
    */
    let data_compare =
        match &(&(*type1.data), &(*type2.data)) {
            (TypeTypeIntro, TypeTypeIntro) => True,
            (Var(index1), Var(index2)) =>
                match index1 == index2 || equivs.contains(&(*index1, *index2)) {
                    true => True,
                    false => False(vec![(type1.clone(), type2.clone())])
                },
            (Rec(ref inner_term1), Rec(ref inner_term2)) =>
                is_terms_eq(inner_term1, inner_term2, equivs),
            (Let(ref bindings1, ref body1), Let(ref bindings2, ref body2)) =>
                comb(
                    bool_to_tc( // TODO: show specifics
                        bindings1.iter().zip(bindings2.iter())
                            .map(|(binding1, binding2)| is_terms_eq(binding1, binding2, equivs.clone()))
                            .all(|tc| if let True = tc { true } else { false })),
                    is_terms_eq(body1, body2, equivs.clone())),
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
            (Postulate(sym1), Postulate(sym2)) => bool_to_tc(sym1 == sym2),
            _ => False(vec![(type1.clone(), type2.clone())])
        };

    /*comb(*/data_compare/*, type_compare)*/
}

pub fn get_free_vars(term: &Term, bounds: HashSet<InnerVar>) -> HashMap<InnerVar, Term> {
    type Map = HashMap<InnerVar, Term>;

    fn inner(term: &Term, bounds: HashSet<InnerVar>) -> Map {
        fn collapse(maps: Vec<Map>) -> Map {
            let mut new_map: Map = HashMap::new();
            for map in maps {
                for (k, v) in map {
                    new_map.insert(k, v);
                }
            }
            new_map
        }

        fn inc(set: HashSet<InnerVar>) -> HashSet<InnerVar> {
            inc_by(set, 1)
        }

        fn inc_by(set: HashSet<InnerVar>, by: usize) -> HashSet<InnerVar> {
            let mut tmp = set.into_iter().map(|i| if let Bound(i_bound) = i { Bound(i_bound + by) } else { i }).collect::<HashSet<InnerVar>>();
            tmp
        }

        fn with(mut set: HashSet<InnerVar>, index: usize) -> HashSet<InnerVar> {
            set.insert(Bound(index));
            set
        }

        let type_ann_free_vars =
            if let Some(type_ann) = &term.type_ann {
                inner(&*type_ann, bounds.clone())
            } else {
                Map::new()
            };

        collapse(vec![
            match *term.data {
                TypeTypeIntro => HashMap::new(),
                Var(index) =>
                    if bounds.contains(&index) {
                        HashMap::new()
                    } else {
                        let mut map = HashMap::new();
                        map.insert(
                            if let Bound(bound_index) = index {
                                Bound(bound_index - bounds.len())
                            } else {
                                index
                            },
                            postulate!(Symbol(642968) ,: Univ!())); // a hack
                        map
                    },
                Rec(ref inner_term) => inner(inner_term, with(inc(bounds.clone()), 0)),
                Let(ref bindings, ref body) => unimplemented!(),
                FunctionTypeIntro(ref in_type, ref out_type) =>
                    collapse(vec![
                        inner(in_type, bounds.clone()),
                        inner(out_type, with(inc(bounds.clone()), 0))
                    ]),
                FunctionIntro(ref body) => inner(body, with(inc(bounds.clone()), 0)),
                FunctionElim(ref abs, ref arg) =>
                    collapse(vec![
                        inner(abs, bounds.clone()),
                        inner(arg, bounds)
                    ]),
                PairTypeIntro(ref fst_type, ref snd_type) =>
                    collapse(vec![
                        inner(fst_type, with(inc_by(bounds.clone(), 2), 1)),
                        inner(snd_type, with(inc_by(bounds.clone(), 2), 0))
                    ]),
                PairIntro(ref fst, ref snd) =>
                    collapse(vec![
                        inner(fst, bounds.clone()),
                        inner(snd, bounds)
                    ]),
                PairElim(ref discrim, ref body) =>
                    collapse(vec![
                        inner(discrim, bounds.clone()),
                        inner(body, with(with(inc_by(bounds.clone(), 2), 0), 1))
                    ]),
                VoidTypeIntro => HashMap::new(),
                UnitTypeIntro => HashMap::new(),
                UnitIntro => HashMap::new(),
                DoubTypeIntro => HashMap::new(),
                DoubIntro(_) => HashMap::new(),
                DoubElim(ref discrim, ref branch1, ref branch2) =>
                    collapse(vec![
                        inner(branch1, bounds.clone()),
                        inner(branch2, bounds.clone()),
                        inner(discrim, bounds)
                    ]),
                FoldTypeIntro(ref inner_type) => inner(inner_type, bounds.clone()),
                FoldIntro(ref inner_term) => inner(inner_term, bounds.clone()),
                FoldElim(ref folded_term) => inner(folded_term, bounds),
                IndexedTypeIntro(_, ref inner_type) => inner(inner_type, bounds.clone()),
                IndexedIntro(ref inner_term) => inner(inner_term, bounds.clone()),
                IndexedElim(ref folded_term) => inner(folded_term, bounds),
                Postulate(_) => Map::new()
            },
            type_ann_free_vars])
    }

    inner(term, bounds)
}

// for debugging
pub fn mark_lines(term: &mut Term) {
    fn mark_inner(term: &mut Term, loc: &mut Location) {
        term.loc = Some(*loc);
        loc.line += 1;
        match *term.data {
            Rec(ref mut inner) => mark_inner(inner, loc),
            Let(ref mut bindings, ref mut body) => {
                for binding in bindings {
                    mark_inner(binding, loc);
                }
                mark_inner(body, loc);
            },
            FunctionTypeIntro(ref mut in_type, ref mut out_type) => {
                mark_inner(in_type, loc);
                mark_inner(out_type, loc);
            },
            FunctionIntro(ref mut body) => mark_inner(body, loc),
            FunctionElim(ref mut abs, ref mut arg) => {
                mark_inner(abs, loc);
                mark_inner(arg, loc);
            },
            PairTypeIntro(ref mut fst_type, ref mut snd_type) => {
                mark_inner(fst_type, loc);
                mark_inner(snd_type, loc);
            },
            PairIntro(ref mut fst, ref mut snd) => {
                mark_inner(fst, loc);
                mark_inner(snd, loc);
            },
            PairElim(ref mut discrim, ref mut body) => {
                mark_inner(discrim, loc);
                mark_inner(body, loc);
            },
            DoubElim(ref mut discrim, ref mut branch1, ref mut branch2) => {
                mark_inner(discrim, loc);
                mark_inner(branch1, loc);
                mark_inner(branch2, loc);
            },
            FoldTypeIntro(ref mut inner_type) => mark_inner(inner_type, loc),
            FoldIntro(ref mut inner) => mark_inner(inner, loc),
            FoldElim(ref mut folded_term) => mark_inner(folded_term, loc),
            IndexedTypeIntro(_, ref mut inner_type) => mark_inner(inner_type, loc),
            IndexedIntro(ref mut inner) => mark_inner(inner, loc),
            IndexedElim(ref mut indexed_term) => mark_inner(indexed_term, loc),
            _ => ()
        }

        if let Some(ref mut type_ann) = term.type_ann {
            mark_inner(type_ann, loc);
        }
    }

    mark_inner(term, &mut Location { line: 0 })
}