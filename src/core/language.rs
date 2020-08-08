#![allow(warnings)]

use std::collections::HashSet;
use std::fmt::Debug;
use std::default::*;
use super::context::*;

pub fn wrap<T: Default>(term: InnerTerm<T>) -> Term<T> { (Box::new(term), Default::default()) }

#[derive(Clone, Debug, PartialEq)]
pub enum CapturesList<T> { // ex: `Int -> <(Int, Nil)> Int -> Int`, type of `+`
    Cons(Term<T>, Term<T>),
    Nil
}

#[derive(Clone, Debug, PartialEq)]
pub enum InnerTerm<T> {
    Ann(Term<T>, Term<T>),
    UniverseIntro(usize),
    Var(usize),
    Rec(Term<T>),
    FunctionTypeIntro(/*Term<T>, */Term<T>, Term<T>),
    FunctionIntro(Term<T>),
    FunctionElim(Term<T>, Term<T>),
    PairTypeIntro(Term<T>, Term<T>),
    PairIntro(Term<T>, Term<T>),
    PairElim(Term<T>, Term<T>),
    EnumTypeIntro(usize),
    EnumIntro(usize),
    EnumElim(Term<T>, Vec<Term<T>>),
    /*
    CapturesListTypeIntro,
    CapturesListIntro(CapturesList<T>),
    */
    UniqueTypeIntro(Term<T>),
    UniqueIntro(Term<T>),
    UniqueElim(Term<T>),
    FoldTypeIntro(Term<T>),
    FoldIntro(Term<T>),
    FoldElim(Term<T>)
}

pub type Term<T> = (Box<InnerTerm<T>>, T);

pub fn shift<T>(term: Term<T>, bounds: HashSet<usize>, amount: isize) -> Term<T> {
    use InnerTerm::*;

    let term_inner: InnerTerm<T> =
        match *term.0 {
            Ann(annd_term, type_ann) => Ann(shift(annd_term, bounds.clone(), amount), shift(type_ann, bounds, amount)),
            Var(index) =>
                if !bounds.contains(&index) {
                    Var(((index as isize) + amount) as usize)
                } else {
                    Var(index)
                },
            Rec(inner_term) => Rec(shift(inner_term, bounds.into_iter().map(|i| i + 1).collect(), amount)),
            UniverseIntro(level) => UniverseIntro(level),
            FunctionTypeIntro(in_type, out_type) => {
                let out_type_bounds = {
                    let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 1).collect();
                    tmp.insert(0);
                    tmp
                };
                FunctionTypeIntro(
                    shift(in_type, bounds, amount),
                    shift(out_type, out_type_bounds, amount))
            },
            FunctionIntro(body) => {
                let body_bounds = {
                    let mut tmp: HashSet<usize> = bounds.into_iter().map(|i| i + 1).collect();
                    tmp.insert(0);
                    tmp
                };
                FunctionIntro(shift(body, body_bounds, amount))
            },
            FunctionElim(abs, arg) => FunctionElim(shift(abs, bounds.clone(), amount), shift(arg, bounds, amount)),
            PairTypeIntro(fst_type, snd_type) => {
                let fst_type_bounds = {
                    let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 1).collect();
                    tmp.insert(0);
                    tmp
                };
                let snd_type_bounds = fst_type_bounds.clone();
                PairTypeIntro(shift(fst_type, fst_type_bounds, amount), shift(snd_type, snd_type_bounds, amount))
            },
            PairIntro(fst, snd) => PairIntro(shift(fst, bounds.clone(), amount), shift(snd, bounds, amount)),
            PairElim(discrim, body) => {
                let body_bounds = {
                    let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 2).collect();
                    tmp.insert(0);
                    tmp.insert(1);
                    tmp
                };
                PairElim(shift(discrim, bounds, amount), shift(body, body_bounds, amount))
            },
            EnumTypeIntro(num_mems) => EnumTypeIntro(num_mems),
            EnumIntro(label) => EnumIntro(label),
            EnumElim(discrim, branches) => EnumElim(shift(discrim, bounds.clone(), amount), branches.into_iter().map(|b| shift(b, bounds.clone(), amount)).collect()),
            UniqueTypeIntro(inner_type) => UniqueTypeIntro(shift(inner_type, bounds, amount)),
            UniqueIntro(inner_term) => UniqueIntro(shift(inner_term, bounds, amount)),
            UniqueElim(unique_term) => UniqueElim(shift(unique_term, bounds, amount)),
            FoldTypeIntro(inner_type) => FoldTypeIntro(shift(inner_type, bounds, amount)),
            FoldIntro(inner_term) => FoldIntro(shift(inner_term, bounds, amount)),
            FoldElim(inner_term) => FoldElim(shift(inner_term, bounds, amount))
        };
    (Box::new(term_inner), term.1)
}

pub fn substitute<T: Clone>(subst_term: Term<T>, context: Context<T>) -> Term<T> {
    use InnerTerm::*;

    let term_inner: InnerTerm<T> =
        match *subst_term.0 {
            Ann(annd_term, type_ann) => Ann(substitute(annd_term, context.clone()), substitute(type_ann, context)),
            Var(index) =>
                match context.find(index) {
                    Some(val) => *val.0,
                    None => Var(index)
                }
            Rec(inner_term) => Rec(substitute(inner_term, context.inc_and_shift(1))),
            UniverseIntro(level) => UniverseIntro(level),
            FunctionTypeIntro(in_type, out_type) => {
                let out_type_context = context.clone().inc_and_shift(1);
                FunctionTypeIntro(
                    substitute(in_type, context),
                    substitute(out_type, out_type_context))
            },
            FunctionIntro(body) => {
                let body_context = context.inc_and_shift(1);
                FunctionIntro(substitute(body, body_context))
            },
            FunctionElim(abs, arg) => FunctionElim(substitute(abs, context.clone()), substitute(arg, context)),
            PairTypeIntro(fst_type, snd_type) => {
                let fst_type_context = context.clone().inc_and_shift(1);
                let snd_type_context = fst_type_context.clone();
                PairTypeIntro(substitute(fst_type, fst_type_context), substitute(snd_type, snd_type_context))
            },
            PairIntro(fst, snd) => PairIntro(substitute(fst, context.clone()), substitute(snd, context)),
            PairElim(discrim, body) => {
                let body_context = context.clone().inc_and_shift(2);
                PairElim(substitute(discrim, context), substitute(body, body_context))
            },
            EnumTypeIntro(num_mems) => EnumTypeIntro(num_mems),
            EnumIntro(label) => EnumIntro(label),
            EnumElim(discrim, branches) => EnumElim(substitute(discrim, context.clone()), branches.into_iter().map(|b| substitute(b, context.clone())).collect()),
            UniqueTypeIntro(inner_type) => UniqueTypeIntro(substitute(inner_type, context)),
            UniqueIntro(inner_term) => UniqueIntro(substitute(inner_term, context)),
            UniqueElim(unique_term) => UniqueElim(substitute(unique_term, context)),
            FoldTypeIntro(inner_type) => FoldTypeIntro(substitute(inner_type, context)),
            FoldIntro(inner_term) => FoldIntro(substitute(inner_term, context)),
            FoldElim(inner_term) => FoldElim(substitute(inner_term, context))
        };
    (Box::new(term_inner), subst_term.1)
}

pub fn normalize<T: Clone>(term: Term<T>, context: Context<T>) -> Term<T> {
    use InnerTerm::*;
    use CapturesList::*;

    match *term.0 {
        Ann(annd_term, type_ann) => normalize(annd_term, context),
        Var(index) => context.find(index).unwrap_or(term),
        Rec(inner_term) => {
            let new_context = context.inc_and_shift(1).insert(0, (Box::new(Rec(inner_term.clone())), term.1)).shift(1);
            shift(normalize(inner_term, new_context), HashSet::new(), -1)
        }
        UniverseIntro(level) => term,
        FunctionTypeIntro(in_type, out_type) => {
            let out_type_context = context.clone().inc_and_shift(1);
            (Box::new(FunctionTypeIntro(normalize(in_type, context), normalize(out_type, out_type_context))), term.1)
        },
        FunctionIntro(body) => (Box::new(FunctionIntro(substitute(body, context.inc_and_shift(1)))), term.1),
        FunctionElim(abs, arg) => {
            let normal_abs = normalize(abs, context.clone());
            let normal_arg = normalize(arg, context.clone());

            match *normal_abs.0 {
                FunctionIntro(body) => {
                    let body_context = context.clone().inc_and_shift(1).insert(0, normal_arg).shift(1);
                    shift(normalize(body, body_context), HashSet::new(), -1)
                },
                _ => {
                    (Box::new(FunctionElim(normal_abs, normal_arg)), term.1)
                }
            }
        },
        PairTypeIntro(fst_type, snd_type) => {
            let new_context = context.inc_and_shift(2);
            (Box::new(PairTypeIntro(normalize(fst_type, new_context.clone()), normalize(snd_type, new_context))), term.1)
        },
        PairIntro(fst, snd) => (Box::new(PairIntro(normalize(fst, context.clone()), normalize(snd, context))), term.1),
        PairElim(discrim, body) => {
            let normal_discrim = normalize(discrim, context.clone());
            match *normal_discrim.0 {
                PairIntro(fst, snd) => {
                    let normal_fst = normalize(fst, context.clone());
                    let normal_snd = normalize(snd, context.clone());
                    let new_context = context.clone().inc_and_shift(2).insert(0, normal_fst).insert(1, normal_snd).shift(2);
                    shift(normalize(body, new_context), HashSet::new(), -2)
                },
                _ => (Box::new(PairElim(normal_discrim, normalize(body, context.inc_and_shift(2)))), term.1)
            }
        },
        EnumTypeIntro(num_mems) => term,
        EnumIntro(label) => term,
        EnumElim(discrim, branches) => {
            let normal_discrim = normalize(discrim, context.clone());
            let fail_term = (Box::new(EnumElim(normal_discrim.clone(), branches.clone().into_iter().map(|b| normalize(b, context.clone())).collect())), term.1);
            match *normal_discrim.0 {
                EnumIntro(label) =>
                    if label < branches.len() {
                        normalize(branches[label].clone(), context)
                    } else {
                        fail_term
                    }
                _ => fail_term
            }
        },
        UniqueTypeIntro(inner_type) => (Box::new(UniqueTypeIntro(normalize(inner_type, context))), term.1),
        UniqueIntro(inner_term) => (Box::new(UniqueIntro(normalize(inner_term, context))), term.1),
        UniqueElim(unique_term) => {
            let normal_unique_term = normalize(unique_term, context);
            match *normal_unique_term.0 {
                UniqueIntro(inner_term) => inner_term,
                _ => (Box::new(UniqueElim(normal_unique_term)), term.1)
            }
        },
        FoldTypeIntro(inner_type) => (Box::new(FoldTypeIntro(substitute(inner_type, context))), term.1),
        FoldIntro(inner_term) => (Box::new(FoldIntro(normalize(inner_term, context))), term.1),
        FoldElim(folded_term) => {
            let normal_folded_term = normalize(folded_term, context);
            match *normal_folded_term.0 {
                FoldIntro(inner_term) => inner_term,
                _ => (Box::new(FoldElim(normal_folded_term)), term.1)
            }
        }
    }
}