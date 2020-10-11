#![allow(warnings)]

use super::{
    context::*,
    lang::{
        *,
        InnerTerm::*,
        List::*,
        Doub::*
    }
};
use std::collections::HashSet;

pub fn shift(term: Term, bounds: HashSet<usize>, amount: isize) -> Term {
    let shifted_type_ann =
        match term.type_ann {
            Some(r#type) => Some(Box::new(shift(*r#type, bounds.clone(), amount))),
            None => None
        };
    let term_inner: InnerTerm =
        match *term.data {
            Var(index) =>
                if !bounds.contains(&index) {
                    Var(((index as isize) + amount) as usize)
                } else {
                    Var(index)
                },
            Rec(inner_term) => Rec(shift(inner_term, bounds.into_iter().map(|i| i + 1).collect(), amount)),
            TypeTypeIntro(level, usage) => TypeTypeIntro(level, usage),
            FunctionTypeIntro(caps_list, in_type, out_type) => {
                let out_type_bounds = {
                    let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 1).collect();
                    tmp.insert(0);
                    tmp
                };
                FunctionTypeIntro(
                    shift(caps_list, bounds.clone(), amount),
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
            VoidTypeIntro => VoidTypeIntro,
            UnitTypeIntro => UnitTypeIntro,
            UnitIntro => UnitIntro,
            DoubTypeIntro => DoubTypeIntro,
            DoubIntro(label) => DoubIntro(label),
            DoubElim(discrim, branch1, branch2) => 
                DoubElim(
                    shift(discrim, bounds.clone(), amount),
                    shift(branch1, bounds.clone(), amount),
                    shift(branch2, bounds, amount)),
            FoldTypeIntro(inner_type) => FoldTypeIntro(shift(inner_type, bounds, amount)),
            FoldIntro(inner_term) => FoldIntro(shift(inner_term, bounds, amount)),
            FoldElim(inner_term) => FoldElim(shift(inner_term, bounds, amount)),
            CapturesListTypeIntro(level) => CapturesListTypeIntro(level),
            CapturesListIntro(list) =>
                CapturesListIntro(
                    match list {
                        Cons(head, tail) => Cons(shift(head, bounds.clone(), amount), shift(tail, bounds, amount)),
                        Nil => Nil
                    })
        };
    Term::new(Box::new(term_inner), shifted_type_ann)
}

pub fn substitute(term: Term, context: Context) -> Term {
    let substd_type_ann =
        match term.type_ann {
            Some(r#type) => Some(Box::new(substitute(*r#type, context.clone()))),
            None => None
        };

    let term_inner: InnerTerm =
        match *term.data {
            Var(index) =>
                match context.get_def(index) {
                    Some(val) => *val.data,
                    None => Var(index)
                }
            Rec(inner_term) => Rec(substitute(inner_term, context.inc_and_shift(1))),
            TypeTypeIntro(level, usage) => TypeTypeIntro(level, usage),
            FunctionTypeIntro(caps_list, in_type, out_type) => {
                let out_type_context = context.clone().inc_and_shift(1);
                FunctionTypeIntro(
                    substitute(caps_list, context.clone()),
                    substitute(in_type, context),
                    substitute(out_type, out_type_context))
            },
            FunctionIntro(body) => FunctionIntro(substitute(body, context.inc_and_shift(1))),
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
            VoidTypeIntro => VoidTypeIntro,
            UnitTypeIntro => UnitTypeIntro,
            UnitIntro => UnitIntro,
            DoubTypeIntro => DoubTypeIntro,
            DoubIntro(label) => DoubIntro(label),
            DoubElim(discrim, branch1, branch2) =>
                DoubElim(
                    substitute(discrim, context.clone()),
                    substitute(branch1, context.clone()),
                    substitute(branch2, context)),
            FoldTypeIntro(inner_type) => FoldTypeIntro(substitute(inner_type, context)),
            FoldIntro(inner_term) => FoldIntro(substitute(inner_term, context)),
            FoldElim(inner_term) => FoldElim(substitute(inner_term, context)),
            CapturesListTypeIntro(level) => CapturesListTypeIntro(level),
            CapturesListIntro(list) =>
                CapturesListIntro(
                    match list {
                        Cons(head, tail) => Cons(substitute(head, context.clone()), substitute(tail, context)),
                        Nil => Nil
                    })
        };
    Term::new(Box::new(term_inner), substd_type_ann)
}

pub fn normalize(term: Term, context: Context) -> Term {
    let normal_type_ann =
        match term.type_ann.clone() {
            Some(r#type) => Some(Box::new(normalize(*r#type, context.clone()))),
            None => None
        };

    match *term.data {
        Var(index) => context.get_def(index).unwrap_or(term),
        Rec(inner_term) => {
            let new_context = context.clone().inc_and_shift(1).with_def(0, Term::new(Box::new(Rec(inner_term.clone())), term.type_ann.clone())).shift(1);
            shift(normalize(inner_term, new_context), HashSet::new(), -1)
        }
        TypeTypeIntro(level, usage) => term,
        FunctionTypeIntro(caps_list, in_type, out_type) => {
            let out_type_context = context.clone().inc_and_shift(1);
            Term::new(
                Box::new(FunctionTypeIntro(
                    normalize(caps_list, context.clone()),
                    normalize(in_type, context),
                    normalize(out_type, out_type_context))),
                normal_type_ann)
        },
        FunctionIntro(body) => Term::new(Box::new(FunctionIntro(substitute(body, context.inc_and_shift(1)))), normal_type_ann),
        FunctionElim(abs, arg) => {
            let normal_abs = normalize(abs, context.clone());
            let normal_arg = normalize(arg, context.clone());

            match *normal_abs.data {
                FunctionIntro(body) => {
                    let shifted_normal_arg = shift(normal_arg, HashSet::new(), 1);
                    shift(normalize(body, context.inc_and_shift(1).with_def(0, shifted_normal_arg)), HashSet::new(), -1)
                },
                _ =>
                    Term::new(
                        Box::new(FunctionElim(normal_abs, normal_arg)),
                        normal_type_ann)
            }
        },
        PairTypeIntro(fst_type, snd_type) => {
            let new_context = context.inc_and_shift(2);
            Term::new(
                Box::new(PairTypeIntro(normalize(fst_type, new_context.clone()), normalize(snd_type, new_context))),
                normal_type_ann)
        },
        PairIntro(fst, snd) => Term::new(Box::new(PairIntro(normalize(fst, context.clone()), normalize(snd, context))), normal_type_ann),
        PairElim(discrim, body) => {
            let normal_discrim = normalize(discrim, context.clone());
            match *normal_discrim.data {
                PairIntro(fst, snd) => {
                    let normal_fst = normalize(fst, context.clone());
                    let normal_snd = normalize(snd, context.clone());
                    let new_context = context.clone().inc_and_shift(2).with_def(0, normal_fst).with_def(1, normal_snd).shift(2);
                    shift(normalize(body, new_context), HashSet::new(), -2)
                },
                _ =>
                    Term::new(
                        Box::new(PairElim(normal_discrim, normalize(body, context.inc_and_shift(2)))),
                        normal_type_ann)
            }
        },
        VoidTypeIntro => term,
        UnitTypeIntro => term,
        UnitIntro => term,
        DoubTypeIntro => term,
        DoubIntro(_) => term,
        DoubElim(discrim, branch1, branch2) => {
            let normal_discrim = normalize(discrim, context.clone());
            match *(normal_discrim.clone()).data {
                DoubIntro(label) =>
                    match label {
                        This => normalize(branch1, context),
                        That => normalize(branch2, context)
                    }
                _ =>
                    Term::new(
                        Box::new(DoubElim(normal_discrim, normalize(branch1, Context::new()), normalize(branch2, Context::new()))),
                        normal_type_ann)
            }
        },
        FoldTypeIntro(inner_type) => Term::new(Box::new(FoldTypeIntro(substitute(inner_type, context))), normal_type_ann),
        FoldIntro(inner_term) => normalize(inner_term, context),
        FoldElim(folded_term) => {
            let normal_folded_term = normalize(folded_term, context);
            match *normal_folded_term.data {
                FoldIntro(inner_term) => inner_term,
                _ => Term::new(Box::new(FoldElim(normal_folded_term)), normal_type_ann)
            }
        },
        CapturesListTypeIntro(level) => term,
        CapturesListIntro(list) =>
            Term::new(
                Box::new(CapturesListIntro(
                    match list {
                        Cons(head, tail) => Cons(normalize(head, context.clone()), normalize(tail, context)),
                        Nil => Nil
                    })),
                normal_type_ann)
    }
}