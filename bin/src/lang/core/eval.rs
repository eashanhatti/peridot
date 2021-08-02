use super::{
    context::*,
    lang::{
        *,
        InnerVar::*,
        InnerTerm::*,
        Doub::*,
        TermComparison
    }
};
use std::{
    collections::{HashSet, HashMap},
    convert::TryInto
};

pub fn shift(term: Term, bounds: HashSet<usize>, amount: isize) -> Term {
    let shifted_type_ann =
        match term.type_ann {
            Some(r#type) => Some(Box::new(shift(*r#type, bounds.clone(), amount))),
            None => None
        };
    fn inc_bounds(bounds: HashSet<usize>) -> HashSet<usize> {
        let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 1).collect();
        tmp.insert(0);
        tmp
    }
    let term_inner: InnerTerm =
        match *term.data {
            Var(index) =>
                if let Bound(bound_index) = index {
                    if !bounds.contains(&bound_index) {
                        Var(Bound(((bound_index as isize) + amount) as usize))
                    } else {
                        Var(index)
                    }
                } else {
                    Var(index)
                },
            Rec(inner_term) => Rec(shift(inner_term, inc_bounds(bounds), amount)),
            Let(bindings, body) => { // TODO: determine if this is correct
                let len = bindings.len();
                let mut new_bounds: HashSet<usize> = bounds.into_iter().map(|i| i + len).collect();
                for i in 0..len {
                    new_bounds.insert(i);
                }
                Let(bindings.into_iter().map(|binding| shift(binding, new_bounds.clone(), amount)).collect(), shift(body, new_bounds, amount))
            }
            TypeTypeIntro => TypeTypeIntro,
            FunctionTypeIntro(in_type, out_type) =>
                FunctionTypeIntro(
                    shift(in_type, bounds.clone(), amount),
                    shift(out_type, inc_bounds(bounds), amount)),
            FunctionIntro(body) => FunctionIntro(shift(body, inc_bounds(bounds), amount)),
            FunctionElim(abs, arg) => FunctionElim(shift(abs, bounds.clone(), amount), shift(arg, bounds, amount)),
            PairTypeIntro(fst_type, snd_type) => {
                let fst_type_bounds = {
                    let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 2).collect();
                    tmp.insert(1);
                    tmp
                };
                let snd_type_bounds = {
                    let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 2).collect();
                    tmp.insert(0);
                    tmp
                };
                PairTypeIntro(shift(fst_type, fst_type_bounds, amount), shift(snd_type, snd_type_bounds, amount))
            },
            PairIntro(fst, snd) => {
                let fst_bounds = {
                    let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 2).collect();
                    tmp.insert(1);
                    tmp
                };
                let snd_bounds = {
                    let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 2).collect();
                    tmp.insert(0);
                    tmp
                };
                PairIntro(shift(fst, fst_bounds.clone(), amount), shift(snd, snd_bounds, amount))
            },
            PairElim(discrim, body) => {
                let body_bounds = {
                    let mut tmp: HashSet<usize> = bounds.clone().into_iter().map(|i| i + 2).collect();
                    tmp.insert(0);
                    tmp.insert(1);
                    tmp
                };
                PairElim(
                    shift(discrim, bounds, amount),
                    shift(body, body_bounds, amount))
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
            IndexedTypeIntro(index, inner_type) => IndexedTypeIntro(index, shift(inner_type, bounds, amount)),
            IndexedIntro(inner_term) => IndexedIntro(shift(inner_term, bounds, amount)),
            IndexedElim(discrim, body) => IndexedElim(shift(discrim, bounds.clone(), amount), shift(body, inc_bounds(bounds), amount)),
            Postulate(sym) => Postulate(sym)
        };
    let mut new_term = Term::new(Box::new(term_inner), shifted_type_ann);
    new_term.note = term.note;
    new_term
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
            Let(bindings, body) => {
                let mut new_context = context.inc_and_shift(bindings.len().try_into().unwrap());
                let mut subst_bindings = Vec::new();
                for (i, binding) in bindings.into_iter().enumerate() {
                    let subst_binding = substitute(binding, new_context.clone());
                    subst_bindings.push(subst_binding.clone());
                    new_context = new_context.with_def(Bound(i), subst_binding);
                }

                Let(subst_bindings, substitute(body, new_context))
            }
            TypeTypeIntro => TypeTypeIntro,
            FunctionTypeIntro(in_type, out_type) => {
                let out_type_context = context.clone().inc_and_shift(1);
                FunctionTypeIntro(
                    substitute(in_type, context),
                    substitute(out_type, out_type_context))
            },
            FunctionIntro(body) => FunctionIntro(substitute(body, context.inc_and_shift(1))),
            FunctionElim(abs, arg) => FunctionElim(substitute(abs, context.clone()), substitute(arg, context)),
            PairTypeIntro(fst_type, snd_type) => {
                let fst_type_context = context.clone().inc_and_shift(2);
                let snd_type_context = fst_type_context.clone();
                PairTypeIntro(substitute(fst_type, fst_type_context), substitute(snd_type, snd_type_context))
            },
            PairIntro(fst, snd) =>
                PairIntro(
                    substitute(fst, context.clone().inc_and_shift(2)),
                    substitute(snd, context.inc_and_shift(2))),
            PairElim(discrim, body) =>
                PairElim(
                    substitute(discrim, context.clone()),
                    substitute(body, context.inc_and_shift(2))),
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
            IndexedTypeIntro(index, inner_type) => IndexedTypeIntro(index, substitute(inner_type, context)),
            IndexedIntro(inner_term) => IndexedIntro(substitute(inner_term, context)),
            IndexedElim(discrim, body) => IndexedElim(substitute(discrim, context.clone()), substitute(body, context.inc_and_shift(1))),
            Postulate(sym) => Postulate(sym)
        };
    let mut new_term = Term::new(Box::new(term_inner), substd_type_ann);
    new_term.note = term.note;
    new_term
}

pub fn normalize(term: Term, context: Context) -> Term {
    let normal_type_ann =
        match term.type_ann.clone() {
            Some(r#type) => Some(Box::new(normalize(*r#type, context.clone()))),
            None => None
        };
    let term_note = term.note.clone();

    let new_term = match *term.data {
        Var(index) => context.get_def(index).unwrap_or(term),
        Rec(inner_term) => {
            let new_context = context.clone().inc_and_shift(1).with_def(Bound(0), Term::new(Box::new(Rec(inner_term.clone())), term.type_ann.clone())).shift(1);
            shift(normalize(inner_term, new_context), HashSet::new(), -1)
        },
        Let(bindings, body) => {
            let num_bindings = bindings.len().try_into().unwrap();
            let mut new_context = context.inc_and_shift(num_bindings);
            let mut normal_bindings = Vec::new();
            for (i, binding) in bindings.into_iter().enumerate() {
                let normal_binding = normalize(binding, new_context.clone());
                normal_bindings.push(normal_binding.clone());
                new_context = new_context.with_def(Bound(i), normal_binding);
            }

            shift(normalize(body, new_context), HashSet::new(), -(num_bindings as isize))
        },
        TypeTypeIntro => term,
        FunctionTypeIntro(in_type, out_type) => {
            let out_type_context = context.clone().inc_and_shift(1);
            Term::new(
                Box::new(FunctionTypeIntro(
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
                    shift(normalize(body, context.inc_and_shift(1).with_def(Bound(0), shifted_normal_arg)), HashSet::new(), -1)
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
        PairIntro(fst, snd) =>
            Term::new(Box::new(PairIntro(
                normalize(fst, context.clone().inc_and_shift(2)),
                normalize(snd, context.inc_and_shift(2)))),
                normal_type_ann),
        PairElim(discrim, body) => {
            let pre_normal_body = normalize(body, context.clone().inc_and_shift(2));
            let free_vars = get_free_vars(&pre_normal_body, HashSet::new());
            if !free_vars.contains_key(&Bound(0)) && !free_vars.contains_key(&Bound(1)) {
                shift(
                    pre_normal_body,
                    HashSet::new(),
                    -2)
            } else {
                let normal_discrim = normalize(discrim, context.clone());
                match *normal_discrim.clone().data {
                    PairIntro(fst, snd) =>
                        shift(
                            normalize(
                                pre_normal_body,
                                context.clone().inc_and_shift(2)
                                    .with_def(Bound(0), normalize(fst, context.clone()))
                                    .with_def(Bound(1), normalize(snd, context))),
                            HashSet::new(),
                            -2),
                    _ => 
                        Term::new(
                            Box::new(PairElim(
                                normal_discrim,
                                pre_normal_body)),
                            normal_type_ann)
                }
            }
        }
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
                    },
                _ => {
                    let normal_branch1 = normalize(branch1.clone(), context.clone());
                    let normal_branch2 = normalize(branch2.clone(), context.clone());
                    let cmp = is_terms_eq(&normal_branch1, &normal_branch2, context.equivs());
                    if let TermComparison::True = &cmp {
                        // println!("NB1{:?}", normal_branch1);
                        // println!("NB2{:?}", normal_branch2);
                        // println!("B1{:?}", branch1);
                        // println!("B2{:?}", branch2);
                        // println!("CTX {:#?}", context);
                        // println!("EQ {:?}", cmp);
                        normal_branch1
                    } else {
                        Term::new(
                            Box::new(DoubElim(
                                normal_discrim,
                                normal_branch1,
                                normal_branch2)),
                            normal_type_ann)
                    }
                }
            }
        },
        FoldTypeIntro(inner_type) => Term::new(Box::new(FoldTypeIntro(substitute(inner_type, context))), normal_type_ann),
        FoldIntro(inner_term) => normalize(inner_term, context), // is this a bug?
        FoldElim(folded_term) => {
            let normal_folded_term = normalize(folded_term, context);
            match *normal_folded_term.data {
                FoldIntro(inner_term) => inner_term,
                _ => Term::new(Box::new(FoldElim(normal_folded_term)), normal_type_ann)
            }
        },
        IndexedTypeIntro(index, inner_type) => Term::new(Box::new(IndexedTypeIntro(index, normalize(inner_type, context))), normal_type_ann),
        IndexedIntro(inner_term) => Term::new(Box::new(IndexedIntro(normalize(inner_term, context))), normal_type_ann),
        IndexedElim(discrim, body) => {
            let normal_discrim = normalize(discrim, context.clone());
            match *normal_discrim.data {
                IndexedIntro(inner_term) => {
                    let body_context = context.inc_and_shift(1).with_def(Bound(0), inner_term);
                    shift(normalize(body, body_context), HashSet::new(), -1)
                },
                _ => {
                    let body_context = context.clone().inc_and_shift(1);
                    let pre_normal_body = normalize(body, body_context);
                    if get_free_vars(&pre_normal_body, HashSet::new()).contains_key(&Bound(0)) {
                        Term::new(Box::new(IndexedElim(normal_discrim, pre_normal_body)), normal_type_ann)   
                    } else {
                        shift(pre_normal_body, HashSet::new(), -1)
                    }
                }
            }
        },
        Postulate(_) => term
    };
    // new_term.note = term_note;
    new_term
}