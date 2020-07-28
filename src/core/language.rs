#![allow(warnings)]
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq)]
pub enum Usage {
    Unique,
    Shared
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeAttribs<T> {
    usage: Term<T>
}

#[derive(Clone, Debug, PartialEq)]
pub enum Type<T> {
    Pi(Term<T>, Term<T>, Term<T>),
    Sigma(Term<T>, Term<T>),
    EnumType(usize),
    Universe(usize),
    UsageType,
    CapturesListType
}

#[derive(Clone, Debug, PartialEq)]
pub enum CapturesList<T> { // ex: `Int -> <(Int, Nil)> Int -> Int`, type of `+`
    Cons(Term<T>, Term<T>),
    Nil
}

#[derive(Clone, Debug, PartialEq)]
pub enum InnerTerm<T> {
    Ann(Term<T>, Term<T>),
    Type(Type<T>, TypeAttribs<T>),
    Function(Term<T>),
    Apply(Term<T>, Term<T>),
    Pair(Term<T>, Term<T>),
    Split(Term<T>, Term<T>),
    Constant(usize),
    Case(Term<T>, Vec<Term<T>>),
    Var(usize),
    Usage(Usage),
    CapturesList(CapturesList<T>)
}

pub type Term<T> = (Box<InnerTerm<T>>, T);

pub enum InnerCheckError<T> {
    CantInferType,
    MismatchedTypes { exp_type: Term<T>, giv_type: Term<T> },
    NonexistentVar
}

pub struct CheckError<'a, T> {
    offending_term: &'a Term<T>
    error: InnerCheckError<T>
}

impl CheckError {
    fn new<'a, T>(offending_term: &'a Term<T>, error: InnerCheckError<T>) -> CheckError<'a, T> {
        CheckError {
            offending_term,
            error
        }
    }
}

pub fn shift<T>(term: Term<T>, amount: usize) -> Term<T> {
    fn shift_inner<T>(term: Term<T>, cutoff: usize, amount: isize) -> Term<T> {
        use self::Type::*;
        use InnerTerm::*;

        let rec = |rec_term| shift_inner(rec_term, cutoff, amount);
        let rec_inc = |rec_term| shift_inner(rec_term, cutoff + 1, amount);
        let rec_arb = |rec_term, cutoff_inc| shift_inner(rec_term, cutoff_inc, amount);

        let term_inner: InnerTerm<T> =
            match *term.0 {
                Ann(annd_term, type_ann) => Ann(rec(annd_term), rec(type_ann)),
                Type(r#type, type_attrs) =>
                    Type(match r#type {
                        Pi(capture_types, in_type, out_type) => self::Type::Pi(rec(capture_types), rec(in_type), rec_inc(out_type)),
                        Sigma(fst_type, snd_type) => self::Type::Sigma(rec_inc(fst_type), rec_inc(snd_type)),
                        _ => r#type
                    }, type_attrs),
                Function(body) => Function(rec_inc(body)),
                Apply(abs, arg) => Apply(rec(abs), rec(arg)),
                Pair(fst, snd) => {
                    let shifted_fst = rec(fst);
                    let shifted_snd = rec(snd);
                    Pair(shifted_fst, shifted_snd)
                },
                Split(discrim, body) => Split(rec(discrim), rec_arb(body, 2)),
                Constant(label) => Constant(label),
                Case(discrim, branches) => Case(rec(discrim), branches.into_iter().map(|b| rec_inc(b)).collect()),
                Var(index) => if index < cutoff { Var(index) } else { Var(index + amount) },
                Multiplicity(m) => Multiplicity(m),
                Stage(s) => Stage(s),
                CapturesList(list) => {
                    use self::CapturesList::*;
                    CapturesList(match list {
                        Cons(data, next) => Cons(rec(data), rec(next)),
                        Nil => Nil
                    })
                }
            };
        (Box::new(term_inner), term.1)
    }
    shift_inner(term, 0, amount) // shifts all the free variables in `term` by `amount`
}

pub fn substitute<T: Clone>(subst_term: Term<T>, with_term: Term<T>, target_index: usize) -> Term<T> {
    use self::Type::*;
    use InnerTerm::*;
    use self::CapturesList::*;

    (Box::new(match *subst_term.0 {
        Ann(annd_term, type_ann) => Ann(substitute(annd_term, with_term.clone(), target_index), substitute(type_ann, with_term, target_index)),
        Type(r#type, type_attrs) =>
            Type(match r#type {
                Pi(capture_types, in_type, out_type) =>
                    self::Type::Pi(
                        substitute(capture_types, with_term.clone(), target_index),
                        substitute(in_type, with_term.clone(), target_index),
                        substitute(out_type, with_term, target_index + 1)),
                Sigma(fst_type, snd_type) => self::Type::Sigma(substitute(fst_type, with_term.clone(), target_index + 1), substitute(snd_type, with_term, target_index + 1)),
                _ => r#type
            }, type_attrs),
        Function(body) => Function(substitute(body, with_term, target_index + 1)),
        Apply(abs, arg) => Apply(substitute(abs, with_term.clone(), target_index), substitute(arg, with_term, target_index)),
        Pair(fst, snd) => {
            let substd_fst = substitute(fst, with_term.clone(), target_index);
            let substd_snd = substitute(snd, with_term, target_index);
            Pair(substd_fst, substd_snd)
        },
        Split(discrim, body) => Split(substitute(discrim, with_term.clone(), target_index), substitute(body, with_term, target_index + 2)),
        Constant(label) => Constant(label),
        Case(discrim, branches) => Case(substitute(discrim, with_term.clone(), target_index), branches.into_iter().map(|b| substitute(b, with_term.clone(), target_index + 1)).collect()),
        Var(index) => if index == target_index { *with_term.0 } else { Var(index) },
        Multiplicity(m) => Multiplicity(m),
        Stage(s) => Stage(s),
        CapturesList(list) =>
            CapturesList(match list {
                Cons(data, next) => Cons(substitute(data, with_term.clone(), target_index), substitute(next, with_term, target_index)),
                Nil => Nil
            })
    }), subst_term.1)
}

pub fn normalize<T: Clone>(term: Term<T>) -> Term<T> {
    fn normalize_inner<T: Clone>(term: Term<T>) -> Term<T> {
        use self::Type::*;
        use InnerTerm::*;
        use self::CapturesList::*;

        fn rec<T: Clone>(term: Term<T>) -> Result<Term<T>, ()> { normalize_inner(term) }

        match *term.0 {
            Ann(annd_term, type_ann) => rec(annd_term),
            Type(r#type, type_attrs) =>
                Ok((Box::new(Type(match r#type {
                    Pi(capture_types, in_type, out_type) => {
                        let normal_capture_types = rec(capture_types.clone()).unwrap_or(capture_types);
                        let normal_in_type = rec(in_type.clone()).unwrap_or(in_type);
                        let normal_out_type = rec(out_type.clone()).unwrap_or(out_type);
                        Pi(normal_capture_types, normal_in_type, normal_out_type)
                    },
                    Sigma(fst_type, snd_type) => {
                        let normal_fst_type = rec(fst_type.clone()).unwrap_or(fst_type);
                        let normal_snd_type = rec(snd_type.clone()).unwrap_or(snd_type);
                        Sigma(normal_fst_type, normal_snd_type)
                    },
                    _ => r#type
                }, type_attrs)), term.1)),
            Apply(abs, arg) => {
                let normal_abs = rec(abs.clone()).unwrap_or(abs);
                let normal_arg = rec(arg.clone()).unwrap_or(arg);
                match *normal_abs.0 {
                    Function(body) => {
                        let substd_arg_body = substitute(body, shift(normal_arg, 1), 0);
                        Ok(rec(substd_arg_body.clone()).unwrap_or((Box::new(Function(substd_arg_body)), term.1)))
                    },
                    _ => Err(())
                }
            },
            Pair(fst, snd) => {
                let normal_fst = rec(fst.clone()).unwrap_or(fst);
                let normal_snd = rec(snd.clone()).unwrap_or(snd);
                Ok((Box::new(Pair(normal_fst, normal_snd)), term.1))
            }
            Split(discrim, body) => {
                let normal_discrim = rec(discrim.clone()).unwrap_or(discrim);
                match *(normal_discrim.clone()).0 {
                    Pair(fst, snd) => {
                        let substd_fst_body = substitute(body.clone(), shift(fst, 1), 0);
                        let substd_snd_body = substitute(substd_fst_body, shift(snd, 2), 1);
                        Ok(rec(substd_snd_body).unwrap_or((Box::new(Split(normal_discrim, body)), term.1)))
                    },
                    _ => Err(())
                }
            },
            Case(discrim, branches) => {
                let normal_discrim = rec(discrim.clone()).unwrap_or(discrim);
                match *normal_discrim.0 {
                    Constant(label) =>
                        if label < branches.len() {
                            let normal_branch = rec(substitute(branches[label].clone(), normal_discrim.clone(), 0))
                            Ok(normal_branch.unwrap_or((Box::new(Case(normal_discrim, branches)), term.1))))
                        } else {
                            Err(())
                        },
                    _ => Err(())
                }
            },
            Var(_) => Err(()),
            CapturesList(list) =>
                Ok((Box::new(CapturesList(match list {
                    Cons(data, next) => {
                        let normal_data = rec(data.clone()).unwrap_or(data);
                        let normal_next = rec(next.clone()).unwrap_or(next);
                        Cons(normal_data, normal_next)
                    }
                    Nil => Nil
                })), term.1)),
            _ => Ok(term)
        }
    }

    normalize_inner(term.clone()).unwrap_or(term)
}

fn infer<T>(term: &'a Term<T>, context: Vec<Term<T>>) -> Result<Term, Vec<CheckError<'a, T>>> {
    match term.0 {
        Ann(_, type_ann) => Ok(type_ann.clone())
        Var(index) => if index < context.len() { Ok(context[index]) } else { Err(Vec::new(CheckError::new(term, NonexistentVar))) }
        _ => Err(vec![CheckError::new(term, CantInferType)])
    }
}

pub fn check<'a, T>(term: &'a Term<T>, context: Vec<Term<T>>, exp_type: Term<T>) -> Result<(), Vec<CheckError<'a, T>>> {
    match term.0 {
        Ann(ref annd_term, ref type_ann) =>
            match check(annd_term, context, normalize(type_ann)) {
                Ok(_) =>
                    if normalize(type_ann) == exp_type {
                        Ok(())
                    } else {
                        Err(vec![CheckError::new(annd_term, MismatchedTypes { exp_type, giv_type: normalize(type_ann) })])
                    },
                Err(errs) => Err(errs)
            },
        Type(r#type, type_attrs) =>
            match r#type {
                Pi(capture_types, in_type, out_type) => {
                    let normal_in_type = normalize(in_type);
                    let normal_out_type = normalize(out_type);

                    match (check(capture_types, context, CapturesListType), infer(normal_in_type, context)) {
                        (Ok(_), Ok(in_type_type)) => {
                            let new_context = context.clone();
                            new_context.insert(0, normal_in_type)

                            match infer(normal_out_type, new_context) { // universe levels are bogus right now, fix later
                                Ok(out_type_type) =>
                                    match (in_type_type.0, out_type_type.0) {
                                        (Universe(in_type_type_level), Universe(out_type_type_level)) =>
                                            match exp_type {
                                                Universe(max_level) =>
                                                other => Err(ve![CheckError::new(MismatchedTypes { exp_type: Universe(42), giv_type: other })])
                                            }
                                        (Universe(_), err_out_type_type) =>
                                            Err(vec![CheckError::new(MismatchedTypes { exp_type: Universe(0), giv_type: err_out_type_type })]),
                                        (err_in_type_type, Universe(_)) =>
                                            Err(vec![CheckError::new(MismatchedTypes { exp_type: Universe(0), giv_type: err_in_type_type })]),
                                        (err_in_type_type, err_out_type_type) =>
                                            Err(vec![
                                                CheckError::new(MismatchedTypes { exp_type: Universe(0), giv_type: err_in_type_type }),
                                                CheckError::new(MismatchedTypes { exp_type: Universe(0), giv_type: err_out_type_type })])
                                    }
                                Err(errs) => Err(errs)
                            }
                        }
                        (Err(errs), Ok(_)) => Err(errs),
                        (Ok(_), Err(errs)) => Err(errs),
                        (Err(errs1), Err(errs2)) => errs1.append(&mut errs2)
                    }
                },
            }
    }
}