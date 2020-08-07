#![feature(box_syntax, box_patterns)]
#![allow(warnings)]

use super::{language::*, context::*};
use InnerTerm::*;
use std::default::*;
use std::cmp::max;

pub enum InnerError<T> {
    MismatchedTypes { exp_type: Term<T>, giv_type: Term<T> },
    NonexistentVar(usize),
    ExpectedUniverse { giv_type: Term<T> },
    ExpectedFunctionType { giv_type: Term<T> },
    ExpectedPairType { giv_type: Term<T> }
}

pub struct Error<'a, T> {
    term: &'a Term<T>,
    error: InnerError<T>
}

impl<'a, T> Error<'a, T> {
    fn new(term: &'a Term<T>, error: InnerError<T>) -> Error<'a, T> {
        Error {
            term,
            error
        }
    }
}

type CheckResult<'a, T> = Result<(), Vec<Error<'a, T>>>;

fn flatten_errors<'a, T>(errors: Vec<Vec<Error<'a, T>>>) -> Vec<Error<'a, T>> {
	let mut new_errs = Vec::new();
	for mut column in errors {
		new_errs.append(&mut column);
	}
	new_errs
}

fn push_check<'a, T>(errors: &mut Vec<Error<'a, T>>, this_check: CheckResult<'a, T>) { // appends errors to an error list, if there are any
	match this_check {
		Ok(()) => {},
		Err(errs) => {
			for err in errs {
				errors.push(err);
			}
		}
	}
}

// returned type should always be in normal form
fn infer<'a, T: Clone>(term: &'a Term<T>, context: Context<T>) -> Term<T> { // core lang is explicitly typed, so inference should always succede
	match *term.0 {
		Ann(_, ref type_ann) => normalize(type_ann.clone(), context),
		_ => panic!("infer must be called on `Ann`s")
	}
}

fn is_terms_eq<T>(type1: &Term<T>, type2: &Term<T>) -> bool { // checks if two terms are equal, disregarding elab info
	unimplemented!()
}

fn wrap_checks<'a, T>(errors: Vec<Error<'a, T>>) -> CheckResult<'a, T> {
	if errors.len() > 0 {
		Err(errors)
	} else {
		Ok(())
	}
}

// exp_type should always be checked and in normal form
pub fn check<'a, T: Clone + PartialEq + Default>(term: &'a Term<T>, exp_type: Term<T>, context: Context<T>) -> CheckResult<T> {
	use InnerError::*;

	match *term.0 {
		Ann(ref annd_term, ref type_ann) => {
			let mut errors = Vec::new();
			
			let type_ann_type = infer(&type_ann, context.clone());
			let type_ann_check = check(&type_ann, type_ann_type, context.clone());
			let normal_type_ann = normalize(type_ann.clone(), context.clone());

			let annd_term_check = check(&annd_term, normal_type_ann.clone(), context);
			let eq_types_check =
				if is_terms_eq(&normal_type_ann, &exp_type) {
					Ok(())
				} else {
					Err(vec![Error::new(&term, MismatchedTypes { exp_type: exp_type.clone(), giv_type: normal_type_ann.clone() })])
				};

			push_check(&mut errors, type_ann_check);
			push_check(&mut errors, annd_term_check);
			push_check(&mut errors, eq_types_check);

			wrap_checks(errors)
		},
		UniverseIntro(level) =>
			match *(exp_type.clone()).0 {
				UniverseIntro(type_ann_level) =>
					if type_ann_level == level + 1 {
						Ok(())
					} else {
						Err(vec![Error::new(&term, MismatchedTypes { exp_type: (Box::new(UniverseIntro(level + 1)), Default::default()), giv_type: exp_type.clone()})])
					}
				_ => Err(vec![Error::new(&term, ExpectedUniverse { giv_type: exp_type })])
			},
		Var(index) =>
			match context.find(index) {
				Some(var_type) =>
					if is_terms_eq(&var_type, &exp_type) {
						Ok(())
					} else {
						Err(vec![Error::new(&term, MismatchedTypes { exp_type, giv_type: var_type })])
					}
				None => Err(vec![Error::new(&term, NonexistentVar(index))])
			},
		Rec(ref inner_term) => {
			let new_context = context.clone().inc_and_shift(1);
			let inner_term_type = infer(&inner_term, new_context.clone()); // for now, all recursive functions must be type annotated
			check(&inner_term, inner_term_type.clone(), new_context.insert(0, inner_term_type))
		},
		FunctionTypeIntro(ref in_type, ref out_type) => {
			let mut errors = Vec::new();
			let normal_in_type = normalize(in_type.clone(), context.clone());

			let in_type_type = infer(&in_type, context.clone());
			let in_type_check = check(&in_type, in_type_type.clone(), context.clone());

			let out_type_type = infer(&out_type, context.clone());
			let out_type_check = check(&out_type, out_type_type.clone(), context.inc_and_shift(1).insert(0, normal_in_type));

			push_check(&mut errors, in_type_check);
			push_check(&mut errors, out_type_check);

			match (*(in_type_type.clone()).0, *(out_type_type.clone()).0) {
				(UniverseIntro(in_level), UniverseIntro(out_level)) =>
					if let UniverseIntro(max_level) = *exp_type.clone().0 {
						if max(in_level, out_level) != max_level {
							errors.push(Error::new(
								&term,
								MismatchedTypes {
									exp_type: (Box::new(UniverseIntro(max_level)), Default::default()),
									giv_type: (Box::new(UniverseIntro(max(in_level, out_level))), Default::default())
								}));
						}
					} else {
						errors.push(Error::new(&term, ExpectedUniverse { giv_type: exp_type }))
					},
				(_, UniverseIntro(_)) => errors.push(Error::new(&in_type, ExpectedUniverse { giv_type: in_type_type })),
				(UniverseIntro(_), _) => errors.push(Error::new(&out_type, ExpectedUniverse { giv_type: out_type_type })),
				(_, _) =>  {
					errors.push(Error::new(&in_type, ExpectedUniverse { giv_type: in_type_type }));
					errors.push(Error::new(&out_type, ExpectedUniverse { giv_type: out_type_type }));
				}
			}

			wrap_checks(errors)
		},
		FunctionIntro(ref body) =>
			match *exp_type.0 {
				FunctionTypeIntro(in_type, out_type) => check(&body, out_type, context.inc_and_shift(1).insert(0, in_type)),
				_ => Err(vec![Error::new(&term, ExpectedFunctionType { giv_type: exp_type })])
			},
		FunctionElim(ref abs, ref arg) => {
			let mut errors = Vec::new();

			let abs_type = infer(&abs, context.clone());
			let abs_check = check(&abs, abs_type.clone(), context.clone());
			push_check(&mut errors, abs_check);

			match *abs_type.0 {
				FunctionTypeIntro(in_type, out_type) => {
					let arg_check = check(&arg, in_type, context.clone());
					push_check(&mut errors, arg_check);
				},
				_ => errors.push(Error::new(&term, ExpectedFunctionType { giv_type: abs_type }))
			}

			wrap_checks(errors)
		},
		PairTypeIntro(ref fst_type, ref snd_type) => {
			let mut errors = Vec::new();
			let normal_fst_type = normalize(fst_type.clone(), context.clone().inc_and_shift(2));
			let normal_snd_type = normalize(snd_type.clone(), context.clone().inc_and_shift(2));

			let fst_type_type = infer(&fst_type, context.clone());
			let fst_type_check = check(&fst_type, fst_type_type.clone(), context.clone().inc_and_shift(2).insert(1, normal_snd_type));

			let snd_type_type = infer(&snd_type, context.clone());
			let snd_type_check = check(&snd_type, snd_type_type.clone(), context.inc_and_shift(2).insert(0, normal_fst_type));

			push_check(&mut errors, fst_type_check);
			push_check(&mut errors, snd_type_check);

			match (*(fst_type_type.clone()).0, *(snd_type_type.clone()).0) {
				(UniverseIntro(fst_level), UniverseIntro(snd_level)) =>
					if let UniverseIntro(max_level) = *exp_type.clone().0 {
						if max(fst_level, snd_level) != max_level {
							errors.push(Error::new(
								&term,
								MismatchedTypes {
									exp_type: (Box::new(UniverseIntro(max_level)), Default::default()),
									giv_type: (Box::new(UniverseIntro(max(fst_level, snd_level))), Default::default())
								}));
						}
					} else {
						errors.push(Error::new(&term, ExpectedUniverse { giv_type: exp_type }))
					},
				(_, UniverseIntro(_)) => errors.push(Error::new(&fst_type, ExpectedUniverse { giv_type: fst_type_type })),
				(UniverseIntro(_), _) => errors.push(Error::new(&snd_type, ExpectedUniverse { giv_type: snd_type_type })),
				(_, _) =>  {
					errors.push(Error::new(&fst_type, ExpectedUniverse { giv_type: fst_type_type }));
					errors.push(Error::new(&snd_type, ExpectedUniverse { giv_type: snd_type_type }));
				}
			}

			wrap_checks(errors)
		},
		PairIntro(ref fst, ref snd) => {
			match *exp_type.0 {
				PairTypeIntro(fst_type, snd_type) => {
					let mut errors = Vec::new();
					let fst_check = check(&fst, fst_type.clone(), context.clone().inc_and_shift(2).insert(1, snd_type.clone()));
					let snd_check = check(&snd, snd_type, context.inc_and_shift(2).insert(0, fst_type));

					push_check(&mut errors, fst_check);
					push_check(&mut errors, snd_check);

					wrap_checks(errors)
				},
				_ => Err(vec![Error::new(&term, ExpectedPairType { giv_type: exp_type })])
			}
		},
		// PairElim(ref discrim, ref body) => {
		// 	let discrim_type = infer(&discrim, context.clone());
		// 	match discrim_type {
		// 		PairTypeIntro(fst_type, snd_type)
		// 	}
		// }
		_ => unimplemented!()
	}
}