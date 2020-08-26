#![allow(warnings)]

use super::{
	language::{
		*,
		InnerTerm::*
	},
	eval::*,
	context::*
};
use std::{
	default::*,
	cmp::max,
	collections::HashMap
};

// for the `Expected...` errors, imagine a universe `U` for each error, the error
// can then be thought of as `MismatchedTypes { exp_type: U, giv_type: ... }
pub enum InnerError<T> {
    MismatchedTypes { exp_type: Term<T>, giv_type: Term<T> },
    NonexistentVar(usize),
    ExpectedUniverse { giv_type: Term<T> },
    ExpectedFunctionType { giv_type: Term<T> },
    ExpectedPairType { giv_type: Term<T> },
    ExpectedEnumType { giv_type: Term<T> },
    ExpectedFoldType { giv_type: Term<T> },
    ExpectedUniqueType { giv_type: Term<T> },
    MismatchedUsage { var_index: usize, exp_usage: (usize, usize), giv_usage: (usize, usize) },
    UniqueTypeInSharedType,
    NonexaustiveEnumElim,
    ExpectedSharedUniverse
}

pub struct Error<'a, T> {
    term: &'a Term<T>,
    error: InnerError<T>
}

impl<'a, T> Error<'a, T> {
    pub fn new(term: &'a Term<T>, error: InnerError<T>) -> Error<'a, T> {
        Error {
            term,
            error
        }
    }
}

pub type CheckResult<'a, T, U> = Result<U, Vec<Error<'a, T>>>;

// fn flatten_errors<'a, T>(errors: Vec<Vec<Error<'a, T>>>) -> Vec<Error<'a, T>> {
// 	let mut new_errs = Vec::new();
// 	for mut column in errors {
// 		new_errs.append(&mut column);
// 	}
// 	new_errs
// }

pub fn push_check<'a, T, U>(errors: &mut Vec<Error<'a, T>>, this_check: CheckResult<'a, T, U>) { // appends errors to an error list, if there are any
	match this_check {
		Ok(_) => {},
		Err(errs) => {
			for err in errs {
				errors.push(err);
			}
		}
	}
}

pub fn is_terms_eq<T>(type1: &Term<T>, type2: &Term<T>) -> bool { // checks if two terms are equal, disregarding elab info
	match (&(*type1.0), &(*type2.0)) {
		(&Ann(ref annd_term1, ref type_ann1), &Ann(ref annd_term2, ref type_ann2)) =>
			is_terms_eq(&annd_term1, &annd_term2) && is_terms_eq(&type_ann1, &type_ann2),
		(&UniverseIntro(level1, usage1), &UniverseIntro(level2, usage2)) =>
			level1 == level2 && usage1 == usage2,
		(&Var(index1), &Var(index2)) =>
			index1 == index2,
		(&Rec(ref inner_term1), &Rec(ref inner_term2)) =>
			is_terms_eq(&inner_term1, &inner_term2),
		(&FunctionTypeIntro(ref in_type1, ref out_type1), &FunctionTypeIntro(ref in_type2, ref out_type2)) =>
			is_terms_eq(&in_type1, &in_type2) && is_terms_eq(&out_type1, out_type2),
		(&FunctionIntro(ref body1), &FunctionIntro(ref body2)) =>
			is_terms_eq(&body1, &body2),
		(&FunctionElim(ref abs1, ref arg1), &FunctionElim(ref abs2, ref arg2)) =>
			is_terms_eq(&abs1, &abs2) && is_terms_eq(&arg1, &arg2),
		(&PairTypeIntro(ref fst_type1, ref snd_type1), &PairTypeIntro(ref fst_type2, ref snd_type2)) =>
			is_terms_eq(&fst_type1, &snd_type1) && is_terms_eq(&fst_type2, &snd_type2),
		(&PairIntro(ref fst1, ref snd1), &PairIntro(ref fst2, ref snd2)) =>
			is_terms_eq(&fst1, &fst2) && is_terms_eq(&snd1, &snd2),
		(&PairElim(ref discrim1, ref body1), &PairElim(ref discrim2, ref body2)) =>
			is_terms_eq(&discrim1, &discrim2) && is_terms_eq(&body1, &body2),
		(&EnumTypeIntro(num_mems1), &EnumTypeIntro(num_mems2)) =>
			num_mems1 == num_mems2,
		(&EnumIntro(label1), &EnumIntro(label2)) =>
			label1 == label2,
		(&EnumElim(ref discrim1, ref branches1), &EnumElim(ref discrim2, ref branches2)) => {
			let discrims_eq = is_terms_eq(&discrim1, &discrim2);
			let mut branches_eq = true;

			if branches1.len() == branches2.len() {
				for i in 0..branches1.len() {
					if !is_terms_eq(&branches1[i], &branches2[i]) {
						branches_eq = false;
						break;
					}
				}
			} else {
				branches_eq = false;
			}

			discrims_eq && branches_eq
		},
		(&FoldTypeIntro(ref inner_type1), &FoldTypeIntro(ref inner_type2)) =>
			is_terms_eq(&inner_type1, &inner_type2),
		(&FoldIntro(ref inner_term1), &FoldIntro(ref inner_term2)) =>
			is_terms_eq(&inner_term1, &inner_term2),
		(&FoldElim(ref inner_term1), &FoldElim(ref inner_term2)) =>
			is_terms_eq(&inner_term1, &inner_term2),
		_ => false
	}
}

// can i make this more sophisticated?
pub fn count_uses<T>(term: &Term<T>, target_index: usize) -> (usize, usize) {
	fn collapse(intervals: Vec<(usize, usize)>) -> (usize, usize) {
		let mut min = std::usize::MAX;
		let mut max = 0;
		for (b1, b2) in intervals {
			if b1 < min { min = b1 }
			if b2 > max { max = b2 }
		}
		(min, max)
	}

	fn sum(intervals: Vec<(usize, usize)>) -> (usize, usize) {
		let mut min = 0;
		let mut max = 0;
		for (b1, b2) in intervals {
			min += b1;
			max += b2;
		}
		(min, max)
	}

	fn mul(intervals: Vec<(usize, usize)>) -> (usize, usize) {
		let mut min = 0;
		let mut max = 0;
		for (b1, b2) in intervals {
			min *= b1;
			max *= b2;
		}
		(min, max)
	}

	fn singleton(bound: usize) -> (usize, usize) { (bound, bound) }

	match *term.0 {
		Ann(ref annd_term, ref type_ann) =>
			// should uses in `type_ann` be counted or not?
			sum(vec![count_uses(annd_term, target_index), /*count_uses(type_ann, target_index)*/]),
		UniverseIntro(level, usage) => singleton(0),
		Var(index) => if index == target_index { singleton(1) } else { singleton(0) },
		Rec(ref inner_term) => count_uses(inner_term, target_index + 1),
		FunctionTypeIntro(ref in_type, ref out_type) =>
			sum(vec![
				mul(vec![
					count_uses(in_type, target_index),
					count_uses(out_type, 0)
				]),
				count_uses(out_type, target_index + 1)
			]),
		FunctionIntro(ref body) => singleton(0),
		FunctionElim(ref abs, ref arg) => unimplemented!(),
		PairTypeIntro(ref fst_type, ref snd_type) =>
			sum(vec![count_uses(fst_type, target_index + 1), count_uses(snd_type, target_index + 1)]),
		PairIntro(ref fst, ref snd) =>
			sum(vec![count_uses(fst, target_index), count_uses(snd, target_index)]),
		PairElim(ref discrim, ref body) =>
			sum(vec![count_uses(discrim, target_index), count_uses(body, target_index + 2)]),
		EnumTypeIntro(num_mems) => singleton(0),
		EnumIntro(label) => singleton(0),
		EnumElim(ref discrim, ref branches) =>
			sum(vec![
				collapse(branches.iter().map(|b| count_uses(b, target_index)).collect::<Vec<(usize, usize)>>()),
				count_uses(discrim, target_index)
			]),
		FoldTypeIntro(ref inner_type) => count_uses(inner_type, target_index),
		FoldIntro(ref inner_term) => count_uses(inner_term, target_index),
		FoldElim(ref folded_term) => count_uses(folded_term, target_index)
	}
}

pub fn wrap_checks<'a, T>(errors: Vec<Error<'a, T>>) -> CheckResult<'a, T, ()> {
	if errors.len() > 0 {
		Err(errors)
	} else {
		Ok(())
	}
}

pub fn check_usage<'a, T: Clone + Default + PartialEq>(binder: &'a Term<T>, term_type: Term<T>, body: &'a Term<T>, target_index: usize, context: Context<T>) -> CheckResult<'a, T, ()> {
	use InnerError::*;

	match term_type.usage(context.clone()) {
		Shared => Ok(()),
		Unique =>
			if count_uses(body, 0) == (1, 1) {
				Ok(())
			} else {
				Err(vec![Error::new(binder, MismatchedUsage { var_index: target_index, exp_usage: (1, 1), giv_usage: count_uses(body, 0) })])
			}
	}
}

// r#type should be checked with `check` before being checked with this
pub fn check_type<'a, T>(r#type: &'a Term<T>, context: Context<T>) -> CheckResult<'a, T, ()> {
	// panic!("`check_type` is not finished");

	// fn check_type_aux<'a, T>(r#type: &'a Term<T>, context: Context<T>, exp_shared: bool) -> CheckResult<'a, T, ()> {
	// 	let exp_usage =
	// 		match r#type.usage(context.clone()) {
	// 			Shared => true,
	// 			Unique => false
	// 		};

	// 	match *r#type.0 {
	// 		Ann(ref annd_term, ref type_ann) => {
	// 			let mut errors = Vec::new();
	// 			push_check(&mut errors, check_type_aux(type_ann, context.clone()));
	// 			push_check(&mut errors, check_type_aux(annd_term, context, exp_usage));
	// 			wrap_checks(errors)
	// 		},
	// 		// Rec(ref inner_term) => check_type_aux(inner_term, context, exp_usage),
	// 		FunctionTypeIntro(ref in_type, ref out_type) => {
	// 			let mut errors = Vec::new();
	// 			push_check(&mut errors, check_type_aux(in_type, context.clone()));
	// 			push_check(&mut errors, check_type_aux(out_type, context));
	// 			wrap_checks(errors)
	// 		},
	// 		FunctionIntro(ref body) => check_type_aux(body, context, exp_usage),
	// 		// FunctionElim(ref abs, ref arg) => {
	// 		// 	let errors = Vec::new();
	// 		// 	push_check(&mut errors, check_type_aux(abs,))
	// 		// }
	// 		PairTypeIntro(ref fst_type, ref snd_type) => {
	// 			let mut errors = Vec::new();
	// 			push_check(&mut errors, check_type_aux(fst_type, context.clone(), exp_usage));
	// 			push_check(&mut errors, check_type_aux(snd_type, context, exp_usage));
	// 			wrap_checks(errors)
	// 		},
	// 		FoldTypeIntro(ref inner_type) => check_type_aux(inner_type, context, exp_usage),
	// 		_ =>
	// 			match (r#type.usage(), exp_shared) {
	// 				(Shared, true) => Ok(()),
	// 				(Unique, true) => Err(vec![Error::new(r#type, ExpectedSharedUniverse)]),
	// 				(Shared, false) => Ok(()),
	// 				(Unique, false) => Ok(())
	// 			}
	// 	}
	// }

	// let mut errors = Vec::new();
	// push_check(&mut errors, check_type_aux(r#type, context, should_expect_shared(r#type)));
	// wrap_checks(errors)
	Ok(()) // until i figure out how this is supposed to work
}

// exp_type should always be checked and in normal form
pub fn check<'a, T: Clone + PartialEq + Default>(term: &'a Term<T>, exp_type: Term<T>, context: Context<T>) -> CheckResult<'a, T, ()> {
	use InnerError::*;

	match *term.0 {
		Ann(ref annd_term, ref type_ann) => {
			let mut errors = Vec::new();
			
			let type_ann_type = type_ann.r#type(context.clone())?;
			let normal_type_ann = normalize(type_ann.clone(), context.clone());

			push_check(&mut errors, check(type_ann, type_ann_type, context.clone()));
			push_check(&mut errors, check_type(type_ann, context.clone()));
			push_check(&mut errors, check(annd_term, normal_type_ann.clone(), context));
			push_check(
				&mut errors,
				if is_terms_eq(&normal_type_ann, &exp_type) {
					Ok(())
				} else {
					Err(vec![Error::new(term, MismatchedTypes { exp_type: exp_type.clone(), giv_type: normal_type_ann.clone() })])
				});

			wrap_checks(errors)
		},
		UniverseIntro(level, usage) =>
			match *(exp_type.clone()).0 {
				UniverseIntro(type_ann_level, type_ann_usage) =>
					if type_ann_level == level + 1 {
						Ok(())
					} else {
						Err(vec![Error::new(term, MismatchedTypes { exp_type: wrap(UniverseIntro(level + 1, type_ann_usage)), giv_type: exp_type.clone()})])
					}
				_ => Err(vec![Error::new(term, ExpectedUniverse { giv_type: exp_type })])
			},
		Var(index) =>
			match context.find(index) {
				Some(var_type) =>
					if is_terms_eq(&var_type, &exp_type) {
						Ok(())
					} else {
						Err(vec![Error::new(term, MismatchedTypes { exp_type, giv_type: var_type })])
					}
				None => Err(vec![Error::new(term, NonexistentVar(index))])
			},
		Rec(ref inner_term) => {
			let mut errors = Vec::new();

			let new_context = context.clone().inc_and_shift(1);
			let inner_term_type = inner_term.r#type(new_context.clone())?; // for now, all recursive functions must be type annotated

			push_check(
				&mut errors,
				check(inner_term, inner_term_type.clone(), new_context.insert(0, inner_term_type.clone())));
			push_check(&mut errors, check_usage(&term, inner_term_type, inner_term, 0, context.clone()));

			wrap_checks(errors)

		},
		FunctionTypeIntro(ref in_type, ref out_type) => {
			let mut errors = Vec::new();

			let normal_in_type = normalize(in_type.clone(), context.clone());
			let in_type_type = in_type.r#type(context.clone())?;
			let out_type_type = out_type.r#type(context.clone())?;
			push_check(
				&mut errors,
				check(in_type, in_type_type.clone(), context.clone()));
			push_check(
				&mut errors,
				check(out_type, out_type_type.clone(), context.clone().inc_and_shift(1).insert(0, normal_in_type.clone())));

			push_check(&mut errors, check_usage(&term, normal_in_type, &out_type, 0, context.clone()));

			match (*(in_type_type.clone()).0, *(out_type_type.clone()).0) {
				(UniverseIntro(in_level, in_usage), UniverseIntro(out_level, out_usage)) =>
					if let UniverseIntro(max_level, fn_usage) = *exp_type.clone().0 {
						if max(in_level, out_level) != max_level {
							errors.push(Error::new(
								term,
								MismatchedTypes {
									exp_type: wrap(UniverseIntro(max_level, fn_usage)),
									giv_type: wrap(UniverseIntro(max(in_level, out_level), fn_usage))
								}));
						}
					} else {
						errors.push(Error::new(term, ExpectedUniverse { giv_type: exp_type }))
					},
				(_, UniverseIntro(_, _)) => errors.push(Error::new(in_type, ExpectedUniverse { giv_type: in_type_type })),
				(UniverseIntro(_, _), _) => errors.push(Error::new(out_type, ExpectedUniverse { giv_type: out_type_type })),
				(_, _) =>  {
					errors.push(Error::new(in_type, ExpectedUniverse { giv_type: in_type_type }));
					errors.push(Error::new(out_type, ExpectedUniverse { giv_type: out_type_type }));
				}
			}

			wrap_checks(errors)
		},
		FunctionIntro(ref body) => {
			let mut errors = Vec::new();

			match *exp_type.0 {
				FunctionTypeIntro(in_type, out_type) => {
					push_check(&mut errors, check(body, out_type, Context::new().insert(0, in_type.clone())));
					push_check(&mut errors, check_usage(&term, in_type, &body, 0, context.clone()));
				},
				_ => errors.push(Error::new(term, ExpectedFunctionType { giv_type: exp_type }))
			}

			wrap_checks(errors)
		}
		FunctionElim(ref abs, ref arg) => {
			let mut errors = Vec::new();

			let abs_type = abs.r#type(context.clone())?;
			push_check(&mut errors, check(abs, abs_type.clone(), context.clone()));


			match *abs_type.0 {
				FunctionTypeIntro(in_type, out_type) => push_check(&mut errors, check(arg, in_type, context.clone())),
				_ => errors.push(Error::new(term, ExpectedFunctionType { giv_type: abs_type }))
			}

			wrap_checks(errors)
		},
		PairTypeIntro(ref fst_type, ref snd_type) => {
			let mut errors = Vec::new();

			let normal_fst_type = normalize(fst_type.clone(), context.clone().inc_and_shift(2));
			let normal_snd_type = normalize(snd_type.clone(), context.clone().inc_and_shift(2));

			let fst_type_type = fst_type.r#type(context.clone())?;
			push_check(
				&mut errors,
				check(fst_type, fst_type_type.clone(), context.clone().inc_and_shift(2).insert(1, normal_snd_type.clone())));

			let snd_type_type = snd_type.r#type(context.clone())?;
			push_check(
				&mut errors,
				check(snd_type, snd_type_type.clone(), context.clone().inc_and_shift(2).insert(0, normal_fst_type.clone())));

			push_check(&mut errors, check_usage(&term, normal_fst_type, snd_type, 0, context.clone()));
			push_check(&mut errors, check_usage(&term, normal_snd_type, fst_type, 1, context.clone()));

			match (*(fst_type_type.clone()).0, *(snd_type_type.clone()).0) {
				(UniverseIntro(fst_level, fst_usage), UniverseIntro(snd_level, snd_usage)) =>
					if let UniverseIntro(max_level, pair_usage) = *exp_type.clone().0 {
						if max(fst_level, snd_level) != max_level {
							errors.push(Error::new(
								term,
								MismatchedTypes {
									exp_type: wrap(UniverseIntro(max_level, pair_usage)),
									giv_type: wrap(UniverseIntro(max(fst_level, snd_level), pair_usage))
								}));
						}
					} else {
						errors.push(Error::new(term, ExpectedUniverse { giv_type: exp_type }))
					},
				(_, UniverseIntro(_, _)) => errors.push(Error::new(fst_type, ExpectedUniverse { giv_type: fst_type_type })),
				(UniverseIntro(_, _), _) => errors.push(Error::new(snd_type, ExpectedUniverse { giv_type: snd_type_type })),
				(_, _) =>  {
					errors.push(Error::new(fst_type, ExpectedUniverse { giv_type: fst_type_type }));
					errors.push(Error::new(snd_type, ExpectedUniverse { giv_type: snd_type_type }));
				}
			}

			wrap_checks(errors)
		},
		PairIntro(ref fst, ref snd) => {
			match *exp_type.0 {
				PairTypeIntro(fst_type, snd_type) => {
					let mut errors = Vec::new();
					let fst_check = check(fst, fst_type.clone(), context.clone().inc_and_shift(2).insert(1, snd_type.clone()));
					let snd_check = check(snd, snd_type, context.inc_and_shift(2).insert(0, fst_type));

					push_check(&mut errors, fst_check);
					push_check(&mut errors, snd_check);

					wrap_checks(errors)
				},
				_ => Err(vec![Error::new(term, ExpectedPairType { giv_type: exp_type })])
			}
		},
		PairElim(ref discrim, ref body) => {
			let mut errors = Vec::new();

			let discrim_type = discrim.r#type(context.clone())?;
			push_check(&mut errors, check(discrim, discrim_type.clone(), context.clone()));

			match *(discrim_type.clone()).0 {
				PairTypeIntro(fst_type, snd_type) => {
					let body_context = context.clone().inc_and_shift(2).insert(0, fst_type.clone()).insert(1, snd_type.clone());
					let body_type = body.r#type(body_context.clone())?;
					push_check(&mut errors, check(body, body_type, body_context));
					
					push_check(&mut errors, check_usage(&term, fst_type.clone(), body, 0, context.clone()));
					push_check(&mut errors, check_usage(&term, snd_type.clone(), body, 1, context.clone()));
				}
				_ => errors.push(Error::new(discrim, ExpectedPairType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		},
		EnumTypeIntro(num_mems) =>
			match *(exp_type.clone()).0 {
				UniverseIntro(_, _) => Ok(()),
				_ => Err(vec![Error::new(term, ExpectedUniverse { giv_type: exp_type.clone() })])
			},
		EnumIntro(label) =>
			match *(exp_type.clone()).0 {
				EnumTypeIntro(num_mems) => if label < num_mems { Ok(()) } else { unimplemented!() }
				_ => Err(vec![Error::new(term, ExpectedEnumType { giv_type: exp_type.clone() })])
			},
		EnumElim(ref discrim, ref branches) => {
			let mut errors = Vec::new();

			let discrim_type = discrim.r#type(context.clone())?;
			push_check(&mut errors, check(discrim, discrim_type.clone(), context.clone()));

			match *(discrim_type.clone()).0 {
				EnumTypeIntro(num_mems) => {
					push_check( // exaustiveness check
						&mut errors,
						if branches.len() == num_mems {
							Ok(())
						} else {
							Err(vec![Error::new(term, NonexaustiveEnumElim)])
						});

					for i in 0..branches.len() { // branch : exp_type check
						let branch_context =
							match *discrim.0 { // updates context with the now known value of discrim if it is a var
								Var(index) => context.clone().update(index, wrap(EnumIntro(i))),
								_ => context.clone()
							};

						push_check(&mut errors, check(&branches[i], exp_type.clone(), branch_context));
					}
				},
				_ => errors.push(Error::new(discrim, ExpectedEnumType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		},
		FoldTypeIntro(ref inner_type) =>
			match *(exp_type.clone()).0 {
				UniverseIntro(_, _) => Ok(()),
				_ => Err(vec![Error::new(term, ExpectedUniverse { giv_type: exp_type.clone() })])
			},
		FoldIntro(ref inner_term) =>
			match *(exp_type.clone()).0 {
				FoldTypeIntro(inner_type) => check(inner_term, normalize(inner_type, context.clone()), context),
				_ => Err(vec![Error::new(term, ExpectedFoldType { giv_type: exp_type.clone() })])
			},
		FoldElim(ref folded_term) => {
			let mut errors = Vec::new();
			let folded_term_type = folded_term.r#type(context)?;

			push_check(
				&mut errors,
				if is_terms_eq(&folded_term_type, &exp_type) {
					Ok(())
				} else {
					Err(vec![Error::new(term, MismatchedTypes { exp_type: exp_type.clone(), giv_type: folded_term_type.clone() })])
				});

			wrap_checks(errors)
		}
	}
}