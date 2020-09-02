#![allow(warnings)]

use super::{
	language::{
		*,
		InnerTerm::*,
		List::*
	},
	eval::*,
	context::*
};
use std::{
	default::*,
	cmp::max,
	collections::{
		HashMap,
		HashSet
	},
	fmt::Debug,
	hash::Hash
};

// for the `Expected...` errors, imagine a universe `U` for each error, the error
// can then be thought of as `MismatchedTypes { exp_type: U, giv_type: ... }
#[derive(Debug)]
pub enum InnerError<T> {
    MismatchedTypes { exp_type: Term<T>, giv_type: Term<T> },
    NonexistentVar { index: usize },
    ExpectedOfUniverse { min_level: usize, giv_type: Term<T> },
    ExpectedOfFunctionType { giv_type: Term<T> },
    ExpectedOfPairType { giv_type: Term<T> },
    ExpectedOfEnumType { giv_type: Term<T> },
    ExpectedOfFoldType { giv_type: Term<T> },
    ExpectedOfCapturesListType { min_level: usize, giv_type: Term<T> },
    ExpectedOfUniqueType { giv_type: Term<T> },
    MismatchedUsage { var_index: usize, exp_usage: (usize, usize), giv_usage: (usize, usize) },
    UniqueTypeInSharedType,
    NonexaustiveEnumElim,
    ExpectedOfSharedUniverse,
    EnumTypeTooSmall { giv_num_mems: usize, needed_num_mems: usize },
    UnmentionedFreeVars { caps_list: Vec<Term<T>>, unmentioned_vars: Vec<Term<T>> }
}

#[derive(Debug)]
pub struct Error<'a, T> {
    term: &'a Term<T>,
    context: Context<T>,
    error: InnerError<T>
}

impl<'a, T> Error<'a, T> {
    pub fn new(term: &'a Term<T>, context: Context<T>, error: InnerError<T>) -> Error<'a, T> {
        Error {
            term,
            context,
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
		Ok(_) => (),
		Err(errs) => {
			for err in errs {
				errors.push(err);
			}
		}
	}
}

// checks if two terms are equal, disregarding elab info
pub fn is_terms_eq<T>(type1: &Term<T>, type2: &Term<T>) -> bool {
	match (&(*type1.0), &(*type2.0)) {
		(&Ann(ref annd_term1, ref type_ann1), &Ann(ref annd_term2, ref type_ann2)) =>
			is_terms_eq(annd_term1, annd_term2) && is_terms_eq(type_ann1, type_ann2),
		(&UniverseIntro(level1, usage1), &UniverseIntro(level2, usage2)) =>
			level1 == level2 && usage1 == usage2,
		(&Var(index1), &Var(index2)) =>
			index1 == index2,
		(&Rec(ref inner_term1), &Rec(ref inner_term2)) =>
			is_terms_eq(inner_term1, inner_term2),
		(&FunctionTypeIntro(ref caps_list1, ref in_type1, ref out_type1), &FunctionTypeIntro(ref caps_list2, ref in_type2, ref out_type2)) =>
			is_terms_eq(caps_list1, caps_list2) && is_terms_eq(in_type1, in_type2) && is_terms_eq(out_type1, out_type2),
		(&FunctionIntro(ref body1), &FunctionIntro(ref body2)) =>
			is_terms_eq(body1, body2),
		(&FunctionElim(ref abs1, ref arg1), &FunctionElim(ref abs2, ref arg2)) =>
			is_terms_eq(abs1, abs2) && is_terms_eq(arg1, arg2),
		(&PairTypeIntro(ref fst_type1, ref snd_type1), &PairTypeIntro(ref fst_type2, ref snd_type2)) =>
			is_terms_eq(fst_type1, snd_type1) && is_terms_eq(fst_type2, snd_type2),
		(&PairIntro(ref fst1, ref snd1), &PairIntro(ref fst2, ref snd2)) =>
			is_terms_eq(fst1, fst2) && is_terms_eq(snd1, snd2),
		(&PairElim(ref discrim1, ref body1), &PairElim(ref discrim2, ref body2)) =>
			is_terms_eq(discrim1, discrim2) && is_terms_eq(body1, body2),
		(&EnumTypeIntro(num_mems1), &EnumTypeIntro(num_mems2)) =>
			num_mems1 == num_mems2,
		(&EnumIntro(label1), &EnumIntro(label2)) =>
			label1 == label2,
		(&EnumElim(ref discrim1, ref branches1), &EnumElim(ref discrim2, ref branches2)) => {
			let discrims_eq = is_terms_eq(discrim1, discrim2);
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
			is_terms_eq(inner_type1, inner_type2),
		(&FoldIntro(ref inner_term1), &FoldIntro(ref inner_term2)) =>
			is_terms_eq(inner_term1, inner_term2),
		(&FoldElim(ref inner_term1), &FoldElim(ref inner_term2)) =>
			is_terms_eq(inner_term1, inner_term2),
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
		Ann(ref annd_term, ref type_ann) => count_uses(annd_term, target_index),
		UniverseIntro(level, usage) => singleton(0),
		Var(index) => if index == target_index { singleton(1) } else { singleton(0) },
		Rec(ref inner_term) => count_uses(inner_term, target_index + 1),
		FunctionTypeIntro(ref caps_list, ref in_type, ref out_type) =>
			sum(vec![
				count_uses(caps_list, target_index),
				mul(vec![
					count_uses(in_type, target_index),
					count_uses(out_type, 0)
				]),
				count_uses(out_type, target_index + 1)
			]),
		FunctionIntro(ref body) => count_uses(body, target_index + 1),
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
		FoldElim(ref folded_term) => count_uses(folded_term, target_index),
		CapturesListTypeIntro(_) => singleton(0),
		CapturesListIntro(ref list) =>
			match list {
				Cons(ref head, ref tail) =>
					sum(vec![
						count_uses(head, target_index),
						count_uses(tail, target_index)
					]),
				Nil => singleton(0)
			}
	}
}

// `term` should be checked before this is called
// should make this more robust in the future
fn get_free_vars<T: Clone + Default + Debug + Hash + Eq>(term: &Term<T>) -> HashSet<(usize, Term<T>)> {
	type Set<T> = HashSet<(usize, Term<T>)>;

	fn inner<T: Hash + Eq + Clone>(term: &Term<T>, bounds: HashSet<usize>) -> Set<T> {
		fn collapse<T: Hash + Eq + Clone>(sets: Vec<Set<T>>) -> Set<T> {
			let mut new_set: Set<T> = HashSet::new();
			for set in sets {
				new_set = new_set.r#union(&set).cloned().collect::<Set<T>>();
			}
			new_set
		}

		fn inc<T: Hash + Eq>(set: HashSet<usize>) -> HashSet<usize> {
			let mut tmp = set.into_iter().map(|i| i + 1).collect::<HashSet<usize>>();
			tmp.insert(0);
			tmp
		}

		match *term.0 {
			Ann(ref annd_term, ref type_ann) =>
				match *annd_term.0 {
					Var(index) => 
						if bounds.contains(&index) {
							HashSet::new()
						} else {
							let mut tmp: Set<T> = HashSet::new();
							tmp.insert((index - bounds.len(), type_ann.clone()));
							tmp
						},
					_ =>
						collapse(vec![
							inner(annd_term, bounds.clone()),
							inner(type_ann, bounds)
						])
				},
			UniverseIntro(_, _) => HashSet::new(),
			Var(index) => panic!(),
			Rec(ref inner_term) => inner(inner_term, inc::<T>(bounds)),
			FunctionTypeIntro(ref caps_list, ref in_type, ref out_type) =>
				collapse(vec![
					inner(caps_list, bounds.clone()),
					inner(in_type, bounds.clone()),
					inner(out_type, inc::<T>(bounds))
				]),
			FunctionIntro(ref body) => inner(body, inc::<T>(bounds)),
			FunctionElim(ref abs, ref arg) =>
				collapse(vec![
					inner(abs, bounds.clone()),
					inner(arg, bounds)
				]),
			PairTypeIntro(ref fst_type, ref snd_type) =>
				collapse(vec![
					inner(fst_type, inc::<T>(bounds.clone())),
					inner(snd_type, inc::<T>(bounds))
				]),
			PairIntro(ref fst, ref snd) =>
				collapse(vec![
					inner(fst, bounds.clone()),
					inner(snd, bounds)
				]),
			PairElim(ref discrim, ref body) =>
				collapse(vec![
					inner(discrim, bounds.clone()),
					inner(body, inc::<T>(bounds))
				]),
			EnumTypeIntro(_) => HashSet::new(),
			EnumIntro(_) => HashSet::new(),
			EnumElim(ref discrim, ref branches) =>
				collapse(vec![
					collapse(branches.iter().map(|b| inner(b, bounds.clone())).collect()),
					inner(discrim, bounds)
				]),
			FoldTypeIntro(ref inner_type) => inner(inner_type, bounds),
			FoldIntro(ref inner_term) => inner(inner_term, bounds),
			FoldElim(ref folded_term) => inner(folded_term, bounds),
			CapturesListTypeIntro(_) => HashSet::new(),
			CapturesListIntro(ref list) =>
				match list {
					Cons(ref head, ref tail) =>
						collapse(vec![
							inner(head, bounds.clone()),
							inner(tail, bounds)
						]),
					Nil => HashSet::new()
				}
		}
	}

	inner(term, HashSet::new())
}

pub fn wrap_checks<'a, T>(errors: Vec<Error<'a, T>>) -> CheckResult<'a, T, ()> {
	if errors.len() > 0 {
		Err(errors)
	} else {
		Ok(())
	}
}

pub fn check_usage<'a, T: Clone + Default + PartialEq + Debug + Hash + Eq>(binder: &'a Term<T>, term_type: Term<T>, body: &'a Term<T>, target_index: usize, context: Context<T>) -> CheckResult<'a, T, ()> {
	use InnerError::*;

	match term_type.usage(context.clone()) {
		Shared => Ok(()),
		Unique =>
			if count_uses(body, 0) == (1, 1) {
				Ok(())
			} else {
				Err(vec![Error::new(binder, context, MismatchedUsage { var_index: target_index, exp_usage: (1, 1), giv_usage: count_uses(body, 0) })])
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
pub fn check<'a, T>(term: &'a Term<T>, exp_type: Term<T>, context: Context<T>) -> CheckResult<'a, T, ()> 
	where T: Clone + PartialEq + Default + Debug + Hash + Eq {
	use InnerError::*;

	match *term.0 {
		Ann(ref annd_term, ref type_ann) => {
			let mut errors = Vec::new();
			
			let type_ann_type = type_ann.r#type(context.clone())?;
			let normal_type_ann = normalize(type_ann.clone(), Context::new());

			push_check(&mut errors, check(type_ann, type_ann_type, context.clone()));
			push_check(&mut errors, check_type(type_ann, context.clone()));
			push_check(&mut errors, check(annd_term, normal_type_ann.clone(), context.clone()));
			push_check(
				&mut errors,
				if is_terms_eq(&normal_type_ann, &exp_type) {
					Ok(())
				} else {
					Err(vec![Error::new(term, context, MismatchedTypes { exp_type: exp_type.clone(), giv_type: normal_type_ann.clone() })])
				});

			wrap_checks(errors)
		},
		UniverseIntro(level, usage) =>
			match *(exp_type.clone()).0 {
				UniverseIntro(type_ann_level, type_ann_usage) =>
					if type_ann_level > level {
						Ok(())
					} else {
						Err(vec![Error::new(term, context, ExpectedOfUniverse { min_level: level + 1, giv_type: exp_type })])
					}
				_ => Err(vec![Error::new(term, context, ExpectedOfUniverse { min_level: level + 1, giv_type: exp_type })])
			},
		Var(index) =>
			match context.find(index) {
				Some(var_type) =>
					if is_terms_eq(&var_type, &exp_type) {
						Ok(())
					} else {
						Err(vec![Error::new(term, context, MismatchedTypes { exp_type, giv_type: var_type })])
					}
				None => Err(vec![Error::new(term, context, NonexistentVar { index })])
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
		FunctionTypeIntro(ref caps_list, ref in_type, ref out_type) => {
			let mut errors = Vec::new();

			let out_type_context = context.clone().inc_and_shift(1).insert(0, in_type.clone());

			let caps_list_type = caps_list.r#type(context.clone())?;
			let in_type_type = in_type.r#type(context.clone())?;
			let out_type_type = out_type.r#type(out_type_context.clone())?;
			push_check(
				&mut errors,
				check(caps_list, caps_list_type.clone(), context.clone()));
			push_check(
				&mut errors,
				check(in_type, in_type_type.clone(), context.clone()));
			push_check(
				&mut errors,
				check(out_type, out_type_type.clone(), out_type_context));

			push_check(&mut errors, check_usage(&term, in_type.clone(), &out_type, 0, context.clone().inc_and_shift(1).clone()));

			match (*(caps_list_type.clone()).0, *(in_type_type.clone()).0, *(out_type_type.clone()).0) {
				(CapturesListTypeIntro(caps_list_level), UniverseIntro(in_level, in_usage), UniverseIntro(out_level, out_usage)) => {
					let giv_max = max(caps_list_level, max(in_level, out_level));
					if let UniverseIntro(max_level, fn_usage) = *exp_type.clone().0 {
						if giv_max != max_level {
							errors.push(Error::new(
								term,
								context,
								MismatchedTypes {
									exp_type: wrap(UniverseIntro(max_level, fn_usage)),
									giv_type: wrap(UniverseIntro(giv_max, fn_usage))
								}));
						}
					} else {
						errors.push(Error::new(term, context, ExpectedOfUniverse { min_level: giv_max, giv_type: exp_type }))
					}
				},
				(_, _, UniverseIntro(level, _)) => {
					errors.push(Error::new(in_type, context.clone(), ExpectedOfUniverse { min_level: level, giv_type: in_type_type }));
					errors.push(Error::new(caps_list, context, ExpectedOfCapturesListType { min_level: level, giv_type: caps_list_type }));
				}
				(_, UniverseIntro(level, _), _) => {
					errors.push(Error::new(out_type, context.clone(), ExpectedOfUniverse { min_level: level, giv_type: out_type_type }));
					errors.push(Error::new(caps_list, context, ExpectedOfCapturesListType { min_level: level, giv_type: caps_list_type }));
				}
				(_, _, _) =>  {
					errors.push(Error::new(in_type, context.clone(), ExpectedOfUniverse { min_level: 0, giv_type: in_type_type }));
					errors.push(Error::new(out_type, context.clone(), ExpectedOfUniverse { min_level: 0, giv_type: out_type_type }));
					errors.push(Error::new(caps_list, context, ExpectedOfCapturesListType { min_level: 0, giv_type: caps_list_type }));
				},
				(CapturesListTypeIntro(level1), _, UniverseIntro(level2, _)) =>
					errors.push(Error::new(in_type, context, ExpectedOfUniverse { min_level: max(level1, level2), giv_type: in_type_type })),
				(CapturesListTypeIntro(level1), UniverseIntro(level2, _), _) =>
					errors.push(Error::new(out_type, context, ExpectedOfUniverse { min_level: max(level1, level2), giv_type: out_type_type })),
				(CapturesListTypeIntro(level1), _, _) =>  {
					errors.push(Error::new(in_type, context.clone(), ExpectedOfUniverse { min_level: level1, giv_type: in_type_type }));
					errors.push(Error::new(out_type, context, ExpectedOfUniverse { min_level: level1, giv_type: out_type_type }));
				}
			}

			wrap_checks(errors)
		},
		FunctionIntro(ref body) => {
			let mut errors = Vec::new();

			match *exp_type.0 {
				FunctionTypeIntro(caps_list, in_type, out_type) => {
					let body_context = context.clone().inc_and_shift(1).insert(0, shift(in_type.clone(), HashSet::new(), 1));
					push_check(&mut errors, check(body, out_type, body_context));
					push_check(&mut errors, check_usage(term, in_type, body, 0, context.clone().inc_and_shift(1)));

					fn flatten_caps_list<T: Clone>(caps_list: &Term<T>) -> Vec<Term<T>> {
						fn inner<T: Clone>(caps_list: &Term<T>, acc: &mut Vec<Term<T>>) {
							match *caps_list.0 {
								CapturesListIntro(ref list) => 
									match list {
										Cons(ref head, ref tail) => {
											acc.push(head.clone());
											inner(tail, acc);
										},
										Nil => ()
									},
								_ => ()
							}
						}

						let mut vec = Vec::new();
						inner(caps_list, &mut vec);
						vec
					}
					let capd_var_types = flatten_caps_list(&caps_list);
					let free_var_types = get_free_vars(body).into_iter().map(|(_, t)| t).collect::<HashSet<Term<T>>>();

					// find the captured vars that are not mentioned in the captures list, if any
					let mut leftover_vars = Vec::new();
					let mut used = HashSet::new();
					'top: for free_var_type in free_var_types {
						for (i, capd_var_type) in capd_var_types.iter().enumerate() {
							if !used.contains(&i) {
								if *capd_var_type == free_var_type {
									used.insert(i);
									continue 'top;
								}
							}
						}
						leftover_vars.push(free_var_type);
					}

					if leftover_vars.len() > 0 {
						errors.push(Error::new(term, context, UnmentionedFreeVars { caps_list: capd_var_types, unmentioned_vars: leftover_vars }))
					}
				},
				_ => errors.push(Error::new(term, context, ExpectedOfFunctionType { giv_type: exp_type }))
			}

			wrap_checks(errors)
		}
		FunctionElim(ref abs, ref arg) => {
			let mut errors = Vec::new();

			let abs_type = abs.r#type(context.clone())?;
			push_check(&mut errors, check(abs, abs_type.clone(), context.clone()));


			match *abs_type.0 {
				FunctionTypeIntro(caps_list, in_type, out_type) => push_check(&mut errors, check(arg, in_type, context.clone())),
				_ => errors.push(Error::new(term, context, ExpectedOfFunctionType { giv_type: abs_type }))
			}

			wrap_checks(errors)
		},
		PairTypeIntro(ref fst_type, ref snd_type) => {
			let mut errors = Vec::new();

			let fst_type_type = fst_type.r#type(context.clone())?;
			push_check(
				&mut errors,
				check(fst_type, fst_type_type.clone(), context.clone().inc_and_shift(2).insert(1, snd_type.clone())));

			let snd_type_type = snd_type.r#type(context.clone())?;
			push_check(
				&mut errors,
				check(snd_type, snd_type_type.clone(), context.clone().inc_and_shift(2).insert(0, fst_type.clone())));

			push_check(&mut errors, check_usage(&term, fst_type.clone(), snd_type, 0, context.clone()));
			push_check(&mut errors, check_usage(&term, snd_type.clone(), fst_type, 1, context.clone()));

			match (*(fst_type_type.clone()).0, *(snd_type_type.clone()).0) {
				(UniverseIntro(fst_level, fst_usage), UniverseIntro(snd_level, snd_usage)) =>
					if let UniverseIntro(max_level, pair_usage) = *exp_type.clone().0 {
						if max(fst_level, snd_level) != max_level {
							errors.push(Error::new(
								term,
								context,
								MismatchedTypes {
									exp_type: wrap(UniverseIntro(max_level, pair_usage)),
									giv_type: wrap(UniverseIntro(max(fst_level, snd_level), pair_usage))
								}));
						}
					} else {
						errors.push(Error::new(term, context, ExpectedOfUniverse { min_level: max(fst_level, snd_level), giv_type: exp_type }))
					},
				(_, UniverseIntro(level, _)) => errors.push(Error::new(fst_type, context, ExpectedOfUniverse { min_level: level, giv_type: fst_type_type })),
				(UniverseIntro(level, _), _) => errors.push(Error::new(snd_type, context, ExpectedOfUniverse { min_level: level, giv_type: snd_type_type })),
				(_, _) =>  {
					errors.push(Error::new(fst_type, context.clone(), ExpectedOfUniverse { min_level: 0, giv_type: fst_type_type }));
					errors.push(Error::new(snd_type, context, ExpectedOfUniverse { min_level: 0, giv_type: snd_type_type }));
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
				_ => Err(vec![Error::new(term, context, ExpectedOfPairType { giv_type: exp_type })])
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
				_ => errors.push(Error::new(discrim, context, ExpectedOfPairType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		},
		EnumTypeIntro(num_mems) =>
			match *(exp_type.clone()).0 {
				UniverseIntro(_, _) => Ok(()),
				_ => Err(vec![Error::new(term, context, ExpectedOfUniverse { min_level: 0, giv_type: exp_type.clone() })])
			},
		EnumIntro(label) =>
			match *(exp_type.clone()).0 {
				EnumTypeIntro(num_mems) => if label < num_mems { Ok(()) } else { Err(vec![Error::new(term, context, EnumTypeTooSmall { giv_num_mems: num_mems, needed_num_mems: label + 1 })]) }
				_ => Err(vec![Error::new(term, context, ExpectedOfEnumType { giv_type: exp_type.clone() })])
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
							Err(vec![Error::new(term, context.clone(), NonexaustiveEnumElim)])
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
				_ => errors.push(Error::new(discrim, context, ExpectedOfEnumType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		},
		FoldTypeIntro(ref inner_type) =>
			match *(exp_type.clone()).0 {
				UniverseIntro(_, _) => {
					let mut errors = Vec::new();
					push_check(&mut errors, check(inner_type, inner_type.r#type(context.clone())?, context.clone()));
					push_check(&mut errors, check_type(inner_type, context.clone()));
					wrap_checks(errors)
				},
				_ => Err(vec![Error::new(term, context, ExpectedOfUniverse { min_level: 0, giv_type: exp_type.clone() })])
			},
		FoldIntro(ref inner_term) =>
			match *(exp_type.clone()).0 {
				FoldTypeIntro(inner_type) => check(inner_term, inner_type, context),
				_ => Err(vec![Error::new(term, context, ExpectedOfFoldType { giv_type: exp_type.clone() })])
			},
		FoldElim(ref folded_term) => {
			let mut errors = Vec::new();
			let folded_term_type = folded_term.r#type(context.clone())?;

			push_check(
				&mut errors,
				if is_terms_eq(&folded_term_type, &exp_type) {
					Ok(())
				} else {
					Err(vec![Error::new(term, context, MismatchedTypes { exp_type: exp_type.clone(), giv_type: folded_term_type.clone() })])
				});

			wrap_checks(errors)
		},
		CapturesListTypeIntro(level) =>
			match *exp_type.clone().0 {
				UniverseIntro(u_level, _) =>
					if u_level > level {
						Ok(())
					} else {
						Err(vec![Error::new(term, context, ExpectedOfUniverse { min_level: level + 1, giv_type: exp_type })])
					}
				_ => Err(vec![Error::new(term, context, ExpectedOfUniverse { min_level: 1, giv_type: exp_type })])
			}
		CapturesListIntro(ref list) =>
			match *exp_type.0 {
				CapturesListTypeIntro(level) =>
					match list {
						Cons(ref head, ref tail) => {
							let mut errors = Vec::new();

							let head_type = head.r#type(context.clone())?;
							let tail_type = head.r#type(context.clone())?;

							match (*head_type.clone().0, *tail_type.clone().0) {
								(UniverseIntro(_, head_usage), CapturesListTypeIntro(_)) => {
									push_check(&mut errors, check(head, wrap(UniverseIntro(level, head_usage)), context.clone()));
									push_check(&mut errors, check_type(head, context.clone()));
									push_check(&mut errors, check(tail, wrap(CapturesListTypeIntro(level)), context));
								}
								(UniverseIntro(level, _), _) => errors.push(Error::new(head, context, ExpectedOfCapturesListType { min_level: level, giv_type: head_type })),
								(_, CapturesListTypeIntro(level)) => errors.push(Error::new(tail, context, ExpectedOfUniverse { min_level: level, giv_type: tail_type })),
								(_, _) => {
									errors.push(Error::new(head, context.clone(), ExpectedOfUniverse { min_level: 0, giv_type: head_type }));
									errors.push(Error::new(tail, context, ExpectedOfCapturesListType { min_level: 0, giv_type: tail_type }));
								}
							}

							wrap_checks(errors)
						},
						Nil => Ok(())
					}
				_ => Err(vec![Error::new(term, context, ExpectedOfCapturesListType { min_level: 0, giv_type: exp_type })])
			}
	}
}