#![allow(warnings)]

use super::{
	lang::{
		*,
		InnerTerm::*,
		List::*,
		Usage::*
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

// for the `Expected...` errors, imagine a TypeType `U` for each error, the error
// can then be thought of as `MismatchedTypes { exp_type: U, giv_type: ... }
#[derive(Debug)]
pub enum InnerError {
    MismatchedTypes { exp_type: Term, giv_type: Term },
    NonexistentVar { index: usize },
    ExpectedOfTypeType { min_level: usize, giv_type: Term },
    ExpectedOfFunctionType { giv_type: Term },
    ExpectedOfPairType { giv_type: Term },
    ExpectedOfEnumType { giv_type: Term },
    ExpectedOfFoldType { giv_type: Term },
    ExpectedOfCapturesListType { min_level: usize, giv_type: Term },
    ExpectedOfUnitType { giv_type: Term },
    MismatchedUsage { var_index: usize, exp_usage: (usize, usize), giv_usage: (usize, usize) },
    UniqueTypeInSharedType,
    ExpectedOfSharedTypeType,
    UnmentionedFreeVars { caps_list: Vec<Term>, unmentioned_vars: Vec<Term> }
}

#[derive(Debug)]
pub struct Error<'a> {
    term: &'a Term,
    context: Context,
    error: InnerError
}

impl<'a> Error<'a> {
    pub fn new(term: &'a Term, context: Context, error: InnerError) -> Error<'a> {
        Error {
            term,
            context,
            error
        }
    }
}

pub type CheckResult<'a, U> = Result<U, Vec<Error<'a>>>;

pub fn push_check<'a, U>(errors: &mut Vec<Error<'a>>, this_check: CheckResult<'a, U>) { // appends errors to an error list, if there are any
	match this_check {
		Ok(_) => (),
		Err(errs) => {
			for err in errs {
				errors.push(err);
			}
		}
	}
}

pub fn count_uses(term: &Term, target_index: usize) -> (usize, usize) {
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

	sum(vec![
		match *term.data {
			TypeTypeIntro(level, usage) => singleton(0),
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
			VoidTypeIntro => singleton(0),
			UnitTypeIntro => singleton(0),
			UnitIntro => singleton(0),
			DoubTypeIntro => singleton(0),
			DoubIntro(_) => singleton(0),
			DoubElim(ref discrim, ref branch1, ref branch2) =>
				sum(vec![
					count_uses(branch1, target_index),
					count_uses(branch2, target_index),
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
		},
		count_uses(&term.r#type(), target_index)])
}

pub fn level_of<'a>(r#type: &'a Term, context: Context) -> CheckResult<'a, usize> {
	use InnerError::*;

	let r#type_type = synth_type(r#type, context)?;
	match *r#type_type.data {
		TypeTypeIntro(level, _) => Ok(level),
		_ => Err(vec![Error::new(r#type, context.clone(), ExpectedOfTypeType { min_level: 1, giv_type: r#type_type })])
	}
}

// `term` should be checked before this is called
// should make this more robust in the future
fn get_free_vars(term: &Term) -> HashSet<(usize, Term)> {
	type Set = HashSet<(usize, Term)>;

	fn inner(term: &Term, bounds: HashSet<usize>) -> Set {
		fn collapse(sets: Vec<Set>) -> Set {
			let mut new_set: Set = HashSet::new();
			for set in sets {
				new_set = new_set.r#union(&set).cloned().collect::<Set>();
			}
			new_set
		}

		fn inc(set: HashSet<usize>) -> HashSet<usize> {
			let mut tmp = set.into_iter().map(|i| i + 1).collect::<HashSet<usize>>();
			tmp.insert(0);
			tmp
		}

		let type_ann_free_vars = inner(&term.r#type(), bounds.clone());
		collapse(vec![
			match *term.data {
				TypeTypeIntro(_, _) => HashSet::new(),
				Var(index) => panic!(),
				Rec(ref inner_term) => inner(inner_term, inc(bounds.clone())),
				FunctionTypeIntro(ref caps_list, ref in_type, ref out_type) =>
					collapse(vec![
						inner(caps_list, bounds.clone()),
						inner(in_type, bounds.clone()),
						inner(out_type, inc(bounds))
					]),
				FunctionIntro(ref body) => inner(body, inc(bounds)),
				FunctionElim(ref abs, ref arg) =>
					collapse(vec![
						inner(abs, bounds.clone()),
						inner(arg, bounds)
					]),
				PairTypeIntro(ref fst_type, ref snd_type) =>
					collapse(vec![
						inner(fst_type, inc(bounds.clone())),
						inner(snd_type, inc(bounds))
					]),
				PairIntro(ref fst, ref snd) =>
					collapse(vec![
						inner(fst, bounds.clone()),
						inner(snd, bounds)
					]),
				PairElim(ref discrim, ref body) =>
					collapse(vec![
						inner(discrim, bounds.clone()),
						inner(body, inc(bounds))
					]),
				VoidTypeIntro => HashSet::new(),
				UnitTypeIntro => HashSet::new(),
				UnitIntro => HashSet::new(),
				DoubTypeIntro => HashSet::new(),
				DoubIntro(_) => HashSet::new(),
				DoubElim(ref discrim, ref branch1, ref branch2) =>
					collapse(vec![
						inner(branch1, bounds.clone()),
						inner(branch2, bounds.clone()),
						inner(discrim, bounds)
					]),
				FoldTypeIntro(ref inner_type) => inner(inner_type, bounds.clone()),
				FoldIntro(ref inner_term) => inner(inner_term, bounds.clone()),
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
			},
			type_ann_free_vars])
	}

	inner(term, HashSet::new())
}

pub fn wrap_checks<'a>(errors: Vec<Error<'a>>) -> CheckResult<'a, ()> {
	if errors.len() > 0 {
		Err(errors)
	} else {
		Ok(())
	}
}

pub fn check_usage<'a>(body: &'a Term, term_type: Term, target_index: usize, context: Context) -> CheckResult<'a, ()> {
	use InnerError::*;

	match term_type.usage() {
		Shared => Ok(()),
		Unique =>
			if count_uses(body, 0) == (1, 1) {
				Ok(())
			} else {
				Err(vec![Error::new(body, context, MismatchedUsage { var_index: target_index, exp_usage: (1, 1), giv_usage: count_uses(body, 0) })])
			}
	}
}

// r#type should be checked with `check` before being checked with this
pub fn check_type<'a>(r#type: &'a Term, context: Context) -> CheckResult<'a, ()> {
	// panic!("`check_type` is not finished");

	// fn check_type_aux<'a>(r#type: &'a Term, context: Context, exp_shared: bool) -> CheckResult<'a, ()> {
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
	// 				(Unique, true) => Err(vec![Error::new(r#type, ExpectedSharedTypeType)]),
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

// returns the normalized and checked type of a term
// type may be infered if the term is a universe, in all other cases the type must be given
// when given, the type of the type is checked as well
// minor concern, is 'synth_type' the right name for this?
pub fn synth_type<'a>(term: &'a Term, context: Context) -> CheckResult<'a, Term> {
    use InnerTerm::*;

    match &term.type_ann {
        Some(r#type) => {
            let r#type = &**r#type;
            let mut errors = Vec::new();
            
            push_check(&mut errors, check(r#type, synth_type(r#type, context.clone())?, context.clone()));
            push_check(&mut errors, check_type(r#type, context.clone()));

            if errors.len() > 0 {
                Ok(normalize(r#type.clone(), context))
            } else {
                Err(errors)
            }
        },
        None =>
            match *term.data {
                TypeTypeIntro(level, _) => Ok(Term::new(Box::new(TypeTypeIntro(level + 1, Usage::Unique)), None)),
                _ => panic!("all terms should be explicitly typed")
            }
    }
}

// exp_type should always be checked and in normal form
pub fn check<'a>(term: &'a Term, exp_type: Term, context: Context) -> CheckResult<'a, ()> {
	use InnerError::*;
	
	let type_ann = synth_type(term, context.clone())?;
	if !is_terms_eq(&type_ann, &exp_type) {
		return
			Err(vec![Error::new(
				term,
				context,
				MismatchedTypes { exp_type: exp_type.clone(), giv_type: type_ann.clone() })]);
	}

	match *term.data {
		TypeTypeIntro(level, usage) =>
			match *(type_ann.clone()).data {
				TypeTypeIntro(type_ann_level, type_ann_usage) =>
					if type_ann_level > level {
						Ok(())
					} else {
						Err(vec![Error::new(term, context, ExpectedOfTypeType { min_level: level + 1, giv_type: type_ann })])
					}
				_ => Err(vec![Error::new(term, context, ExpectedOfTypeType { min_level: level + 1, giv_type: type_ann })])
			},
		Var(index) =>
			match context.get_dec(index) {
				Some(var_type) =>
					if is_terms_eq(&var_type, &type_ann) {
						Ok(())
					} else {
						Err(vec![Error::new(term, context, MismatchedTypes { exp_type: type_ann, giv_type: var_type })])
					}
				None => Err(vec![Error::new(term, context, NonexistentVar { index })])
			},
		Rec(ref inner_term) => {
			let mut errors = Vec::new();

			let new_context = context.clone().inc_and_shift(1).insert_dec(0, type_ann.clone());

			push_check(
				&mut errors,
				check(inner_term, type_ann.clone(), new_context.insert_dec(0, type_ann.clone())));
			push_check(&mut errors, check_usage(inner_term, type_ann, 0, new_context.clone()));

			wrap_checks(errors)

		},
		FunctionTypeIntro(ref caps_list, ref in_type, ref out_type) => {
			let mut errors = Vec::new();

			let out_type_context = context.clone().inc_and_shift(1).insert_dec(0, in_type.clone());

			let caps_list_type = synth_type(caps_list, context.clone())?;
			let in_type_type = synth_type(in_type, context.clone())?;
			let out_type_type = synth_type(out_type, out_type_context.clone())?;
			push_check(
				&mut errors,
				check(caps_list, caps_list_type.clone(), context.clone()));
			push_check(
				&mut errors,
				check(in_type, in_type_type.clone(), context.clone()));
			push_check(
				&mut errors,
				check(out_type, out_type_type.clone(), out_type_context));

			push_check(&mut errors, check_usage(out_type, in_type.clone(), 0, context.clone().inc_and_shift(1).clone()));

			match (*(caps_list_type.clone()).data, *(in_type_type.clone()).data, *(out_type_type.clone()).data) {
				(CapturesListTypeIntro(caps_list_level), TypeTypeIntro(in_level, in_usage), TypeTypeIntro(out_level, out_usage)) => {
					let giv_max = max(caps_list_level, max(in_level, out_level));
					if let TypeTypeIntro(max_level, fn_usage) = *type_ann.clone().data {
						if giv_max != max_level {
							errors.push(Error::new(
								term,
								context,
								MismatchedTypes {
									exp_type: Term::new(Box::new(TypeTypeIntro(max_level, fn_usage)), None),
									giv_type: Term::new(Box::new(TypeTypeIntro(giv_max, fn_usage)), None)
								}));
						}
					} else {
						errors.push(Error::new(term, context, ExpectedOfTypeType { min_level: giv_max, giv_type: type_ann }))
					}
				},
				(_, _, TypeTypeIntro(level, _)) => {
					errors.push(Error::new(in_type, context.clone(), ExpectedOfTypeType { min_level: level, giv_type: in_type_type }));
					errors.push(Error::new(caps_list, context, ExpectedOfCapturesListType { min_level: level, giv_type: caps_list_type }));
				}
				(_, TypeTypeIntro(level, _), _) => {
					errors.push(Error::new(out_type, context.clone(), ExpectedOfTypeType { min_level: level, giv_type: out_type_type }));
					errors.push(Error::new(caps_list, context, ExpectedOfCapturesListType { min_level: level, giv_type: caps_list_type }));
				}
				(_, _, _) =>  {
					errors.push(Error::new(in_type, context.clone(), ExpectedOfTypeType { min_level: 0, giv_type: in_type_type }));
					errors.push(Error::new(out_type, context.clone(), ExpectedOfTypeType { min_level: 0, giv_type: out_type_type }));
					errors.push(Error::new(caps_list, context, ExpectedOfCapturesListType { min_level: 0, giv_type: caps_list_type }));
				},
				(CapturesListTypeIntro(level1), _, TypeTypeIntro(level2, _)) =>
					errors.push(Error::new(in_type, context, ExpectedOfTypeType { min_level: max(level1, level2), giv_type: in_type_type })),
				(CapturesListTypeIntro(level1), TypeTypeIntro(level2, _), _) =>
					errors.push(Error::new(out_type, context, ExpectedOfTypeType { min_level: max(level1, level2), giv_type: out_type_type })),
				(CapturesListTypeIntro(level1), _, _) =>  {
					errors.push(Error::new(in_type, context.clone(), ExpectedOfTypeType { min_level: level1, giv_type: in_type_type }));
					errors.push(Error::new(out_type, context, ExpectedOfTypeType { min_level: level1, giv_type: out_type_type }));
				}
			}

			wrap_checks(errors)
		},
		FunctionIntro(ref body) => {
			let mut errors = Vec::new();

			match *type_ann.data {
				FunctionTypeIntro(caps_list, in_type, out_type) => {
					let body_context = context.clone().inc_and_shift(1).insert_dec(0, shift(in_type.clone(), HashSet::new(), 1));
					push_check(&mut errors, check(body, out_type, body_context));
					push_check(&mut errors, check_usage(body, in_type, 0, context.clone().inc_and_shift(1)));

					fn flatten_caps_list(caps_list: &Term) -> Vec<Term> {
						fn inner(caps_list: &Term, acc: &mut Vec<Term>) {
							match *caps_list.data {
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
					let free_var_types = get_free_vars(body).into_iter().map(|(_, t)| t).collect::<HashSet<Term>>();

					// get the captured vars that are not mentioned in the captures list, if any
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
				_ => errors.push(Error::new(term, context, ExpectedOfFunctionType { giv_type: type_ann }))
			}

			wrap_checks(errors)
		}
		FunctionElim(ref abs, ref arg) => {
			let mut errors = Vec::new();

			let abs_type = synth_type(abs, context.clone())?;
			push_check(&mut errors, check(abs, abs_type.clone(), context.clone()));

			match *abs_type.data {
				FunctionTypeIntro(caps_list, in_type, out_type) => {
					push_check(&mut errors, check(arg, in_type, context.clone()));
					// normalize out_type with normalized `arg` as var 0
					let normal_out_type =
						normalize(
							out_type,
							context.clone().inc_and_shift(1).insert_dec(0, in_type).insert_def(0, normalize(arg, context.clone())));
					push_check(
						&mut errors,
						if is_terms_eq(&type_ann, &normal_out_type) {
							Ok(())
						} else {
							Err(vec![Error::new(&inner_term, context, MismatchedTypes { exp_type: type_ann, giv_type: normal_out_type })])
						});
				},
				_ => errors.push(Error::new(term, context, ExpectedOfFunctionType { giv_type: abs_type }))
			}

			wrap_checks(errors)
		},
		PairTypeIntro(ref fst_type, ref snd_type) => {
			let mut errors = Vec::new();

			let fst_type_type = synth_type(fst_type, context.clone())?;
			push_check(
				&mut errors,
				check(fst_type, fst_type_type.clone(), context.clone().inc_and_shift(2).insert_dec(1, snd_type.clone())));

			let snd_type_type = synth_type(snd_type, context.clone())?;
			push_check(
				&mut errors,
				check(snd_type, snd_type_type.clone(), context.clone().inc_and_shift(2).insert_dec(0, fst_type.clone())));

			push_check(&mut errors, check_usage(snd_type, fst_type.clone(), 0, context.clone()));
			push_check(&mut errors, check_usage(fst_type, snd_type.clone(), 1, context.clone()));

			match (*(fst_type_type.clone()).data, *(snd_type_type.clone()).data) {
				(TypeTypeIntro(fst_level, fst_usage), TypeTypeIntro(snd_level, snd_usage)) =>
					if let TypeTypeIntro(max_level, pair_usage) = *type_ann.clone().data {
						if max(fst_level, snd_level) != max_level {
							errors.push(Error::new(
								term,
								context,
								MismatchedTypes {
									exp_type: Term::new(Box::new(TypeTypeIntro(max_level, pair_usage)), None),
									giv_type: Term::new(Box::new(TypeTypeIntro(max(fst_level, snd_level), pair_usage)), None)
								}));
						}
					} else {
						errors.push(Error::new(term, context, ExpectedOfTypeType { min_level: max(fst_level, snd_level), giv_type: type_ann }))
					},
				(_, TypeTypeIntro(level, _)) => errors.push(Error::new(fst_type, context, ExpectedOfTypeType { min_level: level, giv_type: fst_type_type })),
				(TypeTypeIntro(level, _), _) => errors.push(Error::new(snd_type, context, ExpectedOfTypeType { min_level: level, giv_type: snd_type_type })),
				(_, _) =>  {
					errors.push(Error::new(fst_type, context.clone(), ExpectedOfTypeType { min_level: 0, giv_type: fst_type_type }));
					errors.push(Error::new(snd_type, context, ExpectedOfTypeType { min_level: 0, giv_type: snd_type_type }));
				}
			}

			wrap_checks(errors)
		},
		PairIntro(ref fst, ref snd) => {
			match *type_ann.data {
				PairTypeIntro(fst_type, snd_type) => {
					let mut errors = Vec::new();

					push_check(&mut errors, check(fst, fst_type.clone(), context.clone().inc_and_shift(2).insert_dec(1, snd_type.clone())));
					push_check(&mut errors, check(snd, snd_type, context.inc_and_shift(2).insert_dec(0, fst_type)));

					wrap_checks(errors)
				},
				_ => Err(vec![Error::new(term, context, ExpectedOfPairType { giv_type: type_ann })])
			}
		},
		PairElim(ref discrim, ref body) => {
			let mut errors = Vec::new();

			let discrim_type = synth_type(discrim, context.clone())?;
			push_check(&mut errors, check(discrim, discrim_type.clone(), context.clone()));

			match *(discrim_type.clone()).data {
				PairTypeIntro(fst_type, snd_type) => {
					let body_context = context.clone().inc_and_shift(2).insert_dec(0, fst_type.clone()).insert_dec(1, snd_type.clone());
					let body_type = synth_type(body, body_context.clone())?;
					push_check(&mut errors, check(body, shift(type_ann, 2, HashSet::new()), body_context));
					
					push_check(&mut errors, check_usage(body, fst_type.clone(), 0, context.clone()));
					push_check(&mut errors, check_usage(body, snd_type.clone(), 1, context.clone()));
				}
				_ => errors.push(Error::new(discrim, context, ExpectedOfPairType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		},
		VoidTypeIntro =>
			match *(type_ann.clone()).data {
				TypeTypeIntro(_, _) => Ok(()),
				_ => Err(vec![Error::new(term, context, ExpectedOfTypeType { min_level: 0, giv_type: type_ann.clone() })])
			},
        UnitTypeIntro =>
        	match *(type_ann.clone()).data {
				TypeTypeIntro(_, _) => Ok(()),
				_ => Err(vec![Error::new(term, context, ExpectedOfTypeType { min_level: 0, giv_type: type_ann.clone() })])
			},
        UnitIntro =>
        	match *(type_ann.clone()).data {
				UnitTypeIntro => Ok(()),
				_ => Err(vec![Error::new(term, context, ExpectedOfUnitType { giv_type: type_ann.clone() })])
			},
		DoubTypeIntro =>
			match *(type_ann.clone()).data {
				TypeTypeIntro(_, _) => Ok(()),
				_ => Err(vec![Error::new(term, context, ExpectedOfTypeType { min_level: 0, giv_type: type_ann.clone() })])
			},
		DoubIntro(_) =>
			match *(type_ann.clone()).data {
				EnumTypeIntro => Ok(()),
				_ => Err(vec![Error::new(term, context, ExpectedOfEnumType { giv_type: type_ann.clone() })])
			},
		DoubElim(ref discrim, ref branch1, ref branch2) => {
			let mut errors = Vec::new();

			let discrim_type = synth_type(discrim, context.clone())?;
			push_check(&mut errors, check(discrim, discrim_type.clone(), context.clone()));

			match *(discrim_type.clone()).data {
				DoubTypeIntro => {
					let branch_context = |d: Term|
						match *normalize(discrim.clone(), context.clone()).data { // updates context with the now known value of discrim if it is a var
							Var(index) => context.clone().update(index, d.clone()).insert_def(index, d),
							_ => context.clone()
						};

					push_check(&mut errors, check(branch1, type_ann.clone(), branch_context(discrim.clone())));
					push_check(&mut errors, check(branch2, type_ann, branch_context(discrim.clone())));
				},
				_ => errors.push(Error::new(discrim, context, ExpectedOfEnumType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		},
		FoldTypeIntro(ref inner_type) =>
			match *(type_ann.clone()).data {
				TypeTypeIntro(_, _) => {
					let mut errors = Vec::new();
					push_check(&mut errors, check(inner_type, synth_type(inner_type, context.clone())?, context.clone()));
					push_check(&mut errors, check_type(inner_type, context.clone()));
					wrap_checks(errors)
				},
				_ => Err(vec![Error::new(term, context, ExpectedOfTypeType { min_level: 0, giv_type: type_ann.clone() })])
			},
		FoldIntro(ref inner_term) =>
			match *(type_ann.clone()).data {
				FoldTypeIntro(inner_type) => check(inner_term, inner_type, context),
				_ => Err(vec![Error::new(term, context, ExpectedOfFoldType { giv_type: type_ann.clone() })])
			},
		FoldElim(ref folded_term) => check(folded_term, type_ann, context),
		CapturesListTypeIntro(level) =>
			match *type_ann.clone().data {
				TypeTypeIntro(u_level, _) =>
					if u_level > level {
						Ok(())
					} else {
						Err(vec![Error::new(term, context, ExpectedOfTypeType { min_level: level + 1, giv_type: type_ann })])
					}
				_ => Err(vec![Error::new(term, context, ExpectedOfTypeType { min_level: 1, giv_type: type_ann })])
			}
		CapturesListIntro(ref list) =>
			match *type_ann.data {
				CapturesListTypeIntro(level) =>
					match list {
						Cons(ref head, ref tail) => {
							let mut errors = Vec::new();

							let head_type = synth_type(head, context.clone())?;
							let tail_type = synth_type(head, context.clone())?;

							match (*head_type.clone().data, *tail_type.clone().data) {
								(TypeTypeIntro(_, head_usage), CapturesListTypeIntro(_)) => {
									push_check(&mut errors, check(head, Term::new(Box::new(TypeTypeIntro(level, head_usage)), None), context.clone()));
									push_check(&mut errors, check_type(head, context.clone()));
									let caps_list_type =
										Term::new(Box::new(
											CapturesListTypeIntro(level)),
											Some(Box::new(Term::new(Box::new(
												TypeTypeIntro(level, Usage::Unique)), // TODO: figure out whether this is correct
												None))));
									push_check(&mut errors, check(tail, caps_list_type, context));
								}
								(TypeTypeIntro(level, _), _) => errors.push(Error::new(head, context, ExpectedOfCapturesListType { min_level: level, giv_type: head_type })),
								(_, CapturesListTypeIntro(level)) => errors.push(Error::new(tail, context, ExpectedOfTypeType { min_level: level, giv_type: tail_type })),
								(_, _) => {
									errors.push(Error::new(head, context.clone(), ExpectedOfTypeType { min_level: 0, giv_type: head_type }));
									errors.push(Error::new(tail, context, ExpectedOfCapturesListType { min_level: 0, giv_type: tail_type }));
								}
							}

							wrap_checks(errors)
						},
						Nil => Ok(())
					}
				_ => Err(vec![Error::new(term, context, ExpectedOfCapturesListType { min_level: 0, giv_type: type_ann })])
			}
	}
}