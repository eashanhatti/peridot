#![allow(warnings)]

use super::{
	lang::{
		*,
		VarInner::*,
		InnerTerm::*,
		Usage::*,
		TermComparison::*
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
	fmt::{
		self,
		Debug,
		Display
	},
	hash::Hash,
	iter::FromIterator,
	convert::TryInto
};
extern crate rand;

// for the `Expected...` errors, imagine a TypeType `U` for each error, the error
// can then be thought of as `MismatchedTypes { exp_type: U, giv_type: ... }
#[derive(Debug)]
pub enum InnerError {
    MismatchedTypes { exp_type: Term, giv_type: Term, specific: Vec<(Term, Term)> },
    NonexistentVar { index: VarInner },
    ExpectedOfTypeType { min_level: usize, giv_type: Term },
    ExpectedOfFunctionType { giv_type: Term },
    ExpectedOfPairType { giv_type: Term },
    ExpectedOfDoubType { giv_type: Term },
    ExpectedOfFoldType { giv_type: Term },
    ExpectedOfUnitType { giv_type: Term },
    ExpectedOfIndexedType { giv_type: Term },
    ExpectedOfUniqueKind { giv_kind: Term },
    MismatchedUsage { var_index: VarInner, exp_usage: (usize, usize), giv_usage: (usize, usize) }
}
use InnerError::*;

#[derive(Debug)]
pub struct Error<'a> {
    term: &'a Term,
    error: InnerError,
    context: Context
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

pub fn count_uses(term: &Term, target_index: VarInner) -> (usize, usize) {
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

	fn inc(index: VarInner) -> VarInner {
		if let Bound(bound_index) = index {
			Bound(bound_index + 1)
		} else {
			index
		}
	}

	fn inc_by(index: VarInner, by: usize) -> VarInner {
		if let Bound(bound_index) = index {
			Bound(bound_index + by)
		} else {
			index
		}
	}

	fn singleton(bound: usize) -> (usize, usize) { (bound, bound) }

	sum(vec![
		match *term.data {
			TypeTypeIntro(level, usage) => singleton(0),
			Var(index) => if index == target_index { singleton(1) } else { singleton(0) },
			Rec(ref inner_term) => count_uses(inner_term, inc(target_index)),
			Let(ref bindings, ref body) => unimplemented!(),
			FunctionTypeIntro(ref in_type, ref out_type) =>
				sum(vec![
					mul(vec![
						count_uses(in_type, target_index),
						count_uses(out_type, Bound(0))
					]),
					count_uses(out_type, inc(target_index))
				]),
			FunctionIntro(ref body) => count_uses(body, inc(target_index)),
			FunctionElim(ref abs, ref arg) => unimplemented!(),
			PairTypeIntro(ref fst_type, ref snd_type) =>
				sum(vec![count_uses(fst_type, inc_by(target_index, 2)), count_uses(snd_type, inc_by(target_index, 2))]),
			PairIntro(ref fst, ref snd) =>
				sum(vec![count_uses(fst, target_index), count_uses(snd, target_index)]),
			PairElim(ref discrim, ref body) =>
				sum(vec![count_uses(discrim, target_index), count_uses(body, inc_by(target_index, 2))]),
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
			IndexedTypeIntro(_, ref inner_type) => count_uses(inner_type, target_index),
			IndexedIntro(ref inner_term) => count_uses(inner_term, target_index),
			IndexedElim(ref folded_term) => count_uses(folded_term, target_index),
			Postulate(_) => singleton(0)
		},
		match &term.type_ann {
			Some(r#type) => count_uses(r#type, target_index),
			None => singleton(0)
		}])
}

pub fn level_of<'a>(r#type: &'a Term, context: Context) -> CheckResult<'a, usize> {
	use InnerError::*;

	let r#type_type = synth_type(r#type, context.clone())?;
	match *r#type_type.data {
		TypeTypeIntro(level, _) => Ok(level),
		_ => Err(vec![Error::new(r#type, context, ExpectedOfTypeType { min_level: 1, giv_type: r#type_type })])
	}
}

// `term` should be checked before this is called
// should make this more robust in the future
fn get_free_vars(term: &Term, bounds: HashSet<VarInner>) -> HashMap<VarInner, Term> {
	type Map = HashMap<VarInner, Term>;

	fn inner(term: &Term, bounds: HashSet<VarInner>) -> Map {
		fn collapse(maps: Vec<Map>) -> Map {
			let mut new_map: Map = HashMap::new();
			for map in maps {
				for (k, v) in map {
					new_map.insert(k, v);
				}
			}
			new_map
		}

		fn inc(set: HashSet<VarInner>) -> HashSet<VarInner> {
			inc_by(set, 1)
		}

		fn inc_by(set: HashSet<VarInner>, by: usize) -> HashSet<VarInner> {
			let mut tmp = set.into_iter().map(|i| if let Bound(i_bound) = i { Bound(i_bound + by) } else { i }).collect::<HashSet<VarInner>>();
			tmp
		}

		fn with(mut set: HashSet<VarInner>, index: usize) -> HashSet<VarInner> {
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
				TypeTypeIntro(_, _) => HashMap::new(),
				Var(index) =>
					if bounds.contains(&index) {
						HashMap::new()
					} else {
						let mut map = HashMap::new();
						map.insert(index, term.r#type());
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

pub fn wrap_checks<'a>(errors: Vec<Error<'a>>) -> CheckResult<'a, ()> {
	if errors.len() > 0 {
		Err(errors)
	} else {
		Ok(())
	}
}

pub fn check_usage<'a>(body: &'a Term, term_type: Term, target_index: VarInner, context: Context) -> CheckResult<'a, ()> {
	use InnerError::*;

	match term_type.usage() {
		Shared => Ok(()),
		Unique =>
			if count_uses(body, target_index) == (1, 1) {
				Ok(())
			} else {
				Err(vec![Error::new(body, context, MismatchedUsage { var_index: target_index, exp_usage: (1, 1), giv_usage: count_uses(body, target_index) })])
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

            if errors.len() == 0 {
                Ok(normalize(r#type.clone(), context))
            } else {
                Err(errors)
            }
        },
        None =>
            match *term.data {
                TypeTypeIntro(level, _) => Ok(Term::new(Box::new(TypeTypeIntro(level + 1, Usage::Unique)), None)),
                Var(index) =>
                	match context.get_dec(index) {
						Some(var_type) => Ok(var_type),
						None => Err(vec![Error::new(term, context, NonexistentVar { index })])
					},
				Let(ref bindings, ref body) => { // TODO: check bindings and body?
					let r#type =
						Term::new(
							Box::new(Let(
								bindings.to_vec(),
								body.r#type())),
							None); // TODO: this should probably use `synth_type`
					Ok(normalize(r#type, context))
				},
				FunctionElim(ref abs, ref arg) => { // TODO: checking?
					let abs_type = synth_type(abs, context.clone())?;
					match &*abs_type.data {
						FunctionTypeIntro(_, ref out_type) =>
							Ok(normalize(
								out_type.clone(),
								context.clone().inc_and_shift(1)
									.with_def(Bound(0), normalize(arg.clone(), context)))),
						_ => Err(vec![Error::new(abs, context, ExpectedOfFunctionType { giv_type: abs_type })])
					}
				}
                _ => panic!("all terms must be explicitly typed, this term is not:\n{:#?}", term)
            }
    }
}

pub fn check<'a>(term: &'a Term, exp_type: Term, context: Context) -> CheckResult<'a, ()> {
	use InnerError::*;

	let context = context.normalize();

	let type_ann = synth_type(term, context.clone())?;
	if let False(specific) = is_terms_eq(&type_ann, &exp_type, context.clone().equivs()) {
		// println!("NOT EQ\n{:?}\n{:?}", type_ann, exp_type);
		return
			Err(vec![Error::new(
				term,
				context,
				MismatchedTypes { exp_type: exp_type.clone(), giv_type: type_ann.clone(), specific })]);
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
				Some(var_type) => {
					if let False(specific) = is_terms_eq(&var_type, &type_ann, context.clone().equivs()) {
						Err(vec![Error::new(term, context, MismatchedTypes { exp_type: var_type, giv_type: type_ann, specific })])
					} else {
						Ok(())
					}
				}
				None => Err(vec![Error::new(term, context, NonexistentVar { index })])
			},
		Rec(ref inner_term) => {
			let mut errors = Vec::new();

			let new_context = context.clone().inc_and_shift(1).with_dec(Bound(0), type_ann.clone());

			push_check(
				&mut errors,
				check(inner_term, type_ann.clone(), new_context.clone().with_dec(Bound(0), type_ann.clone())));
			// push_check(&mut errors, check_usage(inner_term, type_ann, Bound(0), new_context));

			wrap_checks(errors)
		},
		Let(ref bindings, ref body) => {
			let mut errors = Vec::new();

			let mut new_context = context.inc_and_shift(bindings.len().try_into().unwrap());
			for (i, binding) in bindings.iter().enumerate() {
				let binding_type = synth_type(binding, new_context.clone())?;
				match check(binding, binding_type.clone(), new_context.clone()) {
					Ok(()) => (),
					Err(errs) => {
						push_check::<()>(&mut errors, Err(errs));
						continue;
					}
				}

				let normal_binding = normalize(binding.clone(), new_context.clone());
				new_context = new_context
					.with_dec(Bound(i), binding_type)
					.with_def(Bound(i), normal_binding);
			}

			push_check(&mut errors, check(body, synth_type(body, new_context.clone())?, new_context));

			wrap_checks(errors)
		}
		FunctionTypeIntro(ref in_type, ref out_type) => {
			let mut errors = Vec::new();

			let out_type_context = context.clone().inc_and_shift(1).with_dec(Bound(0), in_type.clone());

			let in_type_type = synth_type(in_type, context.clone())?;
			let out_type_type = synth_type(out_type, out_type_context.clone())?;
			push_check(
				&mut errors,
				check(in_type, in_type_type.clone(), context.clone()));
			push_check(
				&mut errors,
				check(out_type, out_type_type.clone(), out_type_context));

			// push_check(&mut errors, check_usage(out_type, in_type.clone(), Bound(0), context.clone().inc_and_shift(1).clone()));

			// let mut in_type_level = None;
			// let mut out_type_level = None;
			// if let TypeTypeIntro(level, _) = &(*in_type_type.data) {
			// 	in_type_level = Some(*level);
			// }
			// if let TypeTypeIntro(level, _) = &(*out_type_type.data) {
			// 	out_type_level = Some(*level);
			// }

			// match (in_type_level, out_type_level) {
			// 	(Some(in_type_level), Some(out_type_level)) => {
			// 		let giv_max = max(in_type_level, out_type_level);
			// 		if let TypeTypeIntro(exp_max, fn_usage) = *type_ann.clone().data {
			// 			if giv_max > exp_max {
			// 				errors.push(Error::new(
			// 					term,
			// 					context,
			// 					ExpectedOfTypeType {
			// 						min_level: exp_max,
			// 						giv_type: Term::new(Box::new(TypeTypeIntro(giv_max, fn_usage)), None)
			// 					}));
			// 			}
			// 		} else {
			// 			errors.push(Error::new(term, context, ExpectedOfTypeType { min_level: giv_max, giv_type: type_ann }))
			// 		}
			// 	},
			// 	(None, Some(out_type_level)) =>
			// 		errors.push(Error::new(in_type, context, ExpectedOfTypeType { min_level: out_type_level, giv_type: in_type_type })),
			// 	(Some(in_type_level), None) =>
			// 		errors.push(Error::new(out_type, context, ExpectedOfTypeType { min_level: in_type_level, giv_type: out_type_type })),
			// 	(None, None) => {
			// 		errors.push(Error::new(in_type, context.clone(), ExpectedOfTypeType { min_level: 0, giv_type: in_type_type }));
			// 		errors.push(Error::new(out_type, context, ExpectedOfTypeType { min_level: 0, giv_type: out_type_type }));
			// 	}
			// }

			wrap_checks(errors)
		},
		FunctionIntro(ref body) => {
			let mut errors = Vec::new();

			match *type_ann.clone().data {
				FunctionTypeIntro(in_type, out_type) => {
					let body_context = context.clone().inc_and_shift(1).with_dec(Bound(0), shift(in_type.clone(), HashSet::new(), 1));
					push_check(&mut errors, check(body, out_type, body_context));
					// push_check(&mut errors, check_usage(body, in_type, Bound(0), context.clone().inc_and_shift(1)));

					// let free_vars = get_free_vars(body, HashSet::from_iter(vec![Bound(0)]));
					// if let TypeTypeIntro(level, Shared) = *type_ann.data {
					// 	for (_, var_type) in free_vars {
					// 		if let TypeTypeIntro(_, Unique) = *var_type.r#type().data {
					// 			errors.push(Error::new(term, context, ExpectedOfUniqueKind { giv_kind: type_ann }));
					// 			break;
					// 		}
					// 	}
					// }
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
				FunctionTypeIntro(in_type, out_type) => {
					push_check(&mut errors, check(arg, in_type.clone(), context.clone()));
					// normalize out_type with normalized `arg` as var 0
					let normal_out_type =
						normalize(
							out_type,
							context.clone()
								.inc_and_shift(1)
								.with_dec(Bound(0), in_type)
								.with_def(Bound(0), normalize(arg.clone(), context.clone())));
					push_check(
						&mut errors,
						if let False(specific) = is_terms_eq(&normal_out_type, &type_ann, context.clone().equivs()) {
							Err(vec![Error::new(&term, context, MismatchedTypes { exp_type: type_ann, giv_type: normal_out_type, specific })])
						} else {
							Ok(())
						});
				},
				_ => errors.push(Error::new(term, context, ExpectedOfFunctionType { giv_type: abs_type }))
			}

			wrap_checks(errors)
		},
		PairTypeIntro(ref fst_type, ref snd_type) => {
			let mut errors = Vec::new();

			let fst_type_context = context.clone().inc_and_shift(2).with_dec(Bound(1), snd_type.clone());
			let snd_type_context = context.clone().inc_and_shift(2).with_dec(Bound(0), fst_type.clone());
			let fst_type_type = synth_type(fst_type, context.clone())?;
			push_check(
				&mut errors,
				check(fst_type, fst_type_type.clone(), fst_type_context.clone()));

			let snd_type_type = synth_type(snd_type, context.clone())?;
			push_check(
				&mut errors,
				check(snd_type, snd_type_type.clone(), snd_type_context.clone()));

			// push_check(&mut errors, check_usage(fst_type, snd_type.clone(), Bound(1), fst_type_context));
			// push_check(&mut errors, check_usage(snd_type, fst_type.clone(), Bound(0), snd_type_context));

			match (*(fst_type_type.clone()).data, *(snd_type_type.clone()).data) {
				(TypeTypeIntro(fst_level, fst_usage), TypeTypeIntro(snd_level, snd_usage)) =>
					if let TypeTypeIntro(max_level, pair_usage) = *type_ann.clone().data {
						if max(fst_level, snd_level) > max_level {
							errors.push(Error::new(
								term,
								context,
								MismatchedTypes {
									exp_type: Term::new(Box::new(TypeTypeIntro(max_level, pair_usage)), None),
									giv_type: Term::new(Box::new(TypeTypeIntro(max(fst_level, snd_level), pair_usage)), None),
									specific: Vec::new()
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

					let fst_context = context.clone().inc_and_shift(2).with_dec(Bound(1), snd_type.clone()).with_def(Bound(1), normalize(snd.clone(), context.clone()));
					let snd_context = context.clone().inc_and_shift(2).with_dec(Bound(0), fst_type.clone()).with_def(Bound(0), normalize(fst.clone(), context.clone()));
					let normal_fst_type = normalize(fst_type, fst_context.clone());
					let normal_snd_type = normalize(snd_type, snd_context.clone());

					push_check(&mut errors, check(fst, normal_fst_type, fst_context));
					push_check(&mut errors, check(snd, normal_snd_type, snd_context));

					wrap_checks(errors)
				},
				_ => Err(vec![Error::new(term, context, ExpectedOfPairType { giv_type: type_ann })])
			}
		},
		PairElim(ref discrim, ref body) => {
			let mut errors = Vec::new();

			let discrim_type = synth_type(discrim, context.clone())?;
			// println!("CONTEXT {:?}\nDISCRIM_TYPE {:?}", context.clone(), discrim_type.clone());
			push_check(&mut errors, check(discrim, discrim_type.clone(), context.clone()));

			match *(discrim_type.clone()).data {
				PairTypeIntro(fst_type, snd_type) => {
					let sym_fst_id = Symbol(rand::random::<usize>());
					let sym_fst =
						Term::new(
							Box::new(Var(Free(sym_fst_id))),
							Some(Box::new(fst_type.clone())));
					let sym_snd_id = Symbol(rand::random::<usize>());
					let sym_snd =
						Term::new(
							Box::new(Var(Free(sym_snd_id))),
							Some(Box::new(snd_type.clone())));
					let body_context =
						context.clone().inc_and_shift(2)
							.with_dec(Bound(0), fst_type)
							.with_dec(Bound(1), snd_type);
					let type_ann_context =
						match *discrim.data {
							Var(index) => {
								let refined_discrim =
									Term::new(
										Box::new(PairIntro(
											sym_fst.clone(),
											sym_snd.clone())),
										Some(Box::new(discrim_type.clone())));
								context.update(index, refined_discrim.clone()).with_def(index, refined_discrim)
							},
							_ => context.clone()
						};
					let normal_type_ann =
						/*substitute(*/
							normalize(type_ann, type_ann_context)/*,
							Context::new().with_def(Bound(0), sym_fst).with_def(Bound(1), sym_snd))*/;
					push_check(&mut errors, check(body, normal_type_ann, body_context.with_equiv(Bound(0), Free(sym_fst_id)).with_equiv(Bound(1), Free(sym_snd_id))));
				}
				_ => errors.push(Error::new(discrim, context, ExpectedOfPairType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		}
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
				DoubTypeIntro => Ok(()),
				_ => Err(vec![Error::new(term, context, ExpectedOfDoubType { giv_type: type_ann.clone() })])
			},
		DoubElim(ref discrim, ref branch1, ref branch2) => {
			let mut errors = Vec::new();

			let discrim_type = synth_type(discrim, context.clone())?;
			push_check(&mut errors, check(discrim, discrim_type.clone(), context.clone()));

			match *(discrim_type.clone()).data {
				DoubTypeIntro => {
					// println!("DISCRIM {:?}", discrim);
					// println!("NORMAL_DISCRIM {:?}", normalize(discrim.clone(), context.clone()));
					let branch_context = |d: Term|
						match *normalize(discrim.clone(), context.clone()).data { // updates context with the now known value of discrim if it is a var
							Var(index) => context.clone().update(index, d.clone()).with_def(index, d),
							_ => context.clone()
						};

					let branch1_context =
						branch_context(
							Term::new(
								Box::new(DoubIntro(Doub::This)),
								Some(Box::new(discrim_type.clone()))));
					let branch2_context =
						branch_context(
							Term::new(
								Box::new(DoubIntro(Doub::That)),
								Some(Box::new(discrim_type))));
					// println!("DISCRIM\n{:?}", discrim);
					// println!("NORMAL DISCRIM\n{:?}", normalize(discrim.clone(), context.clone()));
					// println!("TYPE ANN\n{:?}", type_ann);
					// println!("CONTEXT\n{:?}", branch1_context.clone());
					// println!("BRANCH 1 CONTEXT {:?}", branch1_context.len());
					push_check(&mut errors, check(branch1, normalize(type_ann.clone(), branch1_context.clone()), branch1_context.clone()));
					// println!("BRANCH 2 CONTEXT {:?}", branch2_context.len());
					push_check(&mut errors, check(branch2, normalize(type_ann, branch2_context.clone()), branch2_context));
				},
				_ => errors.push(Error::new(discrim, context, ExpectedOfDoubType { giv_type: discrim_type }))
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
		FoldElim(ref folded_term) => {
			let folded_term_type = synth_type(folded_term, context.clone())?;
			match &*folded_term_type.data {
				FoldTypeIntro(_) => check(folded_term, type_ann, context),
				_ => Err(vec![Error::new(term, context, ExpectedOfFoldType { giv_type: folded_term_type })])
			}
		}
		IndexedTypeIntro(_, ref inner_type) =>
			match *(type_ann.clone()).data {
				TypeTypeIntro(_, _) => {
					let mut errors = Vec::new();
					push_check(&mut errors, check(inner_type, synth_type(inner_type, context.clone())?, context.clone()));
					push_check(&mut errors, check_type(inner_type, context.clone()));
					wrap_checks(errors)
				},
				_ => Err(vec![Error::new(term, context, ExpectedOfTypeType { min_level: 0, giv_type: type_ann.clone() })])
			},
		IndexedIntro(ref inner_term) =>
			match *(type_ann.clone()).data {
				IndexedTypeIntro(_, inner_type) => check(inner_term, inner_type, context),
				_ => Err(vec![Error::new(term, context, ExpectedOfIndexedType { giv_type: type_ann.clone() })])
			},
		IndexedElim(ref indexed_term) => {
			let indexed_term_type = synth_type(indexed_term, context.clone())?;
			match &*indexed_term_type.data {
				IndexedTypeIntro(_, _) => check(indexed_term, type_ann, context),
				_ => Err(vec![Error::new(term, context, ExpectedOfIndexedType { giv_type: indexed_term_type })])
			}
		}
		Postulate(_) => Ok(())
	}
}