#![allow(warnings)]

use super::{
	lang::{
		*,
		InnerVar::*,
		InnerTerm::*,
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
extern crate macros;
use macros::*;

// for the `Expected...` errors, imagine a TypeType `U` for each error, the error
// can then be thought of as `MismatchedTypes { exp_type: U, giv_type: ... }
#[derive(Debug)]
pub enum InnerError {
    MismatchedTypes { exp_type: Term, giv_type: Term, specific: Vec<(Term, Term)> },
    NonexistentVar { index: InnerVar },
    ExpectedOfTypeType { giv_type: Term },
    ExpectedOfFunctionType { giv_type: Term },
    ExpectedOfPairType { giv_type: Term },
    ExpectedOfDoubType { giv_type: Term },
    ExpectedOfFoldType { giv_type: Term },
    ExpectedOfUnitType { giv_type: Term },
    ExpectedOfIndexedType { giv_type: Term },
    ExpectedOfUniqueKind { giv_kind: Term }
}
use InnerError::*;

type DebugInfo = (Vec<usize>, String);

#[derive(Debug)]
pub struct Error {
    debug_info: DebugInfo,
    loc: Option<Location>,
    error: InnerError,
    context: Context
}

impl Error {
    pub fn new(loc: Option<Location>, context: Context, error: InnerError) -> Error {
        Error {
            loc,
            context,
            error,
            debug_info: (Vec::new(), String::new())
        }
    }

    pub fn new_o(debug_info: Vec<usize>, loc: Option<Location>, context: Context, error: InnerError) -> Error {
        Error {
            loc,
            context,
            error,
            debug_info: (debug_info, String::new())
        }
    }

    pub fn new_o_s(debug_info: Vec<usize>, debug_string: String, loc: Option<Location>, context: Context, error: InnerError) -> Error {
        Error {
            loc,
            context,
            error,
            debug_info: (debug_info, debug_string)
        }
    }
}

pub type CheckResult<T> = Result<T, Vec<Error>>;

pub fn push_check<T>(errors: &mut Vec<Error>, this_check: CheckResult<T>) { // appends errors to an error list, if there are any
	match this_check {
		Ok(_) => (),
		Err(errs) => {
			for err in errs {
				errors.push(err);
			}
		}
	}
}

pub fn count_uses(term: &Term, target_index: InnerVar) -> (usize, usize) {
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

	fn inc(index: InnerVar) -> InnerVar {
		if let Bound(bound_index) = index {
			Bound(bound_index + 1)
		} else {
			index
		}
	}

	fn inc_by(index: InnerVar, by: usize) -> InnerVar {
		if let Bound(bound_index) = index {
			Bound(bound_index + by)
		} else {
			index
		}
	}

	fn singleton(bound: usize) -> (usize, usize) { (bound, bound) }

	sum(vec![
		match *term.data {
			TypeTypeIntro => singleton(0),
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
			IndexedElim(ref discrim, ref body) =>
				sum(vec![
					count_uses(discrim, target_index),
					count_uses(body, inc_by(target_index, 1))
				]),
			Postulate(_) => singleton(0)
		},
		match &term.type_ann {
			Some(r#type) => count_uses(r#type, target_index),
			None => singleton(0)
		}])
}

pub fn wrap_checks(errors: Vec<Error>) -> CheckResult<()> {
	if errors.len() > 0 {
		Err(errors)
	} else {
		Ok(())
	}
}

// returns the normalized and checked type of a term
// type may be infered if the term is a universe, in all other cases the type must be given
// when given, the type of the type is checked as well
// minor concern, is 'synth_type' the right name for this?
pub fn synth_type(term: &Term, context: Context) -> CheckResult<Term> {
    use InnerTerm::*;

    let r#type = normalize(term.r#type(context.clone()), context.clone());
    match &*r#type.data {
    	TypeTypeIntro => (),
    	_ => check(&r#type, synth_type(&r#type, context.clone())?, context)?
    }
    Ok(r#type)
}

static mut stack: Vec<usize> = Vec::new();
pub fn check_d(term: &Term, exp_type: Term, context: Context) -> CheckResult<()> {
	unsafe { stack.push(term.loc.unwrap_or(Location { line: 0 }).line) };
	let result = check(term, exp_type, context);
	unsafe { stack.pop() };
	result
}

pub fn check(term: &Term, exp_type: Term, context: Context) -> CheckResult<()> {
	use InnerError::*;

	let type_ann = synth_type(term, context.clone())?;
	if let False(specific) = is_terms_eq(&type_ann, &exp_type, context.equivs()) {
		// println!("NOT EQ\n{:?}\n{:?}", type_ann, exp_type);
		return
			Err(vec![Error::new_o(
				unsafe { stack.clone() },
				term.loc(),
				context,
				MismatchedTypes { exp_type: exp_type.clone(), giv_type: type_ann.clone(), specific })]);
	}

	match *term.data {
		TypeTypeIntro =>
			match *(type_ann.clone()).data {
				TypeTypeIntro => Ok(()),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfTypeType { giv_type: type_ann })])
			},
		Var(index) => 
			match context.get_dec(index) {
				Some(var_type) => {
					let var_type = normalize(var_type, context.clone());
					if let False(specific) = is_terms_eq(&var_type, &type_ann, context.equivs()) {
						Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, MismatchedTypes { exp_type: var_type, giv_type: type_ann, specific })])
					} else {
						Ok(())
					}
				}
				None => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, NonexistentVar { index })])
			},
		Rec(ref inner_term) => {
			let mut errors = Vec::new();

			let new_context = context.clone().inc_and_shift(1).with_dec(Bound(0), type_ann.clone());

			push_check(
				&mut errors,
			check_d(inner_term, type_ann.clone(), new_context.clone().with_dec(Bound(0), type_ann.clone())));

			wrap_checks(errors)
		},
		Let(ref bindings, ref body) => {
			let mut errors = Vec::new();

			let mut new_context = context.inc_and_shift(bindings.len().try_into().unwrap());
			for (i, binding) in bindings.iter().enumerate() {
				let binding_type = synth_type(binding, new_context.clone())?;
			check_d(binding, binding_type.clone(), new_context.clone())?;

				let normal_binding = normalize(binding.clone(), new_context.clone());
				new_context = new_context
					.with_dec(Bound(i), binding_type)
					.with_def(Bound(i), normal_binding);
			}

			push_check(&mut errors,check_d(body, synth_type(body, new_context.clone())?, new_context));

			wrap_checks(errors)
		}
		FunctionTypeIntro(ref in_type, ref out_type) => {
			let mut errors = Vec::new();

			let out_type_context = context.clone().inc_and_shift(1).with_dec(Bound(0), shift(in_type.clone(), HashSet::new(), 1));

			let in_type_type = synth_type(in_type, context.clone())?;
			let out_type_type = synth_type(out_type, out_type_context.clone())?;
			push_check(
				&mut errors,
			check_d(in_type, in_type_type.clone(), context.clone()));
			push_check(
				&mut errors,
			check_d(out_type, out_type_type.clone(), out_type_context));

			wrap_checks(errors)
		},
		FunctionIntro(ref body) => {
			let mut errors = Vec::new();

			match *type_ann.clone().data {
				FunctionTypeIntro(mut in_type, out_type) => {
					in_type.note = Some(Note(format!("{:?} / lam bound {:?}", in_type.note, term.note)));
					let body_context = context.clone().inc_and_shift(1).with_dec(Bound(0), shift(in_type.clone(), HashSet::new(), 1));
					push_check(&mut errors,check_d(body, out_type, body_context));
				},
				_ => errors.push(Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfFunctionType { giv_type: type_ann }))
			}

			wrap_checks(errors)
		}
		FunctionElim(ref abs, ref arg) => {
			let mut errors = Vec::new();

			let abs_type = synth_type(abs, context.clone())?;
			push_check(&mut errors,check_d(abs, abs_type.clone(), context.clone()));

			match *abs_type.data {
				FunctionTypeIntro(in_type, out_type) => {
					push_check(&mut errors,check_d(arg, in_type.clone(), context.clone()));
					// normalize out_type with normalized `arg` as var 0
					let normal_out_type =
						shift(
							normalize(
								out_type,
								context.clone()
									.inc_and_shift(1)
									.with_dec(Bound(0), in_type)
									.with_def(Bound(0), normalize(arg.clone(), context.clone()))),
							HashSet::new(),
							-1);
					push_check(
						&mut errors,
						if let False(specific) = is_terms_eq(&normal_out_type, &type_ann, context.equivs()) {
							Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, MismatchedTypes { exp_type: type_ann, giv_type: normal_out_type, specific })])
						} else {
							Ok(())
						});
				},
				_ => errors.push(Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfFunctionType { giv_type: abs_type }))
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
			check_d(fst_type, fst_type_type.clone(), fst_type_context.clone()));

			let snd_type_type = synth_type(snd_type, context.clone())?;
			push_check(
				&mut errors,
			check_d(snd_type, snd_type_type.clone(), snd_type_context.clone()));

			wrap_checks(errors)
		},
		PairIntro(ref fst, ref snd) => {
			match *type_ann.data {
				PairTypeIntro(fst_type, snd_type) => {
					let mut errors = Vec::new();

					let fst_context = context.clone().inc_and_shift(2)
						.with_dec(Bound(1), snd_type.clone())
						.with_def(Bound(1), normalize(snd.clone(), context.clone().inc_and_shift(2)));
					let snd_context = context.clone().inc_and_shift(2)
						.with_dec(Bound(0), fst_type.clone())
						.with_def(Bound(0), normalize(fst.clone(), context.clone().inc_and_shift(2)));
					let normal_fst_type = normalize(fst_type, fst_context.clone());
					let normal_snd_type = normalize(snd_type, snd_context.clone());
					// println!("FST {:?}", fst);
					// println!("FST_CONTEXT {:#?}", fst_context);

					push_check(&mut errors,check_d(fst, normal_fst_type, fst_context));
					push_check(&mut errors,check_d(snd, normal_snd_type, snd_context));

					wrap_checks(errors)
				},
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfPairType { giv_type: type_ann })])
			}
		},
		PairElim(ref discrim, ref body) => {
			let discrim_type = synth_type(discrim, context.clone())?;
			// println!("CONTEXT {:?}\nDISCRIM_TYPE {:?}", context.clone(), discrim_type.clone());
		check_d(discrim, discrim_type.clone(), context.clone())?;

			match *(discrim_type.clone()).data {
				PairTypeIntro(fst_type, snd_type) => {
					let mut body_context = context.clone().inc_and_shift(2)
						.with_dec(Bound(0), fst_type.clone())
						.with_dec(Bound(1), snd_type.clone());
					let mut type_ann_context = context;
					let mut subst_context = Context::new();
					if let Var(index) = &*discrim.data {
						// let (fst_type_clone, snd_type_clone) = (fst_type.clone(), snd_type.clone()); // make this less weird later
						let new_discrim = |f, s, ft, st|
							pair!(
								f,
								s
							,:
								Pair!(
									ft,
									st
								,: Univ!()));
						let fst_var = Free(Symbol(rand::random::<usize>()));
						let snd_var = Free(Symbol(rand::random::<usize>()));
						subst_context = subst_context
							.with_def(fst_var, var!(note format!("split bound 0 l{}", term.loc.unwrap_or(Location { line: 0 }).line), Bound(0)))
							.with_def(snd_var, var!(note format!("split bound 1 l{}", term.loc.unwrap_or(Location { line: 0 }).line), Bound(1)));
						let body_discrim =
							new_discrim.clone()(
								var!(note format!("split bound 0 l{}", term.loc.unwrap_or(Location { line: 0 }).line), Bound(2)),
								var!(note format!("split bound 1 l{}", term.loc.unwrap_or(Location { line: 0 }).line), Bound(3)),
								shift(fst_type.clone(), HashSet::new(), 2),
								shift(snd_type.clone(), HashSet::new(), 2));
						body_context = body_context
							.with_def(
								Bound(index.as_bound() + 2),
								body_discrim.clone())
							.update(
								Bound(index.as_bound() + 2),
								body_discrim);
						let type_ann_discrim =
							new_discrim(
								var!(fst_var),
								var!(snd_var),
								fst_type,
								snd_type);
						type_ann_context = type_ann_context
							.with_def(
								*index,
								type_ann_discrim.clone())
							.update(*index, type_ann_discrim);
					}
				check_d(body, substitute(shift(normalize(type_ann, type_ann_context), HashSet::new(), 2), subst_context), body_context)
					// let sym_fst_id = Symbol(rand::random::<usize>());
					// let sym_fst =
					// 	Term::new(
					// 		Box::new(Var(Free(sym_fst_id))),
					// 		Some(Box::new(fst_type.clone())));
					// let sym_snd_id = Symbol(rand::random::<usize>());
					// let sym_snd =
					// 	Term::new(
					// 		Box::new(Var(Free(sym_snd_id))),
					// 		Some(Box::new(snd_type.clone())));
					// let body_context =
					// 	context.clone().inc_and_shift(2)
					// 		.with_dec(Bound(0), fst_type)
					// 		.with_dec(Bound(1), snd_type);
					// let type_ann_context =
					// 	match &*discrim.data {
					// 		Var(index) => {
					// 			let refined_discrim =
					// 				Term::new(
					// 					Box::new(PairIntro(
					// 						sym_fst.clone(),
					// 						sym_snd.clone())),
					// 					Some(Box::new(discrim_type.clone())));
					// 			context.update(*index, refined_discrim.clone()).with_def(*index, refined_discrim)
					// 		},
					// 		_ => context.clone()
					// 	};
					// let normal_type_ann = shift(normalize(type_ann, type_ann_context), HashSet::new(), 2);
					// push_check(&mut errors,check_d(body, normal_type_ann, body_context.with_equiv(Bound(0), Free(sym_fst_id)).with_equiv(Bound(1), Free(sym_snd_id))));
				}
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, discrim.loc(), context, ExpectedOfPairType { giv_type: discrim_type })])
			}
		}
		VoidTypeIntro =>
			match *(type_ann.clone()).data {
				TypeTypeIntro => Ok(()),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
        UnitTypeIntro =>
        	match *(type_ann.clone()).data {
				TypeTypeIntro => Ok(()),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
        UnitIntro =>
        	match *(type_ann.clone()).data {
				UnitTypeIntro => Ok(()),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfUnitType { giv_type: type_ann.clone() })])
			},
		DoubTypeIntro =>
			match *(type_ann.clone()).data {
				TypeTypeIntro => Ok(()),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
		DoubIntro(_) =>
			match *(type_ann.clone()).data {
				DoubTypeIntro => Ok(()),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfDoubType { giv_type: type_ann.clone() })])
			},
		DoubElim(ref discrim, ref branch1, ref branch2) => {
			let mut errors = Vec::new();

			let discrim_type = synth_type(discrim, context.clone())?;
			push_check(&mut errors,check_d(discrim, discrim_type.clone(), context.clone()));

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
					push_check(&mut errors,check_d(branch1, normalize(type_ann.clone(), branch1_context.clone()), branch1_context.clone()));
					// println!("BRANCH 2 CONTEXT {:?}", branch2_context.len());
					push_check(&mut errors,check_d(branch2, normalize(type_ann, branch2_context.clone()), branch2_context));
				},
				_ => errors.push(Error::new_o(unsafe { stack.clone() }, discrim.loc(), context, ExpectedOfDoubType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		},
		FoldTypeIntro(ref inner_type) =>
			match *(type_ann.clone()).data {
				TypeTypeIntro =>check_d(inner_type, synth_type(inner_type, context.clone())?, context.clone()),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
		FoldIntro(ref inner_term) =>
			match *(type_ann.clone()).data {
				FoldTypeIntro(inner_type) =>check_d(inner_term, inner_type, context),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfFoldType { giv_type: type_ann.clone() })])
			},
		FoldElim(ref folded_term) => {
			let folded_term_type = synth_type(folded_term, context.clone())?;
			match &*folded_term_type.data {
				FoldTypeIntro(_) =>check_d(folded_term, type_ann, context),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfFoldType { giv_type: folded_term_type })])
			}
		}
		IndexedTypeIntro(_, ref inner_type) =>
			match *(type_ann.clone()).data {
				TypeTypeIntro =>check_d(inner_type, synth_type(inner_type, context.clone())?, context.clone()),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
		IndexedIntro(ref inner_term) =>
			match *(type_ann.clone()).data {
				IndexedTypeIntro(_, inner_type) =>check_d(inner_term, inner_type, context),
				_ => Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfIndexedType { giv_type: type_ann.clone() })])
			},
		IndexedElim(ref discrim, ref body) => {
			let discrim_type = /*dbg!(*/synth_type(discrim, context.clone())/*)*/?;
		check_d(discrim, discrim_type.clone(), /*dbg!(*/context.clone()/*)*/)?;
			match *discrim_type.data {
				IndexedTypeIntro(type_index, inner_type) => {
					let mut body_context = context.clone().inc_and_shift(1).with_dec(Bound(0), shift(inner_type.clone(), HashSet::new(), 1));
					let mut type_ann_context = context;
					let mut subst_context = Context::new();
					// let inner_type_clone = shift(inner_type.clone(), HashSet::new(), 1); // make this less weird later
					if let Var(index) = &*discrim.data {
						let new_discrim = |t, tt|
							indexed!(
								t
							,:
								Indexed!(
									type_index,
									tt
								,: Univ!()));
						let bound_var = Free(Symbol(rand::random::<usize>()));
						subst_context = subst_context.with_def(bound_var, var!(note format!("indexedelim bound l{}", term.loc.unwrap_or(Location { line: 0 }).line), Bound(0)));
						let body_discrim = new_discrim.clone()(
							var!(note format!("indexedelim bound l{}", term.loc.unwrap_or(Location { line: 0 }).line), Bound(0)),
							shift(inner_type.clone(), HashSet::new(), 1));
						body_context = body_context
							.with_def(
								Bound(index.as_bound() + 1),
								body_discrim.clone())
							.update(
								Bound(index.as_bound() + 1),
								body_discrim);
						let type_ann_discrim = new_discrim(var!(bound_var), inner_type);
						type_ann_context = type_ann_context
							.with_def(*index, type_ann_discrim.clone())
							.update(*index, type_ann_discrim);
					}
				check_d(body, substitute(shift(normalize(type_ann, type_ann_context), HashSet::new(), 1), subst_context), body_context)
				},
				_ => {
					println!("{}", display_term(discrim, 0));
					Err(vec![Error::new_o(unsafe { stack.clone() }, term.loc(), context, ExpectedOfIndexedType { giv_type: discrim_type })])
				}
			}
		}
		Postulate(_) => Ok(())
	}
}