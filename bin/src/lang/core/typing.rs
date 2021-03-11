#![allow(warnings)]

use super::{
	lang::{
		*,
		VarInner::*,
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

// for the `Expected...` errors, imagine a TypeType `U` for each error, the error
// can then be thought of as `MismatchedTypes { exp_type: U, giv_type: ... }
#[derive(Debug)]
pub enum InnerError {
    MismatchedTypes { exp_type: Term, giv_type: Term, specific: Vec<(Term, Term)> },
    NonexistentVar { index: VarInner },
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

#[derive(Debug)]
pub struct Error {
    loc: Option<Location>,
    error: InnerError,
    context: Context
}

impl Error {
    pub fn new(loc: Option<Location>, context: Context, error: InnerError) -> Error {
        Error {
            loc,
            context,
            error
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
			IndexedElim(ref folded_term) => count_uses(folded_term, target_index),
			Postulate(_) => singleton(0)
		},
		match &term.type_ann {
			Some(r#type) => count_uses(r#type, target_index),
			None => singleton(0)
		}])
}

// `term` should be checked before this is called
// should make this more robust in the future
pub fn get_free_vars(term: &Term, bounds: HashSet<VarInner>) -> HashMap<VarInner, Term> {
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
				TypeTypeIntro => HashMap::new(),
				Var(index) =>
					if bounds.contains(&index) {
						HashMap::new()
					} else {
						let mut map = HashMap::new();
						map.insert(index, term.r#type(Context::new()));
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

    let r#type = term.r#type(context.clone());
    match &*r#type.data {
    	TypeTypeIntro => (),
    	_ => check(&r#type, synth_type(&r#type, context.clone())?, context)?
    }
    Ok(r#type)
}

pub fn check(term: &Term, exp_type: Term, context: Context) -> CheckResult<()> {
	use InnerError::*;

	let type_ann = synth_type(term, context.clone())?;
	if let False(specific) = is_terms_eq(&type_ann, &exp_type, context.clone().equivs()) {
		// println!("NOT EQ\n{:?}\n{:?}", type_ann, exp_type);
		return
			Err(vec![Error::new(
				term.loc(),
				context,
				MismatchedTypes { exp_type: exp_type.clone(), giv_type: type_ann.clone(), specific })]);
	}

	match *term.data {
		TypeTypeIntro =>
			match *(type_ann.clone()).data {
				TypeTypeIntro => Ok(()),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfTypeType { giv_type: type_ann })])
			},
		Var(index) => 
			match context.get_dec(index) {
				Some(var_type) => {
					if let False(specific) = is_terms_eq(&var_type, &type_ann, context.clone().equivs()) {
						Err(vec![Error::new(term.loc(), context, MismatchedTypes { exp_type: var_type, giv_type: type_ann, specific })])
					} else {
						Ok(())
					}
				}
				None => Err(vec![Error::new(term.loc(), context, NonexistentVar { index })])
			},
		Rec(ref inner_term) => {
			let mut errors = Vec::new();

			let new_context = context.clone().inc_and_shift(1).with_dec(Bound(0), type_ann.clone());

			push_check(
				&mut errors,
				check(inner_term, type_ann.clone(), new_context.clone().with_dec(Bound(0), type_ann.clone())));

			wrap_checks(errors)
		},
		Let(ref bindings, ref body) => {
			let mut errors = Vec::new();

			let mut new_context = context.inc_and_shift(bindings.len().try_into().unwrap());
			for (i, binding) in bindings.iter().enumerate() {
				let binding_type = synth_type(binding, new_context.clone())?;
				check(binding, binding_type.clone(), new_context.clone())?;

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

			let out_type_context = context.clone().inc_and_shift(1).with_dec(Bound(0), shift(in_type.clone(), HashSet::new(), 1));

			let in_type_type = synth_type(in_type, context.clone())?;
			let out_type_type = synth_type(out_type, out_type_context.clone())?;
			push_check(
				&mut errors,
				check(in_type, in_type_type.clone(), context.clone()));
			push_check(
				&mut errors,
				check(out_type, out_type_type.clone(), out_type_context));

			wrap_checks(errors)
		},
		FunctionIntro(ref body) => {
			let mut errors = Vec::new();

			match *type_ann.clone().data {
				FunctionTypeIntro(in_type, out_type) => {
					let body_context = context.clone().inc_and_shift(1).with_dec(Bound(0), shift(in_type.clone(), HashSet::new(), 1));
					push_check(&mut errors, check(body, out_type, body_context));
				},
				_ => errors.push(Error::new(term.loc(), context, ExpectedOfFunctionType { giv_type: type_ann }))
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
							Err(vec![Error::new(term.loc(), context, MismatchedTypes { exp_type: type_ann, giv_type: normal_out_type, specific })])
						} else {
							Ok(())
						});
				},
				_ => errors.push(Error::new(term.loc(), context, ExpectedOfFunctionType { giv_type: abs_type }))
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
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfPairType { giv_type: type_ann })])
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
				_ => errors.push(Error::new(discrim.loc(), context, ExpectedOfPairType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		}
		VoidTypeIntro =>
			match *(type_ann.clone()).data {
				TypeTypeIntro => Ok(()),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
        UnitTypeIntro =>
        	match *(type_ann.clone()).data {
				TypeTypeIntro => Ok(()),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
        UnitIntro =>
        	match *(type_ann.clone()).data {
				UnitTypeIntro => Ok(()),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfUnitType { giv_type: type_ann.clone() })])
			},
		DoubTypeIntro =>
			match *(type_ann.clone()).data {
				TypeTypeIntro => Ok(()),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
		DoubIntro(_) =>
			match *(type_ann.clone()).data {
				DoubTypeIntro => Ok(()),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfDoubType { giv_type: type_ann.clone() })])
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
				_ => errors.push(Error::new(discrim.loc(), context, ExpectedOfDoubType { giv_type: discrim_type }))
			}

			wrap_checks(errors)
		},
		FoldTypeIntro(ref inner_type) =>
			match *(type_ann.clone()).data {
				TypeTypeIntro => check(inner_type, synth_type(inner_type, context.clone())?, context.clone()),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
		FoldIntro(ref inner_term) =>
			match *(type_ann.clone()).data {
				FoldTypeIntro(inner_type) => check(inner_term, inner_type, context),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfFoldType { giv_type: type_ann.clone() })])
			},
		FoldElim(ref folded_term) => {
			let folded_term_type = synth_type(folded_term, context.clone())?;
			match &*folded_term_type.data {
				FoldTypeIntro(_) => check(folded_term, type_ann, context),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfFoldType { giv_type: folded_term_type })])
			}
		}
		IndexedTypeIntro(_, ref inner_type) =>
			match *(type_ann.clone()).data {
				TypeTypeIntro => check(inner_type, synth_type(inner_type, context.clone())?, context.clone()),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfTypeType { giv_type: type_ann.clone() })])
			},
		IndexedIntro(ref inner_term) =>
			match *(type_ann.clone()).data {
				IndexedTypeIntro(_, inner_type) => check(inner_term, inner_type, context),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfIndexedType { giv_type: type_ann.clone() })])
			},
		IndexedElim(ref indexed_term) => {
			let indexed_term_type = synth_type(indexed_term, context.clone())?;
			match &*indexed_term_type.data {
				IndexedTypeIntro(_, _) => check(indexed_term, type_ann, context),
				_ => Err(vec![Error::new(term.loc(), context, ExpectedOfIndexedType { giv_type: indexed_term_type })])
			}
		}
		Postulate(_) => Ok(())
	}
}