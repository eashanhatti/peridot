#![allow(warnings)]

use std::{
    collections::HashMap,
    cmp::max
};
use crate::lang::{
	core::{
        self,
        context::{
            *,
            ContextEntryKind::*
        },
        is_terms_eq
    },
    surface::{
        *,
        InnerTerm::*
    }
};
extern crate contracts;
use contracts::*;

#[derive(Clone, Debug)]
pub struct State {
	context: Context,
    names_to_indices: HashMap<Name, usize>
}

impl State {
	pub fn new() -> State {
		State { context: Context::new(), names_to_indices: HashMap::new() }
	}

    pub fn with_dec(self, name: Name, r#type: core::Term) -> State {
        let context = self.context.inc_and_shift(1).insert_dec(0, r#type);
        let mut names_to_indices = self.names_to_indices;
        names_to_indices.iter_mut().map(|(_, i)| *i += 1);
        names_to_indices.insert(name, 0);
        State { context, names_to_indices }
    }

    // declare before use, `with_dec(name, _)` must have been called before this is
    pub fn with_def(self, name: Name, value: core::Term) -> State {
        if let Some(index) = self.names_to_indices.get(&name) {
            if self.context.exists_dec(*index) {
                State { context: self.context.insert_def(*index, value), names_to_indices: self.names_to_indices }
            } else {
                panic!("var must be declared before being given a definition")
            }
        } else {
            panic!("var must be declared before being given a definition")
        }
    }

    pub fn get(&self, name: &Name) -> Option<(usize, ContextEntry)> {
        if let Some(index) = self.names_to_indices.get(name) {
            if let Some(entry) = self.context.get(*index) {
                return Some((*index, entry));
            }
        }
        None
    }

    pub fn get_dec(&self, name: &Name) -> Option<(usize, core::Term)> {
        let entry = self.get(name)?;
        Some((entry.0, entry.1.dec?))
    }

    pub fn get_def(&self, name: &Name) -> Option<(usize, core::Term)> {
        let entry = self.get(name)?;
        Some((entry.0, entry.1.def?))
    }

    pub fn raw_context(&self) -> &Context {
        &self.context
    }
}

#[derive(Debug)]
pub enum Error<'a> {
    MismatchedTypes { term: &'a Term, state: State, exp_type: core::Term, giv_type: core::Term },
    NonexistentVar { var: &'a Term, name: Name },
    ExpectedOfTypeType { term: &'a Term, state: State, min_level: usize, giv_type: core::Term }
}
use Error::*;

pub fn synth_type<'a>(term: &'a Term, state: State) -> Result<core::Term, Vec<Error<'a>>> {
    unimplemented!()
}

macro_rules! with_terms {
    ($(let $name:ident = $check:expr);*; $body:expr) => {{
        let mut _errors = Vec::new();
        $(
            let mut $name: core::Term;
            match $check {
                Ok(elabd_term) => $name = elabd_term,
                Err(errs) =>
                    for err in errs {
                        _errors.push(err);
                    }
            }
        )*
        if _errors.len() > 0 {
            return Err(_errors);
        } else {
            $body
        }
    }};
}

fn context_to_caps_list(context: &Context) -> core::Term {
    unimplemented!()
}

// checks a surface term, and either returns the elaborated term or errors
pub fn elab<'a>(term: &'a Term, exp_type: core::Term, state: State) -> Result<core::Term, Vec<Error<'a>>> {
	match &*term.data {
        Ann(ref annd_term, ref type_ann) => {
            let core_type_ann = elab(type_ann, synth_type(type_ann, state.clone())?, state.clone())?;
            if !is_terms_eq(&core_type_ann, &exp_type) {
                return Err(vec![MismatchedTypes { term, state, exp_type: exp_type, giv_type: core_type_ann }])
            }
            elab(annd_term, core_type_ann, state)
        },
        Var(ref name) =>
            match state.get_dec(name) {
                Some((index, r#type)) =>
                    if is_terms_eq(&r#type, &exp_type) {
                        Ok(core::Term::new(Box::new(core::Var(index)), Some(Box::new(r#type))))
                    } else {
                        Err(vec![MismatchedTypes { term, state, exp_type, giv_type: r#type }])
                    },
                None => Err(vec![NonexistentVar { var: term, name: name.clone() }])
            },
        FunctionTypeIntro(var_name, ref in_type, ref out_type) => {
            // TODO: remove the `?` and add proper error handling
            let mut errors = Vec::new();
            let core_in_type = elab(in_type, synth_type(in_type, state.clone())?, state.clone())?;
            let core_out_type = elab(out_type, core_in_type.clone(), state.clone().with_dec(var_name.clone(), core_in_type.clone()))?;
            let core_in_type_type = core_in_type.r#type();
            let core_out_type_type = core_out_type.r#type();
            let caps_list = context_to_caps_list(&state.raw_context());

            match (*(core_in_type_type.clone()).data, *(core_out_type_type.clone()).data) {
                (core::TypeTypeIntro(in_level, in_usage), core::TypeTypeIntro(out_level, out_usage)) =>
                    if let core::TypeTypeIntro(max_level, pair_usage) = *exp_type.clone().data {
                        if max(in_level, out_level) != max_level {
                            errors.push(
                                MismatchedTypes {
                                    term,
                                    state,
                                    exp_type: core::Term::new(Box::new(core::TypeTypeIntro(max_level, pair_usage)), None),
                                    giv_type: core::Term::new(Box::new(core::TypeTypeIntro(max(in_level, out_level), pair_usage)), None) });
                        }
                    } else {
                        errors.push(ExpectedOfTypeType { term, state, min_level: max(in_level, out_level), giv_type: exp_type.clone() })
                    },
                (_, core::TypeTypeIntro(level, _)) =>
                    errors.push(ExpectedOfTypeType { term: in_type, state, min_level: level, giv_type: core_in_type_type }),
                (core::TypeTypeIntro(level, _), _) =>
                    errors.push(ExpectedOfTypeType { term: out_type, state, min_level: level, giv_type: core_out_type_type }),
                (_, _) =>  {
                    errors.push(ExpectedOfTypeType { term: in_type, state: state.clone(), min_level: 0, giv_type: core_in_type_type });
                    errors.push(ExpectedOfTypeType { term: out_type, state, min_level: 0, giv_type: core_out_type_type });
                }
            }

            if errors.len() > 0 {
                Err(errors)
            } else {
                Ok(core::Term::new(
                    Box::new(core::FunctionTypeIntro(
                        caps_list,
                        core_in_type,
                        core_out_type)),
                    Some(Box::new(exp_type))))
            }
        },
        _ => unimplemented!()
    }
}