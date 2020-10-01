#![allow(warnings)]

use std::collections::HashMap;
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
}

pub enum Error<'a> {
    MismatchedTypes { term: &'a Term, state: State, exp_type: core::Term, giv_type: core::Term },
    NonexistentVar { var: &'a Term, name: Name }
}
use Error::*;

pub fn synth_type<'a>(term: &'a Term, state: State) -> Result<core::Term, Vec<Error<'a>>> {
    unimplemented!()
}

macro_rules! unwrap_checks {
    ($checks:expr) => {{
        let mut errors = Vec::new();
        let mut elabd_terms = Vec::new();
        for check in checks {
            match check {
                Err(errs) =>
                    for err in errs {
                        errors.push(err);
                    },
                Ok(term) => elabd_terms.push(term)
            }
        }
        if errors.len() > 0 {
            return Err(errors);
        } else {
            elabd_terms
        }
    }};
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
        _ => unimplemented!()
    }
}