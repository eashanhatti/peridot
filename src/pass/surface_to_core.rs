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
    names_to_indices: HashMap<(Name, ContextEntryKind), usize>
}

impl State {
	pub fn new() -> State {
		State { context: Context::new(), names_to_indices: HashMap::new() }
	}

    pub fn insert_dec(self: State, name: Name, r#type: core::Term) -> State {
        let context = self.context.inc_and_shift(1).insert_dec(0, r#type);
        let mut names_to_indices = self.names_to_indices;
        names_to_indices.iter_mut().map(|(_, i)| *i += 1);
        names_to_indices.insert((name, Dec), 0);
        State { context, names_to_indices }
    }

    pub fn insert_def(self: State, name: Name, r#type: core::Term) -> State {
        let context = self.context.inc_and_shift(1).insert_def(0, r#type);
        let mut names_to_indices = self.names_to_indices;
        names_to_indices.iter_mut().map(|(_, i)| *i += 1);
        names_to_indices.insert((name, Def), 0);
        State { context, names_to_indices }
    }
}

pub enum Error<'a> {
	MismatchedNumFunctionParams { func: &'a Term, state: State, exp_num: usize, giv_num: usize },
    CannotSynthType { term: &'a Term, state: State },
    MismatchedTypes { term: &'a Term, state: State, exp_type: core::Term, giv_type: core::Term }
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
        Var(ref name) => {
            unimplemented!()
        },
        _ => unimplemented!()
    }
}