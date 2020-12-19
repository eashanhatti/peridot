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
        is_terms_eq,
        lang::TermComparison::*
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
	locals: Context,
    local_names_to_indices: HashMap<Name, usize>,
    globals: HashMap<ModulePath, core::Term>
}

impl State {
	pub fn new() -> State {
        let map1: HashMap<Name, usize> = HashMap::new();
        let map2: HashMap<ModulePath, core::Term> = HashMap::new();
		State {
            locals: Context::new(),
            local_names_to_indices: map1,
            globals: map2
        }
	}

    pub fn with_dec(self, name: Name, r#type: core::Term) -> State {
        let locals = self.locals.inc_and_shift(1).with_dec(0, r#type);
        let mut local_names_to_indices = self.local_names_to_indices;
        for i in &mut local_names_to_indices.values_mut() {
            *i += 1;
        }
        local_names_to_indices.insert(name, 0);
        State { locals, local_names_to_indices, globals: self.globals }
    }

    // declare before use, `with_dec(name, _)` must have been called before this is
    pub fn with_def(self, name: Name, value: core::Term) -> State {
        if let Some(index) = self.local_names_to_indices.get(&name) {
            if self.locals.exists_dec(*index) {
                State {
                    locals: self.locals.with_def(*index, value),
                    local_names_to_indices: self.local_names_to_indices,
                    globals: self.globals
                }
            } else {
                panic!("var must be declared before being given a definition")
            }
        } else {
            panic!("var must be declared before being given a definition")
        }
    }

    pub fn get(&self, name: &Name) -> Option<(usize, ContextEntry)> {
        if let Some(index) = self.local_names_to_indices.get(name) {
            if let Some(entry) = self.locals.get(*index) {
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

    pub fn locals(self) -> Context {
        self.locals
    }
}

#[derive(Debug)]
pub enum Error<'a> {
    MismatchedTypes { term: &'a Term, state: State, exp_type: core::Term, giv_type: core::Term, specific: Vec<(core::Term, core::Term)> },
    NonexistentVar { var: &'a Term, state: State, name: Name },
    ExpectedOfTypeType { term: &'a Term, state: State, min_level: usize, giv_type: core::Term },
    ExpectedOfFunctionType { term: &'a Term, state: State, giv_type: core::Term },
    ExpectedOfEnumType { term: &'a Term, state: State, giv_type: core::Term },
    EnumInhabitantTooLarge { term: &'a Term, state: State, inhabitant: usize, num_inhabitants: usize },
    MismatchedFunctionArgsNum { func: &'a Term, state: State, exp_num: usize, giv_num: usize },
    CannotInferType { term: &'a Term, state: State }
}
use Error::*;

// term may be unchecked
pub fn infer_type<'a>(term: &'a Term, state: State) -> Result<core::Term, Vec<Error<'a>>> {
    match &*term.data {
        Ann(_, ref type_ann) => Ok(elab(type_ann, infer_type(type_ann, state.clone())?, state)?),
        TypeTypeIntro(level) => Ok(core::Term::new(Box::new(core::InnerTerm::TypeTypeIntro(level + 1, core::lang::Usage::Shared)), None)),
        Var(ref name) =>
            if let Some((_, r#type)) = state.get_dec(name) {
                Ok(r#type)
            } else {
                Err(vec![Error::NonexistentVar { var: term, state, name: name.clone() }])
            }
        FunctionTypeIntro(_, _, _) =>
            Ok(core::Term::new(
                Box::new(core::TypeTypeIntro(0, core::Usage::Shared)),
                None
            )),
        FunctionElim(ref abs, _) => {
            let abs_type = infer_type(abs, state.clone())?;
            match &*abs_type.data {
                core::InnerTerm::FunctionTypeIntro(_, _, ref out_type) => Ok(out_type.clone()),
                _ => Err(vec![ExpectedOfFunctionType { term: abs, state, giv_type: abs_type }])
            }
        },
        EnumTypeIntro(_) =>
            Ok(core::Term::new(
                Box::new(core::TypeTypeIntro(0, core::Usage::Shared)),
                None
            )),
        _ => Err(vec![Error::CannotInferType { term, state }])
    }
}

macro_rules! with_terms {
    ($(let $name:ident = $check:expr);*; $body:expr) => {{
        let mut _errors = Vec::new();
        $(
            let mut $name: core::Term;
            match $check {
                Ok(core_term) => $name = core_term,
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

type ElabResult<'a> = Result<core::Term, Vec<Error<'a>>>;

// checks a surface term, and either returns the elaborated term or errors
pub fn elab<'a>(term: &'a Term, exp_type: core::Term, state: State) -> ElabResult<'a> {
	match &*term.data {
        Ann(ref annd_term, ref type_ann) => {
            let core_type_ann = elab(type_ann, infer_type(type_ann, state.clone())?, state.clone())?;
            if let False(specific) = is_terms_eq(&core_type_ann, &exp_type) {
                return Err(vec![MismatchedTypes { term, state, exp_type: exp_type, giv_type: core_type_ann, specific }])
            }
            elab(annd_term, core_type_ann, state)
        },
        Var(ref name) => {
            match state.get_dec(name) {
                Some((index, r#type)) =>
                    if let False(specific) = is_terms_eq(&r#type, &exp_type) {
                        Err(vec![MismatchedTypes { term, state, exp_type, giv_type: r#type, specific }])
                    } else {
                        Ok(core::Term::new(Box::new(core::Var(index)), Some(Box::new(r#type))))
                    },
                None => Err(vec![NonexistentVar { var: term, state, name: name.clone() }])
            }
        },
        FunctionTypeIntro(var_name, ref in_type, ref out_type) => {
            // TODO: remove the `?` and add proper error handling
            let mut errors = Vec::new();
            let core_in_type = elab(in_type, infer_type(in_type, state.clone())?, state.clone())?;
            let core_in_type_type = core_in_type.r#type();
            let core_out_type = elab(out_type, infer_type(out_type, state.clone())?, state.clone().with_dec(var_name.clone(), core_in_type_type.clone()))?;
            let core_out_type_type = core_out_type.r#type();
            let mut caps_list = None;

            match (*(core_in_type_type.clone()).data, *(core_out_type_type.clone()).data) {
                (core::TypeTypeIntro(in_type_level, in_type_usage), core::TypeTypeIntro(out_type_level, out_usage)) =>
                    if let core::TypeTypeIntro(max_level, pair_usage) = &*exp_type.data {
                        if max(in_type_level, out_type_level) != *max_level {
                            errors.push(
                                MismatchedTypes {
                                    term,
                                    state,
                                    exp_type: core::Term::new(Box::new(core::TypeTypeIntro(*max_level, *pair_usage)), None),
                                    giv_type: core::Term::new(Box::new(core::TypeTypeIntro(max(in_type_level, out_type_level), *pair_usage)), None),
                                    specific: Vec::new() });
                        } else {
                            caps_list = Some(state.clone().locals().to_caps_list(max(in_type_level, out_type_level)));
                        }
                    } else {
                        errors.push(ExpectedOfTypeType { term, state, min_level: max(in_type_level, out_type_level), giv_type: exp_type.clone() })
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
                        caps_list.unwrap(),
                        core_in_type,
                        core_out_type)),
                    Some(Box::new(exp_type))))
            }
        },
        FunctionIntro(ref param_names, ref body) => {
            let mut exp_num_params = 0;
            let mut in_types = Vec::new();
            let mut body_state = state.clone();
            let mut curr_out_type = exp_type;
            let num_param_names = param_names.len();
            for name in param_names {
                if let core::FunctionTypeIntro(caps_list, in_type, out_type) = *curr_out_type.data {
                    exp_num_params += 1;
                    in_types.push(in_type.clone());
                    body_state = body_state.with_dec(name.clone(), in_type.clone());
                    curr_out_type = out_type;
                } else {
                    return Err(vec![ExpectedOfFunctionType { term, state, giv_type: curr_out_type }])
                }
            }
            let core_body = elab(body, curr_out_type, body_state.clone())?;
            let mut curr_locals = body_state.locals().without(0).inc_and_shift(-1);
            let mut curr_body = core_body;
            for in_type in in_types {
                let out_type = curr_body.r#type();
                let fun_kind =
                    core::Term::new(
                        Box::new(core::TypeTypeIntro(std::cmp::max(out_type.level(), in_type.level()), core::Usage::Shared)), // TODO: allow shared functions
                        None);
                let fun_type =
                    core::Term::new(
                        Box::new(core::FunctionTypeIntro(
                            curr_locals.clone().to_caps_list(std::cmp::max(out_type.level(), in_type.level())),
                            in_type,
                            out_type)),
                        Some(Box::new(fun_kind)));
                curr_locals = curr_locals.without(0).inc_and_shift(-1);
                curr_body = core::Term::new(
                    Box::new(core::FunctionIntro(curr_body)),
                    Some(Box::new(fun_type)));
            }
            Ok(curr_body)
        },
        FunctionElim(ref abs, ref args) => {
            let abs_type = infer_type(abs, state.clone())?;
            let core_abs = elab(abs, abs_type.clone(), state.clone())?; // change to not use `?` later
            if let core::InnerTerm::FunctionTypeIntro(_, _, _) = &*abs_type.data {
                ()
            } else {
                return Err(vec![ExpectedOfFunctionType { term: abs, state, giv_type: abs_type }])
            }

            let mut in_types = Vec::new();
            let mut out_types = vec![abs_type];
            while let core::InnerTerm::FunctionTypeIntro(_, in_type, out_type) = &*out_types[out_types.len() - 1].data {
                in_types.push(in_type.clone());
                out_types.push(out_type.clone());
            }
            out_types.remove(0);
            if args.len() != in_types.len() {
                return Err(vec![MismatchedFunctionArgsNum { func: term, state, exp_num: in_types.len(), giv_num: args.len() }])
            }
            let mut core_args: Vec<core::Term> = Vec::new();
            for (i, in_type) in in_types.into_iter().enumerate() {
                // change this to not use `?` later
                core_args.push(elab(&args[i], in_type, state.clone())?);
            }

            Ok(core_args.into_iter().fold(core_abs, |curr_abs, core_arg| {
                core::Term::new(
                    Box::new(core::InnerTerm::FunctionElim(curr_abs, core_arg)),
                    Some(Box::new(out_types.remove(0))))
            }))
        },
        EnumTypeIntro(num_inhabitants) =>
            match &*exp_type.data {
                core::InnerTerm::TypeTypeIntro(level, _) => {
                    use crate::lang::core::{Term, InnerTerm::*};

                    if *num_inhabitants == 0usize {
                        Ok(Term::new(
                            Box::new(IndexedTypeIntro(
                                0,
                                Term::new(
                                    Box::new(VoidTypeIntro),
                                    Some(Box::new(exp_type.clone()))))),
                            Some(Box::new(exp_type))))
                    } else {
                        let mut curr_type =
                            core::Term::new(
                                Box::new(core::InnerTerm::UnitTypeIntro),
                                Some(Box::new(exp_type.clone())));
                        for _ in 0..*num_inhabitants - 1  {
                            curr_type =
                                Term::new(
                                    Box::new(PairTypeIntro(
                                        Term::new(
                                            Box::new(DoubTypeIntro),
                                            Some(Box::new(exp_type.clone()))),
                                        Term::new(
                                            Box::new(DoubElim(
                                                Term::new(
                                                    Box::new(Var(0)),
                                                    Some(Box::new(Term::new(
                                                        Box::new(DoubTypeIntro),
                                                        Some(Box::new(exp_type.clone())))))),
                                                Term::new(
                                                    Box::new(UnitTypeIntro),
                                                    Some(Box::new(exp_type.clone()))),
                                                curr_type)),
                                            Some(Box::new(exp_type.clone()))))),
                                    Some(Box::new(exp_type.clone())));
                        }

                        Ok(Term::new(
                            Box::new(IndexedTypeIntro(0, curr_type)),
                            Some(Box::new(exp_type))))
                    }
                },
                _ => Err(vec![ExpectedOfTypeType { term, state, giv_type: exp_type, min_level: 0 }])
            },
        EnumIntro(inhabitant) => {
            fn elab_enum(term: &Term, state: State, inhabitant: usize, exp_type: core::Term) -> ElabResult {
                use self::core::InnerTerm::*;
                let of_et_err = Err(vec![ExpectedOfEnumType { term, state: state.clone(), giv_type: exp_type.clone()}]);
                let exp_type =
                    if let IndexedTypeIntro(_, inner_type) = *exp_type.data {
                        inner_type
                    } else {
                        return of_et_err;
                    };
                if let VoidTypeIntro = &*exp_type.data {
                    return Err(vec![EnumInhabitantTooLarge { term, state, inhabitant, num_inhabitants: 0 }])
                }
                
                let mut num_inhabitants = 0;
                let mut r#type = exp_type.clone();
                loop {
                    if let PairTypeIntro(fst_type, snd_type) = *r#type.data {
                        if let DoubTypeIntro = *fst_type.data { () } else { return of_et_err; }
                        if let DoubElim(discrim, left_branch, right_branch) = *snd_type.data {
                            if let Var(0) = *discrim.data { () } else { return of_et_err; }
                            if let UnitTypeIntro = *left_branch.data { () } else { return of_et_err; }
                            num_inhabitants += 1;
                            r#type = right_branch;
                        } else {
                            return of_et_err;
                        }
                    } else if let UnitTypeIntro = *r#type.data {
                        num_inhabitants += 1;
                        break;
                    } else {
                        return of_et_err;
                    }
                }
                if !(inhabitant < num_inhabitants) {
                    return Err(vec![EnumInhabitantTooLarge { term, state, inhabitant, num_inhabitants }]);
                }

                let mut enum_val =
                    core::Term::new(
                        Box::new(UnitIntro),
                        Some(Box::new(core::Term::new(
                            Box::new(UnitTypeIntro),
                            Some(Box::new(core::Term::new(
                                Box::new(TypeTypeIntro(exp_type.level(), exp_type.usage())),
                                None)))))));
                let mut r#type = exp_type;
                for _ in 0..inhabitant {
                    if let PairTypeIntro(fst_type, snd_type) = *r#type.clone().data {
                        enum_val =
                            core::Term::new(
                                Box::new(PairIntro(
                                    core::Term::new(
                                        Box::new(DoubIntro(core::Doub::That)),
                                        Some(Box::new(fst_type))),
                                    enum_val)),
                                Some(Box::new(r#type)));
                        r#type = snd_type;
                    } else {
                        panic!();
                    }
                }

                Ok(enum_val)
            }
            elab_enum(term, state, *inhabitant, exp_type)
        },
        TypeTypeIntro(level) =>
            match *exp_type.data {
                core::TypeTypeIntro(type_level, usage) =>
                    if *level < type_level {
                        Ok(core::Term::new(
                            Box::new(core::InnerTerm::TypeTypeIntro(*level, core::Usage::Shared)),
                            Some(Box::new(core::Term::new(
                                Box::new(core::InnerTerm::TypeTypeIntro(type_level, usage)),
                                None)))))
                    } else {
                        Err(vec![ExpectedOfTypeType { term, state, min_level: level + 1, giv_type: exp_type }])
                    }
                _ => Err(vec![ExpectedOfTypeType { term, state, min_level: 0, giv_type: exp_type }])
            }
        _ => unimplemented!()
    }
}