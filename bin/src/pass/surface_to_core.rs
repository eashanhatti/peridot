#![allow(warnings)]

use std::{
    collections::{
        HashSet,
        hash_map::{
            HashMap,
            Iter
        }
    },
    cmp::max
};
use crate::{
    lang::{
    	core::{
            self,
            context::{
                *,
                ContextEntryKind::*
            },
            is_terms_eq,
            eval::shift,
            lang::{
                TermComparison::*,
                Usage,
                Note,
                VarInner::*,
                VarInner,
                Symbol
            },
        },
        surface::{
            *,
            InnerTerm::*
        }
    }
};
extern crate rand;
extern crate assoc_collections;
use assoc_collections::*;

#[macro_use]
mod syntax {
    macro_rules! Univ {
        ($level:expr, shared) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::TypeTypeIntro($level, Usage::Shared)),
                None)
        };
        ($level:expr, unique) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::TypeTypeIntro($level, Usage::Unique)),
                None)
        };
        ($level:expr, shared,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::TypeTypeIntro($level, Usage::Shared)),
                Some(Box::new($ann)))
        };
        ($level:expr, unique,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::TypeTypeIntro($level, Usage::Unique)),
                Some(Box::new($ann)))
        }
    }

    macro_rules! var {
        ($index:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::Var($index)),
                None)
        };
        ($index:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::Var($index)),
                Some(Box::new($ann)))
        };
        ($index:expr, $note:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new_with_note(
                Note(String::from($note)),
                Box::new(crate::lang::core::lang::InnerTerm::Var($index)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! pair {
        ($fst:expr, $snd:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::PairIntro(
                    $fst,
                    $snd)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! Pair {
        ($fst_type:expr, $snd_type:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::PairTypeIntro(
                    $fst_type,
                    $snd_type)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! split {
        ($discrim:expr, in $body:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::PairElim(
                    $discrim,
                    $body)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! Doub {
        (,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::DoubTypeIntro),
                Some(Box::new($ann)))
        };
        ($note:expr ,: $ann:expr) => {
            crate::lang::core::lang::Term::new_with_note(
                Note(String::from($note)),
                Box::new(crate::lang::core::lang::InnerTerm::DoubTypeIntro),
                Some(Box::new($ann)))
        };
    }

    macro_rules! doub {
        (this,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::DoubIntro(crate::lang::core::lang::Doub::This)),
                Some(Box::new($ann)))
        };
        (that,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::DoubIntro(crate::lang::core::lang::Doub::That)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! case {
        ($discrim:expr, l => $lbranch:expr; r => $rbranch:expr;,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::DoubElim(
                    $discrim,
                    $lbranch,
                    $rbranch)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! unit {
        (,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::UnitIntro),
                Some(Box::new($ann)))
        };
    }

    macro_rules! Unit {
        (,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::UnitTypeIntro),
                Some(Box::new($ann)))
        };
        ($note:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new_with_note(
                Note(String::from($note)),
                Box::new(crate::lang::core::lang::InnerTerm::UnitTypeIntro),
                Some(Box::new($ann)))
        };
    }

    macro_rules! Void {
        (,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::VoidTypeIntro),
                Some(Box::new($ann)))
        };
        ($note:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new_with_note(
                Note(String::from($note)),
                Box::new(crate::lang::core::lang::InnerTerm::VoidTypeIntro),
                Some(Box::new($ann)))
        };
    }

    macro_rules! pi {
        ($in_type:expr, $out_type:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::FunctionTypeIntro(
                    $in_type,
                    $out_type)),
                Some(Box::new($ann)))
        };
        ($note:expr, $in_type:expr, $out_type:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new_with_note(
                Note(String::from($note)),
                Box::new(crate::lang::core::lang::InnerTerm::FunctionTypeIntro(
                    $in_type,
                    $out_type)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! fun {
        ($body:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::FunctionIntro($body)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! rec {
        ($body:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::Rec($body)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! apply {
        ($abs:expr, $arg:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::FunctionElim(
                    $abs,
                    $arg)),
                None)
        };
        ($abs:expr, $arg:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::FunctionElim(
                    $abs,
                    $arg)),
                Some(Box::new($ann)))
        };

    }

    macro_rules! postulate {
        ($sym:expr ,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::Postulate($sym)),
                Some(Box::new($ann)))
        };
    }

    macro_rules! Indexed {
        ($index:expr, $inner:expr,: $ann:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::IndexedTypeIntro($index, $inner)),
                Some(Box::new($ann)))  
        };
    }

    macro_rules! let_bind {
        ($bindings:expr, $body:expr) => {
            crate::lang::core::lang::Term::new(
                Box::new(crate::lang::core::lang::InnerTerm::Let(
                    $bindings,
                    $body)),
                None)
        };
    }
}

// globals maps names to type id pairs
// id is used to calculate the arg needed to pass to the globals map at index zero in order to get that global term
// global_id is used as a source of fresh ids
#[derive(Clone, Debug)]
pub struct State {
	locals: Context,
    local_names_to_indices: HashMap<Name, VarInner>,
    globals: HashMap<QualifiedName, (core::Term, core::Term, usize)>, // dec, def, id
    global_id: usize,
    globals_map_index: usize,
    num_global_decs: usize
}

impl State {
	pub fn new(num_global_decs: usize) -> State {
        let map1: HashMap<Name, VarInner> = HashMap::new();
        let map2: HashMap<QualifiedName, (core::Term, core::Term, usize)> = HashMap::new();
		State {
            locals: Context::new(),
            local_names_to_indices: map1,
            globals: map2,
            global_id: 0,
            globals_map_index: 0,
            num_global_decs
        }
	}

    pub fn with_dec(self, name: Name, r#type: core::Term) -> State {
        let mut local_names_to_indices: HashMap<Name, VarInner> =
            self.local_names_to_indices.into_iter().map(|(k, v)|
                if let Bound(index) = v {
                    (k, Bound(index + 1))
                } else {
                    (k, v)
                }).collect();
        local_names_to_indices.insert(name, Bound(0));

        State {
            locals: self.locals.inc_and_shift(1).with_dec(Bound(0), shift(r#type, HashSet::new(), 1)),
            local_names_to_indices,
            globals_map_index: self.globals_map_index + 1,
            ..self
        }
    }

    // declare before use, `with_dec(name, _)` must have been called before this is
    pub fn with_def(self, name: Name, value: core::Term) -> State {
        if let Some(index) = self.local_names_to_indices.get(&name) {
            if self.locals.exists_dec(*index) {
                State {
                    locals: self.locals.with_def(*index, value),
                    ..self
                }
            } else {
                panic!("var must be declared before being given a definition")
            }
        } else {
            panic!("var must be declared before being given a definition")
        }
    }

    pub fn get(&self, name: &Name) -> Option<(VarInner, ContextEntry)> {
        if let Some(index) = self.local_names_to_indices.get(name) {
            if let Some(entry) = self.locals.get(*index) {
                return Some((*index, entry));
            }
        }
        None
    }

    pub fn get_dec(&self, name: &Name) -> Option<(VarInner, core::Term)> {
        let entry = self.get(name)?;
        Some((entry.0, entry.1.dec?))
    }

    pub fn get_def(&self, name: &Name) -> Option<(VarInner, core::Term)> {
        let entry = self.get(name)?;
        Some((entry.0, entry.1.def?))
    }

    pub fn with_global_dec(self, name: QualifiedName, r#type: core::Term) -> State {
        if let Some(_) = self.globals.get(&name) {
            panic!("duplicate global");
        } else {
            let mut globals = self.globals;
            globals.insert(name, (r#type.clone(), postulate!(Symbol(rand::random::<usize>()) ,: r#type), self.global_id));
            State {
                globals,
                global_id: self.global_id + 1,
                ..self
            }
        }
    }

    pub fn with_global_def(mut self, name: QualifiedName, value: core::Term) -> State {
        if let Some((r#type, _, id)) = self.globals.get(&name) {
            self.globals.insert(name, (r#type.clone(), value.clone(), *id));
            self
        } else {
            panic!("undeclared global {:?}", name);
        }
    }

    pub fn get_global_dec(&self, name: &QualifiedName) -> Option<(core::Term, usize)> {
        if let Some(entry) = self.globals.get(name) {
            Some((entry.0.clone(), entry.2))
        } else {
            None
        }
    }

    pub fn get_global_def(&self, name: QualifiedName) -> Option<(core::Term, usize)> {
        if let Some((_, value, id)) = self.globals.get(&name) {
            Some((value.clone(), *id))
        } else {
            None
        }
    }

    pub fn iter_globals(&self) -> GlobalsIterator {
        GlobalsIterator {
            id: Some(0),
            globals: &self.globals
        }
    }

    pub fn iter_globals_rev(&self) -> GlobalsIterator {
        GlobalsIterator {
            id: Some(self.globals.len()),
            globals: &self.globals
        }
    }

    pub fn with_globals_map_index(self, index: usize) -> State {
        State {
            globals_map_index: index,
            ..self
        }
    }

    pub fn locals(self) -> Context {
        self.locals
    }

    pub fn globals(self) -> HashMap<QualifiedName, (core::Term, core::Term, usize)> {
        self.globals
    }
}

pub struct GlobalsIterator<'a> {
    id: Option<usize>,
    globals: &'a HashMap<QualifiedName, (core::Term, core::Term, usize)>
}

impl Iterator for GlobalsIterator<'_> {
    type Item = (QualifiedName, core::Term, core::Term, usize);

    fn next(&mut self) -> Option<Self::Item> {
        if self.id.is_none() { return None; }
        for (name, (r#type, value, id)) in self.globals {
            if *id == self.id.unwrap() {
                self.id = Some(self.id.unwrap() + 1);
                return Some((name.clone(), r#type.clone(), value.clone(), *id)); // TODO: fix clone overuse
            }
        }
        None
    }
}

impl DoubleEndedIterator for GlobalsIterator<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.id.is_none() { return None; }
        for (name, (r#type, value, id)) in self.globals {
            if *id == self.id.unwrap() {
                if let Some(ref mut self_id) = self.id {
                    *self_id -= 1;
                } else {
                    self.id = None;
                }
                return Some((name.clone(), r#type.clone(), value.clone(), *id)); // TODO: fix clone overuse
            }
        }
        None
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
    CannotInferType { term: &'a Term, state: State },
    NonexistentGlobal { import: &'a Term, state: State, name: QualifiedName }
}
use Error::*;

type ElabResult<'a> = Result<core::Term, Vec<Error<'a>>>;

// term may be unchecked
pub fn infer_type<'a>(term: &'a Term, state: State) -> ElabResult<'a> {
    match &*term.data {
        Ann(_, ref type_ann) => Ok(elab_term(type_ann, infer_type(type_ann, state.clone())?, state)?),
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
                core::InnerTerm::FunctionTypeIntro(_, ref out_type) => Ok(out_type.clone()),
                _ => Err(vec![ExpectedOfFunctionType { term: abs, state, giv_type: abs_type }])
            }
        },
        EnumTypeIntro(_) =>
            Ok(core::Term::new(
                Box::new(core::TypeTypeIntro(0, core::Usage::Shared)),
                None
            )),
        ImportTerm(path) =>
            match state.get_global_dec(path) {
                Some((r#type, _)) => Ok(r#type),
                None => Err(vec![NonexistentGlobal { import: term, state, name: path.clone() }])
            },
        _ => Err(vec![Error::CannotInferType { term, state }])
    }
}

fn make_enum(inhabitant: usize, num_inhabitants: usize) -> core::Term {
    let r#type = make_enum_type(num_inhabitants);
    if inhabitant == 0 {
        if num_inhabitants > 1 {
            pair!(
                doub!(this ,: Doub!( ,: Univ!(0, shared))),
                unit!( ,: Unit!( ,: Univ!(0, shared)))
            ,: make_enum_type(num_inhabitants))
        } else {
            unit!( ,: Unit!( ,: Univ!(0, shared)))
        }
    } else {
        pair!(
            doub!(that ,: Doub!( ,: Univ!(0, shared))),
            make_enum(inhabitant - 1, num_inhabitants - 1)
        ,: r#type)
    }
}

fn make_enum_type(num_inhabitants: usize) -> core::Term {
    if num_inhabitants == 0 {
        Void!( ,: Univ!(0, shared))
    } else if num_inhabitants == 1 {
        Unit!( ,: Univ!(0, shared))
    } else {
        Pair!(
            Doub!( ,: Univ!(0, shared)),
            case!(
                var!(Bound(0) ,: Doub!( ,: Univ!(0, shared))),
                l => Unit!( ,: Univ!(0, shared));
                r => make_enum_type(num_inhabitants - 1);
            ,: Univ!(0, shared))
        ,: Univ!(0, shared))
    }
}

// checks a surface term, and either returns the elaborated term or errors
pub fn elab_term<'a>(term: &'a Term, exp_type: core::Term, state: State) -> ElabResult<'a> {
    match &*term.data {
        Ann(ref annd_term, ref type_ann) => {
            let core_type_ann = elab_term(type_ann, infer_type(type_ann, state.clone())?, state.clone())?;
            let cmp = is_terms_eq(&core_type_ann, &exp_type, state.clone().locals().equivs());
            if let False(specific) = cmp {
                return Err(vec![MismatchedTypes { term, state, exp_type: exp_type, giv_type: core_type_ann, specific }])
            }
            elab_term(annd_term, core_type_ann, state)
        },
        Var(ref name) => {
            match state.get_dec(name) {
                Some((index, var_type)) => {
                    let cmp = is_terms_eq(&var_type, &exp_type, state.clone().locals().equivs());
                    if let False(specific) = cmp {
                        Err(vec![MismatchedTypes { term, state, exp_type, giv_type: var_type, specific }])
                    } else {
                        Ok(core::Term::new_with_note(Note(format!("{:?}", name)), Box::new(core::Var(index)), Some(Box::new(var_type))))
                    }
                },
                None => Err(vec![NonexistentVar { var: term, state, name: name.clone() }])
            }
        },
        FunctionTypeIntro(var_name, ref in_type, ref out_type) => {
            // TODO: remove the `?` and add proper error handling
            let mut errors = Vec::new();
            let core_in_type = elab_term(in_type, infer_type(in_type, state.clone())?, state.clone())?;
            // println!("IN_TYPE\n{:?}", in_type);
            // println!("CORE_IN_TYPE\n{:?}", core_in_type);
            let core_in_type_type = core_in_type.r#type();
            let core_out_type = elab_term(out_type, infer_type(out_type, state.clone())?, state.clone().with_dec(var_name.clone(), core_in_type.clone()))?;
            // println!("OUT_TYPE\n{:?}", out_type);
            // println!("CORE_OUT_TYPE\n{:?}", core_out_type);
            let core_out_type_type = core_out_type.r#type();

            match (*(core_in_type_type.clone()).data, *(core_out_type_type.clone()).data) {
                (core::TypeTypeIntro(in_type_level, in_type_usage), core::TypeTypeIntro(out_type_level, out_usage)) =>
                    if let core::TypeTypeIntro(max_level, pair_usage) = &*exp_type.data {
                        if max(in_type_level, out_type_level) > *max_level {
                            errors.push(
                                MismatchedTypes {
                                    term,
                                    state,
                                    exp_type: core::Term::new(Box::new(core::TypeTypeIntro(*max_level, *pair_usage)), None),
                                    giv_type: core::Term::new(Box::new(core::TypeTypeIntro(max(in_type_level, out_type_level), *pair_usage)), None),
                                    specific: Vec::new() });
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
                        core_in_type,
                        core_out_type)),
                    Some(Box::new(exp_type))))
            }
        },
        FunctionIntro(ref param_names, ref body) => {
            let mut in_types = Vec::new();
            let mut curr_type = exp_type.clone();
            let mut curr_univ_level = 0;
            let mut curr_state = state.clone();
            for param_name in param_names {
                if let self::core::lang::InnerTerm::FunctionTypeIntro(in_type, out_type) = *curr_type.data {
                    in_types.push(in_type.clone());
                    curr_type = out_type;
                    curr_univ_level = max(curr_univ_level, in_type.level());
                    curr_state = curr_state.with_dec(param_name.clone(), in_type);
                } else {
                    let giv_type = {
                        let mut type_acc = curr_type;
                        for in_type in in_types {
                            type_acc = 
                                pi!(
                                    in_type,
                                    type_acc
                                ,: Univ!(curr_univ_level, shared));
                        }
                        type_acc
                    };
                    return Err(vec![MismatchedTypes { term, state, exp_type, giv_type, specific: Vec::new() }]);
                }
            }

            // println!("CURR_STATE\n{:?}", curr_state);
            let mut body_acc = elab_term(body, curr_type, curr_state)?;
            for in_type in in_types.into_iter().rev() {
                let body_acc_type = body_acc.r#type();
                body_acc =
                    fun!(
                        body_acc
                    ,:
                        pi!(
                            in_type,
                            body_acc_type
                        ,: Univ!(curr_univ_level, shared)));
            }
            Ok(body_acc)
        },
        FunctionElim(ref abs, ref args) => {
            let abs_type = infer_type(abs, state.clone())?;
            let core_abs = elab_term(abs, abs_type.clone(), state.clone())?; // change to not use `?` later
            if let core::InnerTerm::FunctionTypeIntro(_, _) = &*abs_type.data {
                ()
            } else {
                return Err(vec![ExpectedOfFunctionType { term: abs, state, giv_type: abs_type }])
            }

            let mut in_types = Vec::new();
            let mut out_types = vec![abs_type];
            while let core::InnerTerm::FunctionTypeIntro(in_type, out_type) = &*out_types[out_types.len() - 1].data {
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
                core_args.push(elab_term(&args[i], in_type, state.clone())?);
            }

            Ok(core_args.into_iter().fold(core_abs, |curr_abs, core_arg| {
                core::Term::new(
                    Box::new(core::InnerTerm::FunctionElim(curr_abs, core_arg)),
                    Some(Box::new(out_types.remove(0))))
            }))
        },
        EnumTypeIntro(num_inhabitants) => {
            match &*exp_type.data {
                core::InnerTerm::TypeTypeIntro(level, _) =>
                    Ok(Indexed!(
                        0,
                        make_enum_type(*num_inhabitants)
                    ,: Univ!(*level, shared))),
                _ => Err(vec![ExpectedOfTypeType { term, state, giv_type: exp_type, min_level: 0 }])
            }
        },
        EnumIntro(inhabitant) =>
            if let self::core::lang::InnerTerm::IndexedTypeIntro(0, inner_type) = *exp_type.clone().data {
                use self::core::lang::{
                    Term,
                    InnerTerm::*,
                    Doub
                };

                let mut num_inhabitants = 0;
                let mut curr_type = inner_type;
                if let &VoidTypeIntro = &*curr_type.data {
                    ()
                } else if let &UnitTypeIntro = &*curr_type.data {
                    num_inhabitants = 1;
                } else {
                    while let PairTypeIntro(fst_type, snd_type) = *curr_type.data {
                        if let (DoubTypeIntro, DoubElim(discrim, branch1, branch2)) = (*fst_type.data.clone(), *snd_type.data.clone()) {
                            if let (Var(Bound(0)), DoubTypeIntro, UnitTypeIntro) = (*discrim.data.clone(), *discrim.r#type().data, *branch1.data.clone()) {
                                curr_type = branch2;
                                num_inhabitants += 1;
                            } else {/*
                                println!("num_inhabitants {:?}", num_inhabitants);
                                println!("discrim {:?}", discrim);
                                println!("branch1 {:?}", branch1);
                                panic!();*/
                                return Err(vec![ExpectedOfEnumType { term, state, giv_type: exp_type }]);
                            }
                        } else {/*
                            println!("num_inhabitants {:?}", num_inhabitants);
                            println!("fst_type {:?}", fst_type);
                            println!("snd_type {:?}", snd_type);
                            panic!();*/
                            return Err(vec![ExpectedOfEnumType { term, state, giv_type: exp_type }]);
                        }
                    }
                }

                if !(*inhabitant < num_inhabitants) {
                    return Err(vec![EnumInhabitantTooLarge { term, state, inhabitant: *inhabitant, num_inhabitants }]);
                }

                let enum_val = make_enum(*inhabitant, num_inhabitants);
                let enum_type = enum_val.r#type();
                // println!("INHAB {:?} NUM_INHAB {:?}", *inhabitant, num_inhabitants);
                // println!("VAL {:?}\nTYPE {:?}", enum_val, enum_type);
                Ok(Term::new(
                    Box::new(IndexedIntro(enum_val)),
                    Some(Box::new(Term::new(
                        Box::new(IndexedTypeIntro(
                            0,
                            enum_type)),
                        Some(Box::new(Univ!(0, shared))))))))
            } else {
                Err(vec![ExpectedOfEnumType { term, state, giv_type: exp_type }])
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
            },
        ImportTerm(path) => {
            // println!("GLOBALS {:#?}", state.clone().globals());
            // println!("INDEX {:?}", state.globals_map_index);
            // println!("TO {:?}", state.clone());
            let (item_type, id) =
                if let Some(entry) = state.get_global_dec(path) {
                    entry
                } else {
                    return Err(vec![NonexistentGlobal { import: term, state, name: path.clone() }]);
                };
            let mut global_types = {
                let mut map: HashMap<usize, core::Term> = HashMap::new();
                for (_, (global_type, _, global_id)) in state.globals.iter() {
                    // println!("GT {:?}", global_type);
                    map.insert(*global_id, global_type.clone());
                }
                for i in 0..state.num_global_decs {
                    if let Some(_) = map.get(&i) {
                        ()
                    } else {
                        // an import should never normalize down to this. if it ever does it will be ill-typed
                        map.insert(i, postulate!(Symbol(rand::random::<usize>()) ,: Univ!(0, shared)));
                    }
                }
                let mut map = map.into_iter().collect::<Vec<(usize, core::Term)>>();
                map.sort_by(|(id1, _), (id2, _)| id1.cmp(id2));
                map.into_iter()
                    .map(|(_, r#type)| r#type)
                    .collect::<Vec<core::Term>>()
            };
            fn make_discrim(id: usize, num_globals: usize) -> core::Term {
                    let r#type = make_discrim_type(num_globals);
                    if id == 0 {
                        if num_globals > 1 {
                            pair!(
                                unit!( ,: Unit!( ,: Univ!(0, shared))),
                                doub!(this ,: Doub!( ,: Univ!(0, shared)))
                            ,: r#type)
                        } else {
                            unit!( ,: Unit!( ,: Univ!(0, shared)))
                        }
                    } else {
                        pair!(
                            make_discrim(id - 1, num_globals - 1),
                            doub!(that ,: Doub!( ,: Univ!(0, shared)))
                        ,: r#type)
                    }
            }

            fn make_discrim_type(num_globals: usize) -> core::Term {
                if num_globals == 0 {
                    unreachable!()
                } else if num_globals == 1 {
                    Unit!( ,: Univ!(0, shared))
                } else {
                    Pair!(
                        case!(
                            var!(Bound(1), "import discrim_type" ,: Doub!( ,: Univ!(0, shared))),
                            l => Unit!( ,: Univ!(0, shared));
                            r => make_discrim_type(num_globals - 1);
                        ,: Univ!(0, shared)),
                        Doub!( ,: Univ!(0, shared))
                    ,: Univ!(0, shared))
                }
            }

            // println!("NUM GD{:?}", state.num_global_decs);
            let discrim = make_discrim(id, state.num_global_decs);
            // println!("DISCRIM {:?}", discrim);
            // println!("DISCRIM_TYPE {:?}", discrim.r#type());
            let global_map_type = {
                let mut global_map_type = global_types.pop().unwrap();
                let len = global_types.len();
                let mut c = 0;
                for (i, global_type) in global_types.into_iter().rev().enumerate() {
                    // println!("I {:?} LEN - 1 {:?} GMI {:?}", i, len - 1, state.globals_map_index);
                    c += 1;
                    let core_map_case_type =
                        case!(
                            var!(
                                Bound(1),
                                format!("case {:?}", c).as_str()
                            ,: Doub!( ,: Univ!(0, shared))),
                            l => global_type;
                            r => global_map_type;
                        ,: Univ!(42, shared));
                    let core_map_split_type =
                        split!(
                            var!(
                                // if i == len - 1 { Bound(state.globals_map_index) } else { Bound(0) }
                                Bound(0),
                                format!("split {:?}", c).as_str()
                            ,: make_discrim_type(i + 2)),
                            in core_map_case_type.clone()
                        ,: Univ!(42, shared));
                    global_map_type = core_map_split_type;
                }
                pi!(
                    discrim.r#type(),
                    global_map_type
                ,: Univ!(42, shared))
            };
            // println!("GMI {:?}", state.globals_map_index);
            let mut core_term =
                apply!(
                    var!(
                        Bound(state.globals_map_index)
                    ,: global_map_type),
                    discrim
                ,: item_type);
            // if let None = state.get_global_def(path.clone()) {
            //     let core_term_type = core_term.r#type();
            //     core_term =
            //         core::Term::new(
            //             Box::new(core::InnerTerm::FoldIntro(core_term)),
            //             Some(Box::new(core::Term::new(
            //                 Box::new(core::InnerTerm::FoldTypeIntro(core_term_type)),
            //                 Some(Box::new(Univ!(0, shared)))))));
            // }
            Ok(core_term)
        }
        _ => unimplemented!()
    }
}

pub fn elab_toplevel<'a>(module: &'a Module, module_name: QualifiedName) -> ElabResult<'a> {
    fn calc_num_decs(module: &Module) -> usize {
        let mut n = 0;
        for (_, item) in module.items.iter() {
            match item {
                Item::Declaration(r#type) => n += 1,
                Item::ModuleDef(submodule) => n += calc_num_decs(submodule),
                _ => ()
            }
        }
        n
    }

    let starting_info = calc_num_decs(module);
    elab_module(module, module_name, State::new(starting_info))
}

fn elab_module<'a>(module: &'a Module, module_name: QualifiedName, state: State) -> ElabResult<'a> {
    #[derive(Debug)]
    enum FlattenedModuleItem<'a> { // local item type for module flattening
        Declaration(&'a crate::lang::surface::Term),
        TermDef(&'a crate::lang::surface::Term),
        RecordTypeDef(&'a HashMap<Name, crate::lang::surface::Term>),
    }

    // flatten the module structure, turning it into a more haskell-like structure
    fn flatten_module(module: &Module, module_name: QualifiedName) -> AssocVec<(QualifiedName, ItemKind), FlattenedModuleItem> {
        let mut items = AssocVec::new();
        // println!("ITEMS\n{:#?}", module.items);
        for ((item_name, _), item) in module.items.iter() {
            // println!("ITEM_NAME {:?}", item_name);
            match item {
                Item::Declaration(r#type) => { items.insert((module_name.clone().with_name(item_name.clone()), ItemKind::Dec), FlattenedModuleItem::Declaration(r#type)); },
                Item::TermDef(term) => { items.insert((module_name.clone().with_name(item_name.clone()), ItemKind::Def), FlattenedModuleItem::TermDef(term)); },
                Item::RecordTypeDef(fields) => { items.insert((module_name.clone().with_name(item_name.clone()), ItemKind::Def), FlattenedModuleItem::RecordTypeDef(fields)); },
                Item::ModuleDef(submodule) => {
                    let mut flat = flatten_module(submodule, module_name.clone().with_name(item_name.clone()));
                    while flat.len() > 0 {
                        let (key, val) = flat.remove_entry(0);
                        items.insert(key, val);
                    }
                }
            }
        }

        items
    }

    let items = flatten_module(module, module_name);
    // elaborated module items and new state with all the new global declarations in it
    // global declarations are needed for their ids, so `ImportTerm` can calculate the needed arg to the globals map to get the definition
    let (mut core_items, level) = {
        let mut state = state;
        let mut level = 0;
        let indices = {
            let num_decls = {
                let mut n = 0;
                for (_, item) in items.iter() {
                    if let FlattenedModuleItem::Declaration(_) = item {
                        n += 1;
                    }
                }
                n
            };

            let mut indices: Vec<usize> = Vec::new();
            let mut curr_index = 1;
            for _ in 0..num_decls - 1 {
                curr_index += 2;
                indices.push(curr_index);
            }
            indices.push(curr_index);
            indices
        };
        let decs_symbols = {
            let mut symbols = Vec::new();
            for (_, item) in items.iter() {
                if let FlattenedModuleItem::Declaration(_) = item {
                    symbols.push(Symbol(rand::random::<usize>()));
                }
            }
            symbols
        };
        // println!("INDICES {:?}", indices);
        let mut decs_indices_iter = indices.iter();
        let mut defs_indices_iter = indices.iter();

        // println!("ITEMS\n{:#?}", items);

        let mut core_items = Vec::new();
        for ((name, kind), item) in items.iter() {
            // println!("NAME {:?} KIND {:?}", name, kind);
            match item {
                FlattenedModuleItem::Declaration(r#type) => {
                    let core_type = elab_term(r#type, infer_type(r#type, state.clone())?, state.clone())?;
                    level = std::cmp::max(level, core_type.level());
                    let mut globals_iter = state.iter_globals();
                    let mut decs_symbols_iter = decs_symbols.iter();
                    let mut core_map = 
                        if state.globals.len() == 0 {
                            unit!( ,: var!(Free(Symbol(rand::random::<usize>())), "no globals" ,: Univ!(0, shared)))
                        } else {
                            let (_, r#type, value, _) = globals_iter.next().unwrap();
                            value
                        };

                    for ((_, r#type, value, _), symbol) in globals_iter.zip(decs_symbols_iter) {
                        core_map =
                            split!(
                                var!(
                                    Bound(0)
                                ,: postulate!(Symbol(rand::random::<usize>()) ,: Univ!(0, shared))),
                                in
                                    case!(
                                        var!(
                                            Bound(1)
                                        ,: Doub!( ,: Univ!(0, shared))),
                                        l => value;
                                        r => core_map;
                                    ,: postulate!(Symbol(rand::random::<usize>()) ,: Univ!(0, shared)))
                            ,: postulate!(Symbol(rand::random::<usize>()) ,: Univ!(0, shared)));
                    }
                    core_map = fun!(core_map ,: postulate!(Symbol(rand::random::<usize>()) ,: Univ!(0, shared)));
                    // println!("CORE_MAP\n{:?}", core_map);
                    // why does Bound(0) work?
                    let normal_core_type = core::eval::normalize(core_type, Context::new().with_def(Bound(0), core_map));
                    // println!("NCT\n{:?}", normal_core_type);

                    state =
                        state.with_global_dec(
                            name.clone(),
                            normal_core_type);
                }
                FlattenedModuleItem::TermDef(term) => {
                    let core_item_type = state.get_global_dec(name).unwrap().0; // TODO: error reporting
                    let mut core_term =
                        elab_term(
                            term,
                            core_item_type.clone(),
                            state.clone().with_globals_map_index((*defs_indices_iter.next().unwrap())))?;
                    core_term.type_ann = Some(Box::new(core_item_type));
                    core_term.note = Some(Note(format!("item {:?}", name)));
                    state = state.with_global_def(name.clone(), core_term.clone());
                    // println!("CORE_TERM {:?}", term);
                    core_items.push(core_term);
                }
                _ => ()
            }
        }

        (core_items, level)
    };
    let core_module = {
        use self::core::{
            Term,
            InnerTerm::*
        };
        let num_items = core_items.len();
        let mut core_map = core_items.pop().unwrap();
        let mut discrim_type = Unit!("discrim_unit" ,: Univ!(0, shared));
        let mut let_items = Vec::new();
        let_items.push(
            fun!(
                    core_map.r#type()
                ,:
                    pi!(
                        discrim_type.clone(),
                        Univ!(level, shared)
                    ,: Univ!(level, shared))));
        for (i, core_item) in core_items.into_iter().enumerate().rev() {
            let discrim_case_type =
                case!(
                    var!(
                        Bound(0),
                        format!("discrim_type").as_str()
                    ,: Doub!(format!("discrim_type").as_str() ,: Univ!(0, shared))),
                    l => Unit!("discrim unit l" ,: Univ!(0, shared));
                    r => discrim_type.clone();
                ,: Univ!(0, shared));

            let core_map_case_type =
                fun!(
                    fun!(
                        case!(
                            var!(
                                Bound(1),
                                format!("core_map_type_case").as_str()
                            ,: Doub!(format!("core_map_type_case").as_str() ,: Univ!(0, shared))),
                            l => core_item.r#type();
                            r =>
                                apply!(
                                    var!(Bound((let_items.len() - 1) + 2)), // + 2 since the two funs inc context by 2
                                    var!(Bound(0)));
                        ,: Univ!(level, shared))
                    ,:
                        pi!(
                            discrim_case_type.clone(),
                            Univ!(level, shared)
                        ,: Univ!(level, shared)))
                ,:
                    pi!(
                        Doub!(format!("core_map_type_case").as_str() ,: Univ!(0, shared)),
                        pi!(
                            discrim_case_type.clone(),
                            Univ!(level, shared)
                        ,: Univ!(level, shared))
                    ,: Univ!(level, shared)));
            let_items.push(core_map_case_type);

            discrim_type =
                Pair!(
                    if i == num_items - 2 {
                        Unit!( ,: Univ!(0, shared))
                    } else {
                        case!(
                            var!(
                                Bound(1),
                                format!("discrim_type").as_str()
                            ,: Doub!(format!("discrim_type").as_str() ,: Univ!(0, shared))),
                            l => Unit!("discrim unit l" ,: Univ!(0, shared));
                            r => discrim_type.clone();
                        ,: Univ!(0, shared))
                    },
                    Doub!(format!("discrim_type_case") ,: Univ!(0, shared))
                ,: Univ!(0, shared));

            let core_map_split_type =
                fun!(
                    split!(
                        var!(
                            Bound(0),
                            format!("core_map_type_split").as_str()
                        ,: discrim_type.clone()),
                        in
                            apply!(
                                apply!(
                                    var!(Bound((let_items.len() - 1) + 3)), // + 3 since split and fun together inc context by 3
                                    var!(Bound(1))),
                                var!(Bound(0)))
                    ,: Univ!(level, shared))
                ,:
                    pi!(
                        "core_map_split_type_pi",
                        discrim_type.clone(),
                        Univ!(level, shared)
                    ,: Univ!(level, shared)));
            let_items.push(core_map_split_type);

            core_map =
                split!(
                    var!(
                        Bound(0),
                        format!("core_map").as_str()
                    ,: discrim_type.clone()),
                    in
                        case!(
                            var!(
                                Bound(1),
                                format!("core_map").as_str()
                            ,: Doub!(format!("core_map").as_str() ,: Univ!(0, shared))),
                            l => core_item;
                            r => core_map;
                        ,:
                            apply!(
                                apply!(
                                    var!(Bound(num_items * 2)), // + 3 since split and fun together inc context by 3
                                    var!(Bound(1))),
                                var!(Bound(0))))
                ,:
                    apply!(
                        var!(Bound(num_items * 2 - 1)),
                        var!(Bound(0))));
        }

        let core_map_type = core_map.r#type();
        let_bind!(
            let_items,
            fun!(
                core_map
            ,:
                pi!(
                    discrim_type,
                    core_map_type
                ,: Univ!(level, shared))))
    };

    Ok(core_module)
    // let core_map_type = core_map.r#type();
    // println!("CM {:?}", core_map_type);

    // use self::core::{
    //     Term,
    //     InnerTerm::*
    // };

    // let module_type =
    //     pi!(
    //         discrim_type,
    //         core_map_type
    //     ,: Univ!(level, shared));

    // Ok(rec!(
    //     fun!(
    //         core_map
    //     ,: module_type.clone())
    // ,: module_type))
}