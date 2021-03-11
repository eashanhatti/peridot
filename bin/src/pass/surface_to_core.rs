#![allow(warnings)]

use std::{
    collections::{
        HashSet,
        hash_map::{
            HashMap,
            Iter
        }
    },
    cmp::max,
    convert::TryInto
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
            eval::{
                shift,
                normalize
            },
            lang::{
                TermComparison::*,
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
use super::state::*;
extern crate rand;
extern crate assoc_collections;
use assoc_collections::*;
extern crate macros;
use macros::*;

#[derive(Debug)]
pub enum Error<'a> {
    MismatchedTypes { term: &'a Term, state: State, exp_type: core::Term, giv_type: core::Term, specific: Vec<(core::Term, core::Term)> },
    NonexistentVar { var: &'a Term, state: State, name: Name },
    ExpectedOfTypeType { term: &'a Term, state: State, giv_type: core::Term },
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
        TypeTypeIntro => Ok(core::Term::new(Box::new(core::InnerTerm::TypeTypeIntro), None)),
        Var(ref name) =>
            if let Some((_, r#type)) = state.get_dec(name) {
                Ok(r#type)
            } else {
                Err(vec![Error::NonexistentVar { var: term, state, name: name.clone() }])
            }
        FunctionTypeIntro(_, _, _) =>
            Ok(core::Term::new(
                Box::new(core::TypeTypeIntro),
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
                Box::new(core::TypeTypeIntro),
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
                doub!(this ,: Doub!( ,: Univ!())),
                unit!( ,: Unit!( ,: Univ!()))
            ,: make_enum_type(num_inhabitants))
        } else {
            unit!( ,: Unit!( ,: Univ!()))
        }
    } else {
        pair!(
            doub!(that ,: Doub!( ,: Univ!())),
            make_enum(inhabitant - 1, num_inhabitants - 1)
        ,: r#type)
    }
}

fn make_enum_type(num_inhabitants: usize) -> core::Term {
    if num_inhabitants == 0 {
        Void!( ,: Univ!())
    } else if num_inhabitants == 1 {
        Unit!( ,: Univ!())
    } else {
        Pair!(
            Doub!( ,: Univ!()),
            case!(
                var!(Bound(0) ,: Doub!( ,: Univ!())),
                l => Unit!( ,: Univ!());
                r => make_enum_type(num_inhabitants - 1);
            ,: Univ!())
        ,: Univ!())
    }
}

// checks a surface term, and either returns the elaborated term or errors
pub fn elab_term<'a>(term: &'a Term, exp_type: core::Term, state: State) -> ElabResult<'a> {
    match &*term.data {
        Ann(ref annd_term, ref type_ann) => {
            let core_type_ann = elab_term(type_ann, infer_type(type_ann, state.clone())?, state.clone())?;
            let cmp = is_terms_eq(&core_type_ann, &exp_type, state.clone().locals().clone().equivs());
            if let False(specific) = cmp {
                return Err(vec![MismatchedTypes { term, state, exp_type: exp_type, giv_type: core_type_ann, specific }])
            }
            elab_term(annd_term, core_type_ann, state)
        },
        Var(ref name) => {
            match state.get_dec(name) {
                Some((index, var_type)) => {
                    let cmp = is_terms_eq(&var_type, &exp_type, state.clone().locals().clone().equivs());
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
            let core_in_type_type = core_in_type.r#type(Context::new());
            let out_type_context =
                if let Some(some_var_name) = var_name {
                    state.with_dec(some_var_name.clone(), core_in_type.clone())
                } else {
                    state.raw_inc_and_shift(1)
                };
            let core_out_type = elab_term(out_type, infer_type(out_type, out_type_context.clone())?, out_type_context)?;
            // println!("OUT_TYPE\n{:?}", out_type);
            // println!("CORE_OUT_TYPE\n{:?}", core_out_type);
            let core_out_type_type = core_out_type.r#type(Context::new());

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
            let mut curr_state = state.clone();
            for param_name in param_names.iter() {
                if let self::core::lang::InnerTerm::FunctionTypeIntro(in_type, out_type) = *curr_type.data {
                    in_types.push(in_type.clone());
                    curr_type = out_type;
                    curr_state = curr_state.with_dec(param_name.clone(), in_type);
                } else {
                    let giv_type = {
                        let mut type_acc = curr_type;
                        for in_type in in_types {
                            type_acc = 
                                pi!(
                                    in_type,
                                    type_acc
                                ,: Univ!());
                        }
                        type_acc
                    };
                    return Err(vec![MismatchedTypes { term, state, exp_type, giv_type, specific: Vec::new() }]);
                }
            }

            // println!("CURR_STATE\n{:?}", curr_state);
            let mut body_acc = elab_term(body, curr_type, curr_state)?;
            for in_type in in_types.into_iter().rev() {
                let body_acc_type = body_acc.r#type(Context::new());
                body_acc =
                    fun!(
                        body_acc
                    ,:
                        pi!(
                            in_type,
                            body_acc_type
                        ,: Univ!()));
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
                core::InnerTerm::TypeTypeIntro =>
                    Ok(Indexed!(
                        0,
                        make_enum_type(*num_inhabitants)
                    ,: Univ!())),
                _ => Err(vec![ExpectedOfTypeType { term, state, giv_type: exp_type }])
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
                            if let (Var(Bound(0)), DoubTypeIntro, UnitTypeIntro) = (*discrim.data.clone(), *discrim.r#type(Context::new()).data, *branch1.data.clone()) {
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
                let enum_type = enum_val.r#type(Context::new());
                // println!("INHAB {:?} NUM_INHAB {:?}", *inhabitant, num_inhabitants);
                // println!("VAL {:?}\nTYPE {:?}", enum_val, enum_type);
                Ok(Term::new(
                    Box::new(IndexedIntro(enum_val)),
                    Some(Box::new(Term::new(
                        Box::new(IndexedTypeIntro(
                            0,
                            enum_type)),
                        Some(Box::new(Univ!())))))))
            } else {
                Err(vec![ExpectedOfEnumType { term, state, giv_type: exp_type }])
            },
        TypeTypeIntro =>
            match *exp_type.data {
                core::TypeTypeIntro =>
                    Ok(core::Term::new(
                        Box::new(core::InnerTerm::TypeTypeIntro),
                        Some(Box::new(core::Term::new(
                            Box::new(core::InnerTerm::TypeTypeIntro),
                            None))))),
                _ => Err(vec![ExpectedOfTypeType { term, state, giv_type: exp_type }])
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
                for (_, (global_type, _, global_id)) in state.globals().iter() {
                    // println!("GT {:?}", global_type);
                    map.insert(*global_id, global_type.clone());
                }
                for i in 0..state.num_global_decs {
                    if let Some(_) = map.get(&i) {
                        ()
                    } else {
                        // an import should never normalize down to this. if it ever does it will be ill-typed
                        map.insert(i, postulate!(Symbol(rand::random::<usize>()) ,: Univ!()));
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
                                unit!( ,: Unit!( ,: Univ!())),
                                doub!(this ,: Doub!( ,: Univ!()))
                            ,: r#type)
                        } else {
                            unit!( ,: Unit!( ,: Univ!()))
                        }
                    } else {
                        pair!(
                            make_discrim(id - 1, num_globals - 1),
                            doub!(that ,: Doub!( ,: Univ!()))
                        ,: r#type)
                    }
            }

            fn make_discrim_type(num_globals: usize) -> core::Term {
                if num_globals == 0 {
                    unreachable!()
                } else if num_globals == 1 {
                    Unit!( ,: Univ!())
                } else {
                    Pair!(
                        case!(
                            var!(Bound(1), "import discrim_type" ,: Doub!( ,: Univ!())),
                            l => Unit!( ,: Univ!());
                            r => make_discrim_type(num_globals - 1);
                        ,: Univ!()),
                        Doub!( ,: Univ!())
                    ,: Univ!())
                }
            }

            // println!("NUM GD{:?}", state.num_global_decs);
            let discrim = make_discrim(id, state.num_global_decs);
            // println!("DISCRIM {:?}", discrim);
            // println!("DISCRIM_TYPE {:?}", discrim.r#type(Context::new()));
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
                            ,: Doub!( ,: Univ!())),
                            l => global_type;
                            r => global_map_type;
                        ,: Univ!());
                    let core_map_split_type =
                        split!(
                            var!(
                                // if i == len - 1 { Bound(state.globals_map_index) } else { Bound(0) }
                                Bound(0),
                                format!("split {:?}", c).as_str()
                            ,: make_discrim_type(i + 2)),
                            in core_map_case_type.clone()
                        ,: Univ!());
                    global_map_type = core_map_split_type;
                }
                pi!(
                    discrim.r#type(Context::new()),
                    global_map_type
                ,: Univ!())
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
            //     let core_term_type = core_term.r#type(Context::new());
            //     core_term =
            //         core::Term::new(
            //             Box::new(core::InnerTerm::FoldIntro(core_term)),
            //             Some(Box::new(core::Term::new(
            //                 Box::new(core::InnerTerm::FoldTypeIntro(core_term_type)),
            //                 Some(Box::new(Univ!()))))));
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
        RecordTypeDef(&'a AssocSet<Name>, &'a AssocVec<Name, crate::lang::surface::Term>),
    }

    // flatten the module structure, turning it into a more haskell-like structure
    fn flatten_module(module: &Module, module_name: QualifiedName) -> AssocVec<(QualifiedName, ItemKind), FlattenedModuleItem> {
        let mut items = AssocVec::new();
        // println!("ITEMS\n{:#?}", module.items);
        for ((item_name, _), item) in module.items.iter() {
            // println!("ITEM_NAME {:?}", item_name);
            match item {
                Item::Declaration(r#type) =>
                    { items.insert(
                        (module_name.clone().with_name(item_name.clone()), ItemKind::Dec),
                        FlattenedModuleItem::Declaration(r#type)); },
                Item::TermDef(term) =>
                    { items.insert(
                        (module_name.clone().with_name(item_name.clone()), ItemKind::Def),
                        FlattenedModuleItem::TermDef(term)); },
                Item::RecordTypeDef(params, fields) =>
                    { items.insert(
                        (module_name.clone().with_name(item_name.clone()), ItemKind::Def),
                        FlattenedModuleItem::RecordTypeDef(params, fields)); },
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
    let mut core_items = {
        let mut state = state;
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
                    let mut globals_iter = state.iter_globals();
                    let mut decs_symbols_iter = decs_symbols.iter();
                    let mut core_map = 
                        if state.globals().len() == 0 {
                            unit!( ,: var!(Free(Symbol(rand::random::<usize>())), "no globals" ,: Univ!()))
                        } else {
                            let (_, r#type, value, _) = globals_iter.next().unwrap();
                            value
                        };

                    for ((_, r#type, value, _), symbol) in globals_iter.zip(decs_symbols_iter) {
                        core_map =
                            split!(
                                var!(
                                    Bound(0)
                                ,: postulate!(Symbol(rand::random::<usize>()) ,: Univ!())),
                                in
                                    case!(
                                        var!(
                                            Bound(1)
                                        ,: Doub!( ,: Univ!())),
                                        l => value;
                                        r => core_map;
                                    ,: postulate!(Symbol(rand::random::<usize>()) ,: Univ!()))
                            ,: postulate!(Symbol(rand::random::<usize>()) ,: Univ!()));
                    }
                    core_map = fun!(core_map ,: postulate!(Symbol(rand::random::<usize>()) ,: Univ!()));
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
                FlattenedModuleItem::RecordTypeDef(params, fields) => {
                    let core_item_type = state.clone().get_global_dec(name).unwrap().0; // TODO: error reporting
                    let mut record_type_type = core_item_type.clone();
                    let mut fields_state = state.clone();
                    let mut param_types = Vec::new();

                    for param_name in params.iter() {
                        if let core::FunctionTypeIntro(ref in_type, ref out_type) = *record_type_type.data {
                            fields_state = fields_state.with_dec(param_name.clone(), in_type.clone());
                            param_types.push(in_type.clone());
                            record_type_type = out_type.clone();
                        } else {
                            panic!("record param error not implemented");
                        }
                    }

                    if let core::InnerTerm::TypeTypeIntro = *record_type_type.data {
                        let mut core_field_types = Vec::new();
                        fields_state = fields_state.raw_inc_and_shift(2);

                        for (field_name, field_type) in fields.iter() {
                            let core_field_type = elab_term(field_type, infer_type(field_type, fields_state.clone())?, fields_state.clone())?;
                            core_field_types.push(core_field_type.clone());
                            fields_state = fields_state.with_dec(field_name.clone(), core_field_type).raw_inc_and_shift(2);
                        }

                        let mut core_record_type = Unit!("core_record_type_unit" ,: Univ!());
                        for core_field_type in core_field_types.into_iter().rev() {
                            core_record_type =
                                Pair!(
                                    core_field_type,
                                    core_record_type
                                ,: Univ!());
                        }

                        let mut core_record_type_cons = core_record_type;
                        for param_type in param_types.iter().rev() {
                            let core_record_type_cons_type = core_record_type_cons.r#type(Context::new());
                            core_record_type_cons =
                                fun!(
                                    core_record_type_cons
                                ,: 
                                    pi!(
                                        param_type.clone(),
                                        core_record_type_cons_type
                                    ,: Univ!()));
                        }

                        state = state.with_global_def(name.clone(), core_record_type_cons.clone());
                        core_items.push(core_record_type_cons);
                    } else {
                        panic!("record_type_type error not implemented{:#?}", record_type_type);
                    }
                }
            }
        }

        core_items
    };
    let core_module = {
        use self::core::{
            Term,
            InnerTerm::*
        };
        let num_items = core_items.len();
        let mut core_map = core_items.pop().unwrap();
        let mut discrim_type = Unit!("discrim_unit" ,: Univ!());

        let mut discrim_case_index = 0;
        let mut discrim_split_index = 0;
        let mut discrim_prev_index = 0;
        let discrim_offset = ((num_items - 1) * 2) + 1;

        let mut let_discrim_items = Vec::new();
        let_discrim_items.push(discrim_type.clone());
        let mut let_match_items = Vec::new();
        let_match_items.push(
            fun!(
                    core_map.r#type(Context::new())
                ,:
                    pi!(
                        var!(Bound(discrim_split_index + discrim_offset)),
                        Univ!()
                    ,: Univ!())));

        for (i, core_item) in core_items.into_iter().enumerate().rev() {
            let discrim_case_type =
                case!(
                    var!(
                        Bound(0),
                        format!("discrim_type").as_str()
                    ,: Doub!(format!("discrim_type").as_str() ,: Univ!())),
                    l => Unit!("discrim unit l" ,: Univ!());
                    r => var!(Bound(discrim_case_index + discrim_offset + 1));
                ,: Univ!());

            let core_map_case_type =
                fun!(
                    fun!(
                        case!(
                            var!(
                                Bound(1),
                                format!("core_map_type_case").as_str()
                            ,: Doub!(format!("core_map_type_case").as_str() ,: Univ!())),
                            l => core_item.r#type(Context::new());
                            r =>
                                apply!(
                                    var!(Bound((let_match_items.len() - 1) + 2)), // + 2 since the two funs inc context by 2
                                    var!(Bound(0)));
                        ,: Univ!())
                    ,:
                        pi!(
                            discrim_case_type.clone(),
                            Univ!()
                        ,: Univ!()))
                ,:
                    pi!(
                        Doub!(format!("core_map_type_case").as_str() ,: Univ!()),
                        pi!(
                            discrim_case_type.clone(),
                            Univ!()
                        ,: Univ!())
                    ,: Univ!()));
            let_match_items.push(core_map_case_type);
            discrim_case_index += 1;

            let cons_discrim_type = |r|
                Pair!(
                    case!(
                        var!(
                            Bound(1),
                            format!("discrim_type").as_str()
                        ,: Doub!(format!("discrim_type").as_str() ,: Univ!())),
                        l => Unit!("discrim unit l" ,: Univ!());
                        r => r;
                    ,: Univ!()),
                    Doub!(format!("discrim_type_case") ,: Univ!())
                ,: Univ!());
            discrim_type = cons_discrim_type(discrim_type.clone());
            let_discrim_items.push(cons_discrim_type(var!(Bound(discrim_prev_index + 2))));
            discrim_prev_index += 1;

            discrim_split_index += 1;
            let core_map_split_type =
                fun!(
                    split!(
                        var!(
                            Bound(0)),
                        in
                            apply!(
                                apply!(
                                    var!(Bound((let_match_items.len() - 1) + 3)), // + 3 since split and fun together inc context by 3
                                    var!(Bound(1))),
                                var!(Bound(0)))
                    ,: Univ!())
                ,:
                    pi!(
                        "core_map_split_type_pi",
                        var!(Bound(discrim_split_index + discrim_offset)),
                        Univ!()
                    ,: Univ!()));
            let_match_items.push(core_map_split_type);

            core_map =
                split!(
                    var!(Bound(0)),
                    in
                        case!(
                            var!(
                                Bound(1),
                                format!("core_map").as_str()
                            ,: Doub!(format!("core_map").as_str() ,: Univ!())),
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

        let core_map_type = core_map.r#type(Context::new());
        let_bind!(
            let_discrim_items,
            let_bind!(
                let_match_items,
                fun!(
                    core_map
                ,:
                    pi!(
                        normalize(discrim_type, Context::new()),
                        core_map_type
                    ,: Univ!()))))
    };

    Ok(core_module)
}