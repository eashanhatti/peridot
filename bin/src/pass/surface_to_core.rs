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
    convert::TryInto,
    sync::atomic::{
        AtomicUsize,
        Ordering
    }
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
                InnerVar::*,
                InnerVar,
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
extern crate multizip;
use multizip::{zip3, zip2};

#[derive(Debug, Clone)]
pub enum InnerError {
    NonexistentVar { name: Name },
    MismatchedTypes { exp_type: core::Term, giv_type: core::Term, specific: Vec<(core::Term, core::Term)> },
    ExpectedOfTypeType { giv_type: core::Term },
    ExpectedOfFunctionType { giv_type: core::Term },
    ExpectedOfEnumType { giv_type: core::Term },
    ExpectedOfRecordType { giv_type: core::Term },
    NonexistentGlobal { name: QualifiedName },
    EnumInhabitantTooLarge { inhabitant: usize, num_inhabitants: usize },
    MismatchedFunctionArgsNum { exp_num: usize, giv_num: usize },
    InexaustiveMatch { missing_pattern: Pattern },
    CannotInferType
}
use InnerError::*;

#[derive(Debug, Clone)]
pub struct Error {
    pub inner: InnerError,
    pub state: State,
    pub range: Range
}

impl Error {
    pub fn new(range: Range, state: State, inner: InnerError) -> Error {
        Error {
            inner,
            state,
            range
        }
    }
}

type ElabResult = Result<core::Term, Vec<Error>>;

// term may be unchecked
pub fn infer_type<'a>(term: &'a Term, state: State, exp_type: Option<core::Term>) -> ElabResult {
    let context = state.locals().clone();
    Ok(normalize(match &*term.data {
        Ann(_, ref type_ann) => Ok(elab_term(type_ann, infer_type(type_ann, state.clone(), None)?, state)?),
        TypeTypeIntro => Ok(core::Term::new(Box::new(core::InnerTerm::TypeTypeIntro), None)),
        Var(ref name) =>
            if let Some((_, r#type)) = state.get_dec(name) {
                Ok(r#type)
            } else {
                Err(vec![Error::new(term.range, state, NonexistentVar { name: name.clone() })])
            }
        FunctionTypeIntro(_, _, _) =>
            Ok(core::Term::new(
                Box::new(core::TypeTypeIntro),
                None
            )),
        FunctionElim(ref abs, _) => {
            let abs_type = infer_type(abs, state.clone(), None)?;
            match &*abs_type.data {
                core::InnerTerm::FunctionTypeIntro(_, ref out_type) => Ok(out_type.clone()),
                _ => Err(vec![Error::new(abs.range, state, ExpectedOfFunctionType { giv_type: abs_type })])
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
                None => Err(vec![Error::new(term.range, state, NonexistentGlobal { name: path.clone() })])
            },
        _ =>
            if let Some(some_exp_type) = exp_type {
                Ok(some_exp_type)
            } else {
                Err(vec![Error::new(term.range, state, CannotInferType)])
            }
    }?, context))
}

fn make_enum(inhabitant: usize, num_inhabitants: usize) -> core::Term {
    let r#type = make_enum_type(num_inhabitants);
    if inhabitant == 0 {
        if num_inhabitants > 1 {
            pair!(
                doub!(this ,: Doub!( ,: Univ!())),
                unit!( ,: Unit!( ,: Univ!()))
            ,: make_enum_type(num_inhabitants))
        } else if num_inhabitants == 1 {
            unit!( ,: Unit!( ,: Univ!()))
        } else {
            panic!("cannot construct Fin {}", num_inhabitants)
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

fn readback_as_enum_type(r#type: &core::Term) -> usize {
    use self::core::lang::{
        Term,
        InnerTerm::*,
        Doub
    };

    let mut num_inhabitants = 0;
    let mut curr_type = r#type;
    match &*curr_type.data {
        VoidTypeIntro => (),
        UnitTypeIntro => num_inhabitants = 1,
        PairTypeIntro(_, _) => {
            while let PairTypeIntro(ref fst_type, ref snd_type) = &*curr_type.data {
                if let (DoubTypeIntro, DoubElim(ref discrim, ref branch1, ref branch2)) = (&*fst_type.data, &*snd_type.data) {
                    if let (Var(Bound(0)), DoubTypeIntro, UnitTypeIntro) = (&*discrim.data, &*discrim.r#type(Context::new()).data, &*branch1.data) {
                        curr_type = branch2;
                        num_inhabitants += 1;
                    } else {
                        unreachable!();
                    }
                } else if let (DoubTypeIntro, UnitTypeIntro) = (&*fst_type.data, &*snd_type.data) {
                    curr_type = snd_type;
                    num_inhabitants += 2;
                } else {
                    unreachable!();
                }
            }
        },
        _ => unreachable!()
    }
    num_inhabitants
}

static NOMINAL_ID: AtomicUsize = AtomicUsize::new(1);

fn next_nominal_id() -> usize {
    let index = NOMINAL_ID.load(Ordering::SeqCst);
    NOMINAL_ID.fetch_add(1, Ordering::SeqCst);
    index
}

fn elab_match(discrim: core::Term, discrim_type: core::Term, exp_type: core::Term, clauses: &Vec<(Pattern, Term)>, state: &State, match_range: Range) -> ElabResult {
    #[derive(Debug)]
    enum CaseTreeBody {
        CaseTree(usize, core::Term, Box<CaseTree>), // scrutinee, scrutinizer
        Term(core::Term)
    }
    #[derive(Debug)]
    enum CaseTree {
        Record(CaseTreeBody),
        Enum(Vec<CaseTreeBody>),
        DoNothing(CaseTreeBody)
    }
    #[derive(Debug, Clone)]
    enum Discrim {
        Record(Vec<Discrim>),
        Enum(usize),
        Whatever
    }

    fn readback_as_record_type(r#type: &core::Term) -> Vec<&core::Term> {
        let mut curr_type = r#type;
        let mut field_types = Vec::new();
        if let core::InnerTerm::PairTypeIntro(_, _) = *curr_type.data {
            ()
        } else {
            unreachable!("{:#?}", curr_type);
        }
        while let core::InnerTerm::PairTypeIntro(ref fst_type, ref snd_type) = *curr_type.data {
            field_types.push(fst_type);
            curr_type = snd_type;
        }
        field_types
    }

    fn readback_to_record_type(r#type: core::Term) -> Vec<core::Term> {
        let mut curr_type = r#type;
        let mut field_types = Vec::new();
        if let core::InnerTerm::PairTypeIntro(_, _) = *curr_type.data {
            ()
        } else {
            unreachable!("{:#?}", curr_type);
        }
        while let core::InnerTerm::PairTypeIntro(fst_type, snd_type) = *curr_type.data {
            field_types.push(fst_type);
            curr_type = snd_type;
        }
        field_types
    }

    fn readback_discrim_to_core(discrim: &Discrim, discrim_type: &core::Term) -> core::Term {
        match discrim {
            Discrim::Record(fields) => {
                let readback = readback_as_record_type(discrim_type.as_indexed_type_intro().1);
                let mut core_fields = Vec::new();
                for (field, field_type) in fields.iter().zip(readback.into_iter()) {
                    core_fields.push(readback_discrim_to_core(field, field_type));
                }
                let mut core_term = unit!( ,: Unit!( ,: Univ!()));
                for field in core_fields {
                    let field_type = field.r#type(Context::new());
                    let core_term_type = core_term.r#type(Context::new());
                    core_term =
                        pair!(
                            field,
                            core_term
                        ,:
                            Pair!(
                                field_type,
                                core_term_type
                            ,: Univ!()));
                }
                core_term
            },
            Discrim::Enum(inhab) => {
                let mut core_term = make_enum(*inhab, readback_as_enum_type(discrim_type.as_indexed_type_intro().1));
                core_term.type_ann = Some(Box::new(discrim_type.clone()));
                core_term
            },
            Discrim::Whatever => postulate!(Symbol(rand::random::<usize>()) ,: discrim_type.clone())
        }
    }

    fn is_complete(discrim: &Discrim, discrim_type: &core::Term, context: Context) -> bool {
        if let core::InnerTerm::IndexedTypeIntro(type_index, ref inner_type) = &*discrim_type.data {
            if *type_index == 0 {
                if let Discrim::Enum(_) = discrim {
                    true
                } else {
                    unreachable!("DISCRIM\n{:#?}\nDISCRIM_TYPE\n{:#?}", discrim, discrim_type)
                }
            } else {
                if let Discrim::Record(fields) = discrim {
                    let readback = readback_as_record_type(&inner_type);
                    let is_lens_equal = readback.len() == fields.len();
                    let is_fields_complete = {
                        let mut context = context;
                        let mut is_fields_complete = true;
                        context = context.inc_and_shift(2);
                        for (field, field_type) in fields.iter().zip(readback.into_iter()) {
                            is_fields_complete =
                                is_fields_complete &&
                                is_complete(field, &normalize(field_type.clone(), context.clone()), context.clone());
                            context = context.clone()
                                .with_def(
                                    Bound(0),
                                    normalize(readback_discrim_to_core(&field, field_type), context.clone()))
                        }
                        is_fields_complete
                    };

                    is_lens_equal && is_fields_complete
                } else {
                    unreachable!("DISCRIM\n{:#?}\nDISCRIM_TYPE\n{:#?}", discrim, discrim_type)
                }
            }
        } else {
            if let Discrim::Whatever = discrim {
                true
            } else {
                unreachable!("DISCRIM\n{:#?}\nDISCRIM_TYPE\n{:#?}", discrim, discrim_type)
            }
        }
    }


    fn elab_matching_branch(
        clauses: &Vec<(Pattern, Term)>,
        discrim: &Discrim,
        discrim_type: &core::Term,
        exp_type: &core::Term,
        state: &State) -> Option<ElabResult>
    {
        fn is_match(pattern: &Pattern, discrim: &Discrim) -> bool {
            match (&*pattern.data, discrim) {
                (InnerPattern::Record(pattern_fields), Discrim::Record(discrim_fields)) =>
                    pattern_fields.len() == discrim_fields.len() &&
                    pattern_fields.iter().zip(discrim_fields.iter()).all(|(pf, df)| is_match(pf, df)),
                (InnerPattern::Enum(pattern_inhab), Discrim::Enum(discrim_inhab)) =>
                    pattern_inhab == discrim_inhab,
                (InnerPattern::Binding(_), _) => true,
                _ => false
            }
        }

        fn cons_branch_state(discrim: &Discrim, pattern_fields: &Vec<Pattern>, discrim_type: &core::Term, mut state: State) -> (State, isize) {
            fn rec(field: &Discrim, field_type: &core::Term, pattern_fields: Option<&Vec<Pattern>>, mut state: State, mut shift_amount: isize) -> (State, isize) {
                match field {
                    Discrim::Record(ref fields) => {
                        let field_type = shift(field_type.clone(), HashSet::new(), 1);
                        let readback = readback_as_record_type(field_type.as_indexed_type_intro().1);
                        state = state.raw_inc_and_shift(1);
                        shift_amount += 1;
                        if let Some(pattern_fields) = pattern_fields {
                            assert!(readback.len() == pattern_fields.len() && readback.len() == fields.len());
                            for (field, field_type, pattern_field) in zip3(fields.iter(), readback.iter(), pattern_fields.iter()) {
                                state = state.raw_inc_and_shift(2);
                                shift_amount += 2;
                                let locals = state.locals().clone();
                                match &*pattern_field.data {
                                    InnerPattern::Binding(name) => state = state
                                        .raw_with_dec(name.clone(), Bound(0), normalize((*field_type).clone(), locals))
                                        .with_def(name.clone(), readback_discrim_to_core(field, *field_type)),
                                    _ => {
                                        let value = readback_discrim_to_core(field, *field_type);
                                        let value_type = value.r#type(locals.clone());
                                        state = state
                                            .raw_with_unnamed_dec(Bound(0), normalize((*field_type).clone(), locals))
                                            .raw_with_unnamed_def(
                                                Bound(0),
                                                indexed!(
                                                    value
                                                ,: (*field_type).clone()));
                                    }
                                }
                            }
                            for (field, field_type, pattern_field) in zip3(fields.iter(), readback.into_iter(), pattern_fields.iter()) {
                                let (new_state, new_shift_amount) = match &*pattern_field.data {
                                    InnerPattern::Record(next_pattern_fields) => rec(field, field_type, Some(next_pattern_fields), state, shift_amount),
                                    _ => rec(field, field_type, None, state, shift_amount)
                                };
                                state = new_state;
                                shift_amount = new_shift_amount;
                            }
                            (state, shift_amount)
                        } else {
                            assert!(readback.len() == fields.len());
                            for (field, field_type) in zip2(fields.iter(), readback.into_iter()) {
                                let (new_state, new_shift_amount) = rec(field, field_type, None, state.raw_inc_and_shift(2), shift_amount);
                                state = new_state;
                                shift_amount = new_shift_amount;
                            }
                            (state, shift_amount)
                        }
                    },
                    Discrim::Enum(inhab) =>
                        match readback_as_enum_type(field_type.as_indexed_type_intro().1) {
                            1 => (state.raw_inc_and_shift(1), shift_amount + 1isize),
                            0 => unreachable!(),
                            num_inhabs =>
                                if *inhab == num_inhabs - 1 {
                                    let amount = ((inhab + 1 - 1) * 2) as isize + 1;
                                    (state.raw_inc_and_shift(amount), shift_amount + amount)
                                } else {
                                    let amount = ((inhab + 1) * 2) as isize + 1;
                                    (state.raw_inc_and_shift(amount), shift_amount + amount)
                                }
                        }
                    Discrim::Whatever => (state.raw_inc_and_shift(1), shift_amount + 1)
                }
            }
            
            rec(discrim, discrim_type, Some(pattern_fields), state, 0)
        }

        for (ref pattern, ref branch) in clauses {
            if is_match(pattern, discrim) && is_complete(discrim, discrim_type, state.locals().clone()) {
                let (branch_state, shift_amount) =
                    match &*pattern.data {
                        InnerPattern::Record(pattern_fields) => cons_branch_state(discrim, &pattern_fields, discrim_type, state.clone()),
                        InnerPattern::Binding(name) => (state.clone().with_dec(name.clone(), discrim_type.clone()), 0),
                        InnerPattern::Enum(inhab) => match readback_as_enum_type(discrim_type.as_indexed_type_intro().1) {
                            1 => (state.clone().raw_inc_and_shift(1), 1isize),
                            0 => unreachable!(),
                            num_inhabs =>
                                if *inhab == num_inhabs - 1 {
                                    let amount = ((inhab + 1 - 1) * 2) as isize + 1;
                                    (state.clone().raw_inc_and_shift(amount), amount)
                                } else {
                                    let amount = ((inhab + 1) * 2) as isize + 1;
                                    (state.clone().raw_inc_and_shift(amount), amount)
                                }
                        },
                    };
                // dbg!(branch_state.locals());
                return Some(elab_term(branch, shift(exp_type.clone(), HashSet::new(), shift_amount), branch_state));
            }
        }

        None
    }

    fn complete_discrim_to_pattern(discrim: &Discrim) -> Pattern {
        Pattern {
            data:
                Box::new(match discrim {
                    Discrim::Record(fields) => InnerPattern::Record(fields.iter().map(complete_discrim_to_pattern).collect()),
                    Discrim::Enum(inhab) => InnerPattern::Enum(*inhab),
                    Discrim::Whatever => InnerPattern::Binding(Name("_".to_string()))
                }),
            range: None
        }
    }

    fn next_index(incomplete_discrim: &Discrim, discrim_type: &core::Term, context: Context) -> usize {
        fn count_index(field: &Discrim, field_type: &core::Term) -> usize {
            match field {
                Discrim::Record(ref fields) => {
                    let mut index = 1;
                    let readback = readback_as_record_type(field_type.as_indexed_type_intro().1);
                    assert!(readback.len() == fields.len());
                    for (field, field_type) in fields.iter().zip(readback.into_iter()) {
                        index += count_index(field, field_type);
                    }
                    index + fields.len() * 2
                },
                Discrim::Enum(inhab) =>
                    match readback_as_enum_type(field_type.as_indexed_type_intro().1) {
                        1 => 1,
                        0 => unreachable!(),
                        num_inhabs =>
                            if *inhab == num_inhabs - 1 {
                                (inhab - 1 + 1) * 2 + 1
                            } else {
                                (inhab + 1) * 2 + 1
                            }
                    }
                Discrim::Whatever => 1
            }
        }

        fn rec(incomplete_discrim: &Discrim, discrim_type: &core::Term, context: Context) -> usize {
            if let Discrim::Record(ref fields) = incomplete_discrim {
                use std::cmp::Ordering::*;

                let readback = readback_as_record_type(discrim_type.as_indexed_type_intro().1);
                match readback.len().partial_cmp(&fields.len()).unwrap() {
                    Less => unreachable!(),
                    Equal | Greater => {
                        if fields.len() == 0 {
                            (readback.len() - 1) * 2
                        } else {
                            let mut index = 0;
                            let mut context = context;
                            for i in 0..fields.len() - 1 {
                                context = context.inc_and_shift(2);
                                let core_field =
                                    normalize(
                                        readback_discrim_to_core(&fields[i], &readback[i]).clone(),
                                        context.clone());
                                index += count_index(&fields[i], &readback[i]);
                                context = context
                                    .with_dec(Bound(0), readback[i].clone())
                                    .with_def(Bound(0), core_field);
                            }
                            context = context.inc_and_shift(2);

                            let field = &fields[fields.len() - 1];
                            let field_type = &readback[fields.len() - 1];
                            if is_complete(&field, field_type, context.clone()) {
                                index + count_index(field, field_type)
                            } else {
                                rec(field, field_type, context)
                            }
                        }
                    }
                }
            } else {
                unreachable!()
            }
        }

        rec(incomplete_discrim, discrim_type, context)
    } 

    enum NextType {
        Record,
        Enum(usize),
        Unelimable
    }
    fn next_type(incomplete_discrim: &Discrim, discrim_type: &core::Term, context: Context) -> (NextType, core::Term) {
        fn rec(
            incomplete_discrim: &Discrim,
            discrim_type: core::Term,
            next_type: &mut Option<NextType>,
            next_discrim_type: &mut Option<core::Term>,
            mut context: Context) -> usize
        {
            use std::cmp::Ordering::*;

            match incomplete_discrim {
                Discrim::Record(ref fields) => {
                    let mut readback = readback_to_record_type(discrim_type.to_indexed_type_intro().1);
                    let mut total_shift = 0;
                    for (i, field) in fields.iter().enumerate() {
                        context = context.inc_and_shift(2);
                        let shift_amount = 1 + rec(field, normalize(readback[i].clone(), context.clone()), next_type, next_discrim_type, context.clone());
                        total_shift += shift_amount;
                        context = context.clone().with_def(Bound(0), normalize(readback_discrim_to_core(&field, &readback[i]), context.clone()));
                        for field_type in readback.iter_mut().skip(i) {
                            *field_type = shift(field_type.clone(), HashSet::new(), shift_amount as isize);
                        }
                    }

                    match readback.len().partial_cmp(&fields.len()).unwrap() {
                        Less => unreachable!(),
                        Equal => (),
                        Greater => {
                            let readback_next = normalize(readback[fields.len()].clone(), context);
                            *next_type = 
                                if let core::InnerTerm::IndexedTypeIntro(i, ref inner_type) = *readback_next.data {
                                    if i == 0 {
                                        let num_inhabs = readback_as_enum_type(inner_type);
                                        if num_inhabs > 0 {
                                            Some(NextType::Enum(num_inhabs))
                                        } else {
                                            Some(NextType::Unelimable)
                                        }
                                    } else {
                                        Some(NextType::Record)
                                    }
                                } else {
                                    Some(NextType::Unelimable)
                                };

                            *next_discrim_type = Some(readback_next);
                        }
                    }

                    total_shift
                },
                Discrim::Enum(inhab) =>
                    match readback_as_enum_type(discrim_type.as_indexed_type_intro().1) {
                        1 => 0,
                        0 => unreachable!(),
                        num_inhabs =>
                            if *inhab == num_inhabs - 1 {
                                (*inhab - 1 + 1) * 2
                            } else {
                                (*inhab + 1) * 2
                            }
                    },
                Discrim::Whatever => 0
            }
        }

        assert!(if let Discrim::Record(_) = incomplete_discrim {
            true
        } else {
            false
        });

        let mut next_type = None;
        let mut next_discrim_type = None;
        let mut shift_amount = 0;
        rec(dbg!(incomplete_discrim), shift(discrim_type.clone(), HashSet::new(), 1), &mut next_type, &mut next_discrim_type, context);

        (next_type.unwrap(), shift(next_discrim_type.unwrap(), HashSet::new(), dbg!(shift_amount)))
    }

    // fills the hole in `incomplete_discrim` with `fill_with`
    fn next_discrim(incomplete_discrim: Discrim, fill_with: Discrim, discrim_type: &core::Term, context: Context) -> Discrim {
        fn rec(incomplete_discrim: Discrim, fill_with: Discrim, discrim_type: &core::Term, mut context: Context) -> Option<Discrim> {
            use std::cmp::Ordering::*;

            if let Discrim::Record(mut fields) = incomplete_discrim {
                let readback = readback_as_record_type(discrim_type.as_indexed_type_intro().1);
                let comparison = readback.len().partial_cmp(&fields.len()).unwrap();
                for (i, (mut field, field_type)) in fields.iter_mut().zip(readback.into_iter()).enumerate() {
                    context = context.inc_and_shift(2);
                    match rec(field.clone(), fill_with.clone(), &normalize(field_type.clone(), context.clone()), context.clone()) {
                        Some(new_field) => {
                            *field = new_field;
                            assert!(i == fields.len() - 1);
                            return Some(Discrim::Record(fields));
                        },
                        None => ()
                    }

                    context = context.clone().with_def(Bound(0), normalize(readback_discrim_to_core(&field, field_type), context.clone()))
                }
                match comparison {
                    Equal => None,
                    Greater => {
                        fields.push(fill_with);
                        Some(Discrim::Record(fields))
                    }
                    _ => unreachable!()
                }
            } else {
                None
            }
        }

        if let Some(next) = rec(incomplete_discrim, fill_with, &discrim_type, context) {
            next
        } else {
            // println!("DISCRIM\n{:#?}\nFILL_WITH\n{:#?}\nDISCRIM_TYPE\n{:#?}", incomplete_discrim, fill_with, discrim_type);
            unreachable!()
        }
    }

    fn lower_to_case_tree(
        clauses: &Vec<(Pattern, Term)>,
        incomplete_discrim: Discrim,
        discrim_type: core::Term,
        exp_type: core::Term,
        match_range: Range,
        state: &State) -> Result<CaseTreeBody, Vec<Error>>
    {
        let matching_branch = elab_matching_branch(clauses, &incomplete_discrim, &discrim_type, &exp_type, state);
        if let Some(core_branch) = matching_branch {
            Ok(CaseTreeBody::Term(core_branch?))
        } else {
            if is_complete(&incomplete_discrim, &discrim_type, state.locals().clone()) {
                return Err(vec![
                    Error::new(
                        match_range,
                        state.clone(),
                        InexaustiveMatch { missing_pattern: complete_discrim_to_pattern(&incomplete_discrim) })]);
            } else {
                let (fill_type, this_discrim_type) = next_type(&incomplete_discrim, &discrim_type, state.locals().clone());
                let index = next_index(&incomplete_discrim, &discrim_type, state.locals().clone());
                // println!("I: {:?} D: {:?}", index, incomplete_discrim);
                let case_tree =
                    match fill_type {
                        NextType::Record =>
                            CaseTree::Record(lower_to_case_tree(
                                clauses,
                                next_discrim(incomplete_discrim, Discrim::Record(Vec::new()), &discrim_type, state.locals().clone()),
                                discrim_type,
                                exp_type,
                                match_range,
                                state)?),
                        NextType::Enum(num_inhabs) => {
                            let mut branches = Vec::new();
                            let mut errors = Vec::new();
                            for n in 0..num_inhabs {
                                match lower_to_case_tree(
                                    clauses,
                                    next_discrim(incomplete_discrim.clone(), Discrim::Enum(n), &discrim_type, state.locals().clone()),
                                    discrim_type.clone(),
                                    exp_type.clone(),
                                    match_range,
                                    state)
                                {
                                    Ok(branch) => branches.push(branch),
                                    Err(errs) =>
                                        for err in errs {
                                            errors.push(err)
                                        }
                                }
                            }
                            if errors.len() > 0 {
                                return Err(errors)
                            } else {
                                CaseTree::Enum(branches)
                            }
                        }
                        NextType::Unelimable =>
                            CaseTree::DoNothing(
                                lower_to_case_tree(
                                    clauses,
                                    next_discrim(incomplete_discrim, Discrim::Whatever, &discrim_type, state.locals().clone()),
                                    discrim_type,
                                    exp_type,
                                    match_range,
                                    state)?)
                    };
                Ok(CaseTreeBody::CaseTree(index, this_discrim_type, Box::new(case_tree)))
            }
        }
    }

    fn lower_to_core(case_tree: CaseTree, discrim_type: core::Term) -> Box<dyn FnOnce(core::Term) -> core::Term> {
        // println!("CASE_TREE\n{:#?}", case_tree);
        // println!("DISCRIM_TYPE\n{:?}", discrim_type);
        fn lower_body(case_tree_body: CaseTreeBody) -> core::Term {
            match case_tree_body {
                CaseTreeBody::CaseTree(discrim, discrim_type, case_tree) =>
                    lower_to_core(*case_tree, discrim_type)(var!(Bound(discrim))),
                CaseTreeBody::Term(term) => term
            }
        }

        match case_tree {
            CaseTree::Record(body) => {
                use self::core::InnerTerm::*;

                fn make(r#type: core::Term, body: core::Term) -> core::Term {
                    if let PairTypeIntro(_, snd_type) = *r#type.data {
                        let split_body = make(snd_type, body);
                        let split_body_type = split_body.r#type(Context::new());
                        split!(
                            var!(Bound(1)),
                            in
                                split_body
                        ,:
                            split!(
                                var!(Bound(1)),
                                in
                                    split_body_type
                            ,: Univ!()))
                    } else {
                        body
                    }
                }

                let inner_discrim_type = discrim_type.as_indexed_type_intro().1.clone();
                let core_body = lower_body(body);
                let split_body = make(inner_discrim_type.as_pair_type_intro().1.clone(), core_body);
                // println!("SPLIT_BODY\n{:?}", split_body);
                let split_body_type = split_body.r#type(Context::new());
                Box::new(|d: core::Term|
                    indexed_elim!(
                        d.clone(),
                        split!(
                            var!(Bound(0)),
                            in
                                split_body
                        ,:
                            split!(
                                var!(Bound(0)),
                                in
                                    split_body_type.clone()
                            ,: Univ!()))
                    ,:
                        indexed_elim!(
                            d,
                            split!(
                                var!(Bound(0)),
                                in
                                    split_body_type
                            ,: Univ!())
                        ,: Univ!())))
            },
            CaseTree::Enum(branches) => {
                let mut core_branches = branches.into_iter().map(|b| lower_body(b)).collect::<Vec<core::Term>>();
                if core_branches.len() == 1 {
                    let core_branch = core_branches.remove(0);
                    let core_branch_type = core_branch.r#type(Context::new());
                    Box::new(|d: core::Term|
                        indexed_elim!(
                            d.clone(),
                            core_branch
                        ,:
                            indexed_elim!(
                                d,
                                core_branch_type
                            ,: Univ!())))
                } else {
                    let mut core_term = core_branches.remove(core_branches.len() - 1);
                    let first_branch = core_branches.remove(0);
                    for core_branch in core_branches.into_iter().rev() {
                        let case_type =
                            case!(
                                var!(Bound(0)),
                                l => core_branch.r#type(Context::new());
                                r => core_term.r#type(Context::new());
                            ,: Univ!());
                        let split_type =
                            split!(
                                var!(Bound(1)),
                                in
                                    case_type.clone()
                            ,: Univ!());

                        core_term =
                            split!(
                                var!(Bound(1)),
                                in
                                    case!(
                                        var!(Bound(0)),
                                        l => core_branch;
                                        r => core_term;
                                    ,: case_type)
                            ,: split_type);
                    }


                    // let discrim = indexed_elim!(var!(Bound(0)) ,: discrim_type.as_indexed_type_intro().1.clone());
                    let case_type =
                        case!(
                            var!(Bound(0)),
                            l => first_branch.r#type(Context::new());
                            r => core_term.r#type(Context::new());
                        ,: Univ!());
                    let split_type =
                        split!(
                            var!(Bound(0)),
                            in
                                case_type.clone()
                        ,: Univ!());
                    core_term =
                        split!(
                            var!(Bound(0)),
                            in
                                case!(
                                    var!(Bound(0)),
                                    l => first_branch;
                                    r => core_term;
                                ,: case_type)
                        ,: split_type);

                    let core_term_type = core_term.r#type(Context::new());
                    Box::new(|d: core::Term|
                        indexed_elim!(
                            d.clone(),
                            core_term
                        ,:
                            indexed_elim!(
                                d,
                                core_term_type
                            ,: Univ!())))
                }
            },
            CaseTree::DoNothing(body) => {
                let core_body = lower_body(body);
                let core_body_type = core_body.r#type(Context::new());
                Box::new(|d: core::Term|
                    apply!(
                        fun!(
                            core_body
                        ,:
                            pi!(
                                "match pi",
                                discrim_type,
                                core_body_type.clone()
                            ,: Univ!())),
                        d
                    ,: shift(core_body_type, HashSet::new(), -1)))
            }
        }
    }

    let case_tree = ||
        if let core::InnerTerm::IndexedTypeIntro(index, inner_type) = &*discrim_type.data {
            if *index == 0 {
                let num_inhabs = readback_as_enum_type(&inner_type);
                if num_inhabs > 0 {
                    let mut branches = Vec::new();
                    let mut errors = Vec::new();
                    for n in 0..num_inhabs {
                        match lower_to_case_tree(clauses, Discrim::Enum(n), discrim_type.clone(), exp_type.clone(), match_range, state) {
                            Ok(branch) => branches.push(branch),
                            Err(errs) =>
                                for err in errs {
                                    errors.push(err)
                                }
                        }
                    }
                    if errors.len() > 0 {
                        Err(errors)
                    } else {
                        Ok(CaseTree::Enum(branches))
                    }
                } else {
                    Ok(CaseTree::DoNothing(lower_to_case_tree(clauses, Discrim::Whatever, discrim_type.clone(), exp_type.clone(), match_range, state)?))
                }
            } else {
                Ok(CaseTree::Record(lower_to_case_tree(
                    clauses,
                    Discrim::Record(Vec::new()),
                    discrim_type.clone(),
                    exp_type,
                    match_range,
                    state)?))
            }
        } else {
            match elab_matching_branch(clauses, &Discrim::Whatever, &discrim_type, &exp_type, state) {
                Some(branch) => Ok(CaseTree::DoNothing(CaseTreeBody::Term(branch?))),
                None => Err(vec![Error::new(
                    match_range,
                    state.clone(),
                    InexaustiveMatch { missing_pattern: complete_discrim_to_pattern(&Discrim::Whatever) })])
            }
        };
    let case_tree = case_tree()?;
    // let inner_discrim_type = discrim.r#type(Context::new()).as_indexed_type_intro().1.clone();
    let core_term = lower_to_core(case_tree, discrim_type)(discrim);
    // println!("CORE_TERM\n{:#?}", core_term);
    Ok(core_term)
}

// checks a surface term, and either returns the elaborated term or errors
pub fn elab_term(term: &Term, exp_type: core::Term, state: State) -> ElabResult {
    /*{
        let type_ann = infer_type(term, state.clone(), Some(exp_type.clone()))?;
        if let False(specific) = is_terms_eq(&exp_type, &type_ann, state.locals().equivs()) {
            return Err(vec![Error::new(term.range, state, MismatchedTypes { exp_type, giv_type: type_ann, specific })]);
        }
    }*/
    match &*term.data {
        Ann(ref annd_term, ref type_ann) => {
            let core_type_ann = normalize(elab_term(type_ann, infer_type(type_ann, state.clone(), None)?, state.clone())?, state.locals().clone());
            let cmp = is_terms_eq(&core_type_ann, &exp_type, state.locals().equivs());
            if let False(specific) = cmp {
                return Err(vec![Error::new(term.range, state, MismatchedTypes { exp_type: exp_type, giv_type: core_type_ann, specific })])
            }
            elab_term(annd_term, core_type_ann, state)
        },
        Var(ref name) => {
            match state.get_dec(name) {
                Some((index, var_type)) => {
                    // dbg!((name, index, &var_type));
                    let var_type = normalize(var_type, state.locals().clone());
                    let cmp = is_terms_eq(&var_type, &exp_type, state.locals().equivs());/*
                    if let False(specific) = cmp {
                        Err(vec![Error::new(term.range, state, MismatchedTypes { exp_type, giv_type: var_type, specific })])
                    } else {*/
                        Ok(core::Term::new_with_note(Note(format!("{:?}", name)), Box::new(core::Var(index)), Some(Box::new(var_type))))
                    /*}*/
                },
                None => Err(vec![Error::new(term.range, state, NonexistentVar { name: name.clone() })])
            }
        },
        FunctionTypeIntro(var_name, ref in_type, ref out_type) => {
            // TODO: remove the `?` and add proper error handling
            let mut errors = Vec::new();
            // println!("IN_TYPE_STATE {:?}", state);
            let core_in_type = elab_term(in_type, infer_type(in_type, state.clone(), None)?, state.clone())?;
            // dbg!(&core_in_type);
            // dbg!(normalize(core_in_type.clone(), state.locals().clone()));
            // println!("CORE_IN_TYPE {:?}", core_in_type);
            // println!("IN_TYPE\n{:?}", in_type);
            // println!("CORE_IN_TYPE\n{:?}", core_in_type);
            let core_in_type_type = core_in_type.r#type(Context::new());
            let out_type_context =
                if let Some(some_var_name) = var_name {
                    state.with_dec(some_var_name.clone(), core_in_type.clone())
                } else {
                    state.raw_inc_and_shift(1)
                };
            let core_out_type = elab_term(out_type, infer_type(out_type, out_type_context.clone(), None)?, out_type_context)?;
            // println!("OUT_TYPE\n{:?}", out_type);
            // println!("CORE_OUT_TYPE\n{:?}", core_out_type);
            let core_out_type_type = core_out_type.r#type(Context::new());

            if errors.len() > 0 {
                Err(errors)
            } else {
                Ok(core::Term::new_with_note(
                    Note(format!("{:?}", var_name)),
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
                if let self::core::lang::InnerTerm::FunctionTypeIntro(mut in_type, out_type) = *curr_type.data {
                    in_type.note = Some(Note(format!("{:?} / {:?}", param_name, in_type.note)));
                    in_types.push(in_type.clone());
                    curr_type = out_type;
                    // dbg!(&normal_in_type);
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
                    return Err(vec![Error::new(term.range, state, MismatchedTypes { exp_type, giv_type, specific: Vec::new() })]);
                }
            }

            // println!("CURR_STATE\n{:?}", curr_state);
            // println!("CURR_TYPE {:?}", curr_type);
            let mut body_acc = elab_term(body, curr_type.clone(), curr_state.clone())?;
            body_acc.type_ann = Some(Box::new(curr_type));
            for (i, in_type) in in_types.into_iter().enumerate().rev() {
                let body_acc_type = body_acc.r#type(Context::new());
                let Name(param_name) = param_names.get(i);
                body_acc =
                    fun!(
                        param_name.as_str(),
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
            let abs_type = infer_type(abs, state.clone(), None)?;
            let core_abs = elab_term(abs, abs_type.clone(), state.clone())?; // change to not use `?` later
            if let core::InnerTerm::FunctionTypeIntro(_, _) = &*abs_type.data {
                ()
            } else {
                return Err(vec![Error::new(abs.range, state, ExpectedOfFunctionType { giv_type: abs_type })])
            }

            let mut in_types = Vec::new();
            let mut out_types = vec![abs_type];
            while let core::InnerTerm::FunctionTypeIntro(in_type, out_type) = &*out_types[out_types.len() - 1].data {
                in_types.push(in_type.clone());
                out_types.push(out_type.clone());
            }
            out_types.remove(0);
            if args.len() != in_types.len() {
                return Err(vec![Error::new(term.range, state, MismatchedFunctionArgsNum { exp_num: in_types.len(), giv_num: args.len() })])
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
                _ => Err(vec![Error::new(term.range, state, ExpectedOfTypeType { giv_type: exp_type })])
            }
        },
        EnumIntro(inhabitant) =>
            if let self::core::lang::InnerTerm::IndexedTypeIntro(0, inner_type) = *exp_type.clone().data {
                use self::core::lang::{
                    Term,
                    InnerTerm::*,
                    Doub
                };

                let mut num_inhabitants = readback_as_enum_type(&inner_type);

                if !(*inhabitant < num_inhabitants) {
                    return Err(vec![Error::new(term.range, state, EnumInhabitantTooLarge { inhabitant: *inhabitant, num_inhabitants })]);
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
                Err(vec![Error::new(term.range, state, ExpectedOfEnumType { giv_type: exp_type })])
            },
        TypeTypeIntro =>
            match *exp_type.data {
                core::TypeTypeIntro =>
                    Ok(core::Term::new(
                        Box::new(core::InnerTerm::TypeTypeIntro),
                        Some(Box::new(core::Term::new(
                            Box::new(core::InnerTerm::TypeTypeIntro),
                            None))))),
                _ => Err(vec![Error::new(term.range, state, ExpectedOfTypeType { giv_type: exp_type })])
            },
        ImportTerm(path) => {
            if let Some(entry) = state.get_global_def(path.clone()) {
                Ok(entry.0)
            } else {
                let (item_type, id) =
                    if let Some(entry) = state.get_global_dec(path) {
                        entry
                    } else {
                        return Err(vec![Error::new(term.range, state, NonexistentGlobal { name: path.clone() })]);
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

                let discrim = make_discrim(id, state.num_global_decs);
                let mut core_term =
                    apply!(
                        var!(
                            Bound(state.globals_map_index)),
                        discrim
                    ,: item_type);
                Ok(core_term)
            }
        },
        RecordIntro(fields) => {
            if let core::InnerTerm::IndexedTypeIntro(id, mut inner_type) = *exp_type.data {
                let order = state.get_nominal_id_to_field_order(id).unwrap();
                let field_types = {
                    let mut tmp = Vec::new();
                    while let core::PairTypeIntro(fst_type, snd_type) = *inner_type.data {
                        tmp.push(fst_type);
                        inner_type = snd_type;
                    }
                    tmp
                };
                let ordered_fields = {
                    let mut tmp: Vec<(Name, Term)> = Vec::new();
                    for (name, val) in fields.into_iter() {
                        let i = *order.get(&name).unwrap();
                        let pair = (name.clone(), val.clone());
                        if tmp.len() == 0 || i > tmp.len() - 1 {
                            tmp.push(pair);
                        } else {
                            tmp.insert(i, pair);
                        }
                    }
                    tmp
                };

                let mut core_fields = Vec::new();
                let mut fields_state = state.clone();
                for ((field_name, field_val), field_type) in ordered_fields.iter().zip(field_types.iter()) {
                    let core_field =
                        elab_term(
                            field_val,
                            normalize(
                                field_type.clone(),
                                fields_state.locals().clone().inc_and_shift(2)),
                            fields_state.clone().raw_inc_and_shift(2))?;
                    core_fields.push(core_field.clone());
                    fields_state = fields_state
                        .raw_inc_and_shift(2)
                        .raw_with_dec(field_name.clone(), Bound(0), field_type.clone())
                        .with_def(field_name.clone(), core_field);
                }

                fn make_val(mut core_fields: Vec<core::Term>, mut core_field_types: Vec<core::Term>) -> core::Term {
                    if core_fields.len() == 0 {
                        unit!( ,: make_type(core_field_types))
                    } else {
                        let this_type = make_type(core_field_types.clone());
                        core_field_types.remove(0);
                        pair!(
                            core_fields.remove(0),
                            make_val(core_fields, core_field_types)
                        ,: this_type)
                    }
                }

                fn make_type(mut core_field_types: Vec<core::Term>) -> core::Term {
                    if core_field_types.len() == 0 {
                        Unit!( ,: Univ!())
                    } else {
                        Pair!(
                            core_field_types.remove(0),
                            make_type(core_field_types)
                        ,: Univ!())
                    }
                }

                // println!("CORE_FIELDS {:?}", core_fields);
                // println!("FTs {:?}", field_types);
                let mut val = make_val(core_fields, field_types);
                let val_type = val.r#type(Context::new());
                val = indexed!(val ,: Indexed!(id, val_type ,: Univ!()));
                Ok(val)
            } else {
                return Err(vec![Error::new(term.range, state, ExpectedOfRecordType { giv_type: exp_type })]);
            }
        },
        Match(discrim, clauses) => {
            let discrim_type = infer_type(discrim, state.clone(), None)?;
            let core_discrim = elab_term(discrim, discrim_type.clone(), state.clone())?;
            let mut core_term = elab_match(core_discrim, discrim_type, exp_type.clone(), clauses, &state, term.range)?;
            // core::lang::mark_lines(&mut core_term);
            // dbg!(&core_term);
            // dbg!(core_term.r#type(state.locals().clone()));
            // println!("CHECK:\n{:#?}", core::typing::check(&core_term, exp_type, state.locals().clone()));
            Ok(core_term)
        }
        _ => unimplemented!()
    }
}

pub fn elab_toplevel<'a>(module: &'a Module, module_name: QualifiedName) -> ElabResult {
    fn calc_num_decs(module: &Module) -> usize {
        let mut n = 0;
        for (_, item) in module.items.iter() {
            use InnerItem::*;

            match &item.data {
                Declaration(r#type) => n += 1,
                ModuleDef(submodule) => n += calc_num_decs(submodule),
                _ => ()
            }
        }
        n
    }

    let starting_info = calc_num_decs(module);
    let core_module = elab_module(module, module_name, State::new(starting_info));
    core_module
}

fn elab_module<'a>(module: &'a Module, module_name: QualifiedName, state: State) -> ElabResult {
    #[derive(Debug)]
    enum FlattenedModuleItem<'a> { // local item type for module flattening
        Declaration(Range, &'a crate::lang::surface::Term),
        TermDef(Range, &'a crate::lang::surface::Term),
        RecordTypeDef(Range, &'a AssocSet<Name>, &'a AssocVec<Name, crate::lang::surface::Term>),
    }

    // flatten the module structure, turning it into a more haskell-like structure
    fn flatten_module(module: &Module, module_name: QualifiedName) -> AssocVec<(QualifiedName, ItemKind), FlattenedModuleItem> {
        let mut items = AssocVec::new();
        // println!("ITEMS\n{:#?}", module.items);
        for ((item_name, _), item) in module.items.iter() {
            use InnerItem::*;
            use ItemKind::*;
            // println!("ITEM_NAME {:?}", item_name);
            match &item.data {
                Declaration(r#type) =>
                    { items.insert(
                        (module_name.clone().with_name(item_name.clone()), Dec),
                        FlattenedModuleItem::Declaration(item.range, r#type)); },
                TermDef(term) =>
                    { items.insert(
                        (module_name.clone().with_name(item_name.clone()), Def),
                        FlattenedModuleItem::TermDef(item.range, term)); },
                RecordTypeDef(params, fields) =>
                    { items.insert(
                        (module_name.clone().with_name(item_name.clone()), Def),
                        FlattenedModuleItem::RecordTypeDef(item.range, params, fields)); },
                ModuleDef(submodule) => {
                    let mut flat = flatten_module(&submodule, module_name.clone().with_name(item_name.clone()));
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
                    if let FlattenedModuleItem::Declaration(_, _) = item {
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
                if let FlattenedModuleItem::Declaration(_, _) = item {
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
                FlattenedModuleItem::Declaration(_, r#type) => {
                    let new_state = state.clone().with_globals_map_index((*decs_indices_iter.next().unwrap()));
                    let core_type = elab_term(r#type, infer_type(r#type, new_state.clone(), None)?, new_state)?;
                    state =
                        state.with_global_dec(
                            name.clone(),
                            core_type);
                }
                FlattenedModuleItem::TermDef(range, term) => {
                    let dec = match state.get_global_dec(name) {
                        Some(dec) => dec.0,
                        None => return Err(vec![Error::new(*range, state, NonexistentGlobal { name: name.clone() })])
                    };
                    let core_item_type = normalize(dec, state.locals().clone());
                    let mut core_term =
                        elab_term(
                            term,
                            core_item_type.clone(),
                            state.clone().with_globals_map_index((*defs_indices_iter.next().unwrap())))?;
                    core_term.type_ann = Some(Box::new(core_item_type));
                    core_term.note = Some(Note(format!("{:?} | {}", core_term.note, format!("item {:?}", name))));
                    state = state.with_global_def(name.clone(), core_term.clone());
                    // println!("CORE_TERM {:?}", term);
                    core_items.push(core_term);
                }
                FlattenedModuleItem::RecordTypeDef(range, params, fields) => {
                    let dec = match state.get_global_dec(name) {
                        Some(dec) => dec.0,
                        None => return Err(vec![Error::new(*range, state, NonexistentGlobal { name: name.clone() })])
                    };
                    let core_item_type = normalize(dec, state.locals().clone());
                    let mut record_type_type = core_item_type.clone();
                    let mut fields_state = state.clone();
                    let mut param_types = Vec::new();

                    for param_name in params.iter() {
                        if let core::FunctionTypeIntro(ref in_type, ref out_type) = *record_type_type.data {
                            fields_state = fields_state.with_dec(param_name.clone(), in_type.clone());
                            param_types.push(in_type.clone());
                            record_type_type = out_type.clone();
                        } else {
                            return Err(vec![Error::new(*range, fields_state, ExpectedOfFunctionType { giv_type: record_type_type })]);
                        }
                    }

                    if let core::InnerTerm::TypeTypeIntro = &*record_type_type.data {
                        let mut core_field_types = Vec::new();
                        let mut names_to_order = HashMap::new();

                        for (i, (field_name, field_type)) in fields.iter().enumerate() {
                            fields_state = fields_state.raw_inc_and_shift(2);
                            let core_field_type =
                                normalize(
                                    elab_term(
                                        field_type,
                                        infer_type(field_type, fields_state.clone(), None)?,
                                        fields_state.clone())?,
                                    fields_state.locals().clone());
                            core_field_types.push(core_field_type.clone());
                            fields_state = fields_state.raw_with_dec(field_name.clone(), Bound(0), core_field_type);
                            names_to_order.insert(field_name.clone(), i);
                        }

                        let mut core_record_type = Unit!("core_record_type_unit" ,: Univ!());
                        for core_field_type in core_field_types.into_iter().rev() {
                            core_record_type =
                                Pair!(
                                    core_field_type,
                                    core_record_type
                                ,: Univ!());
                        }

                        let nominal_id = next_nominal_id();
                        let mut core_record_type_cons = Indexed!(nominal_id, core_record_type ,: Univ!());
                        for (i, param_type) in param_types.iter().enumerate().rev() {
                            let core_record_type_cons_type = core_record_type_cons.r#type(Context::new());
                            let Name(param_name) = params.get(i);
                            // TODO: task 3
                            core_record_type_cons =
                                fun!(
                                    param_name.as_str(),
                                    core_record_type_cons
                                ,: 
                                    pi!(
                                        param_type.clone(),
                                        core_record_type_cons_type
                                    ,: Univ!()));
                        }

                        state = state
                            .with_global_def(name.clone(), core_record_type_cons.clone())
                            .with_nominal_id_to_field_order(nominal_id, names_to_order);
                        core_items.push(core_record_type_cons);
                    } else {
                        return Err(vec![Error::new(*range, state, ExpectedOfTypeType { giv_type: record_type_type })])
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