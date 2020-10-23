#![allow(warnings)]

mod lang;
use lang::{
	core::{
        self,
        context::*
    },
	surface::{
		Term,
		InnerTerm::*,
		Name
	},
};
use std::{
	collections::HashSet,
	iter::FromIterator
};
mod pass;
use pass::surface_to_core::*;

fn run() {
    let univ0 =
        Some(Box::new(core::Term {
            data: Box::new(core::TypeTypeIntro(0, core::Usage::Shared)),
            type_ann: None
        }));
    let univ1 =
        Some(Box::new(core::Term {
            data: Box::new(core::TypeTypeIntro(1, core::Usage::Shared)),
            type_ann: None
        }));

	let var_term =
    	Term {
    		data: Box::new(Var(Name("x".to_string()))),
    		range: (0, 0),
    	};
    let fun_term =
    	Term {
    		data:
    			Box::new(FunctionIntro(
    				HashSet::from_iter([Name("x".to_string()), Name("y".to_string())].iter().cloned()),
    				var_term.clone())),
    		range: (0, 1)
    	};
    println!("{:#?}", elab(&var_term, core::Term::new(Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone()), State::new()));
    let context = Context::new().with_dec(0, core::Term::new(Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone()));
    let core_fun_term =
        elab(
            &fun_term,
            core::Term::new(
                Box::new(core::FunctionTypeIntro(
                    context.clone().to_caps_list(0),
                    core::Term::new(Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone()),
                    core::Term::new(
                        Box::new(core::FunctionTypeIntro(
                            context.with_dec(1, core::Term::new(Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone())).to_caps_list(1),
                            core::Term::new(Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone()),
                            core::Term::new(Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone()))),
                        univ0.clone()))),
                univ0),
            State::new()).unwrap_or_else(|errs| { println!("{:#?}", errs); panic!() });
    println!("{:#?}", core_fun_term);
    println!("CORE FN TYPE");
    println!("{:#?}", core_fun_term.clone().type_ann.unwrap());
    let core_fun_term_type = match core::typing::synth_type(&core_fun_term, core::context::Context::new()) {
        Ok(r#type) => r#type,
        Err(errs) => { println!("{:#?}\n{}", errs, errs.len()); return; }
    };
    println!("CORE CHECK FUN");
    let core_check = core::typing::check(&core_fun_term, core_fun_term_type, core::context::Context::new());
    println!("{:#?}\n{}", &core_check, if let Err(ref errs) = core_check { errs.len() } else { 0 });
}

fn main() {
    run()
}