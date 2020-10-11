#![allow(warnings)]

mod lang;
use lang::{
	core,
	surface::{
		Term,
		InnerTerm::*,
		Name
	}
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
            data: Box::new(core::TypeTypeIntro(0, core::Usage::Unique)),
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
    println!("{:#?}", elab(&var_term, core::Term::new(Box::new(core::InnerTerm::DoubTypeIntro), univ0.clone()), State::new()));
    let core_fun_term =
        elab(
            &fun_term,
            core::Term::new(
                Box::new(core::FunctionTypeIntro(
                    core::Term::new(Box::new(core::InnerTerm::DoubTypeIntro), univ0.clone()),
                    core::Term::new(Box::new(core::InnerTerm::DoubTypeIntro), univ0.clone()),
                    core::Term::new(
                        Box::new(core::FunctionTypeIntro(
                            core::Term::new(Box::new(core::InnerTerm::DoubTypeIntro), univ0.clone()),
                            core::Term::new(Box::new(core::InnerTerm::DoubTypeIntro), univ0.clone()),
                            core::Term::new(Box::new(core::InnerTerm::DoubTypeIntro), univ0.clone()))),
                        univ0.clone()))),
                univ0),
            State::new()).unwrap();
    println!("{:#?}", core_fun_term);
    let core_fun_term_type = match core::typing::synth_type(&core_fun_term, core::context::Context::new()) {
        Ok(r#type) => r#type,
        Err(errs) => { println!("{:#?}", errs); return; }
    };
    println!("{:#?}", core::typing::check(&core_fun_term, core_fun_term_type, core::context::Context::new()));
}

fn main() {
    run()
}