#![allow(warnings)]

mod lang;
use lang::{
	core::{
        self,
        context::*,
        lang::Note
    },
	surface::{
		Term,
		InnerTerm::*,
		Name
	},
};
use std::{
	collections::HashSet,
	iter::FromIterator,
    io::Write
};
mod pass;
use pass::{
    surface_to_core::*,
    text_to_surface::*
};

fn run() {
    let univ0 =
        Some(Box::new(core::Term::new(
            Box::new(core::TypeTypeIntro(0, core::Usage::Shared)),
            None
        )));
    let univ1 =
        Some(Box::new(core::Term::new(
            Box::new(core::TypeTypeIntro(1, core::Usage::Shared)),
            None
        )));

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
    // println!("{:#?}", elab(&var_term, core::Term::new(Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone()), State::new()));
    let context = Context::new();
    let core_fun_type =
        core::Term::new(
            Box::new(core::FunctionTypeIntro(
                context.clone().to_caps_list(0),
                core::Term::new_with_note(Note("first parameter".to_string()), Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone()),
                core::Term::new(
                    Box::new(core::FunctionTypeIntro(
                        context.with_dec(0, core::Term::new_with_note(Note("caps list first".to_string()), Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone())).to_caps_list(0),
                        core::Term::new_with_note(Note("second parameter".to_string()), Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone()),
                        core::Term::new_with_note(Note("out".to_string()), Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone()))),
                    univ0.clone()))),
            univ0);
    let core_fun_term =
        elab_term(
            &fun_term,
            core_fun_type.clone(),
            State::new()).unwrap_or_else(|errs| { println!("{:#?}", errs); panic!() });/*
    let core_fun_type_check = core::typing::check(&core_fun_type, core::typing::synth_type(&core_fun_type, Context::new()).unwrap(), Context::new());
    println!("CORE FUN TYPE CHECK\n{:#?}\nFN TYPE ERRS{}", &core_fun_type_check, if let Err(ref errs) = core_fun_type_check { errs.len() } else { 0 });
    if let Err(_) = core_fun_type_check {
        return;
    }
    let core_fun_term_check = core::typing::check(&core_fun_term, core_fun_type, Context::new());
    println!("CORE FUN TERM CHECK\n{:#?}\nFN TERM ERRS{}", &core_fun_term_check, if let Err(ref errs) = core_fun_term_check { errs.len() } else { 0 });*/
    // println!("{:?}", core_fun_type);
    // println!("{:?}", core::typing::synth_type(&core_fun_term, Context::new()));
    // println!("{:?}", core::lang::is_terms_eq(&core_fun_type, &core::typing::synth_type(&core_fun_term, Context::new()).unwrap()));
    let mut s = String::new();
    loop {
        print!("> ");
        std::io::stdout().flush();
        std::io::stdin().read_line(&mut s).unwrap();
        
        if let Some('\n') = s.chars().next_back() { s.pop(); }
        if let Some('\r') = s.chars().next_back() { s.pop(); }

        match &s[0..4] {
            "exit" => break,
            "elab" => {
                let ast = parse_text((&s[5..s.len()]).to_string());
                s.clear();
                if let Ok(ast_ok) = ast {
                    println!("{:#?}", &ast_ok);
                    let surface_term = lower_to_surface(ast_ok);
                    let surface_term_type = match infer_type(&surface_term, State::new()) {
                        Ok(r#type) => r#type,
                        Err(errs) => {
                            println!("INFER ERROR\n{:#?}", errs);
                            continue;
                        }
                    };
                    let core_term = match elab_term(&surface_term, surface_term_type, State::new()) {
                        Ok(term) => term,
                        Err(errs) => {
                            println!("SURFACE ERROR\n{:#?}", errs);
                            continue;
                        }
                    };
                    match core::typing::check(&core_term, core::typing::synth_type(&core_term, Context::new()).unwrap(), Context::new()) {
                        Ok(()) => println!("CORE TERM\n{:#?}", core_term),
                        Err(errs) => println!("CORE ERROR\n{:#?}", errs)
                    }
                } else {
                    println!("{:#?}", ast);
                }
            }
            "eq?" => {
                let mut in1 = String::new();
                std::io::stdin().read_line(&mut in1).unwrap();
                let mut in2 = String::new();
                std::io::stdin().read_line(&mut in2).unwrap();
                let ast1 = parse_text(in1.clone());
                let ast2 = parse_text(in1.clone());
            }
            _ => println!("'{:?}' not a command", &s[0..4])
        }
        s.clear();
    }
}

fn main() {
    run()
}