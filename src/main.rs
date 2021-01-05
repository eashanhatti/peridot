#![allow(warnings)]

mod lang;
use lang::{
	core::{
        self,
        context::*,
        lang::Note,
        VarInner::*
    },
	surface::{
		Term,
		InnerTerm::*,
		Name,
        QualifiedName
	},
};
use std::{
	collections::HashSet,
	iter::FromIterator,
    io::{Read, Write},
    fs::File,
    path::Path,
    thread
};
mod pass;
use pass::{
    surface_to_core::*,
    text_to_surface::*
};

extern crate pest;
#[macro_use]
extern crate pest_derive;

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
                        context.with_dec(Bound(0), core::Term::new_with_note(Note("caps list first".to_string()), Box::new(core::InnerTerm::UnitTypeIntro), univ0.clone())).to_caps_list(0),
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
                let mut file = File::open(&Path::new(&s[5..])).unwrap();
                let mut source = String::new();
                file.read_to_string(&mut source);
                println!("{:?}", source);
                let surface_module = text_to_module(&source);
                s.clear();
                if let Ok(surface_module_ok) = surface_module {
                    println!("{:?}", surface_module_ok);
                    // let surface_term_type = match infer_type(&surface_term, State::new()) {
                    //     Ok(r#type) => r#type,
                    //     Err(errs) => {
                    //         println!("INFER ERROR\n{:#?}", errs);
                    //         continue;
                    //     }
                    // };
                    let core_module = match elab_module(&surface_module_ok, QualifiedName(Vec::new(), Name(String::from("main"))), State::new()) {
                        Ok(module) => module,
                        Err(errs) => {
                            println!("SURFACE ERROR\n{:#?}", errs);
                            continue;
                        }
                    };
                    println!("{:?}", core_module);
                    let core_module_type =
                        match core::typing::synth_type(&core_module, Context::new()) {
                            Ok(r#type) => r#type,
                            Err(errs) => { println!("CORE TYPE ERROR\n{:#?}", errs); return; }
                        };
                    match core::typing::check(&core_module, core_module_type, Context::new()) {
                        Ok(()) => println!("NO ERRORS"),
                        Err(errs) => println!("CORE ERROR\n{:#?}", errs)
                    }
                } else {
                    println!("{:#?}", surface_module);
                }
            },
            "elte" => {
                let mut file = File::open(&Path::new(&s[5..])).unwrap();
                let mut source = String::new();
                file.read_to_string(&mut source);
                println!("{:?}", source);
                let surface_term = text_to_term(&source);
                s.clear();
                if let Ok(surface_term_ok) = surface_term {
                    println!("{:?}", surface_term_ok);
                    let surface_term_type = match infer_type(&surface_term_ok, State::new()) {
                        Ok(r#type) => r#type,
                        Err(errs) => {
                            println!("INFER ERROR\n{:#?}", errs);
                            continue;
                        }
                    };
                    let core_term = match elab_term(&surface_term_ok, surface_term_type, State::new()) {
                        Ok(term) => term,
                        Err(errs) => {
                            println!("SURFACE ERROR\n{:#?}", errs);
                            continue;
                        }
                    };
                    println!("{:?}", core_term);
                    let core_term_type =
                        match core::typing::synth_type(&core_term, Context::new()) {
                            Ok(r#type) => r#type,
                            Err(errs) => { println!("CORE TYPE ERROR\n{:#?}", errs); return; }
                        };
                    match core::typing::check(&core_term, core_term_type, Context::new()) {
                        Ok(()) => println!("NO ERRORS"),
                        Err(errs) => println!("CORE ERROR\n{:#?}", errs)
                    }
                } else {
                    println!("{:#?}", surface_term);
                }
            },
            _ => println!("'{:?}' not a command", &s[0..4])
        }
        s.clear();
    }
}

fn main() {
    run()
}