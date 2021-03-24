#![allow(warnings)]

mod lang;
use lang::{
	core::{
        self,
        context::*,
        lang::{
            Note,
            mark_lines
        },
        InnerVar::*
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

macro_rules! if_opt {
    ($opt:expr, $opts:expr, $body:expr) => {{
        if $opts.contains($opt) {
            $body
        }
    }};
}

fn run() {
    let mut args = { let mut tmp = std::env::args(); tmp.next(); tmp };
    let filename =
        match args.next() {
            Some(filename) => filename,
            None => {
                println!("PROVIDE FILE TO ELAB");
                return;
            }
        };
    let options = args.next().unwrap_or(String::new());
    println!("FILENAME {}", filename);
    let mut file =
        match File::open(&Path::new(&filename)) {
            Ok(file) => file,
            Err(err) => {
                println!("CANNOT OPEN FILE \"{}\"\n{}", filename, err);
                return;
            }
        };
    let mut source = String::new();
    file.read_to_string(&mut source);
    if_opt!("ptext", &options, println!("SOURCE\n{}", source));
    let surface_module = text_to_module(&source);
    if_opt!("past", &options, println!("AST {:#?}", surface_module));

    if let Ok(surface_module_ok) = surface_module {
        let core_module = {
            let mut tmp =
                match elab_toplevel(&surface_module_ok, QualifiedName(Vec::new(), Name(String::from("main")))) {
                    Ok(module) => {
                        println!("NO SURFACE ERRORS");
                        module
                    },
                    Err(errs) => {
                        println!("SURFACE ERROR\n{:#?}", errs);
                        return;
                    }
                };
            mark_lines(&mut tmp);
            tmp
        };

        if_opt!("pcore", &options, println!("CORE TERM\n{:?}", core_module));
        if_opt!("dcoretc", &options, {
            let core_module_type =
                match core::typing::synth_type(&core_module, Context::new()) {
                    Ok(r#type) => r#type,
                    Err(errs) => { println!("CORE TYPE ERROR\n{:#?}", errs); return; }
                };
            println!("CORE TYPECHECK");
            let now = std::time::Instant::now();
            match core::typing::check(&core_module, core_module_type, Context::new()) {
                Ok(()) => println!("NO CORE ERRORS"),
                Err(errs) => println!("CORE ERROR\n{:#?}", errs)
            }
            println!("END CORE TYPECHECK, TIME {:?}", now.elapsed());
        });
    } else {
        println!("PARSING ERROR\n{:?}", surface_module);
    }
}

fn main() {
    run();
}