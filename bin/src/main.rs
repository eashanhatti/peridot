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
extern crate indoc;
use indoc::indoc;

macro_rules! if_opt {
    ($opt:expr, $opts:expr, $body:expr) => {{
        if $opts.contains($opt) {
            $body
        }
    }};
}

fn run(options: String, source: String) -> Result<(), ()> {
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
                        println!("SURFACE ERRORS");
                        for err in errs {
                            println!("SOURCE\n{}", &source[err.range.0..err.range.1]);
                            println!("ERROR\n{:#?}", err);
                        }
                        return Err(());
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
                    Err(errs) => { println!("CORE TYPE ERROR\n{:#?}", errs); return Err(()); }
                };
            // println!("CORE TYPECHECK");
            let now = std::time::Instant::now();
            match core::typing::check(&core_module, core_module_type, Context::new()) {
                Ok(()) => println!("NO CORE ERRORS"),
                Err(errs) => { println!("CORE ERROR\n{:#?}", errs); return Err(()) }
            }
            // println!("END CORE TYPECHECK, TIME {:?}", now.elapsed());
        });
        Ok(())
    } else {
        println!("PARSING ERROR\n{:?}", surface_module);
        Err(())
    }
}

fn main() {
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
    run(options, source);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn id_fun() {
        let source = indoc!{"
            module
                id : [T : Type] -> T -> T;
                id = fn T x => x;
            end
        "}.to_string();

        assert_eq!(run(String::from("dcoretc"), source), Ok(()));
    }

    #[test]
    fn records1() {
        let source = indoc!{"
            module
                Pair : Type -> Type -> Type;
                Pair = record A B where
                    fst : A
                    snd : B
                end;

                example : [T : Type] -> T -> ((import main.Pair)(T, Fin 1));
                example = fn T x => record [
                    fst = x,
                    snd = fin 0
                ];
            end
        "}.to_string();

        assert_eq!(run(String::from("dcoretc"), source), Ok(()));
    }

    #[test]
    fn records2() {
        let source = indoc!{"
            module
                Exists : Type;
                Exists = record where
                    T : Type
                    x : T
                end;

                example : [A : Type] -> A -> import main.Exists;
                example = fn A a => record [
                    T = A,
                    x = a
                ];
            end
        "}.to_string();

        assert_eq!(run(String::from("dcoretc"), source), Ok(()));
    }

    #[test]
    fn records3() {
        let source = indoc!{"
            module
                Pair : Type -> Type -> Type;
                Pair = record A B where
                    fst : A
                    snd : B
                end;

                example : [T : Type] -> T -> ((import main.Pair)(T, T));
                example = fn T x => record [
                    fst = x,
                    snd = x
                ];
            end
        "}.to_string();

        assert_eq!(run(String::from("dcoretc"), source), Ok(()));
    }

    #[test]
    fn records4() {
        let source = indoc!{"
            module
                Exists : Type;
                Exists = record where
                    T : Type
                    x : T
                end;

                example : import main.Exists;
                example = record [
                    T = [A : Type] -> A -> A,
                    x = fn A a => a
                ];
            end
        "}.to_string();

        assert_eq!(run(String::from("dcoretc"), source), Ok(()));        
    }
}