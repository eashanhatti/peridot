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
mod pass;
use pass::surface_to_core::*;

fn main() {
    let term =
    	Term {
    		data: Box::new(Var(Name("foo".to_string()))),
    		range: (0, 0),
    	};
    println!("{:?}", elab(&term, core::Term::new(Box::new(core::InnerTerm::DoubTypeIntro), None), State::new()))
}