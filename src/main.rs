#![allow(warnings)]

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod core;
use self::core::{
	language::{
		*,
		InnerTerm::*
	},
	eval::*,
	context::*,
	typing::*
};

// fn w<'a>(info: &'a str, term: InnerTerm<&'a str>) -> Term<&'a str> { Term(Box::new(term), info) }

fn main() {
    
}