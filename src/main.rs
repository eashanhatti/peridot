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
	context::*
};

fn w(term: InnerTerm<()>) -> Term<()> { Term(Box::new(term), ()) }

fn main() {
    let test_term: Term<()> =
        w(FunctionElim(
            w(FunctionIntro(
                w(Var(0))
            )),
            w(Var(0))
        ));

    println!("{:?}", normalize(test_term, Context::new()));
}