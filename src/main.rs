extern crate pest;
#[macro_use]
extern crate pest_derive;

mod core;
use crate::core::language::*;
use InnerTerm::*;

fn w(term: InnerTerm<()>) -> Term<()> { (Box::new(term), ()) }

fn main() {
    let test_term: Term<()> =
        w(FunctionElim(
            w(FunctionIntro(
                w(Var(0))
            )),
            w(Var(0))
        ));

    println!("{:?}", normalize(test_term, Vec::new()));
}