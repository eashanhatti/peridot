extern crate pest;
#[macro_use]
extern crate pest_derive;

mod core;
use crate::core::language::*;
use InnerTerm::*;

fn w(term: InnerTerm<()>) -> Term<()> { (Box::new(term), ()) }

fn main() {
    let test_term: Term<()> = w(
        Apply(
            w(Function(
                w(Var(0))
            )),
            w(Constant(42))
        )
    );

    println!("{:?}", normalize(test_term));
}