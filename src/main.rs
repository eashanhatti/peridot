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

fn w<'a>(info: &'a str, term: InnerTerm<&'a str>) -> Term<&'a str> { Term(Box::new(term), info) }

fn main() {
    let test_term: Term<_> =
  //  		w(Ann(
	 //    	w(FunctionElim(
		//         w(Ann(
		//         	w(FunctionIntro(
		//         		w(Var(0))
		//         	)),
		//         	w(FunctionTypeIntro(
		//         		w(EnumTypeIntro(1)),
		//         		w(EnumTypeIntro(1))
		//         	))
		//         )),
		//         w(Ann(
		//         	w(EnumIntro(0)),
		//         	w(EnumTypeIntro(1))
		//         ))
		//     )),
	 //    	w(EnumTypeIntro(1))
		// ));
		// w(Ann(
		// 	w(FunctionElim(
		// 		w(EnumTypeIntro(42)),
		// 		w(EnumIntro(1))
		// 	)),
		// 	w(PairTypeIntro(
		// 		w(Ann(w(EnumIntro(0)), w(EnumTypeIntro(1)))),
		// 		w(Ann(w(EnumIntro(1)), w(EnumTypeIntro(2))))
		// 	))
		// ));
		// w("", Ann(
		// 	w("", FunctionIntro(
		// 		w("", Ann(
		// 			w("", FunctionIntro(
		// 				w("", Ann(
		// 					w("inner fn", Var(0)),
		// 					w("inner fn", Var(1))
		// 				))
		// 			)),
		// 			w("", FunctionTypeIntro(
		// 				w("inner fn type ann", Var(0)),
		// 				w("inner fn type ann", Var(1))
		// 			))
		// 		))
		// 	)),
		// 	w("", Ann(
		// 		w("", FunctionTypeIntro(
		// 			w("", UniverseIntro(0, Usage::Unique)),
		// 			w("", FunctionTypeIntro(
		// 				w("outer fn type ann", Var(0)),
		// 				w("outer fn type ann", Var(1))
		// 			))
		// 		)),
		// 		w("", UniverseIntro(1, Usage::Unique))
		// 	))
		// ));
		w("", Ann(
			w("", FunctionTypeIntro(
				w("", UniverseIntro(0, Usage::Unique)),
				w("", FunctionTypeIntro(
					w("outer fn type ann var 0", Var(0)),
					w("outer fn type ann var 1", Var(1)),
				))
			)),
			w("", UniverseIntro(1, Usage::Unique))
		));

	match test_term.r#type(Context::new()) {
		Ok(r#type) => println!("{:#?}", check(&test_term, r#type, Context::new())),
		Err(errs) => println!("{:#?}", errs)
	}
}