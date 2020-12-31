#![allow(warnings)]

extern crate pest;
use pest::{
	iterators::*,
	error::*,
	Parser
};
extern crate pest_derive;

use crate::lang::surface::{
	*,
	InnerTerm::*
};
use std::collections::HashSet;

#[derive(pest_derive::Parser)]
#[grammar = "C:\\Users\\Eashan\\dev\\clamn\\src\\pass\\grammar.pest"]
struct LangParser;

pub fn parse_text(input: &str) -> Result<Term, Error<Rule>> { // TODO: error reporting
	let ast = LangParser::parse(Rule::main, input)?.next().unwrap();
	// println!("{:?}", ast);

	fn parse_term(mut pair: Pair<Rule>) -> Term {
		let pair_rule = pair.as_rule();
		let pair_span = pair.as_span();
		let pair_str = pair.as_str();
		let mut pair_iter = pair.into_inner();
		Term {
			data:
				Box::new(match pair_rule {
					Rule::ann => Ann(parse_term(pair_iter.next().unwrap()), parse_term(pair_iter.next().unwrap())),
					Rule::fun => {
						let mut names = HashSet::new();
						for name_pair in pair_iter.next().unwrap().into_inner() {
							names.insert(Name(name_pair.as_str().to_string()));
						}
						FunctionIntro(names, parse_term(pair_iter.next().unwrap()))
					},
					Rule::fun_type =>
						FunctionTypeIntro(
							Name(pair_iter.next().unwrap().as_str().to_string()),
							parse_term(pair_iter.next().unwrap()),
							parse_term(pair_iter.next().unwrap())),
					Rule::fun_elim => FunctionElim(parse_term(pair_iter.next().unwrap()), pair_iter.map(|pair| parse_term(pair)).collect()),
					Rule::type_type => TypeTypeIntro(pair_iter.next().unwrap().as_str().parse::<usize>().unwrap()),
					Rule::var => Var(Name(pair_iter.next().unwrap().as_str().to_string())),
					Rule::fin => EnumIntro(pair_iter.next().unwrap().as_str().parse::<usize>().unwrap()),
					Rule::fin_type => EnumTypeIntro(pair_iter.next().unwrap().as_str().parse::<usize>().unwrap()),
					_ => {
						println!("{:?}, {:?}, {:?}", pair_str, pair_rule, pair_span);
						panic!();
					}
				}),
			range: (pair_span.start(), pair_span.end())
		}
	}

	Ok(parse_term(ast))
}