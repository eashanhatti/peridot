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
use std::collections::{
	HashSet,
	BTreeMap,
	BTreeSet
};

#[derive(pest_derive::Parser)]
#[grammar = "C:\\Users\\Eashan\\dev\\clamn\\src\\pass\\grammar.pest"]
struct LangParser;

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
						let mut names = BTreeSet::new();
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
					_ => unreachable!()
				}),
			range: (pair_span.start(), pair_span.end())
		}
	}

	fn parse_module(mut pair: Pair<Rule>) -> Module {
		if pair.as_rule() == Rule::module {
			let items_iter = pair.into_inner();
			let mut items = BTreeMap::new();
			for item in items_iter {
				let rule = item.as_rule();
				let mut item_iter = item.into_inner();
				let name = Name(item_iter.next().unwrap().as_str().to_string());
				let body = parse_term(item_iter.next().unwrap());
				match rule {
					Rule::dec => { items.insert((name, ItemKind::Dec), Item::Declaration(body)); },
					Rule::term_def => { items.insert((name, ItemKind::Def), Item::TermDef(body)); },
					_ => unreachable!()
				}
			}

			Module { items }
		} else {
			unreachable!()
		}
	}

pub fn text_to_module(input: &str) -> Result<Module, Error<Rule>> { // TODO: error reporting
	let ast = LangParser::parse(Rule::module, input)?.next().unwrap();
	Ok(parse_module(ast))
}

pub fn text_to_term(input: &str) -> Result<Term, Error<Rule>> { // TODO: error reporting
	let ast = LangParser::parse(Rule::term, input)?.next().unwrap();
	Ok(parse_term(ast))
}