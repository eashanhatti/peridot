#![allow(warnings)]

extern crate pest;
use pest::{
	iterators::*,
	error::*,
	Parser
};
extern crate pest_derive;
use pest_derive::*;

use crate::lang::surface::{
	*,
	InnerTerm::*
};
use std::collections::{
	HashSet,
	HashMap,
	BTreeMap
};
extern crate assoc_collections;
use assoc_collections::*;

#[derive(pest_derive::Parser)]
#[grammar = "C:\\Users\\Eashan\\dev\\clamn\\bin\\src\\pass\\grammar.pest"]
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
					let mut names = AssocSet::new();
					for name_pair in pair_iter.next().unwrap().into_inner() {
						names.insert(Name(name_pair.as_str().to_string()));
					}
					FunctionIntro(names, parse_term(pair_iter.next().unwrap()))
				},
				Rule::fun_type => {
					let inner = pair_iter.next().unwrap();
					let inner_rule = inner.as_rule();
					let mut inner_iter = inner.into_inner();
					match inner_rule {
						Rule::dependent =>
							FunctionTypeIntro(
								Some(Name(inner_iter.next().unwrap().as_str().to_string())),
								parse_term(inner_iter.next().unwrap()),
								parse_term(inner_iter.next().unwrap())),
						Rule::simple =>
							FunctionTypeIntro(
								None,
								parse_term(inner_iter.next().unwrap()),
								parse_term(inner_iter.next().unwrap())),
						_ => unreachable!()
					}
				},
				Rule::fun_elim => FunctionElim(parse_term(pair_iter.next().unwrap()), pair_iter.map(|pair| parse_term(pair)).collect()),
				Rule::type_type => TypeTypeIntro,
				Rule::var => Var(Name(pair_iter.next().unwrap().as_str().to_string())),
				Rule::fin => EnumIntro(pair_iter.next().unwrap().as_str().parse::<usize>().unwrap()),
				Rule::fin_type => EnumTypeIntro(pair_iter.next().unwrap().as_str().parse::<usize>().unwrap()),
				Rule::import => {
					let mut names =
						pair_iter
							.next().unwrap()
							.into_inner().into_iter()
							.map(|name_pair| Name(name_pair.as_str().to_string()))
							.collect::<Vec<Name>>();
					let item_name = names.pop().unwrap();
					ImportTerm(QualifiedName(names, item_name))
				},
				Rule::record_val => {
					let mut fields = HashMap::new();
					for field_pair in pair_iter {
						let mut inner = field_pair.into_inner();
						let name = Name(inner.next().unwrap().as_str().to_string());
						let val = parse_term(inner.next().unwrap());
						fields.insert(name, val);
					}

					RecordIntro(fields)
				}
				_ => unimplemented!()
			}),
		range: (pair_span.start(), pair_span.end())
	}
}

fn parse_module(mut pair: Pair<Rule>) -> Module {
	if pair.as_rule() == Rule::module {
		let items_iter = pair.into_inner();
		let mut items = AssocVec::new();
		for item in items_iter {
			let rule = item.as_rule();
			let pair_span = item.as_span();
			let mut item_iter = item.into_inner();
			let name = Name(item_iter.next().unwrap().as_str().to_string());
			match rule {
				Rule::dec =>
					items.insert(
						(name, ItemKind::Dec),
						Item {
							data: InnerItem::Declaration(parse_term(item_iter.next().unwrap())),
							range: (pair_span.start(), pair_span.end())
						}),
				Rule::term_def =>
					items.insert(
						(name, ItemKind::Def),
						Item {
							data: InnerItem::TermDef(parse_term(item_iter.next().unwrap())),
							range: (pair_span.start(), pair_span.end())
						}),
				Rule::record_def => {
					let mut param_list = item_iter.next().unwrap();
					let mut field_list = item_iter.next().unwrap();

					let mut param_names = AssocSet::new();
					for param in param_list.into_inner() {
						param_names.insert(Name(param.as_str().to_string()));
					}

					let mut fields = AssocVec::new();
					for field in field_list.into_inner() {
						let mut field_iter = field.into_inner();
						fields.insert(
							Name(field_iter.next().unwrap().as_str().to_string()),
							parse_term(field_iter.next().unwrap()));
					}

					items.insert(
						(name, ItemKind::Def),
						Item {
							data: InnerItem::RecordTypeDef(param_names, fields),
							range: (pair_span.start(), pair_span.end())
						});
				},
				Rule::module_def =>
					items.insert(
						(name, ItemKind::Def),
						Item {
							data: InnerItem::ModuleDef(parse_module(item_iter.next().unwrap())),
							range: (pair_span.start(), pair_span.end())
						}),
				_ => unreachable!()
			};
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