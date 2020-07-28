// use language::*;

// #[derive(pest::Parser)]
// #[grammar = "C:\\Users\\Eashan\\dev\\moplec\\src\\core\\grammar.pest"]
// struct Parser;

// type Term = Term<()>;

// pub fn parse_to_core(input: String) -> Result<Term, pest::error::Error> {
// 	use pest::iterators::Pair;

// 	let ast = JSONParser::parse(Rule::json, file)?

// 	fn rec(pair: Pair<Rule>) -> Term {
// 		match pair.as_rule() {
// 			Rule::term => {
// 				let inner = pair.into_inner().next().unwrap();
// 				match inner.as_rule() {
// 					Rule::ann => 
// 				}
// 			},
// 			_ => panic!("BUG: toplevel rec only parses full terms")
// 		}
// 	}
// }