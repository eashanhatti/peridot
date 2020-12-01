#![allow(warnings)]

extern crate earlgrey;
extern crate regex;
use crate::lang::surface::{
    *,
    InnerTerm::{
    	self,
    	*
    },
};
use std::collections::hash_set::HashSet;

#[derive(Debug, Clone)]
pub enum Ast {
	Function(Box<Ast>, Box<Ast>),
	PiType(Box<Ast>, Box<Ast>, Box<Ast>),
	Call(Box<Ast>, Box<Ast>),
	Var(Box<Ast>),
	Ann(Box<Ast>, Box<Ast>),
	ParamsList(Box<Ast>, Option<Box<Ast>>),
	ArgsList(Box<Ast>, Option<Box<Ast>>),
	Id(String),
	Dummy
}

impl Ast {
	fn to_function(self) -> (Box<Ast>, Box<Ast>) {
		match self {
			Ast::Function(ast1, ast2) => (ast1, ast2),
			_ => panic!()
		}
	}
	fn to_pitype(self) -> (Box<Ast>, Box<Ast>, Box<Ast>) {
		match self {
			Ast::PiType(ast1, ast2, ast3) => (ast1, ast2, ast3),
			_ => panic!()
		}
	}
	fn to_var(self) -> Box<Ast> {
		match self {
			Ast::Var(ast) => ast,
			_ => panic!()
		}
	}
	fn to_ann(self) -> (Box<Ast>, Box<Ast>) {
		match self {
			Ast::Ann(ast1, ast2) => (ast1, ast2),
			_ => panic!()
		}
	}
	fn to_paramslist(self) -> (Box<Ast>, Option<Box<Ast>>) {
		match self {
			Ast::ParamsList(ast1, ast2) => (ast1, ast2),
			_ => panic!()
		}
	}
	fn to_id(self) -> String {
		match self {
			Ast::Id(name) => name,
			_ => panic!()
		}
	}
	fn to_dummy(self) {
		match self {
			Ast::Dummy => (),
			_ => panic!()
		}
	}
	fn to_call(self) -> (Box<Ast>, Box<Ast>) {
		match self {
			Ast::Call(ast1, ast2) => (ast1, ast2),
			_ => panic!()
		}
	}
	fn to_argslist(self) -> (Box<Ast>, Option<Box<Ast>>) {
		match self {
			Ast::ArgsList(ast1, ast2) => (ast1, ast2),
			_ => panic!()
		}
	}
}

fn build_grammar() -> earlgrey::Grammar {
	earlgrey::GrammarBuilder::default()
		.nonterm("Term")
		.nonterm("Function")
		.nonterm("PiType")
		.nonterm("Var")
		.nonterm("Ann")
		.nonterm("ParamsList")
		.nonterm("Call")
		.nonterm("ArgsList")
		.terminal("fn", |s| s == "fn")
		.terminal("=>", |s| s == "=>")
		.terminal("{", |s| s == "{")
		.terminal("}", |s| s == "}")
		.terminal("->", |s| s == "->")
		.terminal("[a-zA-Z]+", |s| regex::Regex::new("^[[:alpha:]]+$").unwrap().is_match(s))
		.terminal(":", |s| s == ":")
		.terminal(",", |s| s == ",")
		.terminal("(", |s| s == "(")
		.terminal(")", |s| s == ")")
		.terminal("[", |s| s == "[")
		.terminal("]", |s| s == "]")
		.rule("Term", &["Function"])
		.rule("Term", &["PiType"])
		.rule("Term", &["Var"])
		.rule("Term", &["Ann"])
		.rule("Term", &["Call"])
		.rule("Term", &["(", "Term", ")"])
		.rule("Function", &["fn", "ParamsList", "=>", "Term"])
		.rule("PiType", &["{", "[a-zA-Z]+", ":", "Term", "}", "->", "Term"])
		.rule("Var", &["[a-zA-Z]+"])
		.rule("Ann", &["Term", ":", "Term"])
		.rule("ParamsList", &["[a-zA-Z]+", "ParamsList"])
		.rule("ParamsList", &["[a-zA-Z]+"])
		.rule("Call", &["Term", "(", "ArgsList", ")"])
		.rule("ArgsList", &["Term", ",", "ArgsList"])
		.rule("ArgsList", &["Term"])
		.into_grammar("Term")
		.unwrap()
}

fn build_semanter<'a>() -> earlgrey::EarleyForest<'a, Ast> {
    let mut ev = earlgrey::EarleyForest::new(|symbol, token| {
    	match symbol {
    		"[a-zA-Z]+" => Ast::Id(token.to_string()),
    		_ => Ast::Dummy
    	}
    });
    ev.action("Function -> fn ParamsList => Term", |s| Ast::Function(Box::new(s[1].clone()), Box::new(s[3].clone())));
    ev.action("PiType -> { [a-zA-Z]+ : Term } -> Term", |s| Ast::PiType(Box::new(s[1].clone()), Box::new(s[3].clone()), Box::new(s[6].clone())));
    ev.action("Var -> [a-zA-Z]+", |s| Ast::Var(Box::new(s[0].clone())));
    ev.action("Ann -> Term : Term", |s| Ast::Ann(Box::new(s[0].clone()), Box::new(s[2].clone())));
    ev.action("ParamsList -> [a-zA-Z]+ , ParamsList", |s| Ast::ParamsList(Box::new(s[0].clone()), Some(Box::new(s[2].clone()))));
    ev.action("ParamsList -> [a-zA-Z]+", |s| Ast::ParamsList(Box::new(s[0].clone()), None));
    ev.action("Term -> Var", |s| s[0].clone());
    ev.action("Term -> Ann", |s| s[0].clone());
    ev.action("Term -> Function", |s| s[0].clone());
    ev.action("Term -> PiType", |s| s[0].clone());
    ev.action("Term -> ( Term )", |s| s[1].clone());
    ev.action("Term -> Call", |s| s[0].clone());
    ev.action("Call -> Term ( ArgsList )", |s| Ast::Call(Box::new(s[0].clone()), Box::new(s[2].clone())));
    ev.action("ArgsList -> Term , ArgsList", |s| Ast::ArgsList(Box::new(s[0].clone()), Some(Box::new(s[2].clone()))));
    ev.action("ArgsList -> Term", |s| Ast::ArgsList(Box::new(s[0].clone()), None));
    ev
}

pub fn parse_text(text: String) -> Result<Ast, String> {
	let parser = earlgrey::EarleyParser::new(build_grammar());
	let semanter = build_semanter();
	let trees = parser.parse(text.split_whitespace())?;
	semanter.eval((&trees))
}

pub fn lower_to_surface(ast: Ast) -> Term {
	Term {
		data: Box::new(match ast {
			Ast::Function(params, body) => {
				let mut bindings = HashSet::new();
				let mut rest_params = Some(params);
				while let Some(rest_params_some) = rest_params {
					let (param_name, others) = rest_params_some.to_paramslist();
					if !bindings.insert(Name(param_name.to_id())) {
						// need a better way to do this
						// user should be alerted to duplicate param names
						panic!("duplicate params");
					}
					rest_params = others;
				}
				InnerTerm::FunctionIntro(bindings, lower_to_surface(*body))
			},
			Ast::Call(fun, args_ast) => {
				let mut args = Vec::new();
				let mut rest_args = Some(args_ast);
				while let Some(rest_args_some) = rest_args {
					let (arg, others) = rest_args_some.to_argslist();
					args.push(lower_to_surface(*arg));
					rest_args = others;
				}
				InnerTerm::FunctionElim(lower_to_surface(*fun), args)
			}
			Ast::PiType(name, in_type, out_type) => InnerTerm::FunctionTypeIntro(Name(name.to_id()), lower_to_surface(*in_type), lower_to_surface(*out_type)),
			Ast::Var(name) => InnerTerm::Var(Name(name.to_id())),
			Ast::Ann(annd_term, type_ann) => InnerTerm::Ann(lower_to_surface(*annd_term), lower_to_surface(*type_ann)),
			_ => panic!()
		}),
		range: (0, 0)
	}
}