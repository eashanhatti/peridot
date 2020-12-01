#![allow(warnings)]

use std::collections::{HashSet, HashMap};
extern crate non_empty_collections;

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct Name(pub String);

#[derive(Debug, Clone)]
pub enum InnerTerm {
	Ann(Term, Term),
	Var(Name),
	FunctionTypeIntro(Name, Term, Term),
	FunctionIntro(HashSet<Name>, Term),
	FunctionElim(Term, Vec<Term>),
	TypeTypeIntro(usize),
	RecordTypeIntro(HashMap<Name, Term>),
	RecordIntro(HashMap<Name, Term>),
	RecordElim(Term, Name), // term.name
	EnumTypeIntro(HashSet<String>),
	EnumIntro(String),
	Match(HashMap<Pattern, Term>), // elim form of records and enums
	Let(HashMap<Name, (Term, Term)>, Term)
}

#[derive(Debug, Clone)]
pub struct Term {
	pub data: Box<InnerTerm>,
	pub range: (usize, usize),
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum Pattern {
	Record(Vec<Pattern>),
	Enum(String),
	Binding(Name) // binding
}