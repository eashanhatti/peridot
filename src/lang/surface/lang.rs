#![allow(warnings)]

use std::collections::{HashSet, HashMap};
extern crate non_empty_collections;

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct Name(pub String);

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct Label(pub String); // for enums

pub type ModulePath = Vec<Name>;

pub enum Item {
	TermDef(Term),
	RecordTypeDef(HashMap<Name, Term>), // nominal
	ModuleDef(Module)
}

pub enum Visibility {
	Private,
	Public
}

pub struct Module {
	defs: HashMap<Name, (Visibility, Item)>
}

#[derive(Debug, Clone)]
pub enum InnerTerm {
	Ann(Term, Term),
	Var(Name),
	ImportTerm(ModulePath, Name), // module path, term name
	FunctionTypeIntro(Name, Term, Term),
	FunctionIntro(HashSet<Name>, Term),
	FunctionElim(Term, Vec<Term>),
	TypeTypeIntro(usize),
	RecordTypeIntro(ModulePath, Name), // identify nominal types by module path and name
	RecordIntro(HashMap<Name, Term>),
	EnumTypeIntro(HashSet<Label>),
	EnumIntro(Label),
	Match(HashMap<Pattern, Term>), // elim form of records and enums
	Let(HashMap<Name, Term>, Term)
}

#[derive(Debug, Clone)]
pub struct Term {
	pub data: Box<InnerTerm>,
	pub range: (usize, usize),
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum Pattern {
	Record(Vec<Pattern>),
	Enum(Label),
	Binding(Name) // binding
}