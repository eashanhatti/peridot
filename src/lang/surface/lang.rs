#![allow(warnings)]

use std::collections::{HashSet, HashMap, BTreeMap}; 

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct Name(pub String);

pub type ModulePath = Vec<Name>;

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct QualifiedName(pub ModulePath, pub Name);

impl QualifiedName {
	pub fn with_name(self, name: Name) -> Self {
		let mut path = self.0;
		path.push(self.1);
		QualifiedName(path, name)
	}
}

#[derive(Debug)]
pub enum Item {
	Declaration(Term), // `x : t`, `TermDef` and `RecordTypeDef` are for `x = v`
	TermDef(Term),
	RecordTypeDef(HashMap<Name, Term>),
	ModuleDef(Module)
}

pub enum Visibility {
	Private,
	Public
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ItemKind { Dec, Def }

#[derive(Debug)]
pub struct Module {
	pub items: BTreeMap<(Name, ItemKind), Item>
}

#[derive(Debug, Clone)]
pub enum InnerTerm {
	Ann(Term, Term),
	Var(Name),
	ImportTerm(QualifiedName),
	FunctionTypeIntro(Name, Term, Term),
	FunctionIntro(HashSet<Name>, Term),
	FunctionElim(Term, Vec<Term>),
	TypeTypeIntro(usize),
	RecordTypeIntro(QualifiedName, HashMap<Name, Term>),
	RecordIntro(HashMap<Name, Term>),
	EnumTypeIntro(usize),
	EnumIntro(usize),
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
	Enum(usize),
	Binding(Name) // binding
}