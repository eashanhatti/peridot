#![allow(warnings)]

use crate::lang::core::lang::Symbol;
use std::collections::HashMap;
extern crate assoc_collections;
use assoc_collections::*;

pub type Range = (usize, usize);

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
pub enum InnerItem {
	Declaration(Term), // `x : t`, `TermDef` and `RecordTypeDef` are for `x = v`
	TermDef(Term),
	RecordTypeDef(AssocSet<Name>, AssocVec<Name, Term>),
	ModuleDef(Module)
}

#[derive(Debug)]
pub struct Item {
	pub data: InnerItem,
	pub range: Range
}

pub enum Visibility {
	Private,
	Public
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ItemKind { Dec, Def }

#[derive(Debug)]
pub struct Module {
	pub items: AssocVec<(Name, ItemKind), Item>
}

#[derive(Debug, Clone)]
pub enum InnerTerm {
	Ann(Term, Term),
	Var(Name),
	ImportTerm(QualifiedName),
	FunctionTypeIntro(Option<Name>, Term, Term),
	FunctionIntro(AssocSet<Name>, Term),
	FunctionElim(Term, Vec<Term>),
	TypeTypeIntro,
	RecordIntro(HashMap<Name, Term>),
	EnumTypeIntro(usize),
	EnumIntro(usize),
	Match(Term, Vec<(Pattern, Term)>), // elim form of records and enums
	Let(AssocVec<Name, Term>, Term)
}

#[derive(Debug, Clone)]
pub struct Term {
	pub data: Box<InnerTerm>,
	pub range: Range,
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub struct Pattern {
	pub data: Box<InnerPattern>,
	pub range: Range
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum InnerPattern {
	Record(Vec<Pattern>),
	Enum(usize),
	Binding(Name)
}