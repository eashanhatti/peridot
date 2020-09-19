use std::collections::{HashSet, HashMap};

pub struct Name(String);

pub enum Type {
	Enum(HashSet<String>),
	Record(Vec<Term>, HashMap<Name, Term>) // params, field names and types
}

pub enum Item {
	Function(HashSet<Name>, Term),
	Type(Type),
	Namespace(Bindings)
}

pub struct Bindings(HashMap<(Name, Term), Item>);

pub enum Term {
	Var(Name),
	FunctionTypeIntro(Term, Term),
	FunctionIntro(HashSet<Name>, Term),
	FunctionElim(Term, Vec<Term>),
	TypeTypeIntro(usize),
	TypeIntro(Name), // for nominal types
	RecordIntro(Vec<Term>),
	EnumIntro(String),
	NamespaceProj(Name, Name),
	Match(HashMap<Pattern, Term>), // elim form of records and enums
	Let(Bindings, Term)
}

pub enum Pattern {
	Record(HashSet<Pattern>),
	Enum(String),
	Binding(Name) // binding
}