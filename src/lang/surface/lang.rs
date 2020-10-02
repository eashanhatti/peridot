#![allow(warnings)]

use std::collections::{HashSet, HashMap};
extern crate non_empty_collections;
use non_empty_collections::{
	index_map::*,
	index_set::*
};

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

// pub fn is_terms_eq(term1: &Term, term2: &Term) -> bool {
//     match &(&*term1.data, &*term2.data) {
//         (Ann(ref annd_term1, _), Ann(ref annd_term2, _)) => is_terms_eq(annd_term1, annd_term2),
//         (Var(index1), Var(index2)) => index1 == index2,
//         (FunctionTypeIntro(ref in_type1, ref out_type1), FunctionTypeIntro(ref in_type2, ref out_type2)) =>
//             is_terms_eq(in_type1, in_type2) && is_terms_eq(out_type1, out_type2),
//         (FunctionIntro(ref names1, ref body1), FunctionIntro(ref names2, ref body2)) =>
//             is_terms_eq(body1, body2) && names1.len() == names2.len(),
//         (FunctionElim(ref abs1, ref args1), FunctionElim(ref abs2, ref args2)) =>
//             args1.iter().zip(args2.iter()).all(|(t1, t2)| is_terms_eq(t1, t2))
//             && is_terms_eq(abs1, abs2),
//         (TypeTypeIntro(level1), TypeTypeIntro(level2)) => level1 == level2,
//         (RecordTypeIntro(ref field_types1), RecordTypeIntro(ref field_types2)) =>
//             field_types1.len() == field_types2.len()
//             && field_types1.keys().all(|k|
//                 if field_types2.contains_key(k) {
//                     if is_terms_eq(&field_types1.get(k).unwrap(), &field_types2.get(k).unwrap()) {
//                         true
//                     } else {
//                         false
//                     }
//                 } else {
//                     false
//                 }),
//         (RecordIntro(ref fields1), RecordIntro(ref fields2)) =>
//             fields1.len() == fields2.len()
//             && fields1.keys().all(|k|
//                 if fields2.contains_key(k) {
//                     if is_terms_eq(&fields1.get(k).unwrap(), &fields2.get(k).unwrap()) {
//                         true
//                     } else {
//                         false
//                     }
//                 } else {
//                     false
//                 }),
//         (RecordElim(ref record1, ref name1), RecordElim(ref record2, ref name2)) =>
//             is_terms_eq(record1, record2) && name1 == name2,
//         (EnumTypeIntro(ref labels1), EnumTypeIntro(ref labels2)) =>
//             labels1 == labels2,
//         (EnumIntro(ref label1), EnumIntro(ref label2)) => label1 == label2,
//         (Match(ref cases1), Match(ref cases2)) =>
//             cases1.len() == cases2.len()
//             && cases1.keys().all(|k|
//                 if cases2.contains_key(k) {
//                     if is_terms_eq(&cases1.get(k).unwrap(), &cases2.get(k).unwrap()) {
//                         true
//                     } else {
//                         false
//                     }
//                 } else {
//                     false
//                 }),
//         (Let(ref bindings1, ref body1), Let(ref bindings2, ref body2)) =>
//             is_terms_eq(body1, body2)
//             && bindings1.len() == bindings2.len()
//             && bindings1.keys().all(|k|
//                 if bindings2.contains_key(k) {
//                     if is_terms_eq(&bindings1.get(k).unwrap().0, &bindings2.get(k).unwrap().0) && is_terms_eq(&bindings1.get(k).unwrap().1, &bindings2.get(k).unwrap().1) {
//                         true
//                     } else {
//                         false
//                     }
//                 } else {
//                     false
//                 }),
//     }
// }