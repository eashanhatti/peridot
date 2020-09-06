#![allow(warnings)]

use super::{
    lang::*,
    eval::*
};
use std::collections::HashSet;

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
pub enum ContextEntryKind {
    Dec,
    Def
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum ContextEntry<T> {
    Declaration(Term<T>),
    Definition(Term<T>)
}

use ContextEntry::*;
use ContextEntryKind::*;

impl<T> ContextEntry<T> {
    fn inner(self) -> Term<T> {
        match self {
            Declaration(d) => d,
            Definition(d) => d
        }
    }
}

#[derive(Clone, Debug)]
pub struct Context<T>(Vec<(usize, ContextEntry<T>)>);

impl<T: Clone> Context<T> {
    pub fn new() -> Self {
        Context(Vec::new())
    }

    pub fn find(&self, kind: ContextEntryKind, index: usize) -> Option<Term<T>> {
        let context = self.clone().0;
        for (k, v) in context.into_iter() {
            if k == index {
                match (v, kind) {
                    (Declaration(d), Dec) => return Some(d),
                    (Definition(d), Def) => return Some(d),
                    _ => ()
                }
            }
        }
        None
    }

    pub fn find_dec(&self, index: usize) -> Option<Term<T>> {
        self.find(Dec, index)
    }

    pub fn find_def(&self, index: usize) -> Option<Term<T>> {
        self.find(Def, index)
    }

    pub fn inc(self, amount: usize) -> Self {
        let context = self.0;        
        let mut context = context;
        for i in 0..context.len() {
            context[i].0 += amount;
        }
        Context(context)
    }

    pub fn insert(self, index: usize, entry: ContextEntry<T>) -> Self {
        let context = self.0;
        let mut context = context;
        for i in 0..context.len() {
            if context[i].0 == index {
                match (&context[i].1, &entry) {
                    (&Declaration(_), &Declaration(_)) => panic!("BUG: duplicate var"),
                    (&Definition(_), &Definition(_)) => panic!("BUG: duplicate var"),
                    _ => ()
                }
            }
        }
        context.push((index, entry));

        Context(context)
    }

    pub fn insert_dec(self, index: usize, entry: Term<T>) -> Self {
        self.insert(index, Declaration(entry))
    }

    pub fn insert_def(self, index: usize, entry: Term<T>) -> Self {
        self.insert(index, Definition(entry))
    }

    pub fn indices(&self) -> HashSet<usize> {
        let context = &self.0;
        let mut set = HashSet::new();
        for (k, _) in context {
            set.insert(*k);
        }
        set
    }

    pub fn shift(self, amount: isize) -> Self {
        let mut context = self.0;
        for i in 0..context.len() {
            match context[i].1 {
                Declaration(ref d) => context[i].1 = Declaration(shift(d.clone(), HashSet::new(), amount)),
                Definition(ref d) => context[i].1 = Definition(shift(d.clone(), HashSet::new(), amount))
            }
        }
        Context(context)
    }

    pub fn update(self, index: usize, val: Term<T>) -> Self {
    	let mut context = self.0;
    	for i in 0..context.len() {
    		let local_index = index + context[i].0;
            match context[i].1 {
                Declaration(ref d) => context[i].1 = Declaration(normalize(d.clone(), Context::new().insert_def(local_index, val.clone()))),
                Definition(ref d) => context[i].1 = Definition(normalize(d.clone(), Context::new().insert_def(local_index, val.clone())))
            }
    	}
    	Context(context)
    }

    pub fn inc_and_shift(self, amount: usize) -> Self {
        self.inc(amount).shift(amount as isize)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn into_iter(self) -> ContextIterator<T> {
        ContextIterator::new(self)
    }
}

pub struct ContextIterator<T> {
    curr: usize,
    context: Context<T>
}

impl<T> ContextIterator<T> {
    fn new(context: Context<T>) -> ContextIterator<T> {
        ContextIterator { curr: 0, context }
    }
}

impl<T: Clone> Iterator for ContextIterator<T> {
    type Item = (usize, ContextEntry<T>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr >= self.context.len() {
            None
        } else {
            let it = Some(self.context.0[self.curr].clone()); // eh, `.clone`? yeah i should fix this later
            self.curr += 1;
            it
        }
    }
}