#![allow(warnings)]

use super::language::*;
use std::collections::HashSet;
use super::eval::*;

#[derive(Clone, Debug)]
pub struct Context<T>(Vec<(usize, Term<T>)>);

impl<T: Clone> Context<T> {
    pub fn new() -> Self {
        Context(Vec::new())
    }

    pub fn find(self, index: usize) -> Option<Term<T>> {
        let context = self.0;
        for (k, v) in context.into_iter() {
            if k == index {
                return Some(v);
            }
        }
        None
    }

    pub fn inc(self, amount: usize) -> Self {
        let context = self.0;        
        let mut context = context;
        for i in 0..context.len() {
            context[i].0 += amount;
        }
        Context(context)
    }

    pub fn insert(self, index: usize, to_insert: Term<T>) -> Self {
        let context = self.0;
        let mut context = context;
        for i in 0..context.len() {
            if context[i].0 == index {
                panic!("BUG: duplicate var");
            }
        }
        context.push((index, to_insert));
        Context(context)
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
            context[i].1 = shift(context[i].1.clone(), HashSet::new(), amount);
        }
        Context(context)
    }

    pub fn update(self, index: usize, val: Term<T>) -> Self {
    	let mut context = self.0;
    	for i in 0..context.len() {
    		let local_index = index + context[i].0;

    		context[i].1 = normalize(context[i].1.clone(), Context::new().insert(local_index, val.clone()));
    	}
    	Context(context)
    }

    pub fn inc_and_shift(self, amount: usize) -> Self {
        self.inc(amount).shift(amount as isize)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}