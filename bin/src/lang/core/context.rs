#![allow(warnings)]

use super::{
    lang::{
        *,
        VarInner::*,
        InnerTerm::*
    },
    eval::*
};
use std::{
    collections::{
        HashSet,
        hash_map::{
            HashMap,
            IntoIter
        }
    },
    iter::*
};

#[derive(Copy, Clone, Debug, PartialEq, Hash, Eq)]
pub enum ContextEntryKind {
    Dec,
    Def
}
use ContextEntryKind::*;

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct ContextEntry {
    pub dec: Option<Term>,
    pub def: Option<Term>
}

#[derive(Clone, Debug)]
pub struct Context(HashMap<VarInner, ContextEntry>, HashSet<(VarInner, VarInner)>);

impl Context {
    pub fn new() -> Self {
        Context(HashMap::new(), HashSet::new())
    }

    pub fn exists_dec(&self, index: VarInner) -> bool {
        if let Some(ContextEntry { dec: Some(_), def: _ }) = self.0.get(&index) {
            true
        } else {
            false
        }
    }

    pub fn exists_def(&self, index: VarInner) -> bool {
        if let Some(ContextEntry { dec: _, def: Some(_) }) = self.0.get(&index) {
            true
        } else {
            false
        }
    }

    pub fn get(&self, index: VarInner) -> Option<ContextEntry> {
        match self.0.get(&index) {
            Some(term) => Some(term.clone()),
            None => None
        }
    }

    pub fn get_dec(&self, index: VarInner) -> Option<Term> {
        self.get(index)?.dec
    }

    pub fn get_def(&self, index: VarInner) -> Option<Term> {
        self.get(index)?.def
    }

    pub fn inc(self, amount: isize) -> Self {
        let new_var = |var|
            if let Bound(index) = var {
                Bound(((index as isize) + amount) as usize)
            } else {
                var
            };
        let new = Context(self.0.into_iter().map(|(k, v)| (new_var(k), v)).collect(), self.1);
        new
    }

    pub fn with(mut self, index: VarInner, kind: ContextEntryKind, entry: Term) -> Self {
        if let Some(ContextEntry { ref mut dec, ref mut def }) = self.0.get_mut(&index) {
            match kind {
                Dec => *dec = Some(entry),
                Def => *def = Some(entry),
            }
        } else {
            match kind {
                Dec => { self.0.insert(index, ContextEntry { dec: Some(entry), def: None }); },
                Def => { self.0.insert(index, ContextEntry { dec: None, def: Some(entry) }); }
            }
        }
        Context(self.0, self.1)
    }

    pub fn with_dec(self, index: VarInner, entry: Term) -> Self {
        self.with(index, Dec, entry)
    }

    pub fn with_def(self, index: VarInner, entry: Term) -> Self {
        self.with(index, Def, entry)
    }

    pub fn without(mut self, index: VarInner) -> Self {
        self.0.remove(&index);
        self
    }

    pub fn indices(&self) -> HashSet<usize> {
        let mut set = HashSet::new();
        for key in self.0.keys() {
            if let Bound(index) = key {
                set.insert(*index);
            }
        }
        set
    }

    pub fn shift(self, amount: isize) -> Self {
        Context(
            self.0.into_iter().map(|(k, v)| {
                (k,
                ContextEntry {
                    dec: match v.dec {
                        Some(dec) => Some(shift(dec, HashSet::new(), amount)),
                        None => None
                    },
                    def: match v.def {
                        Some(def) => Some(shift(def, HashSet::new(), amount)),
                        None => None
                    }})}).collect(),
            self.1)
    }

    pub fn update(self, index: VarInner, val: Term) -> Self {
        Context(
            self.0.into_iter().map(|(k, v)|
                (k,
                ContextEntry {
                    dec: match v.dec {
                        Some(dec) =>
                            Some(normalize(
                                dec,
                                Context::new()
                                    .with_def(
                                        if let (Bound(k_bound), Bound(index_bound)) = (index, k) {
                                            Bound(k_bound + index_bound)
                                        } else {
                                            index
                                        },
                                        val.clone()))),
                        None => None
                    },
                    def: match v.def {
                        Some(def) =>
                            Some(normalize(
                                def,
                                Context::new()
                                    .with_def(
                                        if let (Bound(k_bound), Bound(index_bound)) = (index, k) {
                                            Bound(k_bound + index_bound)
                                        } else {
                                            index
                                        },
                                        val.clone()))),
                        None => None
                    }})).collect(),
            self.1)
    }

    pub fn inc_and_shift(self, amount: isize) -> Self {
        self.inc(amount).shift(amount as isize)
    }

    pub fn with_equiv(self, v1: VarInner, v2: VarInner) -> Context {
        let mut equivs = self.1;
        equivs.insert((v1, v2));
        Context(self.0, equivs)
    }

    pub fn equivs(self) -> HashSet<(VarInner, VarInner)> {
        self.1
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn into_iter(self) -> ContextIterator {
        ContextIterator::new(self)
    }
}

pub struct ContextIterator {
    inner_iter: IntoIter<VarInner, ContextEntry>,
}

impl ContextIterator {
    fn new(context: Context) -> ContextIterator {
        ContextIterator { inner_iter: context.0.into_iter() }
    }
}

impl Iterator for ContextIterator {
    type Item = (VarInner, ContextEntry);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner_iter.next()
    }
}

// impl DoubleEndedIterator for ContextIterator {
//     fn next_back(&mut self) -> Option<Self::Item> {
//         self.inner_iter.next_back()
//     }
// }