use std::collections::{
    HashSet,
    HashMap
};
use crate::{
    lang::{
        core::{
            self,
            context::*,
            eval::shift,
            lang::{
                VarInner::*,
                VarInner,
                Symbol
            },
        },
        surface::*
    }
};
extern crate macros;
use macros::*;

// globals maps names to type id pairs
// id is used to calculate the arg needed to pass to the globals map at index zero in order to get that global term
// global_id is used as a source of fresh ids
#[derive(Clone, Debug)]
pub struct State {
	locals: Context,
    local_names_to_indices: HashMap<Name, VarInner>,
    globals: HashMap<QualifiedName, (core::Term, core::Term, usize)>, // dec, def, id
    global_id: usize,
    pub globals_map_index: usize,
    pub num_global_decs: usize
}

impl State {
	pub fn new(num_global_decs: usize) -> State {
        let map1: HashMap<Name, VarInner> = HashMap::new();
        let map2: HashMap<QualifiedName, (core::Term, core::Term, usize)> = HashMap::new();
		State {
            locals: Context::new(),
            local_names_to_indices: map1,
            globals: map2,
            global_id: 0,
            globals_map_index: 0,
            num_global_decs
        }
	}

    pub fn with_dec(self, name: Name, r#type: core::Term) -> State {
        let mut local_names_to_indices: HashMap<Name, VarInner> =
            self.local_names_to_indices.into_iter().map(|(k, v)|
                if let Bound(index) = v {
                    (k, Bound(index + 1))
                } else {
                    (k, v)
                }).collect();
        local_names_to_indices.insert(name, Bound(0));

        State {
            locals: self.locals.inc_and_shift(1).with_dec(Bound(0), shift(r#type, HashSet::new(), 1)),
            local_names_to_indices,
            globals_map_index: self.globals_map_index + 1,
            ..self
        }
    }

    // declare before use, `with_dec(name, _)` must have been called before this is
    pub fn with_def(self, name: Name, value: core::Term) -> State {
        if let Some(index) = self.local_names_to_indices.get(&name) {
            if self.locals.exists_dec(*index) {
                State {
                    locals: self.locals.with_def(*index, value),
                    ..self
                }
            } else {
                panic!("var must be declared before being given a definition")
            }
        } else {
            panic!("var must be declared before being given a definition")
        }
    }

    pub fn get(&self, name: &Name) -> Option<(VarInner, ContextEntry)> {
        if let Some(index) = self.local_names_to_indices.get(name) {
            if let Some(entry) = self.locals.get(*index) {
                return Some((*index, entry));
            }
        }
        None
    }

    pub fn get_dec(&self, name: &Name) -> Option<(VarInner, core::Term)> {
        let entry = self.get(name)?;
        Some((entry.0, entry.1.dec?))
    }

    pub fn get_def(&self, name: &Name) -> Option<(VarInner, core::Term)> {
        let entry = self.get(name)?;
        Some((entry.0, entry.1.def?))
    }

    pub fn with_global_dec(self, name: QualifiedName, r#type: core::Term) -> State {
        if let Some(_) = self.globals.get(&name) {
            panic!("duplicate global");
        } else {
            let mut globals = self.globals;
            globals.insert(name, (r#type.clone(), postulate!(Symbol(rand::random::<usize>()) ,: r#type), self.global_id));
            State {
                globals,
                global_id: self.global_id + 1,
                ..self
            }
        }
    }

    pub fn with_global_def(mut self, name: QualifiedName, value: core::Term) -> State {
        if let Some((r#type, _, id)) = self.globals.get(&name) {
            let r#type = r#type.clone();
            let id = *id;
            self.globals.insert(name, (r#type, value.clone(), id));
            self
        } else {
            panic!("undeclared global {:?}", name);
        }
    }

    pub fn get_global_dec(&self, name: &QualifiedName) -> Option<(core::Term, usize)> {
        if let Some(entry) = self.globals.get(name) {
            Some((entry.0.clone(), entry.2))
        } else {
            None
        }
    }

    pub fn get_global_def(&self, name: QualifiedName) -> Option<(core::Term, usize)> {
        if let Some((_, value, id)) = self.globals.get(&name) {
            Some((value.clone(), *id))
        } else {
            None
        }
    }

    pub fn iter_globals(&self) -> GlobalsIterator {
        GlobalsIterator {
            id: Some(0),
            globals: &self.globals
        }
    }

    pub fn iter_globals_rev(&self) -> GlobalsIterator {
        GlobalsIterator {
            id: Some(self.globals.len()),
            globals: &self.globals
        }
    }

    pub fn with_globals_map_index(self, index: usize) -> State {
        State {
            globals_map_index: index,
            ..self
        }
    }

    pub fn locals(&self) -> &Context {
        &self.locals
    }

    pub fn globals(&self) -> &HashMap<QualifiedName, (core::Term, core::Term, usize)> {
        &self.globals
    }
}

pub struct GlobalsIterator<'a> {
    id: Option<usize>,
    globals: &'a HashMap<QualifiedName, (core::Term, core::Term, usize)>
}

impl Iterator for GlobalsIterator<'_> {
    type Item = (QualifiedName, core::Term, core::Term, usize);

    fn next(&mut self) -> Option<Self::Item> {
        if self.id.is_none() { return None; }
        for (name, (r#type, value, id)) in self.globals {
            if *id == self.id.unwrap() {
                self.id = Some(self.id.unwrap() + 1);
                return Some((name.clone(), r#type.clone(), value.clone(), *id)); // TODO: fix clone overuse
            }
        }
        None
    }
}

impl DoubleEndedIterator for GlobalsIterator<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.id.is_none() { return None; }
        for (name, (r#type, value, id)) in self.globals {
            if *id == self.id.unwrap() {
                if let Some(ref mut self_id) = self.id {
                    *self_id -= 1;
                } else {
                    self.id = None;
                }
                return Some((name.clone(), r#type.clone(), value.clone(), *id)); // TODO: fix clone overuse
            }
        }
        None
    }
}