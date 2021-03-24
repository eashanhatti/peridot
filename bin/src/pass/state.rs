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
                InnerVar::*,
                InnerVar,
                Symbol
            },
        },
        surface::*
    }
};
extern crate macros;
use macros::*;
extern crate assoc_collections;
use assoc_collections::*;

// globals maps names to type id pairs
// id is used to calculate the arg needed to pass to the globals map at index zero in order to get that global term
// global_id is used as a source of fresh ids
#[derive(Clone, Debug)]
pub struct State {
	locals: Context,
    local_names_to_indices: HashMap<Name, InnerVar>,
    globals: HashMap<QualifiedName, (core::Term, core::Term, usize)>, // dec, def, id
    global_id: usize,
    pub globals_map_index: usize,
    pub num_global_decs: usize,
    nominal_ids_to_field_order: HashMap<usize, HashMap<Name, usize>> // field name, field position in core type
}

impl State {
	pub fn new(num_global_decs: usize) -> Self {
        let map1: HashMap<Name, InnerVar> = HashMap::new();
        let map2: HashMap<QualifiedName, (core::Term, core::Term, usize)> = HashMap::new();
		Self {
            locals: Context::new(),
            local_names_to_indices: map1,
            globals: map2,
            global_id: 0,
            globals_map_index: 0,
            num_global_decs,
            nominal_ids_to_field_order: HashMap::new()
        }
	}

    pub fn with_nominal_id_to_field_order(mut self, id: usize, dec: HashMap<Name, usize>) -> Self {
        self.nominal_ids_to_field_order.insert(id, dec);
        self
    }

    pub fn get_nominal_id_to_field_order(&self, id: usize) -> Option<HashMap<Name, usize>> {
        if let Some(val) = self.nominal_ids_to_field_order.get(&id) {
            Some(val.clone())
        } else {
            None
        }
    }

    pub fn with_dec(self, name: Name, r#type: core::Term) -> Self {
        let mut local_names_to_indices: HashMap<Name, InnerVar> =
            self.local_names_to_indices.into_iter().map(|(k, v)|
                if let Bound(index) = v {
                    (k, Bound(index + 1))
                } else {
                    (k, v)
                }).collect();
        local_names_to_indices.insert(name, Bound(0));

        Self {
            locals: self.locals.inc_and_shift(1).with_dec(Bound(0), shift(r#type, HashSet::new(), 1)),
            local_names_to_indices,
            globals_map_index: self.globals_map_index + 1,
            ..self
        }
    }

    // declare before use, `with_dec(name, _)` must have been called before this is
    pub fn with_def(self, name: Name, value: core::Term) -> Self {
        if let Some(index) = self.local_names_to_indices.get(&name) {
            if self.locals.exists_dec(*index) {
                Self {
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

    pub fn get(&self, name: &Name) -> Option<(InnerVar, ContextEntry)> {
        if let Some(index) = self.local_names_to_indices.get(name) {
            if let Some(entry) = self.locals.get(*index) {
                return Some((*index, entry));
            }
        }
        None
    }

    pub fn get_dec(&self, name: &Name) -> Option<(InnerVar, core::Term)> {
        let entry = self.get(name)?;
        Some((entry.0, entry.1.dec?))
    }

    pub fn get_def(&self, name: &Name) -> Option<(InnerVar, core::Term)> {
        let entry = self.get(name)?;
        Some((entry.0, entry.1.def?))
    }

    pub fn with_global_dec(self, name: QualifiedName, r#type: core::Term) -> Self {
        if let Some(_) = self.globals.get(&name) {
            panic!("duplicate global");
        } else {
            let mut globals = self.globals;
            globals.insert(name, (r#type.clone(), postulate!(Symbol(rand::random::<usize>()) ,: r#type), self.global_id));
            Self {
                globals,
                global_id: self.global_id + 1,
                ..self
            }
        }
    }

    pub fn with_global_def(mut self, name: QualifiedName, value: core::Term) -> Self {
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

    pub fn with_globals_map_index(self, index: usize) -> Self {
        Self {
            globals_map_index: index,
            ..self
        }
    }

    // this is a hack
    pub fn raw_inc_and_shift(self, amount: isize) -> Self {
        let locals = self.locals.inc_and_shift(amount);
        let mut local_names_to_indices = self.local_names_to_indices;
        for (name, ref mut index) in &mut local_names_to_indices {
            if let Bound(ref mut bound_index) = index {
                *bound_index = ((*bound_index as isize) + amount) as usize;
            }
        }

        Self {
            locals,
            local_names_to_indices,
            globals_map_index: ((self.globals_map_index as isize) + amount) as usize,
            ..self
        }
    }

    // this also is a hack
    pub fn raw_with_dec(self, name: Name, index: InnerVar, r#type: core::Term) -> Self {
        let mut local_names_to_indices = self.local_names_to_indices;
        local_names_to_indices.insert(name, index);
        Self {
            local_names_to_indices,
            locals: self.locals.with_dec(index, r#type),
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