use std::collections::HashMap;

use crate::Symbol;

#[derive(Debug)]
pub struct Env<'a, T> {
    parent: Option<&'a Env<'a, T>>,
    bindings: HashMap<Symbol, T>,
}

impl<'a, T> Env<'a, T> {
    pub fn new(parent: Option<&'a Env<'a, T>>) -> Env<'a, T> {
        Env {
            parent,
            bindings: HashMap::new(),
        }
    }

    pub fn lookup(&self, name: Symbol) -> Option<&T> {
        match self.bindings.get(&name) {
            None => {
                if let Some(p) = self.parent {
                    p.lookup(name)
                } else {
                    None
                }
            }
            x => x,
        }
    }

    pub fn insert(&mut self, name: Symbol, value: T) {
        self.bindings.insert(name, value);
    }
}
