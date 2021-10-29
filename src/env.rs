use std::collections::HashMap;

pub struct Env<'a, T> {
    parent: Option<&'a Env<'a, T>>,
    bindings: HashMap<String, T>,
}

impl<'a, T> Env<'a, T> {
    pub fn new(parent: Option<&'a Env<'a, T>>) -> Env<'a, T> {
        Env {
            parent,
            bindings: HashMap::new(),
        }
    }

    pub fn lookup(&self, name: &str) -> Option<&T> {
        match self.bindings.get(name) {
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

    pub fn insert<S: ToString>(&mut self, name: &S, value: T) {
        self.bindings.insert(name.to_string(), value);
    }
}
