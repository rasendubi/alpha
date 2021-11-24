use crate::ast::exp::{TypeDefinition, TypeSpecifier};
use crate::env::Env;
use crate::Symbol;

use std::error::Error;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeDef {
    pub name: Symbol,
    pub supertype: Symbol,
    pub typedef: TypeDescriptor,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeDescriptor {
    Abstract,
    Int(usize),
    Float(usize),
    Struct { fields: Vec<(Symbol, TypeDef)> },
}

impl TypeDef {
    pub fn from_exp(e: &TypeDefinition, types: &Env<TypeDef>) -> Result<TypeDef, Box<dyn Error>> {
        let name = e.name;
        let supertype = e.supertype;
        let typedef = match &e.specifier {
            TypeSpecifier::Abstract => TypeDescriptor::Abstract,
            TypeSpecifier::Integer(n) => TypeDescriptor::Int(*n),
            TypeSpecifier::Float(n) => TypeDescriptor::Float(*n),
            TypeSpecifier::Struct(fields) => {
                let fs = fields
                    .iter()
                    .map(|f| {
                        (
                            f.name,
                            types.lookup(f.typ).cloned().expect("unable to lookup type"),
                        )
                    })
                    .collect::<Vec<_>>();
                // fs.sort_by(|a, b| a.1.typedef.is_ptr().cmp(&b.1.typedef.is_ptr()).reverse());
                TypeDescriptor::Struct { fields: fs }
            }
        };

        Ok(TypeDef {
            name,
            supertype,
            typedef,
        })
    }
}

impl TypeDescriptor {
    /// Returns `true` if this type can be inlined as a field. i.e. size of the type is known and <
    /// 8 bytes.
    pub fn is_inlinable(&self) -> bool {
        match self {
            TypeDescriptor::Abstract => false,
            TypeDescriptor::Int(_) => true,
            TypeDescriptor::Float(_) => true,
            TypeDescriptor::Struct { fields } => fields.len() <= 1,
        }
    }

    /// Returns `true` if values of that type can contain pointers.
    pub fn has_ptrs(&self) -> bool {
        match self {
            TypeDescriptor::Abstract => true,
            TypeDescriptor::Int(_) => false,
            TypeDescriptor::Float(_) => false,
            TypeDescriptor::Struct { fields } => {
                fields.iter().any(|(_name, typ)| typ.typedef.is_ptr())
            }
        }
    }

    /// Returns `true` if fields of that type (potentially inlined) contain pointers that GC needs
    /// to traverse.
    pub fn is_ptr(&self) -> bool {
        if self.is_inlinable() {
            self.has_ptrs()
        } else {
            // if types is not inlinable, we store it as ptr → this type has pointers
            true
        }
    }

    pub fn size(&self) -> Option<usize> {
        let size = match self {
            TypeDescriptor::Abstract => return None,
            TypeDescriptor::Int(bits) => (bits + 7) / 8,
            TypeDescriptor::Float(bits) => (bits + 7) / 8,
            TypeDescriptor::Struct { fields } => fields.len() * 8,
        };
        let size = ((size + 7) / 8) * 8;
        Some(size)
    }

    pub fn n_ptrs(&self) -> Option<usize> {
        let n = match self {
            TypeDescriptor::Abstract => return None,
            TypeDescriptor::Int(_) => 0,
            TypeDescriptor::Float(_) => 0,
            TypeDescriptor::Struct { fields } => fields
                .iter()
                .take_while(|(_, typ)| typ.typedef.is_ptr())
                .count(),
        };
        Some(n)
    }

    pub fn pointer_offsets(&self) -> Option<Vec<usize>> {
        let pointers = match self {
            TypeDescriptor::Abstract => return None,
            TypeDescriptor::Int(_) => Vec::new(),
            TypeDescriptor::Float(_) => Vec::new(),
            TypeDescriptor::Struct { fields } => {
                let mut ptrs = Vec::new();
                for (i, (_, typ)) in fields.iter().enumerate() {
                    if typ.typedef.is_ptr() {
                        ptrs.push(i * 8);
                    }
                }
                ptrs
            }
        };
        Some(pointers)
    }
}
