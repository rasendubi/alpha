use std::error::Error;

use crate::env::Env;
use crate::exp::{TypeDefinition, TypeSpecifier};
use crate::symbol::Symbol;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AlphaType {
    pub name: Symbol,
    pub typedef: AlphaTypeDef,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AlphaTypeDef {
    Abstract,
    Int(usize),
    Float(usize),
    Struct { fields: Vec<(Symbol, AlphaType)> },
}

impl AlphaType {
    pub fn from_exp(
        e: &TypeDefinition,
        types: &Env<AlphaType>,
    ) -> Result<AlphaType, Box<dyn Error>> {
        let name = e.name;
        let typedef = match &e.specifier {
            TypeSpecifier::Abstract => AlphaTypeDef::Abstract,
            TypeSpecifier::Integer(n) => AlphaTypeDef::Int(*n),
            TypeSpecifier::Float(n) => AlphaTypeDef::Float(*n),
            TypeSpecifier::Struct(fields) => {
                let mut fs = fields
                    .iter()
                    .map(|f| {
                        (
                            f.name,
                            types.lookup(f.typ).cloned().expect("unable to lookup type"),
                        )
                    })
                    .collect::<Vec<_>>();
                fs.sort_by(|a, b| a.1.typedef.is_ptr().cmp(&b.1.typedef.is_ptr()).reverse());
                AlphaTypeDef::Struct { fields: fs }
            }
        };

        Ok(AlphaType { name, typedef })
    }
}

impl AlphaTypeDef {
    /// Returns `true` if this type can be inlined as a field. i.e. size of the type is known and <
    /// 8 bytes.
    pub fn is_inlinable(&self) -> bool {
        match self {
            AlphaTypeDef::Abstract => false,
            AlphaTypeDef::Int(_) => true,
            AlphaTypeDef::Float(_) => true,
            AlphaTypeDef::Struct { fields } => fields.len() <= 1,
        }
    }

    /// Returns `true` if values of that type can contain pointers.
    pub fn has_ptrs(&self) -> bool {
        match self {
            AlphaTypeDef::Abstract => true,
            AlphaTypeDef::Int(_) => false,
            AlphaTypeDef::Float(_) => false,
            AlphaTypeDef::Struct { fields } => {
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
            AlphaTypeDef::Abstract => return None,
            AlphaTypeDef::Int(bits) => (bits + 7) / 8,
            AlphaTypeDef::Float(bits) => (bits + 7) / 8,
            AlphaTypeDef::Struct { fields } => fields.len() * 8,
        };
        let size = ((size + 7) / 8) * 8;
        Some(size)
    }

    pub fn n_ptrs(&self) -> Option<usize> {
        let n = match self {
            AlphaTypeDef::Abstract => return None,
            AlphaTypeDef::Int(_) => 0,
            AlphaTypeDef::Float(_) => 0,
            AlphaTypeDef::Struct { fields } => fields
                .iter()
                .take_while(|(_, typ)| typ.typedef.is_ptr())
                .count(),
        };
        Some(n)
    }
}
