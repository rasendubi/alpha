mod free_global_vars;
#[allow(clippy::module_inception)]
mod hir;
mod hirgen;
mod inline_var_alias;

pub use hir::*;
pub use hirgen::*;
