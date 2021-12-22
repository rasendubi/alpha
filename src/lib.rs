#![allow(clippy::new_without_default)]
mod ast;
mod dispatch;
mod env;
mod execution_session;
mod gc;
mod hir;
mod init;
mod irgen;
mod stdlib;
mod types;
mod utils;

pub use execution_session::ExecutionSession;
pub use init::init;
pub use stdlib::set_stdout;

// re-export symbols as they are widely used
pub(crate) use types::{symbol, Symbol};
