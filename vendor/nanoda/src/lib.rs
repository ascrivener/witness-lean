//! Placeholder:
//! ```ignore
//! Doc comment example
//! ```
// no_std for the PVM; the tests (upstream's, unported) use std.
#![cfg_attr(not(test), no_std)]
#![allow(clippy::too_many_arguments)]
#![deny(clippy::cast_possible_truncation)]

extern crate alloc;
#[cfg(feature = "trace")]
extern crate std;

pub(crate) mod prelude {
    pub use alloc::{borrow::ToOwned, boxed::Box, format, string::{String, ToString}, vec, vec::Vec};
}

pub mod debug_printer;
pub mod env;
pub mod expr;
pub mod inductive;
pub mod level;
pub mod name;
pub mod nodes;
pub mod parser;
pub mod pretty_printer;
pub mod quot;
pub mod tc;
#[cfg(test)]
mod tests;
pub mod unique_hasher;
pub mod util;

#[allow(dead_code)]
pub(crate) const STACK_SIZE: usize = 16_777_216;
