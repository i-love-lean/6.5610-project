//! Placeholder:
//! ```ignore
//! Doc comment example
//! ```
#![allow(clippy::too_many_arguments)]
#![deny(clippy::cast_possible_truncation)]

pub mod anchor;
pub mod env;
pub mod expr;
pub mod flat;
pub mod inductive;
pub mod level;
pub mod name;
pub mod parser;
pub mod quot;
pub mod tc;
pub mod zkvm_entry;
#[cfg(test)]
mod tests;
pub mod union_find;
pub mod unique_hasher;
pub mod util;

pub(crate) const STACK_SIZE: usize = 16_777_216;
