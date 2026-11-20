//! faest 0.3.0 (repo root src/lib.rs) -- Verus transcription tree,
//! crate root.
//!
//! Mirrors the upstream module tree (src/lib.rs) restricted to the
//! batches already transcribed. This file carries the FA1 batch
//! (upstream src/utils.rs + the consumed tau-constant slice of
//! src/parameter.rs); the field algebra, PRG/oracle wrappers, tree
//! commitment, and sign/verify families mount in later batches.
//! Module visibility is opened pub for the harness mounts that
//! reference this file via #[path] (single source of verified facts;
//! nothing re-copied).
//!
//! The upstream crate carries `#[cfg(not(feature = "std"))] use
//! alloc::...` fallbacks on every ungated file (no_std support); this
//! twin runs on the vstd prelude only.

use vstd::prelude::*;

pub mod fields;
pub mod parameter;
pub mod parameter_tower;
pub mod utils;

// Verification driver (single-file driver form; the trailing empty main
// satisfies the standalone-file invocation; the harness zone never
// duplicates this file's content).
fn main() {}
