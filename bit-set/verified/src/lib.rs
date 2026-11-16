//! bit-set 0.11.1 (set/src/lib.rs mirror) -- crate root of the Verus
//! transcription tree.
//!
//! Same-name mirror of the upstream module tree `mod iter; mod set; mod
//! util;` (set/src/lib.rs:64-66, minus the ny-std/cfg extern lines). The
//! underlying BitVec model is mounted once here at the crate root
//! (single source of verified BitVec facts; nothing is re-copied).
//! B = u32 materialization, following the established bit-vec verified
//! convention. Upstream `pub use bit_vec::BitBlock;` has no mirror face
//! (the BitBlock trait is dissolved into the u32 materialization, per the
//! bit-vec pipeline ruling); `mod iter` joined with batch C (the iterator
//! batch; out/harness-inventory.md).
//!
//! Consumption: no fn main in the tree; drivers under harness/ reference
//! this file via `#[path = "../src/lib.rs"]`; copying src-side specs or
//! lemmas is forbidden. Visibility note (harness reference-style, batch
//! H1): `mod bitvec_lib` is opened `pub` so the harness can reach the
//! single verified BitVec facts source -- minimal relaxation, the
//! bit-vec database precedent.

#![feature(allocator_api)] // needed by the mounted bit-vec assume_specification signature
// (the crate-root #![verifier::timeout(240)] face moves to the harness
//  drivers: this file is mounted as a sub-module under harness/ #[path],
//  where inner verifier attributes are rejected)

use vstd::prelude::*;

#[path = "../../../bit-vec/verified/src/lib.rs"]
pub mod bitvec_lib;

pub mod iter;
pub mod set;
pub mod util;

pub use set::BitSet;

// Verification driver (single-file driver form; the harness zone never
// duplicates this file's content).
fn main() {}
