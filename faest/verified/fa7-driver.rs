//! faest FA7 batch driver -- bavc.rs (the batch vector commitment:
//! vector commit / open / decommit, the backbone of the signature
//! wire paths), mounted standalone (the fa6-driver shape). src/lib.rs
//! is NOT touched: the FA1/FA4/FA5/FA9 closed panels keep mounting
//! the pinned twins and their frozen panel counts.
//!
//! Mounts (read-only, closed panels):
//! - `src/fields/large_fields.rs` + `src/fields/small_fields.rs`
//!   (FA3, closed tree at the FA6 close),
//! - `src/prover/mod.rs` (FA6-pre closed tree; the mount chain the
//!   FA6 twin needs),
//! - `src/parameter.rs` (FA1 tau constants -- read-only this batch),
//! - `src/parameter_tower.rs` (FA9),
//! - `src/utils.rs` (FA1),
//! - `src/prg.rs` (FA4),
//! - `src/random_oracles.rs` (FA5),
//! - `src/universal_hashing.rs` (FA6).
//! Mounts (this batch):
//! - `src/bavc.rs`: the FA7 bavc twin.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/fields/large_fields.rs"]
mod large_fields;

#[path = "src/fields/small_fields.rs"]
mod small_fields;

#[path = "src/prover/mod.rs"]
mod prover;

#[path = "src/parameter.rs"]
mod parameter;

#[path = "src/parameter_tower.rs"]
mod parameter_tower;

#[path = "src/utils.rs"]
mod utils;

/// Window-3 note: the FA11 parallel batch landed src/prover/
/// key_expansion.rs importing `crate::rijndael_32`; mounted here so
/// this driver keeps compiling on the shared tree (FA11's own
/// driver mounts it; no sibling files are modified).
#[path = "src/rijndael_32.rs"]
mod rijndael_32;

#[path = "src/prg.rs"]
mod prg;

#[path = "src/random_oracles.rs"]
mod random_oracles;

#[path = "src/universal_hashing.rs"]
mod universal_hashing;

#[path = "src/bavc.rs"]
mod bavc;

fn main() {}
