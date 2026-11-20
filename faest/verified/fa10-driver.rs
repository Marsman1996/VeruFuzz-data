//! faest FA10-pre batch driver -- rijndael_32.rs (the fixsliced
//! Rijndael data layer) plus aes.rs (the OWF constraint-layer trait
//! surface), mounted standalone (the fa5-driver shape).
//! src/lib.rs is NOT mounted: the FA2 batch holds lib.rs this window
//! (its mod lines for the fields panel), and lib.rs carries no
//! verified content of its own beyond the module tree -- so the
//! closed FA1/FA9 panels are mounted here by path instead. The
//! closed panels are re-verified in this run; no FA1/FA9 file is
//! modified (the mtime rule). The fa9-driver's 330-item identity is
//! the regression anchor for this batch's drivers.
//!
//! Mounts (read-only closed panels):
//! - `src/parameter.rs` (FA1): the tau table, WGRIND and OWF-Lambda
//!   pins, the tau-offset exec/spec faces.
//! - `src/utils.rs` (FA1): the challenge-decode and byte-utility
//!   family.
//! - `src/parameter_tower.rs` (FA9): the constant tower and the
//!   identity theorem set (the 330-panel regression carrier).
//! Mounts (this batch):
//! - `src/rijndael_32.rs` (FA10-pre): the bitslice/inv_bitslice
//!   permutation layer, the BPC-113 sbox circuit family
//!   (sub_bytes/sub_bytes_nots/rijndael_sub_bytes), mix_columns_0,
//!   rijndael_shift_rows_1, rijndael_add_round_key, memshift32, the
//!   batch-block word accessor, the RCON pin, the key-schedule size
//!   pins, and the KAT rows (uniform-plane / roundtrip /
//!   mix-columns; the sbox partial row rides D-FA10-2).
//! - `src/aes.rs` (FA10-pre): the eight OWF constraint-layer trait
//!   declarations over the local OWFParametersFace marker.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/rijndael_32.rs"]
mod rijndael_32;

#[path = "src/aes.rs"]
mod aes;

#[path = "src/parameter.rs"]
mod parameter;

#[path = "src/utils.rs"]
mod utils;

#[path = "src/parameter_tower.rs"]
mod parameter_tower;

fn main() {}
