//! faest FA4 batch driver -- src/prg.rs (the AES-CTR PRG face), mounted
//! standalone (the fa9-driver precedent). src/lib.rs is NOT mounted:
//! the FA2 batch holds lib.rs this window (its mod lines for the
//! fields panel), and lib.rs carries no verified content of its own
//! beyond the module tree -- so the closed FA1/FA9 panels are mounted
//! here by path instead. The closed panels are re-verified in this
//! run; no FA1/FA9 file is modified (the mtime rule).
//!
//! Mounts (all read-only, closed panels except the FA4 file):
//! - `src/parameter.rs` (FA1): the tau table, WGRIND and OWF-Lambda
//!   pins, the tau-offset exec/spec faces.
//! - `src/utils.rs` (FA1): the challenge-decode and byte-utility
//!   family (utils supplies the Reader interface prg.rs implements).
//! - `src/parameter_tower.rs` (FA9): the BaseParameters LambdaBytes
//!   consts this batch pins the PRG KeySizes against.
//! - `src/prg.rs` (FA4, this batch): add_tweak (wrapping tweak
//!   arithmetic, fully verified), the trusted AES-CTR stream face
//!   (prg_byte oracle + xor-fill read contract), the zero-dst fill
//!   face closing D-FA1-1, the PRG carrier + PseudoRandomGenerator
//!   trait, the KeySize/LambdaBytes pins, the contract faces and the
//!   add_tweak-reachable KAT halves.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/prg.rs"]
mod prg;

#[path = "src/parameter.rs"]
mod parameter;

#[path = "src/utils.rs"]
mod utils;

#[path = "src/parameter_tower.rs"]
mod parameter_tower;

fn main() {}
