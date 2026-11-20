//! faest FA5 batch driver -- src/random_oracles.rs (the SHAKE H0..H4
//! contract face), mounted standalone (the fa4-driver shape).
//! src/lib.rs is NOT mounted: the FA2 batch holds lib.rs this window
//! (its mod lines for the fields panel), and lib.rs carries no
//! verified content of its own beyond the module tree -- so the closed
//! FA1/FA4/FA9 panels are mounted here by path instead. The closed
//! panels are re-verified in this run; no FA1/FA4/FA9 file is modified
//! (the mtime rule).
//!
//! Mounts (all read-only, closed panels except the FA5 file):
//! - `src/parameter.rs` (FA1): the tau table, WGRIND and OWF-Lambda
//!   pins, the tau-offset exec/spec faces.
//! - `src/utils.rs` (FA1): the challenge-decode and byte-utility
//!   family (utils supplies the Reader interface random_oracles.rs
//!   implements).
//! - `src/parameter_tower.rs` (FA9): the BaseParameters LambdaBytes /
//!   LambdaBytesTimes2 consts this batch pins the H-family read slots
//!   against (the bavc.rs:355 com slab).
//! - `src/prg.rs` (FA4): add_tweak, the trusted AES-CTR stream face,
//!   the PRG carrier and the KeySize/LambdaBytes pins (the byte-oracle
//!   family precedent FA5 follows).
//! - `src/random_oracles.rs` (FA5, this batch): the Hasher128/256
//!   carriers (the verified absorbed-string view), the trusted SHAKE
//!   Xof read face (pure fill), the finish SEP-pad contract, the
//!   h0_init..h4_init family over both SHAKE variants, the
//!   default/clone lowerings, the layout/stream/slot contract faces,
//!   the tower slot pins, and the three KAT groups.

#[allow(unused_imports)]
use vstd::prelude::*;

#[path = "src/random_oracles.rs"]
mod random_oracles;

#[path = "src/prg.rs"]
mod prg;

#[path = "src/parameter.rs"]
mod parameter;

#[path = "src/utils.rs"]
mod utils;

#[path = "src/parameter_tower.rs"]
mod parameter_tower;

fn main() {}
