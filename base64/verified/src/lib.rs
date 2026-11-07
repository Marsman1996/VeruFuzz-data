//! base64 0.23.1 (pin 5b98ee1) -- root of the Verus transcription tree.
//!
//! Mirror and relaxation ledger (KVerus relax conventions; see out/bug-finder-summary.md):
//! 1. The `Engine` trait (generics + default methods + `T: AsRef<[u8]>`) is outside the Verus
//!    transcription surface: it is monomorphized per call site into table-parameterized
//!    machine-level functions (encode_t/decode_t/padding/config bits), landing in the `engine/`
//!    mirror; a trait default method body's semantics = the transcribed function's contract.
//! 2. Upstream `&str` parameters (the Alphabet::new family) are monomorphized to `&[u8]`
//!    (superdomain: any Err conclusion holds on the subdomain; on Ok paths bytes and str
//!    are equivalent).
//! 3. `[u8; 64]`/`[u8; 256]` literal arrays / const-evaluated tables -> length-64/256
//!    slice parameters + spec model constraints (`ValidEncodeTable`/`ValidDecodeTable`);
//!    `Alphabet { symbols: [u8;64], padding }` -> slice parameters.
//! 4. `checked_mul`/`checked_add`/`checked_sub` -> bound-check rewrites with the same
//!    overflow semantics.
//! 5. Unsupported fragments (`u64::from_be_bytes`/`copy_from_slice`/`TryInto` etc.) ->
//!    bitwise-equivalent expansion (exec provides the equivalent machine-level implementation;
//!    `Origin Rust:` comments keep the original text).
//! 6. The alloc/String/io streaming paths (encode/encode_string/decode_vec, read/write,
//!    display) are not transcribed (blocked, on record); the simd engine (unsafe intrinsics)
//!    is not transcribed.
//!
//! Consumption: this file has no fn main; drivers under harness/ reference it via
//! `#[path = "../src/lib.rs"] mod b64;`; copying its spec or lemmas is forbidden.

use vstd::prelude::*;

pub mod alphabet;
pub mod decode;
pub mod encode;
pub mod engine;
