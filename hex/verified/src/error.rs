//! `hex` FromHexError mirror
//!
//! Upstream: https://github.com/KokaKiwi/rust-hex
//!   pin e25a8701f7f6b5ec4acedffcb4a45cfb69cc34eb (empty SUBDIR, i.e.
//!   code/src/error.rs)
//!
//! Mirror strategy (KVerus relax caliber):
//! - Enum body: the structure is mirrored verbatim (fields and variant order
//!   preserved).
//! - `derive(Debug, Clone, Copy, PartialEq, Eq)` kept out: Verus-side
//!   assertions compare variants/fields item by item (harness semantics
//!   equal to assert_eq); spec and proofs do not need PartialEq.
//! - `impl fmt::Display` / `core::error::Error` not transcribed: the
//!   fmt::Formatter/write! machinery is outside the Verus support surface;
//!   its semantic contract ("display the invalid character and its
//!   position") is already carried by val's spec.
//! - The upstream tree is untouched; all transcription lands only in this
//!   verified copy.

use vstd::prelude::*;

verus! {

/// Origin: code/src/error.rs:6-19 `pub enum FromHexError`
pub enum FromHexError {
    /// An invalid character was found. Valid ones are: `0...9`, `a...f`
    /// or `A...F`.
    InvalidHexCharacter { c: char, index: usize },

    /// A hex string's length needs to be even, as two digits correspond to
    /// one byte.
    OddLength,

    /// If the hex string is decoded into a fixed sized container, such as an
    /// array, the hex string's length * 2 has to match the container's
    /// length.
    // SPEC-DOC MISMATCH (rust-hex#99): the doc clause above is unprovable
    // (the length direction is reversed); the implementation instead checks
    // hex_len == 2 * container_len -- the implementation-faithful form that
    // the carried specs follow.
    InvalidStringLength,
}

} // verus!
