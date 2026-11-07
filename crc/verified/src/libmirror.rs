//! # crc (verified mirror -- code/src/lib.rs, pin 1894aa9)
//! Rust implementation of CRC.
//!
//! ### Examples
//! [Origin Rust: doc-example two blocks (CRC_16 X25 check==0x906e / custom alg check==0xaee7)]
//! The verification form of the doc examples is transcribed into verified/harness/ut_vectors.rs (obligation anchors:
//!     the doc contract values 0x906e / 0xaee7); the doc comments themselves are not mirrored here.
//!
//! Porting policy:
//!   - [Origin Rust: `#![no_std]` `#![forbid(unsafe_code)]`] crate attributes, not mirrored;
//!   - [Origin Rust: `pub use crc_catalog::algorithm::*; pub use crc_catalog::{Algorithm, Width};`]
//!     the external crate -> crate::catalog (dependency adaptation; see verified/src/catalog.rs,
//!     a verbatim crc-catalog 2.4.0 subset);
//!   - [Origin Rust: `mod crc128; crc16; crc32; crc64; crc8; table; util;`]
//!     module declarations kept (module-path relatives resolve to the same-named mirror files under verified/src/);
//!   - [Origin Rust: `impl<W: Width + Debug, I: Implementation> Debug for Digest`]
//!     the pure-formatting impl -> #[verifier::external_body] (not a verification target);
//!   - [Origin Rust: `#[cfg(test)] mod test` (test_clone)]
//!     The UT verification form is transcribed into verified/harness/ (reference-style organization), not mirrored here.

use vstd::prelude::*;

pub use crate::catalog::*;

mod crc128;
mod crc16;
mod crc32;
mod crc64;
mod crc8;
mod table;
mod util;

// Re-exports exposed for the verus layer (matching upstream pub use semantics)

verus! {

/// A trait for CRC implementations.
/// [Origin Rust: pub trait Implementation -- verbatim]
pub trait Implementation {
    /// Associated data necessary for the implementation (e.g. lookup tables).
    type Data<W>;
}

/// A table-based implementation of the CRC algorithm, with `L` lanes.
/// The number of entries in the lookup table is `L * 256`.
/// [Origin Rust: #[derive(Copy, Clone)] pub struct Table<const L: usize> {} -- verbatim]
#[derive(Copy, Clone)]
pub struct Table<const L: usize> {}

/// An implementation of the CRC algorithm with no lookup table.
/// [Origin Rust: pub type NoTable = Table<0>; -- verbatim]
pub type NoTable = Table<0>;

/// [Origin Rust: type DefaultImpl = Table<1>; -- verbatim]
pub type DefaultImpl = Table<1>;

/// [Origin Rust: impl<const L: usize> Implementation for Table<L> -- verbatim]
impl<const L: usize> Implementation for Table<L> {
    type Data<W> = [[W; 256]; L];
}

/// [Origin Rust: mod private { pub trait Sealed ... } -- verbatim]
mod private {
    pub trait Sealed {}
    impl Sealed for super::Table<0> {}
    impl Sealed for super::Table<1> {}
    impl Sealed for super::Table<16> {}
}

/// Crc instance with a specific width, algorithm, and implementation.
/// [Origin Rust: #[derive(Clone)] pub struct Crc<W: Width, I: Implementation = DefaultImpl> -- verbatim]
#[derive(Clone)]
pub struct Crc<W: Width, I: Implementation = DefaultImpl> {
    pub algorithm: &'static Algorithm<W>,
    data: I::Data<W>,
}

/// [Origin Rust: #[derive(Clone)] pub struct Digest<'a, W: Width, I: Implementation = DefaultImpl> -- verbatim]
#[derive(Clone)]
pub struct Digest<'a, W: Width, I: Implementation = DefaultImpl> {
    crc: &'a Crc<W, I>,
    value: W,
}

/// [Origin Rust: impl Debug for Digest -- external_body; pure formatting, not a verification target]
#[verifier::external_body]
impl<W: Width + core::fmt::Debug + Sized, I: Implementation> core::fmt::Debug for Digest<'_, W, I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let width = "0x".len() + size_of::<W>() * 2;
        let value = &self.value;
        f.debug_struct("Digest")
            .field("value", &format_args!("{value:#0width$x?}"))
            .finish()
    }
}

} // verus!
