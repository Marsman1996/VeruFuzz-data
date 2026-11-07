//! `base64ct` error type mirror
//!
//! Upstream: https://github.com/RustCrypto/formats (SUBDIR=base64ct)
//!   pin 4c5fadb155ebc05c4a8a3abc05e4e64a6a100614 (see code/base64ct/src/errors.rs; the code/ tree is unmodified)
//!
//! Mirror strategy (KVerus relax conventions; see out/bug-finder-summary.md):
//! - The three error type structures are mirrored verbatim (variant order kept).
//! - `derive(Copy/Clone/Debug/Eq/PartialEq)` and the `fmt::Display` /
//!   `core::error::Error` impls are not transcribed: the fmt machinery is outside the Verus
//!   support surface; assertion semantics are carried by spec-level variant equality (the same
//!   criterion as the upstream `assert_eq!`). - The `INVALID_ENCODING_MSG` / `INVALID_LENGTH_MSG`
//!   texts themselves are fmt-domain, unverified; the upstream doc contract (error classification) is carried by the encoding/decoder-side specs.

use vstd::prelude::*;

verus! {

/// Insufficient output buffer length.
/// Origin: code/base64ct/src/errors.rs:11-20 `pub struct InvalidLengthError`
pub struct InvalidLengthError;

/// Invalid encoding of provided Base64 string.
/// Origin: code/base64ct/src/errors.rs:22-31 `pub struct InvalidEncodingError`
pub struct InvalidEncodingError;

/// Generic error, union of `InvalidEncodingError` and `InvalidLengthError`.
/// Origin: code/base64ct/src/errors.rs:33-81 `pub enum Error`
pub enum Error {
    /// Invalid encoding of provided Base64 string.
    InvalidEncoding,

    /// Insufficient output buffer length.
    InvalidLength,
}

} // verus!
